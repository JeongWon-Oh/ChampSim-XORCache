/*
 *    Copyright 2023 The ChampSim Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*! @file
 *  This is an example of the PIN tool that demonstrates some basic PIN APIs
 *  and could serve as the starting point for developing your first PIN tool
 */

#include <fstream>
#include <iostream>
#include <stdlib.h>
#include <string.h>
#include <string>
#include <cstring>
#include <cstdio>

#include "../../inc/trace_instruction.h"
#include "pin.H"

using trace_instr_format_t = input_instr;

/* ================================================================== */
// Global variables
/* ================================================================== */

UINT64 instrCount = 0;

std::ofstream outfile;

trace_instr_format_t curr_instr;

BOOL is_tracing_active = false;

/* ===================================================================== */
// Command line switches
/* ===================================================================== */
KNOB<std::string> KnobOutputFile(KNOB_MODE_WRITEONCE, "pintool", "o", "champsim.trace", "specify file name for Champsim tracer output");

KNOB<UINT64> KnobSkipInstructions(KNOB_MODE_WRITEONCE, "pintool", "s", "0", "How many instructions to skip before tracing begins");

KNOB<UINT64> KnobTraceInstructions(KNOB_MODE_WRITEONCE, "pintool", "t", "1000000", "How many instructions to trace");

/* ===================================================================== */
// Utilities
/* ===================================================================== */

/*!
 *  Print out help message.
 */
INT32 Usage()
{
  std::cerr << "This tool creates a register and memory access trace" << std::endl
            << "Specify the output trace file with -o" << std::endl
            << "Specify the number of instructions to skip before tracing with -s" << std::endl
            << "Specify the number of instructions to trace with -t" << std::endl
            << std::endl;

  std::cerr << KNOB_BASE::StringKnobSummary() << std::endl;

  return -1;
}

/* ===================================================================== */
// Analysis routines
/* ===================================================================== */

VOID StartTrace() {
  is_tracing_active = true;
  std::cout << "[Pintool] Starting trace at main function." << std::endl;
}

VOID StopTrace() {
  is_tracing_active = false;
  std::cout << "[Pintool] Stopping trace after main function." << std::endl;
}

void ResetCurrentInstruction(VOID* ip)
{
  curr_instr = {};
  curr_instr.ip = (unsigned long long int)ip;
}

BOOL ShouldWrite()
{
  ++instrCount;
  // return (instrCount > KnobSkipInstructions.Value()) && (instrCount <= (KnobTraceInstructions.Value() + KnobSkipInstructions.Value()));
  return is_tracing_active;
}

void WriteCurrentInstruction()
{
  typename decltype(outfile)::char_type buf[sizeof(trace_instr_format_t)];
  std::memcpy(buf, &curr_instr, sizeof(trace_instr_format_t));
  outfile.write(buf, sizeof(trace_instr_format_t));
}

void BranchOrNot(UINT32 taken)
{
  curr_instr.is_branch = 1;
  curr_instr.branch_taken = taken;
}

template <typename T>
void WriteToSet(T* begin, T* end, UINT32 r)
{
  auto set_end = std::find(begin, end, 0);
  auto found_reg = std::find(begin, set_end, r); // check to see if this register is already in the list
  *found_reg = r;
}

// Write (Destination) Operation
void WriteToSet_Dest(ADDRINT addr, UINT32 size)
{
    unsigned long long data = 0;
    // 메모리 크기가 8바이트 이하인 경우에만 캡처 (1 word 단위)
    if (size > 0 && size <= sizeof(data)) {
        // addr에서 size만큼 읽어 data에 안전하게 복사
        PIN_SafeCopy(&data, (void*)addr, size);
    }
    
    // 이전에 정의한 템플릿 함수 WriteToSet_MemAddrAndData의 역할 수행
    // WriteToSet_MemAddrAndData<unsigned long long int> 호출 로직을 인라인화
    
    unsigned long long int* addr_begin = curr_instr.destination_memory;
    unsigned long long int* addr_end = curr_instr.destination_memory + NUM_INSTR_DESTINATIONS;
    unsigned long long int* data_begin = curr_instr.destination_data;
    
    auto set_end = std::find(addr_begin, addr_end, 0);
    auto found_addr = std::find(addr_begin, set_end, addr); 

    if (found_addr == set_end && set_end != addr_end) {
        *set_end = addr;
        std::size_t index = std::distance(addr_begin, set_end);
        *(data_begin + index) = data;
    }
}

// Read (Source) Operation
void WriteToSet_Source(ADDRINT addr, UINT32 size)
{
    unsigned long long data = 0;
    if (size > 0 && size <= sizeof(data)) {
        PIN_SafeCopy(&data, (void*)addr, size);
    }

    // 이전에 정의한 템플릿 함수 WriteToSet_MemAddrAndData의 역할 수행
    // WriteToSet_MemAddrAndData<unsigned long long int> 호출 로직을 인라인화

    unsigned long long int* addr_begin = curr_instr.source_memory;
    unsigned long long int* addr_end = curr_instr.source_memory + NUM_INSTR_SOURCES;
    unsigned long long int* data_begin = curr_instr.source_data;

    auto set_end = std::find(addr_begin, addr_end, 0);
    auto found_addr = std::find(addr_begin, set_end, addr); 

    if (found_addr == set_end && set_end != addr_end) {
        *set_end = addr;
        std::size_t index = std::distance(addr_begin, set_end);
        *(data_begin + index) = data;
    }
}

void WriteToSet_Dest_From_Reg(ADDRINT addr, uint64_t val)
{
    unsigned long long int* addr_begin = curr_instr.destination_memory;
    unsigned long long int* addr_end = curr_instr.destination_memory + NUM_INSTR_DESTINATIONS;
    unsigned long long int* data_begin = curr_instr.destination_data;
    
    // 메모리 주소 배열에서 빈 공간을 찾습니다.
    auto set_end = std::find(addr_begin, addr_end, 0);
    auto found_addr = std::find(addr_begin, set_end, addr); 

    if (found_addr == set_end && set_end != addr_end) {
        *set_end = addr;
        std::size_t index = std::distance(addr_begin, set_end);
        
        // 레지스터 값을 Store 데이터로 기록합니다.
        *(data_begin + index) = val;
    }
}
/* ===================================================================== */
// Instrumentation callbacks
/* ===================================================================== */

VOID Routine(RTN rtn, VOID *v)
{
  // 추가: Pin이 발견하는 모든 함수의 이름을 출력합니다.
    // std::cout << "[Pintool] Found Routine: " << RTN_Name(rtn) << std::endl;


    const std::string rtn_name = RTN_Name(rtn);

    // "start_trace" 함수를 찾으면 StartTrace 분석 함수를 삽입합니다.
    if (rtn_name == "start_trace") {
        // std::cout << "[Pintool] Found 'start_trace' trigger. Instrumenting..." << std::endl;
        RTN_Open(rtn);
        RTN_InsertCall(rtn, IPOINT_BEFORE, (AFUNPTR)StartTrace, IARG_END);
        RTN_Close(rtn);
    }

    // "end_trace" 함수를 찾으면 StopTrace 분석 함수를 삽입합니다.
    if (rtn_name == "end_trace") {
        // std::cout << "[Pintool] Found 'end_trace' trigger. Instrumenting..." << std::endl;
        RTN_Open(rtn);
        RTN_InsertCall(rtn, IPOINT_BEFORE, (AFUNPTR)StopTrace, IARG_END);
        RTN_Close(rtn);
    }
}

VOID WriteMagicMarker()
{
  trace_instr_format_t magic_marker;
  memset(&magic_marker, 0xFF, sizeof(trace_instr_format_t));

  // 기존과 동일하게 outfile에 씁니다.
  typename decltype(outfile)::char_type buf[sizeof(trace_instr_format_t)];
  std::memcpy(buf, &magic_marker, sizeof(trace_instr_format_t));
  outfile.write(buf, sizeof(trace_instr_format_t));
  
  instrCount++;
}

// Is called for every instruction and instruments reads and writes
VOID Instruction(INS ins, VOID* v)
{
  // 1. INS_IsCPUID를 Opcode 비교로 수정
  if (INS_Opcode(ins) == XED_ICLASS_CPUID) {
    INS prev_ins = INS_Prev(ins);
    if (INS_Valid(prev_ins) && INS_Opcode(prev_ins) == XED_ICLASS_MOV &&
      INS_OperandIsReg(prev_ins, 0) && INS_OperandReg(prev_ins, 0) == REG_EAX &&
      INS_OperandIsImmediate(prev_ins, 1) && (ADDRINT)INS_OperandImmediate(prev_ins, 1) == 0xDEADBEEF) {

      // 매직 시퀀스가 맞다면, 실제 액션을 수행할 함수를 등록합니다.
      // 이 함수는 CPUID가 실행될 때마다 호출됩니다 (Execution Time).
      INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)WriteMagicMarker, IARG_END);

      // 이 명령어는 매직 마커 전용이므로,
      // 아래의 일반적인 명령어 처리 로직을 타지 않도록 여기서 종료합니다.
      return;
    }
  }
  
  // begin each instruction with this function
  INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)ResetCurrentInstruction, IARG_INST_PTR, IARG_END);

  // instrument branch instructions
  if (INS_IsBranch(ins))
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)BranchOrNot, IARG_BRANCH_TAKEN, IARG_END);

  // instrument register reads
  UINT32 readRegCount = INS_MaxNumRRegs(ins);
  for (UINT32 i = 0; i < readRegCount; i++) {
    UINT32 regNum = INS_RegR(ins, i);
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)WriteToSet<unsigned char>, IARG_PTR, curr_instr.source_registers, IARG_PTR,
                   curr_instr.source_registers + NUM_INSTR_SOURCES, IARG_UINT32, regNum, IARG_END);
  }

  // instrument register writes
  UINT32 writeRegCount = INS_MaxNumWRegs(ins);
  for (UINT32 i = 0; i < writeRegCount; i++) {
    UINT32 regNum = INS_RegW(ins, i);
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)WriteToSet<unsigned char>, IARG_PTR, curr_instr.destination_registers, IARG_PTR,
                   curr_instr.destination_registers + NUM_INSTR_DESTINATIONS, IARG_UINT32, regNum, IARG_END);
  }

  // instrument memory reads and writes
  UINT32 memOperands = INS_MemoryOperandCount(ins);

  // Iterate over each memory operand of the instruction.
  for (UINT32 memOp = 0; memOp < memOperands; memOp++) {
    // 1. 메모리 접근 크기를 먼저 계산합니다.
    UINT32 memSize = INS_MemoryOperandSize(ins, memOp);
    
    // 2. Load Operation (Read)
    if (INS_MemoryOperandIsRead(ins, memOp))
      INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)WriteToSet_Source, 
                     IARG_MEMORYOP_EA, memOp, 
                     IARG_UINT32, memSize,     // 계산된 크기를 UINT32 타입으로 전달
                     IARG_END);
                     
    // 3. Store Operation (Write)
    if (INS_MemoryOperandIsWritten(ins, memOp)) {
        // Store 명령의 소스 레지스터를 반복하여 캡처합니다.
        UINT32 readRegCount = INS_MaxNumRRegs(ins);
        
        for (UINT32 i = 0; i < readRegCount; i++) {
            REG src_reg = INS_RegR(ins, i); // i번째 소스 레지스터

            // --- 중요: REG_is_gr() 함수를 사용하여 범용 레지스터만 필터링합니다. ---
            if (REG_is_gr(src_reg)) {
                // Store 명령의 메모리 쓰기 주소는 IARG_MEMORYOP_EA로 전달하고,
                // 데이터는 IARG_REG_VALUE로 전달합니다.
                INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)WriteToSet_Dest_From_Reg, 
                               IARG_MEMORYOP_EA, memOp,      // 유효 주소를 실행 시점에 계산하여 전달
                               IARG_REG_VALUE, src_reg,      // GPR의 실제 값 (데이터)
                               IARG_END);
            }
        }
    }
  }

  // finalize each instruction with this function
  INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)ShouldWrite, IARG_END);
  INS_InsertThenCall(ins, IPOINT_BEFORE, (AFUNPTR)WriteCurrentInstruction, IARG_END);
}

/*!
 * Print out analysis results.
 * This function is called when the application exits.
 * @param[in]   code            exit code of the application
 * @param[in]   v               value specified by the tool in the
 *                              PIN_AddFiniFunction function call
 */
VOID Fini(INT32 code, VOID* v) { outfile.close(); }

/*!
 * The main procedure of the tool.
 * This function is called when the application image is loaded but not yet started.
 * @param[in]   argc            total number of elements in the argv array
 * @param[in]   argv            array of command line arguments,
 *                              including pin -t <toolname> -- ...
 */
int main(int argc, char* argv[])
{
  // Initialize PIN library. Print help message if -h(elp) is specified
  // in the command line or the command line is invalid
  if (PIN_Init(argc, argv))
    return Usage();

  PIN_InitSymbols();

  outfile.open(KnobOutputFile.Value().c_str(), std::ios_base::binary | std::ios_base::trunc);
  if (!outfile) {
    std::cout << "Couldn't open output trace file. Exiting." << std::endl;
    exit(1);
  }

  RTN_AddInstrumentFunction(Routine, 0);

  // Register function to be called to instrument instructions
  INS_AddInstrumentFunction(Instruction, 0);

  // Register function to be called when the application exits
  PIN_AddFiniFunction(Fini, 0);

  // Start the program, never returns
  PIN_StartProgram();

  return 0;
}