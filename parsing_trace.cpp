#include <iostream>
#include <fstream>
#include <iomanip>
#include <cstring>  // memcmp, memset을 위해 필요
#include <cstdint>
#include <algorithm> // std::all_of 등을 위해 필요

// inc/ 디렉토리의 헤더 파일을 사용합니다. (경로가 정확한지 확인하세요)
#include "inc/trace_instruction.h"

#pragma pack(push, 1)
using trace_instr_format_t = input_instr;
#pragma pack(pop)

// 매직 마커 식별을 위한 기준 값 (0xFF...FF)
// PIN Tracer에서 memset(&magic_marker, 0xFF, sizeof(trace_instr_format_t))를 사용했기 때문에 필요합니다.
const trace_instr_format_t MAGIC_MARKER_VALUE = []() {
    trace_instr_format_t marker;
    std::memset(&marker, 0xFF, sizeof(trace_instr_format_t));
    return marker;
}();

void print_instruction(uint64_t count, const trace_instr_format_t& instr) {
    // --- Instruction Header ---
    std::cout << "--- Instruction " << std::dec << count << " ---" << std::endl;
    std::cout << "  IP: 0x" << std::hex << instr.ip << std::endl;

    if (instr.is_branch) {
        std::cout << "  Branch: " << (instr.branch_taken ? "Taken" : "Not Taken") << std::endl;
    }

    // --- Register Info ---
    std::cout << "  Src Regs: ";
    for (int i = 0; i < NUM_INSTR_SOURCES; ++i) {
        if (instr.source_registers[i] != 0)
            std::cout << std::dec << (int)instr.source_registers[i] << " ";
    }
    std::cout << std::endl;

    std::cout << "  Dst Regs: ";
    for (int i = 0; i < NUM_INSTR_DESTINATIONS; ++i) {
        if (instr.destination_registers[i] != 0)
            std::cout << std::dec << (int)instr.destination_registers[i] << " ";
    }
    std::cout << std::endl;

    // --- Memory Access Info (Address and Data) ---
    
    // 소스 메모리 (Load)
    bool src_mem_printed = false;
    for (int i = 0; i < NUM_INSTR_SOURCES; ++i) {
        if (instr.source_memory[i] != 0) {
            if (!src_mem_printed) {
                std::cout << "  Src Mem: [Addr] 0x";
                src_mem_printed = true;
            }
            std::cout << std::hex << instr.source_memory[i] << " ";
        }
    }
    if (src_mem_printed) {
        std::cout << std::endl << "           [Data] 0x";
        for (int i = 0; i < NUM_INSTR_SOURCES; ++i) {
            if (instr.source_memory[i] != 0) { // 주소가 있을 때만 데이터 출력
                std::cout << std::hex << instr.source_data[i] << " ";
            }
        }
        std::cout << std::endl;
    }

    // 목적지 메모리 (Store)
    bool dst_mem_printed = false;
    for (int i = 0; i < NUM_INSTR_DESTINATIONS; ++i) {
        if (instr.destination_memory[i] != 0) {
            if (!dst_mem_printed) {
                std::cout << "  Dst Mem: [Addr] 0x";
                dst_mem_printed = true;
            }
            std::cout << std::hex << instr.destination_memory[i] << " ";
        }
    }
    if (dst_mem_printed) {
        std::cout << std::endl << "           [Data] 0x";
        for (int i = 0; i < NUM_INSTR_DESTINATIONS; ++i) {
            if (instr.destination_memory[i] != 0) { // 주소가 있을 때만 데이터 출력
                std::cout << std::hex << instr.destination_data[i] << " ";
            }
        }
        std::cout << std::endl;
    }

    std::cout << std::dec; // 출력 형식을 10진수로 복원
}

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "사용법: " << argv[0] << " <uncompressed_trace_file>" << std::endl;
        return 1;
    }

    std::ifstream trace_file(argv[1], std::ios::binary);
    if (!trace_file) {
        std::cerr << "오류: 파일을 열 수 없습니다: " << argv[1] << std::endl;
        return 1;
    }

    trace_instr_format_t current_instr;
    uint64_t instr_count = 0;
    uint64_t magic_marker_count = 0;
    
    // 출력 포맷 설정
    std::cout << std::setw(8) << std::setfill('0');
    
    while (trace_file.read(reinterpret_cast<char*>(&current_instr), sizeof(trace_instr_format_t))) {
        
        // 매직 마커 검사: 모든 바이트가 0xFF인지 확인
        if (std::memcmp(&current_instr, &MAGIC_MARKER_VALUE, sizeof(trace_instr_format_t)) == 0) {
            magic_marker_count++;
            std::cout << "\n--- MAGIC MARKER " << magic_marker_count << " DETECTED ---" << std::endl;
            // 매직 마커는 명령어 계수에 포함하지 않습니다.
            continue;
        }

        instr_count++;
        print_instruction(instr_count, current_instr);
    }
    
    std::cout << "\n파싱 완료!" << std::endl;
    std::cout << "========================================" << std::endl;
    std::cout << "  총 읽어들인 명령어 수: " << instr_count << std::endl;
    std::cout << "  발견된 매직 마커 수: " << magic_marker_count << std::endl;
    std::cout << "========================================" << std::endl;

    trace_file.close();
    return 0;
}