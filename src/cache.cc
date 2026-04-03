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

#include "cache.h"

#include <algorithm>
#include <cassert>
#include <cmath>
#include <iomanip>
#include <numeric>
#include <random>
#include <fmt/core.h>

#include "bandwidth.h"
#include "champsim.h"
#include "chrono.h"
#include "deadlock.h"
#include "instruction.h"
#include "util/algorithm.h"
#include "util/bits.h"
#include "util/span.h"

CACHE::CACHE(CACHE&& other)
    : operable(other),

      upper_levels(std::move(other.upper_levels)), lower_level(std::move(other.lower_level)), lower_translate(std::move(other.lower_translate)),

      cpu(other.cpu), NAME(std::move(other.NAME)), NUM_SET(other.NUM_SET), NUM_WAY(other.NUM_WAY), MSHR_SIZE(other.MSHR_SIZE), PQ_SIZE(other.PQ_SIZE),
      HIT_LATENCY(other.HIT_LATENCY), FILL_LATENCY(other.FILL_LATENCY), OFFSET_BITS(other.OFFSET_BITS), block(std::move(other.block)), MAX_TAG(other.MAX_TAG),
      MAX_FILL(other.MAX_FILL), prefetch_as_load(other.prefetch_as_load), match_offset_bits(other.match_offset_bits), virtual_prefetch(other.virtual_prefetch),
      pref_activate_mask(std::move(other.pref_activate_mask)),

      directory(std::move(other.directory)),
      xor_metadata(std::move(other.xor_metadata)),
      map_table(std::move(other.map_table)),
      l2c_upper_present(std::move(other.l2c_upper_present)),

      sim_stats(std::move(other.sim_stats)), roi_stats(std::move(other.roi_stats)),

      pref_module_pimpl(std::move(other.pref_module_pimpl)), repl_module_pimpl(std::move(other.repl_module_pimpl))
{
  pref_module_pimpl->bind(this);
  repl_module_pimpl->bind(this);
}

auto CACHE::operator=(CACHE&& other) -> CACHE&
{
  this->clock_period = other.clock_period;
  this->current_time = other.current_time;
  this->warmup = other.warmup;

  this->upper_levels = std::move(other.upper_levels);
  this->lower_level = std::move(other.lower_level);
  this->lower_translate = std::move(other.lower_translate);

  this->cpu = other.cpu;
  this->NAME = std::move(other.NAME);
  this->NUM_SET = other.NUM_SET;
  this->NUM_WAY = other.NUM_WAY;
  ;
  this->MSHR_SIZE = other.MSHR_SIZE;
  ;
  this->PQ_SIZE = other.PQ_SIZE;
  this->HIT_LATENCY = other.HIT_LATENCY;
  this->FILL_LATENCY = other.FILL_LATENCY;
  this->OFFSET_BITS = other.OFFSET_BITS;
  ;
  this->block = std::move(other.block);
  this->MAX_TAG = other.MAX_TAG;
  this->MAX_FILL = other.MAX_FILL;
  this->prefetch_as_load = other.prefetch_as_load;
  this->match_offset_bits = other.match_offset_bits;
  this->virtual_prefetch = other.virtual_prefetch;
  this->pref_activate_mask = std::move(other.pref_activate_mask);

  this->l2c_upper_present = std::move(other.l2c_upper_present);

  this->sim_stats = std::move(other.sim_stats);
  this->roi_stats = std::move(other.roi_stats);

  this->pref_module_pimpl = std::move(other.pref_module_pimpl);
  this->repl_module_pimpl = std::move(other.repl_module_pimpl);

  pref_module_pimpl->bind(this);
  repl_module_pimpl->bind(this);

  return *this;
}

CACHE::tag_lookup_type::tag_lookup_type(const request_type& req, bool local_pref, bool skip)
    : address(req.address), v_address(req.v_address), data(req.data), ip(req.ip), instr_id(req.instr_id), pf_metadata(req.pf_metadata), cpu(req.cpu),
      type(req.type), prefetch_from_this(local_pref), skip_fill(skip), is_translated(req.is_translated), instr_depend_on_me(req.instr_depend_on_me),
      data_value(req.data_value), data_cache_line(req.data_cache_line)
{
}

CACHE::mshr_type::mshr_type(const tag_lookup_type& req, champsim::chrono::clock::time_point _time_enqueued)
    : address(req.address), v_address(req.v_address), ip(req.ip), instr_id(req.instr_id), cpu(req.cpu), type(req.type),
      prefetch_from_this(req.prefetch_from_this), time_enqueued(_time_enqueued), instr_depend_on_me(req.instr_depend_on_me), to_return(req.to_return),
      data_value(req.data_value), data_cache_line(req.data_cache_line), inclusive_evict(req.inclusive_evict)
{
}

CACHE::mshr_type CACHE::mshr_type::merge(mshr_type predecessor, mshr_type successor)
{
  std::vector<uint64_t> merged_instr{};
  std::vector<std::deque<response_type>*> merged_return{};
  std::vector<std::deque<response_type>*> merged_inclusive_evict{};

  std::set_union(std::begin(predecessor.instr_depend_on_me), std::end(predecessor.instr_depend_on_me), std::begin(successor.instr_depend_on_me),
                 std::end(successor.instr_depend_on_me), std::back_inserter(merged_instr));
  std::set_union(std::begin(predecessor.to_return), std::end(predecessor.to_return), std::begin(successor.to_return), std::end(successor.to_return),
                 std::back_inserter(merged_return));
  std::set_union(std::begin(predecessor.inclusive_evict), std::end(predecessor.inclusive_evict), std::begin(successor.inclusive_evict), std::end(successor.inclusive_evict),
                 std::back_inserter(merged_inclusive_evict));               

  mshr_type retval{(successor.type == access_type::PREFETCH) ? predecessor : successor};

  retval.data_cache_line = predecessor.data_cache_line;
  for (int i = 0; i < 8; ++i) {
      if (successor.data_cache_line[i] != 0) {
          retval.data_cache_line[i] = successor.data_cache_line[i];
      }
  }

  if (successor.type != access_type::PREFETCH) {
      retval.data_value = successor.data_value;
  } else {
      retval.data_value = predecessor.data_value;
  }

  // set the time enqueued to the predecessor unless its a demand into prefetch, in which case we use the successor
  retval.time_enqueued =
      ((successor.type != access_type::PREFETCH && predecessor.type == access_type::PREFETCH)) ? successor.time_enqueued : predecessor.time_enqueued;
  retval.instr_depend_on_me = merged_instr;
  retval.to_return = merged_return;
  retval.inclusive_evict = merged_inclusive_evict;
  retval.data_promise = predecessor.data_promise;

  if constexpr (champsim::debug_print) {
    if (successor.type == access_type::PREFETCH) {
      fmt::print("[MSHR] {} address {} type: {} into address {} type: {}\n", __func__, successor.address,
                 access_type_names.at(champsim::to_underlying(successor.type)), predecessor.address,
                 access_type_names.at(champsim::to_underlying(successor.type)));
    } else {
      fmt::print("[MSHR] {} address {} type: {} into address {} type: {}\n", __func__, predecessor.address,
                 access_type_names.at(champsim::to_underlying(predecessor.type)), successor.address,
                 access_type_names.at(champsim::to_underlying(successor.type)));
    }
  }

  return retval;
}

auto CACHE::fill_block(mshr_type mshr, uint32_t metadata) -> BLOCK
{
  CACHE::BLOCK to_fill;
  to_fill.valid = true;
  to_fill.prefetch = mshr.prefetch_from_this;
  to_fill.dirty = (mshr.type == access_type::WRITE);
  to_fill.address = mshr.address;
  to_fill.v_address = mshr.v_address;
  to_fill.data = mshr.data_promise->data;
  // long w_index = get_word_index(mshr.address);
  // to_fill.data_cache_line[w_index] = mshr.data_promise->data.to<uint64_t>();
  to_fill.data_cache_line = mshr.data_promise->data_cache_line;
  to_fill.pf_metadata = metadata;

  return to_fill;
}

auto CACHE::fill_block_write(mshr_type mshr, uint32_t metadata) -> BLOCK
{
  CACHE::BLOCK to_fill;
  to_fill.valid = true;
  to_fill.prefetch = mshr.prefetch_from_this;
  to_fill.dirty = (mshr.type == access_type::WRITE);
  to_fill.address = mshr.address;
  to_fill.v_address = mshr.v_address;
  to_fill.data = mshr.data_promise->data;
  long w_index = get_word_index(mshr.address);
  to_fill.data_cache_line[w_index] = mshr.data_promise->data_cache_line[w_index];
  // to_fill.data_cache_line = mshr.data_promise->data_cache_line;
  to_fill.pf_metadata = metadata;

  return to_fill;
}

auto CACHE::matches_address(champsim::address addr) const
{
  return [match = addr.slice_upper(OFFSET_BITS), shamt = OFFSET_BITS](const auto& entry) {
    return entry.address.slice_upper(shamt) == match;
  };
}

template <typename T>
champsim::address CACHE::module_address(const T& element) const
{
  auto address = virtual_prefetch ? element.v_address : element.address;
  return champsim::address{address.slice_upper(match_offset_bits ? champsim::data::bits{} : OFFSET_BITS)};
}

bool CACHE::handle_fill(const mshr_type& fill_mshr)
{
  cpu = fill_mshr.cpu;

  // find victim
  auto [set_begin, set_end] = get_set_span(fill_mshr.address);
  auto way = std::find_if_not(set_begin, set_end, [](auto x) { return x.valid; });
  if (way == set_end) {
    way = std::next(set_begin, impl_find_victim(fill_mshr.cpu, fill_mshr.instr_id, get_set_index(fill_mshr.address), &*set_begin, fill_mshr.ip,
                                                fill_mshr.address, fill_mshr.type));
  }
  assert(set_begin <= way);
  assert(way <= set_end);
  assert(way != set_end || fill_mshr.type != access_type::WRITE); // Writes may not bypass
  const auto way_idx = std::distance(set_begin, way);             // cast protected by earlier assertion

  if constexpr (champsim::debug_print) {
    fmt::print("[{}] {} instr_id: {} address: {} v_address: {} set: {} way: {} type: {} prefetch_metadata: {} cycle_enqueued: {} cycle: {}\n", NAME, __func__,
               fill_mshr.instr_id, fill_mshr.address, fill_mshr.v_address, get_set_index(fill_mshr.address), way_idx,
               access_type_names.at(champsim::to_underlying(fill_mshr.type)), fill_mshr.data_promise->pf_metadata,
               (fill_mshr.time_enqueued.time_since_epoch()) / clock_period, (current_time.time_since_epoch()) / clock_period);
  }

  if(((NAME == "LLC") && (fill_mshr.type == access_type::WRITE || fill_mshr.type == access_type::RFO))) { //&& ((get_set_index(handle_pkt.address)==10) || (get_set_index(handle_pkt.address)==21)))) {
    fmt::print("[{}] {} instr_id: {} address: {} v_address: {} data_cache_line[0]: 0x{:x} set: {} way: {} type: {} prefetch_metadata: {} cycle_enqueued: {} cycle: {}\n", NAME, __func__,
               fill_mshr.instr_id, fill_mshr.address, fill_mshr.v_address, fill_mshr.data_promise->data_cache_line[0], get_set_index(fill_mshr.address), way_idx,
               access_type_names.at(champsim::to_underlying(fill_mshr.type)), fill_mshr.data_promise->pf_metadata,
               (fill_mshr.time_enqueued.time_since_epoch()) / clock_period, (current_time.time_since_epoch()) / clock_period);
  }

  if (NAME == "LLC" && way != set_end && way->valid) {
    // A. 기존 XOR 관계 끊기 (데이터가 사라지므로)
    long set_idx = get_set_index(fill_mshr.address);
    uint32_t evict_flat_idx = set_idx * NUM_WAY + way_idx;
    
    // [XOR Cache] exclusive_owner 초기화 (eviction)
    directory[evict_flat_idx].exclusive_owner = -1;
    
    if(xor_metadata[evict_flat_idx].is_xored) {
      break_xor_relationship((uint32_t)set_idx, (uint32_t)way_idx);
      fmt::print("[UNXOR_eviction] Cycle: {} Addr: {:#x}\n", 
                    current_time.time_since_epoch() / clock_period, way->address.to<uint64_t>());
      
      // B. [핵심] 상위 캐시 Invalidation 요청 (Inclusive Policy)
      // 상위 캐시(L1/L2)에 있는 사본을 지우고, 만약 Dirty였다면 알려달라고 함
      bool was_upper_dirty = invalidate_entry(*way);

      // C. 상위 캐시가 Dirty였다면, LLC 블록도 Dirty로 승격
      // (그래야 아래 Writeback 로직에서 메모리로 올바르게 내려감)
      if (was_upper_dirty) {
          way->dirty = true;
      }

        way->valid = true;
    } else {
      uint32_t map_idx = get_map_hash(way->data_cache_line);
      // Hash collision 대응: map_table이 실제로 이 블록을 가리키는 경우에만 무효화
      if (map_table[map_idx].valid && 
          map_table[map_idx].set_index == (uint32_t)set_idx && 
          map_table[map_idx].way_index == (uint32_t)way_idx) {
        fmt::print("[remove_from_MAPTABLE] Cycle: {} Addr: {:#x}\n", 
                      current_time.time_since_epoch() / clock_period, way->address.to<uint64_t>());
        map_table[map_idx].valid = false;
      }
    }
  } 
  // else if (NAME == "LLC" && way != set_end && (fill_mshr.type == access_type::WRITE || fill_mshr.type == access_type::RFO)) {
  //   long set_idx = get_set_index(fill_mshr.address);
  //   if(xor_metadata[set_idx * NUM_WAY + way_idx].is_xored) {
  //     break_xor_relationship((uint32_t)set_idx, (uint32_t)way_idx);
  //     fmt::print("[UNXOR_getM] Cycle: {} CPU: {} Addr: {:#x} Data: {:#x} | Set: {} Way: {} | WRITE/RFO triggered unXOR\n", 
  //                   current_time.time_since_epoch() / clock_period, fill_mshr.cpu, way->address.to<uint64_t>(),
  //                   way->data_cache_line[0], set_idx, way_idx);
  //   }
  // }

  // =================================================================
  // [L2C Inclusive Policy] L2C eviction 시 L1 캐시도 무효화 (L1 ⊆ L2 보장)
  // L2C에서 블록을 교체하기 전에 L1D/L1I에 사본이 있으면 invalidation 전송
  // =================================================================
  if ((NAME.find("L2C") != std::string::npos) && way != set_end && way->valid) {
    long set_idx = get_set_index(fill_mshr.address);
    uint32_t flat_idx = set_idx * NUM_WAY + way_idx;
    if (l2c_upper_present[flat_idx]) {
      auto invalidator = channel_type::invalidator_for(way->address);
      for (auto* ul : upper_levels) {
        invalidator(ul);
      }
      l2c_upper_present[flat_idx] = false;
      fmt::print("[L2C_EVICT_INVAL_L1] Cycle: {} Addr: {:#x} Set: {} Way: {} -> invalidating L1 caches (inclusive policy)\n",
                 current_time.time_since_epoch() / clock_period, way->address.to<uint64_t>(),
                 set_idx, way_idx);
    }
  }

  if (way != set_end && way->valid && way->dirty) {
    request_type writeback_packet;

    writeback_packet.cpu = fill_mshr.cpu;
    writeback_packet.address = way->address;
    // writeback_packet.data = way->data;
    writeback_packet.data = champsim::address{way->data_cache_line[get_word_index(way->address)]};
    writeback_packet.data_value = way->data_cache_line[get_word_index(way->address)];
    writeback_packet.data_cache_line = way->data_cache_line;
    writeback_packet.instr_id = fill_mshr.instr_id;
    writeback_packet.ip = champsim::address{};
    writeback_packet.type = access_type::WRITE;
    writeback_packet.pf_metadata = way->pf_metadata;
    writeback_packet.response_requested = false;

    if constexpr (champsim::debug_print) {
      fmt::print("[{}] {} evict address: {} v_address: {} prefetch_metadata: {}\n", NAME, __func__, writeback_packet.address, writeback_packet.v_address,
                 fill_mshr.data_promise->pf_metadata);
    }

    auto success = lower_level->add_wq(writeback_packet);
    if (!success) {
      return false;
    }
  }
  // [XOR Cache] L2C에서 clean eviction 시에만 LLC에 putS 알림 (sharer 제거용)
  // L2C eviction 시 L1은 위에서 이미 invalidation 되었으므로, LLC에 putS만 전송
  // source_cpu를 포함하여 LLC가 해당 CPU의 sharer만 제거하도록 함
  else if (way != set_end && way->valid && !way->dirty && (NAME == "cpu0_L2C" || NAME == "cpu1_L2C")) {
    // L2C clean line eviction -> LLC에 putS 알림 (source_cpu 포함)
    auto invalidator = channel_type::invalidator_for(way->address, cpu);
    invalidator(lower_level);
    fmt::print("[L2C_CLEAN_EVICT] Cycle: {} CPU: {} Addr: {:#x} Set: {} Way: {} -> sending putS to LLC\n",
               current_time.time_since_epoch() / clock_period, cpu, way->address.to<uint64_t>(),
               get_set_index(way->address), std::distance(set_begin, way));
  }
  // [L1 Inclusive Policy] L1에서 clean eviction 시 L2C에 putS 알림 (l2c_upper_present 갱신용)
  // L1D/L1I가 공간 부족으로 clean line을 evict하면 L2C에 알림
  else if (way != set_end && way->valid && !way->dirty && (NAME.find("L1") != std::string::npos)) {
    auto invalidator = channel_type::invalidator_for(way->address);
    invalidator(lower_level);
    fmt::print("[L1_CLEAN_EVICT] Cycle: {} {} Addr: {:#x} Set: {} Way: {} -> sending putS to L2C\n",
               current_time.time_since_epoch() / clock_period, NAME, way->address.to<uint64_t>(),
               get_set_index(way->address), std::distance(set_begin, way));
  }

  champsim::address evicting_address{};
  if (way != set_end && way->valid) {
    evicting_address = module_address(*way);
  }

  auto metadata_thru = impl_prefetcher_cache_fill(module_address(fill_mshr), get_set_index(fill_mshr.address), way_idx,
                                                  (fill_mshr.type == access_type::PREFETCH), evicting_address, fill_mshr.data_promise->pf_metadata);
  impl_replacement_cache_fill(fill_mshr.cpu, get_set_index(fill_mshr.address), way_idx, module_address(fill_mshr), fill_mshr.ip, evicting_address,
                              fill_mshr.type);

  if (way != set_end) {
    if (way->valid && way->prefetch) {
      ++sim_stats.pf_useless;
    }

    if (fill_mshr.type == access_type::PREFETCH) {
      ++sim_stats.pf_fill;
    }

    if(fill_mshr.type == access_type::WRITE) {
      *way = fill_block_write(fill_mshr, metadata_thru);
    } else {
      *way = fill_block(fill_mshr, metadata_thru);
    }
    // for (int i = 0; i < 8; ++i) {
    //     if (fill_mshr.data_cache_line[i] != 0) {
    //         way->data_cache_line[i] = fill_mshr.data_cache_line[i];
    //     }
    // }
    // =================================================================
    // [XOR Cache Logic Start] 데이터가 캐시에 들어온 직후 실행
    // =================================================================
    if(NAME == "LLC") {
      long set_idx = get_set_index(fill_mshr.address);
      uint32_t flat_idx = set_idx * NUM_WAY + way_idx;
      
      // [Directory Update] WRITE는 L2C dirty writeback (eviction)이므로 sharer 제거
      // LOAD/RFO는 상위 캐시가 데이터를 요청한 것이므로 sharer 등록
      if (fill_mshr.type == access_type::WRITE) {
        directory[flat_idx].sharers[fill_mshr.cpu] = false;
        // Dirty writeback 시 exclusive_owner 해제 (M→S0/S 전환)
        if (directory[flat_idx].exclusive_owner == (int)fill_mshr.cpu) {
          directory[flat_idx].exclusive_owner = -1;
        }
        fmt::print("[LLC_FILL_WRITEBACK] Cycle: {} CPU: {} Addr: {:#x} Set: {} Way: {} -> removed sharer (dirty eviction from L2C)\n",
                   current_time.time_since_epoch() / clock_period, fill_mshr.cpu,
                   fill_mshr.address.to<uint64_t>(), set_idx, way_idx);
      } else {
        directory[flat_idx].sharers[fill_mshr.cpu] = true;
        if (fill_mshr.type == access_type::RFO) {
            directory[flat_idx].exclusive_owner = fill_mshr.cpu;
            // 필요하다면 여기서 다른 sharer들을 false로 초기화하는 로직 추가 (Fill이므로 기본적으론 없겠지만 안전상)
        } else {
            directory[flat_idx].exclusive_owner = -1; // 일반 LOAD는 Shared 상태
        }
      }
      // Fill 시에는 항상 S 상태 (exclusive_owner = -1 유지)
      // getM이 오면 그때 exclusive_owner 설정됨
      
      // [XOR Cache] dirty 라인은 XOR 대상에서 제외
      // 논문: "Modified lines remain exclusive and cannot be XORed"
      if (way->dirty || fill_mshr.type == access_type::RFO) {
          fmt::print("[XOR_SKIP] Cycle: {} Addr: {:#x} | Dirty or RFO line, skip XOR\n",
                     current_time.time_since_epoch() / clock_period,
                     fill_mshr.address.to<uint64_t>());
      } else {
      uint32_t map_idx = get_map_hash(way->data_cache_line);

      if (map_table[map_idx].valid) {
          // [Hit] Map Table에 후보가 있음 -> XOR 압축 수행 가능성 확인
          uint32_t p_set = map_table[map_idx].set_index;
          uint32_t p_way = map_table[map_idx].way_index;
          uint32_t p_flat_idx = p_set * NUM_WAY + p_way;

          // 파트너 블록에 접근하기 위한 Iterator
          auto partner_block_it = std::next(std::begin(this->block), p_flat_idx);

          // XOR 압축 조건:
          // 1. 자기 자신이 아님
          // 2. 파트너가 valid
          // 3. 파트너가 M 상태가 아님 (dirty=false AND exclusive_owner=-1)
          bool partner_is_modified = partner_block_it->dirty || is_line_modified(p_flat_idx);
          if (flat_idx != p_flat_idx && partner_block_it->valid && !partner_is_modified) {
            const char* new_state = is_line_s0(flat_idx) ? "S0" : "S";
            const char* partner_state = is_line_s0(p_flat_idx) ? "S0" : "S";
            fmt::print("[XOR_SUCCESS] Cycle: {} CPU: {} | NewAddr: {:#x} NewData: [{:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}] ({}) | PartnerAddr: {:#x} PartnerData: [{:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}] ({}) | Pair: {}+{} | Hash: {} | Set: {} Way: {} <-> Set: {} Way: {}\n", 
                  current_time.time_since_epoch() / clock_period,
                  fill_mshr.cpu,
                  fill_mshr.address.to<uint64_t>(), 
                  way->data_cache_line[0], way->data_cache_line[1], way->data_cache_line[2], way->data_cache_line[3], way->data_cache_line[4], way->data_cache_line[5], way->data_cache_line[6], way->data_cache_line[7],
                  new_state,
                  partner_block_it->address.to<uint64_t>(),
                  partner_block_it->data_cache_line[0], partner_block_it->data_cache_line[1], partner_block_it->data_cache_line[2], partner_block_it->data_cache_line[3], partner_block_it->data_cache_line[4], partner_block_it->data_cache_line[5], partner_block_it->data_cache_line[6], partner_block_it->data_cache_line[7],
                  partner_state,
                  new_state, partner_state,
                  map_idx,
                  set_idx, way_idx,
                  p_set, p_way);
              // A. 메타데이터 업데이트 (XOR 관계 설정)
              xor_metadata[flat_idx] = {true, p_set, p_way};
              xor_metadata[p_flat_idx] = {true, (uint32_t)set_idx, (uint32_t)way_idx};
              // // B. 실제 데이터 XOR 연산 (Value = New_Data ^ Partner_Data)
              // std::array<uint64_t, 8> xor_val;
              // for(int i=0; i<8; i++) {
              //     xor_val[i] = way->data_cache_line[i] ^ partner_block_it->data_cache_line[i];
              // }
              // // C. 데이터 덮어쓰기 (논리적 공유 상태 모사)
              // way->data_cache_line = xor_val;
              // partner_block_it->data_cache_line = xor_val;
              map_table[map_idx].valid = false;
              sim_stats.xor_compressions++;
          } else {
              // 파트너가 무효하거나 자기 자신이거나 Modified인 경우 -> Map Table 갱신
              fmt::print("[XOR_UPDATE] Cpu: {} Cycle: {} Addr: {:#x} Hash: {} | Partner Invalid/Self/Modified -> Update MapTable\n", 
                  fill_mshr.cpu,
                  current_time.time_since_epoch() / clock_period, 
                  fill_mshr.address.to<uint64_t>(), 
                  map_idx);
              map_table[map_idx] = {true, (uint32_t)set_idx, (uint32_t)way_idx};
          }
      } else {
          // [Miss] 후보 없음 -> Map Table에 등록하고 대기
          fmt::print("[XOR_INSERT] Cpu: {} Cycle: {} Addr: {:#x} Hash: {} Data: [{:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}] | Inserted into MapTable\n", 
               fill_mshr.cpu,
               current_time.time_since_epoch() / clock_period, 
               fill_mshr.address.to<uint64_t>(), 
               map_idx,
               way->data_cache_line[0], way->data_cache_line[1], way->data_cache_line[2], way->data_cache_line[3], way->data_cache_line[4], way->data_cache_line[5], way->data_cache_line[6], way->data_cache_line[7]);
          map_table[map_idx] = {true, (uint32_t)set_idx, (uint32_t)way_idx};
      }
      } // end if (!modified)
    }
    // =================================================================
    // [XOR Cache Logic End]
    // =================================================================

    // =================================================================
    // [L2C Directory] handle_fill 시 l2c_upper_present 갱신
    // - WRITE fill: L1에서 dirty writeback → L1은 더 이상 보유하지 않음
    // - 그 외 (to_return 있음): L1에 데이터 전달 → L1이 보유
    // =================================================================
    if (NAME.find("L2C") != std::string::npos) {
      long set_idx = get_set_index(fill_mshr.address);
      uint32_t flat_idx = set_idx * NUM_WAY + way_idx;
      
      if (fill_mshr.type == access_type::WRITE) {
        // L1 dirty writeback: L1은 이 라인을 evict함
        l2c_upper_present[flat_idx] = false;
      } else if (!fill_mshr.to_return.empty()) {
        // 응답이 L1으로 전달됨: L1이 이 라인을 보유
        l2c_upper_present[flat_idx] = true;
      }
    }
  }

  // COLLECT STATS
  if (fill_mshr.type != access_type::PREFETCH)
    sim_stats.total_miss_latency_cycles += (current_time - (fill_mshr.time_enqueued + clock_period)) / clock_period;
  sim_stats.mshr_return.increment(std::pair{fill_mshr.type, fill_mshr.cpu});

  response_type response{fill_mshr.address, fill_mshr.v_address, fill_mshr.data_promise->data, fill_mshr.data_value, fill_mshr.data_cache_line, metadata_thru, fill_mshr.instr_depend_on_me};
  for (auto* ret : fill_mshr.to_return) {
    ret->push_back(response);
  }

  return true;
}

bool CACHE::try_hit(const tag_lookup_type& handle_pkt)
{
  cpu = handle_pkt.cpu;

  // access cache
  auto [set_begin, set_end] = get_set_span(handle_pkt.address);
  auto way = std::find_if(set_begin, set_end, [matcher = matches_address(handle_pkt.address)](const auto& x) { return x.valid && matcher(x); });
  const auto hit = (way != set_end);
  const auto useful_prefetch = (hit && way->prefetch && !handle_pkt.prefetch_from_this);

  // [DEBUG] RFO/WRITE 요청 디버그 출력
  if (NAME == "LLC" && (handle_pkt.type == access_type::WRITE || handle_pkt.type == access_type::RFO)) {
    fmt::print("[LLC_DEBUG] {} Cycle: {} Addr: {:#x} Type: {} Hit: {}\n", __func__,
               current_time.time_since_epoch() / clock_period, handle_pkt.address.to<uint64_t>(),
               access_type_names.at(champsim::to_underlying(handle_pkt.type)), hit ? "HIT" : "MISS");
  }
  if (handle_pkt.data.to<uint64_t>() == 0x0000000000010000 || handle_pkt.data.to<uint64_t>() == 0x0000000001000000 || handle_pkt.data.to<uint64_t>() == 0x0000000100000000 || handle_pkt.data.to<uint64_t>() == 0x0000010000000000 || handle_pkt.data.to<uint64_t>() == 0x1111111111111111
      || handle_pkt.data_value == 0x0000000000010000 || handle_pkt.data_value == 0x0000000001000000 || handle_pkt.data_value == 0x0000000100000000 || handle_pkt.data_value == 0x0000010000000000 || handle_pkt.data_value == 0x1111111111111111
      || way->data_cache_line[0] == 0x0000000000010000 || way->data_cache_line[0] == 0x0000000001000000 || way->data_cache_line[0] == 0x0000000100000000 || way->data_cache_line[0] == 0x0000010000000000 || way->data_cache_line[0] == 0x1111111111111111) {
        fmt::print("CPU{} {} Try Hit with target data ({}) Cycle: {} Addr: {:#x} Pkt Data: {:#x} Pkt Data_val: {:#x} Type: {} Data: [{:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}]\n",
                    cpu, NAME, hit ? "HIT" : "MISS", current_time.time_since_epoch() / clock_period,
                    handle_pkt.address.to<uint64_t>(), handle_pkt.data.to<uint64_t>(), handle_pkt.data_value, 
                    access_type_names.at(champsim::to_underlying(handle_pkt.type)),
                    way->data_cache_line[0], way->data_cache_line[1], way->data_cache_line[2], way->data_cache_line[3], way->data_cache_line[4], way->data_cache_line[5], way->data_cache_line[6], way->data_cache_line[7]);
  }

  // if (handle_pkt.address.to<uint64_t>() == 0x1bd040 || handle_pkt.address.to<uint64_t>() == 0x1ad040 || handle_pkt.address.to<uint64_t>() == 0x1c5040 || handle_pkt.address.to<uint64_t>() == 0x1b5040) {
  //       fmt::print("CPU{} {} Debug Try Hit with target data ({}) Cycle: {} Addr: {:#x} V_Addr: {:#x} Pkt Data: {:#x} Pkt Data_val: {:#x} Type: {} Data: [{:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}]\n",
  //                   cpu, NAME, hit ? "HIT" : "MISS", current_time.time_since_epoch() / clock_period,
  //                   handle_pkt.address.to<uint64_t>(), handle_pkt.v_address.to<uint64_t>(), handle_pkt.data.to<uint64_t>(), handle_pkt.data_value, 
  //                   access_type_names.at(champsim::to_underlying(handle_pkt.type)),
  //                   way->data_cache_line[0], way->data_cache_line[1], way->data_cache_line[2], way->data_cache_line[3], way->data_cache_line[4], way->data_cache_line[5], way->data_cache_line[6], way->data_cache_line[7]);
  // }

  if constexpr (champsim::debug_print) {
    fmt::print("[{}] {} instr_id: {} address: {} v_address: {} data: {} set: {} way: {} ({}) type: {} cycle: {}\n", NAME, __func__, handle_pkt.instr_id,
               handle_pkt.address, handle_pkt.v_address, handle_pkt.data, get_set_index(handle_pkt.address), std::distance(set_begin, way),
               hit ? "HIT" : "MISS", access_type_names.at(champsim::to_underlying(handle_pkt.type)), current_time.time_since_epoch() / clock_period);
  }

  auto metadata_thru = handle_pkt.pf_metadata;
  if (should_activate_prefetcher(handle_pkt)) {
    metadata_thru = impl_prefetcher_cache_operate(module_address(handle_pkt), handle_pkt.ip, hit, useful_prefetch, handle_pkt.type, metadata_thru);
  }

  // update replacement policy
  const auto way_idx = std::distance(set_begin, way);
  impl_update_replacement_state(handle_pkt.cpu, get_set_index(handle_pkt.address), way_idx, module_address(handle_pkt), handle_pkt.ip, {}, handle_pkt.type,
                                hit);

  if (hit) {
    sim_stats.hits.increment(std::pair{handle_pkt.type, handle_pkt.cpu});

    if(NAME == "LLC") {
      long set_idx = get_set_index(handle_pkt.address);
      const auto way_idx = std::distance(set_begin, way);
      uint32_t flat_idx = set_idx * NUM_WAY + way_idx;
      uint32_t map_idx = get_map_hash(way->data_cache_line);

      // [Directory Update] Modified lines remain exclusive in L1 (Table 1: M → Dir only)
      // WRITE hit = dirty writeback to LLC, but L1 retains exclusive ownership
      // LOAD/RFO = upper cache requesting data → register as sharer
      if (handle_pkt.type != access_type::WRITE) {
        directory[flat_idx].sharers[handle_pkt.cpu] = true;
      }
      
      if(xor_metadata[flat_idx].is_xored) {
        // fmt::print("hit on XORed\n");
        // -----------------------------------------------------------
        // 1. Direct Forwarding 확인 (Target: Requested Line B)
        // -----------------------------------------------------------
        bool is_direct_forwarding = false;
        for(int i=0; i<NUM_CPUS; i++) {
             if(i != handle_pkt.cpu && directory[flat_idx].sharers[i]) {
                 is_direct_forwarding = true;
                 break;
             }
        }

        if (is_direct_forwarding) {
            // [Case B] Direct Forwarding
            fmt::print("[DIRECT_FORWARDING] Cycle: {} CPU: {} | ReqAddr: {:#x} ReqData: [{:#x}]\n", 
                    current_time.time_since_epoch() / clock_period, handle_pkt.cpu,
                    handle_pkt.address.to<uint64_t>(), way->data_cache_line[0]);
            sim_stats.total_miss_latency_cycles += 21;
            sim_stats.direct_forwardings++;
            // fmt::print(" -> Direct Forwarding\n");
        } 
        else {
            // -------------------------------------------------------
            // 2. Recovery 수행 (Target: Partner Line A)
            // -------------------------------------------------------
            uint32_t p_set = xor_metadata[flat_idx].partner_set;
            uint32_t p_way = xor_metadata[flat_idx].partner_way;
            uint32_t p_flat_idx = p_set * NUM_WAY + p_way;

            bool partner_is_local = directory[p_flat_idx].sharers[handle_pkt.cpu];
            bool partner_is_remote = false;
            
            // 파트너 유효성 및 리모트 체크
            if (p_flat_idx < directory.size()) { // Safety check
                for(int i=0; i<NUM_CPUS; i++) {
                    if(i != handle_pkt.cpu && directory[p_flat_idx].sharers[i]) {
                        partner_is_remote = true;
                        break;
                    }
                }
            }

            if(partner_is_local) {
                // [Case A] Local Recovery
                auto partner_it = std::next(std::begin(this->block), p_flat_idx);
                fmt::print("[LOCAL_RECOVERY] Cycle: {} CPU: {} | ReqAddr: {:#x} ReqData: [{:#x}] | PartnerAddr: {:#x} PartnerData: [{:#x}] | PartnerSet: {} PartnerWay: {}\n", 
                    current_time.time_since_epoch() / clock_period, handle_pkt.cpu,
                    handle_pkt.address.to<uint64_t>(), way->data_cache_line[0],
                    partner_it->address.to<uint64_t>(), partner_it->data_cache_line[0],
                    p_set, p_way);
                sim_stats.total_miss_latency_cycles += 8;
                sim_stats.local_recoveries++;
            }
            else if(partner_is_remote) {
                // [Case C] Remote Recovery
                auto partner_it = std::next(std::begin(this->block), p_flat_idx);
                fmt::print("[REMOTE_RECOVERY] Cycle: {} CPU: {} | ReqAddr: {:#x} ReqData: [{:#x}] | PartnerAddr: {:#x} PartnerData: [{:#x}] | PartnerSet: {} PartnerWay: {} | Partner in other core\n", 
                    current_time.time_since_epoch() / clock_period, handle_pkt.cpu,
                    handle_pkt.address.to<uint64_t>(), way->data_cache_line[0],
                    partner_it->address.to<uint64_t>(), partner_it->data_cache_line[0],
                    p_set, p_way);
                sim_stats.total_miss_latency_cycles += 35;
                sim_stats.remote_recoveries++;
            }
            else {
                // [Warning Case] 둘 다 S0 상태 - 현재 요청자가 유일한 sharer가 됨
                auto partner_it = std::next(std::begin(this->block), p_flat_idx);
                fmt::print("[ERROR] Cycle: {} CPU: {} | ReqAddr: {:#x} Reqset: {} Reqway: {} | PartnerAddr: {:#x} Partnerset {} Partnerway {} | Both S0 state\n",
                    current_time.time_since_epoch() / clock_period, handle_pkt.cpu,
                    handle_pkt.address.to<uint64_t>(), set_idx, way_idx, partner_it->address.to<uint64_t>(), p_set, p_way);
                sim_stats.total_miss_latency_cycles += 8;
                sim_stats.local_recoveries++;
            }
        }
        // -----------------------------------------------------------
        // 3. UnXORing (Write 시)
        // -----------------------------------------------------------
        if (handle_pkt.type == access_type::WRITE || handle_pkt.type == access_type::RFO) {
          fmt::print("[UNXOR_getM] Cycle: {} CPU: {} Addr: {:#x} Data: [{:#x}] | Set: {} Way: {} | handle_hit WRITE/RFO\n", 
                    current_time.time_since_epoch() / clock_period, handle_pkt.cpu,
                    handle_pkt.address.to<uint64_t>(), way->data_cache_line[0],
                    set_idx, way_idx);
          break_xor_relationship((uint32_t)set_idx, (uint32_t)way_idx);
        }
      } else { // not XORed
        if(handle_pkt.type != access_type::WRITE && handle_pkt.type != access_type::RFO) {
        if(map_table[map_idx].valid) {
          if(map_table[map_idx].set_index != set_idx || map_table[map_idx].way_index != way_idx) {
            uint32_t p_set = map_table[map_idx].set_index;
            uint32_t p_way = map_table[map_idx].way_index;
            uint32_t p_flat_idx = p_set * NUM_WAY + p_way;
            auto partner_block_it = std::next(std::begin(this->block), p_flat_idx);

            directory[flat_idx].exclusive_owner = -1;

            // Minimum Sharer Invariant: at least one line must have an upper-cache sharer
            // If both would be S0, don't form the pair — just register in map table
            if (is_line_s0(flat_idx) && is_line_s0(p_flat_idx)) {
              // Both S0: don't form pair; keep map table pointing to partner
              // so a future S line can pair with it
              fmt::print("[XOR_SKIP_BY_TRY_HIT] Cycle: {} CPU: {} | Addr: {:#x} | Both S0, skipping XOR pair\n",
                  current_time.time_since_epoch() / clock_period, handle_pkt.cpu,
                  handle_pkt.address.to<uint64_t>());
            } else {
              xor_metadata[flat_idx] = {true, p_set, p_way};
              xor_metadata[p_flat_idx] = {true, (uint32_t)set_idx, (uint32_t)way_idx};
              map_table[map_idx].valid = false;
              const char* partner_state = is_line_s0(p_flat_idx) ? "S0" : "S";
              const char* new_state = is_line_s0(flat_idx) ? "S0" : "S";
              fmt::print("[XOR_SUCCESS_BY_TRY_HIT] Cycle: {} CPU: {} | NewAddr: {:#x} NewData: [{:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}] ({}) | PartnerAddr: {:#x} PartnerData: [{:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}] ({}) | Pair: {}+{} | Hash: {} | Set: {} Way: {} <-> Set: {} Way: {}\n", 
                  current_time.time_since_epoch() / clock_period,
                  handle_pkt.cpu,
                  handle_pkt.address.to<uint64_t>(), 
                  way->data_cache_line[0], way->data_cache_line[1], way->data_cache_line[2], way->data_cache_line[3], way->data_cache_line[4], way->data_cache_line[5], way->data_cache_line[6], way->data_cache_line[7],
                  new_state,
                  partner_block_it->address.to<uint64_t>(),
                  partner_block_it->data_cache_line[0], partner_block_it->data_cache_line[1], partner_block_it->data_cache_line[2], partner_block_it->data_cache_line[3], partner_block_it->data_cache_line[4], partner_block_it->data_cache_line[5], partner_block_it->data_cache_line[6], partner_block_it->data_cache_line[7],
                  partner_state,
                  new_state, partner_state,
                  map_idx,
                  set_idx, way_idx,
                  p_set, p_way);
            }
          }
        } else {
          // No valid map entry: insert into map table for potential future XOR pairing
          fmt::print("[XOR_MAPTABLE_INSERT_BY_TRY_HIT] Cycle: {} CPU: {} | Addr: {:#x} Hash: {} Data: [{:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}] | Inserted into MapTable\n", 
                  current_time.time_since_epoch() / clock_period, handle_pkt.cpu,
                  handle_pkt.address.to<uint64_t>(), 
                  map_idx,
                  way->data_cache_line[0], way->data_cache_line[1], way->data_cache_line[2], way->data_cache_line[3], way->data_cache_line[4], way->data_cache_line[5], way->data_cache_line[6], way->data_cache_line[7]);
          map_table[map_idx] = {true, (uint32_t)set_idx, (uint32_t)way_idx};
        }
      }
      }
    }

    // =================================================================
    // [L2C Directory] try_hit 시 l2c_upper_present 갱신
    // - WRITE hit: L1에서 dirty writeback → L1은 더 이상 이 라인을 보유하지 않음
    // - LOAD/RFO hit (to_return 있음): L1에 데이터가 전달됨 → L1이 보유하게 됨
    // =================================================================
    if (NAME.find("L2C") != std::string::npos) {
      long set_idx = get_set_index(handle_pkt.address);
      uint32_t flat_idx = set_idx * NUM_WAY + way_idx;
      
      if (handle_pkt.type == access_type::WRITE) {
        // L1 dirty writeback: L1은 이 라인을 evict함
        l2c_upper_present[flat_idx] = false;
      } else if (!handle_pkt.to_return.empty()) {
        // LOAD/RFO: 응답이 L1으로 전달됨 → L1이 이 라인을 보유
        l2c_upper_present[flat_idx] = true;
      }
    }

    uint64_t response_data = way->data_cache_line[get_word_index(handle_pkt.address)];
    response_type response{handle_pkt.address, handle_pkt.v_address, way->data, response_data, way->data_cache_line, metadata_thru, handle_pkt.instr_depend_on_me};
    // response_type response{handle_pkt.address, handle_pkt.v_address, way->data, metadata_thru, handle_pkt.instr_depend_on_me};
    for (auto* ret : handle_pkt.to_return) {
      ret->push_back(response);
    }

    // [XOR Cache] L1D/L2C write hit → LLC getM 알림
    // 주의: add_wq()는 응답을 기대하므로 MSHR 문제 발생
    // 해결: write_hit_notify_queue 사용 (응답 없음, getM 전용)
    if ((handle_pkt.type == access_type::WRITE || handle_pkt.type == access_type::RFO) 
        && !way->dirty  // S→M 전환 시에만
        && (NAME == "cpu0_L1D" || NAME == "cpu0_L2C" || NAME == "cpu1_L1D" || NAME == "cpu1_L2C")) {
      fmt::print("[{}_WRITE_HIT] Cycle: {} Addr: {:#x} OldData: [{:#x}] NewVal: {:#x} -> S->M transition (getM to LLC)\n",
                 NAME, current_time.time_since_epoch() / clock_period, handle_pkt.address.to<uint64_t>(), way->data_cache_line[0], handle_pkt.data_value);
      // write_hit_notify_queue를 사용해 LLC에 getM 알림
      channel_type::write_hit_notify_type notify{handle_pkt.address, handle_pkt.cpu};
      lower_level->write_hit_notify_queue.push_back(notify);
    }

    way->dirty |= (handle_pkt.type == access_type::WRITE);
    if (handle_pkt.type == access_type::WRITE) {
      long w_index = get_word_index(handle_pkt.address);
      way->data_cache_line[w_index] = handle_pkt.data_value;
    } else if (handle_pkt.type == access_type::LOAD) {
      long w_index = get_word_index(handle_pkt.address);
      way->data_cache_line[w_index] = handle_pkt.data_value;
    }

    // update prefetch stats and reset prefetch bit
    if (useful_prefetch) {
      ++sim_stats.pf_useful;
      way->prefetch = false;
    }
  }

  return hit;
}

auto CACHE::mshr_and_forward_packet(const tag_lookup_type& handle_pkt) -> std::pair<mshr_type, request_type>
{
  mshr_type to_allocate{handle_pkt, current_time};

  long w_index = get_word_index(handle_pkt.address);
  to_allocate.data_cache_line[w_index] = handle_pkt.data_value;

  request_type fwd_pkt;

  fwd_pkt.asid[0] = handle_pkt.asid[0];
  fwd_pkt.asid[1] = handle_pkt.asid[1];
  fwd_pkt.type = (handle_pkt.type == access_type::WRITE) ? access_type::RFO : handle_pkt.type;
  fwd_pkt.pf_metadata = handle_pkt.pf_metadata;
  fwd_pkt.cpu = handle_pkt.cpu;

  fwd_pkt.address = handle_pkt.address;
  fwd_pkt.v_address = handle_pkt.v_address;
  fwd_pkt.data = handle_pkt.data;
  fwd_pkt.data_value = handle_pkt.data_value;
  fwd_pkt.instr_id = handle_pkt.instr_id;
  fwd_pkt.ip = handle_pkt.ip;

  fwd_pkt.instr_depend_on_me = handle_pkt.instr_depend_on_me;
  fwd_pkt.response_requested = (!handle_pkt.prefetch_from_this || !handle_pkt.skip_fill);

  return std::pair{std::move(to_allocate), std::move(fwd_pkt)};
}

bool CACHE::handle_miss(const tag_lookup_type& handle_pkt)
{
  if constexpr (champsim::debug_print) {
    fmt::print("[{}] {} instr_id: {} address: {} v_address: {} type: {} local_prefetch: {} cycle: {}\n", NAME, __func__, handle_pkt.instr_id,
               handle_pkt.address, handle_pkt.v_address, access_type_names.at(champsim::to_underlying(handle_pkt.type)), handle_pkt.prefetch_from_this,
               current_time.time_since_epoch() / clock_period);
  }

  mshr_type to_allocate{handle_pkt, current_time};

  cpu = handle_pkt.cpu;

  auto mshr_pkt = mshr_and_forward_packet(handle_pkt);

  // check mshr
  auto mshr_entry = std::find_if(std::begin(MSHR), std::end(MSHR), matches_address(handle_pkt.address));
  bool mshr_full = (MSHR.size() == MSHR_SIZE);

  if (mshr_entry != MSHR.end()) // miss already inflight
  {
    if (mshr_entry->type == access_type::PREFETCH && handle_pkt.type != access_type::PREFETCH) {
      // Mark the prefetch as useful
      if (mshr_entry->prefetch_from_this) {
        ++sim_stats.pf_useful;
      }
    }

    // COLLECT STATS
    sim_stats.mshr_merge.increment(std::pair{to_allocate.type, to_allocate.cpu});

    *mshr_entry = mshr_type::merge(*mshr_entry, to_allocate);
  } else {
    if (mshr_full) { // not enough MSHR resource
      return false;  // TODO should we allow prefetches anyway if they will not be filled to this level?
    }

    const bool send_to_rq = (prefetch_as_load || handle_pkt.type != access_type::PREFETCH);
    bool success = send_to_rq ? lower_level->add_rq(mshr_pkt.second) : lower_level->add_pq(mshr_pkt.second);

    if (!success) {
      return false;
    }

    // Allocate an MSHR
    if (mshr_pkt.second.response_requested) {
      MSHR.emplace_back(std::move(mshr_pkt.first));
    }
  }

  sim_stats.misses.increment(std::pair{handle_pkt.type, handle_pkt.cpu});

  return true;
}

bool CACHE::handle_write(const tag_lookup_type& handle_pkt)
{
  if constexpr (champsim::debug_print) {
    fmt::print("[{}] {} instr_id: {} address: {} v_address: {} type: {} local_prefetch: {} cycle: {}\n", NAME, __func__, handle_pkt.instr_id,
               handle_pkt.address, handle_pkt.v_address, access_type_names.at(champsim::to_underlying(handle_pkt.type)), handle_pkt.prefetch_from_this,
               current_time.time_since_epoch() / clock_period);
  }

  mshr_type to_allocate{handle_pkt, current_time};
  to_allocate.data_promise.ready_at(current_time + (warmup ? champsim::chrono::clock::duration{} : FILL_LATENCY));
  inflight_writes.push_back(to_allocate);

  sim_stats.misses.increment(std::pair{handle_pkt.type, handle_pkt.cpu});

  return true;
}

template <bool UpdateRequest>
auto CACHE::initiate_tag_check(champsim::channel* ul)
{
  return [time = current_time + (warmup ? champsim::chrono::clock::duration{} : HIT_LATENCY), ul](const auto& entry) {
    CACHE::tag_lookup_type retval{entry};
    retval.event_cycle = time;

    if constexpr (UpdateRequest) {
      if (entry.response_requested) {
        retval.to_return = {&ul->returned};
      }
    } else {
      (void)ul; // supress warning about ul being unused
    }

    if constexpr (champsim::debug_print) {
      fmt::print("[TAG] initiate_tag_check instr_id: {} address: {} v_address: {} type: {} response_requested: {}\n", retval.instr_id, retval.address,
                 retval.v_address, access_type_names.at(champsim::to_underlying(retval.type)), !std::empty(retval.to_return));
    }

    return retval;
  };
}

long CACHE::operate()
{
  // if(llc_print_status && NAME == "LLC" && cpu == 1) {
  //   std::vector<long> sets_to_check = {10, 21};
  //   for (long set_idx : sets_to_check) {
  //       fmt::print("===== CPU{} Cache Set {} Status at Cycle {} =====\n", cpu, set_idx, current_time.time_since_epoch() / clock_period);
  //       auto set_begin = std::next(std::begin(this->block), set_idx * this->NUM_WAY);
  //       auto set_end = std::next(set_begin, this->NUM_WAY);
  //       int way = 0;
  //       // for (auto block_it = set_begin; block_it != set_end; ++block_it) {
  //       //     fmt::print("  [Way {}] Valid: {}, Address: 0x{:x} V_Address: 0x{:x} data: {}\n", way, block_it->valid, block_it->address.to<uint64_t>(), block_it->v_address.to<uint64_t>(), block_it->data);
  //       //     way++;
  //       // }
  //       for (auto block_it = set_begin; block_it != set_end; ++block_it) {
  //         fmt::print("  [Way {}] Valid: {}, Address: 0x{:x} V_Address: 0x{:x} data: {} cache_line: [{}]\n",
  //         way, block_it->valid, block_it->address.to<uint64_t>(), block_it->v_address.to<uint64_t>(), block_it->data,
  //         [&]() {
  //               std::string res;
  //               for (size_t i = 0; i < 8; ++i) {
  //                   // 각 요소를 16진수 문자열로 변환하여 이어 붙임
  //                   res += fmt::format("{:#018x}", block_it->data_cache_line[i]);
  //                   if (i < 7) res += ", ";
  //               }
  //               return res;
  //           }() // <--- 람다를 즉시 실행하여 결과 문자열(std::string)을 리턴받음
  //         );
  //           way++;
  //       }
  //   }
  //   llc_print_status = false;
  // }
  // if(NAME == "cpu0_L1D" || NAME == "cpu0_L2C" || NAME == "LLC") {


  if(NAME == "LLC") {
    std::vector<long> sets_to_check = {};
    for (long set_idx : sets_to_check) {
        fmt::print("===== CPU{} {} Cache Set {} Status at Cycle {} =====\n", cpu, NAME, set_idx, current_time.time_since_epoch() / clock_period);
        auto set_begin = std::next(std::begin(this->block), set_idx * this->NUM_WAY);
        auto set_end = std::next(set_begin, this->NUM_WAY);
        int way = 0;
        for (auto block_it = set_begin; block_it != set_end; ++block_it) {
            fmt::print("  [Way {}] Valid: {}, Address: 0x{:x} V_Address: 0x{:x} data: {} cache_line: [{}]\n",
    way,
    block_it->valid,
    block_it->address.to<uint64_t>(),
    block_it->v_address.to<uint64_t>(),
    block_it->data,
    // --- 여기서부터 수정 ---
    [&]() {
        std::string res;
        for (size_t i = 0; i < 8; ++i) {
            // 각 요소를 16진수 문자열로 변환하여 이어 붙임
            res += fmt::format("{:#018x}", block_it->data_cache_line[i]);
            if (i < 7) res += ", ";
        }
        return res;
    }() // <--- 람다를 즉시 실행하여 결과 문자열(std::string)을 리턴받음
    // -----------------------
      );
        way++;
      }
    }
  }

  long progress{0};

  auto is_ready = [time = current_time](const auto& entry) {
    return entry.event_cycle <= time;
  };
  auto is_translated = [](const auto& entry) {
    return entry.is_translated;
  };

  for (auto* ul : upper_levels) {
    ul->check_collision();
  }

  // Finish returns
  std::for_each(std::cbegin(lower_level->returned), std::cend(lower_level->returned), [this](const auto& pkt) { this->finish_packet(pkt); });
  progress += std::distance(std::cbegin(lower_level->returned), std::cend(lower_level->returned));
  lower_level->returned.clear();

  // Finish translations
  if (lower_translate != nullptr) {
    std::for_each(std::cbegin(lower_translate->returned), std::cend(lower_translate->returned), [this](const auto& pkt) { this->finish_translation(pkt); });
    progress += std::distance(std::cbegin(lower_translate->returned), std::cend(lower_translate->returned));
    lower_translate->returned.clear();
  }

  // =================================================================
  // [L2C Directory] L1 putS 처리: L1에서 clean eviction 시 l2c_upper_present 갱신
  // 반드시 general invalidation 처리 전에 수행해야 함
  // (general 처리 중 L2C→L1 invalidation이 같은 큐에 push될 수 있으므로)
  // =================================================================
  if (NAME.find("L2C") != std::string::npos) {
    for (auto* ul : upper_levels) {
      for (const auto& inv : ul->invalidation_queue) {
        auto [begin, end] = get_set_span(inv.address);
        auto inv_way = std::find_if(begin, end, [matcher = matches_address(inv.address)](const auto& x) { return x.valid && matcher(x); });
        if (inv_way != end) {
          long set_idx = get_set_index(inv.address);
          long way_idx = std::distance(begin, inv_way);
          uint32_t flat_idx = set_idx * NUM_WAY + way_idx;
          l2c_upper_present[flat_idx] = false;
          fmt::print("[L2C_RECV_L1_PUTS] Cycle: {} Addr: {:#x} Set: {} Way: {} -> L1 clean eviction, cleared upper_present\n",
                     current_time.time_since_epoch() / clock_period, inv.address.to<uint64_t>(),
                     set_idx, way_idx);
        }
      }
      ul->invalidation_queue.clear();
    }
  }

  // [Inclusive Policy] LLC eviction 시 상위 캐시도 invalidate하기 위한 기존 코드
  std::for_each(std::cbegin(lower_level->invalidation_queue), std::cend(lower_level->invalidation_queue),
                [this](const auto& inv) {
                    this->invalidate_entry(inv.address); 
                });
  lower_level->invalidation_queue.clear();

  // [XOR Cache] LLC에서 상위 캐시(L2C)로부터 온 putS 처리
  // L2C가 clean eviction 시 lower_level(LLC 채널)의 invalidation_queue에 넣음
  // LLC는 upper_levels를 통해 이를 읽어야 함
  // source_cpu를 사용하여 해당 CPU의 sharer만 제거
  if (NAME == "LLC") {
    for (auto* ul : upper_levels) {
      for (const auto& inv : ul->invalidation_queue) {
        this->invalidate_entry(inv.address, inv.source_cpu);
      }
      ul->invalidation_queue.clear();
      
      // [XOR Cache] L2C로부터 온 getM (write hit) 알림 처리
      for (const auto& notify : ul->write_hit_notify_queue) {
        this->handle_getM(notify.address, notify.cpu_id);
      }
      ul->write_hit_notify_queue.clear();
    }
  }
  
  // [XOR Cache] L2C에서 L1D로부터 온 getM 알림을 LLC로 전달
  if (NAME == "cpu0_L2C" || NAME == "cpu1_L2C") {
    for (auto* ul : upper_levels) {
      for (const auto& notify : ul->write_hit_notify_queue) {
        // L1D의 알림을 LLC로 전달
        lower_level->write_hit_notify_queue.push_back(notify);
      }
      ul->write_hit_notify_queue.clear();
    }
  }

  // Perform fills
  champsim::bandwidth fill_bw{MAX_FILL};
  for (auto q : {std::ref(MSHR), std::ref(inflight_writes)}) {
    auto [fill_begin, fill_end] = champsim::get_span_p(std::cbegin(q.get()), std::cend(q.get()), fill_bw,
                                                       [time = current_time](const auto& x) { return x.data_promise.is_ready_at(time); });
    auto complete_end = std::find_if_not(fill_begin, fill_end, [this](const auto& x) { return this->handle_fill(x); });
    fill_bw.consume(std::distance(fill_begin, complete_end));
    q.get().erase(fill_begin, complete_end);
  }

  // Initiate tag checks
  const champsim::bandwidth::maximum_type bandwidth_from_tag_checks{champsim::to_underlying(MAX_TAG) * (long)(HIT_LATENCY / clock_period)
                                                                    - (long)std::size(inflight_tag_check)};
  champsim::bandwidth initiate_tag_bw{std::clamp(bandwidth_from_tag_checks, champsim::bandwidth::maximum_type{0}, MAX_TAG)};
  auto can_translate = [avail = (std::size(translation_stash) < static_cast<std::size_t>(MSHR_SIZE))](const auto& entry) {
    return avail || entry.is_translated;
  };
  auto stash_bandwidth_consumed =
      champsim::transform_while_n(translation_stash, std::back_inserter(inflight_tag_check), initiate_tag_bw, is_translated, initiate_tag_check<false>());
  initiate_tag_bw.consume(stash_bandwidth_consumed);
  std::vector<long long> channels_bandwidth_consumed{};

  if (std::size(upper_levels) > 1) {
    std::rotate(upper_levels.begin(), upper_levels.begin() + 1, upper_levels.end());
  }

  // upper levels get an equal portion of the remaining bandwidth
  champsim::bandwidth::maximum_type per_upper_bandwidth =
      std::size(upper_levels) >= 1
          ? (champsim::bandwidth::maximum_type)std::max((size_t)initiate_tag_bw.amount_remaining() / std::size(upper_levels), size_t{1})
          : champsim::bandwidth::maximum_type{};

  for (auto* ul : upper_levels) {
    for (auto q : {std::ref(ul->WQ), std::ref(ul->RQ), std::ref(ul->PQ)}) {
      // this needs to be in this loop, we need to ensure that for cases where bandwidth doesn't divide nicely across upstreams,
      // we don't accidentally consume more bandwidth than expected
      champsim::bandwidth per_upper_tag_bw{std::min(per_upper_bandwidth, champsim::bandwidth::maximum_type{initiate_tag_bw.amount_remaining()})};
      auto bandwidth_consumed =
          champsim::transform_while_n(q.get(), std::back_inserter(inflight_tag_check), per_upper_tag_bw, can_translate, initiate_tag_check<true>(ul));
      channels_bandwidth_consumed.push_back(bandwidth_consumed);
      initiate_tag_bw.consume(bandwidth_consumed);
    }
  }

  auto pq_bandwidth_consumed =
      champsim::transform_while_n(internal_PQ, std::back_inserter(inflight_tag_check), initiate_tag_bw, can_translate, initiate_tag_check<false>());
  initiate_tag_bw.consume(pq_bandwidth_consumed);

  // Issue translations
  std::for_each(std::begin(inflight_tag_check), std::end(inflight_tag_check), [this](auto& x) { this->issue_translation(x); });
  std::for_each(std::begin(translation_stash), std::end(translation_stash), [this](auto& x) { this->issue_translation(x); });

  // Find entries that would be ready except that they have not finished translation, move them to the stash
  auto [last_not_missed, stash_end] = champsim::extract_if(std::begin(inflight_tag_check), std::end(inflight_tag_check), std::back_inserter(translation_stash),
                                                           [is_ready, is_translated](const auto& x) { return is_ready(x) && !is_translated(x); });
  progress += std::distance(last_not_missed, std::end(inflight_tag_check));
  inflight_tag_check.erase(last_not_missed, std::end(inflight_tag_check));

  // Perform tag checks
  auto do_handle_miss = [this](const auto& pkt) {
    if (pkt.type == access_type::WRITE && !this->match_offset_bits) {
      return this->handle_write(pkt); // Treat writes (that is, writebacks) like fills
    }
    return this->handle_miss(pkt); // Treat writes (that is, stores) like reads
  };
  champsim::bandwidth tag_check_bw{MAX_TAG};
  auto [tag_check_ready_begin, tag_check_ready_end] =
      champsim::get_span_p(std::begin(inflight_tag_check), std::end(inflight_tag_check), tag_check_bw,
                           [is_ready, is_translated](const auto& pkt) { return is_ready(pkt) && is_translated(pkt); });
  auto hits_end = std::stable_partition(tag_check_ready_begin, tag_check_ready_end, [this](const auto& pkt) { return this->try_hit(pkt); });
  auto finish_tag_check_end = std::stable_partition(hits_end, tag_check_ready_end, do_handle_miss);
  tag_check_bw.consume(std::distance(tag_check_ready_begin, finish_tag_check_end));
  inflight_tag_check.erase(tag_check_ready_begin, finish_tag_check_end);

  impl_prefetcher_cycle_operate();

  if constexpr (champsim::debug_print) {
    fmt::print("[{}] {} cycle completed: {} tags checked: {} remaining: {} stash consumed: {} remaining: {} channel consumed: {} pq consumed {} unused consume "
               "bw {}\n",
               NAME, __func__, current_time.time_since_epoch() / clock_period, tag_check_bw.amount_consumed(), std::size(inflight_tag_check),
               stash_bandwidth_consumed, std::size(translation_stash), channels_bandwidth_consumed, pq_bandwidth_consumed, initiate_tag_bw.amount_remaining());
  }

  return progress + fill_bw.amount_consumed() + initiate_tag_bw.amount_consumed() + tag_check_bw.amount_consumed();
}

long get_word_index(champsim::address address) 
{
  return address.slice(champsim::dynamic_extent{champsim::data::bits{6}, champsim::data::bits{3}}).to<long>(); 
}

uint32_t CACHE::get_sbl_hash(const std::array<uint64_t, 8>& data) {
    if (!hash_tables_initialized) init_hash_tables();

    // Sparse Byte Labeling: only consider the most significant 6 bytes per 8-byte word
    // For each word, skip the 2 least significant bytes (bits [0..15])
    // Generate boolean labels: 0 if byte == 0x00, 1 otherwise
    std::array<uint8_t, SBL_TOTAL_BYTES> labels{};
    uint32_t label_idx = 0;
    for (uint32_t w = 0; w < WORDS_PER_LINE; w++) {
        // Bytes [2..7] of each word (MSB 6 bytes, skip 2 LSBs)
        for (uint32_t b = 2; b < BYTES_PER_WORD; b++) {
            uint8_t byte_val = (data[w] >> (b * 8)) & 0xFF;
            labels[label_idx++] = (byte_val != 0) ? 1 : 0;
        }
    }

    // Permute labels using precomputed permutation
    std::array<uint8_t, SBL_TOTAL_BYTES> permuted{};
    for (uint32_t i = 0; i < SBL_TOTAL_BYTES; i++) {
        permuted[i] = labels[sbl_permutation[i]];
    }

    // XOR fold into MAP_HASH_BITS
    uint32_t hash = 0;
    for (uint32_t i = 0; i < SBL_TOTAL_BYTES; i++) {
        if (permuted[i]) {
            hash ^= (1u << (i % MAP_HASH_BITS));
        }
    }
    return hash % MAP_TABLE_SIZE;
}

// ====== LSH-RP: Locality-Sensitive Hash - Random Projection ======
// For each output bit, compute the dot product of the cache line bytes
// with a random vector of +1/-1 values. The sign of the result is the hash bit.
uint32_t CACHE::get_lsh_rp_hash(const std::array<uint64_t, 8>& data) {
    if (!hash_tables_initialized) init_hash_tables();

    // Extract all 64 bytes from the cache line
    std::array<uint8_t, CACHE_LINE_BYTES> bytes{};
    for (uint32_t w = 0; w < WORDS_PER_LINE; w++) {
        for (uint32_t b = 0; b < BYTES_PER_WORD; b++) {
            bytes[w * BYTES_PER_WORD + b] = (data[w] >> (b * 8)) & 0xFF;
        }
    }

    uint32_t hash = 0;
    for (uint32_t bit = 0; bit < MAP_HASH_BITS; bit++) {
        // Dot product of byte values with random projection vector (+1/-1)
        int32_t dot_product = 0;
        for (uint32_t i = 0; i < CACHE_LINE_BYTES; i++) {
            dot_product += static_cast<int32_t>(bytes[i]) * lsh_rp_projection[bit][i];
        }
        // Sign of dot product determines the hash bit (1 if positive, 0 if non-positive)
        if (dot_product > 0) {
            hash |= (1u << bit);
        }
    }
    return hash % MAP_TABLE_SIZE;
}

// ====== LSH-BS: Locality-Sensitive Hash - Bit Sampling ======
// For each output bit, randomly select one bit position from the cache line (512 bits).
// The value at that position becomes the hash bit.
uint32_t CACHE::get_lsh_bs_hash(const std::array<uint64_t, 8>& data) {
    if (!hash_tables_initialized) init_hash_tables();

    uint32_t hash = 0;
    for (uint32_t bit = 0; bit < MAP_HASH_BITS; bit++) {
        uint32_t bit_pos = lsh_bs_bit_positions[bit];  // position in [0, 511]
        uint32_t word_idx = bit_pos / 64;
        uint32_t bit_in_word = bit_pos % 64;
        if ((data[word_idx] >> bit_in_word) & 1) {
            hash |= (1u << bit);
        }
    }
    return hash % MAP_TABLE_SIZE;
}

// ====== BL: Baseline Byte Labeling ======
// For every byte in the cache line (64 bytes), generate label 0 if byte==0x00, else 1.
// Permute the labels, then XOR fold into the map value.
uint32_t CACHE::get_bl_hash(const std::array<uint64_t, 8>& data) {
    if (!hash_tables_initialized) init_hash_tables();

    // Generate boolean labels for all 64 bytes
    std::array<uint8_t, CACHE_LINE_BYTES> labels{};
    for (uint32_t w = 0; w < WORDS_PER_LINE; w++) {
        for (uint32_t b = 0; b < BYTES_PER_WORD; b++) {
            uint8_t byte_val = (data[w] >> (b * 8)) & 0xFF;
            labels[w * BYTES_PER_WORD + b] = (byte_val != 0) ? 1 : 0;
        }
    }

    // Permute labels using precomputed permutation
    std::array<uint8_t, CACHE_LINE_BYTES> permuted{};
    for (uint32_t i = 0; i < CACHE_LINE_BYTES; i++) {
        permuted[i] = labels[bl_permutation[i]];
    }

    // XOR fold into MAP_HASH_BITS
    uint32_t hash = 0;
    for (uint32_t i = 0; i < CACHE_LINE_BYTES; i++) {
        if (permuted[i]) {
            hash ^= (1u << (i % MAP_HASH_BITS));
        }
    }
    return hash % MAP_TABLE_SIZE;
}

// ====== Map Hash Dispatcher ======
// Routes to the active hash function based on active_hash_function setting
uint32_t CACHE::get_map_hash(const std::array<uint64_t, 8>& data) {
    switch (active_hash_function) {
        case MapHashFunction::LSH_RP: return get_lsh_rp_hash(data);
        case MapHashFunction::LSH_BS: return get_lsh_bs_hash(data);
        case MapHashFunction::BL:     return get_bl_hash(data);
        case MapHashFunction::SBL:    return get_sbl_hash(data);
        default:                      return get_sbl_hash(data);
    }
}

// ====== Initialize Precomputed Random Tables ======
// Uses a fixed seed for reproducibility across simulation runs.
void CACHE::init_hash_tables() {
    std::mt19937 rng(MAP_HASH_SEED);

    // --- LSH-RP: Random projection vectors (+1 or -1) ---
    std::uniform_int_distribution<int> coin(0, 1);
    for (uint32_t bit = 0; bit < MAP_HASH_BITS; bit++) {
        for (uint32_t i = 0; i < CACHE_LINE_BYTES; i++) {
            lsh_rp_projection[bit][i] = coin(rng) ? 1 : -1;
        }
    }

    // --- LSH-BS: Random bit positions in [0, CACHE_LINE_BITS) ---
    std::uniform_int_distribution<uint32_t> bit_dist(0, CACHE_LINE_BITS - 1);
    for (uint32_t bit = 0; bit < MAP_HASH_BITS; bit++) {
        lsh_bs_bit_positions[bit] = bit_dist(rng);
    }

    // --- BL: Random permutation of [0, CACHE_LINE_BYTES) ---
    std::iota(bl_permutation.begin(), bl_permutation.end(), 0);
    std::shuffle(bl_permutation.begin(), bl_permutation.end(), rng);

    // --- SBL: Random permutation of [0, SBL_TOTAL_BYTES) ---
    std::iota(sbl_permutation.begin(), sbl_permutation.end(), 0);
    std::shuffle(sbl_permutation.begin(), sbl_permutation.end(), rng);

    hash_tables_initialized = true;
}

// [XOR Cache] getM 처리: 상위 캐시에서 S→M 전환 시 호출
void CACHE::handle_getM(champsim::address addr, uint32_t cpu_id) {
    for(int idx = 0; idx < MAP_TABLE_SIZE; idx++) {
        if(map_table[idx].valid) {
            fmt::print("[MAP_TABLE_STATUS] Cycle: {} Index: {} Valid: {} Set: {} Way: {}\n",
                       current_time.time_since_epoch() / clock_period, idx, map_table[idx].valid,
                       map_table[idx].set_index, map_table[idx].way_index);
        }
    }

    auto [begin, end] = get_set_span(addr);
    auto way = std::find_if(begin, end, matches_address(addr));
    
    if (way == end) {
        fmt::print("[LLC_GETM_MISS] Cycle: {} Addr: {:#x} not found in LLC\n",
                   current_time.time_since_epoch() / clock_period, addr.to<uint64_t>());
        return;
    }
    
    long set_idx = get_set_index(addr);
    long way_idx = std::distance(begin, way);
    uint32_t flat_idx = set_idx * NUM_WAY + way_idx;
    
    fmt::print("[LLC_GETM] Cycle: {} Addr: {:#x} Set: {} Way: {} CPU: {} is_xored: {} Data: [{:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}, {:#x}]\n",
               current_time.time_since_epoch() / clock_period, addr.to<uint64_t>(),
               set_idx, way_idx, cpu_id, xor_metadata[flat_idx].is_xored, way->data_cache_line[0], way->data_cache_line[1], way->data_cache_line[2], way->data_cache_line[3], way->data_cache_line[4], way->data_cache_line[5], way->data_cache_line[6], way->data_cache_line[7]);
    
    // [멀티코어] Directory 기반 Invalidation: 다른 sharer들에게 invalidate 전송
    // getM은 exclusive access를 요구하므로 다른 코어의 복사본을 무효화해야 함
    // 모든 상위 캐시에 invalidation 전송 (ChampSim에서 upper_levels 순서가 CPU ID와 다를 수 있음)
    auto invalidator = channel_type::invalidator_for(addr);
    bool has_other_sharers = false;
    for (size_t i = 0; i < directory[flat_idx].sharers.size(); ++i) {
        if (directory[flat_idx].sharers[i] && i != cpu_id) {
            has_other_sharers = true;
            directory[flat_idx].sharers[i] = false;  // sharer 목록에서 제거
        }
    }
    
    // 다른 sharer가 있으면 모든 상위 캐시에 invalidation 전송
    if (has_other_sharers) {
        for (auto* ul : upper_levels) {
            invalidator(ul);
        }
        fmt::print("[LLC_GETM_INVALIDATE] Cycle: {} Addr: {:#x} | Sent invalidation to all upper caches (requested by CPU {})\n",
                   current_time.time_since_epoch() / clock_period, addr.to<uint64_t>(), cpu_id);
    }
    
    // 요청 코어만 sharer로 설정 (M 상태)
    directory[flat_idx].sharers[cpu_id] = true;
    // [XOR Cache] exclusive_owner 설정 (M 상태 표시)
    directory[flat_idx].exclusive_owner = cpu_id;
    
    // [XOR Cache] getM된 라인은 Exclusive/Modified 상태이므로 Map Table에서 먼저 제거
    // 더 이상 XOR 압축 대상이 아님 (다른 라인과 re-XOR 방지)
    // 반드시 break_xor_relationship 호출 전에 제거해야 partner의 re-XOR 시 매칭되지 않음
    uint32_t map_idx = get_map_hash(way->data_cache_line);
    if (map_table[map_idx].valid && 
        map_table[map_idx].set_index == (uint32_t)set_idx && 
        map_table[map_idx].way_index == (uint32_t)way_idx) {
        map_table[map_idx].valid = false;
        fmt::print("[MAP_TABLE_REMOVE_GETM] Cycle: {} Addr: {:#x} Set: {} Way: {} Hash: {} | Line exclusive, removed from MapTable\n",
                   current_time.time_since_epoch() / clock_period, addr.to<uint64_t>(),
                   set_idx, way_idx, map_idx);
    }

    // [XOR Cache] XORed 라인에 getM 발생 시 unXOR
    // MSI 기반 프로토콜에서 getM은 exclusive access 요구
    // XORed 상태에서는 데이터 복구가 필요하므로 unXOR 필수
    if (xor_metadata[flat_idx].is_xored) {
        auto block_it = std::next(std::begin(this->block), flat_idx);
        uint32_t p_set = xor_metadata[flat_idx].partner_set;
        uint32_t p_way = xor_metadata[flat_idx].partner_way;
        auto partner_it = std::next(std::begin(this->block), p_set * NUM_WAY + p_way);
        fmt::print("[UNXOR_getM] Cycle: {} CPU: {} Addr: {:#x} Data: [{:#x}] | Partner: {:#x} Data: [{:#x}] | Set: {} Way: {} | getM from upper cache\n",
                   current_time.time_since_epoch() / clock_period, cpu_id, addr.to<uint64_t>(),
                   block_it->data_cache_line[0], partner_it->address.to<uint64_t>(),
                   partner_it->data_cache_line[0], set_idx, way_idx);
        break_xor_relationship((uint32_t)set_idx, (uint32_t)way_idx);
    }
}

void CACHE::break_xor_relationship(uint32_t set, uint32_t way) {
    uint32_t idx = set * NUM_WAY + way;
    
    if (xor_metadata[idx].is_xored) {
        uint32_t p_set = xor_metadata[idx].partner_set;
        uint32_t p_way = xor_metadata[idx].partner_way;
        uint32_t p_idx = p_set * NUM_WAY + p_way;

        xor_metadata[p_idx].is_xored = false;
        xor_metadata[idx].is_xored = false;

        sim_stats.unxorings++;

        // =================================================================
        // [Re-insertion] 논문 4.4.3: recovered line B가 re-insertion 시도
        // XOR 압축 조건: 둘 다 M이 아닐 것 (exclusive_owner == -1)
        // - S0 (sharer=0) + S (sharer>=1) = OK
        // - S + S = OK
        // - M (exclusive_owner>=0) + anything = NO
        // =================================================================
        auto partner_block_it = std::next(std::begin(this->block), p_idx);
        if (partner_block_it->valid) {
            // Partner가 Modified면 RE-XOR 불가
            if (is_line_modified(p_idx)) {
                fmt::print("[SKIP_RE-XOR] Cycle: {} | Partner Set: {} Way: {} | Partner is Modified, cannot RE-XOR\n",
                      current_time.time_since_epoch() / clock_period, p_set, p_way);
                return;
            }

            uint32_t map_idx = get_map_hash(partner_block_it->data_cache_line);

            if (map_table[map_idx].valid) {
                // Map Table에 후보가 있음 -> XOR 압축 재시도
                uint32_t c_set = map_table[map_idx].set_index;
                uint32_t c_way = map_table[map_idx].way_index;
                uint32_t c_flat_idx = c_set * NUM_WAY + c_way;

                auto candidate_block_it = std::next(std::begin(this->block), c_flat_idx);

                // XOR 압축 조건:
                // 1. 자기 자신이 아님
                // 2. 유효한 블록
                // 3. 이미 XOR되지 않음
                // 4. [핵심] Candidate가 Modified가 아님 (M 상태면 write 가능성)
                if (p_idx != c_flat_idx && candidate_block_it->valid && 
                    !xor_metadata[c_flat_idx].is_xored && !is_line_modified(c_flat_idx)) {
                    const char* partner_state = is_line_s0(p_idx) ? "S0" : "S";
                    const char* candidate_state = is_line_s0(c_flat_idx) ? "S0" : "S";
                    // 새로운 XOR 관계 형성
                    xor_metadata[p_idx] = {true, c_set, c_way};
                    xor_metadata[c_flat_idx] = {true, p_set, p_way};
                    map_table[map_idx].valid = false;
                    sim_stats.xor_compressions++;
                    fmt::print("[RE-XOR_SUCCESS] Cycle: {} | PartnerAddr: {:#x} PartnerData: [{:#x}, {:#x}] ({}) | CandidateAddr: {:#x} CandidateData: [{:#x}, {:#x}] ({}) | Pair: {}+{} | Hash: {} | Set: {} Way: {} <-> Set: {} Way: {}\n",
                          current_time.time_since_epoch() / clock_period, 
                          partner_block_it->address.to<uint64_t>(),
                          partner_block_it->data_cache_line[0], partner_block_it->data_cache_line[1],
                          partner_state,
                          candidate_block_it->address.to<uint64_t>(),
                          candidate_block_it->data_cache_line[0], candidate_block_it->data_cache_line[1],
                          candidate_state,
                          partner_state, candidate_state,
                          map_idx,
                          p_set, p_way, c_set, c_way);
                } else {
                    // 후보가 부적합 (Modified 포함) -> Map Table 갱신
                    if (is_line_modified(c_flat_idx)) {
                        fmt::print("[RE-XOR_SKIP_CANDIDATE] Cycle: {} | Candidate Set: {} Way: {} is Modified, skipping\n",
                              current_time.time_since_epoch() / clock_period, c_set, c_way);
                    }
                    map_table[map_idx] = {true, p_set, p_way};
                    fmt::print("[RE-XOR_UPDATE] Cycle: {} Partner Set: {} Way: {} | Updated MapTable\n",
                          current_time.time_since_epoch() / clock_period, p_set, p_way);
                }
            } else {
                // Map Table에 후보 없음 -> 등록
                map_table[map_idx] = {true, p_set, p_way};
                fmt::print("[RE-XOR_INSERT] Cycle: {} Partner Set: {} Way: {} | Inserted into MapTable\n",
                      current_time.time_since_epoch() / clock_period, p_set, p_way);
            }
        }
    }
}

// [XOR Cache] Modified 상태 확인: exclusive_owner가 있으면 M 상태
// - M (exclusive_owner >= 0): 한 코어가 exclusive write access 보유 → XOR 불가
// - S (sharer≥1, no exclusive_owner): clean copy 보유 → XOR 가능
// - S0 (sharer=0): LLC에만 존재 → XOR 가능
bool CACHE::is_line_modified(uint32_t flat_idx) {
    if (flat_idx >= directory.size()) return false;
    
    // exclusive_owner가 설정되어 있으면 M 상태 (getM을 받음)
    bool is_modified = (directory[flat_idx].exclusive_owner >= 0);
    if (is_modified) {
        auto block_it = std::next(std::begin(this->block), flat_idx);
        if (block_it->valid) {
            fmt::print("[IS_MODIFIED] flat_idx: {} Addr: {:#x} exclusive_owner: CPU {} -> Modified (XOR ineligible)\n",
                  flat_idx, block_it->address.to<uint64_t>(), directory[flat_idx].exclusive_owner);
        }
    }
    return is_modified;
}

// [XOR Cache] S0 상태 확인: sharer가 0명이고 exclusive_owner도 없는 상태
// LLC에만 존재하고 상위 캐시에는 사본이 없는 상태 → XOR 압축 가능
bool CACHE::is_line_s0(uint32_t flat_idx) {
    if (flat_idx >= directory.size()) return false;
    
    // exclusive_owner가 있으면 M 상태 (S0 아님)
    if (directory[flat_idx].exclusive_owner >= 0) return false;
    
    // 어떤 코어라도 sharer면 S 상태 (S0 아님)
    for (size_t i = 0; i < directory[flat_idx].sharers.size(); ++i) {
        if (directory[flat_idx].sharers[i]) return false;
    }
    
    return true;  // sharer 없음, exclusive_owner 없음 → S0
}

// LCOV_EXCL_START exclude deprecated function
uint64_t CACHE::get_set(uint64_t address) const { return static_cast<uint64_t>(get_set_index(champsim::address{address})); }
// LCOV_EXCL_STOP

long CACHE::get_set_index(champsim::address address) const { return address.slice(champsim::dynamic_extent{OFFSET_BITS, champsim::lg2(NUM_SET)}).to<long>(); }

template <typename It>
std::pair<It, It> get_span(It anchor, typename std::iterator_traits<It>::difference_type set_idx, typename std::iterator_traits<It>::difference_type num_way)
{
  auto begin = std::next(anchor, set_idx * num_way);
  return {std::move(begin), std::next(begin, num_way)};
}

auto CACHE::get_set_span(champsim::address address) -> std::pair<set_type::iterator, set_type::iterator>
{
  const auto set_idx = get_set_index(address);
  assert(set_idx < NUM_SET);
  return get_span(std::begin(block), static_cast<set_type::difference_type>(set_idx), NUM_WAY); // safe cast because of prior assert
}

auto CACHE::get_set_span(champsim::address address) const -> std::pair<set_type::const_iterator, set_type::const_iterator>
{
  const auto set_idx = get_set_index(address);
  assert(set_idx < NUM_SET);
  return get_span(std::cbegin(block), static_cast<set_type::difference_type>(set_idx), NUM_WAY); // safe cast because of prior assert
}

// LCOV_EXCL_START exclude deprecated function
uint64_t CACHE::get_way(uint64_t address, uint64_t /*unused set index*/) const
{
  champsim::address intern_addr{address};
  auto [begin, end] = get_set_span(intern_addr);
  return static_cast<uint64_t>(std::distance(begin, std::find_if(begin, end, matches_address(champsim::address{address}))));
}
// LCOV_EXCL_STOP

long CACHE::invalidate_entry(champsim::address inval_addr)
{
  return invalidate_entry(inval_addr, std::numeric_limits<uint32_t>::max());
}

long CACHE::invalidate_entry(champsim::address inval_addr, uint32_t source_cpu)
{
  auto [begin, end] = get_set_span(inval_addr);
  auto inv_way = std::find_if(begin, end, matches_address(inval_addr));

  if (inv_way != end) {
    // LLC에서는 블록을 무효화하지 않고, directory만 업데이트 (putS 처리)
    if (NAME == "LLC") {
      long set_idx = get_set_index(inval_addr);
      long way_idx = std::distance(begin, inv_way);
      uint32_t flat_idx = set_idx * NUM_WAY + way_idx;
      
      fmt::print("[LLC_PUTS_RECEIVED] Cycle: {} Addr: {:#x} Set: {} Way: {} flat_idx: {} source_cpu: {}\n",
                 current_time.time_since_epoch() / clock_period, inval_addr.to<uint64_t>(),
                 set_idx, way_idx, flat_idx, source_cpu);
      
      // [Per-CPU sharer removal] source_cpu가 지정된 경우 해당 CPU만 제거
      // source_cpu가 max인 경우 (일반 invalidation) 모든 sharer 제거
      bool had_sharers = false;
      if (source_cpu < directory[flat_idx].sharers.size()) {
        // 특정 CPU의 sharer만 제거 (L2C putS)
        if (directory[flat_idx].sharers[source_cpu]) {
          had_sharers = true;
          directory[flat_idx].sharers[source_cpu] = false;
        }
      } else {
        // 모든 sharer 제거 (일반 invalidation)
        for (size_t i = 0; i < directory[flat_idx].sharers.size(); ++i) {
          if (directory[flat_idx].sharers[i]) {
            had_sharers = true;
            directory[flat_idx].sharers[i] = false;
          }
        }
      }
      
      // [XOR Cache] exclusive_owner 해제
      // source_cpu가 지정된 경우 해당 CPU가 owner일 때만 해제
      // 일반 invalidation인 경우 무조건 해제
      if (directory[flat_idx].exclusive_owner >= 0) {
        bool should_clear = (source_cpu >= directory[flat_idx].sharers.size()) || 
                            (directory[flat_idx].exclusive_owner == (int)source_cpu);
        if (should_clear) {
          fmt::print("[LLC_PUTS_CLEAR_OWNER] Cycle: {} Addr: {:#x} | Clearing exclusive_owner (was CPU {})\n",
                     current_time.time_since_epoch() / clock_period, inval_addr.to<uint64_t>(),
                     directory[flat_idx].exclusive_owner);
          directory[flat_idx].exclusive_owner = -1;
        }
      }
      
      fmt::print("[LLC_PUTS_DEBUG] had_sharers: {} is_xored: {}\n", had_sharers, xor_metadata[flat_idx].is_xored);
      
      // XORed 라인인 경우 Minimum Sharer Invariant 체크
      if (xor_metadata[flat_idx].is_xored && had_sharers) {
        uint32_t p_set = xor_metadata[flat_idx].partner_set;
        uint32_t p_way = xor_metadata[flat_idx].partner_way;
        uint32_t p_flat_idx = p_set * NUM_WAY + p_way;
        
        // 현재 라인의 sharer 확인
        bool current_has_sharer = false;
        for (size_t i = 0; i < directory[flat_idx].sharers.size(); ++i) {
          if (directory[flat_idx].sharers[i]) {
            current_has_sharer = true;
            break;
          }
        }
        
        // 파트너 라인의 sharer 확인
        bool partner_has_sharer = false;
        if (p_flat_idx < directory.size()) {
          for (size_t i = 0; i < directory[p_flat_idx].sharers.size(); ++i) {
            if (directory[p_flat_idx].sharers[i]) {
              partner_has_sharer = true;
              break;
            }
          }
        }
        
        fmt::print("[LLC_PUTS_DEBUG] Partner: Set {} Way {} | current_has_sharer: {} partner_has_sharer: {}\n",
                   p_set, p_way, current_has_sharer, partner_has_sharer);
        
        // 둘 다 sharer가 없으면 (S0, S0) → unXOR 필요!
        if (!current_has_sharer && !partner_has_sharer) {
          fmt::print("[UNXOR_lastPutS] Cycle: {} Addr: {:#x} | Both lines S0 (no sharers) -> unXORing\n",
                     current_time.time_since_epoch() / clock_period, inval_addr.to<uint64_t>());
          break_xor_relationship((uint32_t)set_idx, (uint32_t)way_idx);
        }
      }
      
      // LLC에서는 블록 자체는 유효하게 유지 (S0 상태)
      return std::distance(begin, inv_way);
    }
    
    // =================================================================
    // [L2C Inclusive Policy] LLC에서 온 invalidation을 L1에도 전달
    // L2C 블록이 무효화될 때 L1에 사본이 있으면 함께 무효화
    // =================================================================
    if (NAME.find("L2C") != std::string::npos) {
      long set_idx = get_set_index(inval_addr);
      long way_idx = std::distance(begin, inv_way);
      uint32_t flat_idx = set_idx * NUM_WAY + way_idx;
      
      if (l2c_upper_present[flat_idx]) {
        auto invalidator = channel_type::invalidator_for(inval_addr);
        for (auto* ul : upper_levels) {
          invalidator(ul);
        }
        l2c_upper_present[flat_idx] = false;
        fmt::print("[L2C_INVAL_FORWARD_L1] Cycle: {} Addr: {:#x} Set: {} Way: {} -> forwarding invalidation to L1 (inclusive policy)\n",
                   current_time.time_since_epoch() / clock_period, inval_addr.to<uint64_t>(),
                   set_idx, way_idx);
      }
    }

    // 다른 캐시(L1/L2)에서는 기존처럼 무효화
    inv_way->valid = false;
  }

  return std::distance(begin, inv_way);
}

bool CACHE::invalidate_entry(BLOCK& inval_block)
{
  bool was_dirty = inval_block.dirty;

  // 1. Directory(Sharer List) 확인 및 상위 캐시 요청
  uint32_t set_idx = get_set_index(inval_block.address);
  
  // 포인터 연산으로 flat index 계산
  auto block_start = std::begin(this->block);
  auto current_block_iter = (std::vector<BLOCK>::iterator)&inval_block;
  long flat_idx = std::distance(block_start, current_block_iter);
  
  // Directory 범위 체크
  if (flat_idx >= 0 && flat_idx < (long)directory.size()) {
      
      // ChampSim 표준 Invalidator 생성 (주소를 받아 패킷 생성기를 만듦)
      auto invalidator = channel_type::invalidator_for(inval_block.address);

      for (size_t i = 0; i < directory[flat_idx].sharers.size(); ++i) {
          // 해당 코어가 Sharer라면
          if (directory[flat_idx].sharers[i]) {
              // 채널이 존재하는지 확인 후 Invalidation 패킷 전송
              if (i < upper_levels.size()) {
                   // [수정됨] 직접 호출 대신 채널에 무효화 요청을 보냄
                   invalidator(upper_levels[i]);
              }
              // Sharer 목록에서 제거
              directory[flat_idx].sharers[i] = false;
          }
      }
  }

  // 2. 블록 무효화 (Local Eviction)
  inval_block.valid = false;
  inval_block.dirty = false;
  inval_block.prefetch = false;
  
  // 상위 캐시의 Dirty 여부는 비동기 패킷으로 처리되므로 
  // 여기서는 로컬 Dirty 상태만 반환합니다.
  return was_dirty;
}

bool CACHE::prefetch_line(champsim::address pf_addr, bool fill_this_level, uint32_t prefetch_metadata)
{
  ++sim_stats.pf_requested;

  if (std::size(internal_PQ) >= PQ_SIZE) {
    return false;
  }

  request_type pf_packet;
  pf_packet.type = access_type::PREFETCH;
  pf_packet.pf_metadata = prefetch_metadata;
  pf_packet.cpu = cpu;
  pf_packet.address = pf_addr;
  pf_packet.v_address = virtual_prefetch ? pf_addr : champsim::address{};
  pf_packet.is_translated = !virtual_prefetch;

  internal_PQ.emplace_back(pf_packet, true, !fill_this_level);
  ++sim_stats.pf_issued;

  return true;
}

// LCOV_EXCL_START exclude deprecated function
bool CACHE::prefetch_line(uint64_t pf_addr, bool fill_this_level, uint32_t prefetch_metadata)
{
  return prefetch_line(champsim::address{pf_addr}, fill_this_level, prefetch_metadata);
}

bool CACHE::prefetch_line(uint64_t /*deprecated*/, uint64_t /*deprecated*/, uint64_t pf_addr, bool fill_this_level, uint32_t prefetch_metadata)
{
  return prefetch_line(champsim::address{pf_addr}, fill_this_level, prefetch_metadata);
}
// LCOV_EXCL_STOP

void CACHE::finish_packet(const response_type& packet)
{
  // check MSHR information
  auto mshr_entry = std::find_if(std::begin(MSHR), std::end(MSHR), matches_address(packet.address));
  auto first_unreturned = std::find_if(MSHR.begin(), MSHR.end(), [](auto x) { return x.data_promise.has_unknown_readiness(); });

  // sanity check
  if (mshr_entry == MSHR.end()) {
    fmt::print(stderr, "[{}_MSHR] {} cannot find a matching entry! address: {} v_address: {}\n", NAME, __func__, packet.address, packet.v_address);
    assert(0);
  }

  // MSHR holds the most updated information about this request
  mshr_type::returned_value finished_value{packet.data, packet.pf_metadata, packet.data_cache_line};
  mshr_entry->data_promise = champsim::waitable{finished_value, current_time + (warmup ? champsim::chrono::clock::duration{} : FILL_LATENCY)};
  if constexpr (champsim::debug_print) {
    fmt::print("[{}_MSHR] finish_packet instr_id: {} address: {} data: {} type: {} current: {}\n", this->NAME, mshr_entry->instr_id, mshr_entry->address,
               mshr_entry->data_promise->data, access_type_names.at(champsim::to_underlying(mshr_entry->type)), current_time.time_since_epoch() / clock_period);
  }

  // Order this entry after previously-returned entries, but before non-returned
  // entries
  std::iter_swap(mshr_entry, first_unreturned);
}

void CACHE::finish_translation(const response_type& packet)
{
  auto matches_vpage = [page_num = champsim::page_number{packet.v_address}](const auto& entry) {
    return (champsim::page_number{entry.v_address} == page_num) && !entry.is_translated;
  };
  auto mark_translated = [p_page = champsim::page_number{packet.data}, this](auto& entry) {
    [[maybe_unused]] auto old_address = entry.address;
    entry.address = champsim::address{champsim::splice(p_page, champsim::page_offset{entry.v_address})}; // translated address
    entry.is_translated = true;                                                                          // This entry is now translated

    if constexpr (champsim::debug_print) {
      fmt::print("[{}_TRANSLATE] finish_translation old: {} paddr: {} vaddr: {} type: {} cycle: {}\n", this->NAME, old_address, entry.address, entry.v_address,
                 access_type_names.at(champsim::to_underlying(entry.type)), this->current_time.time_since_epoch() / this->clock_period);
    }
  };

  // Restart stashed translations
  auto finish_begin = std::find_if_not(std::begin(translation_stash), std::end(translation_stash), [](const auto& x) { return x.is_translated; });
  auto finish_end = std::stable_partition(finish_begin, std::end(translation_stash), matches_vpage);
  std::for_each(finish_begin, finish_end, mark_translated);

  // Find all packets that match the page of the returned packet
  for (auto& entry : inflight_tag_check) {
    if (matches_vpage(entry)) {
      mark_translated(entry);
    }
  }
}

void CACHE::issue_translation(tag_lookup_type& q_entry) const
{
  if (!q_entry.translate_issued && !q_entry.is_translated) {
    request_type fwd_pkt;
    fwd_pkt.asid[0] = q_entry.asid[0];
    fwd_pkt.asid[1] = q_entry.asid[1];
    fwd_pkt.type = access_type::LOAD;
    fwd_pkt.cpu = q_entry.cpu;

    fwd_pkt.address = q_entry.address;
    fwd_pkt.v_address = q_entry.v_address;
    fwd_pkt.data = q_entry.data;
    fwd_pkt.instr_id = q_entry.instr_id;
    fwd_pkt.ip = q_entry.ip;

    fwd_pkt.instr_depend_on_me = q_entry.instr_depend_on_me;
    fwd_pkt.is_translated = true;

    q_entry.translate_issued = lower_translate->add_rq(fwd_pkt);
    if constexpr (champsim::debug_print) {
      if (q_entry.translate_issued) {
        fmt::print("[TRANSLATE] do_issue_translation instr_id: {} paddr: {} vaddr: {} type: {}\n", q_entry.instr_id, q_entry.address, q_entry.v_address,
                   access_type_names.at(champsim::to_underlying(q_entry.type)));
      }
    }
  }
}

std::size_t CACHE::get_mshr_occupancy() const { return std::size(MSHR); }

std::vector<std::size_t> CACHE::get_rq_occupancy() const
{
  std::vector<std::size_t> retval;
  std::transform(std::begin(upper_levels), std::end(upper_levels), std::back_inserter(retval), [](auto ulptr) { return ulptr->rq_occupancy(); });
  return retval;
}

std::vector<std::size_t> CACHE::get_wq_occupancy() const
{
  std::vector<std::size_t> retval;
  std::transform(std::begin(upper_levels), std::end(upper_levels), std::back_inserter(retval), [](auto ulptr) { return ulptr->wq_occupancy(); });
  return retval;
}

std::vector<std::size_t> CACHE::get_pq_occupancy() const
{
  std::vector<std::size_t> retval;
  std::transform(std::begin(upper_levels), std::end(upper_levels), std::back_inserter(retval), [](auto ulptr) { return ulptr->pq_occupancy(); });
  retval.push_back(std::size(internal_PQ));
  return retval;
}

// LCOV_EXCL_START exclude deprecated function
std::size_t CACHE::get_occupancy(uint8_t queue_type, uint64_t /*deprecated*/) const
{
  if (queue_type == 0) {
    return get_mshr_occupancy();
  }
  return 0;
}

std::size_t CACHE::get_occupancy(uint8_t queue_type, champsim::address /*deprecated*/) const
{
  if (queue_type == 0) {
    return get_mshr_occupancy();
  }
  return 0;
}
// LCOV_EXCL_STOP

std::size_t CACHE::get_mshr_size() const { return MSHR_SIZE; }
std::vector<std::size_t> CACHE::get_rq_size() const
{
  std::vector<std::size_t> retval;
  std::transform(std::begin(upper_levels), std::end(upper_levels), std::back_inserter(retval), [](auto ulptr) { return ulptr->rq_size(); });
  return retval;
}

std::vector<std::size_t> CACHE::get_wq_size() const
{
  std::vector<std::size_t> retval;
  std::transform(std::begin(upper_levels), std::end(upper_levels), std::back_inserter(retval), [](auto ulptr) { return ulptr->wq_size(); });
  return retval;
}

std::vector<std::size_t> CACHE::get_pq_size() const
{
  std::vector<std::size_t> retval;
  std::transform(std::begin(upper_levels), std::end(upper_levels), std::back_inserter(retval), [](auto ulptr) { return ulptr->pq_size(); });
  retval.push_back(PQ_SIZE);
  return retval;
}

// LCOV_EXCL_START exclude deprecated function
std::size_t CACHE::get_size(uint8_t queue_type, champsim::address /*deprecated*/) const
{
  if (queue_type == 0) {
    return get_mshr_size();
  }
  return 0;
}

std::size_t CACHE::get_size(uint8_t queue_type, uint64_t /*deprecated*/) const
{
  if (queue_type == 0) {
    return get_mshr_size();
  }
  return 0;
}
// LCOV_EXCL_STOP

namespace
{
double occupancy_ratio(std::size_t occ, std::size_t sz) { return std::ceil(occ) / std::ceil(sz); }

std::vector<double> occupancy_ratio_vec(std::vector<std::size_t> occ, std::vector<std::size_t> sz)
{
  std::vector<double> retval;
  std::transform(std::begin(occ), std::end(occ), std::begin(sz), std::back_inserter(retval), occupancy_ratio);
  return retval;
}
} // namespace

double CACHE::get_mshr_occupancy_ratio() const { return ::occupancy_ratio(get_mshr_occupancy(), get_mshr_size()); }

std::vector<double> CACHE::get_rq_occupancy_ratio() const { return ::occupancy_ratio_vec(get_rq_occupancy(), get_rq_size()); }

std::vector<double> CACHE::get_wq_occupancy_ratio() const { return ::occupancy_ratio_vec(get_wq_occupancy(), get_wq_size()); }

std::vector<double> CACHE::get_pq_occupancy_ratio() const { return ::occupancy_ratio_vec(get_pq_occupancy(), get_pq_size()); }

void CACHE::impl_prefetcher_initialize() const { pref_module_pimpl->impl_prefetcher_initialize(); }

uint32_t CACHE::impl_prefetcher_cache_operate(champsim::address addr, champsim::address ip, bool cache_hit, bool useful_prefetch, access_type type,
                                              uint32_t metadata_in) const
{
  return pref_module_pimpl->impl_prefetcher_cache_operate(addr, ip, cache_hit, useful_prefetch, type, metadata_in);
}

uint32_t CACHE::impl_prefetcher_cache_fill(champsim::address addr, long set, long way, bool prefetch, champsim::address evicted_addr,
                                           uint32_t metadata_in) const
{
  return pref_module_pimpl->impl_prefetcher_cache_fill(addr, set, way, prefetch, evicted_addr, metadata_in);
}

void CACHE::impl_prefetcher_cycle_operate() const { pref_module_pimpl->impl_prefetcher_cycle_operate(); }

void CACHE::impl_prefetcher_final_stats() const { pref_module_pimpl->impl_prefetcher_final_stats(); }

void CACHE::impl_prefetcher_branch_operate(champsim::address ip, uint8_t branch_type, champsim::address branch_target) const
{
  pref_module_pimpl->impl_prefetcher_branch_operate(ip, branch_type, branch_target);
}

void CACHE::impl_initialize_replacement() const { repl_module_pimpl->impl_initialize_replacement(); }

long CACHE::impl_find_victim(uint32_t triggering_cpu, uint64_t instr_id, long set, const BLOCK* current_set, champsim::address ip, champsim::address full_addr,
                             access_type type) const
{
  return repl_module_pimpl->impl_find_victim(triggering_cpu, instr_id, set, current_set, ip, full_addr, type);
}

void CACHE::impl_update_replacement_state(uint32_t triggering_cpu, long set, long way, champsim::address full_addr, champsim::address ip,
                                          champsim::address victim_addr, access_type type, bool hit) const
{
  repl_module_pimpl->impl_update_replacement_state(triggering_cpu, set, way, full_addr, ip, victim_addr, type, hit);
}

void CACHE::impl_replacement_cache_fill(uint32_t triggering_cpu, long set, long way, champsim::address full_addr, champsim::address ip,
                                        champsim::address victim_addr, access_type type) const
{
  repl_module_pimpl->impl_replacement_cache_fill(triggering_cpu, set, way, full_addr, ip, victim_addr, type);
}

void CACHE::impl_replacement_final_stats() const { repl_module_pimpl->impl_replacement_final_stats(); }

void CACHE::initialize()
{
  init_hash_tables();
  impl_prefetcher_initialize();
  impl_initialize_replacement();
}

void CACHE::begin_phase()
{
  stats_type new_roi_stats;
  stats_type new_sim_stats;

  new_roi_stats.name = NAME;
  new_sim_stats.name = NAME;

  roi_stats = new_roi_stats;
  sim_stats = new_sim_stats;

  for (auto* ul : upper_levels) {
    channel_type::stats_type ul_new_roi_stats;
    channel_type::stats_type ul_new_sim_stats;
    ul->roi_stats = ul_new_roi_stats;
    ul->sim_stats = ul_new_sim_stats;
  }
}

void CACHE::end_phase(unsigned finished_cpu)
{
  finished_cpu = finished_cpu;
  roi_stats.total_miss_latency_cycles = sim_stats.total_miss_latency_cycles;

  roi_stats.hits = sim_stats.hits;
  roi_stats.misses = sim_stats.misses;
  roi_stats.mshr_merge = sim_stats.mshr_merge;
  roi_stats.mshr_return = sim_stats.mshr_return;

  roi_stats.pf_requested = sim_stats.pf_requested;
  roi_stats.pf_issued = sim_stats.pf_issued;
  roi_stats.pf_useful = sim_stats.pf_useful;
  roi_stats.pf_useless = sim_stats.pf_useless;
  roi_stats.pf_fill = sim_stats.pf_fill;

  roi_stats.xor_compressions = sim_stats.xor_compressions;
  roi_stats.local_recoveries = sim_stats.local_recoveries;
  roi_stats.remote_recoveries = sim_stats.remote_recoveries;
  roi_stats.direct_forwardings = sim_stats.direct_forwardings;
  roi_stats.unxorings = sim_stats.unxorings;

  for (auto* ul : upper_levels) {
    ul->roi_stats.RQ_ACCESS = ul->sim_stats.RQ_ACCESS;
    ul->roi_stats.RQ_MERGED = ul->sim_stats.RQ_MERGED;
    ul->roi_stats.RQ_FULL = ul->sim_stats.RQ_FULL;
    ul->roi_stats.RQ_TO_CACHE = ul->sim_stats.RQ_TO_CACHE;

    ul->roi_stats.PQ_ACCESS = ul->sim_stats.PQ_ACCESS;
    ul->roi_stats.PQ_MERGED = ul->sim_stats.PQ_MERGED;
    ul->roi_stats.PQ_FULL = ul->sim_stats.PQ_FULL;
    ul->roi_stats.PQ_TO_CACHE = ul->sim_stats.PQ_TO_CACHE;

    ul->roi_stats.WQ_ACCESS = ul->sim_stats.WQ_ACCESS;
    ul->roi_stats.WQ_MERGED = ul->sim_stats.WQ_MERGED;
    ul->roi_stats.WQ_FULL = ul->sim_stats.WQ_FULL;
    ul->roi_stats.WQ_TO_CACHE = ul->sim_stats.WQ_TO_CACHE;
    ul->roi_stats.WQ_FORWARD = ul->sim_stats.WQ_FORWARD;
  }
}

template <typename T>
bool CACHE::should_activate_prefetcher(const T& pkt) const
{
  return !pkt.prefetch_from_this && std::count(std::begin(pref_activate_mask), std::end(pref_activate_mask), pkt.type) > 0;
}

// LCOV_EXCL_START Exclude the following function from LCOV
void CACHE::print_deadlock()
{
  std::string_view mshr_write{"instr_id: {} address: {} v_addr: {} type: {} ready: {}"};
  auto mshr_pack = [time = current_time](const auto& entry) {
    return std::tuple{entry.instr_id, entry.address, entry.v_address, access_type_names.at(champsim::to_underlying(entry.type)),
                      entry.data_promise.is_ready_at(time)};
  };

  std::string_view tag_check_write{"instr_id: {} address: {} v_addr: {} is_translated: {} translate_issued: {} event_cycle: {}"};
  auto tag_check_pack = [period = clock_period](const auto& entry) {
    return std::tuple{entry.instr_id,      entry.address,          entry.v_address,
                      entry.is_translated, entry.translate_issued, entry.event_cycle.time_since_epoch() / period};
  };

  champsim::range_print_deadlock(MSHR, NAME + "_MSHR", mshr_write, mshr_pack);
  champsim::range_print_deadlock(inflight_tag_check, NAME + "_tags", tag_check_write, tag_check_pack);
  champsim::range_print_deadlock(translation_stash, NAME + "_translation", tag_check_write, tag_check_pack);

  std::string_view q_writer{"instr_id: {} address: {} v_addr: {} type: {} translated: {}"};
  auto q_entry_pack = [](const auto& entry) {
    return std::tuple{entry.instr_id, entry.address, entry.v_address, access_type_names.at(champsim::to_underlying(entry.type)), entry.is_translated};
  };

  for (auto* ul : upper_levels) {
    champsim::range_print_deadlock(ul->RQ, NAME + "_RQ", q_writer, q_entry_pack);
    champsim::range_print_deadlock(ul->WQ, NAME + "_WQ", q_writer, q_entry_pack);
    champsim::range_print_deadlock(ul->PQ, NAME + "_PQ", q_writer, q_entry_pack);
  }
}
// LCOV_EXCL_STOP
