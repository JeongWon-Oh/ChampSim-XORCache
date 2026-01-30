#include "cache_stats.h"

cache_stats operator-(cache_stats lhs, cache_stats rhs)
{
  cache_stats result;
  result.pf_requested = lhs.pf_requested - rhs.pf_requested;
  result.pf_issued = lhs.pf_issued - rhs.pf_issued;
  result.pf_useful = lhs.pf_useful - rhs.pf_useful;
  result.pf_useless = lhs.pf_useless - rhs.pf_useless;
  result.pf_fill = lhs.pf_fill - rhs.pf_fill;

  result.xor_compressions = lhs.xor_compressions - rhs.xor_compressions;
  result.local_recoveries = lhs.local_recoveries - rhs.local_recoveries;
  result.remote_recoveries = lhs.remote_recoveries - rhs.remote_recoveries;
  result.direct_forwardings = lhs.direct_forwardings - rhs.direct_forwardings;
  result.unxorings = lhs.unxorings - rhs.unxorings;

  result.hits = lhs.hits - rhs.hits;
  result.misses = lhs.misses - rhs.misses;

  result.total_miss_latency_cycles = lhs.total_miss_latency_cycles - rhs.total_miss_latency_cycles;
  return result;
}
