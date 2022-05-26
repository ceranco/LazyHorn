#include "Global.h"

namespace LazyHorn {
LhParams gParams;

std::ostream &operator<<(std::ostream &out, const LhParams &p) {
  out << "LAZY HORN PARAMETERS\n"
      << "\tfName = " << p.fName << "\n"
      << "\talg = " << (p.alg == 0 ? "Z3" : "LazyHorn") << "\n"
      << "\tcover_update_strat = " << (p.cover_update_strat == 0 ? "Recursive Tarjan" : "BFS") << "\n"
      << "\trandom_seed = " << p.random_seed << "\n"
      << "\tclause_addition_strat = " << (p.clause_addition_strat == 0 ? "ssp" : (p.clause_addition_strat == 1 ? "loop-free-ssp" : "top-down-ssp")) << "\n"
      << "\tarray_theory = " << (p.array_theory == 0 ? "no" : "yes") << "\n"
      << "\tcontext_strat = " << (p.context_strat == 0 ? "same" : "fresh") << "\n"
      << "END";
  return out;
}

} // namespace LazyHorn
