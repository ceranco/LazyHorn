#pragma once

#include <iostream>
#include <string>

/** Global variables */
namespace LazyHorn {
struct LhParams {
  std::string fName;

  /**Interpolantion sequence to use
     0 Z3, 1 LazyHorn */
  unsigned alg;

  /** verbosity level */
  unsigned verbosity;

  /** how to traverse the CHC-graph
   0 recursive Tarjan, 1 bfs */
  unsigned cover_update_strat;
  
  /** Random seed to be used by SMT solver */
  unsigned random_seed;
  
  /** how to add clauses
   0 minimal addition, 1 no loops first */
  unsigned clause_addition_strat;
  
  /** Theory of arrays 
   0 no, 1 yes */
  unsigned array_theory;
  
  /** context object for every query
   0 same, 1 fresh */
  unsigned context_strat;
};

std::ostream &operator<<(std::ostream &out, const LhParams &p);

extern LhParams gParams;

/** Output streams */

/// std out
inline std::ostream &outs() { return std::cout; }
/// std err
inline std::ostream &errs() { return std::cerr; }
/// log stream. use in LOG() macro.
inline std::ostream &logs() { return std::cerr; }
/// verbose
inline std::ostream &vout() { return std::cout; }
} // namespace LazyHorn

#define VERBOSE(LVL, CODE)                                                     \
  do {                                                                         \
    if (LVL <= ::LazyHorn::gParams.verbosity) { CODE; }                             \
  } while (0)
