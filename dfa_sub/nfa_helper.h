#pragma once

#include "definitions.h"

#include "tl/formula.hh"
#include "twa/fwd.hh"
#include "bddx.h"
#include <vector>
#include <utility>
#include <spot/twaalgos/emptiness.hh>

// Complete NFA
void complete_nfa(spot::twa_graph_ptr& aut);

// Checks if left and right accept the same language
// Automata need to be complete
// first:  1 left accepts, right rejects
//         0 They have the same language
//        -1 right accepts, left rejects
// second: empty if first is zero
//         else the "trace"
std::pair<int, std::vector<bdd>> nfa_equal(const spot::const_twa_graph_ptr& left,
                                           const spot::const_twa_graph_ptr& right);

// Computes whether an intersecting run between left and right exist
std::vector<bdd> nfa_intersect(const spot::const_twa_graph_ptr& left,
                               const spot::const_twa_graph_ptr& right);

// Determinize a given nfa
// Uses standard powerset construction
// With sorted vectors as powersets
// No sharing no reusing, just straight forward
// pre: nfa needs to be complete
spot::twa_graph_ptr nfa_determinize(spot::const_twa_graph_ptr aut);

// Complement a dfa
spot::twa_graph_ptr dfa_complement(const spot::const_twa_graph_ptr& dfa);