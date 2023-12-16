//
// Created by philipp on 24/07/23.
//

#pragma once

#include "sym_aut.h"

// "Model checking" algos

/**
 * \brief Returns true iff the language of \a left (interpreted as a DFA)
 * is contained in the language of \a right
 * @param left SBA interpreted as DFA
 * @param right SBA interpreted as DFA
 * @return left subseteq right
 */
bool
dfa_contains(const twa_graph_ptr& left, const twa_graph_ptr& right);

/**
 * \brief Checks if the the DFAs \a left and \a right are language equivalent
 * @param left SBA interpreted as DFA
 * @param right SBA interpreted as DFA
 * @return (left subseteq right) && (right \subseteq left)
 */
bool dfa_equiv(const twa_graph_ptr& left, const twa_graph_ptr& right){
  return dfa_contains(left, right) && dfa_contains(right, left);
}


/**
 * \brief Minimizes the symbolic automaton \a sy using and adaption
 * of the signature based approach in
 * @param sy Orig automaton
 * @param base Prefix of the fresh ap for the minimized aut
 * @return A new symbolic aut
 */

sym_aut
signature_min(const sym_aut& sy, const std::string& base);

// Game algos

/**
 * \brief Solve the reachability game on the symbolic automaton æ sy
 * @param sy Game to solve; updates W and Attr
 */
void
solve_reachability(sym_aut& sy);
