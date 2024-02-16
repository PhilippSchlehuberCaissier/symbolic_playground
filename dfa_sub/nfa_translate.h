#pragma once

#include "definitions.h"

#include "twa/fwd.hh"
#include "tl/formula.hh"


// Base method to create an NFA for an ltlf formula
spot::twa_graph_ptr to_nfa(const spot::formula& f,
                           const spot::bdd_dict_ptr& bdd_dict);

spot::twa_graph_ptr from_ltlf(spot::formula f);