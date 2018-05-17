//
// Created by 冯迭乔 on 5/14/18.
//

#ifndef BPRIL_SEARCH_H
#define BPRIL_SEARCH_H

#include "Unification.h"

/*
 * I have no doubt, this search algorithm will conquer an open problem in math
 */

typedef std::pair<std::unordered_set<Term *>, Term *> thm;

bool search(Term *, int);

#endif //BPRIL_SEARCH_H
