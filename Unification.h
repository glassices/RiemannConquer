//
// Created by 冯迭乔 on 5/10/18.
//

#ifndef BPRIL_UNIFICATION_H
#define BPRIL_UNIFICATION_H

#include "Library.h"
#include <forward_list>

bool type_unify(Type *, Type *, ty_instor &);
bool type_unify(std::vector<std::pair<Type *, Type *>> &, ty_instor &);

typedef std::forward_list<std::pair<Term *, Term *>> obj_type;
typedef std::forward_list<std::pair<Term *, int>> rsl_type;

bool simplify(obj_type &, rsl_type &, ty_instor &, tm_instor &, bool = false, int = 0);
bool term_unify(obj_type, rsl_type, std::pair<ty_instor, tm_instor> &);

extern clock_t debug_t;

#endif //BPRIL_UNIFICATION_H
