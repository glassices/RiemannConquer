//
// Created by 冯迭乔 on 5/10/18.
//

#ifndef BPRIL_TYPETERM_H
#define BPRIL_TYPETERM_H

#include <vector>
#include <ostream>
#include <functional>

struct Type
{
    bool tag; // true for fun, false for atom
    Type *lptr, *rptr;
    int idx;

    Type(bool, Type *, Type *, int);
    bool is_atom() const;
    bool is_fun() const;
    Type *dom() const;
    Type *cod() const;
    int arity();
    Type *apex();
    std::pair<Type *, Type *> dest_fun() const;
    void strip_fun(std::vector<Type *> &);
    void strip_fun(std::vector<Type *> &, Type *&);

    bool operator==(const Type &) const;
    struct hash
    {
        size_t operator()(const Type &) const;
    };
};

struct Term
{
    /*
     * Primitive information
     */
    short tag; // 0:comb, 1: abs, 2: leaf
    Type *ty;
    Term *p1, *p2;
    int idx;

    /*
     * Deduced information
     */
    unsigned int size;
    int synapse; // some bound bars might extend the term, this value indicate the maximum "synapse" these bvars have stretched

    Term(short, Type *, Term *, Term *, int, unsigned int, int);

    bool is_comb() const;
    bool is_abs() const;
    bool is_leaf() const;
    Term *rator() const;
    Term *rand() const;
    Term *bod() const;

    bool operator==(const Term &) const;
    struct hash {
        size_t operator()(const Term &) const;
    };
};

#endif //BPRIL_TYPETERM_H
