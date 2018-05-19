//
// Created by 冯迭乔 on 5/10/18.
//

#ifndef BPRIL_LIBRARY_H
#define BPRIL_LIBRARY_H

#include <forward_list>
#include "Kernel.h"

typedef std::unordered_map<int, Type *> ty_instor;
typedef std::unordered_map<int, Term *> tm_instor;

struct pair_hash
{
    template <class T1, class T2>
    std::size_t operator()(const std::pair<T1, T2> &p) const
    {
        auto h1 = std::hash<T1>{}(p.first);
        auto h2 = std::hash<T2>{}(p.second);
        return (h1 << 1) ^ h2;
    }
};

template <class T>
T &assocd(T &key, std::unordered_map<T, T> &pmap, T &def)
{
    auto it = pmap.find(key);
    return it != pmap.end() ? it->second : def;
}


Type *type_subst(int, Type *, Type *);
Type *type_subst(const ty_instor &, Type *);

void insert_tyins(int, Type *, ty_instor &);
void insert_tyins(const ty_instor &, ty_instor &);
void insert_tmins(int, Term *, tm_instor &);

void update_tyins(int, Type *, ty_instor &);
void update_tyins(const ty_instor &, ty_instor &);
void update_tmins(int, Term *, tm_instor &);
void update_tmins(const ty_instor &, tm_instor &);
void update_tmins(const tm_instor &, tm_instor &);
void update_instor(const ty_instor &, const tm_instor &, ty_instor &, tm_instor &);
void update_instor(const ty_instor &, int, Term *, ty_instor &, tm_instor &);

bool tfree_in(int, Type *);

bool vfree_in(int, Term *);

Term *inst(const ty_instor &, Term *);
Term *inst(const ty_instor &, Term *, std::unordered_map<Term *, Term *> &);

Term *vsubst(int, Term *, Term *, int = 0);
Term *vsubst(int, Term *, Term *, std::unordered_map<std::pair<Term *, int>, Term *, pair_hash> &, int = 0);
Term *vsubst(const tm_instor &, Term *, int = 0);
Term *vsubst(const tm_instor &, Term *, std::unordered_map<std::pair<Term *, int>, Term *, pair_hash> &, int = 0);

void strip_comb(Term *, Term *&, std::vector<Term *> &);
void strip_abs(Term *, std::vector<Type *> &, Term *&);
void decompose(Term *, std::vector<Type *> &, Term *&, std::vector<Term *> &);

Term *mk_lcomb(Term *, const std::vector<Term *> &);
Term *mk_lcomb(std::initializer_list<Term *>);
Term *mk_labs(const std::vector<Type *> &, Term *);
Term *mk_nlabs(const std::vector<Type *> &, Term *);
Term *compose(const std::vector<Type *> &, Term*, const std::vector<Term *> &);

Term *mk_ncomb(Term *, Term *); // Internalize beta-normalization
Term *mk_nabs(Type *, Term *); // Internalize eta-normalization

Term *get_head(Term *);
bool head_free(Term *);
int ord_of_type(Type *);

Term *do_beta(Term *, Term *, int = 0);
bool is_eta(Term *);
void bound_eta_norm(Term *&, Term *&);
void remove_dummy_bvar(Term *&);

Term *abstraction(int, Type *, Term *);

void get_free_types(Type *, std::unordered_set<int> &);
void get_frees(Term *, std::unordered_set<int> &, std::unordered_set<Term *> &, int = 0);

/*
 * Naive printers for map, vector
 * Type and Term
 */

template <typename T1, typename T2>
std::ostream &operator<<(std::ostream &os, const std::pair<T1, T2> &pair)
{
    os << "(" << pair.first << ", " << pair.second << ")";
    return os;
};

template <typename T1, typename T2>
std::ostream &operator<<(std::ostream &os, const std::unordered_map<T1, T2> &pmap)
{
    os << "[";
    for (auto it = pmap.begin(); it != pmap.end(); ++it) {
        if (it != pmap.begin())
            os << "; ";
        os << "(" << it->first << " |-> " << it->second << ")";
    }
    os << "]";
    return os;
}

template <typename T>
std::ostream &operator<<(std::ostream &os, const std::vector<T> &pvec)
{
    os << "[";
    for (auto it = pvec.begin(); it != pvec.end(); ++it) {
        if (it != pvec.begin())
            os << "; ";
        os << *it;
    }
    os << "]";
    return os;
}

template <typename T>
std::ostream &operator<<(std::ostream &os, const std::unordered_set<T> &pset)
{
    os << "[";
    for (auto it = pset.begin(); it != pset.end(); ++it) {
        if (it != pset.begin())
            os << "; ";
        os << *it;
    }
    os << "]";
    return os;
}

template <typename T>
std::ostream &operator<<(std::ostream &os, const std::forward_list<T> &plist)
{
    os << "[";
    for (auto it = plist.begin(); it != plist.end(); ++it) {
        if (it != plist.begin())
            os << "; ";
        os << *it;
    }
    os << "]";
    return os;
}

std::ostream &operator<<(std::ostream &, const Type &);

std::ostream &operator<<(std::ostream &, const Type *);

std::ostream &operator<<(std::ostream &, const Term &);

std::ostream &operator<<(std::ostream &, const Term *);

#endif //BPRIL_LIBRARY_H
