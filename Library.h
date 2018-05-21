//
// Created by 冯迭乔 on 5/10/18.
//

#ifndef BPRIL_LIBRARY_H
#define BPRIL_LIBRARY_H

#include <forward_list>
#include "Kernel.h"

typedef std::unordered_map<int, Type *> ty_instor;
typedef std::unordered_map<int, Term *> tm_instor;

struct hterm_scope
{
    std::size_t operator()(const std::pair<Term *, int> &p) const
    {
        return std::hash<Term *>{}(p.first) ^ (p.second << 10);
    }
};

typedef std::unordered_map<std::pair<Term *, int>, Term *, hterm_scope> vdict;
typedef std::unordered_map<Term *, Term *> idict;

Type *type_subst(int, Type *, Type *);
Type *type_subst(const ty_instor &, Type *);
void insert_tyins(int, Type *, ty_instor &);
void insert_tyins(const ty_instor &, ty_instor &);
void update_tyins(int, Type *, ty_instor &);
void update_tyins(const ty_instor &, ty_instor &);


Term *raw_inst(const ty_instor &, Term *);
Term *inst(const ty_instor &, Term *, idict &);
void update_tmins(const ty_instor &, tm_instor &, idict &);


Term *vsubst(int, Term *, Term *, vdict &, int = 0);
Term *vsubst(const tm_instor &, Term *, vdict &, int = 0);
void insert_tmins(int, Term *, tm_instor &, vdict &);
void update_tmins(int, Term *, tm_instor &, vdict &);
void update_tmins(const tm_instor &, tm_instor &, vdict &);

Term *mixsub(const ty_instor &, int, Term *, Term *, vdict &, int = 0);
Term *mixsub(const ty_instor &, const tm_instor &, Term *, vdict &, int = 0);
void update_tmins(const ty_instor &, int, Term *, tm_instor &, vdict &);
void update_tmins(const ty_instor &, const tm_instor &, tm_instor &, vdict &);

bool tfree_in(int, Type *);
bool vfree_in(int, Term *);


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
