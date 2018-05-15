//
// Created by 冯迭乔 on 5/10/18.
//

#include "Kernel.h"
#include <cassert>

namespace kn {
    const int LO_CONST_TYPE = 64;
    const int HI_CONST_TYPE = 128;

    const int LO_CONST_TERM = 128;
    const int HI_CONST_TERM = 256;


    NamePool::NamePool(int _ptr) : ptr(_ptr) {}

    int NamePool::gen() {
        if (!aval.empty()) {
            int idx = aval.back();
            aval.pop_back();
            used.push_back(idx);
            return idx;
        } else {
            used.push_back(ptr);
            return ptr++;
        }
    }

    void NamePool::add_ckpt() {
        ckpt.push_back(used.size());
    }

    void NamePool::rec_ckpt()
    {
        assert(!ckpt.empty());

        auto n = ckpt.back();
        ckpt.pop_back();

        aval.insert(aval.end(), used.begin() + n, used.end());
        used.resize(n);
    }

    void NamePool::rec_ckpt(std::unordered_set<int> &pset) {
        assert(!ckpt.empty());

        auto n = ckpt.back();
        ckpt.pop_back();

        for (auto it = used.begin() + n; it != used.end(); ++it) {
            if (pset.find(*it) != pset.end())
                used[n++] = *it;
            else
                aval.push_back(*it);
        }
        used.resize(n);
    }



    NamePool type_name_pool(HI_CONST_TYPE);
    NamePool term_name_pool(HI_CONST_TERM);

    PointerPool<Type> type_pointer_pool;
    PointerPool<Term> term_pointer_pool;



    Type *mk_atom(int idx)
    {
        return type_pointer_pool.insert(Type(false, nullptr, nullptr, idx));
    }

    Type *mk_fun(Type *ty1, Type *ty2)
    {
        return type_pointer_pool.insert(Type(true, ty1, ty2, 0));
    }

    Type *new_type()
    {
        return mk_atom(type_name_pool.gen());
    }

    Type *mk_lfun(std::vector<Type *> &tyl, Type *apx)
    {
        for (auto it = tyl.rbegin(); it != tyl.rend(); ++it)
            apx = mk_fun(*it, apx);
        return apx;
    }

    bool is_contype(Type *ty)
    {
        return ty->idx < HI_CONST_TYPE;
    }

    bool is_vartype(Type *ty)
    {
        return ty->idx >= HI_CONST_TYPE;
    }



    Term *mk_comb(Term *tm1, Term *tm2)
    {
        assert(tm1->ty->dom() == tm2->ty);

        return term_pointer_pool.insert(Term(0, tm1->ty->cod(), tm1, tm2, 0, tm1->size + tm2->size));
    }

    Term *mk_abs(Type *ty, Term *tm)
    {
        return term_pointer_pool.insert(Term(1, mk_fun(ty, tm->ty), tm, nullptr, 0, tm->size + 1));
    }

    Term *mk_var(Type *ty, int idx)
    {
        return term_pointer_pool.insert(Term(2, ty, nullptr, nullptr, idx, 1));
    }

    Term *new_term(Type *ty, int scope)
    {
        return mk_var(ty, term_name_pool.gen() + scope);
    }

    bool is_const(const Term *tm, int scope)
    {
        return tm->idx >= scope && tm->idx < scope + HI_CONST_TERM;
    }

    bool is_fvar(Term *tm, int scope)
    {
        return tm->idx >= scope + HI_CONST_TERM;
    }

    bool is_bvar(Term *tm, int scope)
    {
        return tm->idx < scope;
    }

    Term *lift(Term *tm, int inc, int scope)
    {
        if (tm->tag == 2)
            return tm->idx < scope ? tm : mk_var(tm->ty, tm->idx + inc);
        else {
            std::tuple<Term *, int, int> key(tm, inc, scope);
            auto it = lift_map.find(key);
            if (it != lift_map.end()) return it->second;

            if (tm->tag == 0)
                return lift_map[key] = mk_comb(lift(tm->p1, inc, scope), lift(tm->p2, inc, scope));
            else
                return lift_map[key] = mk_abs(tm->ty->dom(), lift(tm->p1, inc, scope + 1));
        }
    }

    Term *mk_eq(Term *tm1, Term *tm2, int scope)
    {
        assert(tm1->ty == tm2->ty);

        return mk_comb(mk_comb(mk_var(mk_fun(tm1->ty, mk_fun(tm2->ty, bool_ty)), scope), tm1), tm2);
    }

    Type *const bool_ty = mk_atom(0);

    std::unordered_map<Term *, Term *> nform_map;
    std::unordered_map<std::tuple<Term *, Term *, int>, Term *, tuple_hash> beta_map;
    std::unordered_map<std::tuple<Term *, int, int>, Term *, tuple_hash> lift_map;
}

