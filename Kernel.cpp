//
// Created by 冯迭乔 on 5/10/18.
//

#include "Kernel.h"
#include <cassert>

namespace kn {
    const int LO_CONST_TYPE = 64;
    const int HI_CONST_TYPE = 128;

    const int LO_CONST_TERM = 128;
    const int MD_CONST_TERM = 256;
    const int HI_CONST_TERM = 512;

    const int MEMORY_LIMIT = 10000;
    const int SEARCH_DEPTH_LIMIT = 14;


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

        return term_pointer_pool.insert(Term(0, tm1->ty->cod(), tm1, tm2,
                                             0, tm1->size + tm2->size,
                                             std::max(tm1->synapse, tm2->synapse)));
    }

    Term *mk_abs(Type *ty, Term *tm)
    {
        return term_pointer_pool.insert(Term(1, mk_fun(ty, tm->ty), tm, nullptr,
                                             0, tm->size + 1,
                                             std::max(tm->synapse - 1, 0)));
    }

    Term *mk_var(Type *ty, int idx)
    {
        return term_pointer_pool.insert(Term(2, ty, nullptr, nullptr,
                                             idx, 1,
                                             idx >= 0 ? 0 : -idx));
    }

    Term *new_term(Type *ty)
    {
        return mk_var(ty, term_name_pool.gen());
    }

    bool is_const(const Term *tm)
    {
        return tm->idx >= 0 && tm->idx < HI_CONST_TERM;
    }

    bool is_fvar(Term *tm)
    {
        return tm->idx >= HI_CONST_TERM;
    }

    bool is_bvar(Term *tm)
    {
        return tm->idx < 0;
    }

    bool is_equal(Term *tm)
    {
        return tm->is_comb() && tm->rator()->is_comb() && tm->rator()->rator()->idx == 0;
    }

    Term *lift(Term *tm, int inc, int scope)
    {
        if (tm->tag == 2)
            return tm->idx >= -scope ? tm : mk_var(tm->ty, tm->idx - inc);
        else {
            std::tuple<Term *, int, int> key(tm, inc, scope);
            auto it = lift_map.hmap.find(key);
            if (it != lift_map.hmap.end()) return it->second;

            Term *ret = tm->tag == 0 ? mk_comb(lift(tm->p1, inc, scope), lift(tm->p2, inc, scope))
                                     : mk_abs(tm->ty->dom(), lift(tm->p1, inc, scope + 1));
            lift_map.insert(key, ret);
            return ret;
        }
    }

    Term *mk_eq(Term *tm1, Term *tm2)
    {
        assert(tm1->ty == tm2->ty);

        return mk_comb(mk_comb(mk_var(mk_fun(tm1->ty, mk_fun(tm2->ty, bool_ty)), 0), tm1), tm2);
    }

    Type *const bool_ty = mk_atom(0);

    PersistentMap<std::tuple<Term *, Term *, int>, Term *, hbeta> beta_map;
    PersistentMap<std::tuple<Term *, int, int>, Term *, hlift> lift_map;
    PersistentMap<std::pair<int, Term *>, bool, hvfree_in> vfree_in_map;

    void save_maps()
    {
        type_name_pool.add_ckpt();
        term_name_pool.add_ckpt();
        type_pointer_pool.add_ckpt();
        term_pointer_pool.add_ckpt();
        beta_map.add_ckpt();
        lift_map.add_ckpt();
        vfree_in_map.add_ckpt();
    }

    void load_maps()
    {
        type_name_pool.rec_ckpt();
        term_name_pool.rec_ckpt();
        type_pointer_pool.rec_ckpt();
        term_pointer_pool.rec_ckpt();
        beta_map.rec_ckpt();
        lift_map.rec_ckpt();
        vfree_in_map.rec_ckpt();
    }
}

