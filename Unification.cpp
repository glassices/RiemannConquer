//
// Created by 冯迭乔 on 5/10/18.
//

#include "Unification.h"
#include <iostream>
#include <ctime>

using namespace std;

clock_t debug_t = 0;

bool _type_unify(Type *ty1, Type *ty2, ty_instor &tyins)
{
    if (ty1->is_atom()) {
        auto it = tyins.find(ty1->idx);
        if (it != tyins.end()) ty1 = it->second;
    }
    if (ty2->is_atom()) {
        auto it = tyins.find(ty2->idx);
        if (it != tyins.end()) ty2 = it->second;
    }

    if (ty1 == ty2) return true;

    if (ty2->is_atom() && kn::is_vartype(ty2)) std::swap(ty1, ty2);

    if (ty1->is_atom() && kn::is_vartype(ty1)) {
        ty2 = type_subst(tyins, ty2);
        if (ty1 == ty2) return true;
        if (tfree_in(ty1->idx, ty2)) return false;
        insert_tyins(ty1->idx, ty2, tyins);
        return true;
    }
    else if (ty1->is_fun() && ty2->is_fun())
        return _type_unify(ty1->dom(), ty2->dom(), tyins) &&
               _type_unify(ty1->cod(), ty2->cod(), tyins);
    else
        return false;
}

bool type_unify(Type *ty1, Type *ty2, ty_instor &tyins)
{
    if (ty1 == ty2) return true;
    return _type_unify(ty1, ty2, tyins);
}

bool type_unify(std::vector<std::pair<Type *, Type *>> &task, ty_instor &tyins)
{
    for (auto e : task)
        if (e.first != e.second && !_type_unify(e.first, e.second, tyins))
            return false;
    return true;
}

void _update(ty_instor &tyins, obj_type &obj, rsl_type &rsl)
{
    std::unordered_map<Term *, Term *> minst;
    for (auto &e : obj) {
        e.first = inst(tyins, e.first, minst);
        e.second = inst(tyins, e.second, minst);
    }
    for (auto &e : rsl) e.first = inst(tyins, e.first, minst);
}

void _update(int fv, Term *tm, obj_type &obj, rsl_type &rsl)
{
    std::unordered_map<std::pair<Term *, int>, Term *, pair_hash> mvsub;
    for (auto &e : obj) {
        e.first = vsubst(fv, tm, e.first, mvsub);
        e.second = vsubst(fv, tm, e.second, mvsub);
    }
    for (auto &e : rsl) e.first = vsubst(fv, tm, e.first, mvsub);
}

void _update(ty_instor &tyins, int fv, Term *tm, obj_type &obj, rsl_type &rsl)
{
    std::unordered_map<Term *, Term *> minst;
    std::unordered_map<std::pair<Term *, int>, Term *, pair_hash> mvsub;
    for (auto &e : obj) {
        e.first = vsubst(fv, tm, inst(tyins, e.first, minst), mvsub);
        e.second = vsubst(fv, tm, inst(tyins, e.second, minst), mvsub);
    }
    for (auto &e : rsl) e.first = vsubst(fv, tm, inst(tyins, e.first, minst), mvsub);
}

/*
 * The core principle in simplify is that, we never do imitation and
 * projection rules, which means we will NEVER introduce new free variables.
 * This can guarantee that insert_tmins is optimal and there is no need
 * to use update_tmins.
 * New type variables are also impossible to introduce here.
 *
 * HOWEVER, variable name reuse is possible, which means x |-> f x is the
 * case, so we should guarantee insert_tmins will check the existence
 * of key x
 */
bool simplify(obj_type &obj, rsl_type &rsl, ty_instor &tyins, tm_instor &tmins, int dep)
{
    /*
     * beta_eta_norm and pair-type check cost comparably small time so we
     * do it brainlessly
     */


    /*
     * all in one
     * decompose rule, delete rule, unused bvars elimination and type unify to
     * avoid recursive calls of simplify
     * since no type variable is introduces, feel free to merge tyins
     */

    ty_instor ret_tyins;
    std::vector<Type *> bvs1, bvs2;
    Term *hs1, *hs2;
    std::vector<Term *> args1, args2;

    // beta-eta-norm check
    for (auto &e : obj) {
        e.first = beta_eta_term(e.first);
        e.second = beta_eta_term(e.second);
    }

    /*
    cout << dep << "before decomposition" << endl;
    for (auto &e : obj) cout << e << endl;
    cout << "-----------------------" << endl;
    */

    for (auto prev = obj.before_begin(), it = obj.begin(); it != obj.end(); ) {
        // type check
        if (it->first->ty != it->second->ty) {
            ret_tyins.clear();
            if (!type_unify(it->first->ty, it->second->ty, ret_tyins)) return false;
            update_tmins(ret_tyins, tmins);
            _update(ret_tyins, obj, rsl);
            insert_tyins(ret_tyins, tyins);
        }

        // Delete rule
        if (it->first == it->second) {
            it = obj.erase_after(prev);
            continue;
        }

        // useless bound vars elimination
        bound_eta_norm(it->first, it->second);

        // Decompose rule
        decompose(it->first, bvs1, hs1, args1);
        decompose(it->second, bvs2, hs2, args2);

        if (kn::is_fvar(hs1, static_cast<int>(bvs1.size())) || kn::is_fvar(hs2, static_cast<int>(bvs2.size())))
            ++prev, ++it;
        else if (hs1->idx - bvs1.size() != hs2->idx - bvs2.size())
            return false;
        else {
            if (bvs1.size() < bvs2.size()) {
                bvs1.swap(bvs2);
                std::swap(hs1, hs2);
                args1.swap(args2);
            }
            if (bvs1.size() > bvs2.size()) {
                auto inc = static_cast<int>(bvs1.size() - bvs2.size());
                for (auto &e : args2) e = kn::lift(e, inc);
                for (int i = 0; i < inc; i++)
                    args2.push_back(kn::mk_var(bvs1[bvs2.size() + i], inc - 1 - i));
            }

            it = obj.erase_after(prev);
            for (auto it1 = args1.begin(), it2 = args2.begin(); it1 != args1.end(); ++it1, ++it2)
                it = obj.emplace_after(prev, mk_labs(bvs1, *it1), mk_labs(bvs1, *it2));
        }
    }

    /*
    cout << dep << "after decomposition" << endl;
    for (auto &e : obj) cout << e << endl;
    cout << "-----------------------" << endl;
    */

    /*
    unordered_set<int> tyset;
    unordered_set<Term *> tmset;
    for (auto &e : obj) {
        get_frees(e.first, tyset, tmset);
        get_frees(e.second, tyset, tmset);
    }
    for (auto &e : tmset) cout << e << ' ' << e->ty << endl;
    cout << tmins << endl;
    if (tmins.find(279) != tmins.end() && tmins[279]->is_comb())
        cout << tmins[279]->rand()->ty << endl;
    cout << "=========================" << endl;
    */

    // Bind rule
    for (auto prev = obj.before_begin(), it = obj.begin(); it != obj.end(); ++prev, ++it) {
        int fv;
        Term *tm;
        if (it->first->is_leaf() && kn::is_fvar(it->first) && !vfree_in(it->first->idx, it->second)) {
            fv = it->first->idx;
            tm = it->second;
        }
        else if (it->second->is_leaf() && kn::is_fvar(it->second) && !vfree_in(it->second->idx, it->first)) {
            fv = it->second->idx;
            tm = it->first;
        }
        else
            continue;

        it = obj.erase_after(prev);
        insert_tmins(fv, tm, tmins);
        _update(fv, tm, obj, rsl);
        return simplify(obj, rsl, tyins, tmins, dep + 1);
    }

    /*
     * Deal with rsl
     */

    for (auto &e : rsl) e.first = beta_eta_term(e.first);

    for (auto prev = rsl.before_begin(), it = rsl.begin(); it != rsl.end(); ) {
        remove_dummy_bvar(it->first);

        int c = it->second;
        decompose(it->first, bvs1, hs1, args1);
        if (kn::is_fvar(hs1, static_cast<int>(bvs1.size())))
            ++prev, ++it;
        else if (hs1->idx - bvs1.size() == c)
            return false;
        else {
            it = rsl.erase_after(prev);
            for (auto &e : args1)
                it = rsl.emplace_after(prev, mk_labs(bvs1, e), c);
        }
    }

    /*
     * Higher level semantic check
     */

    return true;
}

/*
 * apex of fv.ty and c.ty should be same
 */
void _imitate(Term *fv, Term *c, Term *&sub)
{
    std::vector<Type *> tyl1, tyl2;
    std::vector<Term *> bvars, args;

    fv->ty->strip_fun(tyl1);
    c->ty->strip_fun(tyl2);
    auto n = static_cast<int>(tyl1.size());

    for (int i = 0; i < n; i++)
        bvars.push_back(kn::mk_var(tyl1[i], n - 1 - i));
    for (auto &e : tyl2)
        args.push_back(mk_lcomb(kn::new_term(kn::mk_lfun(tyl1, e), n), bvars));
    sub = compose(tyl1, kn::mk_var(c->ty, c->idx + n), args);
}

bool _project(Term *fv, int k, Term *&sub, ty_instor &tyins)
{
    Type *apx1, *apx2;
    std::vector<Type *> tyl1, tyl2;
    std::vector<Term *> bvars, args;

    tyins.clear();
    fv->ty->strip_fun(tyl1, apx1);
    tyl1[k]->strip_fun(tyl2, apx2);
    auto n = static_cast<int>(tyl1.size());

    for (int i = 0; i < n; i++)
        bvars.push_back(kn::mk_var(tyl1[i], n - 1 - i));
    if (!type_unify(apx1, apx2, tyins)) return false;
    for (auto &e : tyl2)
        args.push_back(mk_lcomb(kn::new_term(kn::mk_lfun(tyl1, e), n), bvars));
    sub = inst(tyins, compose(tyl1, kn::mk_var(tyl1[k], n - 1 - k), args));
    return true;
}

bool _term_unify(obj_type &obj, rsl_type &rsl, ty_instor &tyins, tm_instor &tmins, int dep, std::pair<ty_instor, tm_instor> &res)
{
    if (dep >= 10) return false;

    ty_instor _tyins;
    tm_instor _tmins;
    Type *apx1, *apx2;
    std::vector<Type *> bvs1, bvs2, tyl1, tyl2;
    Term *hs1, *hs2, *sub;
    std::vector<Term *> args1, args2;

    //std::cout << "before simplify:    " << obj << std::endl;
    if (!simplify(obj, rsl, _tyins, _tmins)) return false;
    //std::cout << "after simplify:    " << obj << std::endl;
    update_instor(_tyins, _tmins, tyins, tmins);

    for (auto &e : obj) if (e.first->size > 30 || e.second->size > 30) return false;
    for (auto &e : rsl) if (e.first->size > 30) return false;
    for (auto &e : tmins) if (e.second->size > 30) return false;

    // naive choose a rigid-flex pair, this might be an interesting ML prediction task
    for (auto &e : obj) {
        decompose(e.first, bvs1, hs1, args1);
        decompose(e.second, bvs2, hs2, args2);
        if (!kn::is_fvar(hs1, static_cast<int>(bvs1.size()))) {
            bvs1.swap(bvs2);
            std::swap(hs1, hs2);
            args1.swap(args2);
        }
        else if (kn::is_fvar(hs2, static_cast<int>(bvs2.size())))
            continue;

        obj_type obj_save(obj);
        rsl_type rsl_save(rsl);
        ty_instor tyins_save(tyins);
        tm_instor tmins_save(tmins);

        int idx = hs1->idx - static_cast<int>(bvs1.size());
        // Imitation
        if (kn::is_const(hs2, static_cast<int>(bvs2.size()))) {
            _imitate(hs1, hs2, sub);
            update_tmins(idx, sub, tmins);
            _update(idx, sub, obj, rsl);
            if (_term_unify(obj, rsl, tyins, tmins, dep + 1, res)) return true;
            obj = obj_save;
            rsl = rsl_save;
            tmins = tmins_save;
        }

        // Projection
        for (int k = 0; k < hs1->ty->arity(); k++) {
            _project(hs1, k, sub, _tyins);
            update_instor(_tyins, idx, sub, tyins, tmins);
            _update(_tyins, idx, sub, obj, rsl);
            if (_term_unify(obj, rsl, tyins, tmins, dep + 1, res)) return true;
            obj = obj_save;
            rsl = rsl_save;
            tyins = tyins_save;
            tmins = tmins_save;
        }

        return false;
    }

    // only flex-flex pairs remaining, unifier found
    std::unordered_set<int> ty_set;
    std::unordered_set<Term *> tm_set;
    for (auto &e : obj) {
        get_frees(e.first, ty_set, tm_set);
        get_frees(e.second, ty_set, tm_set);
    }
    for (auto &e : rsl) get_frees(e.first, ty_set, tm_set);

    std::unordered_map<Type *, int> mon;
    std::vector<Type *> tyl;
    Type *apx;
    for (auto &tm : tm_set) {
        tm->ty->strip_fun(tyl, apx);
        if (mon.find(apx) == mon.end()) mon[apx] = kn::term_name_pool.gen();
        Term *hs = kn::mk_var(apx, mon[apx] + static_cast<int>(tyl.size()));
        sub = mk_labs(tyl, hs);
        update_tmins(tm->idx, sub, tmins);
    }

    res = std::make_pair(tyins, tmins);
    return true;
}

bool term_unify(obj_type obj, rsl_type rsl, std::pair<ty_instor, tm_instor> &res)
{
    kn::type_name_pool.add_ckpt();
    kn::term_name_pool.add_ckpt();
    kn::type_pointer_pool.add_ckpt();
    kn::term_pointer_pool.add_ckpt();
    kn::save_maps();

    //cout << "Current task is " << endl << obj << endl << rsl << endl;
    obj_type _obj(obj);
    rsl_type _rsl(rsl);

    std::unordered_set<int> ty_set;
    std::unordered_set<Term *> tm_set;
    for (auto &e : obj) {
        get_frees(e.first, ty_set, tm_set);
        get_frees(e.second, ty_set, tm_set);
    }
    for (auto &e : rsl) get_frees(e.first, ty_set, tm_set);
    ty_instor tyins;
    tm_instor tmins;
    for (auto &e : ty_set) tyins[e] = kn::mk_atom(e);
    for (auto &e : tm_set) tmins[e->idx] = e;

    bool ok = _term_unify(_obj, _rsl, tyins, tmins, 0, res);

    if (! ok) {
        // we must clear deleted types and terms in res
        res.first.clear();
        res.second.clear();
        kn::type_name_pool.rec_ckpt();
        kn::term_name_pool.rec_ckpt();
        kn::type_pointer_pool.rec_ckpt();
        kn::term_pointer_pool.rec_ckpt();
    }
    else {
        // we must reserve new types and terms in res
        ty_set.clear();
        tm_set.clear();
        std::unordered_set<Type *> ty_ptr;
        std::unordered_set<Term *> tm_ptr;
        for (auto &e : res.first) {
            get_free_types(e.second, ty_set);
            get_types(e.second, ty_ptr);
        }
        for (auto &e : res.second) {
            get_frees(e.second, ty_set, tm_set);
            get_terms(e.second, ty_ptr, tm_ptr);
        }
        std::unordered_set<int> tm_idx;
        for (auto &e : tm_set) tm_idx.insert(e->idx);

        kn::type_name_pool.rec_ckpt(ty_set);
        kn::term_name_pool.rec_ckpt(tm_idx);
        kn::type_pointer_pool.rec_ckpt(ty_ptr);
        kn::term_pointer_pool.rec_ckpt(tm_ptr);
    }

    // clear hash maps
    //clock_t t0 = clock();
    kn::load_maps();
    cout << "finish " << kn::nform_map.hmap.size() << ' ' << kn::beta_map.hmap.size() << ' ' << kn::lift_map.hmap.size() << endl;
    //clock_t t1 = clock();
    //debug_t += t1 - t0;

    return ok;
}


