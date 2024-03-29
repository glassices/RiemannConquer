//
// Created by 冯迭乔 on 5/10/18.
//

#include "Unification.h"
#include <iostream>
#include <utility>
#include <algorithm>
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

void _update(const ty_instor &tyins, obj_type &obj, rsl_type &rsl, idict &ihis)
{
    for (auto &e : obj) {
        e.first = inst(tyins, e.first, ihis);
        e.second = inst(tyins, e.second, ihis);
    }
    for (auto &e : rsl) e.first = inst(tyins, e.first, ihis);
}

void _update(int fv, Term *tm, obj_type &obj, rsl_type &rsl, vdict &vhis)
{
    for (auto &e : obj) {
        e.first = vsubst(fv, tm, e.first, vhis);
        e.second = vsubst(fv, tm, e.second, vhis);
    }
    for (auto &e : rsl) e.first = vsubst(fv, tm, e.first, vhis);
}

void _update(const ty_instor &tyins, int fv, Term *tm, obj_type &obj, rsl_type &rsl, vdict &vhis)
{
    for (auto &e : obj) {
        e.first = mixsub(tyins, fv, tm, e.first, vhis);
        e.second = mixsub(tyins, fv, tm, e.second, vhis);
    }
    for (auto &e : rsl) e.first = mixsub(tyins, fv, tm, e.first, vhis);
}

Term *_find(Term *x, std::unordered_map<Term *, Term *> &pre)
{
    Term *root = x, *ret;
    while ((ret = pre[root]) != root) root = ret;
    while (x != root) {
        Term *&e = pre[x];
        x = e;
        e = root;
    }
    return root;
}

/*
 * tm1 has no free bound vars
 */
bool _subterm(Term *tm1, Term *tm2)
{
    /*
     * fv should be a free var
     */
    if (tm1->size > tm2->size) return false;
    if (tm1->size == tm2->size) return tm1 == tm2;
    if (tm2->is_abs()) return _subterm(tm1, tm2->bod());

    Term *hs;
    std::vector<Term *> args;

    strip_comb(tm2, hs, args);
    if (hs->idx >= kn::HI_CONST_TERM) return false;
    for (auto &arg : args) if (_subterm(tm1, arg)) return true;
    return false;
}


/*
 * apex of fv.ty and c.ty should be same
 */
void _imitate(Type *ty, Term *c, Term *&sub)
{
    std::vector<Type *> tyl1, tyl2;
    std::vector<Term *> bvars, args;

    ty->strip_fun(tyl1);
    c->ty->strip_fun(tyl2);
    auto n = static_cast<int>(tyl1.size());

    for (int i = 0; i < n; i++)
        bvars.push_back(kn::mk_var(tyl1[i], i - n));
    for (auto &e : tyl2)
        args.push_back(mk_lcomb(kn::new_term(kn::mk_lfun(tyl1, e)), bvars));
    sub = compose(tyl1, c, args);
}

bool _project(Type *ty, int k, Term *&sub, ty_instor &tyins)
{
    Type *apx1, *apx2;
    std::vector<Type *> tyl1, tyl2;
    std::vector<Term *> bvars, args;

    ty->strip_fun(tyl1, apx1);
    tyl1[k]->strip_fun(tyl2, apx2);
    auto n = static_cast<int>(tyl1.size());

    for (int i = 0; i < n; i++)
        bvars.push_back(kn::mk_var(tyl1[i], i - n));

    tyins.clear();
    if (!type_unify(apx1, apx2, tyins)) return false;

    for (auto &e : tyl2)
        args.push_back(mk_lcomb(kn::new_term(kn::mk_lfun(tyl1, e)), bvars));
    sub = raw_inst(tyins, compose(tyl1, kn::mk_var(tyl1[k], k - n), args));
    return true;
}

void _eliminate(Term *fv, const std::vector<int> &idxes, Term *&sub)
{
    Type *apx;
    std::vector<Type *> tyl, _tyl;
    fv->ty->strip_fun(tyl, apx);

    std::vector<Term *> args;
    auto n = static_cast<int>(tyl.size());
    auto it = idxes.begin();
    for (int i = 0; i < n; i++) {
        if (it != idxes.end() && *it == i) ++it;
        else {
            _tyl.push_back(tyl[i]);
            args.push_back(kn::mk_var(tyl[i], i - n));
        }
    }

    sub = mk_nlabs(tyl, mk_lcomb(kn::mk_var(kn::mk_lfun(_tyl, apx), fv->idx), args));
}

void _delete_term_from_obj(obj_type &obj, std::vector<Term *> &tms, std::unordered_map<Term *, Term *> &pre, Term *tm)
{
    obj.clear();
    for (auto &e1 : tms) if (pre[e1] == e1) {
        Term *prev = nullptr;
        for (auto &e2 : tms) if (pre[e2] == e1 && e2 != tm) {
            if (prev != nullptr) obj.emplace_front(prev, e2);
            prev = e2;
        }
    }
}

void _traverse(Term *tm, std::unordered_map<Term *, std::vector<Term *>> &record,
                         std::unordered_set<Term *> &visited)
{
    if (visited.find(tm) != visited.end()) return;
    visited.insert(tm);
    if (tm->is_abs()) {
        _traverse(tm->bod(), record, visited);
        return;
    }

    Term *hs;
    std::vector<Term *> args;
    strip_comb(tm, hs, args);

    if (hs->idx >= kn::HI_CONST_TERM) {
        if (record.find(hs) == record.end()) {
            std::vector<Term *> &vec = record[hs];

            for (auto &arg : args) {
                if (arg->synapse == 0)
                    vec.push_back(arg);
                else
                    vec.push_back(nullptr);
            }
        } else {
            std::vector<Term *> &vec = record[hs];
            vec.resize(std::min(vec.size(), args.size()));
            for (int i = 0; i < vec.size(); i++)
                if (vec[i] != args[i])
                    vec[i] = nullptr;
        }
    }

    for (auto &e : args) _traverse(e, record, visited);
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
bool simplify(obj_type &obj, rsl_type &rsl, ty_instor &tyins, tm_instor &tmins, bool is_unify, int dep)
{
    if (dep >= kn::SEARCH_DEPTH_LIMIT) return false;

    ty_instor ret_tyins;
    std::vector<Type *> bvs1, bvs2;
    Term *hs1, *hs2;
    std::vector<Term *> args1, args2;

    /*
    cout << "before decomposition" << endl;
    for (auto &e : obj) cout << e << endl;
    cout << "-----------------------" << endl;
    */

    /*
     * all in one
     * decompose rule, delete rule, unused bvars elimination and type unify to
     * avoid recursive calls of simplify
     * since no type variable is introduces, feel free to merge tyins
     */
    for (auto prev = obj.before_begin(), it = obj.begin(); it != obj.end(); ) {
        // type check
        if (it->first->ty != it->second->ty) {
            ret_tyins.clear();
            if (!type_unify(it->first->ty, it->second->ty, ret_tyins)) return false;
            idict ihis;
            insert_tyins(ret_tyins, tyins);
            update_tmins(ret_tyins, tmins, ihis);
            _update(ret_tyins, obj, rsl, ihis);
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

        // move first rigid to the second
        if (!kn::is_fvar(hs1)) {
            std::swap(it->first, it->second);
            bvs1.swap(bvs2);
            std::swap(hs1, hs2);
            args1.swap(args2);
        }

        if (kn::is_fvar(hs1))
            ++prev, ++it;
        else if ((hs1->idx >= 0 ? hs1->idx : -hs1->idx - static_cast<int>(bvs1.size()) - 1) !=
                 (hs2->idx >= 0 ? hs2->idx : -hs2->idx - static_cast<int>(bvs2.size()) - 1))
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
                    args2.push_back(kn::mk_var(bvs1[bvs2.size() + i], i - inc));
            }

            it = obj.erase_after(prev);
            for (auto it1 = args1.begin(), it2 = args2.begin(); it1 != args1.end(); ++it1, ++it2) {
                it = obj.emplace_after(prev, mk_nlabs(bvs1, *it1), mk_nlabs(bvs1, *it2));
            }
        }
    }

    /*
     * Initialize disjoint union set
     * Notice: the domain is pointer so there EXISTS randomness here,
     * use some extra effort to avoid this
     */
    std::vector<Term *> tms;
    std::unordered_map<Term *, Term *> pre;
    for (auto &e : obj) {
        if (std::find(tms.begin(), tms.end(), e.first) == tms.end()) {
            pre.emplace(e.first, e.first);
            tms.push_back(e.first);
        }
        if (std::find(tms.begin(), tms.end(), e.second) == tms.end()) {
            pre.emplace(e.second, e.second);
            tms.push_back(e.second);
        }
        pre[_find(e.first, pre)] = _find(e.second, pre);
    }
    for (auto &e : tms) _find(e, pre);

    /*
     * remove duplication in obj
     */
    obj.clear();
    for (auto &e1 : tms) if (pre[e1] == e1) {
            Term *prev = nullptr;
            for (auto &e2 : tms) if (pre[e2] == e1) {
                    if (prev != nullptr) obj.emplace_front(prev, e2);
                    prev = e2;
                }
        }

    /*
     * Bind rule
     */

    for (auto &e1 : tms) {
        if (e1->is_leaf() && kn::is_fvar(e1)) {
            Term *tm = nullptr;
            for (auto &e2 : tms)
                if (pre[e1] == pre[e2] && !vfree_in(e1->idx, e2) && (!tm || e2->size < tm->size))
                    tm = e2;
            if (tm) {
                vdict vhis;
                insert_tmins(e1->idx, tm, tmins, vhis);
                _update(e1->idx, tm, obj, rsl, vhis);
                return simplify(obj, rsl, tyins, tmins, is_unify, dep);
            }
        }
    }
    /*
    for (auto &e1 : tms) {
        if (e1->is_leaf() && kn::is_fvar(e1)) {
            bool found = false;
            for (auto &e2 : tms) {
                if (pre[e1] == pre[e2] && !vfree_in(e1->idx, e2)) {
                    found = true;
                    break;
                }
            }

            if (found) {
                for (auto &e2 : tms) {
                    if (pre[e1] == pre[e2] && !vfree_in(e1->idx, e2) && e2->is_leaf()) {
                        vdict vhis;
                        insert_tmins(e1->idx, e2, tmins, vhis);
                        _update(e1->idx, e2, obj, rsl, vhis);
                        return simplify(obj, rsl, tyins, tmins, is_unify, dep);
                    }
                }
                obj_type obj_save(obj);
                rsl_type rsl_save(rsl);
                obj.clear();
                rsl.clear();
                bool is_first = true;
                int ttt = 0;
                for (auto &e2 : tms) if (pre[e1] == pre[e2] && !vfree_in(e1->idx, e2)) ttt++;
                //if (ttt > 1) cout << e1 << endl;
                for (auto &e2 : tms) {
                    if (pre[e1] == pre[e2] && !vfree_in(e1->idx, e2)) {
                        //if (ttt > 1) cout << e2 << endl;
                        obj_type obj_cnt(obj_save);
                        rsl_type rsl_cnt(rsl_save);
                        vdict vhis;
                        if (is_first) {
                            insert_tmins(e1->idx, e2, tmins, vhis);
                            is_first = false;
                        }
                        _update(e1->idx, e2, obj_cnt, rsl_cnt, vhis);
                        obj.splice_after(obj.before_begin(), obj_cnt);
                        rsl.splice_after(rsl.before_begin(), rsl_cnt);
                    }
                }
                //if (ttt > 1) cout << "--------------------" << endl;
                return simplify(obj, rsl, tyins, tmins, is_unify, dep);
            }
        }
    }
    */

    /*
     * Deal with rsl
     */
    for (auto prev = rsl.before_begin(), it = rsl.begin(); it != rsl.end(); ) {
        remove_dummy_bvar(it->first);

        int c = it->second;
        decompose(it->first, bvs1, hs1, args1);
        if (kn::is_fvar(hs1))
            ++prev, ++it;
        else if (hs1->idx == c)
            return false;
        else {
            it = rsl.erase_after(prev);
            for (auto &e : args1)
                it = rsl.emplace_after(prev, mk_nlabs(bvs1, e), c);
        }
    }
    for (auto cnt = rsl.begin(); cnt != rsl.end(); ++cnt) {
        auto prev = cnt, it = cnt;
        for (++it; it != rsl.end(); ) {
            if (*cnt == *it) it = rsl.erase_after(prev);
            else ++prev, ++it;
        }
    }

    /*
     * x mc/mc ==> x := \u. y
     */
    for (auto &e : rsl) if (e.first->is_comb()) {
        Term *x = e.first->rator(), *mc = e.first->rand();
        if (x->is_leaf() && mc->is_leaf() && mc->idx == e.second) {
            Term *sub = kn::mk_abs(x->ty->dom(), kn::mk_var(x->ty->cod(), x->idx));
            vdict vhis;
            insert_tmins(x->idx, sub, tmins, vhis);
            _update(x->idx, sub, obj, rsl, vhis);
            return simplify(obj, rsl, tyins, tmins, is_unify, dep);
        }
    }

    /*
     * Find long-term rigid-rigid pairs
     * An example that might cause infinite loop:
     * [x, x = x] and [x, x = (x = x)]
     * After one step ==> [x = x, x = (x = x)] and [x, x = (x = x)]
     * and after decomposition ==> [x, x = x] and [x, x = (x = x)], which
     * is identical to the origin problem
     * To avoid this, always delete larger rigid term
     * TODO: improve this naive implementation
     */
    for (auto &e1 : tms) if (!head_free(e1)) {
        for (auto &e2 : tms)
            if (e1 != e2 && pre[e1] == pre[e2] && !head_free(e2)) {
                Term *tm1 = e1, *tm2 = e2;
                if (tm1->size < tm2->size) std::swap(tm1, tm2);
                _delete_term_from_obj(obj, tms, pre, tm1);
                obj.emplace_front(tm1, tm2);
                return simplify(obj, rsl, tyins, tmins, is_unify, dep);
            }
    }

    /*
     * For every instance of [x mc, y mc] and {x/mc, y/mc}, we can deduce x = y
     * x and y need not to be leafs
     * TODO: think about generalized form of this reduction rule
     */
    for (auto it1 = tms.begin(); it1 != tms.end(); ++it1) if ((*it1)->is_comb()) {
        Term *x = (*it1)->rator(), *mx = (*it1)->rand();
        if (mx->is_leaf() && mx->idx >= kn::LO_CONST_TERM && mx->idx < kn::MD_CONST_TERM) {
            bool ok = false;
            for (auto &e : rsl) if (e.second == mx->idx) {
                if (x == e.first) {
                    ok = true;
                    break;
                }
                else {
                    auto i1 = pre.find(e.first);
                    auto i2 = pre.find(x);
                    if (i1 != pre.end() && i2 != pre.end() && i1->second == i2->second) {
                        ok = true;
                        break;
                    }
                }
            }
            if (ok) {
                auto it2 = it1;
                for (++it2; it2 != tms.end(); ++it2) if ((*it2)->is_comb() && pre[*it1] == pre[*it2]) {
                    Term *y = (*it2)->rator(), *my = (*it2)->rand();
                    if (my->is_leaf() && mx->idx == my->idx && x != y) {
                        for (auto &e : rsl) if (e.second == my->idx) {
                            ok = false;
                            if (y == e.first) ok = true;
                            else {
                                auto i1 = pre.find(e.first);
                                auto i2 = pre.find(y);
                                if (i1 != pre.end() && i2 != pre.end() && i1->second == i2->second) ok = true;
                            }
                            if (ok) {
                                _delete_term_from_obj(obj, tms, pre, *it1);
                                obj.emplace_front(x, y);
                                return simplify(obj, rsl, tyins, tmins, is_unify, dep);
                            }
                        }
                    }
                }
            }
        }
    }




    /*
     * x and x is a rigid-position of y
     * i.e., x and \u. u (x = y)
     */
    for (auto &e1 : tms) if (head_free(e1)) {
        for (auto &e2 : tms)
            if (pre[e1] == pre[e2] && e1->size < e2->size && _subterm(e1, e2))
                return false;
    }


    /*
     * If the ith argument of a free variables x is always the same bvar-free (tm->synapse == 0),
     * the x can eliminate its ith argument by letting x = \u1 ... un. x u1 ... u(i-1) u(i+1) ... un
     * TODO: We can't do this for search procedure since there are other terms in someplace of trees. Extend this to accept searching.
     */
    if (is_unify) {
        std::unordered_map<Term *, std::vector<Term *>> record;
        std::unordered_set<Term *> visited;
        for (auto &e : obj) {
            _traverse(e.first, record, visited);
            _traverse(e.second, record, visited);
        }
        for (auto &e : rsl) _traverse(e.first, record, visited);

        std::vector<int> idxes;
        for (auto &e : record) {
            idxes.clear();
            for (int i = 0; i < e.second.size(); i++)
                if (e.second[i])
                    idxes.push_back(i);
            if (!idxes.empty()) {
                Term *sub;
                _eliminate(e.first, idxes, sub);
                vdict vhis;
                insert_tmins(e.first->idx, sub, tmins, vhis);
                _update(e.first->idx, sub, obj, rsl, vhis);
                return simplify(obj, rsl, tyins, tmins, is_unify, dep);
            }
        }
    }


    /*
     * Projection is impossible
     * todo: be careful this method might incur infinite recursion
     * look for a candidate, head_var of tm1 is free and every head var of
     * each arg of tm1 is either bounded by tm1's top bvars or constants
     */
    for (auto &e1 : tms) {
        decompose(e1, bvs1, hs1, args1);
        int idx1 = hs1->idx;
        if (idx1 < kn::HI_CONST_TERM) continue;

        std::vector<int> idxes;
        bool ok = true;
        for (auto &arg : args1) {
            decompose(arg, bvs2, hs2, args2);
            if (hs2->idx + static_cast<int>(bvs2.size()) < 0 || (hs2->idx >= 0 && hs2->idx < kn::HI_CONST_TERM)) {
                if (hs2->idx >= 0) idxes.push_back(hs2->idx);
            }
            else {
                ok = false;
                break;
            }
        }
        if (!ok) continue;

        for (auto &e2 : tms) if (pre[e1] == pre[e2]) {
            decompose(e2, bvs2, hs2, args2);
            if (hs2->ty->apex()->idx >= kn::HI_CONST_TYPE) continue;

            int idx2 = hs2->idx;
            if (idx2 >= 0 && idx2 < kn::HI_CONST_TERM && std::find(idxes.begin(), idxes.end(), idx2) == idxes.end()) {
                Term *sub;
                _imitate(hs1->ty, hs2, sub);
                vdict vhis;
                insert_tmins(idx1, sub, tmins, vhis);
                _update(idx1, sub, obj, rsl, vhis);
                return simplify(obj, rsl, tyins, tmins, is_unify, dep + 1);
            }
        }
    }


    return true;
}

bool _term_unify(obj_type &obj, rsl_type &rsl, ty_instor &tyins, tm_instor &tmins, int dep, std::pair<ty_instor, tm_instor> &res)
{
    if (dep >= kn::SEARCH_DEPTH_LIMIT) return false;

    ty_instor _tyins;
    tm_instor _tmins;
    Type *apx1, *apx2;
    std::vector<Type *> bvs1, bvs2, tyl1, tyl2;
    Term *hs1, *hs2, *sub;
    std::vector<Term *> args1, args2;

    if (!simplify(obj, rsl, _tyins, _tmins, true)) return false;
    update_tyins(_tyins, tyins);
    vdict vhis;
    update_tmins(_tyins, _tmins, tmins, vhis);

    std::pair<Term *, Term *> best;
    int ord, min_order = 1000000;
    for (auto &e : obj)
        if (!head_free(e.second) && (ord = ord_of_type(get_head(e.first)->ty)) < min_order) {
            min_order = ord;
            best = e;
        }

    /*
     * naive choose a flex-rigid pair, this might be an interesting ML prediction task
     * TODO: optimize update_tyins and update_tmins
     */

    if (min_order < 1000000) {
        decompose(best.first, bvs1, hs1, args1);
        decompose(best.second, bvs2, hs2, args2);

        obj_type obj_save(obj);
        rsl_type rsl_save(rsl);
        ty_instor tyins_save(tyins);
        tm_instor tmins_save(tmins);

        int idx = hs1->idx;
        // Imitation
        if (kn::is_const(hs2)) {
            _imitate(hs1->ty, hs2, sub);
            kn::save_maps();
            try {
                vhis.clear();
                update_tmins(idx, sub, tmins, vhis);
                _update(idx, sub, obj, rsl, vhis);
                if (_term_unify(obj, rsl, tyins, tmins, dep + 1, res)) return true;
            } catch (kn::MemoryLimitExceeded &e) {}
            kn::load_maps();
            obj = obj_save;
            rsl = rsl_save;
            tyins = tyins_save;
            tmins = tmins_save;
        }

        // Projection
        for (int k = 0; k < hs1->ty->arity(); k++) {
            if (!_project(hs1->ty, k, sub, _tyins)) continue;
            kn::save_maps();
            try {
                vhis.clear();
                if (!_tyins.empty()) {
                    update_tyins(_tyins, tyins);
                    update_tmins(_tyins, idx, sub, tmins, vhis);
                    _update(_tyins, idx, sub, obj, rsl, vhis);
                }
                else {
                    update_tmins(idx, sub, tmins, vhis);
                    _update(idx, sub, obj, rsl, vhis);

                }
                if (_term_unify(obj, rsl, tyins, tmins, dep + 1, res)) return true;
            } catch (kn::MemoryLimitExceeded &e) {}
            kn::load_maps();
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
        Term *hs = kn::mk_var(apx, mon[apx]);
        sub = mk_labs(tyl, hs);
        vhis.clear();
        update_tmins(tm->idx, sub, tmins, vhis);
    }

    res = std::make_pair(tyins, tmins);
    return true;
}

bool term_unify(obj_type obj, rsl_type rsl, std::pair<ty_instor, tm_instor> &res)
{

    static int tot = 0;
    tot++;
    cout << tot << '\t' << "Current task is " << endl << obj << endl << rsl << endl;
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

    clock_t tt = clock();
    bool ret = _term_unify(_obj, _rsl, tyins, tmins, 0, res);
    /*
    if (clock() - tt > 1000000) {
        cout << tot << '\t' << "Current task is " << endl << obj << endl << rsl << endl;
        cout << (clock() - tt) * 0.000001 << endl;
    }
    */
    return ret;
}


