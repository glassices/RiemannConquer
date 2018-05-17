//
// Created by 冯迭乔 on 5/10/18.
//

#include "Unification.h"
#include <iostream>
#include <ctime>
#include <algorithm>

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

bool _subterm(Term *fv, Term *tm, int scope = 0, bool is_bound = false)
{
    /*
     * fv should be a free var
     */
    if (tm->is_abs()) return _subterm(fv, tm->bod(), scope + 1, is_bound);
    if (fv == tm) return is_bound;

    Term *hs;
    std::vector<Term *> args;

    strip_comb(tm, hs, args);
    if (hs->idx >= scope + kn::HI_CONST_TERM) return false;
    for (auto &arg : args)
        if (_subterm(fv, arg, scope, true))
            return true;
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
        bvars.push_back(kn::mk_var(tyl1[i], n - 1 - i));
    for (auto &e : tyl2)
        args.push_back(mk_lcomb(kn::new_term(kn::mk_lfun(tyl1, e), n), bvars));
    sub = compose(tyl1, kn::mk_var(c->ty, c->idx + n), args);
}

bool _project(Type *ty, int k, Term *&sub, ty_instor &tyins)
{
    Type *apx1, *apx2;
    std::vector<Type *> tyl1, tyl2;
    std::vector<Term *> bvars, args;

    tyins.clear();
    ty->strip_fun(tyl1, apx1);
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

    if (dep >= 10) return false;

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
    cout << "before decomposition" << endl;
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

        // move first rigid to the second
        if (!kn::is_fvar(hs1, static_cast<int>(bvs1.size()))) {
            std::swap(it->first, it->second);
            bvs1.swap(bvs2);
            std::swap(hs1, hs2);
            args1.swap(args2);
        }

        if (kn::is_fvar(hs1, static_cast<int>(bvs1.size())))
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
            for (auto it1 = args1.begin(), it2 = args2.begin(); it1 != args1.end(); ++it1, ++it2) {
                it = obj.emplace_after(prev, mk_labs(bvs1, *it1), mk_labs(bvs1, *it2));
            }
        }
    }

    /*
    cout << "after decomposition" << endl;
    for (auto &e : obj) cout << e << endl;
    cout << "-----------------------" << endl;
    */

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
     * We can never cover all cases, try our best to reduce undecidability
     */

    std::unordered_map<Term *, Term *> pre;
    for (auto &e : obj) {
        pre.emplace(e.first, e.first);
        pre.emplace(e.second, e.second);
        pre[_find(e.first, pre)] = _find(e.second, pre);
    }
    for (auto &e : pre) _find(e.first, pre);


    /*
     * Bind rule
     */
    for (auto &e1 : pre) {
        if (e1.first->is_leaf() && kn::is_fvar(e1.first)) {
            for (auto &e2 : pre) if (e1.second == e2.second && !vfree_in(e1.first->idx, e2.first)) {
                insert_tmins(e1.first->idx, e2.first, tmins);
                _update(e1.first->idx, e2.first, obj, rsl);
                return simplify(obj, rsl, tyins, tmins, dep);
            }
        }
    }


    /*
     * Guarantee every pairs in obj are either flex-flex or flex-rigid
     * find (flex, rigid1) and (flex, rigid2)
     * [(`x79529 x79528`, `x79523 = x79523`); (`x79529 x79528`, `x78504 x78505`); (`x78504 x78505`, `C256`)]
     * is found, which means tree structure support is needed...
     * An example that might cause infinite loop:
     * [x, x = x] and [x, x = (x = x)]
     * After one step ==> [x = x, x = (x = x)] and [x, x = (x = x)]
     * and after decomposition ==> [x, x = x] and [x, x = (x = x)], which
     * is identical to the origin problem
     * To avoid this, always delete larger rigid term
     * TODO: improve this naive implementation
     */

    for (auto &e1 : pre) if (!head_free(e1.first))
        for (auto &e2 : pre)
            if (e1.first != e2.first && e1.second == e2.second && !head_free(e2.first)) {
                Term *tm1 = e1.first, *tm2 = e2.first;
                if (tm1->size < tm2->size) std::swap(tm1, tm2);
                /*
                 * delete tm1 and remain tm2
                 */
                obj.clear();
                for (auto &i1 : pre) if (i1.first == i1.second) {
                    Term *prev = nullptr;
                    for (auto &i2 : pre) if (i1.second == i2.second && i2.first != tm1) {
                        if (prev != nullptr) obj.emplace_front(prev, i2.first);
                        prev = i2.first;
                    }
                }
                obj.emplace_front(tm1, tm2);
                return simplify(obj, rsl, tyins, tmins, dep);
            }

    /*
     * For every instance of [x mc, y mc] and {x/mc, y/mc}, we can deduce x = y
     * TODO: think about generalized form of this reduction rule
     */
    for (auto it1 = pre.begin(); it1 != pre.end(); ++it1) if (it1->first->is_comb()) {
        Term *x = it1->first->rator(), *mx = it1->first->rand();
        if (x->is_leaf() && mx->is_leaf()) {
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
                for (++it2; it2 != pre.end(); ++it2) if (it2->first->is_comb() && it1->second == it2->second) {
                    Term *y = it2->first->rator(), *my = it2->first->rand();
                    if (y->is_leaf() && my->is_leaf() && x != y && mx->idx == my->idx) {
                        for (auto &e : rsl) if (e.second == my->idx) {
                            if (y == e.first) {
                                insert_tmins(x->idx, y, tmins);
                                _update(x->idx, y, obj, rsl);
                                return simplify(obj, rsl, tyins, tmins, dep);
                            }
                            auto i1 = pre.find(e.first);
                            auto i2 = pre.find(y);
                            if (i1 != pre.end() && i2 != pre.end() && i1->second == i2->second) {
                                insert_tmins(x->idx, y, tmins);
                                _update(x->idx, y, obj, rsl);
                                return simplify(obj, rsl, tyins, tmins, dep);
                            }
                        }
                    }
                }
            }
        }
    }

    /*
     * x and (x = y)
     */
    for (auto &e1 : pre) if (e1.first->is_leaf() && kn::is_fvar(e1.first, 0))
        for (auto &e2 : pre)
            if (_subterm(e1.first, e2.first))
                return false;

    /*
     * Projection is impossible
     * todo: be careful this method might incur infinite recursion
     */
    for (auto &e1 : pre) {
        /*
         * look for a candidate, head_var of tm1 is free and every head var of
         * each arg of tm1 is either bounded by tm1's top bvars or constants
         */
        decompose(e1.first, bvs1, hs1, args1);
        int idx1 = hs1->idx - static_cast<int>(bvs1.size());
        if (idx1 < kn::HI_CONST_TERM) continue;

        std::vector<int> idxes;
        bool ok = true;
        for (auto &arg : args1) {
            decompose(arg, bvs2, hs2, args2);
            int idx = hs2->idx - static_cast<int>(bvs1.size() + bvs2.size());
            /*
             * shouldn't be locally bounded
             */
            if (idx >= -bvs1.size() && idx < kn::HI_CONST_TERM) {
                if (idx >= 0) idxes.push_back(idx);
            }
            else {
                ok = false;
                break;
            }
        }
        if (!ok) continue;

        for (auto &e2 : pre) if (e1.second == e2.second) {
            decompose(e2.first, bvs2, hs2, args2);
            /*
             * can't imitate a constant with variable apx
             */
            if (hs2->ty->apex()->idx >= kn::HI_CONST_TYPE) continue;

            int idx2 = hs2->idx - static_cast<int>(bvs2.size());
            if (idx2 >= 0 && idx2 < kn::HI_CONST_TERM && std::find(idxes.begin(), idxes.end(), idx2) == idxes.end()) {
                Term *sub;
                _imitate(hs1->ty, kn::mk_var(hs2->ty, idx2), sub);
                insert_tmins(idx1, sub, tmins);
                _update(idx1, sub, obj, rsl);
                return simplify(obj, rsl, tyins, tmins, dep + 1);
            }
        }
    }

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

    for (auto &e : obj) if (e.first->size > 50 || e.second->size > 50) return false;
    for (auto &e : rsl) if (e.first->size > 50) return false;
    for (auto &e : tmins) if (e.second->size > 50) return false;

    std::pair<Term *, Term *> best;
    int ord, min_order = 1000000;
    for (auto &e : obj)
        if (!head_free(e.second) && (ord = ord_of_type(get_head(e.first)->ty)) < min_order) {
            min_order = ord;
            best = e;
        }

    /*
     * naive choose a flex-rigid pair, this might be an interesting ML prediction task
     */

    if (min_order < 1000000) {
        decompose(best.first, bvs1, hs1, args1);
        decompose(best.second, bvs2, hs2, args2);

        obj_type obj_save(obj);
        rsl_type rsl_save(rsl);
        ty_instor tyins_save(tyins);
        tm_instor tmins_save(tmins);

        int idx = hs1->idx - static_cast<int>(bvs1.size());
        // Imitation
        if (kn::is_const(hs2, static_cast<int>(bvs2.size()))) {
            _imitate(hs1->ty, kn::mk_var(hs2->ty, hs2->idx - static_cast<int>(bvs2.size())), sub);
            update_tmins(idx, sub, tmins);
            _update(idx, sub, obj, rsl);
            if (_term_unify(obj, rsl, tyins, tmins, dep + 1, res)) return true;
            obj = obj_save;
            rsl = rsl_save;
            tmins = tmins_save;
        }

        // Projection
        for (int k = 0; k < hs1->ty->arity(); k++) {
            if (!_project(hs1->ty, k, sub, _tyins)) continue;
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
    cout << "start " << kn::nform_map.hmap.size() << ' ' << kn::beta_map.hmap.size() << ' ' << kn::lift_map.hmap.size() << ' ' << kn::term_pointer_pool.hmap.size() << endl;

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

    return _term_unify(_obj, _rsl, tyins, tmins, 0, res);
}


