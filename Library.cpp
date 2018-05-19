//
// Created by 冯迭乔 on 5/10/18.
//

#include "Library.h"
#include <algorithm>

Type *type_subst(int idx, Type *sub, Type *ty)
{
    if (ty->is_fun())
        return kn::mk_fun(type_subst(idx, sub, ty->dom()), type_subst(idx, sub, ty->cod()));
    else
        return idx == ty->idx ? sub : ty;
}

Type *type_subst(const ty_instor &theta, Type *ty)
{
    if (ty->is_fun())
        return kn::mk_fun(type_subst(theta, ty->dom()), type_subst(theta, ty->cod()));
    else {
        auto it = theta.find(ty->idx);
        return it != theta.end() ? it->second : ty;
    }
}

void insert_tyins(int idx, Type *sub, ty_instor &tyins)
{
    for (auto &e : tyins) e.second = type_subst(idx, sub, e.second);
    tyins.insert(std::make_pair(idx, sub));
}

void insert_tyins(const ty_instor &theta, ty_instor &tyins)
{
    for (auto &e : tyins) e.second = type_subst(theta, e.second);
    tyins.insert(theta.begin(), theta.end());
}

void insert_tmins(int idx, Term *sub, tm_instor &tmins)
{
    for (auto &e : tmins) e.second = vsubst(idx, sub, e.second);
    tmins.emplace(idx, sub);
}

void update_tyins(int idx, Type *sub, ty_instor &tyins)
{
    for (auto &e : tyins) e.second = type_subst(idx, sub, e.second);
}

void update_tyins(const ty_instor &theta, ty_instor &tyins)
{
    for (auto &e : tyins) e.second = type_subst(theta, e.second);
}

void update_tmins(int idx, Term *sub, tm_instor &tmins)
{
    for (auto &e : tmins) e.second = vsubst(idx, sub, e.second);
}

void update_tmins(const ty_instor &theta, tm_instor &tmins)
{
    for (auto &e : tmins) e.second = inst(theta, e.second);
}

void update_tmins(const tm_instor &theta, tm_instor &tmins)
{
    for (auto &e : tmins) e.second = vsubst(theta, e.second);
}

void update_instor(const ty_instor &_tyins, const tm_instor &_tmins, ty_instor &tyins, tm_instor &tmins)
{
    // (tyins, tmins) followed by (_tyins, _tmins)
    update_tyins(_tyins, tyins);
    for (auto &e : tmins) e.second = inst(_tyins, e.second);
    update_tmins(_tmins, tmins);
}

void update_instor(const ty_instor &_tyins, int idx, Term *sub, ty_instor &tyins, tm_instor &tmins)
{
    // (tyins, tmins) followed by (_tyins, _(idx, sub))
    update_tyins(_tyins, tyins);
    for (auto &e : tmins) e.second = inst(_tyins, e.second);
    update_tmins(idx, sub, tmins);
}

bool tfree_in(int idx, Type *ty)
{
    if (ty->is_fun())
        return tfree_in(idx, ty->dom()) || tfree_in(idx, ty->cod());
    else
        return idx == ty->idx;
}

bool vfree_in(int idx, Term *tm)
{
    if (tm->is_comb())
        return vfree_in(idx, tm->rator()) || vfree_in(idx, tm->rand());
    else if (tm->is_abs())
        return vfree_in(idx + 1, tm->bod());
    else
        return tm->idx == idx;
}

Term *inst(const ty_instor &theta, Term *tm)
{
    if (tm->is_comb()) {
        Term *tm1 = inst(theta, tm->rator()), *tm2 = inst(theta, tm->rand());
        return tm1 == tm->rator() && tm2 == tm->rand() ? tm : kn::mk_comb(tm1, tm2);
    }
    else if (tm->is_abs()) {
        Type *ty_ = type_subst(theta, tm->ty->dom());
        Term *tm_ = inst(theta, tm->bod());
        return tm->ty->dom() == ty_ && tm->bod() == tm_ ? tm : kn::mk_abs(ty_, tm_);
    }
    else {
        Type *ty = type_subst(theta, tm->ty);
        return ty == tm->ty ? tm : kn::mk_var(ty, tm->idx);
    }
}

Term *inst(const ty_instor &theta, Term *tm, std::unordered_map<Term *, Term *> &minst)
{
    auto it = minst.find(tm);
    if (it != minst.end()) return it->second;

    if (tm->is_comb()) {
        Term *tm1 = inst(theta, tm->rator(), minst), *tm2 = inst(theta, tm->rand(), minst);
        return minst[tm] = tm1 == tm->rator() && tm2 == tm->rand() ? tm : kn::mk_comb(tm1, tm2);
    }
    else if (tm->is_abs()) {
        Type *ty_ = type_subst(theta, tm->ty->dom());
        Term *tm_ = inst(theta, tm->bod(), minst);
        return minst[tm] = tm->ty->dom() == ty_ && tm->bod() == tm_ ? tm : kn::mk_abs(ty_, tm_);
    }
    else {
        Type *ty = type_subst(theta, tm->ty);
        return minst[tm] = ty == tm->ty ? tm : kn::mk_var(ty, tm->idx);
    }
}

Term *vsubst(int idx, Term *sub, Term *tm, int scope)
{
    if (tm->is_comb()) {
        Term *tm1 = vsubst(idx, sub, tm->rator(), scope);
        Term *tm2 = vsubst(idx, sub, tm->rand(), scope);
        return tm1 == tm->rator() && tm2 == tm->rand() ? tm : mk_ncomb(tm1, tm2);
    }
    else if (tm->is_abs()) {
        Term *tmb = vsubst(idx, sub, tm->bod(), scope + 1);
        return tmb == tm->bod() ? tm : mk_nabs(tm->ty->dom(), tmb);
    }
    else
        return tm->idx == idx + scope ? kn::lift(sub, scope) : tm;
}

Term *vsubst(int idx, Term *sub, Term *tm,
             std::unordered_map<std::pair<Term *, int>, Term *, pair_hash> &mvsub, int scope)
{
    if (tm->is_leaf()) {
        /*
         * we have another hash guarantee in lift, so directly call it
         * to avoid hash duplication
         */
        return tm->idx == idx + scope ? kn::lift(sub, scope) : tm;
    }
    else {
        auto key = std::make_pair(tm, scope);
        auto it = mvsub.find(key);
        if (it != mvsub.end()) return it->second;
        if (tm->is_comb()) {
            Term *tm1 = vsubst(idx, sub, tm->rator(), mvsub, scope);
            Term *tm2 = vsubst(idx, sub, tm->rand(), mvsub, scope);
            return mvsub[key] = tm1 == tm->rator() && tm2 == tm->rand() ? tm : mk_ncomb(tm1, tm2);
        }
        else {
            Term *tmb = vsubst(idx, sub, tm->bod(), mvsub, scope + 1);
            return mvsub[key] = tmb == tm->bod() ? tm : mk_nabs(tm->ty->dom(), tmb);
        }
    }
}

Term *vsubst(const tm_instor &tmins, Term *tm, int scope)
{
    if (tm->is_comb()) {
        Term *tm1 = vsubst(tmins, tm->rator(), scope), *tm2 = vsubst(tmins, tm->rand(), scope);
        return tm1 == tm->rator() && tm2 == tm->rand() ? tm : mk_ncomb(tm1, tm2);
    }
    else if (tm->is_abs()) {
        Term *tmm = vsubst(tmins, tm->bod(), scope + 1);
        return tmm == tm->bod() ? tm : mk_nabs(tm->ty->dom(), tmm);
    }
    else if (tm->idx >= scope) {
        auto it = tmins.find(tm->idx - scope);
        if (it != tmins.end())
            return kn::lift(it->second, scope);
        else
            return tm;
    }
    else
        return tm;
}

Term *vsubst(const tm_instor &tmins, Term *tm,
             std::unordered_map<std::pair<Term *, int>, Term *, pair_hash> &mvsub, int scope)
{
    auto key = std::make_pair(tm, scope);
    auto it = mvsub.find(key);
    if (it != mvsub.end()) return it->second;

    if (tm->is_comb()) {
        Term *tm1 = vsubst(tmins, tm->rator(), mvsub, scope);
        Term *tm2 = vsubst(tmins, tm->rand(), mvsub, scope);
        return mvsub[key] = tm1 == tm->rator() && tm2 == tm->rand() ? tm : mk_ncomb(tm1, tm2);
    }
    else if (tm->is_abs()) {
        Term *tmm = vsubst(tmins, tm->bod(), mvsub, scope + 1);
        return mvsub[key] = tmm == tm->bod() ? tm : mk_nabs(tm->ty->dom(), tmm);
    }
    else if (tm->idx >= scope) {
        auto it = tmins.find(tm->idx - scope);
        if (it != tmins.end())
            return mvsub[key] = kn::lift(it->second, scope);
        else
            return mvsub[key] = tm;
    }
    else
        return tm;
}

void strip_comb(Term *tm, Term *&hs, std::vector<Term *> &args)
{
    args.clear();
    while (tm->is_comb()) {
        args.push_back(tm->rand());
        tm = tm->rator();
    }
    reverse(args.begin(), args.end());
    hs = tm;
}

void strip_abs(Term *tm, std::vector<Type *> &bvs, Term *&bod)
{
    bvs.clear();
    while (tm->is_abs()) {
        bvs.push_back(tm->ty->dom());
        tm = tm->bod();
    }
    bod = tm;
}

void decompose(Term *tm, std::vector<Type *> &bvs, Term *&hs, std::vector<Term *> &args)
{
    strip_abs(tm, bvs, tm);
    strip_comb(tm, hs, args);
}


Term *mk_lcomb(Term *hs, const std::vector<Term *> &args)
{
    for (auto &e : args) hs = kn::mk_comb(hs, e);
    return hs;
}

Term *mk_lcomb(std::initializer_list<Term *> list)
{
    assert(list.size() > 0);

    Term *tm = nullptr;
    for (auto &e : list)
        tm = tm == nullptr ? e : kn::mk_comb(tm, e);
    return tm;
}

Term *mk_labs(const std::vector<Type *> &bvs, Term *tm)
{
    for (auto it = bvs.rbegin(); it != bvs.rend(); ++it)
        tm = kn::mk_abs(*it, tm);
    return tm;
}

Term *mk_nlabs(const std::vector<Type *> &bvs, Term *tm)
{
    auto it = bvs.rbegin();
    while (it != bvs.rend() && is_eta(tm)) {
        ++it;
        tm = kn::lift(tm->rator(), -1);
    }
    for ( ; it != bvs.rend(); ++it)
        tm = kn::mk_abs(*it, tm);
    return tm;
}

Term *compose(const std::vector<Type *> &bvs, Term *hs, const std::vector<Term *> &args)
{
    return mk_labs(bvs, mk_lcomb(hs, args));
}

Term *mk_ncomb(Term *tm1, Term *tm2)
{
    assert(tm1->ty->dom() == tm2->ty);

    return tm1->is_abs() ? do_beta(tm1->bod(), tm2, 0) : kn::mk_comb(tm1, tm2);
}

Term *mk_nabs(Type *ty, Term *tm)
{
    return is_eta(tm) ? kn::lift(tm->rator(), -1) : kn::mk_abs(ty, tm);
}

Term *get_head(Term *tm)
{
    while (tm->is_abs()) tm = tm->bod();
    while (tm->is_comb()) tm = tm->rator();
    return tm;
}

bool head_free(Term *tm)
{
    int scope = 0;
    while (tm->is_abs()) {
        tm = tm->bod();
        scope++;
    }
    while (tm->is_comb()) tm = tm->rator();
    return tm->idx >= kn::HI_CONST_TERM + scope;
}

int ord_of_type(Type *ty)
{
    if (ty->is_atom())
        return 1;
    else
        return std::max(ord_of_type(ty->dom()) + 1, ord_of_type(ty->cod()));
}

bool is_eta(Term *tm)
{
    return tm->is_comb() && tm->rand()->is_leaf() && tm->rand()->idx == 0 && !vfree_in(0, tm->rator());
}

void bound_eta_norm(Term *&tm1, Term *&tm2)
{
    if (tm1->is_abs() && tm2->is_abs()) {
        Term *bod1 = tm1->bod(), *bod2 = tm2->bod();
        bound_eta_norm(bod1, bod2);
        if (!vfree_in(0, bod1) && !vfree_in(0, bod2)) {
            tm1 = kn::lift(bod1, -1);
            tm2 = kn::lift(bod2, -1);
        }
        else {
            tm1 = mk_nabs(tm1->ty->dom(), bod1);
            tm2 = mk_nabs(tm2->ty->dom(), bod2);
        }
    }
}

void remove_dummy_bvar(Term *&tm)
{
    // no need to eta-norm to rsl, since eta redex will be eliminated soon
    if (tm->is_abs()) {
        Term *bod = tm->bod();
        remove_dummy_bvar(bod);
        if (!vfree_in(0, bod))
            tm = kn::lift(bod, -1);
        else
            tm = mk_nabs(tm->ty->dom(), bod);
    }
}

/*
 * reduce `\x. tm` and sub
 * replace all 0 in x with tm2 and
 * reduce all positive idx by one
 */

Term *do_beta(Term *tm, Term *sub, int scope)
{
    std::tuple<Term *, Term *, int> key(tm, sub, scope);
    auto it = kn::beta_map.hmap.find(key);
    if (it != kn::beta_map.hmap.end()) return it->second;

    Term *ret;
    if (tm->is_comb())
        ret = mk_ncomb(do_beta(tm->rator(), sub, scope), do_beta(tm->rand(), sub, scope));
    else if (tm->is_abs())
        ret = mk_nabs(tm->ty->dom(), do_beta(tm->bod(), sub, scope + 1));
    else if (tm->idx == scope)
        ret = kn::lift(sub, scope);
    else if (tm->idx > scope)
        ret = kn::mk_var(tm->ty, tm->idx - 1);
    else
        ret = tm;
    kn::beta_map.insert(key, ret);
    return ret;
}

Term *_reorder(int x, int scope, Term *tm)
{
    if (tm->is_comb())
        return kn::mk_comb(_reorder(x, scope, tm->rator()), _reorder(x, scope, tm->rand()));
    else if (tm->is_abs())
        return kn::mk_abs(tm->ty->dom(), _reorder(x, scope + 1, tm->bod()));
    else if (tm->idx == x + scope)
        return kn::mk_var(tm->ty, scope);
    else if (tm->idx < scope)
        return tm;
    else
        return kn::mk_var(tm->ty, tm->idx + 1);

}

Term *abstraction(int x, Type *ty, Term *tm)
{
    return kn::mk_abs(ty, _reorder(x, 0, tm));
}

void get_free_types(Type *ty, std::unordered_set<int> &ty_set)
{
    if (ty->is_fun()) {
        get_free_types(ty->dom(), ty_set);
        get_free_types(ty->cod(), ty_set);
    }
    else if (kn::is_vartype(ty))
        ty_set.insert(ty->idx);
}

void get_frees(Term *tm, std::unordered_set<int> &ty_set, std::unordered_set<Term *> &tm_set, int scope)
{
    if (tm->is_comb()) {
        get_frees(tm->rator(), ty_set, tm_set, scope);
        get_frees(tm->rand(), ty_set, tm_set, scope);
    }
    else if (tm->is_abs()) {
        get_free_types(tm->ty->dom(), ty_set);
        get_frees(tm->bod(), ty_set, tm_set, scope + 1);
    }
    else {
        get_free_types(tm->ty, ty_set);
        if (kn::is_fvar(tm, scope))
            tm_set.insert(kn::mk_var(tm->ty, tm->idx - scope));
    }
}

void _print_type(std::ostream &os, const Type *ty)
{
    if (ty->is_fun()) {
        if (ty->dom()->is_fun()) {
            os << "(";
            _print_type(os, ty->dom());
            os << ")->";
            _print_type(os, ty->cod());
        }
        else {
            _print_type(os, ty->dom());
            os << "->";
            _print_type(os, ty->cod());
        }
    }
    else
        os << ty->idx;
}

std::ostream &operator<<(std::ostream &os, const Type &ty)
{
    os << "`:";
    _print_type(os, &ty);
    os << "`";
    return os;
}

std::ostream &operator<<(std::ostream &os, const Type *ty)
{
    os << *ty;
    return os;
}

void _print_term(std::ostream &os, const Term *tm, int scope)
{
    if (tm->is_comb() && tm->rator()->is_comb() && tm->rator()->rator()->is_leaf() && tm->rator()->rator()->idx == scope) {
        // a = b
        if (! tm->rator()->rand()->is_leaf()) {
            os << "(";
            _print_term(os, tm->rator()->rand(), scope);
            os << ")";
        }
        else
            _print_term(os, tm->rator()->rand(), scope);
        os << " = ";
        if (! tm->rand()->is_leaf()) {
            os << "(";
            _print_term(os, tm->rand(), scope);
            os << ")";
        }
        else
            _print_term(os, tm->rand(), scope);
    }
    else if (tm->is_comb()) {
        if (tm->rator()->is_abs()) {
            os << "(";
            _print_term(os, tm->rator(), scope);
            os << ")";
        }
        else
            _print_term(os, tm->rator(), scope);
        os << " ";
        if (tm->rand()->is_leaf())
            _print_term(os, tm->rand(), scope);
        else {
            os << "(";
            _print_term(os, tm->rand(), scope);
            os << ")";
        }
    }
    else if (tm->is_abs()) {
        os << "\\" << "u" << scope << ". ";
        _print_term(os, tm->bod(), scope + 1);
    }
    else {
        if (tm->idx < scope)
            os << "u" << scope - tm->idx - 1;
        else if (kn::is_const(tm, scope))
            os << "C" << tm->idx - scope;
        else
            os << "x" << tm->idx - scope;
    }
}

std::ostream &operator<<(std::ostream &os, const Term &tm)
{
    os << "`";
    _print_term(os, &tm, 0);
    os << "`";
    return os;
}

std::ostream &operator<<(std::ostream &os, const Term *tm)
{
    os << *tm;
    return os;
}
