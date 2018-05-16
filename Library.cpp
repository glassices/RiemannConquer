//
// Created by 冯迭乔 on 5/10/18.
//

#include "Library.h"

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
    for (auto &e : tmins) e.second = beta_eta_term(vsubst(idx, sub, e.second));
    tmins.insert(std::make_pair(idx, sub));
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
    for (auto &e : tmins) e.second = beta_eta_term(vsubst(idx, sub, e.second));
}

void update_tmins(const ty_instor &theta, tm_instor &tmins)
{
    for (auto &e : tmins) e.second = inst(theta, e.second);
}

void update_tmins(const tm_instor &theta, tm_instor &tmins)
{
    for (auto &e : tmins) e.second = beta_eta_term(vsubst(theta, e.second));
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

bool vfree_in(int idx, Term *tm, int scope)
{
    if (tm->is_comb())
        return vfree_in(idx, tm->rator(), scope) || vfree_in(idx, tm->rand(), scope);
    else if (tm->is_abs())
        return vfree_in(idx, tm->bod(), scope + 1);
    else
        return tm->idx == scope + idx;
}

Term *inst(const ty_instor &theta, Term *tm)
{
    if (tm->is_comb())
        return kn::mk_comb(inst(theta, tm->rator()), inst(theta, tm->rand()));
    else if (tm->is_abs())
        return kn::mk_abs(type_subst(theta, tm->ty->dom()), inst(theta, tm->bod()));
    else
        return kn::mk_var(type_subst(theta, tm->ty), tm->idx);
}

Term *inst(const ty_instor &theta, Term *tm, std::unordered_map<Term *, Term *> &minst)
{
    auto it = minst.find(tm);
    if (it != minst.end()) return it->second;

    if (tm->is_comb())
        return minst[tm] = kn::mk_comb(inst(theta, tm->rator(), minst), inst(theta, tm->rand(), minst));
    else if (tm->is_abs())
        return minst[tm] = kn::mk_abs(type_subst(theta, tm->ty->dom()), inst(theta, tm->bod(), minst));
    else
        return minst[tm] = kn::mk_var(type_subst(theta, tm->ty), tm->idx);
}

Term *vsubst(int idx, Term *sub, Term *tm, int scope)
{
    if (tm->is_comb())
        return kn::mk_comb(vsubst(idx, sub, tm->rator(), scope), vsubst(idx, sub, tm->rand(), scope));
    else if (tm->is_abs())
        return kn::mk_abs(tm->ty->dom(), vsubst(idx, sub, tm->bod(), scope + 1));
    else if (tm->idx == idx + scope)
        // lift(term, inc, scope = 0)
        return kn::lift(sub, scope);
    else
        return tm;
}

Term *vsubst(int idx, Term *sub, Term *tm,
             std::unordered_map<std::pair<Term *, int>, Term *, pair_hash> &mvsub, int scope)
{
    auto key = std::make_pair(tm, scope);
    auto it = mvsub.find(key);
    if (it != mvsub.end()) return it->second;

    if (tm->is_comb())
        return mvsub[key] = kn::mk_comb(vsubst(idx, sub, tm->rator(), mvsub, scope), vsubst(idx, sub, tm->rand(), mvsub, scope));
    else if (tm->is_abs())
        return mvsub[key] = kn::mk_abs(tm->ty->dom(), vsubst(idx, sub, tm->bod(), mvsub, scope + 1));
    else if (tm->idx == idx + scope)
        // lift(term, inc, scope = 0)
        return mvsub[key] = kn::lift(sub, scope);
    else
        return mvsub[key] = tm;
}

Term *vsubst(const tm_instor &tmins, Term *tm, int scope)
{
    if (tm->is_comb())
        return kn::mk_comb(vsubst(tmins, tm->rator(), scope), vsubst(tmins, tm->rand(), scope));
    else if (tm->is_abs())
        return kn::mk_abs(tm->ty->dom(), vsubst(tmins, tm->bod(), scope + 1));
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

    if (tm->is_comb())
        return mvsub[key] = kn::mk_comb(vsubst(tmins, tm->rator(), mvsub, scope), vsubst(tmins, tm->rand(), mvsub, scope));
    else if (tm->is_abs())
        return mvsub[key] = kn::mk_abs(tm->ty->dom(), vsubst(tmins, tm->bod(), mvsub, scope + 1));
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

Term *compose(const std::vector<Type *> &bvs, Term *hs, const std::vector<Term *> &args)
{
    return mk_labs(bvs, mk_lcomb(hs, args));
}

bool _is_eta(Term *tm)
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
            tm1 = _is_eta(bod1) ? kn::lift(bod1->rator(), -1) : kn::mk_abs(tm1->ty->dom(), bod1);
            tm2 = _is_eta(bod2) ? kn::lift(bod2->rator(), -1) : kn::mk_abs(tm2->ty->dom(), bod2);
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
            tm = kn::mk_abs(tm->ty->dom(), bod);
    }
}

/*
 * reduce `tm1 tm2` where tm1 is abs
 * replace all 0 in tm1->bod with tm2 and
 * reduce all positive idx by one
 */

Term *_beta(Term *tm, Term *sub, int scope)
{
    std::tuple<Term *, Term *, int> key(tm, sub, scope);
    auto it = kn::beta_map.hmap.find(key);
    if (it != kn::beta_map.hmap.end()) return it->second;

    Term *ret;
    if (tm->is_comb())
        ret = kn::mk_comb(_beta(tm->rator(), sub, scope), _beta(tm->rand(), sub, scope));
    else if (tm->is_abs())
        ret = kn::mk_abs(tm->ty->dom(), _beta(tm->bod(), sub, scope + 1));
    else if (tm->idx == scope)
        ret = kn::lift(sub, scope);
    else if (tm->idx > scope)
        ret = kn::mk_var(tm->ty, tm->idx - 1);
    else
        ret = tm;
    kn::beta_map.insert(key, ret);
    return ret;
}

Term *application(Term *tm1, Term *tm2)
{
    assert(tm1->is_abs() && tm1->ty->dom() == tm2->ty);

    return _beta(tm1->bod(), tm2, 0);
}

Term *beta_eta_term(Term *tm)
{
    if (tm->is_leaf()) return tm;

    // this hash method is very naive
    auto it = kn::nform_map.hmap.find(tm);
    if (it != kn::nform_map.hmap.end()) return it->second;

    if (tm->is_comb()) {
        Term *tm1 = beta_eta_term(tm->rator());
        Term *ret = tm1->is_abs() ? beta_eta_term(application(tm1, tm->rand()))
                                  : kn::mk_comb(tm1, beta_eta_term(tm->rand()));
        kn::nform_map.insert(tm, ret);
        return ret;
    }
    else {
        Term *bod = beta_eta_term(tm->bod());
        // eta-reduction
        Term *ret = _is_eta(bod) ? kn::lift(bod->rator(), -1)
                                 : kn::mk_abs(tm->ty->dom(), bod);
        kn::nform_map.insert(tm, ret);
        return ret;
    }
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

void get_types(Type *ty, std::unordered_set<Type *> &tset)
{
    if (tset.find(ty) == tset.end()) {
        tset.insert(ty);
        if (ty->is_fun()) {
            get_types(ty->dom(), tset);
            get_types(ty->cod(), tset);
        }
    }
}

void get_terms(Term *tm, std::unordered_set<Type *> &tyset, std::unordered_set<Term *> &tmset)
{
    if (tmset.find(tm) == tmset.end()) {
        tmset.insert(tm);
        if (tm->is_comb()) {
            get_terms(tm->rator(), tyset, tmset);
            get_terms(tm->rand(), tyset, tmset);
        }
        else if (tm->is_abs()) {
            get_types(tm->ty->dom(), tyset);
            get_terms(tm->bod(), tyset, tmset);
        }
        else
            get_types(tm->ty, tyset);
    }
}

void distill_type(Type *ty, std::unordered_set<int> &ty_name, std::unordered_set<Type *> &ty_ptr)
{
    if (ty_ptr.find(ty) == ty_ptr.end()) {
        ty_ptr.insert(ty);
        if (ty->is_fun()) {
            distill_type(ty->dom(), ty_name, ty_ptr);
            distill_type(ty->cod(), ty_name, ty_ptr);
        }
        else
            ty_name.insert(ty->idx);
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
