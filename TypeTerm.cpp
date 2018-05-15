//
// Created by 冯迭乔 on 5/10/18.
//

#include "TypeTerm.h"

Type::Type(bool _tag, Type *_lptr, Type *_rptr, int _idx)
    : tag(_tag), lptr(_lptr), rptr(_rptr), idx(_idx)
{}

bool Type::is_atom() const
{
    return !tag;
}

bool Type::is_fun() const
{
    return tag;
}

Type *Type::dom() const
{
    return lptr;
}

Type *Type::cod() const
{
    return rptr;
}

int Type::arity()
{
    int res = 0;
    for (Type *cnt = this; cnt->is_fun(); cnt = cnt->cod())
        res++;
    return res;
}

std::pair<Type *,Type *> Type::dest_fun() const
{
    return std::make_pair(lptr, rptr);
}

void Type::strip_fun(std::vector<Type *> &tyl)
{
    tyl.clear();
    for (Type *cnt = this; cnt->is_fun(); cnt = cnt->rptr)
        tyl.push_back(cnt->lptr);
}

void Type::strip_fun(std::vector<Type *> &tyl, Type *&apx)
{
    tyl.clear();
    for (apx = this; apx->is_fun(); apx = apx->rptr)
        tyl.push_back(apx->lptr);
}

bool Type::operator==(const Type &other) const
{
    if (tag)
        return other.tag && lptr == other.lptr && rptr == other.rptr;
    else
        return !other.tag && idx == other.idx;
}

bool Type::operator<(const Type &other) const
{
    if (tag)
        return !other.tag || lptr < other.lptr || (lptr == other.lptr && rptr < other.rptr);
    else
        return !other.tag && idx < other.idx;
}

size_t Type::hash::operator()(const Type &t) const
{
    if (t.tag)
        return (std::hash<Type *>{}(t.lptr) << 2) ^ (std::hash<Type *>{}(t.rptr) << 1) ^ 1;
    else
        return std::hash<int>{}(t.idx) << 1;
}



Term::Term(short _tag, Type *_ty, Term *_p1, Term *_p2, int _idx, unsigned int _size)
        : tag(_tag), ty(_ty), p1(_p1), p2(_p2), idx(_idx), size(_size)
{}

bool Term::is_comb() const
{
    return tag == 0;
}

bool Term::is_abs() const
{
    return tag == 1;
}

bool Term::is_leaf() const
{
    return tag == 2;
}

Term *Term::rator() const
{
    return p1;
}

Term *Term::rand() const
{
    return p2;
}

Term *Term::bod() const
{
    return p1;
}

bool Term::operator==(const Term &other) const
{
    if (tag == 0)
        return other.tag == 0 && p1 == other.p1 && p2 == other.p2;
    else if (tag == 1)
        return other.tag == 1 && p1 == other.p1 && ty == other.ty;
    else
        return other.tag == 2 && idx == other.idx && ty == other.ty;
}

bool Term::operator<(const Term &other) const
{
    if (tag == 0)
        return other.tag > 0 || p1 < other.p1 || (p1 == other.p1 && p2 < other.p2);
    else if (tag == 1)
        return other.tag == 2 || (other.tag == 1 && (p1 < other.p1 || (p1 == other.p1 && ty < other.ty)));
    else
        return other.tag == 2 && (idx < other.idx || (idx == other.idx && ty < other.ty));
}

size_t Term::hash::operator()(const Term &t) const
{
    if (t.tag == 0)
        return (std::hash<Term *>{}(t.p1) << 3) ^ (std::hash<Term *>{}(t.p2) << 2);
    else if (t.tag == 1)
        return (std::hash<Term *>{}(t.p1) << 3) ^ (std::hash<Type *>{}(t.ty) << 2) ^ 1;
    else
        return (std::hash<int>{}(t.idx) << 3) ^ (std::hash<Type *>{}(t.ty) << 2) ^ 2;
}
