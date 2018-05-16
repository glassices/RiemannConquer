//
// Created by 冯迭乔 on 5/13/18.
//

#include "ProofGraph.h"

const short Node::eq_mp = 0;
const short Node::mk_comb = 1;
const short Node::trans = 2;
const short Node::deduct = 3;
const short Node::abs = 4;
const short Node::assume = 5;
const short Node::refl = 6;
const short Node::todo = 7;


Node::Node(short _tag, Term *_tm, Node *_par, Node *_p1, Node *_p2, int _c)
    : tag(_tag), tm(_tm), par(_par), p1(_p1), p2(_p2), c(_c)
{}

bool Node::is_binary() const
{
    return tag < 4;
}

bool Node::is_unary() const
{
    return tag == 4;
}

bool Node::is_leaf() const
{
    return tag > 4;
}

Node* Node::duplicate()
{
    auto k = new Node(*this);
    if (p1) {
        k->p1 = p1->duplicate();
        k->p1->par = k;
    }
    if (p2) {
        k->p2 = p2->duplicate();
        k->p2->par = k;
    }
    return k;
}

void Node::delete_all()
{
    if (p1) p1->delete_all();
    if (p2) p2->delete_all();
    delete this;
}

void Node::update_all(ty_instor &tyins, tm_instor &tmins)
{
    if (p1) p1->update_all(tyins, tmins);
    if (p2) p2->update_all(tyins, tmins);
    if (is_leaf() || (par && par->tag == Node::deduct))
        tm = beta_eta_term(vsubst(tmins, inst(tyins, tm)));
}

ProofGraph::ProofGraph()
    : root(nullptr), nc(kn::LO_CONST_TERM)
{}

ProofGraph::ProofGraph(Term *tm)
    : root(new Node(Node::todo, tm, nullptr, nullptr, nullptr, 0)), nc(kn::LO_CONST_TERM)
{}

ProofGraph::ProofGraph(const ProofGraph &other)
    : obj(other.obj), rsl(other.rsl), root(other.root->duplicate()), nc(other.nc)
{}

ProofGraph::~ProofGraph()
{
    if (root) root->delete_all();
}

void swap(ProofGraph &first, ProofGraph &second)
{
    std::swap(first.root, second.root);
    std::swap(first.obj, second.obj);
    std::swap(first.rsl, second.rsl);
    std::swap(first.nc, second.nc);
}

ProofGraph &ProofGraph::operator=(ProofGraph other)
{
    swap(*this, other);
    return *this;
}

/*
 * Here comes the most exciting parts!!!
 * Node k should be inside the proof graph, otherwise undefined behavior occurs
 */

bool ProofGraph::distill()
{
    ty_instor tyins;
    tm_instor tmins;
    if (simplify(obj, rsl, tyins, tmins)) {
        root->update_all(tyins, tmins);
        return true;
    }
    else
        return false;
}

/* tm <- (p = tm) and p
 * NOTE: no need to distill for EQ_MP
 */
bool ProofGraph::req_mp(Node *k)
{
    assert(k->tag == Node::todo);

    Term *p = kn::new_term(kn::bool_ty);
    k->tag = Node::eq_mp;
    k->p1 = new Node(Node::todo, kn::mk_eq(p, k->tm), k, nullptr, nullptr, 0);
    k->p2 = new Node(Node::todo, p, k, nullptr, nullptr, 0);
    return true;
}

/* (tm, s u = t v) <- (s = t) and (u = v)
 */
bool ProofGraph::rmk_comb(Node *k)
{
    assert(k->tag == Node::todo);

    Type *aty = kn::new_type(), *bty = kn::new_type();
    Term *s = kn::new_term(kn::mk_fun(aty, bty)), *u = kn::new_term(aty);
    Term *t = kn::new_term(kn::mk_fun(aty, bty)), *v = kn::new_term(aty);
    k->tag = Node::mk_comb;
    k->p1 = new Node(Node::todo, kn::mk_eq(s, t), k, nullptr, nullptr, 0);
    k->p2 = new Node(Node::todo, kn::mk_eq(u, v), k, nullptr, nullptr, 0);
    obj.emplace_front(k->tm, kn::mk_eq(kn::mk_comb(s, u), kn::mk_comb(t, v)));
    return distill();
}

/* (tm, s = t) <- (s = r) and (r = t)
 */
bool ProofGraph::rtrans(Node *k)
{
    assert(k->tag == Node::todo);

    Type *aty = kn::new_type();
    Term *s = kn::new_term(aty), *t = kn::new_term(aty), *r = kn::new_term(aty);
    k->tag = Node::trans;
    k->p1 = new Node(Node::todo, kn::mk_eq(s, r), k, nullptr, nullptr, 0);
    k->p2 = new Node(Node::todo, kn::mk_eq(r, t), k, nullptr, nullptr, 0);
    obj.emplace_front(k->tm, kn::mk_eq(s, t));
    return distill();
}

/* (tm, p = q) <- p and q
 */
bool ProofGraph::rdeduct(Node *k)
{
    assert(k->tag == Node::todo);

    Term *p = kn::new_term(kn::bool_ty), *q = kn::new_term(kn::bool_ty);
    k->tag = Node::deduct;
    k->p1 = new Node(Node::todo, p, k, nullptr, nullptr, 0);
    k->p2 = new Node(Node::todo, q, k, nullptr, nullptr, 0);
    obj.emplace_front(k->tm, kn::mk_eq(p, q));
    return distill();
}

/* (tm, u = v) <- u c = v c    u/c, v/c
 */
bool ProofGraph::rabs(Node *k)
{
    assert(k->tag == Node::todo);
    if (nc >= kn::MD_CONST_TERM) return false;

    Type *aty = kn::new_type(), *bty = kn::new_type();
    Term *u = kn::new_term(kn::mk_fun(aty, bty)), *v = kn::new_term(kn::mk_fun(aty, bty));
    Term *c = kn::mk_var(aty, nc);
    k->tag = Node::abs;
    k->p1 = new Node(Node::todo, kn::mk_eq(kn::mk_comb(u, c), kn::mk_comb(v, c)), k, nullptr, nullptr, 0);
    k->c = nc;
    obj.emplace_front(k->tm, kn::mk_eq(u, v));
    rsl.emplace_front(u, nc);
    rsl.emplace_front(v, nc);
    ++nc;
    return distill();
}

/* pick a deduct step b upper and match it with tm
 * (tm, mt) / cs
 */
bool ProofGraph::rassume(Node *k, int b)
{
    assert(k->tag == Node::todo);

    // all abstraction variable c should be avoided
    Node *kk = k;
    std::vector<int> cs;
    for ( ; kk->par->tag != Node::deduct || b > 0; kk = kk->par) {
        if (kk->par->tag == Node::deduct)
            b--;
        else if (kk->par->tag == Node::abs)
            cs.push_back(kk->par->c);
    }

    Term *mt = kk == kk->par->p1 ? kk->par->p2->tm : kk->par->p1->tm;
    k->tag = Node::assume;
    obj.emplace_front(k->tm, mt);
    for (auto &e : cs) rsl.emplace_front(mt, e);
    return distill();
}

/* refl and close the node
 * (tm, t = t)
 */
bool ProofGraph::rrefl(Node *k)
{
    assert(k->tag == Node::todo);

    Type *aty = kn::new_type();
    Term *t = kn::new_term(aty);
    k->tag = Node::refl;
    obj.emplace_front(k->tm, kn::mk_eq(t, t));
    return distill();
}
