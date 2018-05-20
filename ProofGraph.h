//
// Created by 冯迭乔 on 5/13/18.
//

#ifndef BPRIL_PROOFGRAPH_H
#define BPRIL_PROOFGRAPH_H

#include "Unification.h"

struct Node
{
    short tag;
    Term *tm;
    Node *par;
    Node *p1, *p2;
    int c; // abstraction variable for ABS node

    static const short eq_mp, mk_comb, trans, deduct, abs, assume, refl, todo;

    Node(short, Term *, Node *, Node *, Node *, int);
    bool is_binary() const;
    bool is_unary() const;
    bool is_leaf() const;

    Node *duplicate();
    void delete_all();
    void update_all(const ty_instor &, const tm_instor &, vdict &);
};

class ProofGraph
{
public:

    Node *root;
    obj_type obj;
    rsl_type rsl;
    int nc;

    ProofGraph();
    explicit ProofGraph(Term *);
    ProofGraph(const ProofGraph &);
    ~ProofGraph();
    friend void swap(ProofGraph &, ProofGraph &);
    ProofGraph &operator=(ProofGraph);

    bool distill();
    bool req_mp(Node *);
    bool rmk_comb(Node *);
    bool rtrans(Node *);
    bool rdeduct(Node *);
    bool rabs(Node *);
    bool rassume(Node *, int);
    bool rrefl(Node *);
};


#endif //BPRIL_PROOFGRAPH_H
