//
// Created by 冯迭乔 on 5/14/18.
//

#include "Search.h"
#include "ProofGraph.h"
#include <iostream>

using namespace std;

Node *_cores(Node *node, Node *root)
{
    // find the corresponding node in root
    std::vector<bool> choice; // is_p1
    for ( ; node->par; node = node->par)
        choice.push_back(node == node->par->p1);
    for (auto it = choice.rbegin(); it != choice.rend(); ++it)
        root = *it ? root->p1 : root->p2;
    return root;
}

Node *_get_todo(Node *k)
{
    if (k->is_binary()) {
        Node *res = _get_todo(k->p1);
        return res ? res : _get_todo(k->p2);
    }
    else if (k->is_unary())
        return _get_todo(k->p1);
    return k->tag == Node::todo ? k : nullptr;
}

int _count_deduct(Node *k)
{
    // count the number of deduct among [k->par, k->par->par, k->par->par->par, ...]
    int res = 0;
    for ( ; k->par != nullptr; k = k->par)
        res += k->par->tag == Node::deduct;
    return res;
}

// if solution is found, return true and set state to the solution
bool _naive_dfs(ProofGraph &state, int rem_node)
{
    kn::save_maps();
    //cout << state.root << rem_node << endl;
    Node *todo = _get_todo(state.root);
    if (todo) {
        ProofGraph next_state;
        if (rem_node > 0) {
            next_state = state;
            if (next_state.req_mp(_cores(todo, next_state.root)) && _naive_dfs(next_state, rem_node - 1)) {
                state = next_state;
                return true;
            }

            next_state = state;
            if (next_state.rmk_comb(_cores(todo, next_state.root)) && _naive_dfs(next_state, rem_node - 1)) {
                state = next_state;
                return true;
            }

            next_state = state;
            if (next_state.rtrans(_cores(todo, next_state.root)) && _naive_dfs(next_state, rem_node - 1)) {
                state = next_state;
                return true;
            }

            next_state = state;
            if (next_state.rdeduct(_cores(todo, next_state.root)) && _naive_dfs(next_state, rem_node - 1)) {
                state = next_state;
                return true;
            }

            next_state = state;
            if (next_state.rabs(_cores(todo, next_state.root)) && _naive_dfs(next_state, rem_node - 1)) {
                state = next_state;
                return true;
            }
        }

        int ndeduct = _count_deduct(todo);
        for (int i = 0; i < ndeduct; i++) {
            next_state = state;
            if (next_state.rassume(_cores(todo, next_state.root), i) && _naive_dfs(next_state, rem_node)) {
                state = next_state;
                return true;
            }
        }

        next_state = state;
        if (next_state.rrefl(_cores(todo, next_state.root)) && _naive_dfs(next_state, rem_node)) {
            state = next_state;
            return true;
        }
    }
    else {
        // all nodes are closed and do unification
        std::pair<ty_instor, tm_instor> res;
        if (term_unify(state.obj, state.rsl, res)) {
            state.root->update_all(res.first, res.second);
            return true;
        }
    }
    kn::load_maps();
    return false;
}

thm _get_proof(Node *k)
{
    if (k->is_binary()) {
        thm th1 = _get_proof(k->p1);
        thm th2 = _get_proof(k->p2);
        std::unordered_set<Term *> asl1 = th1.first, asl2 = th2.first;
        Term *c1 = th1.second, *c2 = th2.second;

        if (k->tag == Node::eq_mp) {
            assert(kn::is_equal(c1) && c1->rator()->rand() == c2);
            asl1.insert(asl2.begin(), asl2.end());
            thm th(asl1, c1->rand());
            std::cout << "EQ_MP\t" << th << std::endl;
            return th;
        }
        else if (k->tag == Node::mk_comb) {
            assert(kn::is_equal(c1) && kn::is_equal(c2) && c1->rand()->ty->dom() == c2->rand()->ty);
            asl1.insert(asl2.begin(), asl2.end());
            Term *tm1 = beta_eta_term(kn::mk_comb(c1->rator()->rand(), c2->rator()->rand()));
            Term *tm2 = beta_eta_term(kn::mk_comb(c1->rand(), c2->rand()));
            thm th(asl1, kn::mk_eq(tm1, tm2));
            std::cout << "MK_COMB\t" << th << std::endl;
            return th;
        }
        else if (k->tag == Node::trans) {
            assert(kn::is_equal(c1) && kn::is_equal(c2) && c1->rand() == c2->rator()->rand());
            asl1.insert(asl2.begin(), asl2.end());
            thm th(asl1, kn::mk_eq(c1->rator()->rand(), c2->rand()));
            std::cout << "TRANS\t" << th << std::endl;
            return th;
        }
        else {
            asl1.erase(c2);
            asl2.erase(c1);
            asl1.insert(asl2.begin(), asl2.end());
            thm th(asl1, kn::mk_eq(c1, c2));
            std::cout << "DEDUCT\t" << th << std::endl;
            return th;
        }
    }
    else if (k->is_unary()) {
        assert(false);
        return _get_proof(k->p1);
        //thm thh = _get_proof(k->p1);
        //std::unordered_set<Term *> asl = thh.first;
        //Term *c = thh.second;

        //for (auto &tm : asl) if (vfree_in(k->c, tm)) assert(false);
        //assert(kn::is_equal(c));
        //thm th(asl, kn::mk_eq(abstraction(k->c, c->rator()->rand()))

        //_print_proof(k->p1);
        //std::cout << "ABS\t" << k->tm << '\t' << k->c << '\t' << k->p1->tm << std::endl;
    }
    else if (k->tag == Node::assume) {
        std::unordered_set<Term *> asl({k->tm});
        thm th(asl, k->tm);
        std::cout << "ASSUME\t" << th << std::endl;
        return th;
    }
    else {
        assert(kn::is_equal(k->tm) && k->tm->rator()->rand() == k->tm->rand());
        std::unordered_set<Term *> asl;
        thm th(asl, k->tm);
        std::cout << "REFL\t" << th << std::endl;
        return th;
    }
}

bool search(Term *goal, int max_node)
{
    ProofGraph state = ProofGraph(goal);
    std::cout << "Goal is: " << goal << std::endl;
    bool ok = _naive_dfs(state, max_node);
    if (ok) {
        std::cout << "Proof found" << std::endl;
        _get_proof(state.root);
    }
    else {
        std::cout << "Failed to find a proof..." << std::endl;
    }
    return ok;
}