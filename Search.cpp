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

        return false;
    }
    else {
        // all nodes are closed and do unification
        std::pair<ty_instor, tm_instor> res;
        if (term_unify(state.obj, state.rsl, res)) {
            state.root->update_all(res.first, res.second);
            return true;
        }
        else
            return false;

    }
}

void _print_proof(Node *k)
{
    if (k->is_binary()) {
        _print_proof(k->p1);
        _print_proof(k->p2);
        if (k->tag == Node::eq_mp)
            std::cout << "EQ_MP\t";
        else if (k->tag == Node::mk_comb)
            std::cout << "MK_COMB\t";
        else if (k->tag == Node::trans)
            std::cout << "TRANS\t";
        else
            std::cout << "DEDUCT\t";
        std::cout << k->tm << '\t' << k->p1->tm << '\t' << k->p2->tm << std::endl;
    }
    else if (k->is_unary()) {
        _print_proof(k->p1);
        std::cout << "ABS\t" << k->tm << '\t' << k->c << '\t' << k->p1->tm << std::endl;
    }
    else if (k->tag == Node::assume)
        std::cout << "ASSUME\t" << k->tm << std::endl;
    else
        std::cout << "REFL\t" << k->tm << std::endl;
}

bool search(Term *goal, int max_node)
{
    ProofGraph state = ProofGraph(goal);
    std::cout << "Goal is: " << goal << std::endl;
    bool ok = _naive_dfs(state, max_node);
    if (ok) {
        std::cout << "Proof found" << std::endl;
        _print_proof(state.root);
    }
    else {
        std::cout << "Failed to find a proof..." << std::endl;
    }
    return ok;
}