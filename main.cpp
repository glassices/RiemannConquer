#include <iostream>
#include "Unification.h"
#include "ProofGraph.h"
#include "Search.h"

using namespace std;
using namespace kn;

vector<Term *> defs;

void init_logic()
{
    /*
    |- (~) = (\p. p ==> F); |- F <=> (!p. p);
    |- (\/) = (\p q. !r. (p ==> r) ==> (q ==> r) ==> r);
    |- (?) = (\P. !q. (!x. P x ==> q) ==> q); |- (!) = (\P. P = (\x. T));
    |- (==>) = (\p q. p /\ q <=> p);
    |- (/\) = (\p q. (\f. f p q) = (\f. f T T)); |- T <=> (\p. p) = (\p. p)]
    */

    Type *aty, *pty;
    Term *tm, *f;

    defs.push_back(nullptr); // 0 for (=)

    defs.push_back(nullptr); // 1 for (@)

    Term *id = mk_abs(bool_ty, mk_var(bool_ty, -1));
    defs.push_back(mk_eq(id, id)); // 2 for (T)

    Type *fty = mk_fun(bool_ty, mk_fun(bool_ty, bool_ty));
    f = mk_var(fty, -1);
    tm = mk_abs(bool_ty, mk_abs(bool_ty, mk_eq(mk_abs(fty, mk_lcomb({f, mk_var(bool_ty, -3), mk_var(bool_ty, -2)})),
                                               mk_abs(fty, mk_lcomb({f, mk_var(bool_ty, 2), mk_var(bool_ty, 2)})))));
    defs.push_back(tm); // 3 for (/\)

    tm = mk_abs(bool_ty, mk_abs(bool_ty, mk_eq(mk_lcomb({mk_var(fty, 3), mk_var(bool_ty, -2), mk_var(bool_ty, -1)}),
                                               mk_var(bool_ty, -2))));
    defs.push_back(tm); // 4 for (==>)

    aty = new_type();
    pty = mk_fun(aty, bool_ty);

    tm = mk_abs(pty, mk_eq(mk_var(pty, -1), mk_abs(aty, mk_var(bool_ty, 2))));
    defs.push_back(tm); // 5 for (!)

    /*
     * (?:(A->bool)->bool) = (\P:A->bool. (!:(bool->bool)->bool) (\q:bool. (==>) ((!:(A->bool)->bool) (\x:A. (==>) (P x) q)) q))
     */
    tm = mk_abs(pty, mk_comb(mk_var(mk_fun(mk_fun(bool_ty, bool_ty), bool_ty), 5),
                             mk_abs(bool_ty, mk_lcomb({mk_var(fty, 4),
                                                       mk_comb(mk_var(mk_fun(pty, bool_ty), 5),
                                                               mk_abs(aty, mk_lcomb({mk_var(fty, 4),
                                                                                     mk_comb(mk_var(pty, -3), mk_var(aty, -1)),
                                                                                     mk_var(bool_ty, -2)}))),
                                                       mk_var(bool_ty, -1)}))));
    defs.push_back(tm); // 6 for (!)

}

Term *_expand(Term *tm, int c, Term *def)
{
    if (tm->is_comb())
        return mk_ncomb(_expand(tm->rator(), c, def), _expand(tm->rand(), c, def));
    else if (tm->is_abs())
        return mk_nabs(tm->ty->dom(), _expand(tm->bod(), c, def));
    else if (tm->idx == c) {
        ty_instor tyins;
        type_unify(tm->ty, def->ty, tyins);
        return raw_inst(tyins, def);
    }
    else
        return tm;
}

Term *expand(Term *tm)
{
    for (int i = static_cast<int>(defs.size()) - 1; i >= 0; i--) {
        if (defs[i])
            tm = _expand(tm, i, defs[i]);
    }
    return tm;
}

void logic_test()
{
    // 0(=), 1(@), 2(T), 3(/\), 4(==>), 5(!)

    Term *p = mk_var(bool_ty, 1000);
    Term *q = mk_var(bool_ty, 1001);
    Type *booo = mk_fun(bool_ty, mk_fun(bool_ty, bool_ty));

    Term *p_and_q = expand(mk_lcomb({mk_var(booo, 3), p, q}));
    cout << "p /\\ q: " << p_and_q << endl;

    Term *p_and_q_imp_p = expand(mk_lcomb({mk_var(booo, 4), p_and_q, p}));
    cout << "(p /\\ q) ==> p: " << p_and_q_imp_p << endl;

    Term *p_imp_p = expand(mk_lcomb({mk_var(booo, 4), p, p}));
    cout << "p ==> p: " << p_imp_p << endl;

    Type *boo = mk_fun(bool_ty, bool_ty);
    Term *tm = mk_nabs(bool_ty, mk_ncomb(mk_var(boo, 1002), mk_var(bool_ty, -1)));
    cout << tm << endl;

}

void searcher_test()
{
    // 0(=), 1(@), 2(T), 3(/\), 4(==>), 5(!)
    Type *booo = mk_fun(bool_ty, mk_fun(bool_ty, bool_ty));
    Type *aty = mk_atom(kn::LO_CONST_TYPE);
    Type *pty = mk_fun(aty, bool_ty);
    Type *quan_ty = mk_fun(pty, bool_ty);
    Term *p = mk_var(bool_ty, kn::MD_CONST_TERM + 0);
    Term *q = mk_var(bool_ty, kn::MD_CONST_TERM + 1);
    Term *P = mk_var(pty, kn::MD_CONST_TERM + 2);

    Term *p_imp_p = expand(mk_lcomb({mk_var(booo, 4), p, p}));
    Term *abs_p_imp_p = mk_eq(abstraction(p->idx, bool_ty, p_imp_p->rator()->rand()),
                              abstraction(p->idx, bool_ty, p_imp_p->rand()));
    Term *p_and_p = expand(mk_lcomb({mk_var(booo, 3), p, p}));
    Term *monster = expand(mk_lcomb({mk_var(booo, 4), p_and_p, p_and_p}));
    Term *p_and_q_imp_p = expand(mk_lcomb({mk_var(booo, 4), mk_lcomb({mk_var(booo, 3), p, q}), p}));
    Term *forall_imp_exists = expand(mk_lcomb({mk_var(booo, 4), mk_comb(mk_var(quan_ty, 5), P), mk_comb(mk_var(quan_ty, 6), P)}));

    search(forall_imp_exists, 8);

    /*
    search(mk_eq(p, p), 1);
    puts("--------------------------------");
    */

    /*
    search(p_imp_p, 6);
    */

    /*
    */

    /*
    search(monster, 6);
    */

    /*
    search(p_and_q_imp_p, 5);
    puts("--------------------------------");
    */
}

int main() {
    init_logic();

    //logic_test();

    searcher_test();


    std::cout << "Hello, World!" << std::endl;
    return 0;
}