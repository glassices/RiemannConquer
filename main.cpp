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

    Term *tm, *f;

    defs.push_back(nullptr); // 0 for (=)

    defs.push_back(nullptr); // 1 for (@)

    Term *id = mk_abs(bool_ty, mk_var(bool_ty, 0));
    defs.push_back(mk_eq(id, id)); // 2 for (T)

    Type *fty = mk_fun(bool_ty, mk_fun(bool_ty, bool_ty));
    f = mk_var(fty, 0);
    tm = mk_abs(bool_ty, mk_abs(bool_ty, mk_eq(mk_abs(fty, mk_lcomb({f, mk_var(bool_ty, 2), mk_var(bool_ty, 1)})),
                                               mk_abs(fty, mk_lcomb({f, mk_var(bool_ty, 5), mk_var(bool_ty, 5)})),
                                               2)));
    defs.push_back(tm); // 3 for (/\)

    tm = mk_abs(bool_ty, mk_abs(bool_ty, mk_eq(mk_lcomb({mk_var(fty, 5), mk_var(bool_ty, 1), mk_var(bool_ty, 0)}),
                                               mk_var(bool_ty, 1),
                                               2)));
    defs.push_back(tm); // 4 for (==>)

    Type *aty = new_type();
    Type *pty = mk_fun(aty, bool_ty);
    tm = mk_abs(pty, mk_eq(mk_var(pty, 0), mk_abs(aty, mk_var(bool_ty, 4)), 1));
    defs.push_back(tm); // 5 for (!)
}

Term *_expand(Term *tm, int c, Term *def, int scope)
{
    if (tm->is_comb())
        return mk_ncomb(_expand(tm->rator(), c, def, scope), _expand(tm->rand(), c, def, scope));
    else if (tm->is_abs())
        return mk_nabs(tm->ty->dom(), _expand(tm->bod(), c, def, scope + 1));
    else if (tm->idx == scope + c) {
        ty_instor tyins;
        type_unify(tm->ty, def->ty, tyins);
        return inst(tyins, lift(def, scope));
    }
    else
        return tm;
}

Term *expand(Term *tm)
{
    for (int i = static_cast<int>(defs.size()) - 1; i >= 0; i--) {
        if (defs[i])
            tm = _expand(tm, i, defs[i], 0);
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
    cout << p_and_q << endl;

    Term *p_and_q_imp_p = expand(mk_lcomb({mk_var(booo, 4), p_and_q, p}));
    cout << p_and_q_imp_p << endl;

    Term *p_imp_p = expand(mk_lcomb({mk_var(booo, 4), p, p}));
    cout << p_imp_p << endl;
}

void searcher_test()
{
    // 0(=), 1(@), 2(T), 3(/\), 4(==>), 5(!)
    Type *booo = mk_fun(bool_ty, mk_fun(bool_ty, bool_ty));
    Term *p = mk_var(bool_ty, kn::MD_CONST_TERM + 0);
    Term *q = mk_var(bool_ty, kn::MD_CONST_TERM + 1);

    /*
    search(mk_eq(p, p), 1);
    puts("--------------------------------");
    */

    Term *p_imp_p = expand(mk_lcomb({mk_var(booo, 4), p, p}));
    search(p_imp_p, 5);

    /*
     * p /\ q ==> p
     * (==>) ((/\) p q) p
     */
    /*
    Term *p_and_q_imp_p = expand(mk_lcomb({mk_var(booo, 4), mk_lcomb({mk_var(booo, 3), p, q}), p}));
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