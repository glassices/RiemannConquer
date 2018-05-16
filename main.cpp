#include <iostream>
#include "Unification.h"
#include "ProofGraph.h"
#include "Search.h"

using namespace std;
using namespace kn;

void memory_test()
{
    const int maxn = 10000000;
    for (int step = 0; step < 100; step++) {
        cout << step << endl;
        vector<Type *> pool;
        kn::type_name_pool.add_ckpt();
        kn::type_pointer_pool.add_ckpt();

        for (int i = 0; i < maxn; i++) {
            if (rand() % 2 == 0 || pool.size() < 2)
                pool.push_back(kn::new_type());
            else {
                Type *ty1 = pool[rand() % pool.size()];
                Type *ty2 = pool[rand() % pool.size()];
                pool.push_back(kn::mk_fun(ty1, ty2));
            }
        }

        unordered_set<int> name;
        unordered_set<Type *> type;
        for (int i = 0; i < 100; i++) {
            Type *ty = pool[rand() % pool.size()];
            distill_type(ty, name, type);
        }
        kn::type_name_pool.rec_ckpt(name);
        kn::type_pointer_pool.rec_ckpt(type);

        cout << "type_name[ptr]: " << kn::type_name_pool.ptr << "\ttype_name[used]: " << kn::type_name_pool.used.size() << "\ttype_name[aval]: " << kn::type_name_pool.aval.size() << endl;
        cout << "type_ptr[pool]: " << kn::type_pointer_pool.pool.size() << "\ttype_ptr[hmap]: " << kn::type_pointer_pool.hmap.size() << endl;
    }
}

void random_test()
{
    Type *xty = kn::new_type();
    Type *yty = kn::new_type();
    Type *cty = kn::new_type();
    Type *fty = kn::mk_fun(xty, kn::mk_fun(yty, kn::mk_atom(0)));
    Term *tm = kn::mk_abs(xty, kn::mk_abs(yty, kn::mk_comb(kn::mk_comb(kn::mk_var(fty, 10), kn::mk_var(xty, 1)), kn::mk_var(yty, 0))));
    cout << *tm << endl;
}

void trivial_test()
{
    Type *aty = kn::new_type();
    Type *bty = kn::new_type();
    Type *cty = kn::new_type();
    Type *boo = kn::mk_atom(0);
    Type *ind = kn::mk_atom(1);
    Type *ty1 = kn::mk_fun(aty, kn::mk_fun(ind, cty));
    Type *ty2 = kn::mk_fun(kn::mk_fun(bty, boo), aty);
    ty_instor tyins;
    cout << type_unify(ty1, ty2, tyins) << endl;
    cout << tyins << endl << type_subst(tyins, ty1) << ' ' << type_subst(tyins, ty2) << endl;

    // eta-reduction test
    Term *tm = kn::mk_abs(boo, kn::mk_comb(kn::mk_var(kn::mk_fun(boo, boo), 100), kn::mk_var(boo, 0)));
    cout << tm << endl;
    cout << beta_eta_term(tm) << ' ' << beta_eta_term(tm)->ty << endl;
    cout << endl;

    Type *boo_fun = kn::mk_fun(boo, boo);
    tm = kn::mk_comb(kn::mk_abs(boo_fun, kn::mk_abs(boo, kn::mk_comb(kn::mk_var(boo_fun, 1), kn::mk_var(boo, 3)))),
                     kn::mk_abs(boo, kn::mk_var(boo, 1)));
    cout << tm << endl;
    cout << tm->rator() << "    " << beta_eta_term(tm->rator()) << endl;
    Term *tm1 = beta_eta_term(tm->rator());
    Term *tm2 = tm->rand();
    cout << "f    " << tm1 << "    " << tm2 << "    " << application(tm1, tm2) << "    " << kn::lift(tm2, 0) << endl;
    Term *res = beta_eta_term(tm);
    cout << res << ' ' << res->ty << endl;
}

void simplify_test()
{
    Type *boo = mk_atom(0);
    Type *boo_fun = mk_fun(boo, boo);
    Type *bvs = mk_fun(boo_fun, mk_fun(boo, boo));

    Term *c = mk_var(bvs, 1);
    Term *tm1 = mk_comb(mk_comb(c, mk_var(boo_fun, 1000)), mk_comb(mk_var(boo_fun, 1000), mk_var(boo, 1001)));
    Term *tm2 = mk_comb(mk_comb(c, mk_abs(boo, mk_var(boo, 0))), mk_var(boo, 1002));
    cout << tm1 << '\t' << tm2 << endl;
    ty_instor tyins;
    tm_instor tmins;
    forward_list<pair<Term *, Term *>> obj = {make_pair(tm1, tm2)};
    forward_list<pair<Term *, int>> rsl;
    simplify(obj, rsl, tyins, tmins);
    for (auto &e : obj) cout << e.first << "\t\t\t" << e.second << endl;
    cout << endl << tyins << endl << tmins << endl;

    cout << "--------------------------------------------" << endl;
    Type *aty = new_type();
    Type *bty = new_type();
    tm1 = mk_comb(mk_var(mk_fun(aty, boo), 1), mk_var(aty, 1000));
    tm2 = mk_comb(mk_var(mk_fun(bty, boo), 1), mk_var(bty, 1001));
    cout << tm1 << "    " << tm2 << endl;
    tyins.clear();
    tmins.clear();
    obj = forward_list<pair<Term *, Term *>>({make_pair(tm1, tm2)});
    simplify(obj, rsl, tyins, tmins);
    for (auto &e : obj) cout << e.first << "\t\t\t" << e.second << endl;
    cout << endl << tyins << endl << tmins << endl;
    cout << "--------------------------------------------" << endl;

    tm1 = mk_abs(boo, mk_var(aty, 1000));
    tm2 = mk_abs(boo, mk_var(bty, 1001));
    cout << tm1 << "    " << tm2 << endl;
    tyins.clear();
    tmins.clear();
    obj = forward_list<pair<Term *, Term *>>({make_pair(tm1, tm2)});
    simplify(obj, rsl, tyins, tmins);
    for (auto &e : obj) cout << e.first << "\t\t\t" << e.second << endl;
    cout << endl << tyins << endl << tmins << endl;
    cout << "--------------------------------------------" << endl;

    tm1 = mk_abs(boo, mk_abs(boo, mk_comb(mk_var(boo_fun, 1002), mk_var(boo, 1))));
    tm2 = mk_abs(boo, mk_abs(boo, mk_comb(mk_var(boo_fun, 1004), mk_var(boo, 1005))));
    cout << tm1 << "    " << tm2 << endl;
    tyins.clear();
    tmins.clear();
    obj = forward_list<pair<Term *, Term *>>({make_pair(tm1, tm2)});
    simplify(obj, rsl, tyins, tmins);
    for (auto &e : obj) cout << e.first << "\t\t\t" << e.second << endl;
    cout << endl << tyins << endl << tmins << endl;
}

void unification_test()
{
    std::pair<ty_instor, tm_instor> res;

    Type *aty = new_type();
    Type *bty = new_type();
    Type *cty = new_type();

    Type *tb = mk_atom(0);
    Type *tbb = mk_fun(tb, tb);
    Type *tbbb = mk_fun(tb, tbb);
    Type *tbbbb = mk_fun(tb, tbbb);

    Term *a, *b, *c, *f, *x, *y, *z, *tm1, *tm2;

    obj_type obj;
    rsl_type rsl;

    // f x (y b) (y c)  =   f a b c
    f = mk_var(tbbbb, 10);
    x = mk_var(tb, 1000);
    y = mk_var(tbb, 1001);
    a = mk_var(tb, 1);
    b = mk_var(tb, 2);
    c = mk_var(tb, 3);
    tm1 = mk_lcomb({f, x, mk_comb(y, b), mk_comb(y, c)});
    tm2 = mk_lcomb({f, a, b, c});
    obj = forward_list<pair<Term *, Term *>>({make_pair(tm1, tm2)});
    cout << "task is: " << obj << endl;
    if (term_unify(obj, rsl, res))
        cout << res.first << ' ' << res.second << endl;
    cout << "--------------------" << endl;

    // x (f a) = f (x a)
    x = mk_var(tbb, 1000);
    f = mk_var(tbb, 10);
    a = mk_var(tb, 1);
    tm1 = mk_comb(x, mk_comb(f, a));
    tm2 = mk_comb(f, mk_comb(x, a));
    obj = forward_list<pair<Term *, Term *>>({make_pair(tm1, tm2)});
    cout << "task is: " << obj << endl;
    if (term_unify(obj, rsl, res))
        cout << res.first << ' ' << res.second << endl;
    cout << "--------------------" << endl;

    /* x (\y1 y2. y1 y2) and f a
     * x (\y3 y4. y3 (y3 y4)) and f (f a)
     */
    Type *xty = mk_fun(mk_fun(tbb, tbb), tb);
    f = mk_var(tbb, 10);
    a = mk_var(tb, 20);
    Term *tm11 = mk_comb(mk_var(xty, 1000), mk_abs(tbb, mk_abs(tb, mk_comb(mk_var(tbb, 1), mk_var(tb, 0)))));
    Term *tm12 = mk_comb(f, a);
    Term *tm21 = mk_comb(mk_var(xty, 1000), mk_abs(tbb, mk_abs(tb, mk_comb(mk_var(tbb, 1), mk_comb(mk_var(tbb, 1), mk_var(tb, 0))))));
    Term *tm22 = mk_comb(f, mk_comb(f, a));
    obj = forward_list<pair<Term *, Term *>>({make_pair(tm11, tm12), make_pair(tm21, tm22)});
    cout << "task is: " << obj << endl;
    if (term_unify(obj, rsl, res))
        cout << res.first << ' ' << res.second << endl;
    cout << "--------------------" << endl;

    tm11 = mk_comb(mk_var(mk_fun(tb, mk_atom(10)), kn::HI_CONST_TERM + 0), mk_var(tb, kn::HI_CONST_TERM + 1));
    tm12 = mk_comb(mk_var(mk_fun(tb, mk_atom(10)), kn::HI_CONST_TERM + 2), mk_var(tb, kn::HI_CONST_TERM + 3));
    tm21 = mk_comb(mk_var(mk_fun(tb, mk_atom(11)), kn::HI_CONST_TERM + 4), mk_var(tb, kn::HI_CONST_TERM + 5));
    tm22 = mk_comb(mk_var(mk_fun(tb, mk_atom(11)), kn::HI_CONST_TERM + 6), mk_var(tb, kn::HI_CONST_TERM + 7));
    obj = forward_list<pair<Term *, Term *>>({make_pair(tm11, tm12), make_pair(tm21, tm22)});
    cout << "task is: " << obj << endl;
    if (term_unify(obj, rsl, res))
        cout << res.first << ' ' << res.second << endl;
    cout << "--------------------" << endl;
}

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
        return mk_comb(_expand(tm->rator(), c, def, scope), _expand(tm->rand(), c, def, scope));
    else if (tm->is_abs())
        return mk_abs(tm->ty->dom(), _expand(tm->bod(), c, def, scope + 1));
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
    return beta_eta_term(tm);
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
    Term *p = mk_var(bool_ty, kn::LO_CONST_TERM + 0);
    /*
    search(mk_eq(p, p), 1);
    puts("--------------------------------");
    */

    Type *booo = mk_fun(bool_ty, mk_fun(bool_ty, bool_ty));
    Term *p_imp_p = expand(mk_lcomb({mk_var(booo, 4), p, p}));
    search(p, 6);
    cout << debug_t << endl;
    puts("--------------------------------");

}

int main() {
    //memory_test();

    //trivial_test();

    //simplify_test();

    //unification_test();

    init_logic();

    // logic_test();

    searcher_test();

    std::cout << "Hello, World!" << std::endl;
    return 0;
}