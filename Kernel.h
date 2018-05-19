//
// Created by 冯迭乔 on 5/10/18.
//

#ifndef BPRIL_KERNEL_H
#define BPRIL_KERNEL_H

#include "TypeTerm.h"
#include <vector>
#include <cassert>
#include <map>
#include <unordered_set>
#include <unordered_map>

namespace kn
{
    /*
     * [0, LO_CONST_TYPE) are reserved for system atom types which can not be touched
     * [LO_CONST_TYPE, HI_CONST_TYPE) are for user-defined const types
     */
    extern const int LO_CONST_TYPE;
    extern const int HI_CONST_TYPE;

    /*
     * [0, LO_CONST_TERM) are reserved for system constants which can not be touched
     * [LO_CONST_TERM, MD_CONST_TERM) are reserved for mc variables used in ABS rules
     * [MD_CONST_TERM, HI_CONST_TERM) are for user-defined const variables
     */
    extern const int LO_CONST_TERM;
    extern const int MD_CONST_TERM;
    extern const int HI_CONST_TERM;


    struct NamePool
    {
        int ptr;
        std::vector<int> used;
        std::vector<int> aval;
        std::vector<size_t> ckpt;

        explicit NamePool(int);
        int gen();
        void add_ckpt();
        void rec_ckpt();
        void rec_ckpt(std::unordered_set<int> &);
    };

    extern NamePool type_name_pool;
    extern NamePool term_name_pool;

    template<class T>
    struct PointerPool
    {
        std::vector<T *> pool;
        std::unordered_map<T, T *, typename T::hash> hmap;
        std::vector<size_t> ckpt;

        T *insert(const T &t)
        {
            auto it = hmap.find(t);
            if (it != hmap.end())
                return it->second;
            else {
                T *cnt = new T(t);
                pool.push_back(cnt);
                hmap[t] = cnt;
                return cnt;
            }
        }

        void add_ckpt()
        {
            ckpt.push_back(pool.size());
        }

        void rec_ckpt()
        {
            assert(!ckpt.empty());

            auto n = ckpt.back();
            ckpt.pop_back();
            for (auto it = pool.begin() + n; it != pool.end(); ++it) {
                hmap.erase(**it);
                delete *it;
            }
            pool.resize(n);
        }

        void rec_ckpt(std::unordered_set<T *> &pset)
        {
            assert(!ckpt.empty());

            auto n = ckpt.back();
            ckpt.pop_back();
            for (auto it = pool.begin() + n; it != pool.end(); it++) {
                if (pset.find(*it) != pset.end())
                    pool[n++] = *it;
                else {
                    hmap.erase(**it);
                    delete *it;
                }
            }
            pool.resize(n);
        }
    };

    template<class T1, class T2, typename T3>
    struct PersistentMap
    {
        std::vector<T1> pool;
        std::unordered_map<T1, T2, T3> hmap;
        std::vector<size_t> ckpt;

        void insert(const T1 &key, const T2 &val)
        {
            /*
             * key is guaranteed not to exists in hmap
             */
            hmap.emplace(key, val);
            pool.push_back(key);
        }

        void add_ckpt()
        {
            ckpt.push_back(pool.size());
        }

        void rec_ckpt()
        {
            assert(!ckpt.empty());

            auto n = ckpt.back();
            ckpt.pop_back();
            for (auto it = pool.begin() + n; it != pool.end(); ++it) hmap.erase(*it);
            pool.resize(n);
        }
    };

    extern PointerPool<Type> type_pointer_pool;
    extern PointerPool<Term> term_pointer_pool;

    Type *mk_atom(int);
    Type *mk_fun(Type *, Type *);
    Type *new_type();
    Type *mk_lfun(std::vector<Type *> &, Type *);
    bool is_contype(Type *);
    bool is_vartype(Type *);

    Term *mk_comb(Term *, Term *);
    Term *mk_abs(Type *, Term *);
    Term *mk_var(Type *, int);
    Term *new_term(Type *, int = 0);
    bool is_const(const Term *, int = 0);
    bool is_fvar(Term *, int = 0);
    bool is_bvar(Term *, int = 0);
    bool is_equal(Term *);
    Term *lift(Term *, int, int = 0);
    Term *mk_eq(Term *, Term *, int = 0);

    extern Type *const bool_ty;

    struct tuple_hash
    {
        template <class T1, class T2, class T3>
        std::size_t operator()(const std::tuple<T1, T2, T3> &p) const
        {
            auto h1 = std::hash<T1>{}(std::get<0>(p));
            auto h2 = std::hash<T2>{}(std::get<1>(p));
            auto h3 = std::hash<T3>{}(std::get<2>(p));
            return (h1 << 2) ^ (h2 << 1) ^ h3;
        }
    };

    extern PersistentMap<std::tuple<Term *, Term *, int>, Term *, tuple_hash> beta_map;

    extern PersistentMap<std::tuple<Term *, int, int>, Term *, tuple_hash> lift_map;

    void save_maps();
    void load_maps();
}

#endif //BPRIL_KERNEL_H
