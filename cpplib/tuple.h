#ifndef TUPLE_H
#define TUPLE_H

#include "global.h"
#include "trace.h"

namespace ttn {

    // Tuple def
    template<typename T>
    struct tuple<T> {
        static constexpr size_t size = 1;
        T v;

        tuple(const T& v): v(v) {}
        tuple(): v(T()) {}
        
        template<size_t N> requires(N == 0) const T& get() const { return v; }
        template<size_t N> requires(N == 0)       T& get()       { return v; }

        
        const String toString() const { return __to_string(v); }
    };

    template<typename T, typename ...Rest>
    struct tuple<T, Rest...> {
        static constexpr size_t size = 1 + tuple<Rest...>::size;
        T v;
        tuple<Rest...> rest;

        tuple(const T& v, const Rest&... args): v(v), rest(args...) {}
        tuple(): v(T()), rest() {}

        template<size_t N> requires(N >  0 && N < size) const auto& get() const { return rest.template get<N - 1>(); }
        template<size_t N> requires(N >  0 && N < size)       auto& get()       { return rest.template get<N - 1>(); }
        template<size_t N> requires(N == 0)             const T&    get() const { return v;                          }
        template<size_t N> requires(N == 0)                   T&    get()       { return v;                          }
        
        
        const String toString() const { return __to_string(v) + ", " + rest.toString(); }
    };

}


#endif