#ifndef TRACE_H
#define TRACE_H

#include "global.h"

namespace ttn {

    // Main string conversion function
    const String __to_string(const char&   c) { return String(1, c);         }
    const String __to_string(const char*   s) { return String(s);            }
    const String __to_string(const String& s) { return s;                    }
    const String __to_string(const bool&   b) { return b ? "true" : "false"; }
    template<typename T> requires(std::is_arithmetic_v<T>)
    const String __to_string(const T&      v) { return std::to_string(v);    }
    const String __to_string(const void*   p) {
        static constexpr const char* hex = "0123456789abcdef";
        constexpr size_t N = (sizeof(uintptr_t) * 2) + 2;
        char buf[N]; // add 2 bytes for 0x
        buf[0] = '0';
        buf[1] = 'x';
        size_t i = N;
        uintptr_t v = reinterpret_cast<uintptr_t>(p);
        // TODO: learn some fucking bit operators
        while (i > 2) {
            uchar at = v % 256;
            buf[--i] = hex[at % 16];
            buf[--i] = hex[at / 16];
            v /= 256;
        }
        return String(buf, N);
    }
    template<TTNObj   T>
    const String __to_string(const T&               o) { return o.toString();             }
    template<typename ...Types>
    const String __to_string(const tuple<Types...>& t) { return "(" + t.toString() + ")"; }

    // Trace function
    template<typename T>
    const T& trace(const T& v) { std::cout << __to_string(v) << "\n"; return v; }
    template<typename T>
    T& trace(T& v) { std::cout << __to_string(v) << "\n"; return v; }
    template<typename ...Args>
    const tuple<Args...>  trace(Args...  args) { return trace(tuple<Args...>(args...)); }

    void trace_bytes(const void* p, size_t n) {
        static constexpr const char* hex = "0123456789ABCDEF";
        byte* bytes = (byte*)p;
        while (n) {
            std::cout << hex[*bytes / 16] << hex[*bytes % 16];
            if (--n) std::cout << ' ';
            bytes++;
        }
        std::cout << "\n";
    }
}


#endif

