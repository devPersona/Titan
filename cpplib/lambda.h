#ifndef LAMBDA_H
#define LAMBDA_H

#include "global.h"

namespace ttn {
    template<typename Ret, typename ...Args>
    struct lambda<Ret(Args...)> {
        alignas(std::max_align_t) static constexpr size_t MaxSize = 64;
        byte buf[MaxSize];

        Ret (*invoke)(byte*, Args...) = nullptr;

        lambda() = default;
        
        template<typename F>
        lambda(F f) {
            new (buf) F(std::move(f));
            invoke = [](byte* p, Args... args) { return (*reinterpret_cast<F*>(p))(args...); };
        }

        template<typename F>
        lambda& operator=(F f) {
            new (buf) F(std::move(f));
            invoke = [](byte* p, Args... args) { return (*reinterpret_cast<F*>(p))(args...); };
            return *this;
        }

        Ret operator()(Args... args) { return invoke(buf, args...); }

        const String toString() { return "Lambda"; }
    };

}


#endif