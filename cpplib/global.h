#ifndef GLOBLE_H
#define GLOBLE_H

#include<iostream>
#include<string>
#include<cstdint>
#include<cstring>

namespace ttn {

    using ulong  = unsigned long;
    using uint   = unsigned int;
    using ushort = unsigned short;
    using uchar  = unsigned char;
    using byte   = unsigned char;
    using String = std::string;

    template<typename T>
    concept TTNObj = requires(const T& x) { x.toString(); };


    // Tuple decl
    template<typename ...Types>
    struct tuple;

    // Lambda decl
    template<typename>
    struct lambda;
    
}


#endif