#include "titan.h"

using namespace ttn;

int main() {
    lambda<void()> lambda;
    {
        int x = 0;
        lambda = [&]<typename T, T x>(){
            trace(x);
            x = 50;
            trace(x);
        };
    } // lambda outlives x... someone needs to do something about this
    lambda();
}