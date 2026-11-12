#include <iostream>

struct Vec2 {
    int x, y;
    int dot(Vec2) { return x * x + y * y; }
};
struct Vec3 {
    int z;
    Vec2 inner;
    operator Vec2() { return inner; }
    int dot(Vec3 v) { return inner.x * v.inner.x + inner.y * v.inner.y + z * v.z; }
};
struct Vec4 {
    int w;
    Vec3 inner;
    operator Vec3() { return inner; }
    int dot(Vec4 v) { return inner.inner.x * v.inner.inner.x + inner.inner.y * v.inner.inner.y + inner.z * v.inner.z + w * v.w; }
};
