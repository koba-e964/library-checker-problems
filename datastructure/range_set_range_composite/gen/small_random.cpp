#include "random.h"
#include <iostream>
#include <tuple>
#include "../params.h"

using namespace std;

int main(int, char* argv[]) {
    long long seed = atoll(argv[1]);
    auto gen = Random(seed);

    int n = gen.uniform<int>(1, 2000);
    int q = gen.uniform<int>(1, 2000);
    printf("%d %d\n", n, q);
    for (int i = 0; i < n; i++) {
        int a = gen.uniform<int>(1, MOD - 1);
        int b = gen.uniform<int>(0, MOD - 1);
        printf("%d %d\n", a, b);
    }
    for (int i = 0; i < q; i++) {
        int t = gen.uniform(0, 1);
        printf("%d ", t);
        if (t == 0) {
            int l, r;
            tie(l, r) = gen.uniform_pair(0, n);
            int c = gen.uniform<int>(1, MOD - 1);
            int d = gen.uniform<int>(0, MOD - 1);
            printf("%d %d %d %d\n", l, r, c, d);
        } else {
            int l, r;
            tie(l, r) = gen.uniform_pair(0, n);
            int x = gen.uniform<int>(0, MOD - 1);
            printf("%d %d %d\n", l, r, x);
        }
    }
    return 0;
}
