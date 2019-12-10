#include "testlib.h"

bool is_prime(long long x) {
  for (long long i = 2; i * i <= x; i++) {
    if (x % i == 0) {
      return false;
    }
  }
  return true;
}

int main() {
    registerValidation();

    int max = (int)1e9 + 9;

    int n = inf.readInt(1, max); // n
    inf.readSpace();
    int p = inf.readInt(n, max); // p
    ensure(is_prime(p));
    inf.readEoln();
    inf.readEof();
    return 0;
}
