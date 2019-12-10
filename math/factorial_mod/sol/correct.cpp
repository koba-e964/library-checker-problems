#include <cassert>
#include <iostream>
#include <vector>

using namespace std;
using uint = unsigned int;
using ll = long long;
using ull = unsigned long long;

/*
 * Uses techniques described in Uses techniques described in
 * https://min-25.hatenablog.com/entry/2017/04/10/215046.
 * Mainly copy-and-paste of https://yukicoder.me/submissions/347989.
 */

// Constants used by NTT-based convolution.
// 3 NTT-friendly primes suffice.
const ll P1 = 1012924417;
const ll P2 = 1224736769;
const ll P3 = 1007681537;
const ll G1 = 5;
const ll G2 = 3;
const ll G3 = 3;

/*
 * Dependencies: typedef long long ll
 * Headers: iostream
 * Verified by: ARC099-F
 *              https://beta.atcoder.jp/contests/arc099/submissions/2743855
 */

template<ll mod = (ll)1e9 + 7>
struct ModInt {
  ll x;
  ModInt(void): x(0) {}
  ModInt(ll x): x(x % mod){}
  ModInt(const ModInt &x): x(x.x) {}
  ModInt operator+(ModInt o) const {
    ll y = x + o.x;
    if (y >= mod) y -= mod;
    return ModInt(y);
  }
  ModInt operator-(ModInt o) const {
    ll y = x - o.x + mod;
    if (y >= mod) y -= mod;
    return ModInt(y);
  }
  ModInt operator*(ModInt o) const {
    return ModInt((x * o.x) % mod);
  }
  void operator+=(ModInt o) { *this = *this + o; }
  void operator-=(ModInt o) { *this = *this - o; }
  void operator*=(ModInt o) { *this = *this * o; }
  ModInt operator-(void) const { return ModInt() - *this; }
  ll to_ll() const {
    return x;
  }
  bool operator<(ModInt o) const {
    return x < o.x;
  }
  ModInt pow(ll e) {
    assert (e >= 0);
    ModInt sum = 1;
    ModInt cur = *this;
    while (e > 0) {
      if (e % 2) {
        sum = sum * cur;
      }
      cur = cur * cur;
      e /= 2;
    }
    return sum;
  }
  ModInt inv(void) {
    return pow(mod - 2);
  }
};

template<ll mod>
ostream &operator<<(ostream &os, ModInt<mod> mi) {
  return os << mi.x;
}

template<ll mod>
void fft(vector<ModInt<mod>> &f, ModInt<mod> zeta) {
  int n = f.size();
  assert (n > 0 && (n & -n) == n);
  // swap
  {
    int i = 0;
    for (int j = 1; j < n - 1; j++) {
      int k = n >> 1;
      for (;;k >>= 1) {
        i ^= k;
        if (k <= i) break;
      }
      if (j < i) swap(f[i], f[j]);
    }
  }
  vector<ModInt<mod>> zetapow;
  {
    ModInt<mod> cur = zeta;
    for (int m = 1; m < n; m *= 2) {
      zetapow.push_back(cur);
      cur = cur * cur;
    }
  }
  for (int m = 1; m < n; m *= 2) {
    ModInt<mod> base = zetapow.back(); zetapow.pop_back();
    for (int r = 0; r < n; r += 2 * m) {
      ModInt<mod> w = 1;
      for (int s = r; s < r + m; s++) {
        ModInt<mod> u = f[s], d = f[s + m] * w;
        f[s] = u + d;
        f[s + m] = u - d;
        w *= base;
      }
    }
  }
}

void zmod(ll &x, ll mod) {
  x %= mod;
  if (x < 0) x += mod;
}

ll extgcd(ll a, ll b, ll &x, ll &y) {
  if (b == 0) {
    x = 1; y = 0;
    return a;
  }
  ll q = a / b;
  ll r = a - q * b;
  ll g = extgcd(b, r, y, x);
  y -= q * x;
  return g;
}

ll invmod(ll a, ll b) {
  ll x, y;
  extgcd(a, b, x, y);
  zmod(x, b);
  return x;
}

ll garner(vector<pair<ll, ll>> mr, ll mod) {
  mr.push_back(make_pair(mod, 0));
  vector<ll> coffs(mr.size(), 1), constants(mr.size(), 0);
  for (int i = 0; i < (int) mr.size() - 1; i++) {
    ll v = mr[i].second - constants[i];
    zmod(v, mr[i].first);
    v = v * invmod(coffs[i], mr[i].first) % mr[i].first;
    assert (v >= 0);
    for (int j = i + 1; j < (int) mr.size(); j++) {
      constants[j] += coffs[j] * v % mr[j].first;
      constants[j] %= mr[j].first;
      coffs[j] = coffs[j] * mr[i].first % mr[j].first;
    }
  }
  return constants[mr.size() - 1];
}

template<ll mod>
vector<ll> convolution_friendly(const vector<ll> &a, const vector<ll> &b,
                                ll gen) {
  int d = a.size();
  vector<ModInt<mod>> f(d), g(d);
  for (int i = 0; i < d; i++) {
    f[i] = a[i];
    g[i] = b[i];
  }
  ModInt<mod> zeta = ModInt<mod>(gen).pow((mod - 1) / d);
  fft(f, zeta);
  fft(g, zeta);
  for (int i = 0; i < d; i++) f[i] = g[i];
  fft(f, zeta.inv());
  ModInt<mod> inv = ModInt<mod>(d).inv();
  vector<ll> ans(d, 0);
  for (int i = 0; i < d; i++) ans[i] = (f[i] * inv).x;
  return ans;
}

vector<ll> arbmod_convolution(vector<ll> &a, vector<ll> &b, ll mod) {
  int d = a.size();
  assert (d > 0 && (d & -d) == d);
  assert (d == (int) b.size());
  for (int i = 0; i < d; i++) zmod(a[i], mod);
  for (int i = 0; i < d; i++) zmod(b[i], mod);

  vector<ll> x = convolution_friendly<P1>(a, b, G1);
  vector<ll> y = convolution_friendly<P2>(a, b, G2);
  vector<ll> z = convolution_friendly<P3>(a, b, G3);

  vector<ll> ret(d);
  vector<pair<ll, ll>> mr(3);
  for (int i = 0; i < d; i++) {
    mr[0] = make_pair(P1, x[i]);
    mr[1] = make_pair(P2, y[i]);
    mr[2] = make_pair(P3, z[i]);
    ret[i] = garner(mr, mod);
  }
  return ret;
}


ll mod;

ll powmod(ll a, ll e) {
  ll p = 1;
  ll c = a % mod;
  while (e > 0) {
    if (e % 2 == 1) {
      p = p * c % mod;
    }
    c = c * c % mod;
    e /= 2;
  }
  return p;
}

// f *= g, g is not destroyed
void convolution(vector<ll> &f, vector<ll> &g) {
  vector<ll> ans = arbmod_convolution(f, g, mod);
  for (int i = 0; i < (int) f.size(); i++) f[i] = ans[i];
}

struct mint {
  ll x;
  mint(): x(0) {}
  mint(ll x): x(x%mod) {}
  mint(ll x, int _bypass): x(x) {}
  mint operator *(mint a) const {
    return mint(x * a.x);
  }
  mint operator +(mint a) const {
    ll y = x + a.x;
    return mint(y >= mod ? y - mod : y, 0);
  }
  mint operator -(mint a) const {
    ll y = x - a.x;
    return mint(y < 0 ? y + mod : y, 0);
  }
  mint inv() const {
    return mint(powmod(x, mod - 2), 0);
  }
};

vector<ll> grow(ll d, ll v, vector<ll> h,
                const vector<mint> &invfac) {
  assert ((ll) h.size() == d + 1);

  vector<ll> aux(d, 1);

  vector<ll> f(4 * d, 0), g(4 * d, 0);
  for (ll i = 0; i <= d; i++) {
    f[i] = (invfac[i] * invfac[d - i] * h[i]).x;
    if ((d + i) % 2 != 0) {
      f[i] = f[i] == 0 ? 0 : mod - f[i];
    }
  }
  vector<ll> oldf(f);
  mint nums[3] = {mint(d + 1), mint(d) * mint(v).inv(), mint(d) * mint(v) + d + 1};
  for (int idx = 0; idx < 3; idx++) {
    mint a = nums[idx];
    for (int i = 0; i < 4 * d; i++) f[i] = oldf[i], g[i] = 0;
    for (int i = 1; i < 2 * d + 2; i++)
      g[i] = (a - d + i - 1).inv().x;
    convolution(f, g);
    ll prod = 1;
    for (int i = 0; i <= d; i++) {
      prod = prod * (a - i).x % mod;
      assert (prod != 0);
    }
    for (int i = 0; i <= d; i++) {
      f[d + i + 1] = f[d + i + 1] * prod % mod;
      prod = prod * (a + i + 1).x % mod;
      prod = prod * (a - d + i).inv().x % mod;
    }
    if (idx == 1) {
      for (int i = 0; i <= d; i++) {
        h[i] = h[i] * f[d + 1 + i] % mod;
      }
    } else if (idx == 0) {
      for (int i = 0; i < d; i++) {
        aux[i] = f[d + 1 + i];
      }
    } else if (idx == 2) {
      for (int i = 0; i < d; i++ ){
        aux[i] = aux[i] * f[d + 1 + i] % mod;
      }
    } else {
      assert (0);
    }
  }
  for (int i = 0; i < d; i++) h.push_back(aux[i]);
  return h;  
}

vector<ll> gen_seq(ll d, ll v) {
  // d must be a power of two.
  assert (d > 0 && (d & -d) == d);

  // precompute factorial ans its inv
  vector<mint> fac(2 * d + 1, mint(0));
  vector<mint> invfac(2 * d + 1, mint(0));
  fac[0] = 1;
  for (ll i = 1; i <= 2 * d; i++) {
    fac[i] = fac[i - 1] * i;
  }
  invfac[2 * d] = fac[2 * d].inv();
  for (ll i = 2 * d - 1; i >= 0; i--) {
    invfac[i] = invfac[i + 1] * (i + 1);
  }
  ll size = 1;
  vector<ll> seq(2);
  seq[0] = 1;
  seq[1] = v + 1;
  while (size < d) {
    seq = grow(size, v, seq, invfac);
    size *= 2;
  }
  assert (size == d);
  return seq;
}

ll fact_mod(ll n, ll mod) {
  ll d = 1 << 15;
  vector<ll> aux = gen_seq(d, d);
  ll ans = 1;
  ll lim = min(d, (n + 1) / d);
  for (ll i = 0; i < lim; i++) {
    ans = ans * aux[i] % mod;
  }
  for (ll i = lim * d; i < n; i++) {
    ans = ans * (i + 1) % mod;
  }
  return ans;
}

int main() {
    cin.tie(nullptr);
    ios::sync_with_stdio(false);

    ll n;
    cin >> n >> mod;

    if (n >= mod) {
      cout << "0\n";
      return 0;
    }

    cout << fact_mod(n, mod) << "\n";

    return 0;
}
