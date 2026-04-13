
// Generated at 2026-04-14 18:55:14.020676 
// By iliayar
#define _USE_MATH_DEFINES
#pragma comment(linker, "/STACK:36777216")
#include <iterator>
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <cmath>
#include <cstdio>
#include <map>
#include <unordered_set>
#include <ctime>
#include <cstdlib>
#include <queue>
#include <set>
#include <deque>
#include <list>
#include <sstream>
#include <numeric>
#include <optional>
#include <variant>
#include <functional>
#include <bitset>
#include <memory>
#include <cassert>

using namespace std;

#define ON 1
#define OFF 0

#define int long long
#ifdef LOCAL
#define DBG_VAR true
#define DBG_CODE(x) x
#else
#define DBG_VAR false
#define DBG_CODE(x)
#endif

#define DBG() if (DBG_VAR) cout << "DBG: "

#define INF 1e+18
#define ALL(a) a.begin(), a.end()

#define FUNC(retTy, name, args...) std::function<retTy (args)> name = [&](args) -> retTy

using vint = vector<int>;
using vint2 = vector<vint>;

template <typename K, typename V>
struct map_pair {
    K k;
    V v;
};

template <typename T, typename K>
ostream &operator<<(ostream &out, pair<T, K> const& p) {
  out << "(" << p.first << ", " << p.second << ")";
  return out;
}

template<typename T>
class Join {
  T& v;
  string const& separator;
  
public:
  
  Join(T v, string const& separator)
    : v(v), separator(separator)
  {}

  friend ostream& operator<<(ostream& out, Join<T> join) {
    for(auto it = join.v.cbegin(); it != join.v.cend(); ++it) {
      if(it != join.v.cbegin()) out << join.separator;
      out << *it;
    }
    return out;
  }
};

template <typename T>
ostream &operator<<(ostream &out, vector<T> v) {
  out << "[" << Join(v, ", ") << "]";
  return out;
}

template <typename K, typename V>
ostream &operator<<(ostream &out, map<K, V> m) {
  vector<map_pair<K, V>> v;
  transform(m.begin(), m.end(), back_inserter(v), [](pair<K, V> const& p){return map_pair<K, V>{p.first, p.second};});
  out << "{" << Join(v, ", ") << "}";
  return out;
}

template <typename K, typename V>
ostream &operator<<(ostream &out, unordered_map<K, V> m) {
  vector<map_pair<K, V>> v;
  transform(m.begin(), m.end(), back_inserter(v), [](pair<K, V> const& p){return map_pair<K, V>{p.first, p.second};});
  out << "{" << Join(v, ", ") << "}";
  return out;
}

template <typename K, typename V>
ostream &operator<<(ostream &out, map_pair<K, V> m) {
  out << m.k << ": " << m.v;
  return out;
}

template <typename K>
ostream &operator<<(ostream &out, set<K> s) {
  out << "{" << Join(s, ", ") << "}";
  return out;
}

std::function<void()> finish = [](){ exit(0); };

//##################CODE BEGIN#############
struct complex {
    double re, im;

    static complex from(double x) {
        return complex{x, 0};
    }

    complex operator+(complex const& rhs) {
        return complex{re + rhs.re, im + rhs.im};
    }

    complex operator*(complex const& rhs) {
        return complex{re * rhs.re - im * rhs.im, re * rhs.im + im * rhs.re};
    }

    static complex from_exp(double x) {
        return {cos(x), sin(x)};
    }

    complex pow(size_t k) {
        auto b = complex::from(1);
        if (k == 0) {
            return b;
        }
        auto n = *this;
        while (k > 1) {
            if (k % 2 == 0) {
                n = n * n;
                k /= 2;
            } else {
                b = b * n;
                k -= 1;
            }
        }
        return b * n;
    }

    friend ostream& operator<<(ostream& out, complex const& c) {
        out << "{" << c.re << ", " << c.im << "}";
        return out;
    }
};

vector<complex> fft(vector<complex> const& p, bool inv) {
    auto n = p.size();
    auto w = complex::from_exp((inv ? -1 : 1) * 2 * M_PI / n);
    if (n == 1) {
        return {p[0]};
    }

    vector<complex> p0, p1;
    p0.reserve(n / 2);
    p1.reserve(n / 2);

    for (int i = 0; i < n; i += 2) {
        p0.push_back(p[i]);
    }
    for (int i = 1; i < n; i += 2) {
        p1.push_back(p[i]);
    }
    auto f = fft(p0, inv);
    auto g = fft(p1, inv);

    vector<complex> a;
    a.reserve(n);
    auto x = complex::from(1);
    for (int i = 0; i < n; ++i) {
        a.push_back(f[i % (n / 2)] + x * g[i % (n / 2)]);
        x = x * w;
    }
    return a;
}

vint fourier(vint const& pi, vint const& qi) {
    auto n = pi.size();
    assert(n == qi.size());
    vector<complex> p(n);
    vector<complex> q(n);
    for (int i = 0; i < n; ++i) {
        p[i] = complex::from(pi[i]);
        q[i] = complex::from(qi[i]);
    }

    auto a = fft(p, false);
    auto b = fft(q, false);

    vector<complex> c(n);
    for (int i = 0; i < n; ++i) {
        c[i] = a[i] * b[i];
    }

    auto d = fft(c, true);
    // DBG() << "d = " << d << endl;
    vint res(n);
    for (int i = 0; i < n; ++i) {
        res[i] = std::round(d[i].re / n);
    }
    return res;
}

int log2(int n) {
    int i = 0;
    while (n > 0) {
        n /= 2;
        i++;
    }
    return i - 1;
}

constexpr int N = 256000 + 1;

//entry
void sol() {
    int n, S; cin >> n >> S;
    vint p(1 << 18);
    vint mm(N);
    for (int i = 0; i < n; ++i) {
        int x; cin >> x;
        p[x]++;
        mm[x] = i;
    }

    vint pp = fourier(p, p);

    int j = -1;
    for (int i = 0; i <= S; ++i) {
        if (pp[i] > 0 && pp[S - i] > 0) {
            j = i;
            break;
        }
    }
    if (j == -1) {
        cout << 0 << endl;
        return;
    }

    vint res;
    for (int i = 0; i <= j; ++i) {
        if (p[i] > 0 && p[j - i] > 0) {
            res.push_back(mm[i]);
            res.push_back(mm[j - i]);
            break;
        }
    }

    for (int i = 0; i <= S - j; ++i) {
        if (p[i] > 0 && p[S - j - i] > 0) {
            res.push_back(mm[i]);
            res.push_back(mm[S - j - i]);
            break;
        }
    }

    for (int i = 0; i < res.size(); ++i) {
        cout << res[i] + 1 << " ";
    }
    cout << endl;
}
//##################CODE END###############
#ifdef LOCAL
#undef FILE_IO
#undef FILENAME
#define FILE_IO ON
#define FILENAME "local"
#endif

signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0); cout.tie(0);
    #if FILE_IO == ON
    freopen(FILENAME".in", "r", stdin);
    freopen(FILENAME".out", "w", stdout);
    #endif
    #ifdef LOCAL
    auto start = std::chrono::high_resolution_clock::now();
    finish = [&]() {
        auto stop = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
        cout << duration.count() << " microseconds" << endl;
        exit(0);
    };
    #endif

    sol();
    finish();
}
