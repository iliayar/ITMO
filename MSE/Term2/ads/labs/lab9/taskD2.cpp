
// Generated at 2026-04-14 17:39:31.937290 
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
constexpr int BASE10 = 3;

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
    DBG() << "d = " << d << endl;
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

//entry
int get_poly_size(int n1, int n2) {
    // return max((1 << (log2(n1) + 1)), (1 << (log2(n2) + 1)));
    return 1 << (log2(n1 + n2 + 1) + 1);
}

//entry
void sol() {
    string n1, n2; cin >> n1 >> n2;

    vint p1;
    for (int i = n1.length() - 1; i >= 0; i -= BASE10) {
        p1.push_back(0);
        for (int j = max(i - BASE10 + 1, 0ll); j <= i; ++j) {
            p1.back() = p1.back() * 10 + n1[j] - '0';
        }
    }

    vint p2;
    for (int i = n2.length() - 1; i >= 0; i -= BASE10) {
        p2.push_back(0);
        for (int j = max(i - BASE10 + 1, 0ll); j <= i; ++j) {
            p2.back() = p2.back() * 10 + n2[j] - '0';
        }
    }

    DBG() << p1 << ", " << p2 << endl;

    int N = get_poly_size(p1.size(), p2.size());
    p1.resize(N);
    p2.resize(N);

    auto res = fourier(p1, p2);
    DBG() << res << endl;

    int mo = pow(10, BASE10);
    for (int i = 0; i < res.size() - 1; ++i) {
        res[i + 1] += res[i] / mo;
        res[i] %= mo;

        if (res[i + 1] >= mo && res.size() == i + 2) {
            res.push_back(0);
        }
    }
    DBG() << res << endl;

    bool first = true;
    bool is_zero = true;
    for (int i = res.size() - 1; i >= 0; --i) {
        if (first && res[i] == 0) continue;
        if (first) {
            cout << res[i];
            is_zero = false;
            first = false;
            continue;
        }
        cout << setw(BASE10) << setfill('0') << res[i];
        is_zero = false;
    }
    if (is_zero) cout << "0";
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
