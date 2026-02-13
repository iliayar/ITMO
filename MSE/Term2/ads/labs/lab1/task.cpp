// Generated at 2026-02-18 22:02:07.574634 
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
struct R {
    vector<int> right;
    int diff;
};

struct llong;
ostream& operator<<(ostream& out, llong const& n);

struct llong {
    constexpr static long long SIZE = 128;
    constexpr static long long BYTE = 1 << 16;
    long long d[SIZE];
    bool neg;

    llong(int n) {
        // DBG() << "llong(" << n << ")" << endl;
        neg = false;
        if (n < 0) {
            neg = true;
            n = -n;
        }
        for (int i = 0; i < SIZE; ++i) {
            d[i] = 0;
        }
        int i = 0;
        while (n > 0) {
            d[i++] = n % BYTE; 
            n /= BYTE;
        }
    }

    llong add_mod(llong const& other) const {
        // DBG() << "add_mod" << endl;
        llong res = *this;
        res.neg = false;
        for (int i = 0; i < SIZE; ++i) {
            res.d[i] += other.d[i];
            while (res.d[i] >= BYTE) {
                if (i + 1 >= SIZE) {
                    DBG() << "Overflow while adding " << *this << " + " << other << endl;
                    exit(67);
                }
                res.d[i] -= BYTE;
                res.d[i + 1] += 1;
            }
        }
        return res;
    }

    llong sub_mod(llong const& other) const {
        // DBG() << "sub_mod" << endl;
        if (other.gt_mod(*this)) {
            auto res = other.sub_mod(*this);
            res.neg = !res.neg;
            return res;
        }
        llong res = *this;
        res.neg = false;
        for (int i = 0; i < SIZE; ++i) {
            res.d[i] -= other.d[i];
            while (res.d[i] < 0) {
                if (i + 1 >= SIZE) exit(67);
                res.d[i] += BYTE;
                res.d[i + 1] -= 1;
            }

        }
        return res;
    }

    bool gt_mod(llong const& other) const {
        for (int i = SIZE - 1; i >= 0; --i) {
            if (d[i] > other.d[i]) {
                return true;
            } else if (d[i] < other.d[i]) {
                return false;
            }
        }
        return false;
    }

    llong operator+(llong const& other) const {
        // DBG() << "operator+" << endl;
        if (neg && other.neg) {
            auto res = add_mod(other);
            res.neg = true;
            return res;
        } else if (neg && !other.neg) {
            return other.sub_mod(*this);
        } else if (!neg && other.neg) {
            return sub_mod(other);
        } else {
            return add_mod(other);
        }
    }

    llong& operator+=(llong const& other) {
        *this = *this + other;
        return *this;
    }

    llong operator-(llong const& other) const {
        if (neg && other.neg) {
            return other.sub_mod(*this);
        } else if (neg && !other.neg) {
            auto res = add_mod(other);
            res.neg = true;
            return res;
        } else if (!neg && other.neg) {
            return add_mod(other);
        } else {
            return sub_mod(other);
        }
    }

    llong operator-() const {
        llong res = *this;
        res.neg = !res.neg;
        return res;
    }

    bool operator<(llong const& other) const {
        if (neg && other.neg) {
            return gt_mod(other);
        } else if (neg && !other.neg) {
            return true;
        } else if (!neg && other.neg) {
            return false;
        } else {
            return other.gt_mod(*this);
        }
    }

    bool operator==(llong const& other) const {
        bool is_zero = true;
        for (int i = 0; i < SIZE; ++i) {
            if (d[i] != other.d[i]) {
                return false;
            }
            if (d[i] != 0) {
                is_zero = false;
            }
        }

        if (is_zero) return true;
        if (other.neg == neg) return true;
        return false;
    }

    static llong inf() {
        llong res(0);
        for (int i = 0; i < SIZE; ++i) {
            res.d[i] = BYTE - 1;
        }
        return res;
    }
};

ostream& operator<<(ostream& out, llong const& n) {
    if (n.neg) cout << "-";
    for (int i = llong::SIZE - 1; i >= 0; --i) {
        out << n.d[i];
        if (i != 0) {
            cout << ":";
        }
    }
    return out;
}

void sol_case(int n, int m) {
    vector<vector<R>> g(n, vector<R>());
    for (int i = 0; i < m; ++i) {
        int left, k; cin >> left >> k; left--;
        g[left].emplace_back(vector<int>{}, 0);
        for (int j = 0; j < k; ++j) {
            string s; cin >> s;
            if (isalpha(s[0])) {
                if (s[0] == 'a') {
                    g[left].back().diff++;
                } else {
                    g[left].back().diff--;
                }
            } else {
                g[left].back().right.push_back(stoull(s) - 1);
            }
        }
    }

    vector<bool> finite(n, false);
    bool run = true;
    while (run) {
        run = false;
        for (int i = 0; i < n; ++i) {
            if (finite[i]) continue;
            for (auto& r : g[i]) {
                bool has_nonfinite = false;
                for (auto& nt : r.right) {
                    if (!finite[nt]) {
                        has_nonfinite = true;
                        break;
                    }
                }
                if (!has_nonfinite) {
                    finite[i] = true;
                    run = true;
                    break;
                }
            }
        }
    }

    if (!finite[0]) {
        cout << "NO" << endl;
        return;
    }

    vector<bool> was(n, false);
    vector<bool> reachable(n, false);
    reachable[0] = true;
    was[0] = true;
    queue<int> q;
    q.push(0);
    while (!q.empty()) {
        int l = q.front(); q.pop();
        for (auto& r : g[l]) {
            bool has_nonfinite = false;
            for (auto nt : r.right) {
                if (!finite[nt]) {
                    has_nonfinite = true;
                    break;
                }
            }
            if (has_nonfinite) continue;
            for (auto nt : r.right) {
                if (!was[nt]) {
                    q.push(nt);
                    was[nt] = true;
                    reachable[nt] = true;
                }
            }
        }
    }
    // DBG() << reachable << endl;

    auto neginf = -llong::inf();
    vector<llong> d(n, neginf);
    for (int i = 0; i < n; ++i) {
        for (auto& r : g[i]) {
            if (r.right.empty()) {
                if (d[i] < llong(r.diff)) {
                    d[i] = r.diff;
                }
            }
        }
    }
    // DBG() << d << endl;
    for (int i = 0; i < n; ++i) {
        for (int l = 0; l < n; ++l) {
            if (!finite[l]) continue;
            for (auto& r : g[l]) {
                bool f = false;
                llong dc = r.diff;
                for (auto& nt : r.right) {
                    if (!finite[nt] || d[nt] == neginf) {
                        f = true;
                        break;
                    }
                    dc += d[nt];
                }
                if (f) continue;
                if (d[l] < dc) {
                    d[l] = dc;
                }
            }
        }
        // DBG() << d << endl;
    }

    for (int l = 0; l < n; ++l) {
        if (!finite[l] || !reachable[l]) continue;
        for (auto& r : g[l]) {
            bool f = false;
            llong dc = r.diff;
            for (auto& nt : r.right) {
                if (!finite[nt] || d[nt] == neginf) {
                    f = true;
                    break;
                }
                dc += d[nt];
            }
            if (f) continue;
            if (d[l] < dc) {
                cout << "YES" << endl;
                return;
            }
        }
    }
    // DBG() << d << endl;

    if (llong(0) < d[0]) {
        cout << "YES" << endl;
    } else {
        cout << "NO" << endl;
    }
}

//entry
void sol() {
    while (true) {
        int n, m; cin >> n >> m;
        if (n == 0 && m == 0) break;
        sol_case(n, m);
    }
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
