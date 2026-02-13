
// Generated at 2026-02-18 00:26:04.272678 
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
    DBG() << reachable << endl;

    vector<double> d(n, -numeric_limits<double>::infinity());
    for (int i = 0; i < n; ++i) {
        for (auto& r : g[i]) {
            if (r.right.empty()) {
                if (r.diff > d[i]) {
                    d[i] = r.diff;
                }
            }
        }
    }
    double ns = 1.;
    double nn = ns;
    for (int i = 0; i < n; ++i, nn *= ns) {
        vector<double> dt(n, -numeric_limits<double>::infinity());
        for (int l = 0; l < n; ++l) {
            if (!finite[l]) continue;
            dt[l] = max(dt[l], d[l] / ns);
            for (auto& r : g[l]) {
                bool f = false;
                double dc = r.diff / nn;
                for (auto& nt : r.right) {
                    if (!finite[nt] || d[nt] == -numeric_limits<double>::infinity()) {
                        f = true;
                        break;
                    }
                    dc += d[nt] / ns;
                }
                if (f) continue;
                if (dt[l] < dc) {
                    dt[l] = dc;
                }
            }
        }
        swap(dt, d);
    }
    nn /= ns;

    for (int l = 0; l < n; ++l) {
        if (!finite[l] || !reachable[l]) continue;
        for (auto& r : g[l]) {
            bool f = false;
            double dc = r.diff / nn;
            for (auto& nt : r.right) {
                if (!finite[nt] || d[nt] == -numeric_limits<double>::infinity()) {
                    f = true;
                    break;
                }
                dc += d[nt];
            }
            if (f) continue;
            if (d[l] < dc) {
                d[l] = numeric_limits<double>::infinity();
            }
        }
    }

    for (int i = 0; i < n; ++i, nn *= ns) {
        vector<double> dt(n, -numeric_limits<double>::infinity());
        for (int l = 0; l < n; ++l) {
            if (!finite[l]) continue;
            dt[l] = max(dt[l], d[l] / ns);
            for (auto& r : g[l]) {
                bool f = false;
                double dc = r.diff / nn;
                for (auto& nt : r.right) {
                    if (!finite[nt] || d[nt] == -numeric_limits<double>::infinity()) {
                        f = true;
                        break;
                    }
                    dc += d[nt] / ns;
                }
                if (f) continue;
                if (dt[l] < dc) {
                    dt[l] = dc;
                }
            }
        }
        swap(dt, d);
    }
    DBG() << d << endl;

    if (d[0] > 0) {
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
