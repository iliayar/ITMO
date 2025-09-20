
// Generated at 2025-07-12 17:34:10.331420 
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

//##################CODE BEGIN#############
vint s;
int get(int v) {
    return v == s[v] ? v : (s[v] = get(s[v]));
}
void join(int a, int b) {
    s[get(a)] = b;
}
void init(int n) {
    s.resize(n, 0);
    for (int i = 0; i < n; ++i) s[i] = i;
}



vint bad;
vint2 g;
vint ps;
void build(int v, int p) {
    for (int u : g[v]) {
        if (bad[u]) {
            build(u, u);
        } else {
            join(u, p);
            build(u, p);
        }
    }
}

struct Q {
    char t; int v;
};

//entry
void sol() {
    int t; cin >> t;
    for (int ti = 0; ti < t; ++ti) {
        int n, q; cin >> n >> q;

        g.clear(); g.resize(n, vint{});
        ps.clear(); ps.resize(n, 0);
        s.clear(); init(n);
        bad.clear(); bad.resize(n, 0);

        for (int i = 0; i < n - 1; ++i) {
            int p; cin >> p; p--;
            g[p].push_back(i + 1);
            ps[i + 1] = p;
        }
        
        vector<Q> qs;
        for (int i = 0; i < q; ++i) {
            char t; int v; cin >> t >> v; v--;
            if (t == '-') {
                bad[v] = true;
            }
            qs.push_back({t, v}); 
        }

        build(0, 0);

        vint res;
        for (int i = qs.size() - 1; i >= 0; --i) {
            int vi = get(qs[i].v);
            if (qs[i].t == '?') {
                res.push_back(bad[vi] ? vi + 1 : -1);
            } else {
                int pi = get(ps[qs[i].v]);
                if (vi != pi) {
                    join(vi, pi);
                }
                bad[vi] = false;
            }
        }

        for (int i = res.size() - 1; i >= 0; --i) {
            cout << res[i] << " ";
        }
        cout << endl;
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
    #endif

    sol();

    #ifdef LOCAL
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    cout << duration.count() << " microseconds" << endl;
    #endif
}
