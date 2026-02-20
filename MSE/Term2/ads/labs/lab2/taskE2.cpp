
// Generated at 2026-02-21 01:32:32.126049 
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
int log2(int n) {
    int i = 0;
    while (n > 0) {
        n /= 2;
        i++;
    }
    return i - 1;
}

struct V {
    int v;
    int idx;
};

bool operator<(V const& lhs, V const& rhs) {
    return lhs.v < rhs.v;
}

//entry
void sol() {
    int n, m; cin >> n >> m;
    vint2 g(n, vint{});
    for (int i = 1; i < n; ++i) {
        int u; cin >> u;
        g[u].push_back(i);
    }

    vint euler;
    vint first(n, -1);
    vint depth(n, -1);

    FUNC(void, dfs1, int u) {
        first[u] = euler.size();
        euler.push_back(u);
        for (int v : g[u]) {
            depth[v] = depth[u] + 1;
            dfs1(v);
            euler.push_back(u);
        }
    };
    depth[0] = 0;
    dfs1(0);

    vint log(euler.size() + 1, -1);
    for (int i = 1; i <= euler.size(); ++i) {
        log[i] = log2(i);
    }

    vector<vector<V>> f(1 << (log[euler.size()] + 2), vector<V>(log[euler.size()] + 1, V(INF, -1)));
    for (int i = 0; i < euler.size(); ++i) {
        f[i][0].v = depth[euler[i]];
        f[i][0].idx = i;
    }
    for (int k = 0; k < log[euler.size()]; ++k) {
        for (int i = 0; i < euler.size(); ++i) {
            f[i][k + 1] = min(f[i][k], f[i + (1 << k)][k]);
        }
    }

    int a1, a2; cin >> a1 >> a2;
    int x, y, z; cin >> x >> y >> z;

    int ans = 0;
    int v = 0;
    for (int q = 1; q <= m; ++q) {
        int u = (a1 + v) % n;
        int w = a2;

        int l = first[u];
        int r = first[w];
        if (l > r) swap(l, r);
        int k = log[r - l];
        if (k == -1) {
            v = u;
        } else {
            auto res = min(f[l][k], f[r - (1 << k)][k]); 
            DBG() << u << " " << w << " " << r << " " << l << " " << k << " " << res.idx << endl;
            v = euler[res.idx];
        }
        ans += v;

        a1 = (x * a1 + y * a2 + z) % n;
        a2 = (x * a2 + y * a1 + z) % n;
    }

    cout << ans << endl;
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
