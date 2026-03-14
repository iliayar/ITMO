
// Generated at 2026-03-15 23:13:16.331085 
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
vint tree;
 
int update(int i, int v, int x, int lx, int rx) {
    if(lx > i || rx <= i) {
        return tree[x];
    }
    if(rx - lx == 1) {
        tree[x] = v;
        return v;
    }
    int m = (lx + rx)/2;
    tree[x] = max(update(i, v, x*2 + 1, lx, m), update(i, v, x*2 + 2, m, rx));
    return tree[x];
}
 
int get(int l, int mi, int x, int lx, int rx) {
    // DBG() << "max " << l << " " << mi << " " << x << " " << lx << " " << rx << " | " << tree[x] << endl;
    if (tree[x] < mi) return -1;
    if (lx + 1 == rx) {
        return lx + 1;
    }
    int m = (lx+rx)/2;
    int res = -1;
    if (l < m && tree[x*2 + 1] >= mi) {
        res = get(l, mi, x*2 + 1, lx, m);
    }
    if (res == -1) {
        res = get(max(l, m), mi, x*2 + 2, m, rx);
    }
    return res;
}

//entry
void sol() {
    int n, m; cin >> n >> m;
    tree.resize(4*n, 0);
    for (int i = 0; i < n; ++i) {
        int x; cin >> x;
        update(i, x, 0, 0, n);
    }

    for (int i = 0; i < m; ++i) {
        int cmd; cin >> cmd;
        if (cmd == 0) {
            int j, x; cin >> j >> x; j--;
            update(j, x, 0, 0, n);
        } else if (cmd == 1) {
            int j, x; cin >> j >> x; j--;
            cout << get(j, x, 0, 0, n) << endl;
        }
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
