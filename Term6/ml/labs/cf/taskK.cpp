
// Generated at 2022-04-30 00:34:14.354170 
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

template <typename T, typename K>
ostream &operator<<(ostream &out, pair<T, K> p) {
  out << "(" << p.first << ", " << p.second << ")";
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
struct Obj {
    int x1, x2;
    int rx1, rx2;
};

// entry
void sol() {
    cout.precision(17);

    int n; cin >> n;
    if (n == 1) {
        cout << 0 << endl;
        return;
    }

    vector<Obj> xs;
    double vx1 = 0, vx2 = 0;
    for (int i = 0; i < n; ++i) {
        int x1, x2; cin >> x1 >> x2;
        xs.push_back({x1, x2, 0, 0});
        vx1 += x1;
        vx2 += x2;
    }

    int cr = -1;
    optional<int> prev = {};

    sort(ALL(xs), [](Obj l, Obj r) { return l.x1 < r.x1; });
    for (auto& o : xs) {
        if (!prev || prev.value() != o.x1) {
            cr++;
        }
        o.rx1 = cr;
        prev = o.x1;
    }

    cr = -1;
    prev = {};

    sort(ALL(xs), [](Obj l, Obj r) { return l.x2 < r.x2; });
    for (auto& o : xs) {
        if (!prev || prev.value() != o.x2) {
            cr++;
        }
        o.rx2 = cr;
        prev = o.x2;
    }

    double s = 0;
    for (auto [x1, x2, rx1, rx2] : xs) {
        s += (rx1 - rx2) * (rx1 - rx2);
    }
    double r = 1 - 6 * s / ((n - 1.) * n * (n + 1.));
    cout << r << endl;
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
