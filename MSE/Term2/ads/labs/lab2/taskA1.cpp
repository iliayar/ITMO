
// Generated at 2026-02-20 21:33:17.123781 
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
struct E {
    int min = INF;
    int max = -INF;
};

ostream& operator<<(ostream& out, E const& e) {
    cout << "{" << e.min << ", " << e.max << "}";
    return out;
}

E mconcat(E const& lhs, E const& rhs) {
    return E{.min = min(lhs.min, rhs.min), .max = max(lhs.max, rhs.max)};
}

E msingleton(int x) {
    return E{.min = x, .max = x};
}

E mzero() {
    return E{};
}

vector<E> tree;
 
E st_update(int i, int v, int x, int lx, int rx) {
    if(lx > i || rx <= i) {
        return tree[x];
    }
    if(rx - lx == 1) {
        tree[x] = msingleton(v);
        return tree[x];
    }
    int m = (lx + rx)/2;
    tree[x] = mconcat(st_update(i, v, x*2 + 1, lx, m), st_update(i, v, x*2 + 2, m, rx));
    return tree[x];
}
 
E st_get(int l, int r, int x, int lx, int rx) {
    // DBG() << "st_get [" << l << "; " << r << ") " << x << " [" << lx << "; " << rx << ")" << endl;
    if(r <= l) {
        return mzero();
    }
    if(l == lx && r == rx) {
        return tree[x];
    }
    int m = (lx+rx)/2;
    return mconcat(st_get(l,min(m,r),x*2 + 1, lx, m), st_get(max(l,m),r,x*2+2,m,rx));
 
}
 
//entry
void sol() {
    int N = 100000;
    tree.resize(N * 4, E{});
    for (int i = 1; i <= N; ++i) {
        int v = ((i * i) % 12345) + ((i * i * i) % 23456);
        st_update(i - 1, v, 0, 0, N);
    }
    // DBG() << tree << endl;
    int k; cin >> k;
    for (int i = 0; i < k; ++i) {
        int x, y; cin >> x >> y;
        if (x > 0) {
            auto e = st_get(x - 1, y, 0, 0, N);
            // DBG() << e.max << " " << e.min << endl;
            cout << e.max - e.min << endl;
        } else {
            x = -x;
            st_update(x - 1, y, 0, 0, N);
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
