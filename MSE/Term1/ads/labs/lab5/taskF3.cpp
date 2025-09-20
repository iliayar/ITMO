
// Generated at 2025-06-15 15:51:18.322965 
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
template <typename F> std::pair<int, int> bs(int l, int r, F pred) {
  while (r - l > 1) {
    int m = (l + r) / 2;
    if (pred(m)) {
      l = m;
    } else {
      r = m;
    }
  }

  if (!pred(l)) {
    l--;
    r--;
  }

  return {l, r};
}

struct P {
    int x;
    int y;
};

bool operator<(const P& lhs, const P& rhs) {
    if (lhs.x == rhs.x) {
        return lhs.y < rhs.y;
    }
    return lhs.x < rhs.x;
}

bool operator==(const P& lhs, const P& rhs) {
    return lhs.x == rhs.x && lhs.y == rhs.y;
}

ostream& operator<<(ostream& out, const P& p) {
    out << "P {x = " << p.x << ", y = " << p.y << "}";
    return out;
}

int dq(const P& lhs, const P& rhs) {
    return pow(rhs.x - lhs.x, 2) + pow(rhs.y - lhs.y, 2);
}

//entry
void sol() {
    int n; cin >> n;
    optional<P> p0, p1;
    vector<P> a(n);
    for (int i = 0; i < n; ++i) {
        cin >> a[i].x >> a[i].y;
        if (!p0) {
            p0 = a[i];
        } else if (*p0 != a[i] && !p1) {
            p1 = a[i];
        }
    }
    int q; cin >> q;
    vector<P> qs(q);
    for (int i = 0; i < q; ++i) {
        cin >> qs[i].x >> qs[i].y;
    }

    if (!p0 || !p1) {
        for (int i = 0; i < q; ++i) {
            cout << a[0].x << " " << a[0].y << endl;
        }
        return;
    }

    P v{p0->x - p1->x, p0->y - p1->y};
    int c = v.x * p0->y - v.y * p0->x;

    P vp;
    if (v.x != 0) {
        vp = P{v.y, -v.x};
    } else {
        if (v.y == 0) return;
        vp = P{-v.y, v.x};
    }

    DBG() << v << " " << vp << endl;

    sort(ALL(a), [&](const P& lhs, const P& rhs) {
        int ld = dq(lhs, P{0, 0}) * (lhs.x * v.x + lhs.y * v.y < 0 ? -1 : 1);
        int rd = dq(rhs, P{0, 0}) * (rhs.x * v.x + rhs.y * v.y < 0 ? -1 : 1);
        return ld < rd;
    });
    DBG() << a << endl;

    for (auto qi : qs) {
        int cp = - vp.y * qi.x + vp.x * qi.y;
        DBG() << "cp = " << cp << endl;

        double x0 = (1. * cp * v.x - c * vp.x) / (1. * v.y * vp.x - vp.y * v.x);
        double y0;
        if (v.x != 0) {
            y0 = (v.y * x0 + c) / (1. * v.x);
        } else {
            y0 = (vp.y * x0 + cp) / (1. * vp.x);
        }

        DBG() "x0 = " << x0 << ", y0 = " << y0 << endl;

        auto [l, r] = bs(0, a.size(), [&](int i) {
            double vdx = a[i].x - x0;
            double vdy = a[i].y - y0;
            double k = vdx * v.x + vdy * v.y;
            return k < 0.;
        });
        DBG() "Found: " << l << " " << r << endl;

        int i = -1;

        if (l < 0) {
            i = r;
        } else if (r >= a.size()) {
            i = l;
        } else if (dq(a[l], qi) < dq(a[r], qi)) {
            i = l;
        } else if (dq(a[l], qi) > dq(a[r], qi)) {
            i = r;
        } else if (a[l] < a[r]) {
            i = l;
        } else {
            i = r;
        }
        if (i < 0 || i >= a.size()) exit(1);
        cout << a[i].x << " " << a[i].y << endl;
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
