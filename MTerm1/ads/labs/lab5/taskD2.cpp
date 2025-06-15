
// Generated at 2025-06-14 22:26:34.216809 
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
template <typename I, typename Comparator>
auto kth(I begin, I end, int k, const Comparator& cmp) {
    int len = end - begin + 1;
    DBG() << "kth " << vector(begin, end + 1) << " " << len << " " << k << endl;
    if (len < 1) exit(1);
    if (len == 1) {
        if (k != 0) exit(1);
        return *begin;
    }
    auto pivot = *(begin + len / 2);
    auto l = begin;
    auto r = end;
    while (l <= r) {
        while (cmp(*l, pivot)) l++;
        while (cmp(pivot, *r)) r--;
        if (l <= r) {
            swap(*(l++), *(r--));
        }
    }
    int ll = r - begin + 1;
    int lm = l - r - 1;
    if (k < ll) {
        return kth(begin, r, k, cmp);
    }
    k -= ll;

    if (k < lm) {
        return *(r + 1);
    }
    k -= lm;

    return kth(l, end, k, cmp);
}

template <typename F> double bs(double l, double r, double delta, F pred) {
  while (r - l > delta) {
    double m = (l + r) / 2.;
    if (pred(m)) {
      l = m;
    } else {
      r = m;
    }
  }
  return (r - l) / 2.;
}
 
struct S {
    int i;
    int v;
    int w;
};

ostream& operator<<(ostream& out, const S& s) {
    out << "S {" << "i = " << s.i << ", v = " << s.v << ", w = " << s.w << "}";
    return out;
}
 
//entry
void sol() {
    int n, k; cin >> n >> k;
    vector<S> a;
    for (int i = 0; i < n; ++i) {
        a.push_back({i+1}); cin >> a.back().v >> a.back().w;
    }
 
    auto calc = [&](const S& s, double x) { return s.v - s.w*x; };
    bs(0, 1e+7, 1e-7, [&](double x) {
        kth(a.begin(), a.end() - 1, k - 1, [&](auto& l, auto& r) {
            return calc(l, x) > calc(r, x);
        });
        double s = 0;
        for (int i = 0; i < k; ++i) {
            s += calc(a[i], x);
        }
        return s > 0;
    });
 
    sort(a.begin(), a.begin() + k, [&](auto& lhs, auto& rhs) {
        return lhs.i < rhs.i;
    });
    for (int i = 0; i < k; ++i) {
        cout << a[i].i << " ";
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
    #endif

    sol();

    #ifdef LOCAL
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    cout << duration.count() << " microseconds" << endl;
    #endif
}
