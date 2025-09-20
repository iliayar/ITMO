
// Generated at 2025-07-06 12:59:20.359568 
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
int ty(char c) {
    switch (c) {
        case ')':
        case '(':
            return 0;
        case '[':
        case ']':
            return 1;
        case '{':
        case '}':
            return 2;
    }
}

int ba(char c) {
    switch (c) {
        case '(':
        case '[':
        case '{':
            return 1;
        case ')':
        case ']':
        case '}':
            return -1;
    }
}

vint2 dp;
vint2 d;
string s;

void restore(int l, int r) {
    if (dp[l][r] == r - l + 1) {
        return;
    }
    if (dp[l][r] == 0) {
        cout << s.substr(l, r - l + 1);
        return;
    }
    if (d[l][r] == -1) {
        cout << s[l];
        restore(l + 1, r - 1);
        cout << s[r];
        return;
    }
    restore(l, d[l][r]);
    restore(d[l][r] + 1, r);
}

//entry
void sol() {
     cin >> s;
     int n = s.length();
     dp.resize(n + 1, vint(n + 1, INF));
     d.resize(n + 1, vint(n + 1, -1));

     for (int i = 0; i < n; ++i) {
         for (int j = 0; j < n; ++j) {
             if (i == j) {
                 dp[j][i] = 1;
             } else if (i < j) {
                 dp[j][i] = 0;
             }
         }
     }

     for (int i = 1; i <= n; ++i) {
         for (int j = 0; j <= n - i; ++j) {
             int l = j, r = i + j - 1;
             if ((ty(s[l]) == ty(s[r])) && (ba(s[l]) == 1) && (ba(s[r]) == -1)) {
                 dp[l][r] = min(dp[l][r], dp[l + 1][r - 1]);
             }

             for (int k = l; k < r; ++k) {
                 if (dp[l][r] > dp[l][k] + dp[k + 1][r]) {
                     dp[l][r] = dp[l][k] + dp[k + 1][r];
                     d[l][r] = k;
                 }
             }
         }
     }

     restore(0, n - 1); cout << endl;
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
