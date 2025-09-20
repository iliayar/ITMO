
// Generated at 2025-07-06 15:20:06.103653 
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
string s;
vint2 dp;
vint2 ty;
vint2 arg;

bool rep(int l, int r, int k) {
    if (r < l) return false;
    if ((r - l + 1) % k != 0) return false;

    for (int i = 1; i < (r - l + 1) / k; ++i) {
        for (int j = 0; j < k; ++j) {
            if (s[l + j] != s[l + i*k + j]) return false;
        }
    }
    return true;
}

void restore(int l, int r) {
    if (ty[l][r] == -1) {
        if (l != r) exit(1);
        cout << s[l];
    } else if (ty[l][r] == 0) {
        restore(l, arg[l][r]);
        restore(arg[l][r] + 1, r);
    } else if (ty[l][r] == 1) {
        int n = (r - l + 1) / arg[l][r];
        cout << n << "(";
        restore(l, l + arg[l][r] - 1);
        cout << ")";
    }
}

int log10(int n) {
    if (n == 0) return 1;
    int r = 0;
    while (n > 0) {
        n /= 10;
        r++;
    }
    return r;
}

//entry
void sol() {
    cin >> s;
    int n = s.length();
    dp.resize(n, vint(n, INF));
    ty.resize(n, vint(n, -1));
    arg.resize(n, vint(n, -1));
    for (int i = 0; i < n; ++i) {
        dp[i][i] = 1;
    }

    for (int le = 1; le < n; ++le) {
        for (int l = 0; l < n - le; ++l) {
            int r = l + le;
            for (int m = l; m < r; ++m) {
                int v = dp[l][m] + dp[m + 1][r];
                if (dp[l][r] > v) {
                    dp[l][r] = v;
                    ty[l][r] = 0;
                    arg[l][r] = m;
                }
            }
            for (int k = 1; k < (r - l + 1); ++k) {
                if (rep(l, r, k)) {
                    int v = dp[l][l + k - 1] + log10((r - l + 1) / k) + 2;
                    if (dp[l][r] > v) {
                        DBG() << "Rep: " << l << " " << r << " " << k << " " << v << endl;
                        dp[l][r] = v;
                        ty[l][r] = 1;
                        arg[l][r] = k;
                    }
                }
            }
        }
    }
    DBG() << "Len = " << dp[0][n-1] << endl;
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
