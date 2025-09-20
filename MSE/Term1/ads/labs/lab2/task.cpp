
// Generated at 2024-09-19 00:35:31.094509 
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
template <typename T>
class min_queue {
    public:
        min_queue() {}

        void push(T v) {
            while (!d_.empty() && d_.back() > v) {
                d_.pop_back();
            }
            d_.push_back(v);
        }

        void pop(T const& v) {
            if (v == d_.front()) {
                d_.pop_front();
            }
        }

        T cur_min() {
            return d_.front();
        }

    private:
        deque<T> d_;
};

//entry
void sol() {
    int n, L; cin >> n >> L;

    vint2 a(n, vint(n, 0));
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            cin >> a[i][j];
        }
    }

    vint2 mj(n, vint(n - L + 1, INF));

    for (int i = 0; i < n; ++i) {
        min_queue<int> q;

        for (int j = 0; j < L - 1; ++j) {
            q.push(a[i][n - j - 1]);
        }

        for (int j = L - 1; j < n; ++j) {
            q.push(a[i][n - j - 1]);
            mj[i][n - j - 1] = q.cur_min();
            q.pop(a[i][n - j + L - 2]);
        }
    }

    for (int i = 0; i < n; ++i) {
        DBG() << mj[i] << endl;
    }
    DBG() << "======================" << endl;

    vint2 mi(n - L + 1, vint(n - L + 1, INF));
    for (int j = 0; j < n - L + 1; ++j) {
        min_queue<int> q;

        for (int i = 0; i < L - 1; ++i) {
            q.push(mj[n - i - 1][j]);
        }

        for (int i = L - 1; i < n; ++i) {
            q.push(mj[n - i - 1][j]);
            mi[n - i - 1][j] = q.cur_min();
            q.pop(mj[n - i + L - 2][j]);
        }
    }

    for (int i = 0; i < n - L + 1; ++i) {
        DBG() << mi[i] << endl;
    }
    DBG() << "======================" << endl;

    for (int i = 0; i < n - L + 1; ++i) {
        for (int j = 0; j < n - L + 1; ++j) {
            cout << mi[i][j] << " ";
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
