
// Generated at 2022-04-10 21:40:53.967717 
// By iliayar
#include <iterator>
#define _USE_MATH_DEFINES
#pragma comment(linker, "/STACK:36777216")
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


using namespace std;

#define ON 1
#define OFF 0

#define int long long
#ifdef LOCAL
#define DBG(x) cout << "DBG: " << x << endl
#define DBG_CODE(x) x
#else
#define DBG(x)
#define DBG_CODE(x)
#endif

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

//##################CODE BEGIN##############include <algorithm>

//entry
void sol() {
    cout << fixed;
    cout.precision(17);
    int K; cin >> K;
    vint ls;
    for (int i = 0; i < K; ++i) {
        int t; cin >> t;
        ls.push_back(t);
    }
    int alpha; cin >> alpha;
    int N; cin >> N;
    vector<map<string, int>> c(K);
    vint cc(K);
    set<string> ww;
    for (int i = 0; i < N; ++i) {
        int C; cin >> C; C--;
        int L; cin >> L;
        set<string> tw;
        for (int j = 0; j < L; ++j) {
            string w; cin >> w;
            ww.insert(w);
            tw.insert(w);
        }
        for (auto const& w : tw) {
            c[C][w] += 1;
        }
        cc[C] += 1;
    }

    // DBG(c);
    // DBG(cc);

    
    int M; cin >> M;
    for (int i = 0; i < M; ++i) {
        int L; cin >> L;
        set<string> ws;
        for (int j = 0; j < L; ++j) {
            string w; cin >> w;
            ws.insert(w);
        }

        vector<double> r;
        for (int j = 0; j < K; ++j) {
          double res = log(cc[j]) - log(N) + log(ls[j]);
          for (auto& w : ww) {
              double a = c[j][w] + alpha;
              double b = cc[j] + 2 * alpha;
              // DBG("Class: " << j << "\tWord: " << w << "\t" << make_pair(a, b));
              if (ws.find(w) != ws.end()) {
                  res += log(a) - log(b);
              } else {
                res += log(b - a) - log(b);
              }
          }
          r.push_back(res);
        }
        double mv = *max_element(r.begin(), r.end());
        double st = 0;
        for (auto v : r) {
            st += exp(v - mv);
        }
        st = log(st) + mv;
        for (auto v : r) {
            cout << exp(v - st) << " ";
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
