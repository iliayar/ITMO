
// Generated at 2021-02-28 01:49:29.190923 
// By iliayar
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

using vint = vector<int>;
using vint2 = vector<vint>;

template<typename T>
class Join {
  T& v;
  string& separator;
  
public:
  
  Join(T v, string separator)
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

template<typename T>
ostream& operator<<(ostream& out, vector<T> v) {
  out << Join(v, " ") << endl;
  return out;
}

template<typename T, typename K>
ostream& operator<<(ostream& out, pair<T, K> p) {
  out << "(" << p.first << ", " << p.second << ")";
  return out;
}

//##################CODE BEGIN#############
vint2 A;
vint2 B;

vint p;
// vint rp;
vint was;

bool dfs(int v) {
    if(was[v]) return false;
    was[v] = true;
    for(int u : A[v]) {
        if(p[u] == -1) {
            // rp[u] = -1;
            p[u] = v;
            return true;
        } else {
            if(dfs(p[u])) {
                // rp[u] = p[u];
                p[u] = v;
                return true;
            }
        }
    }
    return false;
}

// entry
void sol() {

    int m, k, n; cin >> m >> k >> n;
    A.resize(m, vint());
    B.resize(k, vint());
    p.resize(k, -1);
    // rp.resize(m, -1);
    was.resize(m, false);
    vint2 hate(m, vint(k, false));

    int t; cin >> t;
    for(int i = 0; i < t; ++i) {
        int g, y; cin >> g >> y;
        g--; y -= m + 1;
        hate[g][y] = true;
    }

    vint moron(m + k, false);
    int q; cin >> q;
    for(int i = 0; i < q; ++i) {
        int tt; cin >> tt;
        moron[tt - 1] = true;
        if(tt > m) {
            tt -= m + 1;
            for(int j = 0; j < m; ++j) {
                if(!hate[j][tt]) {
                    A[j].push_back(tt);
                    B[tt].push_back(j);
                    DBG("Moron: " << j + 1 << " " << tt + m + 1);
                }
            }
        } else {
          tt -= 1;
          for (int j = 0; j < k; ++j) {
              DBG("AYAYYA " << j);
              if(!hate[tt][j]) {
                  A[tt].push_back(j);
                  B[j].push_back(tt);
                    DBG("Moron: " << tt + 1 << " " << j + m + 1);
              }
          }
        }
    }

    for(int v = 0; v < A.size(); ++v) {
        if(dfs(v)) {
        }
        for(int& w : was) {
            w = false;
        }
    }

    vector<pair<int, int>> res;
    vint doneA(m, false);
    vint doneB(k, false);
    for(int i = 0; i < B.size(); ++i) {
        if(p[i] != -1) {
            doneA[p[i]] = true;
            doneB[i] = true;
            moron[p[i]] = false;
            moron[i + m] = false;
            res.emplace_back(p[i] + 1, i + m + 1);
        }
    }
    // DBG(res);
    for(int mo : moron) {
        if(mo) {
            cout << "NO" << endl;
            return;
        }
    }

    if(res.size() > n) {
        cout << "NO" << endl;
        return;
    }

    A.clear();
    B.clear();
    A.resize(m, vint());
    B.resize(k, vint());

    for(int i = 0; i < m; ++i) {
        for(int j = 0; j < k; ++j) {
            if(!hate[i][j] && !doneA[i] && !doneB[j]) {
                A[i].push_back(j);
                B[j].push_back(i);
                // DBG("Edge: " << i + 1 << " " << j + m + 1);
            }
        }
    }

    p.clear();
    p.resize(k, -1);
    
    for(int v = 0; v < A.size(); ++v) {
        if(dfs(v)) {
        }
        for(int& w : was) {
            w = false;
        }
    }

    for(int i = 0; i < B.size(); ++i) {
        if(res.size() >= n) break;
        if(p[i] != -1) {
            res.emplace_back(p[i] + 1, i + m + 1);
        }
    }

    if(n > res.size()) {
        cout << "NO" << endl;
        return;
    }
    cout << "YES" << endl;
    for(auto [g, y] : res) {
        cout << g << " " << y << endl;
    }

    // for(auto [u, v] : res) {
    //     cout << u << " " << v << endl; 
    // }
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
