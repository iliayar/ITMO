
// Generated at 2021-02-27 23:07:52.904971 
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

    int n, m, a, b; cin >> n >> m >> a >> b;
    A.resize(n*m, vint());
    B.resize(n*m, vint());
    p.resize(n*m, -1);
    // rp.resize(m, -1);
    was.resize(n*m, false);

    int freen = 0;
    vint lol(n*m, true);

    for(int i = 0; i < n; ++i) {
        for(int j = 0; j < m; ++j) {
            char c; cin >> c;
            if (c == '*') {
                freen++;
                if((i + j)%2) {
                    if(i > 0 && lol[(i - 1)*m + j]) {
                        A[i*m + j].push_back((i - 1)*m + j);
                        B[(i - 1)*m + j].push_back(i*m + j);
                    }
                    if(j > 0 && lol[(i*m +j - 1)]) {
                        A[i*m + j].push_back(i*m +j - 1);
                        B[i*m + j - 1].push_back(i*m + j);
                    }
                } else {
                    if(i > 0 && lol[(i - 1)*m + j]) {
                        B[i*m + j].push_back((i - 1)*m + j);
                        A[(i - 1)*m + j].push_back(i*m + j);
                    }
                    if(j > 0 && lol[(i*m +j - 1)]) {
                        B[i*m + j].push_back(i*m +j - 1);
                        A[i*m + j - 1].push_back(i*m + j);
                    }
                }
            } else {
                lol[i*m + j] = false;
            }
        }
    }
    
    // for (int i = 0; i < n; ++i) {
    //     int u;
    //     while(true) {
    //         cin >> u;
    //         if(u == 0) break;
    //         u--;
    //         A[i].push_back(u);
    //         B[u].push_back(i);
    //     }
    // }

    for(int v = 0; v < A.size(); ++v) {
        if(dfs(v)) {
        }
        for(int& w : was) {
            w = false;
        }
    }

    vector<pair<int, int>> res;
    for(int i = 0; i < B.size(); ++i) {
        if(p[i] != -1) {
            res.emplace_back(p[i] + 1, i + 1);
        }
    }
    if(a < 2*b) {
        cout << res.size()*a + (freen - 2*res.size())*b << endl;
    } else {
        cout << b*freen << endl;
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
