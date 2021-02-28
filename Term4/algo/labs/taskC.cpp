
// Generated at 2021-02-27 02:27:56.487376 
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
vint was;
vint wasB;

bool dfs(int v) {
    if(was[v]) return false;
    was[v] = true;
    for(int u : A[v]) {
        if(p[u] == -1) {
            p[u] = v;
            return true;
        } else {
            if(dfs(p[u])) {
                p[u] = v;
                return true;
            }
        }
    }
    return false;
}

void dfs2(int v) {
    if(was[v]) return;
    was[v] = 1;
    for(int u : A[v]) {
        if(wasB[u]) continue;
        wasB[u] = true;
        if(p[u] != -1) {
            dfs2(p[u]);
        }
    }
}

// entry
void sol() {

    int k; cin >> k;
    for(int j = 0; j < k; ++j) {
        int m, n; cin >> m >> n;
        A.clear(); B.clear(); p.clear(); was.clear(); wasB.clear();
        A.resize(m, vint());
        B.resize(n, vint());
        p.resize(n, -1);
        was.resize(m, false);
        wasB.resize(n, false);

        for(int i = 0; i < m; ++i) {
            vint r(n, 1);
            int u;
            while((cin >> u, u) != 0) {
                r[u-1] = 0;
            }
            for(int q = 0; q < n; ++q) {
                if(r[q] == 1) {
                    A[i].push_back(q);
                    B[q].push_back(i);
                }
            }
        }

        for(int v = 0; v < m; ++v) {
            if(dfs(v)) {
            }
            for(int& w : was) {
                w = false;
            }
        }
        DBG(p);
        vint free(m, true);
        for(int q = 0; q < n; ++q) {
            if(p[q] != -1) {
                free[p[q]] = false;
            }
        }
        DBG(free);
        for(int v = 0; v < m; ++v) {
            if(free[v]) dfs2(v);
        }
        vint resA;
        vint resB;
        for(int v = 0; v < m; ++v) {
            if(was[v]) resA.push_back(v + 1);
        }
        for(int v = 0; v < n; ++v) {
            if(!wasB[v]) resB.push_back(v + 1);
        }
        cout << resA.size() + resB.size() << endl;
        cout << resA.size() << " " << resB.size() << endl;
        cout << resA;
        cout << resB;
    }
    
    


    // vector<pair<int, int>> res;
    // for(int i = 0; i < m; ++i) {
    //     if(p[i] != -1) {
    //         res.emplace_back(p[i] + 1, i + 1);
    //     }
    // }
    // cout << res.size() << endl;
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
