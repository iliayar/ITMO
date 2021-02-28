
// Generated at 2021-02-27 22:26:43.405697 
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
struct VLine {
    int x;
    int y1;
    int y2;
};

struct HLine {
    int y;
    int x1;
    int x2;
};

bool intersects(VLine vline, HLine hline) {
    return hline.x1 <= vline.x && vline.x <= hline.x2 && vline.y1 <= hline.y &&
        hline.y <= vline.y2;
}

vint2 A;
vint2 B;

vint p;
vint was;
vint wasB;

bool dfs(int v) {
    if (was[v])
        return false;
    was[v] = true;
    for (int u : A[v]) {
        if (p[u] == -1) {
            p[u] = v;
            return true;
        } else {
            if (dfs(p[u])) {
                p[u] = v;
                return true;
            }
        }
    }
    return false;
}

void dfs2(int v) {
    if (was[v])
        return;
    was[v] = 1;
    for (int u : A[v]) {
        if (wasB[u])
            continue;
        wasB[u] = true;
        if (p[u] != -1) {
            dfs2(p[u]);
        }
    }
}

// entry
void sol() {

    int n;
    cin >> n;

    vector<HLine> preA;
    vector<VLine> preB;

    for(int i = 0; i < n; ++i) {
        int x1, x2, y1, y2; cin >> x1 >> y1 >> x2 >> y2;
        if(x1 == x2) {
            B.push_back({});
            VLine line{x1, min(y1, y2), max(y1, y2)};
            for(int j = 0; j < preA.size(); ++j) {
                if(intersects(line, preA[j])) {
                    B.back().push_back(j);
                    A[j].push_back(B.size() - 1);
                }
            }
            preB.push_back(line);
        } else {
            A.push_back({});
            HLine line{y1, min(x1, x2), max(x1, x2)};
            for(int j = 0; j < preB.size(); ++j) {
                if(intersects(preB[j], line)) {
                    A.back().push_back(j);
                    B[j].push_back(A.size() - 1);
                }
            }
            preA.push_back(line);
        }
    }


    
    p.resize(B.size(), -1);
    was.resize(A.size(), false);
    wasB.resize(B.size(), false);

    for (int v = 0; v < A.size(); ++v) {
        if (dfs(v)) {
        }
        for (int &w : was) {
            w = false;
        }
    }
    DBG(p);
    vint free(A.size(), true);
    for (int q = 0; q < B.size(); ++q) {
        if (p[q] != -1) {
            free[p[q]] = false;
        }
    }
    DBG(free);
    for (int v = 0; v < A.size(); ++v) {
        if (free[v])
            dfs2(v);
    }
    vint resA;
    vint resB;
    for (int v = 0; v < A.size(); ++v) {
        if (was[v])
            resA.push_back(v + 1);
    }
    for (int v = 0; v < B.size(); ++v) {
        if (!wasB[v])
            resB.push_back(v + 1);
    }
    cout << resA.size() + resB.size() << endl;
    // cout << resA.size() << " " << resB.size() << endl;
    // cout << resA;
    // cout << resB;

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
