
// Generated at 2021-03-07 23:17:53.513105 
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
#define DBG(x, ...) cout << ">>> DBG "  << #__VA_ARGS__ << endl << x << endl << "<<< DBG " << #__VA_ARGS__ << endl
#define DBG_CODE(x) x
#else
#define DBG(x, ...)
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
struct Event {
    int time;
    double x;
    double y;

    friend ostream& operator<<(ostream& o, const Event& e) {
        o << e.time << " (" << e.x << ", " << e.y << ")";
        return o;
    }
};
vector<Event> a;
vint2 A;


int v;

vint p;
// vint rp;
vint was;

bool check_event(Event a, Event b) {
    return sqrt((a.x - b .x)*(a.x - b .x) + (a.y - b.y)*(a.y - b.y))*60/v <= abs(a.time - b.time);
}

bool dfs(int v) {
    if(was[v]) return false;
    was[v] = true;
    for(int u : A[v]) {
        if(p[u] == -1 || dfs(p[u])) {
          p[u] = v;
          return true;
        }
    }
    return false;
}

// entry
void sol() {

    int n; cin >> n >> v;
    A.resize(n, vint());
    p.resize(n, -1);
    was.resize(n, false);

    for (int i = 0; i < n; ++i) {
        int h, m, x, y;
        char _;
        cin >> h >> _ >> m >> x >> y;
        Event e = {h*60 + m, static_cast<double>(x), static_cast<double>(y)};
        a.push_back(e);
    }

    A.resize(a.size(), {});
    sort(a.begin(), a.end(), [](Event& a, Event& b) {
        return a.time < b.time;
    });

    for(int i = 0; i < a.size(); ++i) {
        for(int j = i + 1; j < a.size(); ++j) {
            if(check_event(a[i], a[j])) {
                A[i].push_back(j);
            }
        }
    }

    for(int v = 0; v < n; ++v) {
        dfs(v);
        for(int& w : was) {
            w = false;
        }
    }

    // vector<pair<int, int>> res;
    int res = 0;
    for(int i = 0; i < n; ++i) {
        if(p[i] != -1) {
            res++;
        }
    }
    cout << n - res << endl;
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
