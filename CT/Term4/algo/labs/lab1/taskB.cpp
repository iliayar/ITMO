
// Generated at 2021-03-07 22:48:35.148989 
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
struct Edge {
  int from;
  int to;
  int i;

  friend ostream &operator<<(ostream &o, const Edge &e) {
    o << e.from << " -> " << e.to << " [" << e.i << "]";
    return o;
  }
};

struct Node {
  std::vector<Edge> to;
  int w;
  int i;
    friend ostream &operator<<(ostream& o, const Node& n) {
        o << n.w << " {" << Join<vector<Edge>>(n.to, ", ") << "}" << " [" << n.i << "]";
        return o;
    }
};

vector<Node> A;
vector<Node> B;

vint p;
vint was;
vint wasB;

bool dfs(int v, const vector<Node> &L) {
  if (was[v])
    return false;
  was[v] = true;
  for (Edge u : L[v].to) {
    if (p[u.to] == -1 || dfs(p[u.to], L)) {
      p[u.to] = v;
      return true;
    }
  }
  return false;
}

vector<Edge> kuhn(const vector<Node> &L, int sizeR) {
  was.clear();
  was.resize(L.size(), false);
  p.clear();
  p.resize(sizeR, -1);

  for (int v = 0; v < L.size(); ++v) {
    if (dfs(v, L)) {
    }
    for (int &w : was) {
      w = false;
    }
  }

  vector<Edge> res;
  for (int i = 0; i < sizeR; ++i) {
    if (p[i] != -1) {
      for (const Edge &ee : L[p[i]].to) {
        // ee.from = p[v];
        if (ee.to == i) {
          res.push_back(ee);
        }
      }
    }
  }
  return res;
}

// entry
void sol() {

  int n, m, e;
  cin >> n >> m >> e;
  A.resize(n, {std::vector<Edge>(), 0});
  B.resize(m, {std::vector<Edge>(), 0});

  for (int i = 0; i < n; ++i) {
    cin >> A[i].w;
    A[i].i = i;
  }
  for (int i = 0; i < m; ++i) {
    cin >> B[i].w;
    B[i].i = i;
  }

  for (int i = 0; i < e; ++i) {
    int u, v;
    cin >> u >> v;
    u--;
    v--;
    Edge e1 = {u, v, i};
    Edge e2 = {v, u, i};
    bool flag = false;
    for(Edge& a : A[u].to) {
        if(a.to == v) {
            flag = true;
            break;
        }
    }
    if(flag) continue;
    A[u].to.push_back(e1);
    B[v].to.push_back(e2);
  }

  DBG(Join(A, "\n"), A Pure);
  DBG(Join(B, "\n"), B Pure);

  sort(A.begin(), A.end(),
       [](const Node &a, const Node &b) { return a.w > b.w; });
  sort(B.begin(), B.end(),
       [](const Node &a, const Node &b) { return a.w > b.w; });

  DBG(Join(A, "\n"), A Sorted by weight);
  DBG(Join(B, "\n"), B Sorted by weight);

  vector<Edge> resA = kuhn(A, m);
  vector<Edge> resB = kuhn(B, n);

  sort(A.begin(), A.end(),
       [](const Node &a, const Node &b) { return a.i < b.i; });
  sort(B.begin(), B.end(),
       [](const Node &a, const Node &b) { return a.i < b.i; });

  DBG(Join(A, "\n"), A sorted by indecies);
  DBG(Join(B, "\n"), B sorted by indecies);

  DBG(Join(resA, ", "), A Mathes);
  DBG(Join(resB, ", "), B Matches);

  vector<bool> matchA(n, false);
  vector<bool> matchB(m, false);

  for(Edge& a : resA) {
      matchA[a.from] = true;
  }
  for(Edge& a : resB) {
      matchB[a.from] = true;
  }

  vector<Node> newA = A;
  // vector<Node> newB = B;

  for(Node& a : newA) {
      a.to.clear();
  }
  // for(Node& b : newB) {
  //     b.to.clear();
  // }

  for(int i = 0; i < n; ++i) {
      if(!matchA[i]) continue;
      for(Edge& e: A[i].to) {
          if(matchB[e.to]) {
              newA[i].to.push_back(e);
          }
      }
  }
  // for(int i = 0; i < m; ++i) {
  //     if(!matchB[i]) continue;
  //     for(Edge& e: B[i].to) {
  //         if(matchA[e.to]) {
  //             newB[i].to.push_back(e);
  //         }
  //     }
  // }

  DBG(Join(newA, "\n"), newA Pure);
  
  sort(newA.begin(), newA.end(),
       [](const Node &a, const Node &b) { return a.w > b.w; });
  // sort(newB.begin(), newB.end(),
  //      [](const Node &a, const Node &b) { return a.w > b.w; });

  vector<Edge> res = kuhn(newA, B.size());
  int sum = 0;
  for(Edge& a : res) {
      sum += A[a.from].w + B[a.to].w;
  }
  cout << sum << endl;
  cout << res.size() << endl;
  for(Edge& a : res) {
      cout << a.i + 1 << " ";
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
