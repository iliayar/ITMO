
// Generated at 2020-03-05 03:47:56.270606 
// By iliayar
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <cstdio>
#include <map>


using namespace std;

#define ON 1
#define OFF 0

#define int long long
#define vint vector<int>
#ifdef LOCAL
#define DBG(x) cout << "DBG: " << x << endl
#define DBG_CODE(x) x
#else
#define DBG(x)
#define DBG_CODE(x)
#endif

//##################CODE BEGIN##############include <exception>

struct Node {

  int max = 0;
  int add = 0;
  bool isadd = false;

  int x = -1;
  int y = -1;
};

vector<vector<Node>> tree;

Node E = Node();

int n;

Node eval(Node a, Node b, Node c, Node d) {
  Node t = E;
  t.max = a.max;
  t.x = a.x;
  t.y = a.y;
  if (b.max > t.max) {
    t.max = b.max;
    t.x = b.x;
    t.y = b.y;
  }
  if (c.max > t.max) {
    t.max = c.max;
    t.x = c.x;
    t.y = c.y;
  }
  if (d.max > t.max) {
    t.max = d.max;
    t.x = d.x;
    t.y = d.y;
  }
  return t;
}

void propagate(int vx, int vy) {
  if (!tree[vx][vy].isadd)
    return;
  if ((vx * 2 + 2 > tree.size()) || (vy * 2 + 2) > tree[vx].size())
    return;

  tree[vx * 2 + 1][vy * 2 + 1].add += tree[vx][vy].add;
  tree[vx * 2 + 1][vy * 2 + 1].max += tree[vx][vy].add;
  tree[vx * 2 + 1][vy * 2 + 1].isadd = true;

  tree[vx * 2 + 2][vy * 2 + 1].add += tree[vx][vy].add;
  tree[vx * 2 + 2][vy * 2 + 1].max += tree[vx][vy].add;
  tree[vx * 2 + 2][vy * 2 + 1].isadd = true;

  tree[vx * 2 + 1][vy * 2 + 2].add += tree[vx][vy].add;
  tree[vx * 2 + 1][vy * 2 + 2].max += tree[vx][vy].add;
  tree[vx * 2 + 1][vy * 2 + 2].isadd = true;

  tree[vx * 2 + 2][vy * 2 + 2].add += tree[vx][vy].add;
  tree[vx * 2 + 2][vy * 2 + 2].max += tree[vx][vy].add;
  tree[vx * 2 + 2][vy * 2 + 2].isadd = true;

  tree[vx][vy].isadd = false;
  tree[vx][vy].add = 0;
}

void t_add(int slx, int srx, int sly, int sry, int vx, int vy, int lx, int rx,
           int ly, int ry) {
  if ((srx <= slx) || (sry <= sly)) {
    return;
  }
  DBG("t_add (" << lx << ", " << rx << ") (" << ly << ", " << ry << ")");
  propagate(vx, vy);
  if ((slx == lx) && (srx == rx) && (sly == ly) && (sry == ry)) {
      DBG("Found");
    tree[vx][vy].add += 1;
    tree[vx][vy].max += 1;
    tree[vx][vy].isadd = true;
    tree[vx][vy].x = lx;
    tree[vx][vy].y = ly;
    return;
  }
  int mx = (lx + rx) / 2;
  int my = (ly + ry) / 2;
  t_add(slx, min(srx, mx), sly, min(sry, my), vx * 2 + 1, vy * 2 + 1, lx, mx,
        ly, my);
  t_add(slx, min(srx, mx), max(sly, my), sry, vx * 2 + 1, vy * 2 + 2, lx, mx,
        my, ry);
  t_add(max(slx, mx), srx, sly, min(sry, my), vx * 2 + 2, vy * 2 + 1, mx, rx,
        ly, my);
  t_add(max(slx, mx), srx, max(sly, my), sry, vx * 2 + 2, vy * 2 + 2, mx, rx,
        my, ry);
  tree[vx][vy] =
      eval(tree[vx * 2 + 1][vy * 2 + 1], tree[vx * 2 + 2][vy * 2 + 1],
           tree[vx * 2 + 1][vy * 2 + 2], tree[vx * 2 + 2][vy * 2 + 2]);
}

struct Request {
  int slx;
  int srx;
  int sly;
  int sry;
};

// entry
void sol() {
  int m;
  cin >> m;
  vector<Request> requests(0);

  int mi = 0, ma = 0;

  for (int i = 0; i < m; ++i) {
    Request t;
    cin >> t.slx >> t.sly >> t.srx >> t.sry;
    t.srx++;
    t.sry++;
    mi = min(mi, min(min(t.slx, t.srx), min(t.sly, t.sry)));
    ma = max(ma, max(max(t.slx, t.srx), max(t.sly, t.sry)));
    requests.push_back(t);
  }

  mi = abs(mi);

  n = ma + mi;
  DBG(ma << " " << mi);

  tree.resize(n * 8, vector<Node>(n * 8, E));
  for (Request r : requests) {
    DBG("Request");
    t_add(r.slx + mi, r.srx + mi, r.sly + mi, r.sry + mi, 0, 0, 0, n, 0, n);
    DBG(tree[0][0].max);
  }
  cout << tree[0][0].max << endl;
  cout << tree[0][0].x << " " << tree[0][0].y << endl;
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
    cin.tie(0);
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
