
// Generated at 2020-03-05 17:14:39.012009 
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

//##################CODE BEGIN#############

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

Node eval(Node a, Node b) {
    Node t = E;
    if (a.max > b.max) {
        t.max = a.max;
        t.x = a.x;
        t.y = a.y;
    } else {
        t.max = b.max;
        t.x = b.x;
        t.y = b.y;
    }

    return t;
}

void t_propagate(int vx, int vy) {
    if (!tree[vx][vy].isadd)
        return;
    DBG("Propagate");

    if (vx * 2 + 2 < tree.size()) {
        tree[vx * 2 + 1][vy].add += tree[vx][vy].add;
        tree[vx * 2 + 1][vy].max += tree[vx][vy].add;
        tree[vx * 2 + 1][vy].isadd = true;
        tree[vx * 2 + 2][vy].add += tree[vx][vy].add;
        tree[vx * 2 + 2][vy].max += tree[vx][vy].add;
        tree[vx * 2 + 2][vy].isadd = true;
    }
    if (vy * 2 + 2 < tree.size()) {
        tree[vx][vy * 2 + 1].add += tree[vx][vy].add;
        tree[vx][vy * 2 + 1].max += tree[vx][vy].add;
        tree[vx][vy * 2 + 1].isadd = true;
        tree[vx][vy * 2 + 2].add += tree[vx][vy].add;
        tree[vx][vy * 2 + 2].max += tree[vx][vy].add;
        tree[vx][vy * 2 + 2].isadd = true;
    }
    tree[vx][vy].isadd = true;
}

void t_add_y(int slx, int srx, int sly, int sry, int x, int lx, int rx, int vx,
             int v, int ly, int ry) {
    if ((srx < slx) || (sry < sly)) {
        return;
    }
    DBG("t_add_y (" << lx << ", " << rx << ") (" << ly << ", " << ry << ")");
    DBG("t_add_y (" << sly << ", " << sry << ")");
    t_propagate(vx, v);
    if ((sly == ly) && (sry == ry)) {
        DBG("t_add_y end");
        if ((srx == rx) && (slx == lx)) {
            DBG("t_add END");
            tree[vx][v].isadd = true;
            tree[vx][v].add += x;
            tree[vx][v].max += x;
            tree[vx][v].x = slx;
            tree[vx][v].y = sly;
        } else {
            tree[vx][v] = eval(tree[vx * 2 + 1][v], tree[vx * 2 + 2][v]);
        }
        return;
    }
    int m = (ly + ry) / 2;
    t_add_y(slx, srx, sly, min(sry, m), x, lx, rx, vx, v * 2 + 1, ly, m);
    t_add_y(slx, srx, max(sly, m + 1), sry, x, lx, rx, vx, v * 2 + 2, m + 1, ry);
    tree[vx][v] = eval(tree[vx][v * 2 + 1], tree[vx][v * 2 + 2]);
}

void t_add_x(int slx, int srx, int sly, int sry, int x, int v, int lx, int rx) {
    if (srx < slx) {
        return;
    }
    DBG("t_add_x (" << lx << ", " << rx << ")");
    if ((srx == rx) && (slx == lx)) {
        DBG("t_add_x end");
        t_add_y(slx, srx, sly, sry, x, lx, rx, v, 0, 0, n);
        return;
    }
    int m = (lx + rx) / 2;
    t_add_x(slx, min(m, srx), sly, sry, x, v * 2 + 1, lx, m);
    t_add_x(max(slx, m + 1), srx, sly, sry, x, v * 2 + 2, m + 1, rx);
    t_add_y(slx, srx, sly, sry, x, lx, rx, v, 0, 0, n);
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
        t_add_x(r.slx + mi, r.srx + mi, r.sly + mi, r.sry + mi, 1, 0, 0, n);
    }
    cout << tree[0][0].max << endl;
    cout << tree[0][0].x - mi << " " << tree[0][0].y - mi << endl;
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
