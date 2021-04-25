
// Generated at 2020-05-24 02:04:03.118407 
// By iliayar
#pragma comment(linker, "/STACK:36777216")
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <cstdio>
#include <map>
#include <unordered_set>
#include <ctime>
#include <cstdlib>
#include <queue>


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

using vint = vector<int>;
using vint2 = vector<vint>;

//##################CODE BEGIN#############
int n;
vint2 to;
vint res;
vint w;

void count_w(int u, int from) {
    w[u] = 1;
    for(int v : to[u]) {
        if(v == from || res[v] != -1) continue;
        count_w(v, u);
        w[u] += w[v];
    }
}

int find_centroid(int u, int from, int s) {
    while(true) {
        bool flag = true;
        for(int v : to[u]) {
            if(v == from || res[v] != -1) continue;
            if(w[v] > (s + 1)/2) {
                flag = false;
                from = u;
                u = v;
                break;
            }
        }
        if(flag) break;
    }
    return u;
}

void decompose(int u, int from) {
    count_w(u, from);
    u = find_centroid(u, from, w[u]);
    res[u] = from;
    for(int v : to[u]) {
        if(res[v] != -1) continue;
        decompose(v, u);
    }
}

//entry
void sol() {
    cin >> n; n++;
    res.resize(n, -1);
    w.resize(n);
    to.resize(n, {});
    for(int i = 1; i < n - 1; ++i) {
        int u, v; cin >> u >> v;
        to[u].push_back(v);
        to[v].push_back(u);
    }
    decompose(1, 0);
    for(int i = 1; i < n; ++i) {
        cout << res[i] << " ";
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
