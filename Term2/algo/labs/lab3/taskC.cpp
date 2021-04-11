
// Generated at 2020-05-17 01:17:22.362525 
// By iliayar
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <cstdio>
#include <map>
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

//##################CODE BEGIN#############

#define FILE_IO ON
#define FILENAME "minonpath"

using vint = vector<int>;
using vint2 = vector<vint>;


const int INF = 1e+6 + 1;

int log2(int n) {
    int res = 0;
    while(n) {n >>= 1; res++;}
    return res;
}

int lca(int u, int v, vint2 &jmp, vint &d)
{
    if (d[v] > d[u])
        swap(v, u);
    int logn = log2(jmp.size()) - 1;
    for(int i = logn; i >= 0; --i) {
        if(d[jmp[u][i]] >= d[v])
            u = jmp[u][i];
    }
    if (v == u)
        return u;
    for(int i = logn; i >= 0; --i) {
        if(jmp[v][i] != jmp[u][i]) {
            v = jmp[v][i];
            u = jmp[u][i];
        }
    }
    return jmp[v][0];
}

int path_min(int u, int v, vint2 &jmp, vint &d, vint2 &mi)
{
    int p = lca(u, v, jmp, d);
    DBG(p + 1);
    int logn = log2(jmp.size()) - 1;
    int mi_u = INF;
    int mi_v = INF;
    for(int i = logn; i >= 0; --i) {
        if(d[jmp[u][i]] >= d[p]) {
            mi_u = min(mi_u, mi[u][i]);
            u = jmp[u][i];
        }
    }
    for(int i = logn; i >= 0; --i) {
        if(d[jmp[v][i]] >= d[p]) {
            mi_v = min(mi_v, mi[v][i]);
            v = jmp[v][i];
        }
    }
    return min(mi_v, mi_u);
}


//entry
void sol() {

    int n; cin >> n;
    vint2 jmp(n, vector<int>(log2(n), 0));
    vint2 mi(n, vector<int>(log2(n), INF));
    vint d(n, 0);
    for(int i = 1; i < n; ++i) {
      cin >> jmp[i][0] >> mi[i][0];
      jmp[i][0]--;
      d[i] = d[jmp[i][0]] + 1;
    }
    int m; cin >> m;
    for(int i = 1; i < log2(n); ++i) {
        for(int j = 1; j < n; ++j) {
            jmp[j][i] = jmp[jmp[j][i - 1]][i - 1];
            mi[j][i] = min(mi[j][i - 1], mi[jmp[j][i - 1]][i - 1]);
        }
    }
    DBG_CODE(
        for(int i = 0; i < n; ++i) {
            cout << i + 1 << ": ";
            for(int j = 0; j < log2(n + 1); ++j) {
                if(jmp[i][j] == 0) continue;
                cout << jmp[i][j] + 1 << " ";
            }
            cout << endl;
        }
        for(int i = 0; i < n; ++i) {
            cout << i + 1 << ": " << d[i] << endl;
        }
    );
    for(int i = 0; i < m; ++i) {
        int u, v; cin >> u >> v;
        u--; v--;
        cout << path_min(u, v, jmp, d, mi) << endl;
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
