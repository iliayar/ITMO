
// Generated at 2020-05-19 18:38:16.880943 
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

int follow(int u, vint& mv)
{
    if(mv[u] == u) return u;
    mv[u] = follow(mv[u], mv);
    return mv[u];
}


//entry
void sol() {

    int n; cin >> n;
    int logn = log2(n);
    vint2 jmp(1, vint(logn, 0));
    vint mv(1, 0);
    vint d(1, 0);
    int size = 0;
    for(int i = 0; i < n; ++i) {
        int t;
        char op; cin >> op;
        switch(op) {
            case '+':
                cin >> t; t--;
                size++;
                jmp.push_back(vint(logn, 0));
                mv.push_back(size);
                d.push_back(d[t] + 1);
                jmp[size][0] = t;
                for(int j = 1; j < logn; ++j) {
                    jmp[size][j] = jmp[jmp[size][j - 1]][j - 1];
                }
                break;
            case '-':
                cin >> t; t--;
                mv[t] = jmp[t][0];
                break;
            case '?':
                int u, v; cin >> u >> v;
                u--; v--;
                cout << follow(lca(u, v, jmp, d), mv) + 1 << endl;
                break;
        }
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
