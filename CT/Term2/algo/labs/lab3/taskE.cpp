
// Generated at 2020-05-20 02:00:28.949424 
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

void build_jmp_0(int u, int from, int h, vint2& jmp, vint& d, vint2& to)
{
    DBG("build_jmp_0 " << u << " from " << from);
    jmp[u][0] = from;
    d[u] = h;
    for(int v : to[u]) {
        if(v != from) {
            DBG("\t" << v << " from " << u);
            build_jmp_0(v, u, h + 1, jmp, d, to);
        }
    }
}

int count(int& res, int u, vint2& jmp, vint& a, vint& b, vint2& to)
{
    int r = a[u];
    for(int v : to[u]) {
        if(v != jmp[u][0]) {
            int rr = count(res, v, jmp, a, b, to);
            if(rr == 0) res++;
            r += rr;
        }
    }
    return r - 2*b[u];
}

//entry
void sol() {

    int n; cin >> n;
    int logn = log2(n);
    vint2 jmp(n, vint(logn, 0));
    vint d(n, 0);
    vint2 to(n, vint{});
    for(int i = 0; i < n - 1; ++i) {
        int u, v; cin >> u >> v;
        u--; v--;
        to[u].push_back(v);
        to[v].push_back(u);
    }
    build_jmp_0(0, 0, 0, jmp, d, to);
    for(int i = 1; i < logn; ++i) {
        for(int j = 1; j < n; ++j) {
            jmp[j][i] = jmp[jmp[j][i - 1]][i - 1];
        }
    }
    int m; cin >> m;
    vint a(n, 0);
    vint b(n, 0);
    for(int i = 0; i < m; ++i) {
        int u, v; cin >> u >> v;
        u--; v--;
        a[u]++; a[v]++;
        b[lca(u, v, jmp, d)]++;
    }
    int res = 0;
    count(res, 0, jmp, a, b, to);
    cout << res << endl;
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
