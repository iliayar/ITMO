
// Generated at 2020-05-15 19:47:55.311552 
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
#define vint vector<int>
#ifdef LOCAL
#define DBG(x) cout << "DBG: " << x << endl
#define DBG_CODE(x) x
#else
#define DBG(x)
#define DBG_CODE(x)
#endif

//##################CODE BEGIN#############
int log2(int n) {
    int res = 0;
    while(n) {n >>= 1; res++;}
    return res;
}

struct Node {
    Node * parent = nullptr;
    vector<Node*> to;
};

//entry
void sol() {

    int n; cin >> n;
    vector<int> p(n + 1);
    for(int i = 1; i <= n; ++i) {
        cin >> p[i];
    }
    vector<vector<int>> jmp(n + 1, vector<int>(log2(n + 1), 0));

    for(int i = 1; i <= n; ++i) {
        jmp[i][0] = p[i];
    }
    for(int i = 1; i < log2(n + 1); ++i) {
        for(int j = 1; j <= n; ++j) {
            jmp[j][i] = jmp[jmp[j][i - 1]][i - 1];
        }
    }
    for(int i = 1; i <= n; ++i) {
        cout << i << ": ";
        for(int j = 0; j < log2(n + 1); ++j) {
            if(!jmp[i][j]) continue;
            cout << jmp[i][j] << " ";
        }
        cout << endl;
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
