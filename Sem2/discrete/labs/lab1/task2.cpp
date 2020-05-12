
// Generated at 2020-05-02 03:51:04.198170 
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
#define FILE_IO ON
#define FILENAME "problem2"

struct DFA
{


    DFA(int n)
    {
        acc.resize(n + 1, false);
        to.resize(n + 1);
        a[0].resize(n+1, false);
        a[1].resize(n+1, false);
        a[0][1] = true;
    }

    void accept(int n)
    {
        acc[n] = true;
    }

    void add(int f, char c, int t)
    {
        to[f][c].push_back(t);
    }


    bool check(string s)
    {
        for(char c : s) {
            for(int i = 1; i < a[0].size(); ++i) {
                if(a[0][i]) {
                    for(int j : to[i][c]) {
                        a[1][j] = true;
                    }
                }
                a[0][i] = false;
            }
            swap(a[0], a[1]);
        }
        for(int i = 1; i < a[0].size(); ++i) {
            if(a[0][i]) return true;
        }
        return false;
    }

    vector<bool> a[2];
    vector<bool> acc;
    vector<map<char, vector<int>>> to;

};

//entry
void sol()
{
    string s; cin >> s;
    int n, m, k; cin >> n >> m >> k;
    DFA a(n);
    for(int i = 0; i < k; ++i) {
        int t; cin >> t;
        a.accept(t);
    }
    for(int i = 0; i < m; ++i) {
        int f, t;
        char c;
        cin >> f >> t >> c;
        a.add(f, c, t);
    }
    if(a.check(s)) {
        cout << "Accepts" << endl;
    } else {
        cout << "Rejects" << endl;
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
