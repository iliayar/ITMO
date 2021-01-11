// Generated at 2020-06-09 00:05:59.377676 
// By iliayar
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <set>
#include <unordered_set>
#include <cstdio>
#include <map>
#include <cctype>
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
#define FILENAME "epsilon"
 
 
 
//entry
void sol() {
 
    map<char, vector<vector<char>>> a;
 
    int m = 3;
 
    int n;
    char start;
    cin >> n >> start;
 
    cin.get();
    for(int i = 0; i < n; ++i) {
        char f = cin.get();
        cin.get(); //' '
        cin.get(); //'-'
        cin.get(); //'>'
        char c = cin.get(); //' '
        a[f].push_back({});
        vector<char>& cur = a[f].back();
        if(c == '\n') continue;
        for(c = cin.get(); c != '\n' && c != -1; c = cin.get()) {
            cur.push_back(c);
        }
    }
 
    vector<bool> eps(30);
    for(int i = 0; i < n; ++i) {
        for(auto p : a) {
            for(auto v : p.second) {
                bool flag = true;
                for(char t : v) {
                    if(isupper(t)) {
                        if(!eps[t - 'A']) {
                            flag = false;
                        }
                    }
                    if(islower(t)) {
                        flag = false;
                    }
                }
                eps[p.first - 'A'] = eps[p.first - 'A'] || flag;
            }
        }
    }
 
    for(int i = 0; i < 30; ++i) {
        if(eps[i]) {
            cout << static_cast<char>(i + 'A') << " ";
        }
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
