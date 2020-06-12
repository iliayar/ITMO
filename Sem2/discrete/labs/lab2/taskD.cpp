
// Generated at 2020-06-09 19:06:59.153591 
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
#define FILENAME "nfc"


const int MOD = 1e+9 + 7;


//entry
void sol() {
    map<char, vector<vector<char>>> a;

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
    string s; cin >> s;
    vector<vector<vector<int>>> dp (30 , vector<vector<int>>(s.length() + 1, vector<int>(s.length() + 1, 0)));
    for(auto& p : a) {
        for(auto& v : p.second) {
            if(v.size() == 2) continue;
            for(int i = 0; i < s.length(); ++i) {
                dp[p.first - 'A'][i][i] += (s[i] == v[0]);
            }
        }
    }
    for(int i = 0; i < s.length(); ++i) {
        for(auto& p : a) {
            for(int j = 0; j + i < s.length(); ++j) {
                for(auto& v : p.second) {
                    if(v.size() == 1) continue;
                    for(int k = j; k < j + i; ++k) {
                        dp[p.first - 'A'][j][j + i] += dp[v[0] - 'A'][j][k]*dp[v[1] - 'A'][k + 1][j + i] % MOD;
                        dp[p.first - 'A'][j][j + i] %= MOD;
                    }
                }
            }
        }
    }
    cout << dp[start - 'A'][0][s.length() - 1] << endl;
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
