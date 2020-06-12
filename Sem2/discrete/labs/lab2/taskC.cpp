
// Generated at 2020-06-09 15:16:05.819009 
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
#define FILENAME "useless"



//entry
void sol() {

    map<char, vector<vector<char>>> a;

    int m = 3;

    int n;
    char start;
    cin >> n >> start;

    vector<bool> was(30, false);
    was[start - 'A'] = true;

    cin.get();
    for(int i = 0; i < n; ++i) {
        char f = cin.get();
        was[f - 'A'] = true;
        cin.get(); //' '
        cin.get(); //'-'
        cin.get(); //'>'
        char c = cin.get(); //' '
        a[f].push_back({});
        vector<char>& cur = a[f].back();
        if(c == '\n') continue;
        for(c = cin.get(); c != '\n' && c != -1; c = cin.get()) {
            cur.push_back(c);
            if(isupper(c)) {
                was[c - 'A'] = true;
            }
        }
    }

    vector<bool> reachable(30, false);
    reachable[start - 'A'] = true;
    vector<bool> productable(30, false);
    for(auto& p : a) {
        for(auto& v : p.second) {
            bool flag = true;
            for(auto& t : v) {
                if(isupper(t)) {
                    flag = false;
                }
            }
            productable[p.first - 'A'] = productable[p.first - 'A'] | flag;
        }
    }
    for(int i = 0; i < n; ++i) {
        for(auto& p : a) {
            for(auto& v : p.second) {
                bool flag = true;
                for(auto& t : v) {
                    if(isupper(t)) {
                        flag &= productable[t - 'A'];
                    }
                }
                productable[p.first - 'A'] = productable[p.first - 'A'] | flag;
            }
        }
    }
    for(auto& p : a) {
        if(!productable[p.first - 'A']) {
            p.second.clear();
        } else {
            p.second.erase(
                remove_if(
                    p.second.begin(),
                    p.second.end(),
                    [&](auto& v) {
                        for(auto& t : v) {
                            if(isupper(t)) {
                                if(!productable[t - 'A']) {
                                    return true;
                                }
                            }
                        }
                        return false;
                    }),
                p.second.end());
        }
    }
    for(int i = 0; i < n; ++i) {
        for(auto& p : a) {
            if(reachable[p.first - 'A']) {
                for(auto& v : p.second) {
                    for(auto& t : v) {
                        if(isupper(t)) {
                            reachable[t - 'A'] = true;
                        }
                    }
                }
            }
        }
    }

    for(int i = 0; i < 30; ++i) {
        if(!was[i]) continue;
        // DBG(endl << static_cast<char>(i + 'A') << " " << empty[i] << " " << reachable[i]);
        if(!productable[i] || !reachable[i]) {
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
