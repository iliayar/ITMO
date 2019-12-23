#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <cmath>

#define int long long
#define vint vector<int>
#define ALL(a) a.begin(), a.end()

#define FILENAME "local"
 
#ifndef LOCAL
#define FILENAME "nextperm"
#endif
 
using namespace std;


signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0); cout.tie(0);
     
    freopen(FILENAME".in", "r", stdin);
    freopen(FILENAME".out", "w", stdout);

    int n; cin >> n;

    vint a(n);
    for(int i = 0; i < n; ++i) cin >> a[i];

    vint t(0);
    
    //PREV
    int i = a.size() - 1;
    while(i > 0 && a[i-1] < a[i]) {
        t.push_back(a[i]);
        i--;
    }
    if(i == 0) {
        for(int j = 0; j < n; ++j) cout << 0 << ' ';
    } else {
        t.push_back(a[i]);
        t.push_back(a[i-1]);
        int p = a[i-1];
        for(int j = 0; j < i - 1; ++j) {
            cout << a[j] << ' ';
        }
        sort(ALL(t));
        i = 0;
        while(t[++i] < p);
        int tp = t[i-1]; cout << tp << ' ';
        for(int j = t.size() - 1; j >= 0; --j) {
            if(t[j] != tp) cout << t[j] << ' ';
        }
    }
    cout << endl;
    //NEXT
    t.clear();
    i = a.size() - 1;
    while(i > 0 && a[i-1] > a[i]) {
        t.push_back(a[i]);
        i--;
    }
    if(i == 0) {
        for(int j = 0; j < n; ++j) cout << 0 << ' ';
    } else {
        t.push_back(a[i]);
        t.push_back(a[i-1]);
        int p = a[i-1];
        for(int j = 0; j < i - 1; ++j) {
            cout << a[j] << ' ';
        }
        sort(ALL(t));
        i = t.size();
        while(t[--i] > p);
        int tp = t[i+1]; cout << tp << ' ';
        for(int j = 0; j < t.size(); ++j) {
            if(t[j] != tp) cout << t[j] << ' ';
        }
    }
    return 0;
}