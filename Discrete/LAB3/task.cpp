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
#define FILENAME "nextpartition"
#endif
 
using namespace std;

char c1337c;

signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0); cout.tie(0);
    freopen(FILENAME".in", "r", stdin);
    freopen(FILENAME".out", "w", stdout);

    int n; cin >> n;
    cin >> c1337c;
    
    int t;
    vint a(0);
    while(cin >> t) {
        a.push_back(t);
        cin >> c1337c;
    }
    if(a.size() == 1) {
        cout << "No solution" << endl;
        return 0;
    }
    a[a.size() - 1]--;
    a[a.size() - 2]++;

    if(a[a.size() - 1] >= a[a.size() - 2]) {
        // a[i]++;
        // a[i + 1]--;
        cout << n << '=';
        cout << a[0];
        int s = a[0];
        int st = a[0];
        for(int j = 1; j < a.size() - 1; ++j) {
            cout << '+' << a[j];
            s+=a[j];
            st = a[j];
        }
        // cout << endl << st << ' ' << s << endl;
        s = n - s;
        while(st*2 <= s) {
            cout << '+' << st;
            s -= st;
        }
        if(s!=0) cout << '+' << s;
        cout << endl;
    } else {
        t = a[a.size() - 1];
        a.pop_back();
        a[a.size() - 1] += t;
        cout << n << '=';
        cout << a[0];
        for(int j = 1; j < a.size(); ++j) {
            cout << '+' << a[j];
        }

        cout << endl;
    }


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