#include <iostream>
#include <algorithm>
#include <cmath>
#include <vector>
#include <string>

using namespace std;

vector<vector<bool>> v;
vector<bool> was;
int n, m;


void renewWas() {
    for(int i = 0; i < 2*n; ++i) {
        was[i] = false;
    }
}

bool find (int st, int w) {
    if(was[w])
        return false;
    was[w] = true;
    if(st == w - n || st - n == w) {
        return true;
    }
    bool res = false;
    for(int i = 0; i < 2*n; ++i) {
        if(v[w][i]) {
            res = res || find(st,i);
        }
    }
    return res;
}

signed main() {
    cin >> n >> m;

    v.resize(2*n,vector<bool>(2*n));
    was.resize(2*n,false);

    for(int i = 0; i < m; ++i) {
        int a, b; cin >> a >> b;
        int na = -a, nb = -b;
        a = a < 0 ? n-a : a;
        b = b < 0 ? n-b : b;
        na = na < 0 ? n-na : na;
        nb = nb < 0 ? n-nb : nb;
        a--; b--; na--; nb--;
        v[na][b] = true;
        v[nb][a] = true;
    }
    for(int i = 0; i < n; ++i) {
        bool a = find(i,i); renewWas();
        bool b = find(n+i,n+i); renewWas();
        if(a && b) {
            cout << "YES" << endl;
            return 0;
        }
    }
    cout << "NO" << endl;
    return 0;
}
