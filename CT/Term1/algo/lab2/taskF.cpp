#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <cmath>

#define int long long

#define INF 1<<30

using namespace std;

vector<int> a;
vector<int> b;

int m = 0;

void push(int x) {
    b[m++] = x;
}

int pop() {
    return b[--m];
}

int top() {
    return b[m-1];
}

bool solve(bool release) {
    vector<int> t(a.size());
    for(int i = 0, ti = 0; i < a.size() - 1; ++i) {
        push(a[i]);
        if(release) cout << "push" << endl;
        while(m > 0 && top() < a[i + 1]) {
            t[ti++] = pop();
            if(release) cout << "pop" << endl;
        }
    }
    m = 0;
    b = vector<int>(b.size(), 0);
    for(int i = 1; i < t.size() - 1; ++i) {
        if(t[i-1] > t[i])
            return false;
    }
    return true;
}

signed main(){
    int n; cin >> n;
    a.resize(n + 1);
    b.resize(n + 1,0);
    a[n] = INF;
    for(int i = 0; i < n; ++i) {
        cin >> a[i];
    }
    if(!solve(false))
        cout << "impossible" << endl;
    else
        solve(true);
    return 0;
}
