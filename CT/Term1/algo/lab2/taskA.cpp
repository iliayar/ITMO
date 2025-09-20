#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <cmath>

#define int long long

using namespace std;


int s = 0;
int smin = 1;

vector<int> a;
vector<int> amin;

void push(int n) {
    a[s++] = n;
    if(amin[smin-1] >= n)
        amin[smin++] = n;
}
int pop() {
    if(a[s-1] == amin[smin - 1]){
        smin--;
    }

    return a[--s];
}
int getMin() {
    return amin[smin-1];
}


signed main(){
    ios_base::sync_with_stdio(0);
    cin.tie(0); cout.tie(0);
    int n; cin >> n;
    a.resize(n);
    amin.resize(n);
    amin[0] =1e9 + 1;
    for(int i = 0; i < n; ++i) {
        int t; cin >> t;
        if(t == 1) {
            int b; cin >> b;
            push(b);
        } else if(t == 2) {
            pop();
        } else if(t == 3) {
            cout << getMin() << endl;
        }
    }
    return 0;
}
