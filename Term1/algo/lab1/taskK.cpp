#include <iostream>
#include <vector>
#include <algorithm>

#define int long long
#define double long double 

#define DELTA 1e-6

using namespace std;


struct Item {
    int i;
    double k;
    int v;
    int w;
};

vector<Item> a;

int k, n;

bool comp1(Item a, Item b) {
    return a.k > b.k;
}
bool comp2(Item a, Item b) {
    return a.i < b.i;
}

bool check(double koef) {
    for(int i = 0; i < n; ++i) {
        a[i].k = 1.0*a[i].v*koef - 1.0*a[i].w;
    }
    sort(a.begin(),a.end(),comp1);
    double sum = 0;
    for(int i = 0; i < k; ++i) {
        sum += a[i].k;
    }
    return sum < 0;
}


signed main() {
    //ios_base::sync_with_stdio(0);
    //cin.tie(0); cout.tie(0);
    cin >> n >> k;
    a.resize(n);
    for(int i = 0; i < n; ++i) {
        scanf("%Ld %Ld",&a[i].v,&a[i].w);
        a[i].i = i + 1;
    }
    double l = 0, r = 1e+7;
    int j = 50;
    while(j > 0) {
        double m = (l+r)/2;
        if(check(m)) {
            l = m;
        } else {
            r = m;
        }
        j--;
    }
    sort(a.begin(),a.begin() + k,comp2);

    for(int i = 0; i < k; ++i)
        printf("%d\n",a[i].i);

    return 0;
}
