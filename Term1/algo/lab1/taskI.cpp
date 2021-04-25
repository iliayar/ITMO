#include <iostream>
//#include <bits/stdc++.h>
#include <vector>
#include <cmath>

#define int long long
#define double long double

using namespace std;

#define EPS 1e-6

double f(double x, double C) {
    return x*x + sqrt(x) - C;
}

double bs(double l, double r, double x, double C) {
    while(r - l > EPS) {
        double m = (r+l)/2;
        if(x < f(m,C)) {
            r = m;
        } else {
            l = m;
        }
    }
    return (l+r)/2;
}

signed main() {

    double C; cin >> C;

    printf("%Lf\n",bs(0,C,0,C));
    return 0;
}
