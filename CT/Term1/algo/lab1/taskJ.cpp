#include <iostream>
//#include <bits/stdc++.h>
#include <vector>
#include <cmath>

#define int long long
#define double long double

using namespace std;

#define EPS 1e-9

double vp,vf,a;
 
double a1,a2;
 
double t(double x) {
    return (sqrt(a1 + x*x)*vf + sqrt(a2 + (1-x)*(1-x))*vp)/(vp*vf);
}

signed main() {

    cin >> vp >> vf >> a;
    a1 = (1-a)*(1-a);
    a2 = a*a;
    double l = 0;
    double r = 1;
    while(r-l >= EPS) {
        double m1 = l + (r-l)/100;
        double m2 = r - (r-l)/100;
        if(t(m1) > t(m2)) {
            l = m1;
        } else {
            r = m2;
        }
    }
    printf("%Lf\n",r);

    return 0;
}
