#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <cmath>

#define int long long

#define FILENAME "local"

#ifndef LOCAL
#define FILENAME "vectors"
#endif

using namespace std;

vector<int> a;


int n;

int k = 0;

void gen(int i, bool log) {
	if(i == n) {
		if(!log) {
			k++;
			return;
		}
		for(int i = 0; i < n; ++i)
			cout << a[i];
		cout << endl;
		k++;
		return;
	}

	a[i] = 0;
	gen(i+1, log);
	if(a[i - 1] != 1) {
		a[i] = 1;
		gen(i+1, log);
	}
}

signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0); cout.tie(0);
    
    freopen(FILENAME".in", "r", stdin);
    freopen(FILENAME".out", "w", stdout);


    cin >> n;
    
	a.resize(n);

	a[0] = 0;
	gen(1, false);
	a[0] = 1;
	gen(1, false);
	cout << k << endl;
	a[0] = 0;
	gen(1, true);
	a[0] = 1;
	gen(1, true);
	return 0;
}
