#include <iostream>
#include <vector>
#include <algorithm>
#ifdef LOCAL
#include <chrono>
#endif

using namespace std;

#define ON 1
#define OFF 0

#ifdef LOCAL
#define FILE_OUTPUT ON
#define FILENAME "local"
#else
#define FILE_OUTPUT OFF
#define FILENAME "local"
#endif

#define int long long

//##################CODE BEGIN########################

#define dbg cout << "DBG: "

//entry
void sol() {

    const int MOD1 = 16;
    const int MOD2 = 30;

    int n, x, y, a0;
    cin >> n >> x >> y >> a0;

    int m, z, t, b0;
    cin >> m >> z >> t >> b0;

    vector<int> sum(n, 0);
    int prev = a0;
    for(int i = 0; i < n; ++i) {
        if(i > 0) {
            sum[i] = sum[i-1];
        }
        sum[i] += prev;
        prev = (x*prev + y) & ~(~0 << MOD1);
    }

    prev = b0;
    int res = 0;
    for(int i = 0; i < m; ++i) {
        int t1 = prev % n;
        prev = (z*prev + t) & ~(~0 << MOD2);
        if(prev < 0) prev += 1 << MOD2;
        int t2 = prev % n;
        prev = (z*prev + t) & ~(~0 << MOD2);
        if(prev < 0) prev += 1 << MOD2;

        // dbg << t1 << " " << t2 << endl;


        int l = min(t1,t2);
        int r = max(t1,t2);
        // dbg << sum[r] - (l == 0 ? 0 : sum[l-1]) << endl;
        res += sum[r] - (l == 0 ? 0 : sum[l-1]);
    }

    cout << res << endl;


}
//####################CODE END#######################
signed main() {
    #if FILE_OUTPUT == ON
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
