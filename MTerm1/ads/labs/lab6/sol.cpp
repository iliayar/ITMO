#include "template.cpp"

struct S {
    int i;
    int j;
    int c;
};

//entry
void sol() {
    int n; cin >> n;
    vint a(n);
    for (int i = 0; i < n; ++i) {
        cin >> a[i];
    }

    int i = 0, j = 1;

    int s = 0;
    vector<S> p(n + 1, 0);
    for (int i = n - 1; ++i) {
        if (p[i + 1] > a[i]) {
            p[i] = p[i + 1] - a[i];
        } else {
            p[i] = a[i] - p[i + 1]
        }
        s += a[i];
    }

    vector<S> res;
    // while (i < n && j < n) {
    //     int c = min(a[i], a[j]);
    //     res.push_back({i, j, c});
    //     a[i] -= c;
    //     a[j] -= c;
    //
    //     while (a[i] == 0 && i < n) i++;
    //     while (a[j] == 0 && j < n) j++;
    //
    //     if (i == j) {
    //         j += 1;
    //     } else if (j < i) {
    //         swap(j, i);
    //     }
    // }
    for (int i = 0; i < n; ++i) {
        int j = i + 1;
        for (;j < n; ++j) {

        }
    }

    cout << res.size() << endl;
    for (int i = 0; i < res.size(); ++i) {
        cout << res[i].i + 1 << " " << res[i].j + 1 << " " << res[i].c << endl;
    }
}
