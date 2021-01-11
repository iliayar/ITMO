#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <algorithm>
#include <cmath>
 
#define int long long
 
using namespace std;
 
class BinArray {
    unsigned int number;
 
public:
    BinArray() {
        BinArray(0);
    }
 
    BinArray(unsigned int number) {
        this->number = number;
    }
 
    static BinArray fromString(const string& strNumber) {
        unsigned int number = 0;
        for(int i = 0; i < strNumber.length(); ++i) {
            number += ((strNumber[i] - '0') << i);
        }
        return BinArray(number);
    }
     
    static BinArray fromReverseString(const string& strNumber) {
        unsigned int number = 0;
        for(int i = 0; i < strNumber.length(); ++i) {
            number = number*2 + (strNumber[i] - '0');
        }
        return BinArray(number);
    }
 
    static BinArray fromVector(const vector<bool>& strVector) {
        unsigned int number = 0;
        for(int i = 0; i < strVector.size(); ++i) {
            number += strVector[i] << i;
        }
        return BinArray(number);
    }
 
    static BinArray fromReverseVector(const vector<bool>& strVector) {
        unsigned int number = 0;
        for(int i = 0; i < strVector.size(); ++i) {
            number = number*2 + strVector[i];
        }
        return BinArray(number);
    }
 
    void set(int i, bool val) {
        if(val == 0) {
            this->number = this->number & ~(1 << i);
        } else {
            this->number = this->number | (1 << i);
        }
    }
 
    bool operator [](int i) const {
        return (bool)(1 & (number >> i));
    }
 
    BinArray operator &(unsigned int a) const {
        return BinArray(this->number & a);
    }
 
    BinArray operator |(unsigned int a) const {
        return BinArray(this->number | a);
    }
 
    BinArray operator ^(unsigned int a) const {
        return BinArray(this->number ^ a);
    }
 
    unsigned int value() {
        return this->number;
    }
    unsigned int revValue() {
        int number = this->number;
        int res = 0;
        while(number > 0) {
            res = res + number%2;
            number /= 2;
        }
        return res;
    }
 
 
    BinArray operator ++(signed i) {
        this->number++;
        return *this;
    }
 
    bool operator <(int n) const {
        return this->number < n;
    }
 
    string toString(int n) {
        string res = "";
        int number = this->number;
        for(int i = 0; i < n; ++i) {
            res += to_string(number%2);
            number /= 2;
        }
        return res;
    }
 
};
 
vector<BinArray> a;
 
string buildExprSDNF(BinArray line) {
    string res = "";
    res += 40;
    for(int i = 0; i < a.size(); ++i) {
        res += 40;
        if(line[i] == 0)
            res += 126;
        res += to_string(i+1);
        res += 41;
        if(i != a.size() - 1) {
            res += 38;
        }
    }
    res += 41;
    return res;
}
 
string buildExprSKNF(BinArray line) {
    string res = "";
    res += 40;
    for(int i = 0; i < a.size(); ++i) {
        res += 40;
        if(line[i] == 1)
            res += 126;
        res += to_string(i+1);
        res += 41;
        if(i != a.size() - 1) {
            res += 124;
        }
    }
    res += 41;
    return res;
}
 
signed main() {
    int n; cin >> n;
    a.resize(n);
    int maxP = 0;
    for(int i = 0; i < n; ++i) {
        unsigned int t; cin >> t;
        a[i] = BinArray(t);
        int c = 0; while(t >>= 1) c++;
        maxP = max(maxP,c);
    }
    unsigned int t; cin >> t;
    BinArray s(t);
    int c = 0; while(t >>= 1) c++;
    maxP = max(maxP,c);
 
    BinArray was(0);
    BinArray table(0);
 
    for(int i = 0; i <= maxP + 1; ++i) {
        BinArray c(0);
        for(int j = 0; j < n; ++j) {
            c.set(j,a[j][i]);
        }
        if(was[c.value()] && (table[c.value()] != s[i])) {
            cout << "Impossible" << endl;
            return 0;
        }
        was.set(c.value(), 1);
        table.set(c.value(),s[i]);
    }
 
    string res = "";
    bool flag = false;
    for(int i = 0; i < (1 << n); ++i) {
        if(table[i]) {
            if(flag)
                res += 124;
            res += buildExprSDNF(i);
            flag = true;
        }
    }
    if(res.length() == 0) {
        res = "";
        bool flag = false;
        for(int i = 0; i < (1 << n); ++i) {
            if(!table[i]) {
                if(flag)
                    res += 38;
                res += buildExprSKNF(i);
                flag = true;
            }
        }
    }
    cout << res << endl;
    return 0;
}
