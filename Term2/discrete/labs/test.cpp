#include <iostream>
#include <fstream>
#include <vector>
#include <map>
#include <cassert>
#include <set>
#include <string>

using namespace std;

struct Grammar 
{
    int start;
    vector<pair<int, vector<int> > > rules;
    int nterms;

    Grammar(int start, vector<pair<int, vector<int> > > rules):
        start(start),
        rules(rules)
    {
        nterms = nonTerminalsCnt2();
    }
    
    int nonTerminalsCnt2() const 
    {
        int mx = -1;
        for (int i = 0; i < rules.size(); i++)
        {
            mx = max(mx, rules[i].first);
            for (int j = 0; j < rules[i].second.size(); j++)
            {
                int to = rules[i].second[j];
                mx = max(mx, to);
            }
        }
        return max(mx, start) + 1;
    }
};

ostream& operator<<(ostream& out, const Grammar& g)
{
    out << g.rules.size() << " " << g.start << "\n";
    for (int i = 0; i < g.rules.size(); i++)
    {
        out << g.rules[i].first << " -> ";
        for (int j = 0; j < g.rules[i].second.size(); j++)
            out << g.rules[i].second[j] << " ";
        out << "\n";
    }
    out << "\n";
    return out;
}

template<typename T>
ostream& operator<<(ostream& out, const set<T>& s)
{
    out << "{";
    for (typename set<T>::const_iterator it = s.begin(); it != s.end(); it++)
        out << *it << ", ";
    out << "}";
    return out;
}

int get(int& used, map<int,int>& m, int i)
{
    if (m.count(i))
        return m[i];
    return m[i] = used++;
}

Grammar reduceNonTerminals(const Grammar& g)
{
    map<int, int> m;
    vector<pair<int, vector<int> > > newRules;
    int used = 0;
    for (int i = 0; i < g.rules.size(); i++)
    {
        int from = get(used, m, g.rules[i].first);
        vector<int> to;
        for (int j = 0; j < g.rules[i].second.size(); j++)
        {
            int t = g.rules[i].second[j];
            if (t < 0) 
                to.push_back(t);
            else
                to.push_back(get(used, m, t));
        }
        newRules.push_back(make_pair(from, to));
    }
    return Grammar(get(used,m,g.start), newRules);
}

set<int> epsilonGeneratingRules(const Grammar& g)
{
    set<int> rules;
    for (int i = 0; i < g.rules.size(); i++)
    {
        if (g.rules[i].second.size() == 0)
        {
            rules.insert(g.rules[i].first);
        }
    }
    bool changes = true;
    while (changes)
    {
        changes = false;
        for (int i = 0; i < g.rules.size(); i++)
        {
            if (rules.count(g.rules[i].first))
                continue;
            bool all = true;
            for (int j = 0; j < g.rules[i].second.size(); j++)
            {
                int to = g.rules[i].second[j];
                if (!rules.count(to))
                    all = false;
            }
            if (all)
            {
                rules.insert(g.rules[i].first);
                changes = true;
            }
        }
    }
    return rules;
}

void generateNewRulesToEpsCloj(int from, const set<int> eps, vector<pair<int, vector<int> > >& res, vector<int> pref, vector<int> rest)
{
    if (rest.size() == 0)
    {
        res.push_back(make_pair(from, pref));
        return;
    }
    vector<int> newPref = pref;
    newPref.push_back(rest[0]);
    vector<int> newRest;
    for (int i = 1; i < rest.size(); i++)
        newRest.push_back(rest[i]);
    if (eps.count(rest[0]))
    {
        generateNewRulesToEpsCloj(from, eps, res, pref, newRest);
    }
    generateNewRulesToEpsCloj(from, eps, res, newPref, newRest);
}

Grammar removeEpsilonRules(const Grammar& g)
{
    set<int> eps = epsilonGeneratingRules(g);
    vector<pair<int, vector<int> > > newRules2;
    for (int i = 0; i < g.rules.size(); i++)
    {
        int from = g.rules[i].first;
        generateNewRulesToEpsCloj(from, eps, newRules2, vector<int>(), g.rules[i].second);
    }
    vector<pair<int, vector<int> > > newRules;
    for (int i = 0; i < newRules2.size(); i++)
    {
        if (newRules2[i].second.size() != 0)
            newRules.push_back(newRules2[i]);
    }
    return Grammar(g.start, newRules);
}

Grammar removeTerminalsFromRHS(const Grammar& g)
{
    int used = g.nterms;
    map<int, int> terms;
    vector<pair<int, vector<int> > > newRules;
    for (int i = 0; i < g.rules.size(); i++)
    {
        int from = g.rules[i].first;
        vector<int> newTo;
        for (int j = 0; j < g.rules[i].second.size(); j++)
        {
            int to = g.rules[i].second[j];
            if (to < 0)
            {
                if (terms.count(to))
                {
                    newTo.push_back(terms[to]);
                } else {
                    terms[to] = used++;
                    newTo.push_back(terms[to]);
                    vector<int> newRHS;
                    newRHS.push_back(to);
                    newRules.push_back(make_pair(terms[to], newRHS));
                }
            } else {
                newTo.push_back(to);
            }
        }
        newRules.push_back(make_pair(from, newTo));
    }
    return Grammar(g.start, newRules);
}

Grammar removeChainRules(const Grammar& g)
{
    vector<vector<int> > imp(g.nterms, vector<int>(g.nterms, 0));
    for (int i = 0; i < g.rules.size(); i++)
    {
        int from = g.rules[i].first;
        if (g.rules[i].second.size() == 1)
        {
            int to = g.rules[i].second[0];
            if (to < 0)
                continue;
            imp[from][to] = 1;
        }
    }
    for (int k = 0; k < g.nterms; k++)
        for (int i = 0; i < g.nterms; i++)
            for (int j = 0; j < g.nterms; j++)
                imp[i][j] |= imp[i][k] && imp[k][j];
    vector<pair<int, vector<int> > > newRules;
    for (int i = 0; i < g.rules.size(); i++)
    {
        int from = g.rules[i].first;
        if (g.rules[i].second.size() == 1)
        {
            int to = g.rules[i].second[0];
            if (to < 0)
            {
                for (int j = 0; j < g.nterms; j++)
                {
                    if (from == j)
                        continue;
                    if (imp[j][from])
                    {
                        vector<int> newRHS;
                        newRHS.push_back(to);
                        newRules.push_back(make_pair(j, newRHS));
                    }
                }
                newRules.push_back(g.rules[i]);
            }
        } else {
            for (int j = 0; j < g.nterms; j++)
            {
                if (from == j)
                    continue;
                if (imp[j][from])
                {
                    newRules.push_back(make_pair(j, g.rules[i].second));
                }
            }
            newRules.push_back(g.rules[i]);
        }
    }
    return Grammar(g.start, newRules);
}

Grammar removeLongRules(const Grammar& g)
{
    int used = g.nterms;
    vector<pair<int, vector<int> > > newRules;
    for (int i = 0; i < g.rules.size(); i++)
    {
        if (g.rules[i].second.size() > 2)
        {
            int last = g.rules[i].first;
            // S -> ABCDE ===> S -> AB' B' -> BC', C' -> CD', D' -> DE
            int sz = g.rules[i].second.size();
            for (int j = 0; j < sz - 2; j++)
            {
                vector<int> newRHS;
                newRHS.push_back(g.rules[i].second[j]);
                newRHS.push_back(used);
                newRules.push_back(make_pair(last, newRHS));
                last = used++;
            }
            vector<int> newRHS;
            newRHS.push_back(g.rules[i].second[sz-2]);
            newRHS.push_back(g.rules[i].second[sz-1]);
            newRules.push_back(make_pair(last, newRHS));
        } else {
            newRules.push_back(g.rules[i]);
        }
    }
    return Grammar(g.start, newRules);
}

bool accepts(const Grammar& g, const string& ss)
{
    int m = ss.size();
    vector<int> s;
    for (int i = 0; i < m; i++)
        s.push_back(ss[i]);
        
    vector<vector<vector<int> > > dp(g.nterms, vector<vector<int> >(m + 1, vector<int>(m + 1, 0)));
    for (int i = 0; i < m; i++)
    {
        for (int j = 0; j < g.rules.size(); j++)
        {
            if (g.rules[j].second.size() == 1)
            {
                int from = g.rules[j].first;
                int to = g.rules[j].second[0];
                if (s[i] == -to)
                    dp[from][i][i+1] = 1;
            }
        }
    }
    vector<int> from;
    vector<int> to1;
    vector<int> to2;

    for (int i = 0; i < g.rules.size(); i++)
    {
        if (g.rules[i].second.size() == 2)
        {
            from.push_back(g.rules[i].first);
            to1.push_back(g.rules[i].second[0]);
            to2.push_back(g.rules[i].second[1]);
        }
    }

    for (int length = 2; length <= m; length++)
    {
        for (int start = 0; start + length <= m; start++)
        {
            for (int rule = 0; rule < from.size(); rule++)
            {
                int cnt = 0;
                for (int drop = 1; drop < length && !cnt; drop++)
                {
                    cnt |= dp[to1[rule]][start][start + drop] && dp[to2[rule]][start + drop][start + length];
                }
                dp[from[rule]][start][start + length] |= cnt;
            }
        }
    }
    
    
    return dp[g.start][0][m];
}

bool isLower(char ch)
{   return 'a' <= ch && ch <= 'z';}

int main() 
{
    ifstream in("local.in");
    ofstream out("local.out");
    int n;
    char st;
    in >> n >> st;
    vector<pair<int, vector<int> > > rules;
    string s;
    getline(in, s);
    for (int i = 0; i < n; i++)
    {
        getline(in, s);
        int from = s[0];
        vector<int> to;
        for (int j = 5; j < s.size(); j++)
        {
            if (isLower(s[j]))
                to.push_back(-s[j]);
            else
                to.push_back(s[j]);
        }
        rules.push_back(make_pair(from, to));
    }
    Grammar g(st, rules);
    cerr << "initial " << g;
    g = reduceNonTerminals(g);
    cerr << "smallIDs " << g;
    g = removeEpsilonRules(g);
    cerr << "without eps " << g;
    g = removeTerminalsFromRHS(g);
    cerr << "without terminals RHS " << g;
    g = removeChainRules(g);
    cerr << "without chain rules " << g;
    g = removeLongRules(g);
    cerr << "without long rules " << g;
    getline(in, s);
    if (accepts(g, s))
        out << "yes\n";
    else
        out << "no\n";
}
