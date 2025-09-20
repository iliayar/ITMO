#include <cstdio>
#include <algorithm>
using namespace std;
int tot,pos[100010],dep[100010],b[100010],a[100010][2],f[100010][17];
void dfs(int x)
{
    pos[x]=++tot;
    for (int i=1;i<=16;i++)
        f[x][i]=f[f[x][i-1]][i-1];
    for (int i=b[x];i;i=a[i][1])
    {
        int y=a[i][0];
        dep[y]=dep[x]+1;
        f[y][0]=x;
        dfs(y);
    }
}
int c[100010];
inline bool cmp(int x,int y)
{
    return(pos[x]<pos[y]);
}
inline int lca(int x,int y)
{
    if (dep[x]<dep[y])
        swap(x,y);
    for (int i=16;i>=0;i--)
        if (dep[f[x][i]]>=dep[y])
            x=f[x][i];
    if (x==y)
        return(x);
    for (int i=16;i>=0;i--)
        if (f[x][i]!=f[y][i])
            x=f[x][i],y=f[y][i];
    return(f[x][0]);
}
inline int dist(int x,int y)
{
    return(dep[x]+dep[y]-2*dep[lca(x,y)]);
}
int main()
{
    int n,root;
    scanf("%d",&n);
    for (int i=1;i<=n;i++)
    {
        int x;
        scanf("%d",&x);
        if (x==-1)
            root=i;
        else
            a[i][0]=i,a[i][1]=b[x],b[x]=i;
    }
    dfs(root);
    int Q;
    scanf("%d",&Q);
    while (Q--)
    {
        int K;
        scanf("%d",&K);
        bool flag=false;
        for (int i=1;i<=K;i++)
        {
            scanf("%d",&c[i]);
            if (c[i]==root)
                flag=true;
        }
        if (!flag)
            c[++K]=root;
        sort(c+1,c+K+1,cmp);
        int ans=0;
        for (int i=2;i<=K;i++)
            ans+=dist(c[i-1],c[i]);
        ans+=dist(c[K],c[1]);
        printf("%d\n",ans/2+1);
    }
    return(0);
}
