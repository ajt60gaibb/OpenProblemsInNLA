// Exhaustive absolute permanent ranges of sign matrices, for n<=9.
// upper: normalized triangular-negative matrices (all are represented).
// full: normalized matrices, with sorted remaining rows.
// canonical: additionally sort columns lexicographically.
// orderly: necessary prefix conditions for a lexicographically least orbit representative.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
using namespace std;
struct Search{
 using Bits=array<uint64_t,8>;int n,N,full;string mode,prefix;vector<vector<int>>subsets,a;vector<vector<long long>>dp;vector<char>seen;
 vector<vector<pair<int,int>>>transitions;vector<vector<Bits>>allowed_after;uint64_t count=0,found=0;ofstream witnesses;chrono::steady_clock::time_point start;
 Search(int nn,string mm,string pp):n(nn),N(1<<n),full(N-1),mode(mm),prefix(pp){
  subsets.resize(n+1);for(int s=0;s<N;s++)subsets[__builtin_popcount((unsigned)s)].push_back(s);dp.assign(n+1,vector<long long>(N));dp[0][0]=1;a.assign(n,vector<int>(n,1));int f=1;for(int j=2;j<=n;j++)f*=j;seen.assign(f+1,0);witnesses.open(prefix+"_witnesses.txt");if(!witnesses)throw runtime_error("cannot open witnesses");start=chrono::steady_clock::now();
  if(mode!="canonical"&&mode!="orderly")return;int m=n-1;transitions.resize(1<<max(0,m-1));
  for(int cuts=0;cuts<(int)transitions.size();cuts++)for(int mask=0;mask<(1<<m);mask++){
   bool ok=true;int next=cuts,lo=0;for(int hi=0;hi<m;hi++)if(hi==m-1||(cuts&(1<<hi))){int len=hi-lo+1,part=(mask>>lo)&((1<<len)-1);if(part&(part+1)){ok=false;break;}int ones=__builtin_popcount((unsigned)part);if(ones&&ones<len)next|=1<<(lo+ones-1);lo=hi+1;}if(ok)transitions[cuts].push_back({mask,next});
  }
  if(mode!="orderly")return;allowed_after.resize(transitions.size(),vector<Bits>(1<<m));
  for(int cuts=0;cuts<(int)transitions.size();cuts++)for(auto [mask,next]:transitions[cuts]){
   auto&allow=allowed_after[cuts][mask];for(int candidate=0;candidate<(1<<m);candidate++){
    int sorted=0,lo=0;for(int hi=0;hi<m;hi++)if(hi==m-1||(cuts&(1<<hi))){int len=hi-lo+1,p=(candidate>>lo)&((1<<len)-1),ones=__builtin_popcount((unsigned)p);sorted|=((1<<ones)-1)<<lo;lo=hi+1;}if(sorted>=mask)allow[candidate>>6]|=1ULL<<(candidate&63);
   }
  }
 }
 void record(long long val){count++;val=abs(val);if(seen[val])return;seen[val]=1;found++;witnesses<<val;for(auto&r:a){witnesses<<" ";for(int x:r)witnesses<<(x>0?'+':'-');}witnesses<<endl;}
 void upper(int i){int k=n-i,old=k-1;
  if(i==0){long long per=0;for(int j=0;j<n;j++)per+=dp[old][full^(1<<j)];fill(a[0].begin(),a[0].end(),1);record(per);for(int t=1;t<(1<<(n-1));t++){int j=1+__builtin_ctz((unsigned)t);per-=2*a[0][j]*dp[old][full^(1<<j)];a[0][j]=-a[0][j];record(per);}return;}
  fill(a[i].begin(),a[i].end(),1);for(int s:subsets[k]){long long v=0;for(int z=s;z;z&=z-1){int b=z&-z;v+=dp[old][s^b];}dp[k][s]=v;}upper(i-1);
  for(int t=1;t<(1<<(n-i));t++){int j=i+__builtin_ctz((unsigned)t),b=1<<j,delta=-2*a[i][j];a[i][j]=-a[i][j];for(int s:subsets[k])if(s&b)dp[k][s]+=delta*dp[old][s^b];upper(i-1);}
 }
 void putrow(int i,int mask){a[i][0]=1;for(int j=1;j<n;j++)a[i][j]=((mask>>(j-1))&1)?-1:1;int k=i+1;for(int s:subsets[k]){long long v=0;for(int z=s;z;z&=z-1){int j=__builtin_ctz((unsigned)z);v+=a[i][j]*dp[k-1][s^(1<<j)];}dp[k][s]=v;}}
 void unrestricted(int i,int least){if(i==n){record(dp[n][full]);return;}for(int mask=least;mask<(1<<(n-1));mask++){putrow(i,mask);unrestricted(i+1,mask);}}
 void canonical(int i,int least,int cuts){if(i==n){record(dp[n][full]);return;}for(auto[mask,next]:transitions[cuts])if(mask>=least){putrow(i,mask);canonical(i+1,mask,next);}}
 void orderly(int i,int cuts,Bits allowed){if(i==n){record(dp[n][full]);return;}for(auto[mask,next]:transitions[cuts]){
  if(!((allowed[mask>>6]>>(mask&63))&1))continue;Bits future;for(int j=0;j<8;j++)future[j]=allowed[j]&allowed_after[cuts][mask][j];putrow(i,mask);orderly(i+1,next,future);
 }}
 void run(){if(n==1)record(1);else{for(int j=0;j<n;j++)dp[1][1<<j]=1;if(mode=="upper")upper(n-2);else if(mode=="full")unrestricted(1,0);else if(mode=="canonical")canonical(1,0,0);else if(mode=="orderly"){Bits b;b.fill(~0ULL);orderly(1,0,b);}else throw runtime_error("unknown mode");}
  ofstream out(prefix+"_spectrum.txt");if(!out)throw runtime_error("cannot open spectrum");for(size_t v=0;v<seen.size();v++)if(seen[v])out<<v<<"\n";
  cerr<<"mode="<<mode<<" n="<<n<<" matrices="<<count<<" absolute_values="<<found<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
 }
};
int main(int argc,char**argv){try{if(argc!=4){cerr<<"usage: spectrum n upper|full|canonical|orderly output_prefix\n";return 2;}int n=stoi(argv[1]);if(n<1||n>9)throw runtime_error("order must be 1..9");Search(n,argv[2],argv[3]).run();return 0;}catch(const exception&e){cerr<<"ERROR: "<<e.what()<<"\n";return 2;}}
