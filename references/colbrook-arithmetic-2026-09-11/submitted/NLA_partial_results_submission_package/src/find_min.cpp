// Exact cofactor completion search for minimum positive sign-matrix permanents.
// C++17; no external arithmetic library required for orders <= 35.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <numeric>
#include <random>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
using namespace std;using i128=__int128_t;using u128=__uint128_t;using Matrix=vector<vector<int>>;
int g(int k){return k-(31-__builtin_clz((unsigned)(k+1)));}
vector<long long> cofactors_dp(const Matrix&a){
 int n=a[0].size();uint64_t N=1ULL<<n;vector<long long>d(N);d[0]=1;
 for(uint64_t s=1;s<N-1;s++){int k=__builtin_popcountll(s);i128 v=0;
  for(uint64_t z=s;z;z&=z-1){int j=__builtin_ctzll(z);v+=(i128)a[k-1][j]*d[s^(1ULL<<j)];}
  if(g(k)>g(k-1)){if(v%2)throw runtime_error("DP divisibility failure");v/=2;}
  if(v>numeric_limits<long long>::max()||v<numeric_limits<long long>::min())throw runtime_error("DP overflow");d[s]=(long long)v;
 }vector<long long>c(n);for(int j=0;j<n;j++)c[j]=d[(N-1)^(1ULL<<j)];return c;
}
vector<long long> cofactors_glynn(const Matrix&a){
 int n=a[0].size(),m=n-1;bool second=m%2;int h=second?m-1:m,offset=second?1:0;
 if(n<3||n>35)throw runtime_error("Glynn range is 3..35");if(second)for(int x:a[0])if(x!=1)throw runtime_error("first row must be positive");
 int t[40]={},sgn[40];for(int i=0;i<h;i++)sgn[i]=1;
 for(int j=0;j<n;j++){int z=0;for(int i=0;i<h;i++)z+=a[offset+i][j];t[j]=z/2;}
 // Unsigned wrap is intentional. The true final accumulator is per(minor)/2,
 // whose magnitude is <=34!/2<2^127. Thus centered recovery is exact.
 u128 sums[40]={},pre[41],der[41];int nz[40];uint64_t lim=1ULL<<(h-1);
 for(uint64_t step=0;step<lim;step++){
  if(step){int r=1+__builtin_ctzll(step),d=-sgn[r];sgn[r]=-sgn[r];for(int j=0;j<n;j++)t[j]+=d*a[offset+r][j];}
  int zeros=0,z0=-1,z1=-1,k=0;for(int j=0;j<n;j++)if(!t[j]){if(!zeros)z0=j;else if(zeros==1)z1=j;zeros++;}else nz[k++]=j;
  if(zeros>(second?2:1))continue;bool neg=step&1;
  if(zeros==(second?2:1)){
   u128 p=1;for(int i=0;i<k;i++)p*=(u128)(i128)t[nz[i]];
   if(neg)sums[z0]-=p;else sums[z0]+=p;if(second){if(neg)sums[z1]-=p;else sums[z1]+=p;}
  }else if(!second||zeros==1){
   pre[0]=1;for(int i=0;i<k;i++)pre[i+1]=pre[i]*(u128)(i128)t[nz[i]];u128 suffix=1,total=0;
   for(int i=k-1;i>=0;i--){u128 v=pre[i]*suffix;int j=nz[i];if(neg)sums[j]-=v;else sums[j]+=v;total+=v;suffix*=(u128)(i128)t[j];}
   if(second){if(neg)sums[z0]-=total;else sums[z0]+=total;}
  }else{
   pre[0]=1;der[0]=0;for(int j=0;j<n;j++){u128 q=(u128)(i128)t[j];der[j+1]=der[j]*q+pre[j];pre[j+1]=pre[j]*q;}
   u128 suffix=1,dsuffix=0;for(int j=n-1;j>=0;j--){u128 v=der[j]*suffix+pre[j]*dsuffix;if(neg)sums[j]-=v;else sums[j]+=v;u128 q=(u128)(i128)t[j];dsuffix=dsuffix*q+suffix;suffix*=q;}
  }
 }
 vector<long long>c(n);i128 scale=(i128)1<<(g(m)-1);
 for(int j=0;j<n;j++){u128 u=sums[j];i128 z=(u>>127)?-(i128)(~u)-1:(i128)u;if(z%scale)throw runtime_error("Glynn divisibility failure");z/=scale;if(z>numeric_limits<long long>::max()||z<numeric_limits<long long>::min())throw runtime_error("cofactor range exceeded");c[j]=(long long)z;}return c;
}
bool sign_solution(const vector<long long>&c,long long target,vector<int>&s){
 int n=c.size(),m=n/2;i128 bound=abs(target);for(auto x:c)bound+=4*(x<0?-(i128)x:(i128)x);if(bound>numeric_limits<long long>::max())throw runtime_error("sign solver range exceeded");
 vector<pair<long long,uint64_t>>left(1ULL<<m);long long v=0;for(int j=0;j<m;j++)v+=c[j];uint64_t mask=0;left[0]={v,0};
 for(uint64_t t=1;t<(1ULL<<m);t++){int j=__builtin_ctzll(t);v+=((mask>>j)&1)?2*c[j]:-2*c[j];mask^=1ULL<<j;left[t]={v,mask};}sort(left.begin(),left.end());v=0;for(int j=m;j<n;j++)v+=c[j];mask=0;
 for(uint64_t t=0;t<(1ULL<<(n-m));t++){if(t){int j=__builtin_ctzll(t);v+=((mask>>j)&1)?2*c[m+j]:-2*c[m+j];mask^=1ULL<<j;}
  auto it=lower_bound(left.begin(),left.end(),pair<long long,uint64_t>{target-v,0});if(it!=left.end()&&it->first==target-v){s.assign(n,1);for(int j=0;j<m;j++)if((it->second>>j)&1)s[j]=-1;for(int j=m;j<n;j++)if((mask>>(j-m))&1)s[j]=-1;return true;}
 }return false;
}
int main(int argc,char**argv){try{
 if(argc<4){cerr<<"usage: find_min n seed output_prefix [attempts=1] [skip=0] [glynn|dp]\n";return 2;}
 int n=stoi(argv[1]),attempts=argc>4?stoi(argv[4]):1,skip=argc>5?stoi(argv[5]):0;string method=argc>6?argv[6]:"glynn",prefix=argv[3];if(n<3||n>35||attempts<1||skip<0)throw runtime_error("invalid parameters");if(method=="dp"&&n>29)throw runtime_error("DP memory limit is n<=29");
 mt19937_64 rng(stoull(argv[2]));auto start=chrono::steady_clock::now();
 for(int attempt=1;attempt<=skip+attempts;attempt++){
  Matrix a(n-1,vector<int>(n));for(auto&r:a)for(auto&x:r)x=(rng()&1)?1:-1;for(int j=0;j<n;j++){int z=a[0][j];for(auto&r:a)r[j]*=z;}if(attempt<=skip)continue;
  auto c=method=="dp"?cofactors_dp(a):cofactors_glynn(a);vector<int>s;long long target=1LL<<(g(n)-g(n-1));
  cerr<<"n="<<n<<" attempt="<<attempt<<" method="<<method<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
  if(sign_solution(c,target,s)){
   a.push_back(s);ofstream out(prefix+".txt"),co(prefix+"_cofactors.txt");if(!out||!co)throw runtime_error("output could not be opened");out<<n<<" "<<(1ULL<<g(n))<<"\n";for(auto&r:a){for(int j=0;j<n;j++)out<<r[j]<<(j==n-1?'\n':' ');}co<<"scale "<<(1ULL<<g(n-1))<<"\n";for(auto z:c)co<<z<<"\n";
   cerr<<"FOUND n="<<n<<" permanent="<<(1ULL<<g(n))<<"\n";return 0;
  }
 }cerr<<"NO WITNESS\n";return 1;
}catch(const exception&e){cerr<<"ERROR: "<<e.what()<<"\n";return 2;}}
