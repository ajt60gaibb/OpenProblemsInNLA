// Full-matrix exact verifier, independent of the cofactor search.
// Transpose input; compute per(A)/2 modulo 2^128 and 2^61-1.
// The combined modulus exceeds n!/2 + |claim|/2 for supported orders.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>
#include <boost/multiprecision/cpp_int.hpp>
using namespace std;using u128=__uint128_t;using i128=__int128_t;using boost::multiprecision::cpp_int;
constexpr uint64_t P=(1ULL<<61)-1;
uint64_t addmod(uint64_t x,uint64_t y){uint64_t z=x+y;return z>=P?z-P:z;}
uint64_t submod(uint64_t x,uint64_t y){return x>=y?x-y:x+P-y;}
uint64_t mulsmall(uint64_t x,int y){unsigned a=y<0?-y:y;u128 z=(u128)x*a;uint64_t r=(uint64_t)(z&P)+(uint64_t)(z>>61);if(r>=P)r-=P;return y<0&&r?P-r:r;}
struct Residue{u128 low=0;uint64_t prime=0,terms=0;};
Residue calculate(const vector<vector<int>>&a,uint64_t begin,uint64_t end){
 int n=a.size();bool odd=n%2;int h=odd?n-1:n,off=odd?1:0;vector<int>sgn(h,1),t(n);uint64_t gray=begin^(begin>>1);
 for(int r=1;r<h;r++)if((gray>>(r-1))&1)sgn[r]=-1;for(int j=0;j<n;j++){int s=0;for(int r=0;r<h;r++)s+=sgn[r]*a[off+r][j];t[j]=s/2;}
 Residue out;
 for(uint64_t step=begin;step<end;step++){
  if(step!=begin){int r=1+__builtin_ctzll(step),d=-sgn[r];sgn[r]=-sgn[r];for(int j=0;j<n;j++)t[j]+=d*a[off+r][j];}
  int zeros=0;for(int x:t)if(!x)zeros++;if(zeros>(odd?1:0))continue;
  u128 product=1,derivative=0;uint64_t prodp=1,derp=0;
  for(int j=0;j<n;j++){u128 tj=(u128)(i128)t[j];if(odd){derivative=derivative*tj+(u128)(i128)a[0][j]*product;derp=addmod(mulsmall(derp,t[j]),mulsmall(prodp,a[0][j]));}product*=tj;prodp=mulsmall(prodp,t[j]);}
  u128 v=odd?derivative:product;uint64_t vp=odd?derp:prodp;if(step&1){out.low-=v;out.prime=submod(out.prime,vp);}else{out.low+=v;out.prime=addmod(out.prime,vp);}out.terms++;
 }return out;
}
string hex128(u128 x){const char*d="0123456789abcdef";string s(32,'0');for(int j=31;j>=0;j--){s[j]=d[x&15];x>>=4;}return s;}
int main(int argc,char**argv){try{
 if(argc<2){cerr<<"usage: verify_permanent MATRIX_FILE [THREADS=1]\n";return 2;}auto start=chrono::steady_clock::now();ifstream in(argv[1]);if(!in)throw runtime_error("cannot open matrix");int n;long long claim;in>>n>>claim;if(!in||n<1||n>40)throw runtime_error("order must be 1..40");
 vector<vector<int>>a(n,vector<int>(n));for(int i=0;i<n;i++)for(int j=0;j<n;j++){int x;in>>x;if(!in||(x!=1&&x!=-1))throw runtime_error("invalid sign entry");a[j][i]=x;}string excess;if(in>>excess)throw runtime_error("trailing data");
 if(n==1){if(a[0][0]!=claim)throw runtime_error("wrong permanent");cout<<"PASS n=1 permanent="<<claim<<"\n";return 0;}if(claim%2)throw runtime_error("odd claim for order >=2");
 cpp_int f=1;for(int j=2;j<=n;j++)f*=j;cpp_int modulus=(cpp_int(1)<<128)*P;cpp_int absclaim=claim;if(absclaim<0)absclaim=-absclaim;if(modulus<=f/2+absclaim/2)throw runtime_error("CRT uniqueness bound failed");
 int threads=argc>2?stoi(argv[2]):1;if(threads<1||threads>64)throw runtime_error("invalid thread count");int h=n%2?n-1:n;uint64_t states=1ULL<<(h-1);threads=min<uint64_t>(threads,states);vector<Residue>parts(threads);vector<thread>jobs;
 for(int k=0;k<threads;k++)jobs.emplace_back([&,k](){parts[k]=calculate(a,states*k/threads,states*(k+1)/threads);});for(auto&job:jobs)job.join();Residue total;for(auto r:parts){total.low+=r.low;total.prime=addmod(total.prime,r.prime);total.terms+=r.terms;}
 i128 want=claim/2;uint64_t wp=want<0?P-((uint64_t)(-want)%P):(uint64_t)want%P;if(wp==P)wp=0;bool ok=total.low==(u128)want&&total.prime==wp;
 cout<<(ok?"PASS":"FAIL")<<" n="<<n<<" permanent="<<claim<<" half_mod2_128=0x"<<hex128(total.low)<<" half_mod2_61_minus1="<<total.prime<<" states="<<states<<" nonzero_candidates="<<total.terms<<" threads="<<threads<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";return ok?0:1;
}catch(const exception&e){cerr<<"ERROR: "<<e.what()<<"\n";return 2;}}
