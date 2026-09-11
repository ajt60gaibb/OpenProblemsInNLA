// Exhaustive branch-and-bound inclusion check: |per(Omega_n)| subset of S.
// S must separately be certified by explicit U_n witnesses.
// With k rows fixed, every completion has |per(A)| <=
// (n-k)! * sum_{|I|=k} |per(prefix[:,I])|.
// The universal divisor q(n) permits a whole branch to be certified whenever
// all multiples of q(n) from 0 to this bound are present in S.
#define main spectrum_program_main
#include "spectrum.cpp"
#undef main
#include <numeric>
struct RangeCheck:Search{
 vector<char>allowed;long long q=0,central=-1;long long factorial[11];
 uint64_t nodes=0,pruned=0,leaves=0;bool failure=false,collect=false;
 RangeCheck(int nn,string input,string output):Search(nn,"orderly",output){
  allowed.assign(seen.size(),0);ifstream in(input);if(!in)throw runtime_error("cannot read allowed range");long long x;
  q=1LL<<(n-(31-__builtin_clz((unsigned)(n+1))));
  while(in>>x){if(x<0||x>=(long long)allowed.size()||x%q)throw runtime_error("invalid allowed permanent");allowed[x]=1;}
  if(!in.eof())throw runtime_error("malformed allowed range");
  central=-q;while(central+q<(long long)allowed.size()&&allowed[central+q])central+=q;
  factorial[0]=1;for(int j=1;j<=n;j++)factorial[j]=factorial[j-1]*j;
 }
 bool covered(int k){
  if(central<0||k<n-4)return false;
  long long sum=0;for(int s:subsets[k]){sum+=abs(dp[k][s]);if(sum*factorial[n-k]>central)return false;}
  return true;
 }
 void check(int i,int cuts,Bits possible){
  nodes++;if(covered(i)){pruned++;return;}
  if(i==n){
   leaves++;long long value=abs(dp[n][full]);if(!allowed[value]){
    failure=true;if(!seen[value]){record(dp[n][full]);ofstream out(prefix+"_outside.txt");out<<n<<" "<<dp[n][full]<<"\n";for(auto&r:a){for(int j=0;j<n;j++)out<<r[j]<<(j==n-1?'\n':' ');}
    cerr<<"OUTSIDE n="<<n<<" absolute_permanent="<<value<<"\n";}
   }return;
  }
  for(auto[mask,next]:transitions[cuts]){
   if(!((possible[mask>>6]>>(mask&63))&1))continue;
   Bits future;for(int j=0;j<8;j++)future[j]=possible[j]&allowed_after[cuts][mask][j];putrow(i,mask);check(i+1,next,future);if(failure&&!collect)return;
  }
 }
 int run_check(){
  if(n==1){failure=!allowed[1];}else{for(int j=0;j<n;j++)dp[1][1<<j]=1;Bits all;all.fill(~0ULL);check(1,0,all);}
  cerr<<(failure?"FAIL":"PASS")<<" RANGE n="<<n<<" allowed_values="<<accumulate(allowed.begin(),allowed.end(),0ULL)<<" divisor="<<q<<" central_end="<<central<<" visited_nodes="<<nodes<<" certified_branches="<<pruned<<" uncovered_values="<<found<<" explicit_leaves="<<leaves<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
  return failure?1:0;
 }
};
int main(int argc,char**argv){try{if(argc<4||argc>5){cerr<<"usage: check_range n allowed_spectrum output_prefix [--collect]\n";return 2;}int n=stoi(argv[1]);if(n<1||n>10)throw runtime_error("range 1..10");RangeCheck check(n,argv[2],argv[3]);if(argc==5){if(string(argv[4])!="--collect")throw runtime_error("unknown option");check.collect=true;}return check.run_check();}catch(const exception&e){cerr<<"ERROR: "<<e.what()<<"\n";return 2;}}
