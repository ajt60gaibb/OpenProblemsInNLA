// Generate explicit U_n witnesses by bordering supplied U_{n-1} witnesses.
#define main spectrum_program_main
#include "spectrum.cpp"
#undef main
#include <sstream>
int main(int argc,char**argv){try{
 if(argc!=4){cerr<<"usage: extend_upper n parent_witnesses output_prefix\n";return 2;}int n=stoi(argv[1]);if(n<2||n>10)throw runtime_error("n must be 2..10");Search s(n,"upper",argv[3]);ifstream in(argv[2]);if(!in)throw runtime_error("cannot read witnesses");string line;int parents=0;
 while(getline(in,line)){
  if(line.empty())continue;istringstream rowin(line);long long value;rowin>>value;vector<string>r(n-1);for(auto&x:r){rowin>>x;if(x.size()!=size_t(n-1)||x.find_first_not_of("+-")!=string::npos)throw runtime_error("invalid parent witness");}string extra;if(rowin>>extra)throw runtime_error("extra data");
  vector<vector<int>>b(n-1,vector<int>(n-1));for(int i=0;i<n-1;i++)for(int j=0;j<n-1;j++)b[i][j]=r[i][j]=='+'?1:-1;
  for(int variant=0;variant<4;variant++){
   auto c=b;if(variant&1)for(int&x:c[0])x=-x;
   if(variant&2){auto old=c;for(int i=0;i<n-1;i++)for(int j=0;j<n-1;j++)c[i][j]=old[n-2-j][n-2-i];}
   for(int i=1;i<n;i++){s.a[i][0]=1;for(int j=1;j<n;j++)s.a[i][j]=c[i-1][j-1];}
   s.dp[0][0]=1;for(int i=n-1;i>=1;i--){int k=n-i;for(int mask:s.subsets[k]){long long x=0;for(int z=mask;z;z&=z-1){int j=__builtin_ctz((unsigned)z);x+=s.a[i][j]*s.dp[k-1][mask^(1<<j)];}s.dp[k][mask]=x;}}
   s.upper(0);
  }parents++;
 }
 ofstream out(string(argv[3])+"_spectrum.txt");for(size_t v=0;v<s.seen.size();v++)if(s.seen[v])out<<v<<"\n";
 cerr<<"EXTENSION WITNESSES n="<<n<<" parents="<<parents<<" matrices="<<s.count<<" absolute_values="<<s.found<<"\n";return 0;
}catch(const exception&e){cerr<<"ERROR: "<<e.what()<<"\n";return 2;}}
