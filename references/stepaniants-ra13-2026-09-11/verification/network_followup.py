"""Read-only supplement: PR review bodies and GitHub Discussions in every public fork."""
from pathlib import Path
import argparse,concurrent.futures,datetime,json,os,re,shutil,subprocess
p=argparse.ArgumentParser();p.add_argument('--audit',type=Path,required=True);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
GH=os.environ.get('GH',shutil.which('gh'));audit=json.loads(args.audit.read_text());pattern=re.compile(r'\bRA-13\b|Gamma|trace.{0,30}tail|Hallman|absolute.{0,30}trace',re.I|re.S)
def api(endpoint,paged=False):
 data=json.loads(subprocess.check_output([GH,'api',endpoint]+(['--paginate','--slurp'] if paged else []),text=True))
 return [item for page in data for item in page] if paged else data
def gql(query,variables):
 command=[GH,'api','graphql','-f','query='+query]
 for k,v in variables.items():
  if v is not None:command+=['-f',k+'='+str(v)]
 data=json.loads(subprocess.check_output(command,text=True))
 if data.get('errors'):raise RuntimeError(data['errors'])
 return data['data']
def connection(query,variables,extract):
 cursor=None
 while True:
  d=extract(gql(query,{**variables,'cursor':cursor}));yield from d['nodes']
  if not d['pageInfo']['hasNextPage']:break
  cursor=d['pageInfo']['endCursor']
summary=[];matches=[];prs=[]
for repo in audit['repositories']:
 info=api('repos/'+repo);pulls=api('repos/'+repo+'/pulls?state=all&per_page=100',True)
 summary.append({'repo':repo,'has_discussions':info.get('has_discussions',False),'pull_requests':len(pulls)})
 prs += [(repo,q['number']) for q in pulls]
 if info.get('has_discussions'):
  o,n=repo.split('/')
  query='query($o:String!,$n:String!,$cursor:String){repository(owner:$o,name:$n){discussions(first:100,after:$cursor){nodes{id title body url}pageInfo{hasNextPage endCursor}}}}'
  discussions=list(connection(query,{'o':o,'n':n},lambda d:d['repository']['discussions']))
  summary[-1]['discussions']=len(discussions)
  for d in discussions:
   if pattern.search(d['title']+'\n'+d['body']):matches.append({'repo':repo,'kind':'discussion',**d})
   cq='query($id:ID!,$cursor:String){node(id:$id){... on Discussion{comments(first:100,after:$cursor){nodes{id body url}pageInfo{hasNextPage endCursor}}}}}'
   for c in connection(cq,{'id':d['id']},lambda x:x['node']['comments']):
    if pattern.search(c['body']):matches.append({'repo':repo,'kind':'discussion_comment',**c})
    rq='query($id:ID!,$cursor:String){node(id:$id){... on DiscussionComment{replies(first:100,after:$cursor){nodes{body url}pageInfo{hasNextPage endCursor}}}}}'
    for r in connection(rq,{'id':c['id']},lambda x:x['node']['replies']):
     if pattern.search(r['body']):matches.append({'repo':repo,'kind':'discussion_reply',**r})
def reviews(pair):
 repo,n=pair
 return repo,n,api(f'repos/{repo}/pulls/{n}/reviews?per_page=100',True)
count=0
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
 for repo,n,rs in pool.map(reviews,prs):
  count+=len(rs)
  for r in rs:
   if pattern.search(r.get('body') or ''):matches.append({'repo':repo,'kind':'pr_review','pull_number':n,'url':r['html_url'],'body':r.get('body'),'state':r.get('state')})
report={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Every public fork from the accompanying full network audit; all paginated PR review bodies and, where enabled, all paginated GitHub Discussion threads, comments and replies. Earlier audit covers issue/PR bodies, issue comments and inline PR review comments.','repositories':summary,'total_review_bodies_read':count,'matches':matches}
encoded=json.dumps(report,indent=2)
encoded=re.sub(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}','[public contact address redacted]',encoded)
args.output.write_text(encoded+'\n')
print(report['checked_utc'],'PR review bodies:',count,'matches:',len(matches));print(summary)
