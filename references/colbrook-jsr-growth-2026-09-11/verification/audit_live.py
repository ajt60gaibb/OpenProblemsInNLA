import json,subprocess,concurrent.futures,base64,re,datetime
from pathlib import Path
cache=Path(__file__).resolve().parent;data=json.loads((cache/'eligibility-input.json').read_text());repo='ajt60gaibb/OpenProblemsInNLA'
def gh(*args):return json.loads(subprocess.check_output(['gh',*args],encoding='utf-8'))
forks=gh('api',f'repos/{repo}/forks?per_page=100')
data['branches']={x:[{'name':b['name'],'sha':b['commit']['sha']} for b in gh('api',f'repos/{x}/branches?per_page=100')] for x in [repo]+[f['full_name'] for f in forks]}
tasks=[(name,b,i) for name,bs in data['branches'].items() for b in bs for i in ['MF-05','MF-07','MF-12']]
def read(t):
 name,b,i=t;p=f'matrix-functions-and-stability/{i}/README.md'
 response=gh('api',f'repos/{name}/contents/{p}?ref={b["sha"]}');text=base64.b64decode(response['content']).decode()
 return {'repository':name,'branch':b['name'],'sha':b['sha'],'target':i,'status':re.search(r'\*\*Status:\*\* (.+)',text)[1].strip(),'blob':response['sha'],'resolution_terms':bool(re.search(r'^##.*[Rr]esolution|\*\*Status:\*\* (Solved|Solution claimed)',text,re.M))}
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:data['branch_targets']=list(pool.map(read,tasks))
prs=gh('pr','list','--repo',repo,'--state','all','--limit','100','--json','number,title,state')
def pr_audit(p):
 n=p['number'];pages=gh('api','--paginate','--slurp',f'repos/{repo}/pulls/{n}/files?per_page=100');files=[x['filename'] for page in pages for x in page]
 detail=gh('pr','view',str(n),'--repo',repo,'--json','reviews,comments')
 inline=gh('api','--paginate','--slurp',f'repos/{repo}/pulls/{n}/comments?per_page=100')
 texts=detail['reviews']+detail['comments']+[x for page in inline for x in page]
 return {'number':n,'title':p['title'],'state':p['state'],'target_files':[f for f in files if re.search(r'MF-(?:05|07|12)(?:/|\b)',f)],'target_review_mentions':[x.get('body','') for x in texts if re.search(r'MF[-_ ]?(?:0?5|0?7|12)\b',x.get('body',''),re.I)]}
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:data['pr_file_and_review_audit']=list(pool.map(pr_audit,prs))
pages=gh('api','--paginate','--slurp',f'repos/{repo}/issues/comments?per_page=100')
data['issue_comment_mentions']=[{'url':x['html_url'],'body':x['body']} for page in pages for x in page if re.search(r'MF[-_ ]?(?:0?5|0?7|12)\b',x['body'],re.I)]
data['checked_at_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();data['limitations']='Publicly visible repository/fork branches, issue/PR bodies, comments, reviews and PR changed-file records; cannot exclude private or unpublished work. Branch canonical status checks do not scan arbitrary unlinked manuscripts.'
(cache/'eligibility-live.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'branch_targets_checked':len(data['branch_targets']),'unexpected_status':[x for x in data['branch_targets'] if x['status']!='Partially resolved'],'pr_target_hits':[x for x in data['pr_file_and_review_audit'] if x['target_files'] or x['target_review_mentions']],'issue_comment_hits':data['issue_comment_mentions']},indent=2))
