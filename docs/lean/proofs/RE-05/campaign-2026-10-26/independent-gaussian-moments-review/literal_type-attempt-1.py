import re
def literal(name):
 d=lookup[name];text=without_comments(frozen[d['source']].decode());start=sum(len(x)+1 for x in text.splitlines()[:d['line']-1]);tail=text[start:]
 match=re.match(r'\s*(?:@\[[^\n]*\]\s*)?(?:(?:private|local|protected)\s+)?(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_.\']*)',tail)
 assert match,(name,d)
 declaration=match[1];prefix=None if name==declaration else name.removesuffix('.'+declaration);assert prefix!=name
 body=tail[match.end():];stack=[];header=None;pending_top_level_lets=0
 for i,c in enumerate(body):
  if c in '({[':stack.append(c)
  elif c in ')}]':
   assert stack
   stack.pop()
  elif not stack and re.match(r'let\b',body[i:]) and (i==0 or not re.match(r"[\w']",body[i-1])):
   pending_top_level_lets+=1
  elif body[i:i+2]==':=' and not stack:
   if pending_top_level_lets:
    pending_top_level_lets-=1
   else:
    header=body[:i].rstrip();break
 assert header is not None,name
 assert not re.search(r"(?m)^\s*(?:(?:private|local|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|axiom|instance|structure|inductive)\b",header),('Captured a named declaration in literal type',name)
 rest=header.lstrip();args=[]
 while rest and rest[0] in '({[':
  opener=rest[0];closer={'(':')','{':'}','[':']'}[opener];depth=0
  for i,c in enumerate(rest):
   if c==opener:depth+=1
   elif c==closer:
    depth-=1
    if depth==0:break
  group=rest[1:i]
  if ':' in group:
   names=group.split(':',1)[0].strip().split();assert all(re.fullmatch(r"[^\W\d][\w']*",n) and n!='_' for n in names),(name,group)
   args.extend(names)
  else:
   assert opener=='[',(name,group)
   args.append('(inferInstance)')
  rest=rest[i+1:].lstrip()
 assert rest.startswith(':'),(name,rest[:100])
 source_opens=[line for line in text.splitlines() if line.startswith('open ') and not line.startswith('open scoped ')]
 application=d['audit_id'] if d['visibility']=='private' else name
 code=(f'namespace {prefix}\n' if prefix else 'section\n')+'\n'.join(source_opens)+f'\nexample{header} := by\n  exact @{application} '+ ' '.join(args)+(f'\nend {prefix}\n' if prefix else '\nend\n')
 return code,{'name':name,'source':d['source'],'line':d['line'],'verbatim_header_sha256':sha(header.encode()),'application_arguments':args,'application_name':application,'visibility':d['visibility']}
