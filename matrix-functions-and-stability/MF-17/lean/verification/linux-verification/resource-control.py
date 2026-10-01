"""One-run storage and OS job control; no checker or proof-input edits."""
import os,signal,subprocess,time,sys
from pathlib import Path
pid=int(sys.argv[1])
root=Path('/tmp/mf17-nla-tools')
log=Path(sys.argv[2])/'comparator.log'
paused=set();count=0;mounted=False;ir=None
started=time.time()
def stop(sig,frame): raise SystemExit(128+sig)
signal.signal(signal.SIGTERM,stop)
try:
 while True:
  candidates=[p/'project' for p in (root/'.verification-tmp').glob('nla-fresh-proof-*') if p.name!='nla-fresh-proof-6m663gk1' and (p/'project/lakefile.toml').exists()]
  if len(candidates)==1: break
  if not Path(f'/proc/{pid}/cmdline').exists(): raise RuntimeError('Verifier ended before fresh-copy setup')
  time.sleep(.1)
 project=candidates[0]
 os.kill(pid,signal.SIGSTOP)
 try:
  ir=project/'.lake/build/ir'
  ir.mkdir(parents=True,exist_ok=True)
  if any(ir.iterdir()): raise RuntimeError('Expected an empty project IR directory before building')
  for p in [project/'.lake',project/'.lake/build',ir]: os.chown(p,1000,1000)
  backing=root/f'.tools/cache/generated-ir-{pid}'
  backing.mkdir();os.chown(backing,1000,1000)
  subprocess.run(['mount','--bind',str(backing),str(ir)],check=True)
  mounted=True
  print(f'Generated C/setup outputs: {ir} backed by {backing}. Native .olean/.ir libraries and toolchain remain unchanged.',flush=True)
 finally: os.kill(pid,signal.SIGCONT)
 while Path(f'/proc/{pid}/cmdline').exists():
  current=[]
  for p in Path('/proc').iterdir():
   if p.name.isdigit():
    try:
     if (p/'cmdline').read_bytes().startswith(b'/tmp/mf17-lean/bin/lean\x00'): current.append(int(p.name))
    except OSError: pass
  live=set(current);paused.intersection_update(live)
  active=set(sorted(current)[:2])
  for p in live-active:
   if p not in paused:
    try: os.kill(p,signal.SIGSTOP);paused.add(p);count+=1
    except ProcessLookupError: pass
  for p in paused & active:
   try: os.kill(p,signal.SIGCONT)
   except ProcessLookupError: pass
   paused.discard(p)
  if mounted and log.exists():
   s=log.read_text()
   if 'Building Solution\n' in s and 'Build completed successfully (' in s.split('Building Solution\n',1)[1]:
    subprocess.run(['umount',str(ir)],check=True);mounted=False
    print('Solution build finished; generated-C mount detached before proof export/kernel check and ordinary fresh-copy cleanup.',flush=True)
    break
  time.sleep(.2)
finally:
 for p in paused:
  try: os.kill(p,signal.SIGCONT)
  except ProcessLookupError: pass
 if mounted:
  subprocess.run(['umount',str(ir)],check=False)
 print(f'OS resource control ended after {time.time()-started:.1f}s; {count} compiler pauses; surviving paused processes resumed.',flush=True)
