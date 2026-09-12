import torch, numpy as np, json, time, pathlib, argparse

def run(n,p,seed,steps=1800):
    torch.manual_seed(seed); torch.set_num_threads(1)
    dtype=torch.float64
    L=torch.nn.Parameter(torch.randn(2,n,n,dtype=dtype)/n**.5)
    t=torch.nn.Parameter(torch.randn(n,dtype=dtype))
    optim=torch.optim.Adam([L,t], lr=.025)
    best=-1; saved=None
    for it in range(steps):
        optim.zero_grad()
        X=L@L.transpose(-1,-2)
        S=X.sum(0)
        r=torch.softmax(t,0)
        RX=r[None,:,None]*X
        num=torch.linalg.svdvals(RX).sum()
        den=(r.pow(p/(p-1)).sum()).pow((p-1)/p)*torch.linalg.eigvalsh(S).clamp_min(1e-25).pow(p).sum().pow(1/p)
        ratio=num/den
        if ratio.item()>best:
            best=ratio.item(); saved={'n':n,'p':p,'seed':seed,'iteration':it,'ratio':best,'L':L.detach().tolist(),'r':r.detach().tolist()}
        (-ratio).backward(); optim.step()
        if it in [steps//2,3*steps//4]:
            for group in optim.param_groups: group['lr']*=.25
    return saved

if __name__=='__main__':
 ap=argparse.ArgumentParser(); ap.add_argument('--steps',type=int,default=1800); ap.add_argument('--ns',default='2,3,4,6'); ap.add_argument('--p',type=float,default=1.2); ap.add_argument('--seeds',type=int,default=3); args=ap.parse_args()
 out=pathlib.Path(__file__).parent/'mi20_search'; out.mkdir(exist_ok=True)
 for n in map(int,args.ns.split(',')):
  for seed in range(args.seeds):
   v=run(n,args.p,seed,args.steps)
   (out/f'n{n}_p{args.p}_seed{seed}.json').write_text(json.dumps(v,indent=2))
   print(n,args.p,seed,'%.15f'%v['ratio'],flush=True)
