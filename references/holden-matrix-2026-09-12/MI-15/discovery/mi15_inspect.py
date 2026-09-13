from mi15_gram import setup
import numpy as np
n=8
vals,pairs,C,Q0,zero,keep,free,forced,ii,jj,sg=setup(n)
print('zero',[(i,pairs[i]) for i in zero])
var=set()
for _,loc in free:
 for i,j,s in loc: var.add(tuple(sorted((i,j))))
for i in keep:
 for j in keep:
  if i<j and (i,j) not in var and Q0[i,i]*Q0[j,j]==Q0[i,j]**2:
   print('saturated',i,pairs[i],j,pairs[j],Q0[i,i],Q0[j,j],Q0[i,j])
z=np.load('/mnt/data/nla_current_work/mi15_n8_float.npz');w,v=np.linalg.eigh(z['Q'])
for k in range(4):
 ix=np.argsort(-abs(v[:,k]))[:20]
 print('\neig',w[k]);print([(pairs[keep[i]],round(float(v[i,k]),6)) for i in ix])
