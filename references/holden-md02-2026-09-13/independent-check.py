import itertools, math, json
count=0
max_error=0.0
max_second=0.0
for n in range(2,15):
    classes=[tuple(sorted({i,(-i)%n})) for i in range(1,n//2+1)]
    for t in [1, n, n*n, 1000000]:
        a=1-1/math.sqrt(t)
        values=[]
        for signs in itertools.product([-1,1], repeat=len(classes)):
            r=[sum(s*sum(math.cos(2*math.pi*f*j/n) for f in c) for s,c in zip(signs,classes))/n for j in range(n)]
            u1=a*r[0]
            u2=sum(r[j]*math.sqrt((1 if j==0 else 1/t)+a*a*r[j]*r[j]) for j in range(n))
            values.append((u1*u1,u2*u2))
            count+=1
        first=n*sum(v[0] for v in values)/len(values)
        second=n*sum(v[1] for v in values)/len(values)
        expected=a*a*(2-(2 if n%2 else 3)/n)
        max_error=max(max_error,abs(first-expected))
        assert abs(first-expected)<1e-11
        assert second<=68*a*a+1e-11
        if a: max_second=max(max_second,second/(a*a))
print(json.dumps({'mask_time_checks':count,'orders':'2 through 14','times':'1,n,n^2,1000000','maximum_first_formula_error':max_error,'maximum_n_E_second_squared_divided_by_a_squared':max_second,'status':'PASS'},indent=2))
