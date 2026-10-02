import sys
from sympy import factorint, divisors
from itertools import combinations
L=int(sys.argv[1]); DMAX=int(sys.argv[2]); RMAX=int(sys.argv[3])
assert L%1755==0 and L%2==1
primes=set()
for d in divisors(L):
    if d<2 or d>DMAX: continue
    try:
        f=factorint(2**d-1, limit=10**7)
    except Exception: continue
    for p in f:
        if (2**d-1)%p==0 and pow(2,d,p)==1 and L%p and p!=3511 and p>2:
            from sympy import isprime
            if isprime(p): primes.add(p)
primes=sorted(primes)
print(len(primes), primes[:40],flush=True)
c=(2*pow(3511*3511,-1,L))%L
# meet in middle on residues: dynamic programming over subsets limited size
from collections import defaultdict
best=None
# BFS over products mod L with small number of primes
reach={1%L:()}
for p in primes:
    new={}
    for r,comb in reach.items():
        if len(comb)>=RMAX: continue
        r2=(r*p)%L
        if r2 not in reach and r2 not in new: new[r2]=comb+(p,)
    reach.update(new)
    if c in reach: break
print("reach size",len(reach))
if c in reach:
    comb=reach[c]; m=1
    for p in comb: m*=p
    n=3511**2*m
    print("m=",m,"comb=",comb,"check",pow(2,n,n)==4%n, "n=",n)
