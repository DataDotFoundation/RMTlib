# Exact-rational checks (q = 1/3) of RMT.Symmetric.qWhittV (RMTlib/Symmetric/QWhittaker.lean):
# (1) symmetry in the variables; (2) qWhittV = prod_{i<=l} (q;q)_{lam_i - lam_{i+1}} * GLO Psi
# (arXiv:1101.4567, Thm 1.1, gl_3); (3) the q-Cauchy identity sum P_lam(x) b_lam P_lam(y)
# = prod_{i,j} 1/(x_i y_j; q)_inf, degree by degree.  Run: python3 -I scripts/q_whittaker_check.py
import itertools
from fractions import Fraction as F
from math import prod
q=F(1,3); a=[F(2),F(5,7),F(-3,2),F(1)]
def qf(n): return F(1)*prod([1-q**(i+1) for i in range(n)])
def qb(n,k): return 0 if k<0 or k>n else (qf(n)/(qf(k)*qf(n-k)))
def interl(lam):
    N=len(lam)
    rng=[range((lam[i+1] if i+1<N else 0), lam[i]+1) for i in range(N)]
    return itertools.product(*rng)
def br(lam,mu):
    N=len(lam); return prod([qb(lam[i]-(lam[i+1] if i+1<N else 0), lam[i]-mu[i]) for i in range(N)])
def P(m,lam):
    if m==0: return 1 if all(x==0 for x in lam) else 0
    return sum(br(lam,mu)*a[m-1]**(sum(lam)-sum(mu))*P(m-1,mu) for mu in interl(lam))

def Pa(m,lam,aa):
    global a
    old=a; a=aa; r=P(m,lam); a=old; return r
for lam in [(2,1,0),(3,1,0),(2,2,1),(3,0,0),(4,2,1)]:
    v=[Pa(3,lam,[a[i] for i in p]) for p in itertools.permutations(range(3))]
    print(lam, len(set(v))==1)
def GLO(lam):
    tot=0; l=len(lam)-1
    def rec(k,row):  # build rows downward from row k
        if k==0: yield [] ; return
    # enumerate row2 then row1
    p3=list(lam)
    for p2 in itertools.product(*[range(p3[i+1],p3[i]+1) for i in range(2)]):
        for p1 in [(x,) for x in range(p2[1],p2[0]+1)]:
            rows={1:p1,2:p2,3:p3}
            z=a[0]**sum(p1)*a[1]**(sum(p2)-sum(p1))*a[2]**(sum(p3)-sum(p2))
            num=prod([qf(rows[k][i]-rows[k][i+1]) for k in range(2,l+1) for i in range(k-1)])
            den=prod([qf(rows[k+1][i]-rows[k][i])*qf(rows[k][i]-rows[k+1][i+1]) for k in range(1,l+1) for i in range(k)])
            tot+=z*num/den
    return tot
for lam in [(2,1,0),(3,1,0),(2,2,1),(3,1,1)]:
    norm=prod([qf(lam[i]-lam[i+1]) for i in range(2)])
    print(lam, P(3,lam)==norm*GLO(lam))

# --- q-Cauchy check (2 x 2 variables, degrees < 6) ---
x=[F(2,3),F(-1,5)]; y=[F(3,4),F(1,2)]
D=6
def parts(d):  # partitions of d with ≤2 parts
    return [(d-k,k) for k in range(0,d//2+1)]
def Pv(lam,v):
    global a
    a=v+[0,0]; return P(2,lam)
def b(lam): return F(1)/prod([qf(lam[i]-(lam[i+1] if i+1<len(lam) else 0)) for i in range(len(lam))])
lhs=[sum(Pv(l,x)*b(l)*Pv(l,y) for l in parts(d)) for d in range(D)]
# rhs: product of series sum_k t^k/(q;q)_k with t=x_i y_j, graded
ser=[F(1)]+[F(0)]*(D-1)
for xi in x:
  for yj in y:
    s=[(xi*yj)**k/qf(k) for k in range(D)]
    ser=[sum(ser[i]*s[d-i] for i in range(d+1)) for d in range(D)]
print([l==r for l,r in zip(lhs,ser)])
