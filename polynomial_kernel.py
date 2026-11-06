"""Exact rational autocorrelation construction; verification checks are in verify_band.py."""
from fractions import Fraction as F
from math import comb,factorial

def evaluate(coeff,x):
    value=0
    for c in reversed(coeff):value=value*x+c
    return value

def construct(config):
    a=F(config['kernel_halfwidth']);shape=[F(v) for v in config['kernel_shape']]
    # q(y)=(1-y^2)*(1+c1*y^2+c2*y^4+...), on [-1,1].
    factor=[F(1)]+shape
    qc=[F(0)]*(len(factor)+1)
    for j,c in enumerate(factor):qc[j]+=c;qc[j+1]-=c
    D=4*(len(qc)-1)+1
    wc=[F(0)]*(D+1)
    for ii,ci in enumerate(qc):
        for jj,cj in enumerate(qc):
            i=2*ii;j=2*jj
            for k in range(j+1):
                pref=ci*cj*comb(j,k)*(-1)**(j-k)/F(i+k+1)
                power=j-k;n=i+k+1
                wc[power]+=pref
                for ell in range(n+1):wc[power+ell]-=pref*comb(n,ell)*(-1)**(n-ell)
    while wc[-1]==0:wc.pop()
    norm=wc[0];amplitude=F(config.get('kernel_amplitude','10'))
    wc=[amplitude*v/norm/a**j for j,v in enumerate(wc)]
    d=2*a;degree=len(wc)-1
    at0=[wc[j]*factorial(j) for j in range(degree+1)]
    atd=[sum(wc[k]*F(factorial(k),factorial(k-j))*d**(k-j) for k in range(j,degree+1)) for j in range(degree+1)]
    fourth=[wc[k+4]*F(factorial(k+4),factorial(k)) for k in range(degree-3)]
    bn=max(13,len(fourth)-1)
    bern4=[sum(fourth[j]*d**j*F(comb(i,j),comb(bn,j)) for j in range(min(i,len(fourth)-1)+1)) for i in range(bn+1)]
    derivative=[(j+1)*qc[j+1] for j in range(len(qc)-1)]
    n=len(derivative)-1
    bern_qprime=[sum(derivative[j]*F(comb(i,j),comb(n,j)) for j in range(i+1)) for i in range(n+1)]
    return dict(a=a,d=d,qc=qc,norm=norm,amplitude=amplitude,coeff=wc,at0=at0,atd=atd,bern4=bern4,bern_qprime=bern_qprime,M4=max(abs(v) for v in bern4))
