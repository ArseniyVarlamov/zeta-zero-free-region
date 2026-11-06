#!/usr/bin/env python3
"""Finite inequalities of the paper "A larger explicit zero-free region for the Riemann zeta-function".
This checks the numerical part of the proof; it is not a formalization of the analysis.

Every mathematical comparison uses rational arithmetic or Arb enclosures.
Python floats are used only for elapsed wall-clock time. No numerical search,
downloaded certificate, precomputed moments, or source files are needed.
"""
from flint import arb, acb, fmpq, fmpq_poly, ctx
from math import factorial, comb, isqrt
import json
import time
import resource
import sys
from pathlib import Path
from fractions import Fraction
from polynomial_kernel import construct as construct_polynomial_kernel

def verify_band(CONFIG):
    ctx.prec = 160
    START = time.monotonic()
    checks = {}
    
    
    def require(name, condition, value=None, record=True):
        if not condition:
            raise AssertionError(f"FAILED: {name}: {value}")
        if record:
            checks[name] = str(value) if value is not None else True
    
    
    def ball(lo, hi):
        """Enclose rational endpoints; Arb rounds its radius outwards."""
        return arb((lo + hi)/2, arb((hi-lo)/2))
    
    
    def rat(s):
        f=Fraction(str(s)); return fmpq(f.numerator,f.denominator)
    H = arb(3)*10**12
    T0 = arb(10)**10
    K = len(CONFIG['c'])-1
    require('trigonometric degree range',1<=K<=64)
    R = arb(rat(CONFIG['R']))
    ASTAR = 1/R
    SMIN = arb(rat(CONFIG['sigma_min']))
    EMAX = arb(rat(CONFIG['eta_max']))
    XMIN = SMIN-arb('0.5')
    kernel_type=CONFIG.get('kernel_type','cosine')
    require('known kernel type',kernel_type in ['cosine','polynomial'])
    if kernel_type=='polynomial':
        pk=construct_polynomial_kernel(CONFIG)
        require('polynomial kernel normalization',pk['a']>0 and pk['norm']>0 and pk['amplitude']>0)
        require('polynomial q decreases to zero',pk['qc'][0]==1 and sum(pk['qc'])==0 and all(v<0 for v in pk['bern_qprime']),pk['bern_qprime'])
        require('polynomial kernel endpoint identities',pk['at0'][1]==0 and pk['atd'][0]==pk['atd'][1]==pk['atd'][2]==0 and pk['at0'][3]==-pk['atd'][3])
        wcoeff=[arb(rat(v)) for v in pk['coeff']]
        wleft=[arb(rat(v)) for v in pk['at0']]
        wright=[arb(rat(v)) for v in pk['atd']]
        d=arb(rat(pk['d']));w0=wleft[0];w20=wleft[2];w30=wleft[3]
        M4=arb(rat(pk['M4']))
        require('exact polynomial fourth derivative bound',all(abs(v)<=pk['M4'] for v in pk['bern4']),pk['bern4'])
    else:
        theta = arb(rat(CONFIG['theta']))
        b = theta.tan()
        a = theta/b
        KERNEL_SCALE=arb(rat(CONFIG.get('kernel_scale','1')))
        require('positive kernel scale',KERNEL_SCALE>0)
        d = 2*a/KERNEL_SCALE
        S = 1/theta.cos()**2
        w0 = S*(theta*b+3*a-3)
        w20 = -S*(S*a-1)*b**2*KERNEL_SCALE**2
        w30 = S*b**4*KERNEL_SCALE**3
    kr = [rat(x) for x in CONFIG.get('kr', ['1','-851/859','780/859','-525/859','171/859','28/859','-29/859'])]
    M=len(kr)-1
    require('multiplier normalization',1<=M<=20 and kr[0]==1 and sum(kr)>0)
    kap = [arb(x) for x in kr]
    kappa = sum(kap)
    absk = sum(abs(x) for x in kap)
    c = CONFIG["c"]
    require("integer spectral factor", len(c)==K+1 and all(type(x) is int for x in c) and sum(x*x for x in c)>0)
    cnorm=sum(x*x for x in c)
    ar = [fmpq(sum(c[j]*c[j+k] for j in range(K+1-k))*(1 if k==0 else 2),cnorm) for k in range(K+1)]
    ak = [arb(x) for x in ar]
    a1 = ak[1]
    asum = sum(ak[1:])
    Q = asum*kappa*w0/2
    require('P coefficients exact', ar[0]==1 and all(x>=0 for x in ar), ar)
    require('strict improvement', R<arb('4.85025'), arb('4.85025')-R)
    require('positive parameter ranges', R>4 and SMIN>arb('0.99') and SMIN<1 and EMAX>0 and EMAX<arb('0.01') and (kernel_type=='polynomial' or (theta>0 and theta<arb.pi()/2)))
    LLOW=rat(CONFIG.get('Llo','28.7296'))
    require('positive band lower bound', LLOW>0)
    LHIGH=arb(rat(CONFIG['Lhi']))
    SMAX=1-(arb(1)/6)/(LHIGH+(K+T0*(-LHIGH).exp()).log())
    require('band sigma upper bound range',SMIN<SMAX and SMAX<1,SMAX)
    require('parameter sigma', 1-ASTAR/(arb(LLOW)+(K+T0*(-arb(LLOW)).exp()).log())>SMIN)
    require('parameter eta', ASTAR/arb(LLOW)<EMAX)
    require('small heights', 1-1/(R*arb(2).log())>arb('0.5'))
    # The driver certifies the global Yang crossover and the complete union of bands.
    
    # p(x)>0 on [0,1]: exact Bernstein coefficients of degree M.
    bern = [sum(kr[j]*fmpq(comb(i,j),comb(M,j)) for j in range(i+1)) for i in range(M+1)]
    require('p positive on [0,1]', all(x>0 for x in bern), bern)
    
    # Three integrations by parts give W(z)=w0/z+[w''(0)+int exp(-zu)w'''(u)du]/z^3.
    # The boundary identities used here are proved in Section 4 of the paper.
    require('kernel ranges and derivative signs',d>0 and w0>0 and w20<0 and w30>0)
    if kernel_type=='cosine':
        require('derivative coefficient extrema', S*a-1>1)
        M4 = S*((S*a-1)*b**4+b**3*(S/2+b**2))*KERNEL_SCALE**4
    require('finite positive fourth derivative bound', M4>0 and M4.is_finite(), M4)
    
    
    def Csafe(nu):
        # One more integration by parts leaves boundary terms w'''(0)/z and
        # exp(-zd)w'''(d)/z; both kernels satisfy |w'''(d)| = w30.
        return abs(w20)+w30*(1+(-arb(nu)*d).exp())/nu+M4/arb(nu)**2
    
    
    NU_REAL=1/EMAX-3
    C_REAL=Csafe(NU_REAL)
    require('real transform remainder domain', NU_REAL>0 and C_REAL>0, [NU_REAL,C_REAL])
    Cminus = abs(w20)+d*d.exp()*(w30+M4*d)
    require('W remainder at Re z >=-1', Cminus>0 and Cminus.is_finite(), Cminus)
    
    # Positivity of the paired transform, as a rational-function certificate.
    hmin=2*SMIN-1
    eps=rat(CONFIG['paired_eps'])
    cmin=2*rat(CONFIG['sigma_min'])-1
    require('paired epsilon range',0<eps<1)
    C_PAIR=Csafe(hmin/EMAX)
    require('paired rescaling flag',type(CONFIG.get('pair_rescaled',False)) is bool,CONFIG.get('pair_rescaled',False))
    require('h minimum', cmin>0 and cmin<1)
    require('paired W argument domain', hmin/EMAX>0)
    require('paired error coefficient', EMAX**2*C_PAIR/(hmin*hmin*w0)<arb(eps))
    br=[kr[m]+(kr[m-1] if m else 0) for m in range(M+1)]+[kr[-1]]
    require('horizontal boundary leading sign', sum((2*m+1)*kr[m] for m in range(M+1))>0)
    # With rescaling v=y/h all denominators are m^2+v^2. The error
    # coefficient is b_m*m - abs(b_m)*eps/m, with no sign-dependent
    # replacement of h. See Proposition "Paired positivity" (Section 5).
    den=[]
    num=[]
    for m in range(1,M+2):
        den.append(fmpq_poly([(cmin*m)**2 if br[m]<=0 and not CONFIG.get('pair_rescaled',False) else m*m,1]))
        num.append(br[m]*(m+eps/m if br[m]<=0 else m-eps/m))
    pn=fmpq_poly([0])
    for i in range(M+1):
        term=fmpq_poly([num[i]])
        for j in range(M+1):
            if j!=i:
                term*=den[j]
        pn+=term
    sturm=[pn,pn.derivative()]
    while sturm[-1].degree()>0:
        rem=-(sturm[-2]%sturm[-1])
        require(f'Sturm nonzero remainder {len(sturm)}', not rem.is_zero())
        sturm.append(rem)
    
    
    def variations(seq):
        signs=[1 if x>0 else -1 for x in seq if x!=0]
        return sum(x!=y for x,y in zip(signs,signs[1:]))
    
    
    v0=variations([p[0] for p in sturm])
    vinf=variations([p[p.degree()] for p in sturm])
    require('paired numerator no nonnegative roots', v0==vinf and pn[0]>0,
            {'degree':pn.degree(),'V(0)':v0,'V(infinity)':vinf})
    
    # Off-strip loss: Lemma "Paired transform off the strip" (Section 5).
    SHIFT=w0+2*Cminus*EMAX**2/T0
    OFF=2*SHIFT*absk
    require('positive off-strip bound', SHIFT>0 and OFF>0, [SHIFT,OFF])
    
    # Lehman summation, with an explicit positive-height zero-tail majorant.
    logH=H.log()
    dK=(K+T0/H).log()
    ctail=((K+T0/H)/(2*arb.pi())).log()
    dtail=((H+T0)/(2*arb.pi())).log()/(2*H+T0)+((2*H+T0)/T0).log()/H
    tail_pos=OFF*ASTAR*((1+ctail/logH)/(2*arb.pi()*T0)+dtail/(2*arb.pi()*logH)
                     +8*(1+dK/logH)/T0**2+4/(logH*H*T0))
    tail_zero=2*OFF*EMAX*T0.log()/T0
    require('zero tails k >= 1', tail_pos<arb('1e-8'), tail_pos)
    require('zero tail k = 0', tail_zero<arb('1e-8'), tail_zero)
    TAIL=tail_zero+asum*tail_pos
    require('finite positive weighted zero tails', TAIL>0 and TAIL.is_finite(),TAIL)
    
    # Gamma term: sign-aware bounds for k=0, Stirling remainder for k>=1.
    gamma0=sum(k*((((SMAX+(2*SMAX-1)*m)/2+1) if CONFIG.get('tight_gamma',False) else arb(m+3)/2).digamma() if k>0 else
                    ((SMIN+hmin*m)/2+1).digamma()) for m,k in enumerate(kap))/2
    gamma_const=(gamma0-kappa*arb.pi().log()/2
                 +kappa*sum(ak[k]*arb(k).log() for k in range(1,K+1))/2
                 -asum*kappa*(2*arb.pi()).log()/2+asum*absk*arb('1e-10')/2)
    xmax=arb(M+3)/2; ymin=H/2
    require('digamma argument domain',xmax<ymin)
    stirling_error=xmax/(2*ymin**2)+1/(12*ymin)+xmax**2/(2*ymin**2)
    require('Stirling error', stirling_error<arb('1e-10'))
    GAMMA=-gamma_const
    require('gamma constant', GAMMA>0, GAMMA)
    
    # Pole terms, using the independently proved W remainder.
    pole=asum*absk*(M*w0/H**2+Cminus*EMAX**2/H**3)
    require('nonreal pole contribution / eta', pole<arb('1e-10'), pole)
    
    if CONFIG.get('error_method','absolute_convolution')=='trivial_zero_series':
        # Identity of Proposition "Remainder over the trivial zeros" (Section 6): T(s)=-sum_{n>=1}
        # W0((s+2*n)/eta). In particular the high-ordinate logarithmic
        # convolution loss is absent; only an eta^3 error remains.
        E2=arb(0); E3=arb(0)
        for m,k in enumerate(kap):
            sm=SMIN+hmin*m
            u=sm+2
            cm=Csafe(u/EMAX)
            require(f'trivial-zero series argument {m}',u>0 and cm>0)
            e0=cm*(1/u**3+1/(4*u**2))
            ehigh=cm*(1/H**3+1/(2*H**2))
            E3+=abs(k)*(e0+asum*ehigh)
        require('trivial-zero identity numerical domain',SMIN>arb('0.5'))
    elif CONFIG.get('error_method','absolute_convolution')=='absolute_convolution':
        # Digamma majorants and tails used for every real shift m.
        require('U majorant x>=2', arb(2)/17+arb(1)/3+arb(1)/32<arb(2).log())
        require('U majorant abs x<=1/2', arb(16).log()/2+4<arb(998).log())
        require('U majorant 1/2<=abs x<=2', arb(4).log()+1+arb(4)/3+arb(1)/2<arb(998).log())
        Y=H-2
        left_tail=(Y.log()/2+arb(1)/4)/Y**2+1000/(3*Y**3)
        right_tail=((3*Y).log()/2+arb(1)/4)/Y**2
        ITAIL=left_tail+right_tail
        require('off-centre integral tails', ITAIL<arb('2e-10'),ITAIL)
        E2=arb(0); E3=arb(0)
        for m,k in enumerate(kap):
            sm=SMIN+hmin*m
            xm=sm-arb('0.5')
            cm=Csafe(xm/EMAX)
            require(f'shift {m} remainder domain', xm>0 and cm>0)
            integral0=arb(0)
            for left,right,mode in [(0,fmpq(1,2),0),(fmpq(1,2),2,1),(2,20,2)]:
                def integrand(y, analytic, mode=mode):
                    if mode==0:
                        U=(16/(1+4*y*y)).log(analytic=analytic)/2+2/(1+4*y*y)+2
                    else:
                        U=((-1 if mode==1 else 1)*(y/2).log(analytic=analytic)
                           +2/(1+4*y*y)+2/(3*y)+1/(8*y*y))
                    z=xm*xm+y*y
                    return U/(z*z.sqrt(analytic=analytic))
                integral0+=2*acb.integral(integrand,left,right,abs_tol=arb('1e-30')).real
            tail0=2*((arb(20).log()/2+arb(1)/4)/400+arb(2)/(9*20**3)+arb(5)/(32*20**4))
            I0=integral0+tail0
            require(f'shift {m} zero-height integral', I0.is_finite() and I0>0 and I0.rad()<arb('1e-25'),I0)
            e0=cm*I0/(2*arb.pi())+Csafe(sm/EMAX)/sm**3
            # Sum log(kt)=L+log k exactly before eliminating L eta=A<=ASTAR.
            e2=cm*ASTAR*asum/(arb.pi()*xm**2)
            e3=(cm*sum(ak[j]*arb(j).log() for j in range(1,K+1))/(arb.pi()*xm**2)
                +asum*(cm*ITAIL/(2*arb.pi())+Csafe(sm/EMAX)/sm**3))
            E2+=abs(k)*e2
            E3+=abs(k)*(e0+e3)
    else:
        require('known error method',False)
    require('combined quadratic error', E2>=0 and E2.is_finite(),E2)
    require('combined cubic error', E3>0 and E3.is_finite(),E3)
    
    
    def w(u):
        if kernel_type=='polynomial':
            value=0
            for coef in reversed(wcoeff):value=value*u+coef
            return value
        u=u*KERNEL_SCALE
        return S*(S*(a-u/2)*(b*u).cos()+2*a-u
                  +(2*theta-u*b).sin()/(2*theta).sin()
                  -2*(1+(theta-u*b).sin()/theta.sin()))
    
    
    # D0(mu)=int exp(-(1-mu)u)(a1-exp(u))w(u)du.
    moments=[acb.integral(lambda u, analytic, n=n: u**n*(a1-u.exp())*w(u),0,d,
                         abs_tol=arb('1e-30')).real for n in range(9)]
    remainder=w0*(a1+d.exp())*d**10*arb('0.1')**9/(10*factorial(9))
    require('degree eight Taylor remainder', remainder<arb('1e-12'),remainder)
    require('finite moments', all(x.is_finite() and x.rad()<arb('1e-25') for x in moments))
    
    # Positive prime-power contribution (Lemma "Prime powers", Section 7). Lemma "Kernel" (Section 4) gives the Cauchy--Schwarz
    # bound |w''(u)| <= -w''(0), valid for the autocorrelation kernel.
    bern_minus=[x-sum(kr) for x in bern]
    require('p >= kappa on [0,1]',all(x>=0 for x in bern_minus),bern_minus)
    require('p decreasing on [0,1]',all(bern[i+1]<bern[i] for i in range(M)))
    PRIME=arb(0)
    prime_ids=[v['p'] for v in CONFIG.get('primes',[])]
    require('distinct prime contributions',len(prime_ids)==len(set(prime_ids)))
    prime_boxes=0
    for prime in CONFIG.get('primes',[]):
        p=prime['p']; J=prime['J']; target=arb(rat(prime.get('lower','0')))
        require(f'prime {p} admissibility',type(p) is int and p>=2 and all(p%q for q in range(2,isqrt(p)+1)) and type(J) is int and J>0 and target>=0)
        logp=arb(p).log()
        bs=[arb(0) for _ in range(K*J+1)]
        for j in range(1,J+1):
            xp=(-hmin*j*logp).exp()
            p_lower=sum(k*xp**m for m,k in enumerate(kap))
            require(f'prime {p} power {j} p lower positive',p_lower>0)
            if CONFIG.get('prime_method','quadratic')=='exact_kernel_sigma':
                up=EMAX*j*logp
                require(f'prime {p} power {j} in kernel support',up>0 and up<d)
                kernel_lower=w(up)
                require(f'prime {p} power {j} exact kernel positive',kernel_lower>0)
                weight=p_lower*kernel_lower/w0*(-SMAX*j*logp).exp()
            else:
                require('known prime method',CONFIG.get('prime_method','quadratic')=='quadratic')
                weight=p_lower*(1+w20*(EMAX*j*logp)**2/(2*w0))/arb(p)**j
            require(f'prime {p} power {j} kernel lower bound positive',weight>0)
            for k in range(K+1):
                bs[j*k]+=weight*ak[k]
        require(f'prime {p} nonnegative Fourier coefficients',all(x>=0 for x in bs))
        dbs=[k*bs[k] for k in range(len(bs))]
        M2=sum(k*k*bs[k] for k in range(len(bs)))
        N=prime.get('N',2048)
        require(f'prime {p} grid count',type(N) is int and N>0)
        radius=arb.pi()/(2*N)
        prime_min=arb(1000)
        for i in range(N):
            center=arb.pi()*(2*i+1)/(2*N)
            z=acb(0,center).exp()
            f=acb(0); df=acb(0)
            for coef,dcoef in zip(reversed(bs),reversed(dbs)):
                f=f*z+coef; df=df*z+dcoef
            lower=f.real-abs(df.imag)*radius-M2*radius**2/2
            require(f'prime {p} interval {i}',lower>target,lower,record=False)
            prime_boxes+=1
            if lower.lower()<prime_min:prime_min=lower.lower()
        require(f'prime {p} certified minimum',prime_min>target,prime_min)
        PRIME+=logp*prime_min
    require('prime contribution nonnegative',PRIME>=0,PRIME)
    require('all prime intervals covered',prime_boxes==sum(v.get('N',2048) for v in CONFIG.get('primes',[])),prime_boxes)
    
    
    exact_real=CONFIG.get('real_transform','cubic_bound')=='polynomial_exact'
    require('known real transform method',CONFIG.get('real_transform','cubic_bound') in ['cubic_bound','polynomial_exact'])
    require('exact real transform applicability',not exact_real or kernel_type=='polynomial')
    def real_transform(z):
        inverse=1/z;left=arb(0);right=arb(0)
        for v0,vd in zip(reversed(wleft),reversed(wright)):
            left=(left+v0)*inverse;right=(right+vd)*inverse
        return left-(-d*z).exp()*right

    def margin(L,A):
        shift=(K+T0*(-L).exp()).log()
        mu=1-shift/(L+shift)
        eta=A/L
        require('parameter box inside analytic domain',mu>arb('0.9') and mu<1 and eta>0 and eta<EMAX and 1-A/(L+shift)>SMIN,record=False)
        v=1-mu
        D=sum(moments[n]*(-v)**n/factorial(n) for n in range(9))-arb('1e-12')
        err=arb(0)
        for m,k in enumerate(kap):
            z=(m+1)/eta-(2*m+1)*mu-1
            require('large real W argument domain',z>NU_REAL,record=False)
            if exact_real:D+=a1*k*real_transform(z)
            else:
                D+=a1*k*w0/z
                err+=a1*abs(k)/z**3
            if m:
                z1=m/eta-(2*m+1)*mu+1
                z2=m/eta-(2*m+1)*mu
                require('large real W arguments domain',z1>NU_REAL and z2>NU_REAL,record=False)
                if exact_real:D+=k*(a1*real_transform(z1)-real_transform(z2))
                else:
                    D+=k*w0*(a1/z1-1/z2)
                    err+=abs(k)*(a1/z1**3+1/z2**3)
        D-=C_REAL*err
        return (D+(GAMMA+PRIME)*w0*eta-E2*eta**2-E3*eta**3
                -TAIL-arb('1e-10')*eta-Q*A)
    
    
    # Exact rational partition, adaptive only when a closed box is inconclusive.
    Llo=LLOW; Lhi=rat(CONFIG['Lhi'])
    Alo=fmpq(1,6); Ahi=1/rat(CONFIG['R'])
    # Only the first band's lower endpoint must cover log H; checked by driver.
    require('ordered search rectangle', Llo<Lhi and Alo<Ahi)
    NL=128; NA=16
    min_margin=arb(1); worst=None; count=0; split_count=0
    MAXDEPTH=40
    stack=[]
    for i in range(NL):
        for j in range(NA):
            stack.append((Llo+(Lhi-Llo)*i/NL,Llo+(Lhi-Llo)*(i+1)/NL,
                          Alo+(Ahi-Alo)*j/NA,Alo+(Ahi-Alo)*(j+1)/NA,0))
    while stack:
        l0,l1,a0,a1box,depth=stack.pop()
        value=margin(ball(l0,l1),ball(a0,a1box))
        if not value>arb('1e-6'):
            require('adaptive depth limit',depth<MAXDEPTH,{'box':[str(x) for x in [l0,l1,a0,a1box]],'value':str(value)})
            split_count+=1
            if depth%2==0:
                mid=(a0+a1box)/2
                stack.extend([(l0,l1,a0,mid,depth+1),(l0,l1,mid,a1box,depth+1)])
            else:
                mid=(l0+l1)/2
                stack.extend([(l0,mid,a0,a1box,depth+1),(mid,l1,a0,a1box,depth+1)])
            continue
        count+=1
        if value.lower()<min_margin:
            min_margin=value.lower(); worst=[str(x) for x in [l0,l1,a0,a1box]]
    require('all rectangles strictly positive', min_margin>arb('1e-6'), min_margin)
    require('complete rectangle partition',count==NL*NA+split_count,{'leaves':count,'splits':split_count})
    checks['worst_box']=worst
    checks['w0']=str(w0); checks['Q']=str(Q)
    checks['moments']=[str(x) for x in moments]
    checks['endpoint_margin_diagnostic']=str(margin(arb(Lhi),arb(Ahi)))
    result={'status':'PASS','statement':'C_8a <= '+CONFIG['R'],
                      'arithmetic':'FLINT/Arb 160-bit balls and exact rational polynomials',
                      'scope':'Finite inequalities of the paper; the analytic arguments and cited theorems are not checked by this program.',
                      'parameters':CONFIG,'checks':checks,'seconds':time.monotonic()-START,
                      'peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024)}
    return result,min_margin
