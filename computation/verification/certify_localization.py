"""v0.7: common Dirichlet cover, denominator-dependent smoothing and periodic residues."""
import argparse
from common import metadata,write_result
from mpmath import iv
from parameters import (THRESHOLD,DIRICHLET_Q,FOURIER_K,ETA_NUMERATOR,ETA_DENOMINATOR,
 NON5_FOURIER_K,NON5_ETA_NUMERATOR,NON5_ETA_DENOMINATOR,BOUNDARY_NUMERATOR,BOUNDARY_DENOMINATOR)
from certify_resonant_gap import gap_bound


def certify(output_dir=None):
    iv.dps=60;I=iv.mpf;N=I(THRESHOLD);Q=I(DIRICHLET_Q);boundary=I(BOUNDARY_NUMERATOR)/BOUNDARY_DENOMINATOR
    checks=[]
    def positive(key,description,value):
        assert bool(value.a>0),(key,str(value))
        checks.append({'id':key,'description':description,'positive_margin_interval':str(value),'passed':True})
    calL=lambda x:(1+x)*iv.log(1+x)-x*iv.log(x)
    t=I('4.97')
    H=t*iv.log(2*iv.sin(t/2))+sum((iv.sin(k*t)/k**2 for k in range(1,1001)),I(0))
    positive('L00a','H(4.97) > 0',H-I(1)/1000)
    positive('L00b','f(4.97) < 1/5',I(1)/5-iv.log(2*iv.sin(t/2)))
    eta=I(NON5_ETA_NUMERATOR)/NON5_ETA_DENOMINATOR; K=NON5_FOURIER_K
    eta5=I(ETA_NUMERATOR)/ETA_DENOMINATOR;K5=FOURIER_K
    L=iv.log(2/eta);L5=iv.log(2/eta5)
    tail=10*iv.exp(-eta*K)/(eta*K);tail5=10*iv.exp(-eta5*K5)/(eta5*K5)
    gap=I('0.001');Rmin=I('0.238')
    kappa=lambda z:I(1)/2+z/(12*(1-z*z/(4*iv.pi**2)))
    z=boundary*K/N+10*iv.pi*K/Q
    z5=boundary*K5/N+2*iv.pi*K5/Q
    positive('L01','non-5 geometric argument < 2 pi',2*iv.pi-z)
    positive('L02','multiple-of-5 geometric argument < 2 pi',2*iv.pi-z5)
    positive('L03','non-5 geometric kernel kappa < 3',I(3)-kappa(z))
    positive('L04','multiple-of-5 geometric kernel kappa < 1.4',I('1.4')-kappa(z5))
    positive('L05','non-5 K/Q < 1/5',Q-5*K)
    positive('L06','multiple-of-5 K/Q < 1',Q-K5)
    resonance=4*kappa(z)*L/N;resonance5=4*kappa(z5)*L5/N
    gamma=I(1)/(2*(1-K/Q))+I(1)/(2*(1-5*K/Q))
    gamma5=I('0.6')/(1-K5/Q)
    gamma_cusp=I(1)/(2*(1-K5/Q))
    # b=1: short angles use the maximum over every radius directly.
    short=4*(1-iv.pi/6)*iv.log(2*iv.sin(I(1)))
    positive('L07','q=1 short-angle competition > .025',I('1.189')-short-I('.025'))
    positive('L08','q=1 long-angle competition > .025',I('1.189')-I('.8')-4*iv.pi*calL(eta/2)-I('.025'))
    positive('L09','b>=2 small-tau competition > .1',I('1.189')-I('.4')-4*iv.pi*calL(eta)-I('.1'))
    def dilog_upper(a):
        y=iv.exp(-a)
        return sum((y**k/k**2 for k in range(1,101)),I(0))+y**101/(101**2*(1-y))
    C=2*iv.pi**2/15;A0=iv.pi**2/6
    li5lower=sum((iv.exp(-I('2.5')*k)/k**2 for k in range(1,6)),I(0))
    positive('L09r','R(.5) > 1.189',(C+li5lower/5-dilog_upper(I('.5')))/I('.5')-I('1.189'))
    for j in range(200):
        a=I('.5')+I(j)/40;b=a+I(1)/40
        B=dilog_upper(a)
        positive(f'L10a_{j}','q=1 radial competition > .025 on tau cell',
                 (C-B-B**2/A0)/b-4*calL(eta/a)-I('.025'))
        positive(f'L10b_{j}','b>=2 radial competition > .1 on tau cell',
                 (C-B-B**2/(2*A0))/b-2*calL(eta/a)-I('.1'))
    y=iv.exp(-boundary)
    positive('L11','R(boundary) > .238',(C-y-y*y/(4*(1-y)))/boundary-Rmin)
    sums={}
    for label,kk,ee in [('non5',K,eta),('five',K5,eta5)]:
        sums[label]=sum((iv.exp(-ee*l)/(I(l)*((l+1)//2)) for l in range(1,kk+1)),I(0))
    def period_bounds(label,B):
        kk,ee=(K,eta) if label=='non5' else (K5,eta5)
        q=iv.exp(-ee*B)
        T=sums[label]+2*(1+iv.log(I(kk)))*q/(B*(1-q))
        U=iv.pi**2/(3*(1-q))
        return T,U
    correction=1/(Q*(1-K/Q))+5/(Q*(1-5*K/Q))
    def non5_bound(bmax,bmin):
        T,U=period_bounds('non5',I(bmin))
        return I(bmax)/(2*N)*(2*T+correction*U)
    T1,U1=period_bounds('five',I(301));T5,U5=period_bounds('five',I(61))
    large5=Q/(2*N)*(T1+T5/5+(U1+U5/5)/(Q*(1-K5/Q)))
    S1=sum((iv.exp(-eta*l)/l**2 for l in range(1,K+1)),I(0))
    large_non5=Q/(2*N)*(2*S1+correction*iv.pi**2/6)
    positive('L12','b=1 localization gap > .001',I('.025')-2*eta-resonance-tail-gap)
    positive('L13','2<=b<=100 non-5 gap > .001',I('.1')-2*eta-gamma*100*L/N-resonance-tail-gap)
    positive('L14','100<b<=2K non-5 gap > .001',Rmin-4*iv.log(2)/101-2*eta-non5_bound(2*K,101)-resonance-tail-gap)
    positive('L15','2K<b<=Q non-5 gap > .001',Rmin-4*iv.log(2)/(2*K+1)-2*eta-large_non5-resonance-tail-gap)
    positive('L16','5<b<=300 proper multiple-of-5 gap > .001',Rmin/2-2*eta5-gamma5*300*L5/N-resonance5-tail5-gap)
    positive('L17','300<b<=Q multiple-of-5 gap > .001',Rmin-5*iv.log(5)/301-2*eta5-large5-resonance5-tail5-gap)
    resonant=gap_bound(output_dir)
    positive('L18','grouped denominator-5 gap > .00992',resonant-I('.00992'))
    positive('L19','b=5 outside main arcs gap > .001',I('.00992')-2*eta5-gamma_cusp*5*L5/N-resonance5-tail5-gap)
    result={**metadata('outward-rounded denominator-dependent localization certificate'),
      'status':'passed','decimal_precision':60,'theorem_threshold':THRESHOLD,
      'common_Q':DIRICHLET_Q,'kernel_bounds':{'non5':str(kappa(z)),'five':str(kappa(z5))},'non5_parameters':{'eta':f'{NON5_ETA_NUMERATOR}/{NON5_ETA_DENOMINATOR}','K':K},
      'five_parameters':{'eta':f'{ETA_NUMERATOR}/{ETA_DENOMINATOR}','K':K5},
      'uniform_log_gap':'1/1000','S0_intervals':{k:str(v) for k,v in sums.items()},'S1_interval':str(S1),
      'check_count':len(checks),'checks':checks,
      'scope':'Interval comparisons after analytic reductions; covers every Dirichlet denominator.'}
    write_result('localization_certificate.json',result,output_dir)
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output-dir');certify(p.parse_args().output_dir)
