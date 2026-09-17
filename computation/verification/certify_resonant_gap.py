"""Uniform denominator-5 gap via analytic monotone lower envelopes.

The 400 subintervals partition x in [0,1], NOT the angle t. The sinc
inequality in manuscript section 8.3a handles every real |t| >= 6/5.
"""
import argparse
from math import comb
from common import metadata, write_result
from mpmath import iv
from parameters import ETA_NUMERATOR, ETA_DENOMINATOR, BOUNDARY_NUMERATOR, BOUNDARY_DENOMINATOR


def verify_weight_polynomials():
    """Exact coefficients for dW_d/dy=(1-y) Q_d(y)/S(y)^3."""
    result=[]
    for d in range(1,5):
        coefficients=[0]*11
        for i in range(d,10-d,2):
            for j in range(5):coefficients[i+j-1]+=i-2*j
        q=[];total=0
        for c in coefficients:total+=c;q.append(total)
        assert q[-1]==0
        while q and q[-1]==0:q.pop()
        if d==1:
            degree=len(q)-1
            transformed=[sum(q[i]*comb(degree-i,k-i) for i in range(k+1)) for k in range(degree+1)]
            signs=[1 if c>0 else -1 for c in transformed if c]
            assert sum(a!=b for a,b in zip(signs,signs[1:]))==1
            assert q[0]>0 and sum(q)<0
        else:
            assert all(c>=0 for c in q) and any(c>0 for c in q)
            transformed=None
        result.append({'difference':d,'Q_coefficients_ascending':q,'mobius_coefficients':transformed})
    return result


def gap_bound(output_dir=None):
    polynomials=verify_weight_polynomials()
    iv.dps=60
    I=iv.mpf
    eta=I(ETA_NUMERATOR)/ETA_DENOMINATOR
    T=I(6)/5
    boundary=I(BOUNDARY_NUMERATOR)/BOUNDARY_DENOMINATOR
    cells=400
    profiles={}
    branches={'uniform':0,'endpoint':0}
    for s in range(1,5):
        profile=[]
        for i in range(1,cells+1):
            z=eta+boundary*I(i)/cells
            y=iv.exp(-z)
            value=sum((y**(2*j+s) for j in range(5-s)),I(0))/sum((y**r for r in range(5)),I(0))**2
            uniform=I(5-s)/25
            # Certify which exact endpoint gives min(1/25,f_s(z)).
            if value.a > uniform.b:
                profile.append(uniform)
                branches['uniform']+=1
            elif value.b < uniform.a:
                profile.append(value)
                branches['endpoint']+=1
            else:
                raise RuntimeError(f'Undecided interval min at s={s}, i={i}')
        profile.append(I(0))
        profiles[s]=profile
    total=I(0)
    pairs=[]
    for d in range(1,5):
            profile=profiles[d]
            contribution=I(0)
            for i in range(1,cells+1):
                b=I(i)/cells
                # Compare rational arguments using integers, not floating point.
                a=T*d*b if 6*d*i<=10*cells else I(2)
                primitive_lower=b*(a*a/6-a**4/120)
                contribution+=(profile[i-1]-profile[i])*primitive_lower
            pairs.append({'difference':d,'lower_bound_expression_interval':str(contribution)})
            total+=contribution
    positive_margin=total-I('0.00992')
    if not bool(positive_margin.a>0):
        raise RuntimeError('Uniform resonant gap did not exceed 0.00992')
    report={**metadata('uniform resonant-gap interval certificate'),'status':'passed',
            'decimal_precision':60,'subintervals':cells,'eta':f'{ETA_NUMERATOR}/{ETA_DENOMINATOR}','T':'6/5',
            'tau_range':f'[0,{BOUNDARY_NUMERATOR}/{BOUNDARY_DENOMINATOR}]','angle_range':'all real |t| >= 6/5',
            'analytic_basis':'Grouped difference weights W_d, endpoint envelopes and global sinc bound; manuscript 8.3a',
            'branches_certified':branches,'pair_contributions':pairs,'exact_weight_polynomials':polynomials,
            'gap_interval':str(total),'certified_gap':'0.00992',
            'strict_margin_interval':str(positive_margin),
            'scope':'Finite interval evaluation of an analytically uniform bound; no angle sampling.'}
    write_result('resonant_gap_certificate.json',report,output_dir)
    return total


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output-dir')
    gap_bound(parser.parse_args().output_dir)
