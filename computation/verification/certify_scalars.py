"""Directed interval checks of scalar budgets, not a formal proof of the manuscript.

All input decimals are exact strings. Each check requires a STRICTLY positive
lower interval endpoint. No floating-point sampling is used for certification.
"""
import argparse
from common import write_result, metadata
from mpmath import iv
from certify_profiles import certify as certify_profiles
from certify_localization import certify as certify_localization
from parameters import (THRESHOLD, ETA_NUMERATOR, ETA_DENOMINATOR, FOURIER_K,
                        DIRICHLET_Q, BOUNDARY_NUMERATOR, BOUNDARY_DENOMINATOR)


def certify(output_dir=None):
    iv.dps = 60
    I = iv.mpf
    p = iv.pi
    boundary=I(BOUNDARY_NUMERATOR)/BOUNDARY_DENOMINATOR
    x = iv.exp(-boundary)
    w = I('0.0013')
    v = I('0.0065')
    A = 2*p*p/75
    C = 5*A
    eta = I(ETA_NUMERATOR)/ETA_DENOMINATOR
    N = I(THRESHOLD)
    K = FOURIER_K
    Q = DIRICHLET_Q
    log_budget = iv.log(2/eta)
    fourier_tail = 10*iv.exp(-eta*K)/(eta*K)
    records = []

    def positive(key, section, expression, value):
        ok = bool(value.a > 0)
        records.append({'id': key, 'section': section, 'positive_expression': expression,
                        'interval': str(value), 'passed': ok})

    def lt(key, section, description, left, right):
        positive(key, section, description + ' (right - left)', right-left)

    # Endpoint periodic-product estimate and eta/tail expansions.
    lt('E01','5.1','0.2 < far-cusp lower bound', I('0.2'),
       (4-10*v)/5*(1-1/iv.sqrt(1+16*iv.exp(-5*v)/(p*p))))
    lt('E02','5.1','sqrt(5)-1 < 1.25',iv.sqrt(5)-1,I('1.25'))
    length = 5*iv.sqrt(5)*v
    lt('E03','5.1','coth remainder < 0.507', I('0.5')+length/(12*(1-length**2/(4*p*p))),I('0.507'))
    lt('E04','5.1','6.195+2.028+4.028 < 13', I('6.195')+I('2.028')+I('4.028'),I(13))
    lt('E05','5.1','0.2 < 0.288 - 13v',I('0.2'),I('0.288')-13*v)
    lt('E06','5.1','0.2 < 0.55 - 13v',I('0.2'),I('0.55')-13*v)
    lt('E07','5.2','1 < eta transformed exponent',I(1),(4*p*p/25)*I(16)/25)
    z = iv.exp(-1/w)
    lt('E08','5.2','two transformed log-product bounds < 3 exp(-1/w)',2/(1-z)**2,I(3))
    lt('E09','5.2','eta relative remainder < 10 exp(-1/w)',3*iv.exp(3*z),I(10))
    lt('E10','5.2','root-filter product bound < 2',iv.exp(2*w)*(4*I('1.001')+I('0.001'))/5,I(2))
    lt('E11','5.3','root derivative bound for Re(t)<=1',1/(2*(1-iv.cos(2*p/5-I('0.75')))),I(4))
    lt('E12','5.3','root derivative bound for Re(t)>=1',1/(iv.exp(1)+iv.exp(-1)-2),I(4))
    lt('E13','5.3','4+5/12 < 5',4+I(5)/12,I(5))
    L = x/(1-x)
    lt('E14','5.3','weak-mode quadratic remainder < 8x^2',
       4*(1/(2*(1-x))+iv.exp(L)/(2*(1-x)**2)),I(8))
    lt('E15','5.3','four tail exponential errors < 25 |w| x',
       20*iv.exp(L+5*I('0.001625')*x/(1-x))/(1-x),I(25))
    lt('E16','5.4','tail log budget <= x/w',(4*w+I(4)/5)/(1-x),I(1))
    lt('E17','5.4','minor-arc exponent gap > 1/30',I(1)/30,I('0.04')-x-x/(5*(1-x)))
    lt('E18','5.4','minor-arc prefactor < 16',6*iv.sqrt(2*p*I('0.67'))*iv.exp(w/6),I(16))
    lt('E19','5.4','eta exponent gap > 0.9',I('0.9'),1-x-x/(5*(1-x)))
    lt('E20','5.4','q=1 exponent gap > 0.9',I('0.9'),A+C/(1+I('0.75')**2)-x-x/(5*(1-x)))
    # Normalized eta and q=1 errors can each be absorbed into one exponential budget.
    positive('E21','5.4','(0.9-1/30)/w - log(100) + log(w)/2',
             (I('0.9')-I(1)/30)/w-iv.log(100)+iv.log(w)/2)
    B2 = I(8)/5*(1+boundary+boundary**2/2)*x/(1-x)
    B3 = I(24)/5*((1+boundary+boundary**2/2)*x/(1-x)+boundary**3/6*x/(1-x)**2)
    lt('E22','5.5','B2 < 0.142', B2,I('0.142'))
    lt('E23','5.5','0.38 < 2A-B2',I('0.38'),2*A-B2)
    lt('E24','5.5','2A+B2 < 0.67',2*A+B2,I('0.67'))
    lt('E25','5.5','6A+B3 < 2.56',6*A+B3,I('2.56'))
    lt('E26','5.5','A/(1+(3/4)^2)-B2/2 > 0.097',I('0.097'),A/(1+I('0.75')**2)-B2/2)
    lt('E27','5.5','Gaussian L1 coefficient < 14.9',
       I('2.56')/6*iv.sqrt(I('0.67')/(2*p))/I('0.097')**2,I('14.9'))
    lt('E28','5.5','absolute integral / Gaussian < 1.86',iv.sqrt(I('0.67')/I('0.194')),I('1.86'))
    lt('E29','5.5','amplitude x coefficient < 15',8*I('1.86'),I(15))
    lt('E30','5.5','amplitude w coefficient < 60',32*I('1.86'),I(60))
    lt('E31','5.5','endpoint Gaussian tail < 0.1 sqrt(w)',
       2*iv.exp(-I('0.106875')/w),I('0.1')*iv.sqrt(w))
    lt('E32','5.5','combined endpoint error < 0.85',
       15*iv.sqrt(w)+15*x+60*w+50*w**(-3)*iv.exp(-1/(30*w)),I('0.85'))
    positive('E33','5.5','1/30 - 3w',I(1)/30-3*w)
    lt('E34','6','endpoint cutoff < 31147',C/(25*w*w),I(31147))
    lt('E35','5.3','strong mode linear error / min sigma < 8x',
       4*iv.exp(L)/(1-x)/((5-iv.sqrt(5))/2),I(8))
    lt('E36','5.2','primitive eta factor < 1.001',1+10*iv.exp(-1/w),I('1.001'))
    lt('E37','5.2','q=1 root-filter term < 0.001 of primitive exponential',
       iv.sqrt(5)*(1+10*iv.exp(-1/w))*iv.exp(-(C+A)/w),I('0.001'))

    # Bulk phase and competition bounds.
    u0 = (iv.sin(p/5)*iv.cos(p/5)+2*iv.sin(2*p/5)*iv.cos(2*p/5))/5
    v0 = (iv.sin(2*p/5)-iv.cos(2*p/5)/iv.sin(2*p/5))/5
    lt('B01','7','weak phase a=3 margin > x/4',I(1)/4,8*iv.cos(p/5)*v0/p)
    lt('B02','7','weak phase a=4 margin > x/4',I(1)/4,8*iv.cos(3*p/10)*u0/p)
    for key,expr in [('B03',4*iv.cos(p/10)**2),
                     ('B04',4*(-iv.cos(3*p/5))*iv.cos(p/5)),
                     ('B05',4*(-iv.cos(13*p/10))*iv.cos(2*p/5))]:
        lt(key,'7','strong-mode constant lower bound > 1/4',I(1)/4,expr)
    localization=certify_localization(output_dir)
    profiles=certify_profiles(output_dir)
    lt('G01','9.1','large-box denominator > .05',I('.05'),iv.sin(2*p/5-I('1.2')))
    lt('G02','9.1','small-box denominator > .75',I('.75'),iv.sin(2*p/5-I('.4')))
    lt('G03','9.1','large-box integral EM error < 7200/n',(boundary**2+I('1.44'))/(2*I('.05')**2),I(7200))
    lt('G04','9.1','small-box |z| < 5.6',iv.sqrt(boundary**2+I('.16')),I('5.6'))
    lt('G05','9.2','small-box amplitude < 1.54',iv.exp(I('.4')*I('.8')/I('.75')),I('1.54'))
    lt('G06','9.2','large-box amplitude < 6',I(80)**(I(2)/5),I(6))
    lt('G07','9.1','second EM remainder coefficient < 3400',8*I('5.6')**3/I('.75')**3,I(3400))
    lt('G08','9.3','rotated characteristic function modulus > .69',I('.69'),iv.cos(I('.8')))
    lt('G09','9.3','complex third cumulant coefficient < 23',
       4/I('.69')+I('4.8')/I('.69')**2+I('2.048')/I('.69')**3,I(23))
    lt('G10','9.3','complex fourth cumulant coefficient < 240',
       16/I('.69')+I('37.6')/I('.69')**2+I('30.72')/I('.69')**3+I('9.8304')/I('.69')**4,I(240))
    lt('G11','9.3','small-angle cosine coefficient > .39',I('.39'),I('.5')-I('1.6')**2/24)
    for j in range(16):
        left=I(8+j)/20;right=I(9+j)/20
        coefficient=(iv.sin(2*right)/(2*right))**2/2
        lt('G16_'+str(j),'9.3','intermediate loss > .052 V on angle cell',I('.052'),coefficient*left**2)
    lt('G17','9.3','profile-derived Gaussian decay > .001',I('.001'),profiles['min_variance']*I('.16')/2)
    lt('G18','9.3','profile-derived intermediate decay > .00074',I('.00074'),profiles['min_variance']*I('.052'))
    lt('G19','9.3','minor-arc prefactor < 15',5*iv.sqrt(2*p*I(4)/3),I(15))
    lt('G20','9.3','intermediate prefactor < 34',4*I('2.4')*6*iv.exp(7200/N)*iv.sqrt((I(4)/3)/(2*p)),I(34))
    for key,decay,power,prefactor in [('G21',I('.001'),I('2.5'),I(15)),
                                     ('G22',I('.00074'),I('1.5'),I(34)),
                                     ('G23',I('.001'),I(1),I(8))]:
        positive(key,'9.3','decay*N - power*log(N) - log(prefactor)',decay*N-power*iv.log(N)-iv.log(prefactor))
        positive(key+'m','9.3','decay - power/N',decay-power/N)
    lt('G24','9.4','uniform grouped error/phase ratio < .98',profiles['max_ratio'],I('.98'))
    lt('G25','10','integer threshold >= 31147',I(31146),N)
    lt('G26','9.2','absolute first EM coefficient < 1',I('5.6')*(I(1)/30+I(2)/(25*I('.75'))),I(1))
    data = {**metadata('outward-rounded scalar interval certificate'), 'decimal_precision':60,
            'theorem_threshold':THRESHOLD,
            'localization_parameters':{'eta':f'{ETA_NUMERATOR}/{ETA_DENOMINATOR}',
                                       'K':K,'Q':Q,'non5_small_denominator_cutoff':100,'five_small_denominator_cutoff':300},
            'check_count':len(records), 'status':'passed' if all(r['passed'] for r in records) else 'FAILED',
            'localization_interval_checks':localization['check_count'],
            'scope':'Endpoint, phase and bulk comparisons; all localization comparisons are in localization_certificate.json.', 'checks':records}
    write_result('scalar_certificate.json',data,output_dir)
    for r in records:
        if not r['passed']: print('FAILED',r['id'],r['positive_expression'],r['interval'])
    if data['status'] != 'passed': raise RuntimeError('Scalar certification failed')
    return data


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output-dir')
    certify(parser.parse_args().output_dir)
