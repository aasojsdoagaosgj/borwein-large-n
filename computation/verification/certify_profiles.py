"""Uniform parameter boxes and rigorous grouped-root error bounds for v0.6.

All of [0,11/2] is covered by 128 closed tau intervals. Each integral is
enclosed by interval range bounds on 200 x intervals, with exact monomial
integrals. This is not midpoint sampling or numerical quadrature.
"""
import argparse
from common import metadata, write_result
from mpmath import iv
from parameters import (THRESHOLD, TAU_CELLS, INTEGRATION_CELLS,
                        BOUNDARY_NUMERATOR,BOUNDARY_DENOMINATOR)


def certify(output_dir=None):
    iv.dps=60
    I=iv.mpf
    beta=I('0.39')
    boundary=I(BOUNDARY_NUMERATOR)/BOUNDARY_DENOMINATOR
    denominator_bound=I('0.75')
    amplitude_bound=I('1.54')
    rows=[]
    min_v=None
    max_ratio=None
    worst=None
    for cell in range(TAU_CELLS):
        ta=boundary*cell/TAU_CELLS
        tb=boundary*(cell+1)/TAU_CELLS
        tau=I([ta.a,tb.b])
        V=I(0); W3=I(0); W4=I(0)
        for ix in range(INTEGRATION_CELLS):
            xa=I(ix)/INTEGRATION_CELLS
            xb=I(ix+1)/INTEGRATION_CELLS
            x=I([xa.a,xb.b])
            y=iv.exp(-tau*x)
            powers=[y**r for r in range(8)]
            denominator=sum(powers[:5],I(0))**2
            variance=sum((I((k-j)**2)*powers[j+k]/denominator
                          for j in range(5) for k in range(j+1,5)),I(0))
            V+=variance*(xb**3-xa**3)/3
            W3+=variance*(xb**4-xa**4)/4
            W4+=variance*(xb**5-xa**5)/5
        xphase=iv.exp(-tau)
        v=(1-xphase)/(1+xphase)
        alpha=iv.atan2(v*iv.cos(iv.pi/5)/iv.sin(iv.pi/5),I(1))
        angle_b=iv.atan2(v*iv.cos(2*iv.pi/5)/iv.sin(2*iv.pi/5),I(1))
        U=(alpha+2*angle_b)/5
        Vangle=(2*alpha-angle_b)/5
        phases=[4*iv.cos(3*iv.pi*a/5+U)*iv.cos(-iv.pi*a/5+Vangle)
                *(1 if a==0 else -1) for a in range(5)]
        phase_lower=min(p.a for p in phases)
        if not all(bool(p.a>0) for p in phases):
            raise RuntimeError(f'Phase lower bound failed in cell {cell}')
        if not bool(V.a>(I(1)/80).b):
            raise RuntimeError(f'Variance lower bound failed in cell {cell}')
        A1=amplitude_bound*I('0.8')*xphase/denominator_bound
        A2=amplitude_bound/2*(I('0.8')*xphase/denominator_bound**2
                        +(I('0.8')*xphase/denominator_bound)**2)
        gaussian_base=(240*W4/(32*beta**2*V**2)+5*23**2*W3**2/(192*beta**3*V**3))/iv.sqrt(2*beta)
        amplitude_cross=4/iv.sqrt(2*beta)*(23*A1*W3/(8*beta**2*V**2)+A2/(2*beta*V))
        Z=iv.sqrt(tb**2+I('0.16'))
        Dmax=Z*(I(1)/30+2*xphase/(25*denominator_bound))
        em_remainder=4*amplitude_bound*(3400+Dmax**2/2)*iv.exp(Dmax/THRESHOLD+I(3400)/THRESHOLD**2)/iv.sqrt(2*beta)
        residue_rows=[]
        ratios=[]
        for residue,phase in enumerate(phases):
            gaussian=phase*gaussian_base+amplitude_cross
            # Theta_a=-z Psi_a/30+z exp(-z) sum A_l C_l.
            em_first=(Z/30*(phase+I('1.6')*A1)
                       +8*amplitude_bound*Z*xphase/(25*denominator_bound))/iv.sqrt(2*beta)
            error=(gaussian+em_first+3)/THRESHOLD+em_remainder/THRESHOLD**2
            ratio=error/phase.a
            if not bool(ratio.b<I('0.98').a):
                raise RuntimeError(f'Grouped error/phase failed in cell {cell}, residue {residue}: {ratio}')
            ratios.append(ratio)
            residue_rows.append({'residue':residue,'Gaussian_coefficient_interval':str(gaussian),
                                 'EM_first_coefficient_interval':str(em_first),
                                 'error_over_phase_interval':str(ratio)})
        ratio_upper=max(r.b for r in ratios)
        if min_v is None or bool(V.a<min_v):min_v=V.a
        if max_ratio is None or bool(ratio_upper>max_ratio):max_ratio=ratio_upper;worst=cell
        rows.append({'cell':cell,'tau_interval':str(tau),'V_interval':str(V),
                     'W3_interval':str(W3),'W4_interval':str(W4),
                     'signed_phase_intervals':[str(p) for p in phases],
                     'phase_lower_bound':str(phase_lower),
                     'grouped_residue_bounds':residue_rows,
                     'EM_second_order_remainder_coefficient_interval':str(em_remainder),
                     'passed':True})
    result={**metadata('uniform grouped-root profile interval certificate'),
            'status':'passed','decimal_precision':60,'theorem_threshold':THRESHOLD,
            'tau_cells':TAU_CELLS,'integration_cells':INTEGRATION_CELLS,
            'covered_rectangles':TAU_CELLS*INTEGRATION_CELLS,
            'inequality_count':11*TAU_CELLS,
            'uniform_variance_lower_bound':'1/80',
            'computed_variance_lower_bound':str(min_v),
            'uniform_error_over_phase_upper_bound':'0.98',
            'computed_error_over_phase_upper_bound':str(max_ratio),'worst_cell':worst,
            'scope':'Full interval coverage and integral enclosures; analytic error formulas in manuscript sections 9-10.',
            'cells':rows}
    write_result('profile_certificate.json',result,output_dir)
    return {'max_ratio':max_ratio,'min_variance':min_v,'report':result}


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output-dir')
    certify(parser.parse_args().output_dir)
