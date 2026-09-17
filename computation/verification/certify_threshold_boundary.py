"""Certify the active endpoint cutoff at fixed w_max; not global optimality."""
import argparse
from common import metadata,write_result
from parameters import THRESHOLD
from mpmath import iv
def certify(output_dir=None):
 iv.dps=60;I=iv.mpf;w=I('0.0013');floor=(2*iv.pi**2/15)/(25*w*w)
 above=I(THRESHOLD)-floor;below=floor-(THRESHOLD-1)
 assert bool(above.a>0) and bool(below.a>0)
 data={**metadata('fixed-endpoint cutoff interval certificate'),'status':'passed',
       'decimal_precision':60,'threshold':THRESHOLD,'fixed_w_max':'0.0013',
       'cutoff_interval':str(floor),'threshold_minus_cutoff':str(above),
       'cutoff_minus_previous_integer':str(below),
       'scope':'Smallest integer satisfying C/(25*w_max^2) <= n at this fixed w_max. Does not prove a globally optimal analytic threshold.'}
 write_result('threshold_boundary_certificate.json',data,output_dir);return data
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output-dir');certify(p.parse_args().output_dir)
