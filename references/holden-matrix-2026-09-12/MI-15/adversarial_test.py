#!/usr/bin/env python3
"""Ensure deliberately invalid certificates are rejected by the exact checker."""
from copy import deepcopy
from pathlib import Path
import json
from verify_exact import gram_from_certificate,check_polynomial,check_psd

def expect_failure(data,label):
 try:
  pairs,Q=gram_from_certificate(data)
  check_polynomial(data['n'],data['gram_denominator'],pairs,Q)
  check_psd(data,pairs,Q)
 except AssertionError:
  return {'mutation':label,'result':'REJECTED AS EXPECTED'}
 raise AssertionError('Invalid certificate was accepted: '+label)

def main():
 d=json.loads((Path(__file__).parent/'certificates/n8.json').read_text())
 a=deepcopy(d)
 for row in a['plucker_coefficients']:
  if row[0]==-7 and row[3]==7:
   row[4]+=1;break
 else:raise AssertionError('No expected forced coefficient found')
 b=deepcopy(d)
 for row in b['congruence_numerators']:row[0]=0
 print(json.dumps([expect_failure(a,'one-unit change in a forced Plucker numerator'),
                   expect_failure(b,'zero first column of congruence matrix')],indent=2))

if __name__=='__main__':main()
