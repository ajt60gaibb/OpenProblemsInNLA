"""Generate only the export wrappers from the reviewed, unchanged Challenge."""
from pathlib import Path
import hashlib
import re

P = Path(__file__).resolve().parents[2]
raw = (P / 'Challenge.lean').read_bytes()
assert hashlib.sha256(raw).hexdigest() == '6dfe1fe49431bd3f5dc4c91360911d02c6aaf73d902a40fcabec79155fb11c18'
source = raw.decode()
arguments = {
    'orderedSpectral_exists': ' A hA',
    'orderedSpectral_semantics': ' d',
    'functionalCalculus_spectral': ' d f',
    'spectral_tail_norms': ' d k hk f hf',
    'operator_rayleigh_bound': ' A x',
    'witness_data': '',
    'witness_spectral_location': '',
    'minorant_scalar': ' x hx hgap',
    'minorant_functional_calculus': '',
    'witness_tail_data': ' dA dAhat',
    'witness_rational_certificate': '',
    'numerical_gap_positive': '',
    'counterexample': ' dA dAhat',
    'not_concaveSpectralTransferConjecture': '',
}
assert re.findall(r'^theorem (\w+)', source, re.M) == list(arguments)
def replace(m):
    name = re.match(r'theorem (\w+)', m.group()).group(1)
    return m.group().replace('  sorry', '  exact ' + name + '_proved' + arguments[name])
source, count = re.subn(r'theorem \w+[\s\S]*?:= by\n  sorry', replace, source)
assert count == 14 and 'sorry' not in source
start = source.index('set_option autoImplicit false')
source = '''/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact exports of the independently reviewed RA-08 Challenge contracts.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.RA08.Proof

''' + source[start:]
audits = '\n'.join('#assert_trust kernel ' + n + '\n#print axioms ' + n for n in arguments)
source = source.replace('end NLA.RA08', audits + '\n\nend NLA.RA08')
(P / 'Solution.lean').write_text(source)
print('Created Solution.lean with all 14 original contracts and no Challenge import.')
