# Independent canonical-color and class-recovery review

Reviewer: `/root`, OpenAI Codex AI agent, 17 October 2026. APPROVE for these
other-agent support modules. This report does not approve my own modules,
assert a complete unique-coefficient theorem, or certify an SP-11 solution.

CanonicalColoring defines actual recursive color choices. Every normal child
receives its zero-based position and the root cap is supplied above its arity.
The all-node arity bound makes every Fin color valid. The NormalStructure
child-arity bound ensures recursive normal colorings are admissible; local
injectivity excludes exactly the root cap and distinguishes all child slots.
Inserted colorings use Fin.succAbove to skip the cap slot, so every root
incident color is distinct, and child colors only increase from their ordinary
positions. These predicates are separately proved for actual lssGarden trees
from the concrete OrderedGreedy source facts. They are not assumed as a
faithfulness condition.

ColorRigidity is a finite, label-founded recovery theorem. Strictly earlier
children have already recovered outputs at the class step. Their finite sums
can consequently be canceled from equality of class incident sums. Explicit
local reconstruction premises give each output its canonical lower bound;
equality of the output sums then gives pointwise equality. The blockers form
uses only an earlier tied output or an earlier conduit for every smaller
color, with actual inequality of the two conduit colors. The theorem leaves
these concrete shape premises explicit; it does not certify that the paired
LSS trees satisfy them until a later source bridge is proved.

LSSLabelBounds keeps actual occurrence paths. A childOccurrence is the actual
child root at the selected slot of the selected occurrence; its output color
is proved equal to the parent input color. HasChildLabels and DescendingLabels
are proved for actual earlier-nonneighbor recursion, with strict labels on
children and sibling roots. Therefore every descendant label is below its
root, and only the actual root occurrence has its root's label. Empty child
lists and repeated labels in separate subtrees are retained.

DoubleHistogramWeights derives local injectivity from a nonzero actual
paired sign product. The concrete sorted-subset coordinate-sum weight reads
exactly every occurrence's incident-color sum in its original vertex class.
Linearity transfers equality of the actual shared-variable exponent arrays to
equality of those class sums. Repeated occurrences are included with their
multiplicities; invalid zero-coefficient colorings are excluded only by the
explicit nonzero-sign premise. No extra coefficient-independence assumption
is inserted. The full source uses the genuine SharedVariable Sigma type.

I read the complete files and independently recompiled them with the pinned
runtime. Their source-level kernel checks and printed axiom closures pass with
foundational subsets. The actual paired-tree blocker bridge and unique nonzero
coefficient still remain necessary for the original target.

## Reviewed source SHA-256

- `lean-statements/NLA/Proofs/SP11/CanonicalColoring.lean`: `bc1e9ea1cccf8c9805f28c7b0a5062a3fa871c7a2d1e472b8d1609c57faf9830`
- `lean-statements/NLA/Proofs/SP11/ColorRigidity.lean`: `0454ea402344587a986a46a9e11307bd8d7e409af0b5182047dfeaa66167bc41`
- `lean-statements/NLA/Proofs/SP11/LSSLabelBounds.lean`: `3374decce83cc1d911a4323438137f41fe99f74ed6d5b3f249bfa7717c08a49b`
- `lean-statements/NLA/Proofs/SP11/DoubleHistogramWeights.lean`: `b930e37ee7b17e0c4282b0be0d1162df133d19620a49995cac6e056482d5aecb`

The final DoubleHistogramWeights proof was restored after a cosmetic cleanup
caused a Decidable-instance elaboration failure. I independently recompiled
the restored final source; the mathematical statement is unchanged. The
failed cleanup was not accepted as evidence.
