# IE-03 isolated Linux verification

The [IE-03 verification job](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/42710286364) passed the repository's pinned,
unprivileged Linux harness on 2026-11-09. The project snapshot matched the
reviewed proof revision `89987eb5059ce5a497c18ce50c9b86f8cf394b86`. The GitHub Actions checkout was
`ba2e527285c775f16a685453926ef200f7706660`.

[Comparator output](comparator.log) records successful statement comparison
and acceptance by Lean's default kernel. [The receipt](result.json) binds all
35 input files to SHA-256 hashes, the approved axiom
list, the pinned verifier source lock, and the tool bootstrap receipt. Both
exports have a [local transitive axiom report](../local-build-and-axioms.log).
The run also executed the repository's sandbox and rejection controls.
