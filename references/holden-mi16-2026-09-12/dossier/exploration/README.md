# Uncertified numerical exploration

These local Riemannian-gradient searches were used to test structural guesses.
They are floating-point computations with multiple random starts, not exhaustive
searches or global-optimality certificates. No claimed theorem relies on them.

`numerical_results.json` records approximate local objective values, gradients,
and matrices. Coincidence between real and complex searches is not a proof that
real matrices suffice in general. NumPy and SciPy are optional dependencies for
rerunning this exploratory script; they are not needed for the exact core.
