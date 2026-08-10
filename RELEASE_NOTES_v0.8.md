# Release notes v0.8

This release packages the exact algebraic certificate for the Raigorodskii lower-bound constant.

Included:

- manuscript v0.8 in PDF and LaTeX;
- independent SymPy and Python-standard-library verifiers;
- detailed adversarial audit;
- pinned Lean 4.32.1 and Mathlib 4.32.1 project;
- placeholder-free Lean core covering the optimizer, elimination identity, sextic relation, exact enclosures, and integrality of `6 gamma_R`;
- reproducibility workflow and citation metadata.

The full exact-arithmetic certificate proves irreducibility, exactly two real roots, minimal scaling factor `6`, and the `S_6` Galois-group conclusion. The Lean companion is explicitly partial and does not overstate those claims.
