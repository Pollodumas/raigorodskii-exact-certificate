# Publication checklist

## Before release

1. Wait for independent human review of the mathematical argument and bibliographic context.
2. Incorporate any corrections into a new manuscript version rather than silently changing v0.8.
3. Run both exact verifiers from a fresh clone.
4. Run the pinned Lean build and confirm the core contains no placeholder proofs.
5. Recompile the PDF from the committed LaTeX source.
6. Regenerate and verify `SHA256SUMS`.
7. Confirm that the abstract and README do not claim an improved chromatic bound or a solution of Erdős Problem 704.
8. Confirm the disclosure accurately describes the multi-model AI-assisted workflow.

## Suggested release artifacts

- `Raigorodskii_Exact_Certificate_Draft_v0_8.pdf`
- source LaTeX and changelog
- both verification scripts and pinned requirements
- exhaustive audit
- Lean source, toolchain, Lake configuration, and manifest
- `SHA256SUMS`

## Versioning policy

Published artifacts are immutable. Corrections should produce v0.9 or v1.0 with an explicit changelog. The current v0.8 remains a review draft until a specialist has assessed correctness, significance, attribution, and priority.
