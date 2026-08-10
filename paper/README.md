# Manuscript

This directory contains the source and rendered PDF for draft v0.8:

- `Raigorodskii_Exact_Certificate_Draft_v0_8.tex`
- `Raigorodskii_Exact_Certificate_Draft_v0_8.pdf`
- `CHANGELOG_v0_8.md`

Rebuild with:

```bash
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error Raigorodskii_Exact_Certificate_Draft_v0_8.tex
```

Draft v0.8 is not peer reviewed. Corrections should produce a new immutable version rather than silently replacing these artifacts.
