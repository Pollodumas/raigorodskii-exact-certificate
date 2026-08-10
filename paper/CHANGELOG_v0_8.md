# Changes in v0.8

- Repaired a broken inline LaTeX command in the Markdown audit: `p\nmid\operatorname{disc}(R)` now renders correctly.
- Added exact assertions in both distributed verifiers that the rational isolating endpoints for the optimizer satisfy `s2 - s1 = 10^-18`, matching the manuscript's statement that they are consecutive at 18 decimal places.
- Updated all package names and internal references consistently from v0.7 to v0.8.
- Recompiled and visually inspected the PDF, reran both exact verifiers from a fresh ZIP extraction, and regenerated and checked every SHA-256 checksum.
