# Colour cubes core

Palette-independent Lean definitions and proofs for face-coloured cubes,
proper rotations and corner assembly. Requires Lean and mathlib v4.35.0.

`ColourCubes.Cube α` is a face map with arbitrary palette `α`.
`Builds cubes target` selects eight distinct copies and proper rotations matching
their exterior faces. `HasSolution allowed cubes` lets each application specify
which targets are allowed. Internal faces impose no conditions.

- `GeometryDefs` and `Geometry`: coordinate faces, the 24 proper rotations,
  inverses, composition and exposed faces.
- `Corners`: oriented corner types and their equivalence to physical matching.
- `PhysicalDefs` and `Physical`: the common model and equivalence of geometric
  rotations with the verified finite rotation table.
- `RotationAction`: corner-position permutations and rotation invariance.

No cube catalogues, colour-specific theorems or certificate archives are imported.
The library depends only on mathlib.

Run `lake exe cache get`, then `make check` to build and audit the public theorems.

Comparator challenges should copy the required definitions locally and import
only their approved canonical libraries. Importing this proof library into a
Palomar challenge would defeat that separation. The consuming papers check
agreement of their local restatements with this library through the comparator.

Geometry was extracted from Jason Davies's `macmahon-min-universal-sets`,
`four-to-three-colour-cubes` and `macmahon-five-colour-threshold` projects.
The extraction and generalisation were developed with OpenAI Codex under the
author's direction. The original research attribution remains in those projects.
Code is distributed under the Apache-2.0 licence.
