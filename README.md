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

Geometry was extracted from Jason Davies's projects:

- [Six-colour rotations](https://github.com/jasondavies/macmahon-min-universal-sets/tree/3f854795a77cd7c902e4c5a1a5da3322f9cd44fa), including the rotation and exposed-face definitions.
- [Four-to-three corner geometry](https://github.com/jasondavies/four-to-three-colour-cubes/tree/d69d92b2c7ba725f986054d8f1157c88b0a0eafa), including the palette-independent matching theorem and corner-position permutations.
- [Five-colour rotation transport](https://github.com/jasondavies/five-colour-cubes/tree/c959cc786bade7d479fae74d8fcc64a76bf1f93b), generalised here to arbitrary palettes.

The extraction and generalisation were developed with OpenAI Codex under the
author's direction. The original research attribution remains in those projects.
Code is distributed under the Apache-2.0 licence.
