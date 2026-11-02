# colour-cubes-core

Lean definitions and proofs for face-coloured cubes, for any palette:
proper rotations, corner types, and assembling eight cubes into a 2×2×2 target.
Depends only on mathlib (Lean and mathlib v4.35.0).

## Model

- `ColourCubes.Cube α` colours the six faces from an arbitrary palette `α`.
  `Uses n c` says that exactly `n` colours occur; `UsesAllColours c` says that
  every colour of `α` occurs.
- `Fits c t k` holds when a proper rotation of `c` matches the three exterior
  faces of `t` at corner position `k`.
- `Builds cubes target` holds when eight distinct copies from `cubes`
  fit the eight corner positions of `target`. Internal faces impose no conditions.
- `HasSolution allowed cubes` asks for some target satisfying `allowed` that
  `cubes` builds, so each application chooses its own target condition.

The main theorem, `fits_iff_corner`, states that a cube fits a corner position
exactly when it has a corner of the same cyclic type. It holds for any palette
and allows repeated colours.

## Modules

- `GeometryDefs`, `Geometry`: coordinate faces, the 24 proper rotations,
  inverses, composition and exposed faces.
- `Corners`: oriented corner types and the corner–rotation theorem.
- `PhysicalDefs`, `Physical`: the common model; geometric proper rotations
  agree with the verified 24-entry table.
- `RotationAction`: how rotations permute corner positions, and rotation invariance.

The `…Defs` modules contain only definitions. Comparator challenges should copy
the definitions they need rather than import this library, which would defeat
the separation between statements and proofs. Each consuming project's
comparator run checks its copies against the originals here.

## Use

```toml
[[require]]
name = "colour_cubes_core"
git = "https://github.com/jasondavies/colour-cubes-core.git"
rev = "<full commit SHA>"
```

Pin a full commit SHA, noting the release tag beside it. Any change to a
definition gets a new major version, so published results keep their pins.

## Checks

```sh
lake exe cache get
make check
```

This builds the library, rejects proof holes, `native_decide` and non-mathlib
imports, and checks that every public theorem in `Audit.lean` uses only
`propext`, `Classical.choice` and `Quot.sound`. No cube catalogues,
colour-specific theorems or certificate archives are included.

Written for
[four-to-three-colour-cubes](https://github.com/jasondavies/four-to-three-colour-cubes)
and [five-colour-cubes](https://github.com/jasondavies/five-colour-cubes).
Code is distributed under the [Apache-2.0 licence](LICENSE).
