module

public import ColourCubes.Corners
public import ColourCubes.PhysicalDefs

@[expose] public section

namespace ColourCubes

/-- The table and geometric notions of a proper rotation agree. -/
theorem fits_iff_tableFits {α : Type*} (c t : Cube α) (k : Fin 8) :
    Fits c t k ↔ TableFits c t k := by
  constructor
  · rintro ⟨r, hr, h⟩
    obtain ⟨n, rfl⟩ := (proper_rotation_iff r).mp hr
    exact ⟨n, h⟩
  · rintro ⟨n, h⟩
    exact ⟨rotations n, (proper_rotation_iff _).mpr ⟨n, rfl⟩, h⟩

theorem fits_iff_corner {α : Type*} (c t : Cube α) (k : Fin 8) :
    Fits c t k ↔ ∃ l, Geometry.CyclicEq (Geometry.corner c l) (Geometry.corner t k) :=
  Geometry.corner_proper_rotation_iff c t k

/-- A solution can equivalently select indices in the finite rotation table. -/
theorem builds_iff_tableFits {α ι : Type*} (cubes : ι → Cube α) (target : Cube α) :
    Builds cubes target ↔ ∃ p : Fin 8 ↪ ι, ∀ k, TableFits (cubes (p k)) target k := by
  simp only [Builds, fits_iff_tableFits]

end ColourCubes
