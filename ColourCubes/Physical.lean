module

public import ColourCubes.Corners
public import ColourCubes.PhysicalDefs

@[expose] public section

namespace ColourCubes

/-- The table and geometric notions of a proper rotation agree. -/
theorem fits_iff_tableFits {α : Type*} (c t : Cube α) (k : Fin 8) :
    Fits c t k ↔ TableFits c t k :=
  exists_proper_rotation_iff _

instance {α : Type*} [DecidableEq α] (c t : Cube α) (k : Fin 8) : Decidable (Fits c t k) :=
  decidable_of_iff _ (fits_iff_tableFits c t k).symm

theorem fits_iff_corner {α : Type*} (c t : Cube α) (k : Fin 8) :
    Fits c t k ↔ ∃ l, Geometry.CyclicEq (Geometry.corner c l) (Geometry.corner t k) :=
  Geometry.corner_proper_rotation_iff c t k

/-- A solution can equivalently select indices in the finite rotation table. -/
theorem builds_iff_tableFits {α ι : Type*} (cubes : ι → Cube α) (target : Cube α) :
    Builds cubes target ↔ ∃ p : Fin 8 ↪ ι, ∀ k, TableFits (cubes (p k)) target k := by
  simp only [Builds, fits_iff_tableFits]

end ColourCubes
