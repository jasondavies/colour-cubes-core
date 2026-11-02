module

public import ColourCubes.GeometryDefs
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace ColourCubes

theorem rotation_table_valid : ∀ n : Fin 24,
    ValidAxes (rotations n 0) (rotations n 2) (rotations n 4) ∧
    rotations n = fromAxes (rotations n 0) (rotations n 2) (rotations n 4) := by
  decide +kernel

theorem rotation_table_complete : ∀ a b c : Fin 6, ValidAxes a b c →
    ∃ n : Fin 24, fromAxes a b c = rotations n := by decide +kernel

theorem proper_rotation_iff (r : Fin 6 → Fin 6) :
    ProperRotation r ↔ ∃ n : Fin 24, r = rotations n := by
  constructor
  · rintro ⟨a,b,c,h,rfl⟩
    exact rotation_table_complete a b c h
  · rintro ⟨n,rfl⟩
    exact ⟨_,_,_,rotation_table_valid n⟩

/-- Quantifying over geometric proper rotations is the same as quantifying
over indices in the verified rotation table. -/
theorem exists_proper_rotation_iff (P : (Fin 6 → Fin 6) → Prop) :
    (∃ r, ProperRotation r ∧ P r) ↔ ∃ n : Fin 24, P (rotations n) := by
  constructor
  · rintro ⟨r, hr, h⟩
    obtain ⟨n, rfl⟩ := (proper_rotation_iff r).mp hr
    exact ⟨n, h⟩
  · rintro ⟨n, h⟩
    exact ⟨rotations n, (proper_rotation_iff _).mpr ⟨n, rfl⟩, h⟩

theorem rotations_bijective : ∀ n : Fin 24, Function.Bijective (rotations n) := by
  decide +kernel

theorem rotations_distinct : Function.Injective rotations := by decide +kernel

theorem rotation_inverse : ∀ r : Fin 24, ∃ s : Fin 24,
    ∀ f : Fin 6, rotations r (rotations s f) = f := by decide +kernel

theorem rotation_composition : ∀ r s : Fin 24, ∃ t : Fin 24,
    ∀ f : Fin 6, rotations t f = rotations r (rotations s f) := by decide +kernel

/-- The three outward faces at each of the eight binary cube positions. -/
theorem exposed_face_rule : ∀ k : Fin 8, ∀ d : Fin 3,
    (exposedFaces k d).val = 2*d.val + (k.val / 2^(2-d.val)) % 2 := by decide +kernel

end ColourCubes
