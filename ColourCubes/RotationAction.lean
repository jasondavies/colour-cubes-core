module

public import ColourCubes.Physical
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace ColourCubes
open scoped BigOperators

variable {α ι : Type*}

/-- Rotate a face assignment; face colours themselves remain fixed. -/
def rotate (c : Cube α) (r : Fin 24) : Cube α := fun f => c (rotations r f)

namespace Geometry

/-- The binary corner position obtained by rotating its three outward faces. -/
def rotatedSlot (r : Fin 24) (k : Fin 8) : Fin 8 :=
  Fin.ofNat 8 (∑ f : Fin 3,
    let face := rotations r (exposedFaces k f)
    face.val % 2 * 2 ^ (2 - face.val / 2))

lemma rotatedSlot_bijective : ∀ r, Function.Bijective (rotatedSlot r) := by
  decide +kernel

noncomputable def slotEquiv (r : Fin 24) : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective (rotatedSlot r) (rotatedSlot_bijective r)

lemma rotatedSlot_frame : ∀ (r : Fin 24) (k : Fin 8), ∃ s : Fin 3, ∀ f,
    rotations r (frame k f) = frame (slotEquiv r k) (f + s) := by
  decide +kernel

lemma rotated_corner (t : Cube α) (r : Fin 24) (k : Fin 8) :
    CyclicEq (corner t (slotEquiv r k)) (corner (rotate t r) k) := by
  obtain ⟨s, hs⟩ := rotatedSlot_frame r k
  exact ⟨s, fun f => congrArg t (hs f).symm⟩

end Geometry

open ColourCubes.Geometry

/-- Rotating a source preserves the corners it can supply. -/
theorem fits_rotate_source (c t : Cube α) (r : Fin 24) (k : Fin 8) :
    TableFits (rotate c r) t k ↔ TableFits c t k := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨u, hu⟩ := rotation_composition r s
    refine ⟨u, fun f => ?_⟩
    rw [hu]
    exact hs f
  · rintro ⟨s, hs⟩
    obtain ⟨v, hv⟩ := rotation_inverse r
    obtain ⟨u, hu⟩ := rotation_composition v s
    refine ⟨u, fun f => ?_⟩
    change c (rotations r (rotations u (exposedFaces k f))) = _
    rw [hu, hv]
    exact hs f

/-- Rotating a target only permutes its eight requirements. -/
theorem fits_rotate_target (c t : Cube α) (r : Fin 24) (k : Fin 8) :
    TableFits c (rotate t r) k ↔ TableFits c t (slotEquiv r k) := by
  rw [TableFits, TableFits, corner_rotation_iff, corner_rotation_iff]
  constructor
  · rintro ⟨l, h⟩
    exact ⟨l, cyclicEq_trans h (cyclicEq_symm (rotated_corner t r k))⟩
  · rintro ⟨l, h⟩
    exact ⟨l, cyclicEq_trans h (rotated_corner t r k)⟩

/-- A target and any rotation of it can be built from exactly the same
collections of eight distinct physical copies. -/
theorem builds_rotate (cubes : ι → Cube α) (t : Cube α) (r : Fin 24) :
    Builds cubes (rotate t r) ↔ Builds cubes t := by
  simp only [builds_iff_tableFits]
  constructor
  · rintro ⟨p, h⟩
    refine ⟨(slotEquiv r).symm.toEmbedding.trans p, fun k => ?_⟩
    simpa using (fits_rotate_target _ _ _ _).mp (h ((slotEquiv r).symm k))
  · rintro ⟨p, h⟩
    exact ⟨(slotEquiv r).toEmbedding.trans p, fun k =>
      (fits_rotate_target _ _ _ _).mpr (by simpa using h (slotEquiv r k))⟩

end ColourCubes
