module

public import ColourCubes.Physical

@[expose] public section

namespace ColourCubes.Geometry
open scoped BigOperators

/-- The binary corner position obtained by rotating its three outward faces. -/
def rotatedSlot (r : Fin 24) (k : Fin 8) : Fin 8 :=
  Fin.ofNat 8 (∑ f : Fin 3,
    let face := ColourCubes.rotations r (ColourCubes.exposedFaces k f)
    face.val % 2 * 2 ^ (2 - face.val / 2))

lemma rotatedSlot_bijective : ∀ r, Function.Bijective (rotatedSlot r) := by
  decide +kernel

noncomputable def slotEquiv (r : Fin 24) : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective (rotatedSlot r) (rotatedSlot_bijective r)

lemma rotatedSlot_frame : ∀ (r : Fin 24) (k : Fin 8), ∃ s : Fin 3, ∀ f,
    ColourCubes.rotations r (frame k f) = frame (slotEquiv r k) (f + s) := by
  decide +kernel

variable {α : Type*}

/-- Rotate a face assignment; face colours themselves remain fixed. -/
def rotate (c : Cube α) (r : Fin 24) : Cube α := fun f => c (ColourCubes.rotations r f)

/-- Rotating a source preserves the corners it can supply. -/
theorem fits_rotate_source (c t : Cube α) (r : Fin 24) (k : Fin 8) :
    TableFits (rotate c r) t k ↔ TableFits c t k := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨u, hu⟩ := ColourCubes.rotation_composition r s
    refine ⟨u, fun f => ?_⟩
    rw [hu]
    exact hs f
  · rintro ⟨s, hs⟩
    obtain ⟨v, hv⟩ := ColourCubes.rotation_inverse r
    obtain ⟨u, hu⟩ := ColourCubes.rotation_composition v s
    refine ⟨u, fun f => ?_⟩
    change c (ColourCubes.rotations r (ColourCubes.rotations u (ColourCubes.exposedFaces k f))) = _
    rw [hu, hv]
    exact hs f

lemma cyclicEq_trans {a b c : Fin 3 → α} (hab : CyclicEq a b)
    (hbc : CyclicEq b c) : CyclicEq a c := by
  obtain ⟨s, hs⟩ := hab
  obtain ⟨t, ht⟩ := hbc
  refine ⟨t + s, fun f => ?_⟩
  rw [← add_assoc, hs, ht]

lemma cyclicEq_symm {a b : Fin 3 → α} (h : CyclicEq a b) : CyclicEq b a := by
  obtain ⟨s, hs⟩ := h
  refine ⟨-s, fun f => ?_⟩
  simpa using (hs (f + -s)).symm

lemma rotated_corner (t : Cube α) (r : Fin 24) (k : Fin 8) :
    CyclicEq (corner t (slotEquiv r k)) (corner (rotate t r) k) := by
  obtain ⟨s, hs⟩ := rotatedSlot_frame r k
  exact ⟨s, fun f => congrArg t (hs f).symm⟩

/-- Rotating a target only permutes its eight requirements. -/
theorem fits_rotate_target (c t : Cube α) (r : Fin 24) (k : Fin 8) :
    TableFits c (rotate t r) k ↔ TableFits c t (slotEquiv r k) := by
  rw [TableFits, TableFits, corner_rotation_iff, corner_rotation_iff]
  constructor
  · rintro ⟨l, h⟩
    exact ⟨l, cyclicEq_trans h (cyclicEq_symm (rotated_corner t r k))⟩
  · rintro ⟨l, h⟩
    exact ⟨l, cyclicEq_trans h (rotated_corner t r k)⟩

/-- A solution of a rotated target gives a solution of its representative,
with the same eight distinct physical copies. -/
theorem unrotate_solution {n : Nat} (cubes : Fin n → Cube α) (t : Cube α) (r : Fin 24)
    (copies : Fin 8 ↪ Fin n) (h : ∀ k, TableFits (cubes (copies k)) (rotate t r) k) :
    ∃ copies' : Fin 8 ↪ Fin n, ∀ k, TableFits (cubes (copies' k)) t k := by
  refine ⟨(slotEquiv r).symm.toEmbedding.trans copies, fun k => ?_⟩
  have hk := (fits_rotate_target _ _ _ _).mp (h ((slotEquiv r).symm k))
  simpa using hk

end ColourCubes.Geometry
