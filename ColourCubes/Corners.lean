module

public import ColourCubes.Geometry
public import Mathlib.Algebra.Group.Fin.Basic

@[expose] public section

namespace ColourCubes.Geometry

/-- Reorder each corner's coordinate faces with consistent orientation. -/
def cornerOrder : Fin 8 → Fin 3 → Fin 3 :=
  ![![0,1,2], ![0,2,1], ![0,2,1], ![0,1,2],
    ![0,2,1], ![0,1,2], ![0,1,2], ![0,2,1]]

def frame (k : Fin 8) (f : Fin 3) : Fin 6 :=
  ColourCubes.exposedFaces k (cornerOrder k f)

lemma cornerOrder_involutive : ∀ k f, cornerOrder k (cornerOrder k f) = f := by
  decide +kernel

/-- A rotation takes an oriented corner frame to a cyclic shift of another. -/
lemma rotated_frame : ∀ (k : Fin 8) (r : Fin 24),
    ∃ (l : Fin 8) (s : Fin 3), ∀ f,
      ColourCubes.rotations r (frame k f) = frame l (f + s) := by
  decide +kernel

/-- Every cyclic alignment of two oriented corner frames is realised by a rotation. -/
lemma align_frame : ∀ (k l : Fin 8) (s : Fin 3),
    ∃ r : Fin 24, ∀ f,
      ColourCubes.rotations r (frame k f) = frame l (f + s) := by
  decide +kernel

/-- The ordered colours of a corner, for an arbitrary palette. -/
def corner {α : Type*} (c : Fin 6 → α) (k : Fin 8) : Fin 3 → α :=
  fun f => c (frame k f)

/-- Equality of oriented triples up to cyclic shift. -/
def CyclicEq {α : Type*} (a b : Fin 3 → α) : Prop :=
  ∃ s : Fin 3, ∀ f, a (f + s) = b f

instance {α : Type*} [DecidableEq α] (a b : Fin 3 → α) : Decidable (CyclicEq a b) := by
  unfold CyclicEq
  infer_instance

lemma cyclicEq_trans {α : Type*} {a b c : Fin 3 → α} (hab : CyclicEq a b)
    (hbc : CyclicEq b c) : CyclicEq a c := by
  obtain ⟨s, hs⟩ := hab
  obtain ⟨t, ht⟩ := hbc
  refine ⟨t + s, fun f => ?_⟩
  rw [← add_assoc, hs, ht]

lemma cyclicEq_symm {α : Type*} {a b : Fin 3 → α} (h : CyclicEq a b) : CyclicEq b a := by
  obtain ⟨s, hs⟩ := h
  refine ⟨-s, fun f => ?_⟩
  simpa using (hs (f + -s)).symm

/-- A cube fits a target corner precisely when it has the same cyclic corner type.
This statement is independent of the palette and allows repeated colours. -/
theorem corner_rotation_iff {α : Type*} (c t : Fin 6 → α) (k : Fin 8) :
    (∃ r : Fin 24, ∀ f : Fin 3,
      c (ColourCubes.rotations r (ColourCubes.exposedFaces k f)) =
        t (ColourCubes.exposedFaces k f)) ↔
    ∃ l : Fin 8, CyclicEq (corner c l) (corner t k) := by
  constructor
  · rintro ⟨r, h⟩
    obtain ⟨l, s, hs⟩ := rotated_frame k r
    refine ⟨l, s, fun f => ?_⟩
    change c (frame l (f + s)) = t (frame k f)
    rw [← hs f]
    exact h (cornerOrder k f)
  · rintro ⟨l, s, h⟩
    obtain ⟨r, hr⟩ := align_frame k l s
    refine ⟨r, fun f => ?_⟩
    have hf := h (cornerOrder k f)
    change c (frame l (cornerOrder k f + s)) = t (frame k (cornerOrder k f)) at hf
    rw [← hr (cornerOrder k f)] at hf
    simpa only [frame, cornerOrder_involutive] using hf

/-- The same correspondence expressed using geometric proper rotations rather
than indices in the verified rotation table. -/
theorem corner_proper_rotation_iff {α : Type*} (c t : Fin 6 → α) (k : Fin 8) :
    (∃ r : Fin 6 → Fin 6, ColourCubes.ProperRotation r ∧ ∀ f : Fin 3,
      c (r (ColourCubes.exposedFaces k f)) = t (ColourCubes.exposedFaces k f)) ↔
    ∃ l : Fin 8, CyclicEq (corner c l) (corner t k) :=
  (ColourCubes.exists_proper_rotation_iff _).trans (corner_rotation_iff c t k)

end ColourCubes.Geometry
