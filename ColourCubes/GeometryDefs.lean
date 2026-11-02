module

public import Mathlib

@[expose] public section

namespace ColourCubes

abbrev Face := Fin 6
abbrev Slot := Fin 8
def exposedFaces : Slot → Fin 3 → Fin 6 := ![![0, 2, 4], ![0, 2, 5], ![0, 3, 4], ![0, 3, 5], ![1, 2, 4], ![1, 2, 5], ![1, 3, 4], ![1, 3, 5]]

def rotations : Fin 24 → Fin 6 → Fin 6 := ![![0, 1, 2, 3, 4, 5], ![0, 1, 3, 2, 5, 4], ![0, 1, 4, 5, 3, 2], ![0, 1, 5, 4, 2, 3], ![1, 0, 2, 3, 5, 4], ![1, 0, 3, 2, 4, 5], ![1, 0, 4, 5, 2, 3], ![1, 0, 5, 4, 3, 2], ![2, 3, 0, 1, 5, 4], ![2, 3, 1, 0, 4, 5], ![2, 3, 4, 5, 0, 1], ![2, 3, 5, 4, 1, 0], ![3, 2, 0, 1, 4, 5], ![3, 2, 1, 0, 5, 4], ![3, 2, 4, 5, 1, 0], ![3, 2, 5, 4, 0, 1], ![4, 5, 0, 1, 2, 3], ![4, 5, 1, 0, 3, 2], ![4, 5, 2, 3, 1, 0], ![4, 5, 3, 2, 0, 1], ![5, 4, 0, 1, 3, 2], ![5, 4, 1, 0, 2, 3], ![5, 4, 2, 3, 0, 1], ![5, 4, 3, 2, 1, 0]]

theorem faceOne_bound : 1 < 6 := by decide

def opposite (f : Fin 6) : Fin 6 :=
  if f.val % 2 = 0 then f + ⟨1, faceOne_bound⟩ else f - ⟨1, faceOne_bound⟩
def fromAxes (a b c : Fin 6) : Fin 6 → Fin 6 :=
  ![a, opposite a, b, opposite b, c, opposite c]

/-- Distinct coordinate axes and determinant +1. -/
def ValidAxes (a b c : Fin 6) : Prop :=
  a.val / 2 ≠ b.val / 2 ∧ a.val / 2 ≠ c.val / 2 ∧ b.val / 2 ≠ c.val / 2 ∧
  (a.val % 2 + b.val % 2 + c.val % 2) % 2 =
    ((if a.val / 2 > b.val / 2 then 1 else 0) +
     (if a.val / 2 > c.val / 2 then 1 else 0) +
     (if b.val / 2 > c.val / 2 then 1 else 0)) % 2
instance (a b c : Fin 6) : Decidable (ValidAxes a b c) := by
  unfold ValidAxes; infer_instance

def ProperRotation (r : Fin 6 → Fin 6) : Prop :=
  ∃ a b c, ValidAxes a b c ∧ r = fromAxes a b c

end ColourCubes
