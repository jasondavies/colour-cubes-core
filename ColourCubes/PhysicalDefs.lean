module

public import ColourCubes.GeometryDefs

@[expose] public section

namespace ColourCubes

/-- Face colours from an arbitrary palette; colours may repeat. -/
abbrev Cube (α : Type*) := Fin 6 → α

/-- Exactly `n` distinct colours occur on the six faces. -/
def Uses {α : Type*} [DecidableEq α] (n : ℕ) (c : Cube α) : Prop :=
  (Finset.univ.image c).card = n

instance {α : Type*} [DecidableEq α] (n : ℕ) (c : Cube α) : Decidable (Uses n c) := by
  unfold Uses
  infer_instance

/-- Every colour in the palette occurs. -/
def UsesAllColours {α : Type*} (c : Cube α) : Prop := ∀ a, ∃ f, c f = a

instance {α : Type*} [Fintype α] [DecidableEq α] (c : Cube α) :
    Decidable (UsesAllColours c) := by
  unfold UsesAllColours
  infer_instance

/-- Matching by an index in the verified rotation table. -/
def TableFits {α : Type*} (c t : Cube α) (k : Fin 8) : Prop :=
  ∃ r : Fin 24, ∀ f : Fin 3,
    c (rotations r (exposedFaces k f)) = t (exposedFaces k f)

/-- Matching the three exterior faces by a geometric proper rotation. -/
def Fits {α : Type*} (c t : Cube α) (k : Fin 8) : Prop :=
  ∃ r : Fin 6 → Fin 6, ProperRotation r ∧ ∀ f : Fin 3,
    c (r (exposedFaces k f)) = t (exposedFaces k f)

/-- Build a specified target using eight distinct indexed copies. -/
def Builds {α ι : Type*} (cubes : ι → Cube α) (target : Cube α) : Prop :=
  ∃ placement : Fin 8 ↪ ι, ∀ k, Fits (cubes (placement k)) target k

/-- Each application chooses its own admissible target predicate. -/
def HasSolution {α ι : Type*} (allowed : Cube α → Prop) (cubes : ι → Cube α) : Prop :=
  ∃ target, allowed target ∧ Builds cubes target

end ColourCubes
