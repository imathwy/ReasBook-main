import Mathlib.Topology.Category.TopCat.Basic

open CategoryTheory

universe u

/-- An expanding sequence of subspaces whose union is the whole ambient space `X`. -/
structure ExpandingUnion (X : TopCat.{u}) where
  /-- The `n`-th stage `X_n ⊆ X` of the expanding sequence. -/
  stage : ℕ → Set X
  /-- The stages are nested increasingly. -/
  mono : Monotone stage
  /-- The union of the stages is all of `X`. -/
  iUnion_eq_univ : (⋃ n : ℕ, stage n) = Set.univ

namespace ExpandingUnion

variable {X : TopCat.{u}}

/-- The `n`-th stage of an expanding union, viewed as a bundled topological space. -/
abbrev stageSpace (U : ExpandingUnion X) (n : ℕ) : TopCat.{u} :=
  TopCat.of (U.stage n)

/-- The inclusion of the `n`-th stage into the ambient space. -/
abbrev stageInclusion (U : ExpandingUnion X) (n : ℕ) : U.stageSpace n ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of the `n`-th stage into the `(n + 1)`-st stage. -/
abbrev stageStep (U : ExpandingUnion X) (n : ℕ) : U.stageSpace n ⟶ U.stageSpace (n + 1) :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, U.mono (Nat.le_succ n) x.2⟩,
      continuous_subtype_val.subtype_mk fun x ↦ U.mono (Nat.le_succ n) x.2⟩

end ExpandingUnion
