import Mathlib
import StacksProject_2024.Chap17.Lemma_17_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopologicalSpace.Opens
open scoped TopCat

noncomputable section

universe u

/- Domain-style sampling for 17.19.2.1:
- primary domain: set-valued sheaves on a topological space, finite coproducts of lower-shriek
  constant sheaves, and coequalizers in the sheaf topos;
- sampled relevant declarations:
  `j![U, S]`,
  `∐`,
  `coequalizer`,
  `coequalizer.π`,
  `coequalizer.condition`;
- best owner abstraction: the core displayed object of Equation `17.19.2.1` is still the canonical
  coproduct/coequalizer expression itself, but the neighboring lemmas repeatedly quantify over the
  same finite presentation data. The minimal reusable owner layer is therefore a thin Prop-valued
  abbreviation recording that exact data, without introducing any new packaged structure;
- primitive data: finite families `U`, `V`, `S`, `T` indexed by arbitrary finite types `ι`, `κ`
  and a parallel pair `left`, `right` between the corresponding finite coproducts;
- derived API: the compact-open and basis-relative presentation predicates, together with the
  canonical coequalizer object, its projection, and its defining relation.

Source/core/bridge triage:
- `source-facing`: the finite lower-shriek constant coequalizer presentation predicates used by the
  adjacent lemmas;
- `core/canonical`: finite coproducts in `Sh(X)` and `coequalizer`;
- `bridge/view`: the basis-to-compact-open implication under quasi-compactness of the basis.
-/

section

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

local instance (ι : Type u) : HasColimitsOfShape (Discrete ι) (TopCat.Sheaf (Type u) X) :=
  by
    let _ : HasColimitsOfShape (Discrete ι) (Type u) := by infer_instance
    change HasColimitsOfShape (Discrete ι)
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
    exact CategoryTheory.Sheaf.instHasColimitsOfShape

local instance : HasColimitsOfShape WalkingParallelPair (TopCat.Sheaf (Type u) X) :=
  by
    let _ : HasColimitsOfShape WalkingParallelPair (Type u) := by infer_instance
    change HasColimitsOfShape WalkingParallelPair
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
    exact CategoryTheory.Sheaf.instHasColimitsOfShape

/-- A sheaf of sets on `X` has a finite compact-open lower-shriek constant coequalizer
presentation if it is isomorphic to the coequalizer of two maps between finite coproducts of
sheaves `j![U, S]` and `j![V, T]`, with each open quasi-compact and each fibre finite. -/
abbrev HasFiniteCompactOpenLowerShriekConstantCoequalizerPresentation
    (ℱ : Sh(X)) : Prop :=
  ∃ (ι κ : Type u) (_ : Finite ι) (_ : Finite κ)
    (U : ι → Opens X) (V : κ → Opens X)
    (S : ι → Type u) (T : κ → Type u),
      ∃ (left right :
        (∐ fun b : κ ↦ j![V b, T b]) ⟶
          (∐ fun a : ι ↦ j![U a, S a]))
        (_ : ℱ ≅ coequalizer left right),
          (∀ a, IsCompact (U a : Set X)) ∧
            (∀ b, IsCompact (V b : Set X)) ∧
              (∀ a, Finite (S a)) ∧
                ∀ b, Finite (T b)

/-- A sheaf of sets on `X` has a finite basis lower-shriek constant coequalizer presentation
relative to `B` if it is isomorphic to the coequalizer of two maps between finite coproducts of
sheaves `j![U, S]` and `j![V, T]`, with each `U a` and `V b` in `B` and each fibre finite. -/
abbrev HasFiniteBasisLowerShriekConstantCoequalizerPresentation
    (B : Set (Opens X)) (ℱ : Sh(X)) : Prop :=
  ∃ (ι κ : Type u) (_ : Finite ι) (_ : Finite κ)
    (U : ι → Opens X) (V : κ → Opens X)
    (S : ι → Type u) (T : κ → Type u),
      ∃ (left right :
        (∐ fun b : κ ↦ j![V b, T b]) ⟶
          (∐ fun a : ι ↦ j![U a, S a]))
        (_ : ℱ ≅ coequalizer left right),
          (∀ a, U a ∈ B) ∧
            (∀ b, V b ∈ B) ∧
              (∀ a, Finite (S a)) ∧
                ∀ b, Finite (T b)

theorem HasFiniteBasisLowerShriekConstantCoequalizerPresentation.compactOpen
    {B : Set (Opens X)} {ℱ : Sh(X)}
    (hℱ : HasFiniteBasisLowerShriekConstantCoequalizerPresentation B ℱ)
    (hqc : ∀ U, U ∈ B → IsCompact (U : Set X)) :
    HasFiniteCompactOpenLowerShriekConstantCoequalizerPresentation ℱ := by
  rcases hℱ with
    ⟨ι, κ, _, _, U, V, S, T, left, right, e, hU, hV, hS, hT⟩
  exact ⟨ι, κ, ‹Finite ι›, ‹Finite κ›, U, V, S, T, left, right, e,
    fun a ↦ hqc (U a) (hU a),
    fun b ↦ hqc (V b) (hV b),
    hS, hT⟩

variable {ι κ : Type u} [Finite ι] [Finite κ]
variable (U : ι → Opens X) (V : κ → Opens X)
variable (S : ι → Type u) (T : κ → Type u)
variable (left right :
  (∐ fun b : κ ↦ j![V b, T b]) ⟶
    (∐ fun a : ι ↦ j![U a, S a]))

/- 17.19.2.1: the displayed finite coproduct is the canonical coproduct
`∐ fun a ↦ j_{U_a!}\underline{S_a}` in `Sh(X)`. -/
#check (∐ fun a : ι ↦ j![U a, S a])

/- 17.19.2.1: the displayed sheaf is the canonical coequalizer of the parallel pair
`left`, `right` between the two finite coproducts. -/
#check coequalizer left right

/- Companion recall: the universal projection from the target coproduct to the displayed
coequalizer is the canonical morphism `coequalizer.π left right`. -/
#check coequalizer.π left right

/- Companion recall: the defining relation of the displayed coequalizer is the canonical equation
`coequalizer.condition left right`. -/
#check coequalizer.condition left right

end

end
