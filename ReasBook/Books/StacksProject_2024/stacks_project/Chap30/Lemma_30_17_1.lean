import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap30.Lemma_30_16_1
import StacksProject_2024.Chap30.Lemma_30_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: `lean_leansearch` did not find a packaged Serre-vanishing equivalence in
mathlib. Local Chapter 30 precedent uses `List.TFAE` for listwise equivalences,
`Scheme.Modules.IsAmple` for ampleness, `Subobject (SheafOfModules.unit X.ringCatSheaf)` for
ideal sheaves, and `schemeModuleCohomology`/tensor powers from Lemma 30.16.1 for global sheaf
cohomology. The Stacks tag evidence is consistent for tag `0B5U`. -/

variable {X : Scheme.{u}} [MonoidalCategory X.Modules]

/-- Positive-degree cohomology of all sufficiently high natural tensor twists of a module
vanishes. -/
abbrev positiveTwistCohomologyVanishesEventually
    (L : X.Modules) [hL : Invertible L] (F : X.Modules) : Prop :=
  ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ p : ℕ, 0 < p →
    IsZero (schemeModuleCohomology (tensorObj F (hL n)) p)

/-- The first cohomology of a positive tensor twist vanishes for every quasi-coherent ideal
subsheaf of the structure sheaf. -/
abbrev idealH1PositiveTwistVanishes
    (L : X.Modules) [hL : Invertible L] : Prop :=
  ∀ I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules),
    (Subobject.underlying.obj I).IsQuasicoherent →
      ∃ n : ℕ, 0 < n ∧
        IsZero
          (schemeModuleCohomology
            (tensorObj (Subobject.underlying.obj I : X.Modules) (hL n)) 1)

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Lemma 30.17.1: for a proper morphism `X → Spec(R)` with `R` Noetherian and an invertible
`\mathcal O_X`-module `L`, ampleness of `L`, eventual vanishing of higher cohomology after high
positive twists for every coherent module, and positive-twist `H^1`-vanishing for every
quasi-coherent ideal sheaf are equivalent. -/
@[stacks 0B5U]
theorem isAmple_tfae_eventual_positive_twist_cohomology_and_ideal_H1
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (L : X.Modules) [Invertible L] :
    List.TFAE
      [ IsAmple L,
        ∀ F : X.Modules, F.IsCoherent → positiveTwistCohomologyVanishesEventually L F,
        idealH1PositiveTwistVanishes L ] := sorry

end AlgebraicGeometry.Scheme.Modules
