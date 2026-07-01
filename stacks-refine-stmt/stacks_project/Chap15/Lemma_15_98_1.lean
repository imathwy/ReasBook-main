import Mathlib
import stacks_project.Chap13.Definition_13_34_1
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Lemma_15_60_3
import stacks_project.Chap15.Lemma_15_88_5_TowerBridge

open CategoryTheory
open CategoryTheory.Limits
open CommRingCat
open Opposite
open DerivedModuleTower

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {F : ℕᵒᵖ ⥤ CommRingCat.{u}}

section

local notation "DModA" => DerivedCategory (ModuleCat (inverseLimitRing F))

namespace DerivedModuleTower

/-- A stagewise property on a derived module tower either holds at every stage, or it holds at one
stage after which all transition kernels are nilpotent. -/
def StagewiseOrEventuallyNilpotent
    (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (P : ℕ → Prop) : Prop :=
  (∀ n : ℕ, P n) ∨
    ∃ n₀ : ℕ, P n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → IsNilpotent (RingHom.ker (stageTransitionRingHom F n))

/-- Monotonicity of the stagewise/eventually-nilpotent hypothesis with respect to the stagewise
property. -/
theorem stagewiseOrEventuallyNilpotent_mono
    (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (P Q : ℕ → Prop) (hPQ : ∀ n : ℕ, P n → Q n)
    (hP : StagewiseOrEventuallyNilpotent F P) :
    StagewiseOrEventuallyNilpotent F Q := by
  rcases hP with hP | ⟨n₀, hPn₀, hnil⟩
  · exact Or.inl (fun n ↦ hPQ n (hP n))
  · exact Or.inr ⟨n₀, hPQ n₀ hPn₀, hnil⟩

/-- The canonical stagewise derived base-change comparison induced by the tower map
`T.stepMap n : K_{n + 1} ⟶ K_n` viewed over `A_{n + 1}`. -/
abbrev stageDerivedBaseChangeComparison
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) (n : ℕ) :
    stageDerivedBaseChange F T n ⟶ T.obj n :=
  ((derivedTensorWithAlgebraAdjunction).homEquiv (T.obj (n + 1)) (T.obj n)).symm (T.stepMap n)

/-- The derived-limit base-change comparison attached to a chosen stage comparison
`c : K ⟶ K_n|_A`. -/
abbrev inverseLimitBaseChangeComparison
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F))
    (K : DModA) (n : ℕ) (c : K ⟶ (stageRestrictionToLimitTower F T).obj (op n)) :
    inverseLimitBaseChange F K n ⟶ T.obj n :=
  ((derivedTensorWithAlgebraAdjunction).homEquiv K (T.obj n)).symm c

end DerivedModuleTower

/- Domain-style sampling for Lemma 15.98.1:
- primary domain: derived inverse limits for towers of derived module objects over a sequential
  inverse system of commutative rings, together with pseudo-coherence and derived base change;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `CategoryTheory.IsDerivedLimit`,
  `DerivedModuleTower.stageRestrictionToLimitTower`,
  `DerivedModuleTower.stageDerivedBaseChangeComparison`,
  `CategoryTheory.HasMilnorTriangle.WithMap`;
- best owner abstraction: the chapter bridge owner
  `DerivedModuleTower (stageRing F) (stageTransitionRingHom F)` together with its canonical
  fixed-base inverse system `DerivedModuleTower.stageRestrictionToLimitTower T`, the canonical
  stagewise adjoint comparison
  `DerivedModuleTower.stageDerivedBaseChangeComparison F T n`, and the canonical
  derived-category owners `K.IsPseudoCoherent`, `CategoryTheory.IsDerivedLimit`, and the
  chosen-Milnor-map bridge `CategoryTheory.HasMilnorTriangle.WithMap`;
- primitive vs. derived:
  primitive data are the tower `T`, the chosen derived limit `K` of the canonical fixed-base
  tower `stageRestrictionToLimitTower T`, and the stagewise pseudo-coherence / nilpotence
  hypotheses;
  derived API is the pseudo-coherence conclusion for `K` and the inverse-limit base-change
  comparison induced by a derived-limit stage map.

Source/core/bridge triage:
- `source-facing`: the pseudo-coherence and base-change conclusion for the chosen derived limit;
- `core/canonical`: `K.IsPseudoCoherent` and `CategoryTheory.IsDerivedLimit`;
- `bridge/view`: `stageRestrictionToLimitTower`, `stageDerivedBaseChangeComparison`, and
  `inverseLimitBaseChangeComparison`, together with `HasMilnorTriangle.WithMap`. -/

-- Proof sketch: represent the tower by bounded-above finite-free complexes compatible under
-- reduction along the surjective transition maps, form the termwise inverse limit complex over
-- `A = lim A_n`, and use the Milnor description of `R lim` together with stagewise derived
-- tensor compatibility to identify pseudo-coherence of the limit object.
/-
Lemma 15.98.1: let `A = \varprojlim_n A_n` be a sequential inverse limit of commutative
rings, let `T` encode the compatible system `K_n ∈ D(A_n)`, and let `K` be a chosen derived
limit of the canonical fixed-base tower `stageRestrictionToLimitTower T` in `D(A)`. Assume the
transition maps `A_{n + 1} → A_n` are surjective with locally nilpotent kernels, that either every
`K_n` is pseudo-coherent or some stage `K_{n₀}` is pseudo-coherent and all later kernels are
nilpotent, and that the canonical stagewise derived base-change comparisons
`K_{n + 1} \otimes_{A_{n + 1}}^{\mathbf L} A_n → K_n` induced by `T.stepMap` are isomorphisms.
Then `K` is pseudo-coherent over `A`.
-/
variable
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F))
    (K : DModA)
    (h_surj : ∀ n : ℕ, Function.Surjective (stageTransitionRingHom F n))
    (h_locnil :
      ∀ n : ℕ, RingHom.ker (stageTransitionRingHom F n) ≤ nilradical (stageRing F (n + 1)))
    (hpc : StagewiseOrEventuallyNilpotent F (fun n ↦ (T.obj n).IsPseudoCoherent))
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison T n))

theorem derivedLimit_isPseudoCoherent_of_stagewisePseudoCoherent_or_eventuallyNilpotent
    (hKlim : IsDerivedLimit (stageRestrictionToLimitTower F T) K) :
    K.IsPseudoCoherent := sorry

-- Proof sketch: apply Lemma `15.98.1` to the canonical fixed-base tower
-- `stageRestrictionToLimitTower T`; any chosen Milnor map
-- `ι : K ⟶ ∏ stageRestrictionToLimitTower(T)_n` then yields the stage comparison
-- `ι ≫ π_n : K ⟶ K_n|_A`, which transposes under the derived extension/restriction adjunction to
-- the canonical base-change morphism `K ⊗_A^{\mathbf L} A_n ⟶ K_n`.
/-- Under the hypotheses of Lemma 15.98.1, the `n`th component of any chosen Milnor product map
from the derived limit `K` to the fixed-base tower `stageRestrictionToLimitTower T` induces an
isomorphism on derived base change `K ⊗_A^{\mathbf L} A_n → K_n`. -/
theorem inverseLimitBaseChangeComparison_isIso_of_stagewisePseudoCoherent_or_eventuallyNilpotent
    [HasProduct (inverseSystemFamily (stageRestrictionToLimitTower F T))]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily (stageRestrictionToLimitTower F T)} {n : ℕ}
    (hι : HasMilnorTriangle.WithMap (stageRestrictionToLimitTower F T) ι) :
    IsIso
      (inverseLimitBaseChangeComparison T K n
        (ι ≫ Pi.π (inverseSystemFamily (stageRestrictionToLimitTower F T)) n)) := sorry

end

end
