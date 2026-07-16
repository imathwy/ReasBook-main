import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_82_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

/-- Helper for Lemma 15.82.8: absolute `m`-pseudo-coherence is stable under retracts. -/
private theorem absolute_isMPseudoCoherent_of_retract
    {S : Type*} [Ring S]
    {X Y : DerivedCategory (ModuleCat S)} {m : ℤ}
    (h : Retract X Y) (hY : Y.IsMPseudoCoherent m) :
    X.IsMPseudoCoherent m := by
  sorry

section

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.82.8:
- primary domain: relative pseudo-coherence in `D(A)` for a finite type `R`-algebra `A`;
- sampled owner declarations:
  `CategoryTheory.ObjectProperty.IsStableUnderRetracts`,
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `isMPseudoCoherent_isStableUnderRetracts`;
- best owner abstraction: the chapter-standard owner layer is
  `ObjectProperty.IsStableUnderRetracts (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m)` and
  `ObjectProperty.IsStableUnderRetracts (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R)`;
- primitive vs. derived:
  primitive data are the relative pseudo-coherence owners from Definition `15.82.4` and
  Lemma `15.82.10`;
  derived API is the source-facing direct-summand consequence, obtained from retract-stability via
  `of_biprod_left` and `of_biprod_right`;
- source/core/bridge triage:
  `source-facing`: the direct-summand statements of Lemma `15.82.8`;
  `core/canonical`: retract-stability for the relative pseudo-coherence object properties;
  `bridge/view`: restriction to each surjective polynomial presentation of `A` over `R`, where the
    absolute retract-stability instances apply.
- layer: this file now targets the `core/canonical` owner layer first and derives the textbook
  biproduct lemmas from it, matching the Chapter 15 pattern of `Lemma_15_65_8`.
-/

-- Route correction: this item only needs the relative derived predicates, which are already
-- defined in the earlier dependency-closed file `Lemma_15_82_6`; importing `Lemma_15_82_10`
-- pulled in a later heavy theorem file and obscured the intended direct-summand route.

-- Proof sketch: for each surjective polynomial presentation `α : R[x₁, ..., xₙ] → A`, map a
-- retract `K ⟶ L ⟶ K` through the derived restriction-of-scalars functor to `D(R[x₁, ..., xₙ])`
-- and apply the absolute retract-stability of `m`-pseudo-coherence there.
/-- Relative `m`-pseudo-coherent objects of `D(A)` are stable under retracts/direct summands. -/
instance isMPseudoCoherentRelativeTo_isStableUnderRetracts (m : ℤ) :
    ObjectProperty.IsStableUnderRetracts
      (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m) where
  of_retract h hK := by
    intro n α hα
    exact absolute_isMPseudoCoherent_of_retract
      (S := MvPolynomial (Fin n) R)
      (h.map ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory))
      (hK n α hα)

-- Proof sketch: apply the previous retract-stability instance degreewise in `m`.
/-- Relative pseudo-coherent objects of `D(A)` are stable under retracts/direct summands. -/
instance isPseudoCoherentRelativeTo_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts
      (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R) where
  of_retract h hK := by
    intro m
    exact
      prop_of_retract
        (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m)
        h (hK m)

/-- If `K ⊞ L` is `m`-pseudo-coherent relative to `R`, then `K` is `m`-pseudo-coherent relative to
`R`. -/
theorem isMPseudoCoherentRelativeTo_left_of_biprod
    (K L : DModA) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherentRelativeTo R m) :
    K.IsMPseudoCoherentRelativeTo R m := by
  exact of_biprod_left (fun X : DModA ↦ X.IsMPseudoCoherentRelativeTo R m) hKL

/-- If `K ⊞ L` is `m`-pseudo-coherent relative to `R`, then `L` is `m`-pseudo-coherent relative to
`R`. -/
theorem isMPseudoCoherentRelativeTo_right_of_biprod
    (K L : DModA) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherentRelativeTo R m) :
    L.IsMPseudoCoherentRelativeTo R m := by
  exact of_biprod_right (fun X : DModA ↦ X.IsMPseudoCoherentRelativeTo R m) hKL

-- Proof sketch: combine the left and right summand statements for relative `m`-pseudo-coherence.
/-- Lemma 15.82.8 (1): if `K^• ⊞ L^•` is `m`-pseudo-coherent relative to `R`, then both `K^•`
and `L^•` are `m`-pseudo-coherent relative to `R`. -/
@[stacks 0676]
theorem isMPseudoCoherentRelativeTo_summands_of_biprod
    (K L : DModA) (m : ℤ)
    (hKL : (K ⊞ L).IsMPseudoCoherentRelativeTo R m) :
    K.IsMPseudoCoherentRelativeTo R m ∧ L.IsMPseudoCoherentRelativeTo R m := by
  exact
    ⟨isMPseudoCoherentRelativeTo_left_of_biprod K L m hKL,
      isMPseudoCoherentRelativeTo_right_of_biprod K L m hKL⟩

/-- If `K ⊞ L` is pseudo-coherent relative to `R`, then `K` is pseudo-coherent relative to `R`. -/
theorem isPseudoCoherentRelativeTo_left_of_biprod
    (K L : DModA)
    (hKL : (K ⊞ L).IsPseudoCoherentRelativeTo R) :
    K.IsPseudoCoherentRelativeTo R := by
  exact of_biprod_left (fun X : DModA ↦ X.IsPseudoCoherentRelativeTo R) hKL

/-- If `K ⊞ L` is pseudo-coherent relative to `R`, then `L` is pseudo-coherent relative to `R`. -/
theorem isPseudoCoherentRelativeTo_right_of_biprod
    (K L : DModA)
    (hKL : (K ⊞ L).IsPseudoCoherentRelativeTo R) :
    L.IsPseudoCoherentRelativeTo R := by
  exact of_biprod_right (fun X : DModA ↦ X.IsPseudoCoherentRelativeTo R) hKL

-- Proof sketch: combine the left and right pseudo-coherent summand statements.
/-- Lemma 15.82.8 (2): if `K^• ⊞ L^•` is pseudo-coherent relative to `R`, then both `K^•` and
`L^•` are pseudo-coherent relative to `R`. -/
@[stacks 0676]
theorem isPseudoCoherentRelativeTo_summands_of_biprod
    (K L : DModA)
    (hKL : (K ⊞ L).IsPseudoCoherentRelativeTo R) :
    K.IsPseudoCoherentRelativeTo R ∧ L.IsPseudoCoherentRelativeTo R := by
  exact
    ⟨isPseudoCoherentRelativeTo_left_of_biprod K L hKL,
      isPseudoCoherentRelativeTo_right_of_biprod K L hKL⟩

end

end

end CategoryTheory
