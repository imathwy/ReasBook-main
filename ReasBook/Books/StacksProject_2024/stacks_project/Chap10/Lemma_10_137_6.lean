import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap10.Definition_10_136_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x

namespace Algebra

section Generic

variable {R : Type u} {R' : Type v} {Rf : Type w} {S : Type x} {Sg : Type x}
variable [CommRing R] [CommRing R'] [CommRing Rf] [CommRing S] [CommRing Sg]
variable [Algebra R S] [Algebra R R']

/- Domain-style sampling:
- primary domain: standard smooth `R`-algebras and their canonical stability/smoothness API;
- sampled owner declarations:
  `RingHom.IsStandardSmooth.smooth`,
  `Algebra.IsStandardSmooth.baseChange`,
  `Algebra.IsStandardSmooth.localization_away`,
  `SubmersivePresentation.basisKaehler`,
  `SubmersivePresentation.basisCotangent`;
- best owner abstraction: `Algebra.IsStandardSmooth R S`;
- primitive data: a submersive presentation witnessing standard smoothness;
- derived API: smoothness, localization/base-change stability, cotangent bases, and the relative
  global complete intersection bridge.
-/

/- Lemma 10.137.6 (1): a standard smooth `R`-algebra is smooth over `R`. This is exactly the
canonical theorem `RingHom.IsStandardSmooth.smooth`, specialized to `algebraMap R S`. -/
recall RingHom.IsStandardSmooth.smooth

-- Proof sketch: localize `S` away from `g`; the localization map `S → S_g` is standard smooth of
-- relative dimension `0`, and composition of standard smooth maps preserves standard smoothness.
namespace IsStandardSmooth

/-- Lemma 10.137.6 (2): for any `g : S`, any away-localization `Sg` of `S` at `g` is again
standard smooth over `R`. -/
theorem localizationAway (hS : IsStandardSmooth R S) (g : S) [Algebra R Sg] [Algebra S Sg]
    [IsScalarTower R S Sg] [IsLocalization.Away g Sg] :
    IsStandardSmooth R Sg := by
  letI := hS
  letI : IsStandardSmooth S Sg := Algebra.IsStandardSmooth.localization_away g
  exact Algebra.IsStandardSmooth.trans R S Sg

end IsStandardSmooth

/- Lemma 10.137.6 (3): for any ring map `R → R'`, the base change `R' → R' ⊗[R] S` is standard
smooth. This is exactly the canonical base-change instance
`Algebra.IsStandardSmooth.baseChange`. -/
recall Algebra.IsStandardSmooth.baseChange

variable [Algebra R Rf] [Algebra Rf S] [IsScalarTower R Rf S]

-- Proof sketch: because `S` is already an `R_f`-algebra, the image of `f` is automatically a
-- unit in `S`. Base changing the standard smooth `R`-algebra `S` along `R → R_f` yields the
-- standard smooth `R_f`-algebra `R_f ⊗[R] S`, and the canonical tensor-localization
-- identification plus the fact that localizing `S` away from a unit does nothing gives an
-- `R_f`-algebra isomorphism `R_f ⊗[R] S ≃ₐ[R_f] S`.
namespace IsStandardSmooth

/-- Lemma 10.137.6 (4): if `f : R` maps to a unit in `S`, then after localizing `R` away from
`f`, the induced map `R_f → S` is standard smooth. -/
theorem of_isUnit_base
    (hS : IsStandardSmooth R S) {f : R} [IsLocalization.Away f Rf] :
    IsStandardSmooth Rf S := by
  letI := hS
  let hu : IsUnit (algebraMap R S f) := by
    rw [show algebraMap R S f = algebraMap Rf S (algebraMap R Rf f) by
      rw [IsScalarTower.algebraMap_apply R Rf S]]
    exact (IsLocalization.Away.algebraMap_isUnit f).map (algebraMap Rf S)
  letI : IsLocalization.Away (algebraMap R S f) S :=
    IsLocalization.away_of_isUnit_of_bijective S hu Function.bijective_id
  letI : Algebra S (Rf ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let eu : S ≃ₐ[S] Localization.Away (algebraMap R S f) :=
    IsLocalization.atUnit S (Localization.Away (algebraMap R S f)) (algebraMap R S f) hu
  let eS : Rf ⊗[R] S ≃ₐ[S] S :=
    (IsLocalization.Away.tensorRightEquiv S f Rf).trans eu.symm
  have hcomm : (eS : Rf ⊗[R] S →+* S).comp (algebraMap Rf (Rf ⊗[R] S)) = algebraMap Rf S := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext r
    change eS (algebraMap Rf (Rf ⊗[R] S) (algebraMap R Rf r)) = algebraMap Rf S (algebraMap R Rf r)
    rw [← IsScalarTower.algebraMap_apply R Rf (Rf ⊗[R] S), ← IsScalarTower.algebraMap_apply R Rf S]
    have hmap : algebraMap R (Rf ⊗[R] S) r = algebraMap S (Rf ⊗[R] S) (algebraMap R S r) :=
      IsScalarTower.algebraMap_apply R S (Rf ⊗[R] S) r
    rw [hmap]
    exact eS.commutes _
  let e : Rf ⊗[R] S ≃ₐ[Rf] S :=
    { __ := eS.toRingEquiv
      commutes' := by
        intro x
        exact RingHom.ext_iff.mp hcomm x }
  letI : IsStandardSmooth Rf (Rf ⊗[R] S) := inferInstance
  exact IsStandardSmooth.of_algEquiv e

-- Proof sketch: after base change to each residue field `κ(p)`, clause (5) reduces the statement
-- to the field case. There the standard smooth algebra is a local complete intersection, and the
-- cotangent and conormal freeness from clauses (2) and (3) give the expected fiber dimension,
-- which is exactly the relative global complete intersection condition.
/-- Lemma 10.137.6 (5): a standard smooth `R`-algebra is a relative global complete
intersection over `R`. -/
theorem isRelativeGlobalCompleteIntersection (hS : IsStandardSmooth R S) :
    IsRelativeGlobalCompleteIntersection R S := sorry

end IsStandardSmooth

end Generic

section Presentation

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [Finite σ]
variable (P : SubmersivePresentation R S ι σ)

/- For a standard smooth presentation `P`, the canonical basis
`P.basisKaehler` exhibits `Ω[S⁄R]` as free on the images of the differentials `dxᵢ` indexed by
the complement of `P.map`; this is the library-facing form of the basis
`dx_{c + 1}, …, dx_n`. -/
#check P.basisKaehler

/- For a standard smooth presentation `P`, the canonical basis
`P.basisCotangent` exhibits `I/I²` as free on the classes of the defining relations `P.relation`;
this is the library-facing form of the basis given by the classes of `f₁, …, f_c`. -/
#check P.basisCotangent

end Presentation

end Algebra
