import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Lemma_10_112_1
import stacks_proof.stacks_project.Chap10.Lemma_10_114_1
import stacks_proof.stacks_project.Chap10.Lemma_10_125_5
import stacks_proof.stacks_project.Chap10.Definition_10_136_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.HasGoingDown

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
@[stacks 00T7]
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
@[stacks 00T7]
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

end IsStandardSmooth

/-- Helper for Chap10 Lemma 10 137 6: a nonempty open subset of the prime spectrum of a
Jacobson ring contains a maximal ideal. -/
private lemma exists_maximal_mem_open_of_isJacobsonRing
    {A : Type*} [CommRing A] [IsJacobsonRing A] {U : Set (PrimeSpectrum A)}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ p : PrimeSpectrum A, p ∈ U ∧ p.asIdeal.IsMaximal := by
  -- A Jacobson spectrum has a closed point in every nonempty open subset.
  obtain ⟨p, hpU, hpclosed⟩ :=
    PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing U hU hne
  -- In an affine prime spectrum, closed points are exactly maximal ideals.
  exact ⟨p, hpU, (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hpclosed⟩

/-- Helper for Chap10 Lemma 10 137 6: localizing at a prime cannot increase Krull dimension. -/
private lemma ringKrullDim_localizationAtPrime_le_ringKrullDim
    {A : Type*} [CommRing A] (q : Ideal A) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime q) ≤ ringKrullDim A := by
  -- Rewrite the local dimension as the height of the prime, then use the global height bound.
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
  exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'

/-- Helper for Chap10 Lemma 10 137 6: étale maps preserve Krull dimension after localizing at
a prime and its contraction. -/
private theorem ringKrullDim_localizationAtPrime_eq_of_etale
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Ideal B) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime (q.under A)) =
      ringKrullDim (Localization.AtPrime q) := by
  -- Faithfully flatness of the induced local map gives the lower comparison for the base local
  -- ring via the Chapter 10 going-down dimension inequality.
  have hAB :
      ringKrullDim (Localization.AtPrime (q.under A)) ≤
        ringKrullDim (Localization.AtPrime q) := by
    letI :
        Module.FaithfullyFlat (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    simpa using
      ringKrullDim_le_of_surjective_comap_of_specializing_or_generalizing
        (algebraMap (Localization.AtPrime (q.under A)) (Localization.AtPrime q))
        PrimeSpectrum.comap_surjective_of_faithfullyFlat
        (.inr <| iff_generalizingMap_primeSpectrumComap.mp inferInstance)
  -- Étale maps are quasi-finite at every prime, so the local quasi-finite bound gives the reverse
  -- comparison.
  have hBA :
      ringKrullDim (Localization.AtPrime q) ≤
        ringKrullDim (Localization.AtPrime (q.under A)) := by
    simpa using ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt q
  exact le_antisymm hAB hBA

/-- Helper for Chap10 Lemma 10 137 6: an étale algebra over a polynomial algebra over a field
has Krull dimension at most the number of variables. -/
private theorem ringKrullDim_le_of_etale_mvPolynomial_field
    {K A : Type*} [Field K] [CommRing A] [Algebra K A] {d : ℕ}
    (φ : MvPolynomial (Fin d) K →ₐ[K] A) (hφ : φ.Etale) :
    ringKrullDim A ≤ (d : WithBot ℕ∞) := by
  -- View `A` as an algebra over the polynomial ring through `φ`; then `hφ` supplies the étale
  -- algebra structure needed for quasi-finiteness.
  letI : Algebra (MvPolynomial (Fin d) K) A := φ.toAlgebra
  have hetale : Algebra.Etale (MvPolynomial (Fin d) K) A := by
    simpa [Algebra.Etale, RingHom.algebraMap_toAlgebra] using hφ
  letI : Algebra.Etale (MvPolynomial (Fin d) K) A := hetale
  -- Finite type over the field follows by transitivity through the finite type polynomial algebra.
  letI : Algebra.FiniteType K A :=
    Algebra.FiniteType.trans (R := K) (S := MvPolynomial (Fin d) K) (A := A)
      inferInstance inferInstance
  exact ringKrullDim_le_of_quasiFinite_mvPolynomial_algebra (k := K) (n := d) (S := A)

/-- Helper for Chap10 Lemma 10 137 6: a nonzero étale algebra over a polynomial algebra over a
field has Krull dimension at least the number of variables. -/
private theorem le_ringKrullDim_of_etale_mvPolynomial_field
    {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Nontrivial A] {d : ℕ}
    (φ : MvPolynomial (Fin d) K →ₐ[K] A) (hφ : φ.Etale) :
    (d : WithBot ℕ∞) ≤ ringKrullDim A := by
  -- Use `φ` to make the spectrum map from `Spec A` to affine `d`-space the canonical comap.
  letI : Algebra (MvPolynomial (Fin d) K) A := φ.toAlgebra
  have hetale : Algebra.Etale (MvPolynomial (Fin d) K) A := by
    simpa [Algebra.Etale, RingHom.algebraMap_toAlgebra] using hφ
  letI : Algebra.Etale (MvPolynomial (Fin d) K) A := hetale
  -- Étale maps are flat and finitely presented, so the spectrum image is open.
  have hopen : IsOpen (Set.range (PrimeSpectrum.comap
      (algebraMap (MvPolynomial (Fin d) K) A))) := by
    exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation.isOpen_range
  -- Nontriviality of `A` gives a prime of `A`, hence a nonempty image in the polynomial spectrum.
  have hne : (Set.range (PrimeSpectrum.comap
      (algebraMap (MvPolynomial (Fin d) K) A))).Nonempty := by
    letI : Nonempty (PrimeSpectrum A) := PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance
    exact Set.range_nonempty (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin d) K) A))
  -- Choose a maximal polynomial prime lying in the open image.
  obtain ⟨p, hpRange, hpMax⟩ := exists_maximal_mem_open_of_isJacobsonRing hopen hne
  rcases hpRange with ⟨q, hq⟩
  have hunder : q.asIdeal.under (MvPolynomial (Fin d) K) = p.asIdeal := by
    simpa [Ideal.under_def, PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hq
  have hqMax : (q.asIdeal.under (MvPolynomial (Fin d) K)).IsMaximal := by
    rw [hunder]
    exact hpMax
  let m : MaximalSpectrum (MvPolynomial (Fin d) K) :=
    ⟨q.asIdeal.under (MvPolynomial (Fin d) K), hqMax⟩
  -- The known dimension of a maximal localization of affine `d`-space transfers through the
  -- étale local comparison and then into the global dimension of `A`.
  have hpoly :
      ringKrullDim (Localization.AtPrime (q.asIdeal.under (MvPolynomial (Fin d) K))) =
        (d : WithBot ℕ∞) := by
    simpa [m] using ringKrullDim_localizationAtMaximal_mvPolynomial (m := m)
  calc
    (d : WithBot ℕ∞) =
        ringKrullDim (Localization.AtPrime (q.asIdeal.under (MvPolynomial (Fin d) K))) :=
      hpoly.symm
    _ = ringKrullDim (Localization.AtPrime q.asIdeal) :=
      ringKrullDim_localizationAtPrime_eq_of_etale
        (A := MvPolynomial (Fin d) K) (B := A) q.asIdeal
    _ ≤ ringKrullDim A :=
      ringKrullDim_localizationAtPrime_le_ringKrullDim q.asIdeal

/-- Helper for Chap10 Lemma 10 137 6: a nonzero algebra étale over a polynomial algebra in
`d` variables over a field has Krull dimension `d`. -/
private theorem ringKrullDim_eq_of_etale_mvPolynomial_field
    {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Nontrivial A] {d : ℕ}
    (φ : MvPolynomial (Fin d) K →ₐ[K] A) (hφ : φ.Etale) :
    ringKrullDim A = d := by
  -- Combine the quasi-finite upper bound with the open-image/Jacobson lower bound.
  exact le_antisymm
    (ringKrullDim_le_of_etale_mvPolynomial_field φ hφ)
    (le_ringKrullDim_of_etale_mvPolynomial_field φ hφ)

namespace SubmersivePresentation

/-- Helper for Chap10 Lemma 10 137 6: a submersive presentation over a field has Krull dimension
equal to its presentation dimension. -/
private theorem ringKrullDim_eq_dimension_of_field
    {K A ι σ : Type*} [Field K] [CommRing A] [Algebra K A] [Finite ι] [Finite σ]
    [Nontrivial A] (P : SubmersivePresentation K A ι σ) :
    ringKrullDim A = P.dimension := by
  -- The submersive presentation makes `A` standard smooth of relative dimension `P.dimension`.
  have hstd : IsStandardSmoothOfRelativeDimension P.dimension K A :=
    P.isStandardSmoothOfRelativeDimension rfl
  letI : IsStandardSmoothOfRelativeDimension P.dimension K A := hstd
  -- Factor that standard-smooth algebra through an étale map from the polynomial algebra in the
  -- same number of variables, then invoke the isolated field-dimension theorem.
  obtain ⟨φ, hφ⟩ :=
    IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial P.dimension K A
  exact ringKrullDim_eq_of_etale_mvPolynomial_field φ hφ

/-- Helper for Chap10 Lemma 10 137 6: the fiber of a submersive presentation has the dimension
of the finite reindexed presentation used in the relative-GCI witness. -/
private theorem fiber_ringKrullDim_eq_reindexFin_dimension
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι] [Fintype σ]
    (P : SubmersivePresentation R S ι σ) (p : PrimeSpectrum R)
    [Nontrivial (p.asIdeal.Fiber S)] :
    ringKrullDim (p.asIdeal.Fiber S) =
      ((P.reindex (Fintype.equivFin ι).symm
        (Fintype.equivFin σ).symm).toPresentation).dimension := by
  -- Base change the submersive presentation to the residue field at `p`.
  have hbase :
      ringKrullDim (p.asIdeal.Fiber S) =
        (P.baseChange p.asIdeal.ResidueField).dimension :=
    ringKrullDim_eq_dimension_of_field (P.baseChange p.asIdeal.ResidueField)
  -- The presentation dimension is unchanged by residue-field base change and finite reindexing.
  calc
    ringKrullDim (p.asIdeal.Fiber S) =
        (P.baseChange p.asIdeal.ResidueField).dimension := hbase
    _ =
        ((P.reindex (Fintype.equivFin ι).symm
          (Fintype.equivFin σ).symm).toPresentation).dimension := by
          simp [Algebra.Presentation.dimension]

end SubmersivePresentation

namespace IsStandardSmooth

-- Proof sketch: after base change to each residue field `κ(p)`, clause (5) reduces the statement
-- to the field case. There the standard smooth algebra is a local complete intersection, and the
-- cotangent and conormal freeness from clauses (2) and (3) give the expected fiber dimension,
-- which is exactly the relative global complete intersection condition.
/-- Chap10 Lemma 10 137 6 (5): a standard smooth `R`-algebra is a relative global complete
intersection over `R`. -/
@[stacks 00T7]
theorem isRelativeGlobalCompleteIntersection (hS : IsStandardSmooth R S) :
    IsRelativeGlobalCompleteIntersection R S := by
  classical
  -- Choose the finite submersive presentation supplied by standard smoothness and turn its
  -- arbitrary finite index types into `Fin` index types for the intrinsic RGCI witness.
  rcases hS.out with ⟨ι, σ, hσ, hι, ⟨P⟩⟩
  letI : Finite σ := hσ
  letI : Finite ι := hι
  letI : Fintype σ := Fintype.ofFinite σ
  letI : Fintype ι := Fintype.ofFinite ι
  let Q : Algebra.Presentation R S (Fin (Fintype.card ι)) (Fin (Fintype.card σ)) :=
    (P.reindex (Fintype.equivFin ι).symm (Fintype.equivFin σ).symm).toPresentation
  refine Algebra.Presentation.toIsRelativeGlobalCompleteIntersection (P := Q) ?_
  intro p hp
  -- Nonempty fibers are exactly the nontrivial fibers needed by the field-level dimension helper.
  letI : Nontrivial (p.asIdeal.Fiber S) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp hp
  simpa [Q] using
    SubmersivePresentation.fiber_ringKrullDim_eq_reindexFin_dimension P p

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
