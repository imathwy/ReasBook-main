import Mathlib
import StacksProject_2024.Chap10.Lemma_10_154_2
import StacksProject_2024.Chap10.Lemma_10_154_6
import StacksProject_2024.Chap10.Lemma_10_154_7
import StacksProject_2024.Chap10.Lemma_10_155_1
import StacksProject_2024.Chap15.Lemma_15_12_1
import StacksProject_2024.Chap15.Lemma_15_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open IsLocalRing
open RingPairCat

universe u

noncomputable section

section

variable (A : Type u) [CommRing A] [IsLocalRing A]

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

local notation "A_pair" => pairOfIdeal (maximalIdeal A)
local notation "A_h" => henselizationRing A_pair

/-- Helper for Lemma 15.12.3: the maximal-ideal residue field agrees with the ambient residue
field of a local ring. -/
private noncomputable abbrev maximalIdealResidueFieldEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] :
    (maximalIdeal R).ResidueField ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm

/-- Helper for Lemma 15.12.3: quotienting a local ring by its maximal ideal gives its residue
field. -/
private noncomputable abbrev maximalIdealQuotientResidueFieldEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] :
    R ⧸ maximalIdeal R ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).trans
      (maximalIdealResidueFieldEquiv R)

/-- Helper for Lemma 15.12.3: a surjective local map to a field induces a bijection on residue
field lifts. -/
private theorem residueField_lift_bijective_of_surjective_localHom
    {R K : Type u} [CommRing R] [IsLocalRing R] [Field K]
    (f : R →+* K) (hf : Function.Surjective f) [IsLocalHom f] :
    Function.Bijective (ResidueField.lift f) := by
  constructor
  · exact RingHom.injective (ResidueField.lift f)
  · intro z
    obtain ⟨x, rfl⟩ := hf z
    exact ⟨residue R x, IsLocalRing.ResidueField.lift_residue_apply f x⟩

/-- Helper for Lemma 15.12.3: the distinguished ideal in the pair-henselization of
`(A, maximalIdeal A)` is maximal. -/
private theorem pair_henselizationIdeal_isMaximal :
    Ideal.IsMaximal (henselizationIdeal A_pair) := by
  let qmap :
      A ⧸ (maximalIdeal A ^ 1) →+* A_h ⧸ (henselizationIdeal A_pair ^ 1) :=
    Ideal.quotientMap
      (henselizationIdeal A_pair ^ 1)
      (toHenselization A_pair)
      (by
        simpa [henselizationIdeal_eq_map (X := A_pair), ← Ideal.map_pow] using
          (Ideal.le_comap_map :
            maximalIdeal A ^ 1 ≤
              Ideal.comap (toHenselization A_pair)
                (Ideal.map (toHenselization A_pair) (maximalIdeal A ^ 1))))
  let e :
      A ⧸ (maximalIdeal A ^ 1) ≃+* A_h ⧸ (henselizationIdeal A_pair ^ 1) :=
    RingEquiv.ofBijective qmap
      (by simpa [qmap] using quotientPowToHenselization_bijective (X := A_pair) 1)
  have hFieldSource : IsField (A ⧸ (maximalIdeal A ^ 1)) := by
    simpa using ((Ideal.Quotient.field (maximalIdeal A)).toIsField :
      IsField (A ⧸ maximalIdeal A))
  let hFieldTarget : IsField (A_h ⧸ (henselizationIdeal A_pair ^ 1)) :=
    e.toMulEquiv.isField hFieldSource
  have hmaxPow : Ideal.IsMaximal (henselizationIdeal A_pair ^ 1) :=
    Ideal.Quotient.maximal_of_isField (henselizationIdeal A_pair ^ 1) hFieldTarget
  simpa using hmaxPow

/-- Helper for Lemma 15.12.3: the pair-henselization object is henselian at its distinguished
ideal. -/
private instance pair_henselization_instHenselianRing :
    HenselianRing A_h (henselizationIdeal A_pair) := by
  change HenselianRing (henselizationPair A_pair).ring (henselizationPair A_pair).ideal
  exact (henselization A_pair).property

/-- Helper for Lemma 15.12.3: the pair-henselization ring of `(A, maximalIdeal A)` is local. -/
private theorem pair_henselization_isLocalRing :
    IsLocalRing A_h := by
  refine IsLocalRing.of_unique_max_ideal ?_
  refine ⟨henselizationIdeal A_pair, pair_henselizationIdeal_isMaximal A, ?_⟩
  intro J hJ
  have hI_jac :
      henselizationIdeal A_pair ≤ Ring.jacobson A_h := by
    simpa [Ideal.jacobson_bot] using
      (show henselizationIdeal A_pair ≤ Ideal.jacobson (⊥ : Ideal A_h) from
        HenselianRing.jac (R := A_h) (I := henselizationIdeal A_pair))
  have hIJ : henselizationIdeal A_pair ≤ J := by
    exact hI_jac.trans (Ring.jacobson_le_of_isMaximal J)
  exact ((pair_henselizationIdeal_isMaximal A).eq_of_le hJ.ne_top hIJ).symm

/-- Helper for Lemma 15.12.3: the pair-henselization ring inherits the local-ring structure just
proved. -/
private instance pair_henselization_instIsLocalRing :
    IsLocalRing A_h :=
  pair_henselization_isLocalRing A

/-- Helper for Lemma 15.12.3: in the pair-henselization of `(A, maximalIdeal A)`, the
distinguished ideal is the maximal ideal. -/
private theorem pair_henselizationIdeal_eq_maximalIdeal :
    henselizationIdeal A_pair = maximalIdeal A_h := by
  exact IsLocalRing.eq_maximalIdeal (pair_henselizationIdeal_isMaximal A)

/-- Helper for Lemma 15.12.3: the structural map `A → A^h` of the pair-henselization is local
once `A^h` is viewed as a local ring. -/
private theorem pair_henselization_isLocalHom :
    IsLocalHom (algebraMap A A_h) := by
  have hmap :
      Ideal.map (algebraMap A A_h) (maximalIdeal A) = maximalIdeal A_h := by
    calc
      Ideal.map (algebraMap A A_h) (maximalIdeal A) = henselizationIdeal A_pair := by
        symm
        simpa using henselizationIdeal_eq_map (X := A_pair)
      _ = maximalIdeal A_h := pair_henselizationIdeal_eq_maximalIdeal A
  exact ((IsLocalRing.local_hom_TFAE (algebraMap A A_h)).out 2 0).mp <| by
    simpa [hmap]

/-- Helper for Lemma 15.12.3: the pair-henselization of `(A, maximalIdeal A)` is henselian as a
local ring. -/
private theorem pair_henselization_henselianLocalRing :
    HenselianLocalRing A_h := by
  refine
    { toIsLocalRing := pair_henselization_isLocalRing A
      is_henselian := ?_ }
  intro f hf a₀ ha₀ hderiv
  have hroot :=
    HenselianRing.is_henselian (R := A_h) (I := henselizationIdeal A_pair) f hf a₀
      (by simpa [pair_henselizationIdeal_eq_maximalIdeal A] using ha₀)
      (IsUnit.map (Ideal.Quotient.mk (henselizationIdeal A_pair)) hderiv)
  rcases hroot with ⟨a, ha, hmem⟩
  refine ⟨a, ha, ?_⟩
  simpa [pair_henselizationIdeal_eq_maximalIdeal A] using hmem

-- Proof sketch: the henselization pair `(A, maximalIdeal A)` is henselian by construction. Lemma
-- `15.12.2` identifies its distinguished ideal with the image of `maximalIdeal A`, so the target
-- has the expected maximal ideal and residue field, and the filtered-colimit-of-etale condition is
-- the same one appearing in the pair-henselization construction of Lemma `15.12.1`.
/-- Lemma 15.12.3: the pair-henselization functor sends a local ring `A`, viewed as the pair
`(A, maximalIdeal A)`, to a henselization of `A` as a local ring. -/
@[stacks 0A03]
theorem localRing_henselization_isHenselizationOf :
    IsHenselizationOf A (henselizationRing (pairOfIdeal (maximalIdeal A))) := sorry

/-- The pair-henselization of a local ring is available to typeclass search as a henselization. -/
instance localRing_henselization.instIsHenselizationOf :
    IsHenselizationOf A (henselizationRing (pairOfIdeal (maximalIdeal A))) :=
  localRing_henselization_isHenselizationOf A

end
