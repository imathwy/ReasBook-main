import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CanonicalSourceProductSerreIntegralRepresentatives

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section CanonicalSourceProductSerreBasisSourceQuotient

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

local instance canonicalSourceProductSerreBasisSourceQuotientFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance canonicalSourceProductSerreBasisSourceQuotientDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The coordinate integer lattice mapped into Serre's canonical source quotient. -/
noncomputable def regularIntegerFunctionCastToCanonicalVirtualModularCartanRangeASpanQuotient :
    (PRegularConjClass G p → ℤ) →+
      ((PRegularConjClass G p → K) ⧸
        canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G)) :=
  (canonicalVirtualModularCartanRangeASpan
      (p := p) (A := A) (K := K) (G := G)).mkQ.toAddMonoidHom.comp
    (regularIntegerFunctionCast (p := p) (K := K) (G := G))

@[simp]
theorem regularIntegerFunctionCastToCanonicalVirtualModularCartanRangeASpanQuotient_apply
    (g : PRegularConjClass G p → ℤ) :
    regularIntegerFunctionCastToCanonicalVirtualModularCartanRangeASpanQuotient
        (p := p) (A := A) (K := K) (G := G) g =
      Submodule.Quotient.mk
        (p := canonicalVirtualModularCartanRangeASpan
          (p := p) (A := A) (K := K) (G := G))
        (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) := by
  rfl

/-- The integral Serre 18.4 Brauer-basis lattice in `R₀[k](G)`. -/
noncomputable def serreBasisIntegerCombination
    (π : ι → FDRep k G) :
    (ι → ℤ) →+ R₀[k](G) where
  toFun m := ∑ i : ι, m i • ([π i]₀ : R₀[k](G))
  map_zero' := by
    simp
  map_add' m n := by
    dsimp
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [add_zsmul]

@[simp]
theorem serreBasisIntegerCombination_apply
    (π : ι → FDRep k G) (m : ι → ℤ) :
    serreBasisIntegerCombination π m =
      ∑ i : ι, m i • ([π i]₀ : R₀[k](G)) := by
  rfl

/-- The Serre 18.4 simple Brauer-character lattice mapped into the canonical source quotient. -/
noncomputable def canonicalSourceProductSerreBasisToCanonicalQuotient
    (π : ι → FDRep k G) :
    (ι → ℤ) →+
      ((PRegularConjClass G p → K) ⧸
        canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G)) :=
  ((canonicalVirtualModularCartanRangeASpan
      (p := p) (A := A) (K := K) (G := G)).mkQ.toAddMonoidHom.comp
    (virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K))))).comp
    (serreBasisIntegerCombination π)

@[simp]
theorem canonicalSourceProductSerreBasisToCanonicalQuotient_apply
    (π : ι → FDRep k G) (m : ι → ℤ) :
    canonicalSourceProductSerreBasisToCanonicalQuotient
        (p := p) (A := A) (K := K) (G := G) π m =
      Submodule.Quotient.mk
        (p := canonicalVirtualModularCartanRangeASpan
          (p := p) (A := A) (K := K) (G := G))
        (virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          (∑ i : ι, m i • ([π i]₀ : R₀[k](G)))) := by
  unfold canonicalSourceProductSerreBasisToCanonicalQuotient
  change
    Submodule.Quotient.mk
        (p := canonicalVirtualModularCartanRangeASpan
          (p := p) (A := A) (K := K) (G := G))
        (virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          (serreBasisIntegerCombination π m)) =
      Submodule.Quotient.mk
        (p := canonicalVirtualModularCartanRangeASpan
          (p := p) (A := A) (K := K) (G := G))
        (virtualModularCharacterOnPRegularConjClass
          (p := p) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift
            (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
          (∑ i : ι, m i • ([π i]₀ : R₀[k](G))))
  rw [serreBasisIntegerCombination_apply]

/-- Source quotient image match for a Serre 18.4 Brauer basis.

This is the source-lattice form of Serre 18.5(b): after quotienting by the Serre 18.5(a)
divisibility lattice, the integer span of the Brauer basis has the same image as the coordinate
integer lattice. -/
def canonicalSourceProductSerreBasisSourceQuotientImageMatchesIntegerImage
    (π : ι → FDRep k G) : Prop :=
  (canonicalSourceProductSerreBasisToCanonicalQuotient
      (p := p) (A := A) (K := K) (G := G) π).range =
    (regularIntegerFunctionCastToCanonicalVirtualModularCartanRangeASpanQuotient
      (p := p) (A := A) (K := K) (G := G)).range

/-- Source quotient image match for the actual Cartan source image. -/
def canonicalVirtualModularCartanSourceQuotientImageMatchesIntegerImage : Prop :=
  (cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient
      (p := p) (A := A) (K := K) (G := G)).range =
    (regularIntegerFunctionCastToCanonicalVirtualModularCartanRangeASpanQuotient
      (p := p) (A := A) (K := K) (G := G)).range

omit [DecidableEq ι] in
/-- Forward and reverse Serre-basis representatives identify the two source-quotient images.

This is the quotient-level form of the Serre-basis route: the forward representatives put every
integral Serre-basis row in the coordinate integer image, and the reverse point representatives
put every coordinate point mass in the integral Serre-basis image. -/
theorem canonicalSourceProductSerreBasisSourceQuotientImageMatchesIntegerImage_of_forward_reverse
    (π : ι → FDRep k G)
    (hforward :
      canonicalSourceProductSerreBasisForwardInput
        (p := p) (A := A) (K := K) (G := G) π)
    (hreverse :
      canonicalSourceProductSerreBasisReversePointInput
        (p := p) (A := A) (K := K) (G := G) π) :
    canonicalSourceProductSerreBasisSourceQuotientImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) π := by
  classical
  let χ : R₀[k](G) →+ (PRegularConjClass G p → K) :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
  let S : Submodule A (PRegularConjClass G p → K) :=
    canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G)
  choose g hg using hforward
  choose m hm using hreverse
  apply le_antisymm
  · rintro q ⟨n, hn⟩
    let gsum : PRegularConjClass G p → ℤ := ∑ i : ι, n i • g i
    refine ⟨gsum, ?_⟩
    rw [← hn]
    have hχ_sum :
        χ (∑ i : ι, n i • ([π i]₀ : R₀[k](G))) =
          ∑ i : ι, n i • χ ([π i]₀ : R₀[k](G)) := by
      calc
        χ (∑ i : ι, n i • ([π i]₀ : R₀[k](G))) =
            ∑ i : ι, χ (n i • ([π i]₀ : R₀[k](G))) := by
              rw [map_sum]
        _ = ∑ i : ι, n i • χ ([π i]₀ : R₀[k](G)) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              rw [map_zsmul]
    have hcast_sum :
        regularIntegerFunctionCast (p := p) (K := K) (G := G) gsum =
          ∑ i : ι,
            n i • regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i) := by
      ext c
      simp [gsum, regularIntegerFunctionCast, Finset.sum_apply]
    have hdiff :
        χ (∑ i : ι, n i • ([π i]₀ : R₀[k](G))) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) gsum =
          ∑ i : ι,
            n i •
              (χ ([π i]₀ : R₀[k](G)) -
                regularIntegerFunctionCast (p := p) (K := K) (G := G) (g i)) := by
      rw [hχ_sum, hcast_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [zsmul_sub]
    have hmem :
        χ (∑ i : ι, n i • ([π i]₀ : R₀[k](G))) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) gsum ∈ S := by
      rw [hdiff]
      refine Submodule.sum_mem S ?_
      intro i _hi
      exact S.toAddSubgroup.zsmul_mem (by simpa [S, χ] using hg i) (n i)
    have hq :
        Submodule.Quotient.mk (p := S)
            (χ (∑ i : ι, n i • ([π i]₀ : R₀[k](G)))) =
          Submodule.Quotient.mk (p := S)
            (regularIntegerFunctionCast (p := p) (K := K) (G := G) gsum) :=
      (Submodule.Quotient.eq S).2 hmem
    calc
      regularIntegerFunctionCastToCanonicalVirtualModularCartanRangeASpanQuotient
          (p := p) (A := A) (K := K) (G := G) gsum =
        Submodule.Quotient.mk (p := S)
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) gsum) := by
          rfl
      _ =
        Submodule.Quotient.mk (p := S)
          (χ (∑ i : ι, n i • ([π i]₀ : R₀[k](G)))) := hq.symm
      _ =
        canonicalSourceProductSerreBasisToCanonicalQuotient
            (p := p) (A := A) (K := K) (G := G) π n := by
          exact
            (canonicalSourceProductSerreBasisToCanonicalQuotient_apply
              (p := p) (A := A) (K := K) (G := G) π n).symm
  · rintro q ⟨g₀, hg₀⟩
    let nsum : ι → ℤ := ∑ c : PRegularConjClass G p, g₀ c • m c
    refine ⟨nsum, ?_⟩
    rw [← hg₀]
    have hχ_sum :
        χ (∑ i : ι, nsum i • ([π i]₀ : R₀[k](G))) =
          ∑ i : ι, nsum i • χ ([π i]₀ : R₀[k](G)) := by
      calc
        χ (∑ i : ι, nsum i • ([π i]₀ : R₀[k](G))) =
            ∑ i : ι, χ (nsum i • ([π i]₀ : R₀[k](G))) := by
              rw [map_sum]
        _ = ∑ i : ι, nsum i • χ ([π i]₀ : R₀[k](G)) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              rw [map_zsmul]
    have hsource_sum :
        ∑ i : ι, nsum i • χ ([π i]₀ : R₀[k](G)) =
          ∑ c : PRegularConjClass G p,
            g₀ c •
              (∑ i : ι, m c i • χ ([π i]₀ : R₀[k](G))) := by
      calc
        ∑ i : ι, nsum i • χ ([π i]₀ : R₀[k](G)) =
            ∑ i : ι,
              (∑ c : PRegularConjClass G p, g₀ c • m c i) •
                χ ([π i]₀ : R₀[k](G)) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              congr 1
              simp [nsum, Finset.sum_apply]
        _ =
            ∑ i : ι, ∑ c : PRegularConjClass G p,
              (g₀ c • m c i) • χ ([π i]₀ : R₀[k](G)) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              simpa using
                (Finset.sum_smul
                  (s := Finset.univ)
                  (f := fun c : PRegularConjClass G p => g₀ c • m c i)
                  (x := χ ([π i]₀ : R₀[k](G))))
        _ =
            ∑ c : PRegularConjClass G p, ∑ i : ι,
              (g₀ c • m c i) • χ ([π i]₀ : R₀[k](G)) := by
              rw [Finset.sum_comm]
        _ =
            ∑ c : PRegularConjClass G p,
              g₀ c •
                (∑ i : ι, m c i • χ ([π i]₀ : R₀[k](G))) := by
              refine Finset.sum_congr rfl ?_
              intro c _hc
              calc
                ∑ i : ι, (g₀ c • m c i) • χ ([π i]₀ : R₀[k](G)) =
                    ∑ i : ι, g₀ c • (m c i • χ ([π i]₀ : R₀[k](G))) := by
                    refine Finset.sum_congr rfl ?_
                    intro i _hi
                    rw [smul_assoc]
                _ =
                    g₀ c •
                      (∑ i : ι, m c i • χ ([π i]₀ : R₀[k](G))) := by
                    rw [Finset.smul_sum]
    have hcast_point_sum :
        regularIntegerFunctionCast (p := p) (K := K) (G := G) g₀ =
          ∑ c : PRegularConjClass G p,
            g₀ c •
              regularIntegerFunctionCast (p := p) (K := K) (G := G)
                (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) := by
      ext d
      simp [regularIntegerFunctionCast, Pi.single_apply, zsmul_eq_mul]
    have hdiff :
        regularIntegerFunctionCast (p := p) (K := K) (G := G) g₀ -
            χ (∑ i : ι, nsum i • ([π i]₀ : R₀[k](G))) =
          ∑ c : PRegularConjClass G p,
            g₀ c •
              (regularIntegerFunctionCast (p := p) (K := K) (G := G)
                  (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ) -
                ∑ i : ι, m c i • χ ([π i]₀ : R₀[k](G))) := by
      rw [hχ_sum, hsource_sum, hcast_point_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro c _hc
      rw [zsmul_sub]
    have hmem :
        regularIntegerFunctionCast (p := p) (K := K) (G := G) g₀ -
            χ (∑ i : ι, nsum i • ([π i]₀ : R₀[k](G))) ∈ S := by
      rw [hdiff]
      refine Submodule.sum_mem S ?_
      intro c _hc
      exact S.toAddSubgroup.zsmul_mem (by simpa [S, χ] using hm c) (g₀ c)
    have hmem' :
        χ (∑ i : ι, nsum i • ([π i]₀ : R₀[k](G))) -
            regularIntegerFunctionCast (p := p) (K := K) (G := G) g₀ ∈ S := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using S.neg_mem hmem
    have hq :
        Submodule.Quotient.mk (p := S)
            (χ (∑ i : ι, nsum i • ([π i]₀ : R₀[k](G)))) =
          Submodule.Quotient.mk (p := S)
            (regularIntegerFunctionCast (p := p) (K := K) (G := G) g₀) :=
      (Submodule.Quotient.eq S).2 hmem'
    calc
      canonicalSourceProductSerreBasisToCanonicalQuotient
          (p := p) (A := A) (K := K) (G := G) π nsum =
        Submodule.Quotient.mk (p := S)
          (χ (∑ i : ι, nsum i • ([π i]₀ : R₀[k](G)))) := by
          exact
            canonicalSourceProductSerreBasisToCanonicalQuotient_apply
              (p := p) (A := A) (K := K) (G := G) π nsum
      _ =
        Submodule.Quotient.mk (p := S)
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) g₀) := hq
      _ =
        regularIntegerFunctionCastToCanonicalVirtualModularCartanRangeASpanQuotient
          (p := p) (A := A) (K := K) (G := G) g₀ := by
          rfl

omit [DecidableEq ι] in
/-- Integer representatives modulo Serre's divisibility lattice give the Serre-basis
source-quotient image equality. -/
theorem canonicalSourceProductSerreBasisSourceQuotientImageMatchesIntegerImage_of_integerRepresentativesModuloD
    (π : ι → FDRep k G)
    (hreps :
      canonicalSourceProductSerreBasisIntegerRepresentativesModuloD
        (p := p) (A := A) (K := K) (G := G) π) :
    canonicalSourceProductSerreBasisSourceQuotientImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) π :=
  canonicalSourceProductSerreBasisSourceQuotientImageMatchesIntegerImage_of_forward_reverse
    (p := p) (A := A) (K := K) (G := G) π
    ((canonicalSourceProductSerreBasisForwardInput_iff_forwardDivisibilityRepresentatives
      (p := p) (A := A) (K := K) (G := G) π).2 hreps.1)
    ((canonicalSourceProductSerreBasisReversePointInput_iff_reversePointDivisibilityRepresentatives
      (p := p) (A := A) (K := K) (G := G) π).2 hreps.2)

omit [DecidableEq ι] in
/-- The image of the actual Cartan source quotient is the image of the integral Serre 18.4
Brauer-basis lattice, for any complete simple family. -/
theorem cartanSourceQuotient_range_eq_serreBasisSourceQuotient_range
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    (cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient
        (p := p) (A := A) (K := K) (G := G)).range =
      (canonicalSourceProductSerreBasisToCanonicalQuotient
        (p := p) (A := A) (K := K) (G := G) π).range := by
  classical
  let χ : R₀[k](G) →+ (PRegularConjClass G p → K) :=
    virtualModularCharacterOnPRegularConjClass
      (p := p) (A := K) (G := G)
      (PrimeToPRoot.toFieldLift
        (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
  let S : Submodule A (PRegularConjClass G p → K) :=
    canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G)
  let bR := simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  apply le_antisymm
  · rintro q ⟨q₀, hq₀⟩
    revert hq₀
    refine QuotientAddGroup.induction_on q₀ ?_
    intro x hx
    let m : ι → ℤ := fun i ↦ bR.repr x i
    refine ⟨m, ?_⟩
    have hx_expand :
        (∑ i : ι, m i • ([π i]₀ : R₀[k](G))) = x := by
      calc
        (∑ i : ι, m i • ([π i]₀ : R₀[k](G))) =
            ∑ i : ι, (bR.repr x i) • bR i := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              simp [m, bR, simple_finiteRep_classes_basis_of_complete_family_apply]
        _ = x := bR.sum_repr x
    calc
      canonicalSourceProductSerreBasisToCanonicalQuotient
          (p := p) (A := A) (K := K) (G := G) π m =
        Submodule.Quotient.mk (p := S)
          (χ (∑ i : ι, m i • ([π i]₀ : R₀[k](G)))) := by
          rw [canonicalSourceProductSerreBasisToCanonicalQuotient_apply]
      _ = Submodule.Quotient.mk (p := S) (χ x) := by
          rw [hx_expand]
      _ = q := by
          simpa [S, χ] using hx
  · rintro q ⟨m, hm⟩
    refine
      ⟨QuotientAddGroup.mk' (cartanHom k G).range
        (∑ i : ι, m i • ([π i]₀ : R₀[k](G))), ?_⟩
    calc
      cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient
          (p := p) (A := A) (K := K) (G := G)
          (QuotientAddGroup.mk' (cartanHom k G).range
            (∑ i : ι, m i • ([π i]₀ : R₀[k](G)))) =
      Submodule.Quotient.mk (p := S)
          (χ (∑ i : ι, m i • ([π i]₀ : R₀[k](G)))) := by
          rfl
      _ =
        canonicalSourceProductSerreBasisToCanonicalQuotient
            (p := p) (A := A) (K := K) (G := G) π m := by
          rw [canonicalSourceProductSerreBasisToCanonicalQuotient_apply]
      _ = q := hm

omit [Fintype ι] [DecidableEq ι] in
/-- A source quotient image match gives the minimal source-congruence representative statement. -/
theorem canonicalVirtualModularCartanProductImageSourceCongruences_of_sourceQuotient_range_eq
    (hmatch :
      canonicalVirtualModularCartanSourceQuotientImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G)) :
    canonicalVirtualModularCartanProductImageSourceCongruences
      (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro x
    let χ : R₀[k](G) →+ (PRegularConjClass G p → K) :=
      virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
    let S : Submodule A (PRegularConjClass G p → K) :=
      canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G)
    let q : (PRegularConjClass G p → K) ⧸ S := Submodule.Quotient.mk (p := S) (χ x)
    have hcartan :
        q ∈
          (cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient
            (p := p) (A := A) (K := K) (G := G)).range := by
      refine ⟨QuotientAddGroup.mk' (cartanHom k G).range x, ?_⟩
      rfl
    have hint :
        q ∈
          (regularIntegerFunctionCastToCanonicalVirtualModularCartanRangeASpanQuotient
            (p := p) (A := A) (K := K) (G := G)).range := by
      change
        q ∈
          (regularIntegerFunctionCastToCanonicalVirtualModularCartanRangeASpanQuotient
            (p := p) (A := A) (K := K) (G := G)).range
      rw [← hmatch]
      exact hcartan
    rcases hint with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    have hq :
        Submodule.Quotient.mk (p := S) (χ x) =
          Submodule.Quotient.mk (p := S)
            (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) := by
      simpa [q, S, χ,
        regularIntegerFunctionCastToCanonicalVirtualModularCartanRangeASpanQuotient] using hg.symm
    simpa [S, χ] using (Submodule.Quotient.eq S).1 hq
  · intro g
    let χ : R₀[k](G) →+ (PRegularConjClass G p → K) :=
      virtualModularCharacterOnPRegularConjClass
        (p := p) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift
          (projectiveCartanASpanFieldLift (p := p) (A := A) (K := K)))
    let S : Submodule A (PRegularConjClass G p → K) :=
      canonicalVirtualModularCartanRangeASpan (p := p) (A := A) (K := K) (G := G)
    let q : (PRegularConjClass G p → K) ⧸ S :=
      Submodule.Quotient.mk (p := S)
        (regularIntegerFunctionCast (p := p) (K := K) (G := G) g)
    have hint :
        q ∈
          (regularIntegerFunctionCastToCanonicalVirtualModularCartanRangeASpanQuotient
            (p := p) (A := A) (K := K) (G := G)).range := by
      exact ⟨g, rfl⟩
    have hcartan :
        q ∈
          (cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient
            (p := p) (A := A) (K := K) (G := G)).range := by
      change
        q ∈
          (cartanCokernelToCanonicalVirtualModularCartanRangeASpanQuotient
            (p := p) (A := A) (K := K) (G := G)).range
      rw [hmatch]
      exact hint
    rcases hcartan with ⟨q₀, hq₀⟩
    revert hq₀
    refine QuotientAddGroup.induction_on q₀ ?_
    intro x hx
    refine ⟨x, ?_⟩
    have hq :
        Submodule.Quotient.mk (p := S)
            (regularIntegerFunctionCast (p := p) (K := K) (G := G) g) =
          Submodule.Quotient.mk (p := S) (χ x) := by
      simpa [q, S, χ,
        regularIntegerFunctionCastToCanonicalVirtualModularCartanRangeASpanQuotient] using hx.symm
    simpa [S, χ] using (Submodule.Quotient.eq S).1 hq

omit [Fintype ι] [DecidableEq ι] in
/-- Source quotient image match implies the source-product image match. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_sourceQuotient_range_eq
    (hmatch :
      canonicalVirtualModularCartanSourceQuotientImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G)) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) :=
  canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_source_congruences
    (p := p) (A := A) (K := K) (G := G)
    (canonicalVirtualModularCartanProductImageSourceCongruences_of_sourceQuotient_range_eq
      (p := p) (A := A) (K := K) (G := G) hmatch)

/-- Serre 18.4 source-basis quotient image match implies the canonical source-product image
identification. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasis_sourceQuotientImageMatch
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hmatch :
      canonicalSourceProductSerreBasisSourceQuotientImageMatchesIntegerImage
        (p := p) (A := A) (K := K) (G := G) π) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) := by
  refine
    canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_sourceQuotient_range_eq
      (p := p) (A := A) (K := K) (G := G) ?_
  exact
    (cartanSourceQuotient_range_eq_serreBasisSourceQuotient_range
      (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete).trans hmatch

/-- Source-quotient route from Serre-basis integer representatives modulo the divisibility
lattice to the canonical source-product image statement. -/
theorem canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasis_integerRepresentativesModuloD_sourceQuotient
    (π : ι → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hreps :
      canonicalSourceProductSerreBasisIntegerRepresentativesModuloD
        (p := p) (A := A) (K := K) (G := G) π) :
    canonicalVirtualModularCartanProductImageMatchesIntegerImage
      (p := p) (A := A) (K := K) (G := G) :=
  canonicalVirtualModularCartanProductImageMatchesIntegerImage_of_serreBasis_sourceQuotientImageMatch
    (p := p) (A := A) (K := K) (G := G) π hπ_pairwise hπ_complete
    (canonicalSourceProductSerreBasisSourceQuotientImageMatchesIntegerImage_of_integerRepresentativesModuloD
      (p := p) (A := A) (K := K) (G := G) π hreps)

end CanonicalSourceProductSerreBasisSourceQuotient

end Representation
