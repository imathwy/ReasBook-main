import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegerDescent
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.IntegerDivisibilityDescent
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.IntegerLatticeSaturation
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularIntegerDiagonalQuotient

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanCokernelSaturation

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanCokernelSaturationFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanCokernelSaturationDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The fixed regular-class coordinate map identifies the Cartan cokernel with the quotient by the
integer Cartan coordinate range. -/
noncomputable def cartanCokernel_addEquiv_cartanCoordinateRangeQuotient :
    cartanCokernel k G ≃+
      ((PRegularConjClass G p → ℤ) ⧸
        (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range) := by
  let e := regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)
  have hmap :
      (cartanHom k G).range.map e.toAddMonoidHom =
        (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range := by
    ext f
    constructor
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨cartanHom k G x, ⟨x, rfl⟩, rfl⟩
  simpa [cartanCokernel, e] using
    QuotientAddGroup.congr
      ((cartanHom k G).range)
      ((cartanCoordinateAddHom (p := p) (k := k) (G := G)).range)
      e
      hmap

/-- The fixed-coordinate quotient by the Cartan coordinate range is finite. -/
theorem cartanCoordinateAddHom_range_quotient_finite :
    Finite
      ((PRegularConjClass G p → ℤ) ⧸
        (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range) := by
  letI : Finite (cartanCokernel k G) :=
    cartanCokernel_finite (p := p) (k := k) (G := G)
  exact Finite.of_equiv (cartanCokernel k G)
    (cartanCokernel_addEquiv_cartanCoordinateRangeQuotient
      (p := p) (k := k) (G := G)).toEquiv

/-- The fixed-coordinate quotient by the Cartan coordinate range is a `p`-group. -/
theorem cartanCoordinateAddHom_range_quotient_isPGroup :
    IsPGroup p
      (Multiplicative
        ((PRegularConjClass G p → ℤ) ⧸
          (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range)) := by
  exact (cartanCokernel_isPGroup (p := p) (k := k) (G := G)).of_equiv
    (AddEquiv.toMultiplicative
      (cartanCokernel_addEquiv_cartanCoordinateRangeQuotient
        (p := p) (k := k) (G := G)))

/-- The fixed regular-class coordinate equivalence transports the abstract Cartan range to the
integer coordinate range. -/
theorem cartanHom_range_map_regularClassCoordinateAddEquiv_eq_cartanCoordinateAddHom_range :
    (cartanHom k G).range.map
        (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom =
      (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range := by
  ext f
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨cartanHom k G x, ⟨x, rfl⟩, rfl⟩

/-- Prime-to-`p` saturation inside the fixed-coordinate Cartan quotient: because the quotient is a
`p`-group, a class killed by a number coprime to `p` is already zero. -/
theorem cartanCoordinateAddHom_mem_range_of_coprime_nsmul_mem_range
    {n : ℕ} (hn : Nat.Coprime n p) {f : PRegularConjClass G p → ℤ}
    (hf :
      n • f ∈ (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range) :
    f ∈ (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range := by
  let R : AddSubgroup (PRegularConjClass G p → ℤ) :=
    (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range
  let q : ((PRegularConjClass G p → ℤ) ⧸ R) := QuotientAddGroup.mk' R f
  have hnq : n • q = 0 := by
    calc
      n • q = QuotientAddGroup.mk' R (n • f) := by
        simp [q]
      _ = 0 := (QuotientAddGroup.eq_zero_iff (N := R) (n • f)).2
        (by simpa [R] using hf)
  have hpgroup : IsPGroup p (Multiplicative (((PRegularConjClass G p → ℤ) ⧸ R))) := by
    simpa [R] using
      cartanCoordinateAddHom_range_quotient_isPGroup (p := p) (k := k) (G := G)
  obtain ⟨e, horder⟩ :=
    (IsPGroup.iff_orderOf.mp hpgroup) (Multiplicative.ofAdd q)
  have hpow : (Multiplicative.ofAdd q) ^ n = 1 := by
    simpa using congrArg Multiplicative.ofAdd hnq
  have hdvdn : orderOf (Multiplicative.ofAdd q) ∣ n :=
    orderOf_dvd_of_pow_eq_one hpow
  have hpowe_dvd_n : p ^ e ∣ n := by
    simpa [horder] using hdvdn
  have hpowe_coprime_n : Nat.Coprime (p ^ e) n :=
    Nat.Coprime.pow_left e hn.symm
  have hpowe_eq_one : p ^ e = 1 :=
    hpowe_coprime_n.eq_one_of_dvd hpowe_dvd_n
  have horder_one : orderOf (Multiplicative.ofAdd q) = 1 := by
    rw [horder, hpowe_eq_one]
  have hq_one : Multiplicative.ofAdd q = 1 := orderOf_eq_one_iff.mp horder_one
  have hq_zero : q = 0 := by
    simpa using congrArg Multiplicative.toAdd hq_one
  exact (QuotientAddGroup.eq_zero_iff (N := R) f).1 (by simpa [q] using hq_zero)

/-- Formal cokernel adapter for Exercise 18-18.3-2.

Once the fixed regular-class coordinate map identifies the integer Cartan coordinate range with
the regular diagonal lattice, the Cartan cokernel is the corresponding regular integer diagonal
quotient. -/
noncomputable def cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_coordinateRange_eq
    (hrange :
      (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :
    cartanCokernel k G ≃+
      ((PRegularConjClass G p → ℤ) ⧸
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) := by
  let e := regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)
  have hmap :
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
    calc
      (cartanHom k G).range.map e.toAddMonoidHom =
          (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range := by
            ext f
            constructor
            · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
              exact ⟨x, rfl⟩
            · rintro ⟨x, rfl⟩
              exact ⟨cartanHom k G x, ⟨x, rfl⟩, rfl⟩
      _ = (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := hrange
  simpa [cartanCokernel, e] using
    QuotientAddGroup.congr
      ((cartanHom k G).range)
      ((regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
      e
      hmap

/-- Product form of
`cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_coordinateRange_eq`. -/
noncomputable def cartanCokernel_addEquiv_pi_centralizerPPart_of_coordinateRange_eq
    (hrange :
      (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :
    cartanCokernel k G ≃+
      ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1) :=
  (cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_coordinateRange_eq
      (p := p) (k := k) (G := G) hrange).trans
    (regularIntegerDiagonalQuotient_addEquiv_pi_centralizerPPart
      (p := p) (G := G))

/-- Nonempty wrapper for the range-equality quotient adapter. -/
theorem cartanCokernel_nonempty_addEquiv_regularIntegerDiagonalQuotient_of_coordinateRange_eq
    (hrange :
      (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :
    Nonempty
      (cartanCokernel k G ≃+
        ((PRegularConjClass G p → ℤ) ⧸
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)) :=
  ⟨cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_coordinateRange_eq
    (p := p) (k := k) (G := G) hrange⟩

/-- Nonempty wrapper for the range-equality cyclic-product adapter. -/
theorem cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_coordinateRange_eq
    (hrange :
      (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :
    Nonempty
      (cartanCokernel k G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
  ⟨cartanCokernel_addEquiv_pi_centralizerPPart_of_coordinateRange_eq
    (p := p) (k := k) (G := G) hrange⟩

/-- Existential coordinate-equivalence form of the fixed-coordinate range equality. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_coordinateRange_eq
    (hrange :
      (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine ⟨regularClassCoordinateAddEquiv (p := p) (k := k) (G := G), ?_⟩
  exact
    (cartanHom_range_map_regularClassCoordinateAddEquiv_eq_cartanCoordinateAddHom_range
      (p := p) (k := k) (G := G)).trans hrange

end CartanCokernelSaturation

section CartanCokernelSaturationDescent

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]

local instance cartanCokernelSaturationDescentFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanCokernelSaturationDescentDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The span equality from Serre 18.5(a) already supplies the diagonal-lattice containment needed
by the quotient adapters: every Cartan coordinate vector casts into the Cartan `A`-span, hence into
the regular value-divisibility lattice, and integer divisibility descent brings it back to the
integer diagonal lattice. -/
theorem cartanCoordinateAddHom_range_le_regularIntegerDiagonalSubmodule_of_span_eq
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    (cartanCoordinateAddHom
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  rintro f ⟨x, rfl⟩
  have hcast_span :
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (cartanCoordinateAddHom (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
        Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) := by
    rw [regularIntegerFunctionCast_cartanCoordinateAddHom
      (p := p) (A := A) (K := K) (G := G) x]
    exact Submodule.subset_span ⟨x, rfl⟩
  have hcast_regular :
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (cartanCoordinateAddHom (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    rw [← hspan]
    exact hcast_span
  have hdiag :
      cartanCoordinateAddHom (p := p) (k := IsLocalRing.ResidueField A) (G := G) x ∈
        regularIntegerDiagonalSubmodule (p := p) (G := G) :=
    (regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_iff
      (p := p) (A := A) (K := K) (G := G)).1 hcast_regular
  simpa using hdiag

omit [HenselianLocalRing A] [IsFractionRing A K] [IsDomain A]
  [IsDiscreteValuationRing A] [CharZero K] in
/-- Helper for Exercise 18-18.3-2: the fixed Cartan coordinate range has full rank as an
integer sublattice of the regular-class function lattice. -/
theorem cartanCoordinateAddHom_range_toIntSubmodule_finrank_eq :
    Module.finrank ℤ
        ((cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range.toIntSubmodule) =
      Module.finrank ℤ (PRegularConjClass G p → ℤ) := by
  let R : AddSubgroup (PRegularConjClass G p → ℤ) :=
    (cartanCoordinateAddHom (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range
  haveI : R.FiniteIndex := by
    have hquot : Finite ((PRegularConjClass G p → ℤ) ⧸ R) := by
      simpa [R] using
        cartanCoordinateAddHom_range_quotient_finite
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)
    exact AddSubgroup.finiteIndex_of_finite_quotient
  -- A finite-index subgroup of a finite free abelian group has the same ambient rank.
  simpa [R] using
    AddSubgroup.finrank_eq_of_finiteIndex
      (M := PRegularConjClass G p → ℤ) R

omit [HenselianLocalRing A] [IsDiscreteValuationRing A] in
/-- Helper for Exercise 18-18.3-2: Serre's prime-to-`p` denominator-clearing step for the fixed
Cartan coordinate range. If a cast integer function lies in the `A`-span of the cast Cartan
range, then a prime-to-`p` multiple already lies in the integral Cartan coordinate range. -/
theorem cartanCoordinateAddHom_range_coprime_nsmul_saturation
    (f : PRegularConjClass G p → ℤ)
    (hf :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) :
    ∃ n : ℕ,
      Nat.Coprime n p ∧
        n • f ∈
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range := by
  -- Delegate the Smith denominator-clearing argument to the integer-lattice API and supply the
  -- Cartan range's full-rank input from the finite Chapter 16 cokernel.
  exact
    cartanCoordinateAddHom_exists_coprime_nsmul_mem_range_of_regularIntegerFunctionCast_mem_span_of_full_rank
      (p := p) (A := A) (K := K) (G := G)
      (Pi.basisFun ℤ (PRegularConjClass G p))
      (cartanCoordinateAddHom_range_toIntSubmodule_finrank_eq
        (p := p) (A := A) (G := G))
      hf

omit [HenselianLocalRing A] [IsFractionRing A K] [IsDomain A] [IsDiscreteValuationRing A]
  [CharZero K] in
/-- Cast-saturation follows from the denominator-clearing form expected from localizing away from
`p`: if every cast span member has a prime-to-`p` multiple in the integer Cartan coordinate range,
then the member itself is in the range, because the fixed-coordinate quotient is a `p`-group. -/
theorem cartanCoordinateAddHom_range_cast_saturated_of_coprime_nsmul_mem_range
    (hclear :
      ∀ f : PRegularConjClass G p → ℤ,
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) →
          ∃ n : ℕ,
            Nat.Coprime n p ∧
              n • f ∈
                (cartanCoordinateAddHom
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    ∀ f : PRegularConjClass G p → ℤ,
      regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K)) →
        f ∈
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range := by
  intro f hf
  rcases hclear f hf with ⟨n, hn, hnmem⟩
  exact cartanCoordinateAddHom_mem_range_of_coprime_nsmul_mem_range
    (p := p) (k := IsLocalRing.ResidueField A) (G := G) hn hnmem

omit [HenselianLocalRing A] [IsDiscreteValuationRing A] in
/-- Helper for Exercise 18-18.3-2: the fixed Cartan coordinate range is cast-saturated in its
own mixed-characteristic `A`-span. This is the direct composition of the prime-to-`p`
denominator-clearing theorem with the fact that the fixed-coordinate Cartan quotient is a
`p`-group. -/
theorem cartanCoordinateAddHom_range_cast_saturated :
    ∀ f : PRegularConjClass G p → ℤ,
      regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K)) →
        f ∈
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range :=
  cartanCoordinateAddHom_range_cast_saturated_of_coprime_nsmul_mem_range
    (p := p) (A := A) (K := K) (G := G)
    (cartanCoordinateAddHom_range_coprime_nsmul_saturation
      (p := p) (A := A) (K := K) (G := G))

omit [HenselianLocalRing A] [IsDiscreteValuationRing A] in
/-- Helper for Exercise 18-18.3-2: the integer points of the `A`-span of the fixed Cartan
coordinate range are exactly the integral Cartan coordinate range. This is the source-lattice
descent statement supplied by prime-to-`p` denominator clearing, and it does not assume the fixed
coordinate span is the regular divisibility lattice. -/
theorem regularIntegerFunctionCast_mem_projectiveCartanCoordinate_span_iff_mem_cartanCoordinateAddHom_range
    (f : PRegularConjClass G p → ℤ) :
    regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
        Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) ↔
      f ∈
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range := by
  constructor
  · exact cartanCoordinateAddHom_range_cast_saturated
      (p := p) (A := A) (K := K) (G := G) f
  · rintro ⟨x, rfl⟩
    rw [regularIntegerFunctionCast_cartanCoordinateAddHom
      (p := p) (A := A) (K := K) (G := G) x]
    exact Submodule.subset_span ⟨x, rfl⟩

/-- Formal quotient bridge from explicit span/saturation descent hypotheses.

If the Cartan coordinate span is the regular value-divisibility lattice, the coordinate range is
contained in the regular diagonal lattice, and the cast-saturation condition holds, then the
coordinate range is forced to be the diagonal lattice. This theorem turns that equality into the
cokernel quotient. -/
noncomputable def cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_span_eq_and_saturation
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hsubset :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
    (hsaturated :
      ∀ f : PRegularConjClass G p → ℤ,
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) →
          f ∈
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    cartanCokernel (IsLocalRing.ResidueField A) G ≃+
      ((PRegularConjClass G p → ℤ) ⧸
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) := by
  have hrange :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
    apply le_antisymm
    · exact hsubset
    · intro f hf
      refine hsaturated f ?_
      rw [hspan]
      exact regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_of_mem
        (p := p) (A := A) (K := K) (G := G) (by simpa using hf)
  exact cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_coordinateRange_eq
    (p := p) (k := IsLocalRing.ResidueField A) (G := G) hrange

/-- Cyclic-product form of
`cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_span_eq_and_saturation`. -/
noncomputable def cartanCokernel_addEquiv_pi_centralizerPPart_of_span_eq_and_saturation
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hsubset :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
    (hsaturated :
      ∀ f : PRegularConjClass G p → ℤ,
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) →
          f ∈
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    cartanCokernel (IsLocalRing.ResidueField A) G ≃+
      ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1) :=
  (cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_span_eq_and_saturation
      (p := p) (A := A) (K := K) (G := G) hspan hsubset hsaturated).trans
    (regularIntegerDiagonalQuotient_addEquiv_pi_centralizerPPart
      (p := p) (G := G))

/-- Quotient bridge from the span equality and the remaining cast-saturation input. The diagonal
containment is derived from `hspan` by
`cartanCoordinateAddHom_range_le_regularIntegerDiagonalSubmodule_of_span_eq`. -/
noncomputable def
    cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_span_eq_and_cast_saturation
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hsaturated :
      ∀ f : PRegularConjClass G p → ℤ,
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) →
          f ∈
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    cartanCokernel (IsLocalRing.ResidueField A) G ≃+
      ((PRegularConjClass G p → ℤ) ⧸
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :=
  cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_span_eq_and_saturation
    (p := p) (A := A) (K := K) (G := G) hspan
    (cartanCoordinateAddHom_range_le_regularIntegerDiagonalSubmodule_of_span_eq
      (p := p) (A := A) (K := K) (G := G) hspan)
    hsaturated

/-- Cyclic-product bridge from the span equality and the remaining cast-saturation input. -/
noncomputable def cartanCokernel_addEquiv_pi_centralizerPPart_of_span_eq_and_cast_saturation
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hsaturated :
      ∀ f : PRegularConjClass G p → ℤ,
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) →
          f ∈
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    cartanCokernel (IsLocalRing.ResidueField A) G ≃+
      ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1) :=
  (cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_span_eq_and_cast_saturation
      (p := p) (A := A) (K := K) (G := G) hspan hsaturated).trans
    (regularIntegerDiagonalQuotient_addEquiv_pi_centralizerPPart
      (p := p) (G := G))

/-- Brauer-representation form of the saturation quotient adapter.

The existing `ProjectiveCartanIntegerDescent` API supplies
`projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span`; the extra
hypothesis here is exactly the remaining divisibility-stability input needed to turn that
Brauer-coordinate image into the regular divisibility lattice itself. -/
noncomputable def
    cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_brauerRepr_stable_and_saturation
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hbrauer :
      Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hsubset :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
    (hsaturated :
      ∀ f : PRegularConjClass G p → ℤ,
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) →
          f ∈
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    cartanCokernel (IsLocalRing.ResidueField A) G ≃+
      ((PRegularConjClass G p → ℤ) ⧸
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) := by
  have hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    have hbrauerSpan :=
      projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
    exact hbrauerSpan.symm.trans hbrauer
  exact cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_span_eq_and_saturation
    (p := p) (A := A) (K := K) (G := G) hspan hsubset hsaturated

/-- Cyclic-product form of
`cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_brauerRepr_stable_and_saturation`. -/
noncomputable def cartanCokernel_addEquiv_pi_centralizerPPart_of_brauerRepr_stable_and_saturation
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hbrauer :
      Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hsubset :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
    (hsaturated :
      ∀ f : PRegularConjClass G p → ℤ,
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) →
          f ∈
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    cartanCokernel (IsLocalRing.ResidueField A) G ≃+
      ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1) :=
  (cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_brauerRepr_stable_and_saturation
      (p := p) (A := A) (K := K) (G := G)
      π hπ_simple hπ_coord hbrauer hsubset hsaturated).trans
    (regularIntegerDiagonalQuotient_addEquiv_pi_centralizerPPart
      (p := p) (G := G))

/-- Nonempty wrapper for the saturation quotient adapter. -/
theorem cartanCokernel_nonempty_addEquiv_regularIntegerDiagonalQuotient_of_span_eq_and_saturation
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hsubset :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
    (hsaturated :
      ∀ f : PRegularConjClass G p → ℤ,
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) →
          f ∈
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ((PRegularConjClass G p → ℤ) ⧸
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)) :=
  ⟨cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_span_eq_and_saturation
    (p := p) (A := A) (K := K) (G := G) hspan hsubset hsaturated⟩

/-- Nonempty wrapper for the saturation cyclic-product adapter. -/
theorem cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_span_eq_and_saturation
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hsubset :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
    (hsaturated :
      ∀ f : PRegularConjClass G p → ℤ,
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) →
          f ∈
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
  ⟨cartanCokernel_addEquiv_pi_centralizerPPart_of_span_eq_and_saturation
    (p := p) (A := A) (K := K) (G := G) hspan hsubset hsaturated⟩

/-- Nonempty quotient wrapper with the diagonal containment derived from `hspan`. -/
theorem
    cartanCokernel_nonempty_addEquiv_regularIntegerDiagonalQuotient_of_span_eq_and_cast_saturation
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hsaturated :
      ∀ f : PRegularConjClass G p → ℤ,
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) →
          f ∈
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ((PRegularConjClass G p → ℤ) ⧸
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)) :=
  ⟨cartanCokernel_addEquiv_regularIntegerDiagonalQuotient_of_span_eq_and_cast_saturation
    (p := p) (A := A) (K := K) (G := G) hspan hsaturated⟩

/-- Nonempty cyclic-product wrapper with the diagonal containment derived from `hspan`. -/
theorem cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_span_eq_and_cast_saturation
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hsaturated :
      ∀ f : PRegularConjClass G p → ℤ,
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) →
          f ∈
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
  ⟨cartanCokernel_addEquiv_pi_centralizerPPart_of_span_eq_and_cast_saturation
    (p := p) (A := A) (K := K) (G := G) hspan hsaturated⟩

/-- Residue-field cyclic-product support theorem whose only remaining saturation input is the
prime-to-`p` denominator-clearing statement for cast span membership. -/
theorem
    cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_span_eq_and_coprime_nsmul_saturation
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hclear :
      ∀ f : PRegularConjClass G p → ℤ,
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) →
          ∃ n : ℕ,
            Nat.Coprime n p ∧
              n • f ∈
                (cartanCoordinateAddHom
                  (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
  cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_span_eq_and_cast_saturation
    (p := p) (A := A) (K := K) (G := G) hspan
    (cartanCoordinateAddHom_range_cast_saturated_of_coprime_nsmul_mem_range
      (p := p) (A := A) (K := K) (G := G) hclear)

/-- Direct fixed-coordinate range equality from the remaining source span statement.

This packages the already-proved finite-index, prime-to-`p` denominator clearing and p-primary
cokernel descent: once Serre's source argument gives the Cartan `A`-span as the regular
divisibility lattice, no additional saturation hypothesis is needed. -/
theorem cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_span_eq
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    (cartanCoordinateAddHom
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  exact
    cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_span_eq_and_saturation
      (p := p) (A := A) (K := K) (G := G)
      hspan
      (cartanCoordinateAddHom_range_le_regularIntegerDiagonalSubmodule_of_span_eq
        (p := p) (A := A) (K := K) (G := G) hspan)
      (cartanCoordinateAddHom_range_cast_saturated
        (p := p) (A := A) (K := K) (G := G))

/-- Source-span bridge in the existential coordinate-equivalence shape used by
`CartanFormalRange.lean`: once the mixed-characteristic Cartan coordinate span is Serre's regular
divisibility lattice, the canonical regular-class coordinate equivalence identifies the full
Cartan range with the regular integer diagonal lattice. -/
theorem existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_span_eq
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    ∃ e : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_coordinateRange_eq
    (p := p) (k := IsLocalRing.ResidueField A) (G := G)
    (cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_span_eq
      (p := p) (A := A) (K := K) (G := G) hspan)

/-- Direct diagonal-quotient form from the remaining source span statement. -/
theorem cartanCokernel_nonempty_addEquiv_regularIntegerDiagonalQuotient_of_span_eq
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ((PRegularConjClass G p → ℤ) ⧸
          (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)) :=
  cartanCokernel_nonempty_addEquiv_regularIntegerDiagonalQuotient_of_coordinateRange_eq
    (p := p) (k := IsLocalRing.ResidueField A) (G := G)
    (cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_span_eq
      (p := p) (A := A) (K := K) (G := G) hspan)

/-- Direct cyclic-product form from the remaining source span statement. -/
theorem cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_span_eq
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    Nonempty
      (cartanCokernel (IsLocalRing.ResidueField A) G ≃+
        ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) :=
  cartanCokernel_nonempty_addEquiv_pi_centralizerPPart_of_coordinateRange_eq
    (p := p) (k := IsLocalRing.ResidueField A) (G := G)
    (cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_span_eq
      (p := p) (A := A) (K := K) (G := G) hspan)

end CartanCokernelSaturationDescent

end Representation
