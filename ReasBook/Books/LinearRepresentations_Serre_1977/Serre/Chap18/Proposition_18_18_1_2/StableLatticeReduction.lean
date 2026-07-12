import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_2
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.ProjectiveScalarExtensionClasses
import LinearRepresentations_Serre_1977.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_1_2
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.FiniteOrderEigenbasis
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.QuotientCharpoly
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.RealizationCore

noncomputable section

open CategoryTheory
open scoped Representation
open scoped TensorProduct

universe u v x y

namespace Representation

section StableReduction

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G]
variable {E : Type u} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]
variable [FiniteDimensional K E]

local notation "k" => IsLocalRing.ResidueField A

variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]

/-- Helper for Proposition 18-18.1-2 (6): in a discrete valuation ring, two roots of unity of
order prime to the residue characteristic with the same residue are equal. The source uses this
for the canonical identification of eigenvalue lifts. -/
private theorem eq_of_pow_eq_one_of_residue_eq
    [IsDomain A] [IsDiscreteValuationRing A] [Fact p.Prime]
    {m : ℕ} (hm : m ≠ 0) (hpm : ¬ p ∣ m)
    {ω : K} (hω : IsPrimitiveRoot ω m)
    {a a' : A} (ha : a ^ m = 1) (ha' : a' ^ m = 1)
    (hres : IsLocalRing.residue A a = IsLocalRing.residue A a') :
    a = a' := by
  classical
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  -- the primitive root descends to `A`
  have hωint : ∃ ωA : A, algebraMap A K ωA = ω := by
    refine IsIntegrallyClosed.isIntegral_iff.mp ?_
    exact ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hm, by
      simp [Polynomial.eval₂_sub, hω.pow_eq_one]⟩
  obtain ⟨ωA, hωA⟩ := hωint
  have hωAprim : IsPrimitiveRoot ωA m := by
    refine IsPrimitiveRoot.of_map_of_injective ?_ hinj
    rw [hωA]
    exact hω
  -- both torsion elements are powers of the descended primitive root
  haveI : NeZero m := ⟨hm⟩
  have hclass : ∀ b : A, b ^ m = 1 → ∃ t : ℕ, b = ωA ^ t := by
    intro b hb
    have hbK : (algebraMap A K b) ^ m = 1 := by
      rw [← map_pow, hb, map_one]
    obtain ⟨t, _, ht⟩ := hω.eq_pow_of_pow_eq_one hbK
    refine ⟨t, hinj ?_⟩
    rw [map_pow, hωA, ht]
  obtain ⟨t, rfl⟩ := hclass a ha
  obtain ⟨t', rfl⟩ := hclass a' ha'
  -- the residue of the primitive root is a primitive root of the residue field
  have hmk : ((m : ℕ) : IsLocalRing.ResidueField A) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) p]
    exact hpm
  have hfac : ∀ d, 0 < d → d < m → IsLocalRing.residue A (ωA ^ d) ≠ 1 := by
    intro d hd0 hdm hone
    obtain ⟨n', hn'⟩ : ∃ n', m = n' + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hm)).symm⟩
    have hprodA : (∏ i ∈ Finset.range n', ((1 : A) - ωA ^ (i + 1))) = ((n' : A) + 1) := by
      exact_mod_cast IsPrimitiveRoot.prod_one_sub_pow_eq_order (hn' ▸ hωAprim)
    have hmA : IsLocalRing.residue A ((m : ℕ) : A) ≠ 0 := by
      rw [show IsLocalRing.residue A ((m : ℕ) : A) =
          ((m : ℕ) : IsLocalRing.ResidueField A) from map_natCast _ m]
      exact hmk
    apply hmA
    have hm_eq : ((m : ℕ) : A) = ((n' : A) + 1) := by
      rw [hn']
      push_cast
      ring
    rw [hm_eq, ← hprodA, map_prod]
    refine Finset.prod_eq_zero (i := d - 1) ?_ ?_
    · rw [Finset.mem_range]
      omega
    · have hd1 : d - 1 + 1 = d := by omega
      rw [hd1, map_sub, map_one, hone, sub_self]
  -- compare the exponents through the residue field
  have hresunit : IsUnit (IsLocalRing.residue A ωA) := by
    refine IsUnit.of_pow_eq_one (n := m) ?_ hm
    rw [← map_pow, hωAprim.pow_eq_one, map_one]
  have hresord : orderOf hresunit.unit = m := by
    rw [orderOf_eq_iff (Nat.pos_of_ne_zero hm)]
    constructor
    · apply Units.ext
      push_cast [IsUnit.unit_spec]
      rw [← map_pow, hωAprim.pow_eq_one, map_one]
    · intro d hdm hd0 hcon
      refine hfac d hd0 hdm ?_
      have hval : ((hresunit.unit ^ d : (IsLocalRing.ResidueField A)ˣ) :
          IsLocalRing.ResidueField A) = 1 := by
        rw [hcon]
        rfl
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec] at hval
      rw [map_pow]
      exact hval
  -- equality of residues forces congruent exponents, hence equal torsion elements
  have hrespow : hresunit.unit ^ t = hresunit.unit ^ t' := by
    apply Units.ext
    push_cast [IsUnit.unit_spec]
    rw [← map_pow, ← map_pow]
    exact hres
  have hmod : t ≡ t' [MOD m] := by
    have := (pow_eq_pow_iff_modEq (x := hresunit.unit)).mp hrespow
    rwa [hresord] at this
  -- transfer the congruence back to `A` through the unit of `ωA`
  have hωAunit : IsUnit ωA := by
    refine IsUnit.of_pow_eq_one (n := m) hωAprim.pow_eq_one hm
  have hωAord : orderOf hωAunit.unit = m := by
    rw [orderOf_eq_iff (Nat.pos_of_ne_zero hm)]
    constructor
    · apply Units.ext
      push_cast [IsUnit.unit_spec]
      exact hωAprim.pow_eq_one
    · intro d hdm hd0 hcon
      refine hfac d hd0 hdm ?_
      have hval : ((hωAunit.unit ^ d : Aˣ) : A) = 1 := by
        rw [hcon]
        rfl
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec] at hval
      rw [hval, map_one]
  have : hωAunit.unit ^ t = hωAunit.unit ^ t' :=
    (pow_eq_pow_iff_modEq (x := hωAunit.unit)).mpr (by rwa [hωAord])
  have := congrArg (Units.coeHom A) this
  push_cast [IsUnit.unit_spec] at this
  exact this

open Polynomial in
/-- Helper for Proposition 18-18.1-2 (6): the characteristic polynomial of the ambient action is
the scalar image of the characteristic polynomial of the lattice action. -/
private theorem stableLattice_charpoly_eq_map_algebraMap
    [IsDomain A] [IsDiscreteValuationRing A]
    (ρ : Representation K G E) (L : StableLattice A ρ) (g : G) :
    (ρ g).charpoly = (L.toRepresentation g).charpoly.map (algebraMap A K) := by
  classical
  have hinjAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  haveI : Module.IsTorsionFree A K := by
    constructor
    intro r hr x y hxy
    have hr0 : r ≠ 0 := hr.ne_zero
    have hK : algebraMap A K r ≠ 0 := fun h ↦ hr0 (hinjAK (by rwa [map_zero]))
    have hmul : algebraMap A K r * x = algebraMap A K r * y := by
      simpa [Algebra.smul_def] using hxy
    exact mul_left_cancel₀ hK hmul
  haveI : Module.Free A ↥L.toSubmodule := inferInstance
  haveI : Module.Finite A ↥L.toSubmodule := inferInstance
  set uA : Module.End A ↥L.toSubmodule := L.toRepresentation g with huAdef
  set bA := Module.Free.chooseBasis A ↥L.toSubmodule with hbAdef
  set bK := bA.extendOfIsLattice K with hbKdef
  have hmat : LinearMap.toMatrix bK bK (ρ g) =
      (LinearMap.toMatrix bA bA uA).map (algebraMap A K) := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    have hact : ρ g (bK j) = ((uA (bA j) : ↥L.toSubmodule) : E) := by
      rw [hbKdef, Module.Basis.extendOfIsLattice_apply]
      exact (L.toRepresentation_apply_coe g (bA j)).symm
    rw [hact]
    have hexp : ((uA (bA j) : ↥L.toSubmodule) : E) =
        ∑ i', algebraMap A K ((bA.repr (uA (bA j))) i') • bK i' := by
      conv_lhs => rw [← bA.sum_repr (uA (bA j))]
      push_cast
      refine Finset.sum_congr rfl fun i' _ ↦ ?_
      rw [hbKdef, Module.Basis.extendOfIsLattice_apply]
      exact (algebraMap_smul K _ _).symm
    rw [hexp]
    rw [map_sum]
    have hrepr : ∀ i', bK.repr (algebraMap A K ((bA.repr (uA (bA j))) i') • bK i') =
        algebraMap A K ((bA.repr (uA (bA j))) i') • bK.repr (bK i') := by
      intro i'
      rw [map_smul]
    rw [Finset.sum_congr rfl fun i' _ ↦ hrepr i']
    rw [Finset.sum_apply']
    rw [Finset.sum_eq_single i]
    · rw [Finsupp.smul_apply, Module.Basis.repr_self]
      simp [Finsupp.single_apply]
    · intro i' _ hi'
      rw [Finsupp.smul_apply, Module.Basis.repr_self]
      simp [Finsupp.single_apply, hi']
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hcharK : (ρ g).charpoly = uA.charpoly.map (algebraMap A K) := by
    rw [← LinearMap.charpoly_toMatrix (ρ g) bK, hmat, Matrix.charpoly_map,
      LinearMap.charpoly_toMatrix uA bA]
  exact hcharK

section ReductionCharpolyBridge

variable [IsDomain A] [IsDiscreteValuationRing A]
variable (ρ : Representation K G E) (L : StableLattice A ρ)

/-- Helper instance for clause `(6)`: the canonical `A ⧸ 𝔪`-module structure on the tensor
product, re-spelled with `IsLocalRing.ResidueField A` as the scalar ring (matching the reduction's
own scalar structure). -/
local instance instReductionTensorModule :
    Module (IsLocalRing.ResidueField A)
      ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] ↥L.toSubmodule) :=
  inferInstanceAs (Module (A ⧸ IsLocalRing.maximalIdeal A)
    ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] ↥L.toSubmodule))

/-- Helper for Proposition 18-18.1-2 (6): the reduction of a stable lattice, identified with the
residue-field base change of the lattice.  Routing the comparison through the tensor product avoids
the instance diamond between the lattice reduction's hand-built scalar action and the canonical
quotient-by-`𝔪 • ⊤` action. -/
noncomputable def stableLatticeReductionEquiv :
    L.reduction ≃ₗ[IsLocalRing.ResidueField A]
      ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] ↥L.toSubmodule) where
  toFun x := (quotSMulTopEquiv (IsLocalRing.maximalIdeal A) (L := ↥L.toSubmodule)).symm x
  invFun x := (quotSMulTopEquiv (IsLocalRing.maximalIdeal A) (L := ↥L.toSubmodule)) x
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := map_add _ x y
  map_smul' := by
    intro c x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [RingHom.id_apply]
    show (quotSMulTopEquiv (IsLocalRing.maximalIdeal A)).symm
        ((Submodule.Quotient.mk (a • y) : L.reduction)) = _
    rw [quotSMulTopEquiv_symm_mk, quotSMulTopEquiv_symm_mk]
    rw [TensorProduct.tmul_smul]
    rw [← algebraMap_smul (A ⧸ IsLocalRing.maximalIdeal A) a
      ((1 : A ⧸ IsLocalRing.maximalIdeal A) ⊗ₜ[A] y)]
    rw [Ideal.Quotient.algebraMap_eq]
    exact rfl

/-- Helper for Proposition 18-18.1-2 (6): conjugating the reduced action by
`stableLatticeReductionEquiv` recovers the base change of the lattice action. -/
theorem stableLatticeReductionEquiv_conj (g : G) :
    (stableLatticeReductionEquiv ρ L).conj (L.reductionRepresentation g) =
      LinearMap.baseChange (A ⧸ IsLocalRing.maximalIdeal A) (L.toRepresentation g) := by
  apply LinearMap.ext
  intro x
  have hgen : ∀ y : ↥L.toSubmodule,
      (stableLatticeReductionEquiv ρ L).conj (L.reductionRepresentation g)
          ((1 : A ⧸ IsLocalRing.maximalIdeal A) ⊗ₜ[A] y) =
        LinearMap.baseChange (A ⧸ IsLocalRing.maximalIdeal A) (L.toRepresentation g)
          ((1 : A ⧸ IsLocalRing.maximalIdeal A) ⊗ₜ[A] y) := by
    intro y
    rw [LinearEquiv.conj_apply]
    rw [LinearMap.baseChange_tmul]
    have hsymm : (stableLatticeReductionEquiv ρ L).symm
        ((1 : A ⧸ IsLocalRing.maximalIdeal A) ⊗ₜ[A] y) =
        (Submodule.Quotient.mk y : L.reduction) := by
      show quotSMulTopEquiv (IsLocalRing.maximalIdeal A) _ = _
      rw [show ((1 : A ⧸ IsLocalRing.maximalIdeal A) ⊗ₜ[A] y :
            (A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] ↥L.toSubmodule) =
          (quotSMulTopEquiv (IsLocalRing.maximalIdeal A)).symm
            (Submodule.Quotient.mk y) from (quotSMulTopEquiv_symm_mk _ y).symm]
      rw [LinearEquiv.apply_symm_apply]
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    rw [show ((stableLatticeReductionEquiv ρ L).symm.toLinearMap)
        ((1 : A ⧸ IsLocalRing.maximalIdeal A) ⊗ₜ[A] y) =
        (Submodule.Quotient.mk y : L.reduction) from hsymm]
    rw [L.reductionRepresentation_apply_mk]
    show (quotSMulTopEquiv (IsLocalRing.maximalIdeal A)).symm _ = _
    rw [quotSMulTopEquiv_symm_mk]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c y =>
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      have hsmul : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) ⊗ₜ[A] y =
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) •
            ((1 : A ⧸ IsLocalRing.maximalIdeal A) ⊗ₜ[A] y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hsmul, map_smul, map_smul, hgen y]
      exact rfl
  | add x₁ x₂ h₁ h₂ =>
      simpa [map_add, h₁, h₂]

open Polynomial in
/-- Helper for Proposition 18-18.1-2 (6): the characteristic polynomial of the reduced action is
the residue image of the characteristic polynomial of the lattice action. -/
theorem stableLattice_reduction_charpoly_eq_map_residue (g : G) :
    (L.reductionRepresentation g).charpoly =
      (L.toRepresentation g).charpoly.map (IsLocalRing.residue A) := by
  classical
  have hinjAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  haveI : Module.IsTorsionFree A K := by
    constructor
    intro r hr x y hxy
    have hr0 : r ≠ 0 := hr.ne_zero
    have hK : algebraMap A K r ≠ 0 := fun h ↦ hr0 (hinjAK (by rwa [map_zero]))
    have hmul : algebraMap A K r * x = algebraMap A K r * y := by
      simpa [Algebra.smul_def] using hxy
    exact mul_left_cancel₀ hK hmul
  haveI : Module.Free A ↥L.toSubmodule := inferInstance
  haveI : Module.Finite A ↥L.toSubmodule := inferInstance
  letI : Module.Free (IsLocalRing.ResidueField A)
      ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] ↥L.toSubmodule) :=
    inferInstanceAs (Module.Free (A ⧸ IsLocalRing.maximalIdeal A)
      ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] ↥L.toSubmodule))
  letI : Module.Finite (IsLocalRing.ResidueField A)
      ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] ↥L.toSubmodule) :=
    inferInstanceAs (Module.Finite (A ⧸ IsLocalRing.maximalIdeal A)
      ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] ↥L.toSubmodule))
  haveI : Module.Free (IsLocalRing.ResidueField A) L.reduction :=
    Module.Free.of_equiv (stableLatticeReductionEquiv ρ L).symm
  haveI : Module.Finite (IsLocalRing.ResidueField A) L.reduction :=
    Module.Finite.equiv (stableLatticeReductionEquiv ρ L).symm
  rw [← LinearEquiv.charpoly_conj (stableLatticeReductionEquiv ρ L) (L.reductionRepresentation g)]
  rw [stableLatticeReductionEquiv_conj ρ L g]
  exact LinearMap.charpoly_baseChange (L.toRepresentation g) (A ⧸ IsLocalRing.maximalIdeal A)

end ReductionCharpolyBridge


open Polynomial in
/-- Helper for Proposition 18-18.1-2: the modular character of a stable-lattice
reduction is the restriction of the ambient ordinary character on `p`-regular elements. -/
theorem stableLatticeReduction_modularCharacter_eq_character_restriction
    [IsDomain A] [IsDiscreteValuationRing A] [Fact p.Prime]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p k, ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : kˣ) : k))
    (ρ : Representation K G E) (L : StableLattice A ρ)
    (s : { t : G // IsPRegular p t })
    (hω : ∃ ω : K, IsPrimitiveRoot ω (orderOf s.1)) :
    φ[PrimeToPRoot.toFieldLift lift](L.reductionRepresentation) s =
      ρ.character s.1 := by
  classical
  obtain ⟨ω, hω⟩ := hω
  set m := orderOf s.1 with hmdef
  have hm : m ≠ 0 := by
    intro h0
    have := s.2
    unfold IsPRegular at this
    rw [hmdef] at h0
    rw [h0, Nat.coprime_zero_right] at this
    exact (Fact.out : p.Prime).one_lt.ne' this
  have hpm : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp s.2
  haveI : NeZero m := ⟨hm⟩
  have hinjAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  -- the lattice is finite free over `A`
  haveI : Module.IsTorsionFree A K := by
    constructor
    intro r hr x y hxy
    have hr0 : r ≠ 0 := hr.ne_zero
    have hK : algebraMap A K r ≠ 0 := fun h ↦ hr0 (hinjAK (by rwa [map_zero]))
    have hmul : algebraMap A K r * x = algebraMap A K r * y := by
      simpa [Algebra.smul_def] using hxy
    exact mul_left_cancel₀ hK hmul
  haveI : Module.Free A ↥L.toSubmodule := inferInstance
  haveI : Module.Finite A ↥L.toSubmodule := inferInstance
  -- the action of `s` on the lattice and its two scalar images
  set uA : Module.End A ↥L.toSubmodule := L.toRepresentation s.1 with huAdef
  have hcharK : (ρ s.1).charpoly = uA.charpoly.map (algebraMap A K) :=
    stableLattice_charpoly_eq_map_algebraMap ρ L s.1
  have hcharRed : (L.reductionRepresentation s.1).charpoly =
      uA.charpoly.map (IsLocalRing.residue A) :=
    stableLattice_reduction_charpoly_eq_map_residue ρ L s.1
  -- ## the upstairs polynomial splits into root-of-unity factors over `K`
  have hupow : (ρ s.1) ^ m = 1 := by
    rw [hmdef, ← map_pow, pow_orderOf_eq_one, map_one]
  set qbar := (ρ s.1).charpoly.map (algebraMap K (AlgebraicClosure K)) with hqbardef
  have hmonic : ((ρ s.1).charpoly).Monic := LinearMap.charpoly_monic _
  have hroots_tor : ∀ μ ∈ qbar.roots, μ ^ m = 1 := by
    intro μ hμ
    have hcp : (LinearMap.baseChange (AlgebraicClosure K) (ρ s.1)).charpoly = qbar :=
      LinearMap.charpoly_baseChange (ρ s.1) (AlgebraicClosure K)
    have hroot : (LinearMap.baseChange (AlgebraicClosure K) (ρ s.1)).charpoly.IsRoot μ := by
      rw [hcp]
      exact Polynomial.isRoot_of_mem_roots hμ
    have heig := (Module.End.hasEigenvalue_iff_isRoot_charpoly
      (LinearMap.baseChange (AlgebraicClosure K) (ρ s.1)) μ).mpr hroot
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
    have hbpow : (LinearMap.baseChange (AlgebraicClosure K) (ρ s.1)) ^ m = 1 := by
      have := map_pow (Module.End.baseChangeHom (R := K) (A := AlgebraicClosure K)
        (M := E)) (ρ s.1) m
      rw [hupow, map_one] at this
      exact this.symm
    have hvm : v = (μ ^ m) • v := by
      have hp := hv.pow_apply m
      rw [hbpow] at hp
      exact hp
    have hsub : (μ ^ m - 1) • v = 0 := by
      rw [sub_smul (μ ^ m) (1 : AlgebraicClosure K) v, one_smul, ← hvm, sub_self]
    rcases smul_eq_zero.mp hsub with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv.2
  -- the primitive root of the closure classifies the torsion
  have hωbar : IsPrimitiveRoot (algebraMap K (AlgebraicClosure K) ω) m :=
    hω.map_of_injective (algebraMap K (AlgebraicClosure K)).injective
  obtain ⟨R, hRmap, hRtors⟩ : ∃ R : Multiset K,
      R.map (algebraMap K (AlgebraicClosure K)) = qbar.roots ∧ ∀ ζ ∈ R, ζ ^ m = 1 := by
    have hchoice : ∀ μ ∈ qbar.roots,
        ∃ ζ : K, algebraMap K (AlgebraicClosure K) ζ = μ ∧ ζ ^ m = 1 := by
      intro μ hμ
      obtain ⟨t, _, ht⟩ := hωbar.eq_pow_of_pow_eq_one (hroots_tor μ hμ)
      refine ⟨ω ^ t, by rw [map_pow, ht], ?_⟩
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    refine ⟨qbar.roots.attach.map (fun μ ↦ Classical.choose (hchoice μ.1 μ.2)), ?_, ?_⟩
    · rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.attach_map_val qbar.roots]
      refine Multiset.map_congr rfl ?_
      intro μ _
      exact (Classical.choose_spec (hchoice μ.1 μ.2)).1
    · intro ζ hζ
      obtain ⟨μ, _, rfl⟩ := Multiset.mem_map.mp hζ
      exact (Classical.choose_spec (hchoice μ.1 μ.2)).2
  have hqbar_fact : qbar = (qbar.roots.map (fun μ ↦ X - C μ)).prod :=
    (IsAlgClosed.splits qbar).eq_prod_roots_of_monic (hmonic.map _)
  have hRfact : (ρ s.1).charpoly = (R.map (fun ζ ↦ (X : Polynomial K) - C ζ)).prod := by
    apply Polynomial.map_injective (algebraMap K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective
    rw [Polynomial.map_multiset_prod, Multiset.map_map]
    have hfac : ∀ ζ ∈ R, ((Polynomial.map (algebraMap K (AlgebraicClosure K))) ∘
        fun ζ ↦ (X : Polynomial K) - C ζ) ζ =
        X - C (algebraMap K (AlgebraicClosure K) ζ) := by
      intro ζ _
      show ((X : Polynomial K) - C ζ).map (algebraMap K (AlgebraicClosure K)) = _
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [Multiset.map_congr rfl hfac]
    rw [show (R.map fun ζ ↦ (X : Polynomial (AlgebraicClosure K)) -
        C (algebraMap K (AlgebraicClosure K) ζ)) =
        qbar.roots.map (fun μ ↦ X - C μ) by
      rw [← hRmap, Multiset.map_map]
      rfl]
    rw [← hqbardef]
    exact hqbar_fact
  -- ## descend the eigenvalue factors to `A`
  obtain ⟨RA, hRAmap, hRAtors⟩ : ∃ RA : Multiset A,
      RA.map (algebraMap A K) = R ∧ ∀ a ∈ RA, a ^ m = 1 := by
    have hchoiceA : ∀ ζ ∈ R, ∃ a : A, algebraMap A K a = ζ := by
      intro ζ hζ
      refine IsIntegrallyClosed.isIntegral_iff.mp ?_
      exact ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hm, by
        simp [Polynomial.eval₂_sub, hRtors ζ hζ]⟩
    refine ⟨R.attach.map (fun ζ ↦ Classical.choose (hchoiceA ζ.1 ζ.2)), ?_, ?_⟩
    · rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.attach_map_val R]
      refine Multiset.map_congr rfl ?_
      intro ζ _
      exact Classical.choose_spec (hchoiceA ζ.1 ζ.2)
    · intro a ha
      obtain ⟨ζ, _, rfl⟩ := Multiset.mem_map.mp ha
      apply hinjAK
      rw [map_pow, Classical.choose_spec (hchoiceA ζ.1 ζ.2), map_one]
      exact hRtors ζ.1 ζ.2
  have huAfact : uA.charpoly = (RA.map (fun a ↦ (X : Polynomial A) - C a)).prod := by
    apply Polynomial.map_injective (algebraMap A K) hinjAK
    rw [← hcharK, hRfact]
    rw [Polynomial.map_multiset_prod, Multiset.map_map]
    rw [← hRAmap, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro a _
    show ((X : Polynomial K) - C (algebraMap A K a)) =
      ((X : Polynomial A) - C a).map (algebraMap A K)
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  -- the reduced eigenvalues
  have hredroots : (L.reductionRepresentation s.1).charpoly.roots =
      RA.map (IsLocalRing.residue A) := by
    have hredfact : (L.reductionRepresentation s.1).charpoly =
        ((RA.map (IsLocalRing.residue A)).map
          (fun c ↦ (X : Polynomial (IsLocalRing.ResidueField A)) - C c)).prod := by
      rw [hcharRed, huAfact]
      rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
      refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
      intro a _
      show ((X : Polynomial A) - C a).map (IsLocalRing.residue A) = _
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rfl
    rw [hredfact]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  -- ## the canonical extension of the lift to residue values
  have hkey : ∀ a ∈ RA,
      (if h : ∃ x : PrimeToPRoot p (IsLocalRing.ResidueField A),
          ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) =
            IsLocalRing.residue A a
        then ((lift (Classical.choose h) : Kˣ) : K) else 0) = algebraMap A K a := by
    intro a ha
    have hator : a ^ m = 1 := hRAtors a ha
    have hres_tor : (IsLocalRing.residue A a) ^ m = 1 := by
      rw [← map_pow, hator, map_one]
    have hresunit : IsUnit (IsLocalRing.residue A a) :=
      IsUnit.of_pow_eq_one hres_tor hm
    have hu_tor : hresunit.unit ^ m = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hres_tor]
      rfl
    have hordm : orderOf hresunit.unit ∣ m := orderOf_dvd_of_pow_eq_one hu_tor
    have hcop : IsPRegular p hresunit.unit :=
      Nat.Coprime.coprime_dvd_right hordm s.2
    have hex : ∃ x : PrimeToPRoot p (IsLocalRing.ResidueField A),
        ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) =
          IsLocalRing.residue A a :=
      ⟨⟨hresunit.unit, hcop⟩, by rw [IsUnit.unit_spec]⟩
    rw [dif_pos hex]
    set x0 := Classical.choose hex with hx0def
    have hx0coe : ((x0 : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) =
        IsLocalRing.residue A a := Classical.choose_spec hex
    obtain ⟨a', ha'K, ha'res⟩ := hred x0
    have hx0tor : x0 ^ m = 1 := by
      apply Subtype.ext
      apply Units.ext
      have : (((x0 ^ m : PrimeToPRoot p (IsLocalRing.ResidueField A)) :
          (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) =
          (IsLocalRing.residue A a) ^ m := by
        push_cast
        rw [hx0coe]
      rw [hres_tor] at this
      push_cast at this
      exact this
    have ha'tor : a' ^ m = 1 := by
      apply hinjAK
      rw [map_pow, ha'K, map_one]
      have : ((lift x0 ^ m : Kˣ) : K) = ((lift (x0 ^ m) : Kˣ) : K) := by
        rw [← map_pow]
      rw [← Units.val_pow_eq_pow_val, this, hx0tor, map_one]
      rfl
    have ha'res' : IsLocalRing.residue A a' = IsLocalRing.residue A a := by
      rw [ha'res, hx0coe]
    have haa : a' = a :=
      eq_of_pow_eq_one_of_residue_eq (p := p) (K := K) hm hpm hω ha'tor hator ha'res'
    rw [← ha'K, haa]
  -- ## conclude: both sides equal the eigenvalue sum
  have hfK : ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A),
      PrimeToPRoot.toFieldLift lift x =
        (fun μ ↦ if h : ∃ y : PrimeToPRoot p (IsLocalRing.ResidueField A),
            ((y : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) = μ
          then ((lift (Classical.choose h) : Kˣ) : K) else 0)
          ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) := by
    intro x
    have hex : ∃ y : PrimeToPRoot p (IsLocalRing.ResidueField A),
        ((y : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) =
          ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) := ⟨x, rfl⟩
    beta_reduce
    rw [dif_pos hex]
    have : Classical.choose hex = x := by
      apply Subtype.ext
      apply Units.ext
      exact Classical.choose_spec hex
    rw [this]
    rfl
  have hφ := modularCharacter_eq_roots_sum (p := p)
    (G := G) (lift := PrimeToPRoot.toFieldLift lift)
    (f := fun μ ↦ if h : ∃ y : PrimeToPRoot p (IsLocalRing.ResidueField A),
        ((y : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) = μ
      then ((lift (Classical.choose h) : Kˣ) : K) else 0)
    hfK L.reductionRepresentation s
  have hsplitsK : ((ρ s.1).charpoly).Splits := by
    rw [Polynomial.splits_iff_exists_multiset]
    refine ⟨R, ?_⟩
    rw [hmonic.leadingCoeff, Polynomial.C_1, one_mul]
    exact hRfact
  have htrace : LinearMap.trace K E (ρ s.1) = R.sum := by
    rw [Module.End.trace_eq_sum_roots_charpoly_of_splits hsplitsK]
    rw [hRfact, Polynomial.roots_multiset_prod_X_sub_C]
  show modularCharacter (PrimeToPRoot.toFieldLift lift) L.reductionRepresentation s =
    ρ.character s.1
  rw [hφ, hredroots, Multiset.map_map]
  have hmapkey : Multiset.map
      ((fun μ ↦ if h : ∃ y : PrimeToPRoot p (IsLocalRing.ResidueField A),
          ((y : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) = μ
        then ((lift (Classical.choose h) : Kˣ) : K) else 0) ∘
        ⇑(IsLocalRing.residue A)) RA = Multiset.map (⇑(algebraMap A K)) RA :=
    Multiset.map_congr rfl (fun a ha ↦ hkey a ha)
  rw [hmapkey, hRAmap]
  rw [show ρ.character s.1 = LinearMap.trace K E (ρ s.1) from rfl, htrace]

end StableReduction

end Representation
