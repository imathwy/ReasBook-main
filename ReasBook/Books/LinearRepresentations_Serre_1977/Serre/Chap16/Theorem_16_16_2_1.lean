import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap06.Proposition_6_6_2_1
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_1
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_2
import LinearRepresentations_Serre_1977.Serre.Chap03.Lemma_3_3_3_2
import LinearRepresentations_Serre_1977.Serre.Chap03.Exercise_3_3_3_7
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_1_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Lemma_12_12_7_7
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_2_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Theorem_12_12_6_2
import LinearRepresentations_Serre_1977.Serre.Chap12.Theorem_12_12_6_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Exercise_14_14_5_2
import LinearRepresentations_Serre_1977.Serre.Chap14.Exercise_14_14_5_3.RepresentationBridge
import LinearRepresentations_Serre_1977.Serre.Chap14.Infra_14_4_ProjectiveLift
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_5_3.ResidueFieldLift
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_1_2
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_1_11
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_3.GrothendieckCharacter
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_1_12
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_1_12.TransversalGroupAlgebra
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_2_3
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_2
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_2.BrauerMultiplicity
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5.SubgroupInduction
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5.PGroupBridges
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_2_1.ProjectiveInductionScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap16.SubgroupRestriction

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace Representation

open scoped MonoidAlgebra Representation
open CategoryTheory

section GrothendieckCharacter

variable (K : Type u) [Field K]
variable (G : Type u) [Group G]

local instance : CoeFun (R[K](G)) fun _ ↦ G → K where
  coe χ := χ.1

/-- The source-facing Grothendieck-character map agrees with the Chapter `16` owner-near
character map used in Corollary `16-16.1-3`. -/
private theorem finiteRepGrothendieckCharacter_eq_character_local
    [Finite G] (x : R₀[K](G)) :
    finiteRepGrothendieckCharacter K G x =
      ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
        (F := K) (G := G) x := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    apply Subtype.ext
    funext g
    change finiteRepGrothendieckCharacter K G [V]₀ g =
      ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
        (F := K) (G := G) [V]₀ g
    rw [finiteRepGrothendieckCharacter_class]
    exact
      (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local_class
        (F := K) (G := G) V g).symm
  · intro a ha
    simpa [map_neg] using congrArg Neg.neg ha
  · intro a b ha hb
    simpa [map_add, ha, hb] using congrArg₂ HAdd.hAdd ha hb

/-- In characteristic zero, equality of Grothendieck-group characters is equivalent to equality of
Grothendieck classes. This is the public wrapper around the Chapter `16` character injectivity
bridge. -/
theorem finiteRepGrothendieckCharacter_eq_iff
    [Finite G] [CharZero K]
    {x y : R₀[K](G)} :
    finiteRepGrothendieckCharacter K G x =
      finiteRepGrothendieckCharacter K G y ↔ x = y := by
  letI : NeZero (Nat.card G : K) := by
    exact ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  rw [finiteRepGrothendieckCharacter_eq_character_local (K := K) (G := G) x,
    finiteRepGrothendieckCharacter_eq_character_local (K := K) (G := G) y]
  exact
    ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_eq_iff_general_local
      (F := K) (G := G)

end GrothendieckCharacter

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P_k(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k G

/-- Helper for Theorem 16-16.2-1: choose one representative of each isomorphism class of simple
finite-dimensional representations over an arbitrary field. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_over_field_local
    {F : Type u} [Field F] {H : Type u} [Group H] :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep F H),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep F H // CategoryTheory.Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep F H := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hq : Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Theorem 16-16.2-1: a stable lattice restricts to every subgroup. -/
private def stableLattice_subgroupRestriction_local
    {H : Subgroup G} {V : FDRep K G} (L : StableLattice A V.ρ) :
    StableLattice A (V.ρ.comp H.subtype) :=
  { toSubmodule := L.toSubmodule
    apply_mem_toSubmodule := by
      intro h x hx
      exact L.apply_mem_toSubmodule (h : G) hx
    isLattice := L.isLattice }

/-- Helper for Theorem 16-16.2-1: the ordinary character of a restricted Grothendieck class is
the restriction of the ordinary character. -/
private theorem finiteRepGrothendieckCharacter_subgroupRestriction_apply_local
    (H : Subgroup G) (x : R₀[K](G)) (h : H) :
    (finiteRepGrothendieckCharacter K H
        (Subgroup.finiteRepGrothendieckGroupRestriction K H x) : H → K) h =
      (finiteRepGrothendieckCharacter K G x : G → K) (h : G) := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    change
      (finiteRepGrothendieckCharacter K H
          (Subgroup.finiteRepGrothendieckGroupRestriction K H [V]₀) : H → K) h =
        (finiteRepGrothendieckCharacter K G [V]₀ : G → K) (h : G)
    rw [Subgroup.finiteRepGrothendieckGroupRestriction_apply_class]
    rw [finiteRepGrothendieckCharacter_class, finiteRepGrothendieckCharacter_class]
    change
      LinearMap.trace K (FDRep.subgroupRestriction (H := H) V)
          ((FDRep.subgroupRestriction (H := H) V).ρ h) =
        LinearMap.trace K V (V.ρ (h : G))
    rfl
  · intro a ha
    simpa [map_neg] using congrArg Neg.neg ha
  · intro a b ha hb
    simpa [map_add, ha, hb] using congrArg₂ HAdd.hAdd ha hb

/-- Helper for Theorem 16-16.2-1: decomposition commutes with restriction to a subgroup. -/
private theorem decompositionHom_subgroupRestriction_comm_local
    (H : Subgroup G) (x : R₀[K](G)) :
    decompositionHom A K H (Subgroup.finiteRepGrothendieckGroupRestriction K H x) =
      Subgroup.finiteRepGrothendieckGroupRestriction k H (decompositionHom A K G x) := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    obtain ⟨L⟩ := Representation.exists_stableLattice A V.ρ
    let LH : StableLattice A (V.ρ.comp H.subtype) :=
      stableLattice_subgroupRestriction_local (A := A) (K := K) (G := G) (H := H) L
    calc
      decompositionHom A K H
          (Subgroup.finiteRepGrothendieckGroupRestriction K H [V]₀) =
        decompositionHom A K H [FDRep.subgroupRestriction (H := H) V]₀ := by
          rw [Subgroup.finiteRepGrothendieckGroupRestriction_apply_class]
      _ = decompositionHom A K H [FDRep.of (V.ρ.comp H.subtype)]₀ := by
          rfl
      _ = [FDRep.of LH.reductionRepresentation]₀ := by
          rw [decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := H)
            (V := FDRep.of (V.ρ.comp H.subtype)) (L := LH)]
          rfl
      _ =
        [FDRep.subgroupRestriction (G := G) (H := H)
          (FDRep.of L.reductionRepresentation)]₀ := by
          rfl
      _ =
        Subgroup.finiteRepGrothendieckGroupRestriction k H
          [FDRep.of L.reductionRepresentation]₀ := by
          rw [Subgroup.finiteRepGrothendieckGroupRestriction_apply_class]
      _ =
        Subgroup.finiteRepGrothendieckGroupRestriction k H
          (decompositionHom A K G [V]₀) := by
          rw [decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G)
            (V := V) (L := L)]
  · intro a ha
    simpa [map_neg] using congrArg Neg.neg ha
  · intro a b ha hb
    simpa [map_add, ha, hb] using congrArg₂ HAdd.hAdd ha hb

/-- Helper for Theorem 16-16.2-1: if the group order is prime to `p`, the decomposition
homomorphism is injective. -/
private theorem decompositionHom_injective_of_order_prime_to_p_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {H : Type u} [Group H] [Finite H] (hH : ¬ p ∣ Nat.card H) :
    Function.Injective (decompositionHom A K H) := by
  classical
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_over_field_local (F := K) (H := H)
  let L : ∀ i, StableLattice A (π i).ρ := fun i ↦
    Classical.choice (Representation.exists_stableLattice A (π i).ρ)
  let s : R₀[k](H) →ₗ[ℤ] R₀[K](H) :=
    (reduced_simple_basis_of_order_prime_to_p_local
        (A := A) (K := K) (G := H) (p := p)
        hH π hπ_pairwise hπ_complete L).constr ℤ
      (generic_simple_basis_of_order_prime_to_p_local
        (G := H) π hπ_pairwise hπ_complete)
  have hleft :
      s.comp (decompositionHom A K H).toIntLinearMap =
        (LinearMap.id : R₀[K](H) →ₗ[ℤ] R₀[K](H)) := by
    simpa [s, L] using
      decomposition_basis_leftInverse_of_order_prime_to_p_local
        (A := A) (K := K) (G := H) (p := p)
        hH π hπ_pairwise hπ_complete L
  intro x y hxy
  calc
    x = ((LinearMap.id : R₀[K](H) →ₗ[ℤ] R₀[K](H)) x) := rfl
    _ = (s.comp (decompositionHom A K H).toIntLinearMap) x := by rw [hleft]
    _ = s ((decompositionHom A K H).toIntLinearMap x) := rfl
    _ = s ((decompositionHom A K H).toIntLinearMap y) := by simpa using congrArg s hxy
    _ = (s.comp (decompositionHom A K H).toIntLinearMap) y := rfl
    _ = ((LinearMap.id : R₀[K](H) →ₗ[ℤ] R₀[K](H)) y) := by rw [hleft]
    _ = y := rfl

/-- Helper for Theorem 16-16.2-1: a class in the kernel of decomposition has ordinary character
zero on `p`-regular elements. -/
private theorem character_eq_zero_on_pRegular_of_mem_decompositionHom_ker_local
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {x : R₀[K](G)} (hx : decompositionHom A K G x = 0) :
    ∀ g : G, IsPRegular p g → (finiteRepGrothendieckCharacter K G x : G → K) g = 0 := by
  intro g hg
  let H : Subgroup G := Subgroup.zpowers g
  let gen : H := ⟨g, by simp [H]⟩
  have hH : ¬ p ∣ Nat.card H := by
    rw [show Nat.card H = orderOf g by simpa [H] using Nat.card_zpowers g]
    exact (isPRegular_iff_not_dvd_orderOf (p := p) g).1 hg
  have hres_decomp :
      decompositionHom A K H (Subgroup.finiteRepGrothendieckGroupRestriction K H x) = 0 := by
    rw [decompositionHom_subgroupRestriction_comm_local (A := A) (K := K) (G := G) H x,
      hx, map_zero]
  have hres_zero :
      Subgroup.finiteRepGrothendieckGroupRestriction K H x = 0 :=
    (decompositionHom_injective_of_order_prime_to_p_local
      (A := A) (K := K) (p := p) (H := H) hH) (by simpa using hres_decomp)
  have hchar_res :
      (finiteRepGrothendieckCharacter K H
        (Subgroup.finiteRepGrothendieckGroupRestriction K H x) : H → K) gen = 0 := by
    rw [hres_zero]
    simp
  simpa [H, gen] using
    (finiteRepGrothendieckCharacter_subgroupRestriction_apply_local
      (K := K) (G := G) H x gen).symm.trans hchar_res

/-- Helper for Theorem 16-16.2-1: a characteristic-zero Grothendieck class has no nonzero natural
torsion. -/
private theorem finiteRepGrothendieckClass_eq_zero_of_nsmul_eq_zero_local
    {N : ℕ} (hN : N ≠ 0) {x : R₀[K](G)} (hx : N • x = 0) : x = 0 := by
  apply (finiteRepGrothendieckCharacter_eq_iff (K := K) (G := G)).mp
  ext g
  have hchar :=
    congrArg (finiteRepGrothendieckCharacter K G) hx
  rw [map_nsmul, map_zero] at hchar
  have hpoint :=
    congrArg (fun χ : R[K](G) => (χ : G → K) g) hchar
  change ((N • finiteRepGrothendieckCharacter K G x : R[K](G)) : G → K) g = 0 at hpoint
  simp [nsmul_eq_mul] at hpoint
  rcases hpoint with hNzero | hzero
  · exact False.elim (hN hNzero)
  · exact hzero

/-- Helper for Theorem 16-16.2-1: if the ordinary virtual character vanishes on both the
`p`-regular and `p`-singular loci, then the Grothendieck class itself is zero. -/
private theorem eq_zero_of_character_eq_zero_on_pRegular_and_pSingular_local
    [CharZero K]
    {x : R₀[K](G)}
    (hregular :
      ∀ g : G, IsPRegular p g → (finiteRepGrothendieckCharacter K G x : G → K) g = 0)
    (hsingular :
      ∀ g : G, ¬ IsPRegular p g → (finiteRepGrothendieckCharacter K G x : G → K) g = 0) :
    x = 0 := by
  -- Compare the ordinary character of `x` with the zero character pointwise across the
  -- `p`-regular / `p`-singular dichotomy, then invoke Grothendieck-character injectivity.
  apply (finiteRepGrothendieckCharacter_eq_iff (K := K) (G := G)).mp
  ext g
  by_cases hg : IsPRegular p g
  · -- On the `p`-regular locus, the first vanishing hypothesis supplies the needed value.
    simpa using hregular g hg
  · -- On the complementary `p`-singular locus, use the second vanishing hypothesis instead.
    simpa using hsingular g hg

/-- Helper for Theorem 16-16.2-1: the canonical generator of `Subgroup.zpowers g` stays
`p`-singular whenever `g` itself is `p`-singular. -/
private theorem zpowers_generator_not_isPRegular_local
    (g : G) (hg : ¬ IsPRegular p g) :
    ¬ IsPRegular p (⟨g, by simp⟩ : Subgroup.zpowers g) := by
  -- Compare `IsPRegular` through the order-divisibility criterion and the subgroup-order formula.
  rw [isPRegular_iff_not_dvd_orderOf (p := p) g] at hg
  rw [isPRegular_iff_not_dvd_orderOf (p := p) (⟨g, by simp⟩ : Subgroup.zpowers g)]
  intro hregular
  exact hg (by simpa [Subgroup.orderOf_mk] using hregular)

/-- Helper for Theorem 16-16.2-1: left multiplication on a finite group algebra over a
commutative ring has trace equal to the group order times the coefficient of the identity. -/
private theorem trace_lmul_groupAlgebra_eq_card_mul_coeff_one_commRing_local
    {R : Type u} [CommRing R] {H : Type u} [Group H] [Finite H]
    (v : MonoidAlgebra R H) :
    LinearMap.trace R (MonoidAlgebra R H)
        (Algebra.lmul R (MonoidAlgebra R H) v) = (Nat.card H : R) * v 1 := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  have hcard : (Nat.card H : R) = (Fintype.card H : R) := by
    simp [Nat.card_eq_fintype_card]
  -- Compute the trace in the delta-function basis of the group algebra.
  rw [show LinearMap.trace R (MonoidAlgebra R H)
        (Algebra.lmul R (MonoidAlgebra R H) v) =
      (LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
        (Algebra.lmul R (MonoidAlgebra R H) v)).trace by
    exact LinearMap.trace_eq_matrix_trace R Finsupp.basisSingleOne
      (Algebra.lmul R (MonoidAlgebra R H) v)]
  rw [Matrix.trace, hcard]
  simp [LinearMap.toMatrix_apply]
  calc
    Finset.univ.sum (fun x : H =>
        (((LinearMap.mul R (MonoidAlgebra R H)) v) (Finsupp.single x (1 : R))) x)
        = Finset.univ.sum (fun _ : H => v 1) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            calc
              (((LinearMap.mul R (MonoidAlgebra R H)) v) (Finsupp.single x (1 : R))) x =
                  v (x * x⁻¹) * (1 : R) := by
                    exact MonoidAlgebra.mul_single_apply v (1 : R) x x
              _ = v 1 := by simp
    _ = (Fintype.card H : R) * v 1 := by
          simp

/-- Helper for Theorem 16-16.2-1: the regular group-algebra action of a nonidentity element has
zero trace over any commutative coefficient ring. -/
private theorem trace_lmul_groupAlgebra_of_ne_one_commRing_local
    {R : Type u} [CommRing R] {H : Type u} [Group H] [Finite H]
    {h : H} (hh : h ≠ 1) :
    LinearMap.trace R (MonoidAlgebra R H)
        (Algebra.lmul R (MonoidAlgebra R H) (MonoidAlgebra.of R H h)) = 0 := by
  rw [trace_lmul_groupAlgebra_eq_card_mul_coeff_one_commRing_local
    (R := R) (H := H) (v := MonoidAlgebra.of R H h)]
  simp [MonoidAlgebra.of_apply, hh]

/-- Helper for Theorem 16-16.2-1: if a module is free over a finite group algebra, then the
underlying base-linear trace of any nonidentity group element is zero. -/
private theorem trace_action_eq_zero_of_free_over_groupAlgebra_local
    {R : Type u} [CommRing R] {H : Type u} [Group H] [Finite H]
    {M : Type u} [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R H) M]
    [IsScalarTower R (MonoidAlgebra R H) M]
    [Module.Free (MonoidAlgebra R H) M] [Module.Finite (MonoidAlgebra R H) M]
    {h : H} (hh : h ≠ 1) :
    LinearMap.trace R M ((Representation.ofModule' M : Representation R H M) h) = 0 := by
  classical
  let α : Type u := Module.Free.ChooseBasisIndex (MonoidAlgebra R H) M
  letI : Fintype α := Fintype.ofFinite α
  let bRH : Module.Basis H R (MonoidAlgebra R H) := MonoidAlgebra.basis H R
  let bM : Module.Basis α (MonoidAlgebra R H) M :=
    Module.Free.chooseBasis (MonoidAlgebra R H) M
  let b : Module.Basis (H × α) R M := bRH.smulTower bM
  rw [LinearMap.trace_eq_matrix_trace R b ((Representation.ofModule' M : Representation R H M) h)]
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro i _hi
  rcases i with ⟨x, a⟩
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  have hmap :
      ((Representation.ofModule' M : Representation R H M) h) (b (x, a)) = b (h * x, a) := by
    simp [b, bRH, bM, Representation.ofModule', smul_smul]
  rw [hmap]
  have hne : (h * x, a) ≠ (x, a) := by
    intro hp
    have hx : h * x = x := congrArg Prod.fst hp
    have hx' : h * x = 1 * x := by
      simpa using hx
    exact hh (mul_right_cancel hx')
  simp [hne]

/-- Helper for Theorem 16-16.2-1: over a field whose characteristic kills the group order, every
group-algebra-linear endomorphism of a finite free group-algebra module has zero underlying trace.
This is the matrix calculation used after restricting to the cyclic `p`-subgroup generated by the
unipotent part. -/
private theorem trace_groupAlgebra_linearMap_eq_zero_of_card_eq_zero_local
    {R : Type u} [Field R] {H : Type u} [Group H] [Finite H]
    {M : Type u} [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R H) M]
    [IsScalarTower R (MonoidAlgebra R H) M]
    [Module.Free (MonoidAlgebra R H) M] [Module.Finite (MonoidAlgebra R H) M]
    (f : M →ₗ[MonoidAlgebra R H] M) (hcard : (Nat.card H : R) = 0) :
    LinearMap.trace R M (f.restrictScalars R) = 0 := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  have hcard' : (Fintype.card H : R) = 0 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  let α : Type u := Module.Free.ChooseBasisIndex (MonoidAlgebra R H) M
  let bH : Module.Basis H R (MonoidAlgebra R H) := MonoidAlgebra.basis H R
  let bM : Module.Basis α (MonoidAlgebra R H) M :=
    Module.Free.chooseBasis (MonoidAlgebra R H) M
  letI : Finite α := Module.Finite.finite_basis bM
  letI : Fintype α := Fintype.ofFinite α
  let b : Module.Basis (H × α) R M := bH.smulTower bM
  rw [LinearMap.trace_eq_matrix_trace R b (f.restrictScalars R), Matrix.trace]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y _hy
  let c : R := (((bM.repr (f (bM y))) y) 1)
  calc
    (∑ x : H, (LinearMap.toMatrix b b (f.restrictScalars R)).diag (x, y)) =
        ∑ _x : H, c := by
          apply Finset.sum_congr rfl
          intro x _hx
          dsimp [Matrix.diag]
          rw [LinearMap.toMatrix_apply]
          simp only [b, bH, bM, Module.Basis.smulTower_apply,
            LinearMap.restrictScalars_apply, map_smul, Module.Basis.smulTower_repr,
            Finsupp.smul_apply]
          change (MonoidAlgebra.single x (1 : R) * ((bM.repr (f (bM y))) y)) x = c
          rw [MonoidAlgebra.single_mul_apply]
          simp [c]
    _ = (Fintype.card H : R) * c := by simp [nsmul_eq_mul]
    _ = 0 := by simp [hcard']

/-- Helper for Theorem 16-16.2-1: the canonical free `K[G]`-representation on `n` generators has
character equal to `n` copies of the left-regular character. -/
private theorem free_character_eq_nsmul_leftRegular_local
    [CharZero K] (n : ℕ) :
    let α : Type u := ULift (Fin n)
    (FDRep.of (Rep.free K G α).ρ).character =
      n • (Representation.leftRegular K G).character := by
  let α : Type u := ULift (Fin n)
  let e := Rep.leftRegularTensorTrivialIsoFree K G α
  -- Rewrite the free owner through the tensor-product model `leftRegular ⊗ trivial`.
  ext g
  have hchar := congrFun
    (Representation.char_iso (Representation.equivOfIso e)).symm g
  by_cases hg : g = 1
  · subst hg
    have hchar_one :
        (Rep.free K G α).ρ.character (1 : G) = (Nat.card G : K) * (n : K) := by
      calc
        (Rep.free K G α).ρ.character (1 : G) =
            (CategoryTheory.MonoidalCategoryStruct.tensorObj
              (Rep.leftRegular K G) (Rep.trivial K G (α →₀ K))).ρ.character (1 : G) := by
              simpa using hchar
        _ = (((Rep.leftRegular K G).ρ).character *
              ((Rep.trivial K G (α →₀ K)).ρ).character) (1 : G) := by
              simpa using congrFun
                (Representation.char_tensor
                  ((Rep.leftRegular K G).ρ) ((Rep.trivial K G (α →₀ K)).ρ)) (1 : G)
        _ = (Nat.card G : K) * (n : K) := by
              letI : Fintype G := Fintype.ofFinite G
              have hfinrankG : Module.finrank K (G →₀ K) = Nat.card G := by
                simpa [Nat.card_eq_fintype_card] using
                  (show Module.finrank K (G →₀ K) = Fintype.card G from
                    Module.finrank_finsupp_self K)
              have hcardα : Fintype.card α = n := by
                simp [α]
              simp [Representation.character, Representation.trivial, hfinrankG, hcardα]
    calc
      (FDRep.of (Rep.free K G α).ρ).character (1 : G) =
          (Rep.free K G α).ρ.character (1 : G) := rfl
      _ = (Nat.card G : K) * (n : K) := hchar_one
      _ = (n • (Representation.leftRegular K G).character) (1 : G) := by
            rw [Pi.smul_apply, Representation.leftRegular_character_one]
            simp [nsmul_eq_mul, mul_comm]
  · calc
      (FDRep.of (Rep.free K G α).ρ).character g =
          (Rep.free K G α).ρ.character g := rfl
      _ = 0 := by
            simpa [hg] using hchar
      _ = (n • (Representation.leftRegular K G).character) g := by
            rw [Pi.smul_apply, Representation.leftRegular_character_eq_zero_of_ne_one hg]
            simp

/-- Helper for Theorem 16-16.2-1: a `L[H]`-linear equivalence between the owner modules of two
finite-dimensional representations upgrades to an isomorphism in `FDRep L H`. -/
private theorem fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_local
    {L : Type u} [Field L] {H : Type u} [Group H] [Finite H]
    {σ τ : FDRep L H}
    (hστ : Nonempty (asModule σ.ρ ≃ₗ[L[H]] asModule τ.ρ)) :
    Nonempty (σ ≅ τ) := by
  rcases hστ with ⟨e⟩
  let eRep : ((forget₂ (FDRep L H) (Rep L H)).obj σ) ≅
      ((forget₂ (FDRep L H) (Rep L H)).obj τ) :=
    Rep.unitIso ((forget₂ (FDRep L H) (Rep L H)).obj σ) ≪≫
      Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso ≪≫
      (Rep.unitIso ((forget₂ (FDRep L H) (Rep L H)).obj τ)).symm
  refine ⟨⟨(FDRep.forget₂HomLinearEquiv σ τ) eRep.hom,
    (FDRep.forget₂HomLinearEquiv τ σ) eRep.inv, ?_, ?_⟩⟩
  · apply (forget₂ (FDRep L H) (Rep L H)).map_injective
    change eRep.hom ≫ eRep.inv = 𝟙 _
    exact eRep.hom_inv_id
  · apply (forget₂ (FDRep L H) (Rep L H)).map_injective
    change eRep.inv ≫ eRep.hom = 𝟙 _
    exact eRep.inv_hom_id

/-- Helper for Theorem 16-16.2-1: the canonical free representation on a finite basis set has
ordinary character equal to the corresponding multiple of the regular character. -/
private theorem free_character_eq_card_nsmul_leftRegular_local
    (α : Type u) [Fintype α] :
    (FDRep.of (Rep.free k G α).ρ).character =
      (Fintype.card α) • (Representation.leftRegular k G).character := by
  let e := Rep.leftRegularTensorTrivialIsoFree k G α
  ext g
  have hchar := congrFun
    (Representation.char_iso (Representation.equivOfIso e)).symm g
  by_cases hg : g = 1
  · subst hg
    have hchar_one :
        (Rep.free k G α).ρ.character (1 : G) =
          (Nat.card G : k) * (Fintype.card α : k) := by
      calc
        (Rep.free k G α).ρ.character (1 : G) =
            (CategoryTheory.MonoidalCategoryStruct.tensorObj
              (Rep.leftRegular k G) (Rep.trivial k G (α →₀ k))).ρ.character (1 : G) := by
                simpa using hchar
        _ = (((Rep.leftRegular k G).ρ).character *
              ((Rep.trivial k G (α →₀ k)).ρ).character) (1 : G) := by
                exact congrFun
                  (Representation.char_tensor
                    ((Rep.leftRegular k G).ρ) ((Rep.trivial k G (α →₀ k)).ρ)) (1 : G)
        _ = (Nat.card G : k) * (Fintype.card α : k) := by
              letI : Fintype G := Fintype.ofFinite G
              have hfinrankG : Module.finrank k (G →₀ k) = Nat.card G := by
                rw [Nat.card_eq_fintype_card]
                exact Module.finrank_finsupp_self k
              simp [Representation.character, Representation.trivial, hfinrankG]
    calc
      (FDRep.of (Rep.free k G α).ρ).character (1 : G) =
          (Rep.free k G α).ρ.character (1 : G) := rfl
      _ = (Nat.card G : k) * (Fintype.card α : k) := hchar_one
      _ = ((Fintype.card α) • (Representation.leftRegular k G).character) (1 : G) := by
            rw [Pi.smul_apply, Representation.leftRegular_character_one]
            simp [nsmul_eq_mul, mul_comm]
  · calc
      (FDRep.of (Rep.free k G α).ρ).character g =
          (Rep.free k G α).ρ.character g := rfl
      _ = 0 := by
            simpa [hg] using hchar
      _ = ((Fintype.card α) • (Representation.leftRegular k G).character) g := by
            rw [Pi.smul_apply, Representation.leftRegular_character_eq_zero_of_ne_one hg]
            simp

/-- Helper for Theorem 16-16.2-1: over a finite `p`-group in characteristic `p`, an honest
projective owner has character zero away from the identity because it is free over the group
algebra. -/
private theorem projective_character_eq_zero_of_ne_one_of_isPGroup_local
    (Q : FiniteProjectiveGroupAlgebraModule k G)
    (hG : IsPGroup p G)
    {g : G} (hg : g ≠ 1) :
    Q.toFiniteRep.character g = 0 := by
  letI : Module.Free k[G] Q.V :=
    FiniteProjectiveGroupAlgebraModule.free_of_charP_of_isPGroup
      (p := p) (G := G) Q hG
  let α : Type u := Module.Free.ChooseBasisIndex k[G] Q.V
  letI : Finite α := Module.Finite.finite_basis (Module.Free.chooseBasis k[G] Q.V)
  letI : Fintype α := Fintype.ofFinite α
  have hlin :
      Nonempty (asModule Q.toFiniteRep.ρ ≃ₗ[k[G]]
        asModule ((FDRep.of (Rep.free k G α).ρ).ρ)) := by
    refine ⟨?_⟩
    let eQ : asModule Q.toFiniteRep.ρ ≃ₗ[k[G]] Q.V := by
      simpa [FiniteProjectiveGroupAlgebraModule.toFiniteRep,
        FiniteProjectiveGroupAlgebraModule.toRep] using
        (Rep.counitIso Q.V).toLinearEquiv
    let eFree :
        (α →₀ k[G]) ≃ₗ[k[G]]
          asModule ((FDRep.of (Rep.free k G α).ρ).ρ) := by
      simpa using
        (Representation.finsuppLEquivFreeAsModule k G α)
    exact eQ.trans ((Module.Free.chooseBasis k[G] Q.V).repr.trans eFree)
  obtain ⟨e⟩ :=
    fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_local
      (L := k) (H := G) hlin
  calc
    Q.toFiniteRep.character g =
        (FDRep.of (Rep.free k G α).ρ).character g := by
          simpa using congrFun (FDRep.char_iso e) g
    _ = ((Fintype.card α) • (Representation.leftRegular k G).character) g := by
          rw [free_character_eq_card_nsmul_leftRegular_local (G := G) (α := α)]
    _ = 0 := by
          rw [Pi.smul_apply, Representation.leftRegular_character_eq_zero_of_ne_one hg]
          simp

/-- Helper for Theorem 16-16.2-1: a residue-field projective class can be represented by the
scalar extension of an actual finite projective `A[G]`-module. -/
private theorem residueField_projective_class_has_scalarExtension_lift_local
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (F : FiniteProjectiveGroupAlgebraModule k G) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      projectiveGrothendieckScalarExtensionHom A K [F]ₚ₀ = [Q.scalarExtension K]₀ := by
  -- First lift the residue-field projective module to an honest projective `A[G]`-module.
  obtain ⟨Q, hQ⟩ :=
    exists_projective_lift_of_residueField_projective (A := A) (G := G) F
  refine ⟨Q, ?_⟩
  have hred :
      projectiveGrothendieckReductionEquiv (A := A) (G := G) [Q]ₚ₀ = [F]ₚ₀ := by
    change projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ = [F]ₚ₀
    calc
      projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ =
          [Q.residueFieldReduction]ₚ₀ := by
            exact projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := G) Q
      _ = [F]ₚ₀ := by
            exact
              finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
                (A := k) (G := G) hQ
  have hsymm :
      (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm [F]ₚ₀ = [Q]ₚ₀ := by
    exact (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_eq.2 hred.symm
  calc
    projectiveGrothendieckScalarExtensionHom A K [F]ₚ₀ =
        projectiveGrothendieckBaseChangeHom K [Q]ₚ₀ := by
          rw [projectiveGrothendieckScalarExtensionHom_apply, hsymm]
    _ = [Q.scalarExtension K]₀ := by
          exact projectiveGrothendieckBaseChangeHom_projectiveClass_eq (K := K) Q

/-- Helper for Theorem 16-16.2-1: the ordinary character of the scalar extension
`Q.scalarExtension K` evaluated at `g` is the image under `algebraMap A K` of the `A`-linear trace
of the `g`-action on the underlying free `A`-module `Q.V`.  This is just base change of trace:
`Q.scalarExtension K = K ⊗[A] Q.V`, so the `K`-trace of the `g`-action is the scalar extension of
the `A`-trace. -/
private theorem character_scalarExtension_eq_algebraMap_trace_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) (g : G) :
    (Q.scalarExtension K).character g
      = algebraMap A K (LinearMap.trace A Q.V ((Representation.ofModule' Q.V) g)) := by
  letI : Module.Free A Q.V := Q.free
  have hbc : (Q.scalarExtension K).ρ g
      = ((Representation.ofModule' Q.V) g).baseChange K := rfl
  show LinearMap.trace K _ ((Q.scalarExtension K).ρ g) = _
  rw [hbc]
  exact LinearMap.trace_baseChange ((Representation.ofModule' Q.V) g) K

/-- Helper for Theorem 16-16.2-1: reducing a finite projective `A[G]`-owner to the residue field
sends the character value to the residue of the same `A`-linear trace. -/
private theorem character_residueFieldReduction_eq_residue_trace_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) (g : G) :
    Q.residueFieldReduction.toFiniteRep.character g =
      IsLocalRing.residue A (LinearMap.trace A Q.V ((Representation.ofModule' Q.V) g)) := by
  letI : Module.Free A Q.V := Q.free
  let f : Q.V →ₗ[A] Q.V := (Representation.ofModule' Q.V) g
  let W : Type u := TensorProduct A k Q.V
  letI : Module k[G] W := inferInstance
  let instRestrict : Module k (RestrictScalars k (k[G]) W) :=
    RestrictScalars.module (R := k) (S := k[G]) (M := W)
  letI : Module k (RestrictScalars k (k[G]) W) := instRestrict
  let e : W ≃ₗ[k] (RestrictScalars k (k[G]) W) := by
    refine { (RestrictScalars.addEquiv k (k[G]) W).symm with map_smul' := ?_ }
    intro a x
    rw [← IsScalarTower.algebraMap_smul (A := k[G]) (M := W) a x]
    exact
      (RestrictScalars.addEquiv_symm_map_algebraMap_smul
        (R := k) (S := k[G]) (M := W) a x)
  have haction : ∀ y : W, (MonoidAlgebra.of k G g) • y = f.baseChange k y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
        simp
    | tmul a x =>
        -- On pure tensors the reduced `k[G]`-action is the scalar extension of the integral
        -- `A[G]`-action.
        change ((Representation.scalarExtension (Representation.ofModule' Q.V)).asAlgebraHom
            (MonoidAlgebra.single g (1 : k))) (a ⊗ₜ[A] x) = a ⊗ₜ[A] f x
        rw [Representation.asAlgebraHom_single_one]
        exact LinearMap.baseChange_tmul (f := (Representation.ofModule' Q.V) g) a x
    | add y z hy hz =>
        simpa [MonoidAlgebra.of_apply, map_add] using congrArg₂ HAdd.hAdd hy hz
  have hrep :
      ((Representation.ofModule W) g :
        RestrictScalars k (k[G]) W →ₗ[k] RestrictScalars k (k[G]) W) =
        e.conj (f.baseChange k) := by
    -- The `ofModule` carrier is a restricted-scalar synonym of the tensor product; under the
    -- identity equivalence its action is exactly the base-changed integral action.
    ext x
    simp [e, f, Representation.ofModule, RestrictScalars.lsmul_apply_apply]
    simpa [MonoidAlgebra.of_apply] using haction ((RestrictScalars.addEquiv k k[G] W) x)
  have htrace_conj :
      LinearMap.trace k (RestrictScalars k (k[G]) W) (e.conj (f.baseChange k)) =
        LinearMap.trace k W (f.baseChange k) := by
    exact @LinearMap.trace_conj' k inferInstance W inferInstance inferInstance
      (RestrictScalars k (k[G]) W) inferInstance instRestrict (f.baseChange k) e
  -- Trace is invariant under the restricted-scalar comparison, then base change of trace gives the
  -- residue of the original `A`-linear trace.
  change LinearMap.trace k (RestrictScalars k (k[G]) W) ((Representation.ofModule W) g) =
    IsLocalRing.residue A (LinearMap.trace A Q.V ((Representation.ofModule' Q.V) g))
  calc
    LinearMap.trace k (RestrictScalars k (k[G]) W) ((Representation.ofModule W) g) =
        LinearMap.trace k (RestrictScalars k (k[G]) W) (e.conj (f.baseChange k)) := by
          rw [hrep]
    _ = LinearMap.trace k W (f.baseChange k) := htrace_conj
    _ = IsLocalRing.residue A
        (LinearMap.trace A Q.V ((Representation.ofModule' Q.V) g)) := by
          exact LinearMap.trace_baseChange ((Representation.ofModule' Q.V) g) k

namespace FiniteProjectiveGroupAlgebraModule

/-- Helper for Theorem 16-16.2-1: restricting a projective module along a homomorphism whose
target is free over the source keeps it projective. -/
private theorem projective_restrictScalars_of_free_hom_local
    {R : Type u} [Semiring R]
    {S : Type u} [Semiring S] (σ : R →+* S)
    {M : Type*} [AddCommMonoid M] [Module S M]
    [Module R S] [Module R M] [IsScalarTower R S M]
    (hsmulS : ∀ (r : R) (s : S), (r • s : S) = σ r * s)
    [Module.Free R S] [Module.Projective S M] :
    Module.Projective R M := by
  obtain ⟨P, _instAddCommMonoid, _instModule, _instFree, i, s, hs⟩ :=
    (Module.Projective.iff_split (R := S) (P := M)).mp inferInstance
  let _ : Module R P := Module.compHom P σ
  let _ : IsScalarTower R S P := by
    refine ⟨?_⟩
    intro r s x
    calc
      (r • s) • x = (σ r * s) • x := by rw [hsmulS]
      _ = (σ r) • (s • x) := by simpa using (mul_smul (σ r) s x)
  let _ : Module.Free R P :=
    Module.Free.of_basis
      ((Module.Free.chooseBasis R S).smulTower (Module.Free.chooseBasis S P))
  exact Module.Projective.of_split (i.restrictScalars R) (s.restrictScalars R) <| by
    ext x
    exact LinearMap.congr_fun hs x

/-- Helper for Theorem 16-16.2-1: a representation equivalence induces an equivalence of owner
modules over the group algebra. -/
private theorem nonempty_asModuleLinearEquiv_of_repEquiv_restriction_local
    {H : Type u} [Group H]
    {V W : Type u} [AddCommGroup V] [AddCommGroup W]
    [Module A V] [Module A W]
    (ρ : Representation A H V) (σ : Representation A H W) (e : ρ.Equiv σ) :
    Nonempty (ρ.asModule ≃ₗ[A[H]] σ.asModule) := by
  refine ⟨
    { toFun := fun x => σ.asModuleEquiv.symm (e.toLinearEquiv (ρ.asModuleEquiv x))
      invFun := fun y => ρ.asModuleEquiv.symm (e.symm.toLinearEquiv (σ.asModuleEquiv y))
      left_inv := by
        intro x
        simp
      right_inv := by
        intro y
        simp
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro r x
        apply σ.asModuleEquiv.injective
        rw [σ.asModuleEquiv_map_smul, ρ.asModuleEquiv_map_smul]
        change e.toLinearEquiv ((ρ.asAlgebraHom r) (ρ.asModuleEquiv x)) =
          (σ.asAlgebraHom r) (e.toLinearEquiv (ρ.asModuleEquiv x))
        refine MonoidAlgebra.induction_on
          (p := fun s : A[H] =>
            e.toLinearEquiv ((ρ.asAlgebraHom s) (ρ.asModuleEquiv x)) =
              (σ.asAlgebraHom s) (e.toLinearEquiv (ρ.asModuleEquiv x))) r ?_ ?_ ?_
        · intro h
          simpa [Representation.asAlgebraHom, MonoidAlgebra.of] using
            (Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap h
              (ρ.asModuleEquiv x))
        · intro a b ha hb
          simp [map_add, ha, hb]
        · intro a b hb
          simp [hb] }⟩

/-- Helper for Theorem 16-16.2-1: the restricted subgroup-algebra action is compatible with the
base `A`-action. -/
private theorem subgroup_compHom_isScalarTower_local
    (H : Subgroup G) (M : Type*) [AddCommGroup M] [Module A M] [Module A[G] M]
    [IsScalarTower A A[G] M] :
    let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
    let _ : Module A[↥H] M := Module.compHom M σ
    IsScalarTower A A[↥H] M := by
  let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[↥H] M := Module.compHom M σ
  exact IsScalarTower.of_algebraMap_smul fun a x ↦ by
    have hσalg : σ ((algebraMap A A[↥H]) a) = algebraMap A A[G] a := by
      simpa [σ] using
        congrArg (fun f : A →+* A[G] => f a)
          (MonoidAlgebra.mapDomainRingHom_comp_algebraMap
            (R := A) (A := A) H.subtype)
    change (σ ((algebraMap A A[↥H]) a)) • x = a • x
    rw [hσalg]
    change (algebraMap A A[G] a) • x = a • x
    exact IsScalarTower.algebraMap_smul (A := A[G]) (M := M) a x

/-- Helper for Theorem 16-16.2-1: the right-transversal model is compatible with the restricted
left-regular action. -/
private theorem rightTransversal_freeModel_map_single_smul_local
    (H : Subgroup G) (T : H.RightTransversal) (h : H) (g : G) (r : A) :
    let e : G ≃ (↥(T : Set G) × H) :=
      T.2.equiv.trans (Equiv.prodComm H ↥(T : Set G))
    let Φ : (G →₀ A) ≃ₗ[A] (↥(T : Set G) →₀ H →₀ A) :=
      Finsupp.domLCongr e ≪≫ₗ Finsupp.curryLinearEquiv A
    Φ (Finsupp.single (h.1 * g) r) =
      (Representation.free A H ↥(T : Set G) h) (Φ (Finsupp.single g r)) := by
  dsimp
  have he :
      (T.2.equiv.trans (Equiv.prodComm H ↥(T : Set G))) (h.1 * g) =
        ((T.2.equiv.trans (Equiv.prodComm H ↥(T : Set G)) g).1,
          h * (T.2.equiv.trans (Equiv.prodComm H ↥(T : Set G)) g).2) := by
    simpa using
      congrArg (Equiv.prodComm H ↥(T : Set G))
        (T.2.equiv_mul_left_of_mem (g := g) h.2)
  simp [he]

/-- Helper for Theorem 16-16.2-1: restricting the left-regular representation to `H` is the free
representation on a right transversal. -/
private theorem right_transversal_restricted_leftRegular_equiv_free_local
    (H : Subgroup G) (T : H.RightTransversal) :
    Nonempty (Representation.Equiv
      ((Representation.leftRegular A G).comp H.subtype)
      (Representation.free A H ↥(T : Set G))) := by
  let e : G ≃ (↥(T : Set G) × H) :=
    T.2.equiv.trans (Equiv.prodComm H ↥(T : Set G))
  let Φ : (G →₀ A) ≃ₗ[A] (↥(T : Set G) →₀ H →₀ A) :=
    Finsupp.domLCongr e ≪≫ₗ Finsupp.curryLinearEquiv A
  refine ⟨Representation.Equiv.mk Φ ?_⟩
  intro h
  apply Finsupp.lhom_ext'
  intro g
  apply LinearMap.ext
  intro r
  simpa [Φ, e] using
    rightTransversal_freeModel_map_single_smul_local (A := A) (G := G) H T h g r

/-- Helper for Theorem 16-16.2-1: the owner of the restricted left-regular representation is the
literal group algebra `A[G]` with scalars restricted along `A[H] → A[G]`. -/
private theorem restricted_leftRegular_asModuleLinearEquiv_compHom_groupAlgebra_local
    (H : Subgroup G) :
    let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
    let _ : Module A[↥H] A[G] := Module.compHom A[G] σ
    Nonempty (Representation.asModule ((Representation.leftRegular A G).comp H.subtype) ≃ₗ[A[↥H]]
      A[G]) := by
  let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[↥H] A[G] := Module.compHom A[G] σ
  refine ⟨
    { (Representation.asModuleEquiv ((Representation.leftRegular A G).comp H.subtype)) with
      map_smul' := ?_ }⟩
  intro r x
  let y : A[G] :=
    (Representation.asModuleEquiv ((Representation.leftRegular A G).comp H.subtype)) x
  calc
    (Representation.asModuleEquiv ((Representation.leftRegular A G).comp H.subtype)) (r • x) =
        (Representation.asAlgebraHom ((Representation.leftRegular A G).comp H.subtype) r) y := by
          simpa [y] using
            (Representation.asModuleEquiv_map_smul
              (ρ := ((Representation.leftRegular A G).comp H.subtype)) r x)
    _ = σ r * y := by
          refine MonoidAlgebra.induction_on
            (p := fun s : A[↥H] =>
              (Representation.asAlgebraHom ((Representation.leftRegular A G).comp H.subtype) s) y =
                σ s * y) r ?_ ?_ ?_
          · intro h
            ext g
            simpa [σ, Algebra.smul_def] using
              (Finsupp.mapDomain_equiv_apply (f := Equiv.mulLeft h.1) y g)
          · intro a b ha hb
            calc
              ((Representation.asAlgebraHom ((Representation.leftRegular A G).comp H.subtype))
                  (a + b)) y
                  =
              ((Representation.asAlgebraHom ((Representation.leftRegular A G).comp H.subtype))
                  a) y +
                ((Representation.asAlgebraHom ((Representation.leftRegular A G).comp H.subtype))
                  b) y := by
                    simp
              _ = σ a * y + σ b * y := by
                    rw [ha, hb]
                    rfl
              _ = (σ a + σ b) * y := by rw [add_mul]
              _ = σ (a + b) * y := by rw [map_add]
          · intro a b hb
            calc
              ((Representation.asAlgebraHom ((Representation.leftRegular A G).comp H.subtype))
                  (a • b)) y
                  =
                ((Representation.asAlgebraHom ((Representation.leftRegular A G).comp H.subtype))
                  ((algebraMap A A[↥H]) a))
                    (((Representation.asAlgebraHom
                      ((Representation.leftRegular A G).comp H.subtype)) b) y) := by
                        rw [Algebra.smul_def, map_mul, Module.End.mul_apply]
              _ = a •
                  (((Representation.asAlgebraHom
                    ((Representation.leftRegular A G).comp H.subtype)) b) y) := by
                      simp [Representation.asAlgebraHom_single]
              _ = a • (σ b * y) := by
                    exact congrArg (fun z => a • z) hb
              _ = σ ((algebraMap A A[↥H]) a * b) * y := by
                    calc
                      a • (σ b * y) = σ ((algebraMap A A[↥H]) a) * (σ b * y) := by
                        simp [Algebra.smul_def, σ]
                      _ = (σ ((algebraMap A A[↥H]) a) * σ b) * y := by
                            rw [mul_assoc]
                      _ = σ ((algebraMap A A[↥H]) a * b) * y := by
                            rw [← map_mul]
              _ = σ (a • b) * y := by
                    simp [Algebra.smul_def]
    _ = r • y := by
          rfl

/-- Helper for Theorem 16-16.2-1: a right-transversal decomposition exhibits `A[G]` as a free
`A[H]`-module. -/
private theorem subgroup_groupAlgebra_free_of_transversal_local
    (H : Subgroup G) :
    let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
    let _ : Module A[↥H] A[G] := Module.compHom A[G] σ
    Module.Free A[↥H] A[G] := by
  let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[↥H] A[G] := Module.compHom A[G] σ
  let T : H.RightTransversal := default
  obtain ⟨eρ⟩ :=
    right_transversal_restricted_leftRegular_equiv_free_local (A := A) (G := G) H T
  obtain ⟨eM⟩ :=
    nonempty_asModuleLinearEquiv_of_repEquiv_restriction_local
      (A := A)
      (H := ↥H)
      (V := G →₀ A)
      (W := ↥(T : Set G) →₀ H →₀ A)
      ((Representation.leftRegular A G).comp H.subtype)
      (Representation.free A H ↥(T : Set G))
      eρ
  let _ : Module.Free A[↥H] (Representation.free A H ↥(T : Set G)).asModule := by
    simpa using
      (Representation.free_asModule_free A ↥H ↥(T : Set G))
  let hfreeReg :
      Module.Free A[↥H]
        (Representation.asModule ((Representation.leftRegular A G).comp H.subtype)) :=
    Module.Free.of_equiv eM.symm
  obtain ⟨eOwner⟩ :=
    restricted_leftRegular_asModuleLinearEquiv_compHom_groupAlgebra_local
      (A := A) (G := G) H
  let _ :
      Module.Free A[↥H]
        (Representation.asModule ((Representation.leftRegular A G).comp H.subtype)) :=
    hfreeReg
  let hfreeOwner : Module.Free A[↥H] A[G] := Module.Free.of_equiv eOwner
  simpa using hfreeOwner

/-- Helper for Theorem 16-16.2-1: the ambient owner with subgroup-restricted scalars is projective
over `A[H]`. -/
private theorem subgroup_compHom_owner_projective_local
    (H : Subgroup G) (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
    let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
    let _ : IsScalarTower A A[↥H] Q.V :=
      subgroup_compHom_isScalarTower_local (A := A) (G := G) H Q.V
    Module.Projective A[↥H] Q.V := by
  let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[↥H] A[G] := Module.compHom A[G] σ
  let _ : Module.Free A[↥H] A[G] :=
    subgroup_groupAlgebra_free_of_transversal_local (A := A) (G := G) H
  let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
  let _ : IsScalarTower A A[↥H] Q.V :=
    subgroup_compHom_isScalarTower_local (A := A) (G := G) H Q.V
  let _ : IsScalarTower A[↥H] A[G] Q.V := by
    refine ⟨?_⟩
    intro r s x
    simpa [σ, Module.compHom] using (mul_smul (σ r) s x)
  exact projective_restrictScalars_of_free_hom_local
    (R := A[↥H]) (S := A[G]) (σ := σ) (M := Q.V)
    (fun (r : A[↥H]) (s : A[G]) => rfl)

/-- Helper for Theorem 16-16.2-1: restrict a finite projective `A[G]`-owner to a subgroup
`H ≤ G`, keeping the same carrier and restricting the scalar action along `A[H] → A[G]`. -/
private def restrictedToSubgroupBase_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) (H : Subgroup G) :
    FiniteProjectiveGroupAlgebraModule A H :=
  let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
  let _ : IsScalarTower A A[↥H] Q.V :=
    subgroup_compHom_isScalarTower_local (A := A) (G := G) H Q.V
  let _ : Module.Finite A Q.V := Q.finite
  let _ : Module.Finite A[↥H] Q.V := Module.Finite.of_restrictScalars_finite A A[↥H] Q.V
  ⟨FGModuleCat.of A[↥H] Q.V, subgroup_compHom_owner_projective_local (A := A) (G := G) H Q⟩

end FiniteProjectiveGroupAlgebraModule

/-- Helper for Theorem 16-16.2-1: the group-algebra action recovered from
`Representation.ofModule'` is the original scalar action. -/
private theorem ofModule'_asAlgebraHom_apply_commSemiring_local
    {R : Type u} [CommSemiring R] {H : Type u} [Monoid H]
    {M : Type u} [AddCommMonoid M] [Module R M] [Module (MonoidAlgebra R H) M]
    [IsScalarTower R (MonoidAlgebra R H) M]
    (r : MonoidAlgebra R H) (m : M) :
    (((Representation.ofModule' M :
      Representation R H M).asAlgebraHom r) m) = r • m := by
  refine MonoidAlgebra.induction_on
    (p := fun s : MonoidAlgebra R H =>
      (((Representation.ofModule' M :
        Representation R H M).asAlgebraHom s) m) = s • m) r
      ?_ ?_ ?_
  · intro h
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

/-- Helper for Theorem 16-16.2-1: the subgroup-restricted owner uses the same carrier and the
same base-linear action as the ambient owner, so traces of subgroup elements agree with the
corresponding ambient traces. -/
private theorem trace_action_restrictedToSubgroupBase_eq_ambient_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) (H : Subgroup G) (h : H) :
    LinearMap.trace A
        (FiniteProjectiveGroupAlgebraModule.restrictedToSubgroupBase_local
          (A := A) (G := G) Q H).V
        ((Representation.ofModule'
            (FiniteProjectiveGroupAlgebraModule.restrictedToSubgroupBase_local
              (A := A) (G := G) Q H).V :
            Representation A H
              (FiniteProjectiveGroupAlgebraModule.restrictedToSubgroupBase_local
                (A := A) (G := G) Q H).V) h) =
      LinearMap.trace A Q.V ((Representation.ofModule' Q.V) (h : G)) := by
  let QH : FiniteProjectiveGroupAlgebraModule A H :=
    FiniteProjectiveGroupAlgebraModule.restrictedToSubgroupBase_local (A := A) (G := G) Q H
  let σ : A[H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[H] Q.V := Module.compHom Q.V σ
  let _ : IsScalarTower A A[H] Q.V :=
    FiniteProjectiveGroupAlgebraModule.subgroup_compHom_isScalarTower_local
      (A := A) (G := G) H Q.V
  let e : Q.V ≃ₗ[A] QH.V :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change a • x = (algebraMap A A[H] a) • x
        exact (IsScalarTower.algebraMap_smul (A := A[H]) (M := Q.V) a x).symm }
  have haction :
      ((Representation.ofModule' QH.V : Representation A H QH.V) h) =
        e.conj ((Representation.ofModule' Q.V : Representation A G Q.V) (h : G)) := by
    ext x
    rw [← Representation.asAlgebraHom_single_one
      (ρ := (Representation.ofModule' QH.V : Representation A H QH.V)) h]
    rw [← Representation.asAlgebraHom_single_one
      (ρ := (Representation.ofModule' Q.V : Representation A G Q.V)) (h : G)]
    rw [LinearEquiv.conj_apply]
    rw [ofModule'_asAlgebraHom_apply_commSemiring_local
      (R := A) (H := H) (M := QH.V)
      (r := MonoidAlgebra.single h (1 : A)) (m := x)]
    apply e.symm.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [ofModule'_asAlgebraHom_apply_commSemiring_local
      (R := A) (H := G) (M := Q.V)
      (r := MonoidAlgebra.single (h : G) (1 : A)) (m := e.symm x)]
    change
      σ (MonoidAlgebra.single h (1 : A)) • (e.symm x : Q.V) =
        (MonoidAlgebra.single (h : G) (1 : A) : A[G]) • (e.symm x : Q.V)
    simp [σ]
  change
    LinearMap.trace A QH.V ((Representation.ofModule' QH.V : Representation A H QH.V) h) =
      LinearMap.trace A Q.V ((Representation.ofModule' Q.V : Representation A G Q.V) (h : G))
  rw [haction]
  exact LinearMap.trace_conj' ((Representation.ofModule' Q.V : Representation A G Q.V) (h : G)) e

/-- Helper for Theorem 16-16.2-1: if the subgroup-restricted owner is free over the subgroup
group algebra, then every nonidentity subgroup element acts with zero trace over the base ring. -/
private theorem trace_action_eq_zero_of_free_restricted_subgroup_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) (H : Subgroup G)
    (hfree :
      Module.Free A[H]
        (FiniteProjectiveGroupAlgebraModule.restrictedToSubgroupBase_local
          (A := A) (G := G) Q H).V)
    {h : H} (hh : h ≠ 1) :
    LinearMap.trace A
        (FiniteProjectiveGroupAlgebraModule.restrictedToSubgroupBase_local
          (A := A) (G := G) Q H).V
        ((Representation.ofModule'
            (FiniteProjectiveGroupAlgebraModule.restrictedToSubgroupBase_local
              (A := A) (G := G) Q H).V :
            Representation A H
              (FiniteProjectiveGroupAlgebraModule.restrictedToSubgroupBase_local
                (A := A) (G := G) Q H).V) h) = 0 := by
  let QH : FiniteProjectiveGroupAlgebraModule A H :=
    FiniteProjectiveGroupAlgebraModule.restrictedToSubgroupBase_local (A := A) (G := G) Q H
  letI : Module.Free A[H] QH.V := hfree
  -- The restricted owner is now literally a finite free `A[H]`-module, so the group-algebra
  -- basis computation above applies to the nonidentity element `h`.
  exact
    trace_action_eq_zero_of_free_over_groupAlgebra_local
      (R := A) (H := H) (M := QH.V) hh

/-- Helper for Theorem 16-16.2-1: the preceding restricted-owner trace zero statement can be read
back on the original ambient carrier. -/
private theorem trace_ambient_action_eq_zero_of_free_restricted_subgroup_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) (H : Subgroup G)
    (hfree :
      Module.Free A[H]
        (FiniteProjectiveGroupAlgebraModule.restrictedToSubgroupBase_local
          (A := A) (G := G) Q H).V)
    {h : H} (hh : h ≠ 1) :
    LinearMap.trace A Q.V ((Representation.ofModule' Q.V) (h : G)) = 0 := by
  rw [← trace_action_restrictedToSubgroupBase_eq_ambient_local
    (A := A) (G := G) Q H h]
  exact trace_action_eq_zero_of_free_restricted_subgroup_owner_local
    (A := A) (G := G) Q H hfree hh

/-- Helper for Theorem 16-16.2-1: the trace of a block-diagonal endomorphism on a finite product
of finite free modules over a commutative ring is the sum of the traces of its blocks. -/
private theorem trace_piMap_eq_sum_trace_commRing_local
    {R : Type u} [CommRing R] {ι : Type u} [Fintype ι] [DecidableEq ι]
    {M : ι → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
    (f : ∀ i, M i →ₗ[R] M i) :
    LinearMap.trace R (∀ i, M i) (LinearMap.piMap f) =
      ∑ i, LinearMap.trace R (M i) (f i) := by
  let b : ∀ i, Module.Basis _ R (M i) := fun i ↦ Module.Free.chooseBasis R (M i)
  -- Compute the product trace in the sigma-indexed basis coming from the bases of the blocks.
  rw [LinearMap.trace_eq_matrix_trace R (Pi.basis b)]
  simp [Matrix.trace, Matrix.diag_apply, Fintype.sum_sigma, LinearMap.piMap,
    LinearMap.toMatrix_apply]
  congr with i
  simpa [Matrix.trace, LinearMap.toMatrix_apply] using
    (LinearMap.trace_eq_matrix_trace R (b i) (f i)).symm

/-- Helper for Theorem 16-16.2-1: once Serre's Henselian eigenspace decomposition has been
constructed, the final trace sum vanishes.  The data model the decomposition
`Q.V ≃ ∏ i, M i`, with `g` acting on the `i`-th summand as a scalar multiple of the
unipotent action `ν i`; zero trace of each unipotent block forces zero trace globally. -/
private theorem trace_action_eq_zero_of_scalar_block_decomposition_local
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {M : ι → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module.Free A (M i)] [∀ i, Module.Finite A (M i)]
    (Q : FiniteProjectiveGroupAlgebraModule A G) (g : G)
    (e : Q.V ≃ₗ[A] ∀ i, M i)
    (ω : ι → A) (ν : ∀ i, M i →ₗ[A] M i)
    (haction :
      ((Representation.ofModule' Q.V : Representation A G Q.V) g) =
        e.symm.conj (LinearMap.piMap fun i ↦ ω i • ν i))
    (htrace : ∀ i, LinearMap.trace A (M i) (ν i) = 0) :
    LinearMap.trace A Q.V ((Representation.ofModule' Q.V) g) = 0 := by
  -- Transport the trace to the product decomposition, then evaluate it block-by-block.
  rw [haction, LinearMap.trace_conj',
    trace_piMap_eq_sum_trace_commRing_local (R := A) (f := fun i ↦ ω i • ν i)]
  simp [htrace]

/-- Helper for Theorem 16-16.2-1: the `A`-linear trace of the `g`-action on a finite projective
`A[G]`-module vanishes whenever `g` is `p`-singular (Serre's Theorem 36, part (a), integral core).

Mathematical proof (Serre §16.2): write `g = u * s` with `u` its (nontrivial) `p`-part and `s` its
`p`-regular part, commuting, via `p_component_decomposition_exists`.  The `p`-regular operator
`ρ s` has order `m = orderOf s` prime to `p`; since `A` is Henselian with algebraically closed
residue field of characteristic `p`, `A` contains a primitive `m`-th root of unity `ω`
(`exists_primitiveRoot_of_henselian`), so `ρ s` is diagonalisable over `A`: the Lagrange
idempotents `e_i` (polynomials in `ρ s` at the nodes `ω^i`) split `Q.V = ⨁_i Q.V_i` into
`ρ s`-eigenspaces, each an `A[⟨u⟩]`-summand of the projective `Q.V`.  As `⟨u⟩` is a `p`-group and
`A[⟨u⟩]` is local, each eigenspace is free over `A[⟨u⟩]`; the action of `u ≠ 1` on a free
`A[⟨u⟩]`-module is a fixed-point-free permutation of a basis, so has trace `0`.  Hence
`trace (ρ g) = ∑_i ω^i · trace (ρ u | Q.V_i) = 0`.  Formalising the integral eigenspace splitting
and the local group-algebra freeness is a substantial development; left as the remaining frontier. -/
private theorem trace_action_eq_zero_on_pSingular_of_projective_local
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (Q : FiniteProjectiveGroupAlgebraModule A G) (g : G) (hg : ¬ IsPRegular p g) :
    LinearMap.trace A Q.V ((Representation.ofModule' Q.V) g) = 0 := by
  classical
  let M : NonzeroResidualCharacteristicMaximalIdeal A p :=
    ⟨⟨IsLocalRing.maximalIdeal A, IsLocalRing.maximalIdeal.isMaximal A⟩, by
      constructor
      · exact IsDiscreteValuationRing.not_a_field A
      ·
        haveI : CharP (A ⧸ IsLocalRing.maximalIdeal A) p := by
          change CharP k p
          infer_instance
        exact
          charP_of_injective_algebraMap
            (IsFractionRing.injective (A ⧸ IsLocalRing.maximalIdeal A)
              ((IsLocalRing.maximalIdeal A).ResidueField)) p⟩
  have hchar :
      (Q.scalarExtension (FractionRing A)).character g = 0 :=
    FiniteProjectiveGroupAlgebraModule.scalarExtension_character_eq_zero_of_not_isPRegular_of_residue_prime
        A (FractionRing A) G Q M g hg
  have hchar_eq :
      (Q.scalarExtension (FractionRing A)).character g =
        algebraMap A (FractionRing A)
          (LinearMap.trace A Q.V ((Representation.ofModule' Q.V) g)) := by
    letI : Module.Free A Q.V := Q.free
    have hbc : (Q.scalarExtension (FractionRing A)).ρ g =
        ((Representation.ofModule' Q.V) g).baseChange (FractionRing A) := rfl
    show LinearMap.trace (FractionRing A) _ ((Q.scalarExtension (FractionRing A)).ρ g) = _
    rw [hbc]
    exact LinearMap.trace_baseChange ((Representation.ofModule' Q.V) g) (FractionRing A)
  rw [hchar_eq] at hchar
  exact (IsFractionRing.injective A (FractionRing A)) (by simpa using hchar)

/-- Helper for Theorem 16-16.2-1: the scalar extension of an actual finite projective
`A[G]`-module has character zero on `p`-singular elements. -/
private theorem projective_scalar_extension_character_eq_zero_on_pSingular_local
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (Q : FiniteProjectiveGroupAlgebraModule A G) (g : G) (hg : ¬ IsPRegular p g) :
    (Q.scalarExtension K).character g = 0 := by
  rw [character_scalarExtension_eq_algebraMap_trace_local Q g,
    trace_action_eq_zero_on_pSingular_of_projective_local (p := p) Q g hg, map_zero]

/-- Helper for Theorem 16-16.2-1: subgroup induction commutes with Serre's scalar-extension map
on projective Grothendieck groups. -/
private theorem
    projective_scalarExtension_subgroupInduction_eq_subgroupInduction_projective_scalarExtension_local
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (H : Subgroup G) (y : P₀[k](H)) :
    finiteRep_subgroupInduction (G := G) H
        ((projectiveGrothendieckScalarExtensionHom A K) y) =
      (projectiveGrothendieckScalarExtensionHom A K)
        (projective_subgroupInduction (G := G) H y) := by
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro F
    obtain ⟨Q, hQ⟩ :=
      exists_projective_lift_of_residueField_projective (A := A) (G := H) F
    have hF :
        [F]ₚ₀ = [Q.residueFieldReduction]ₚ₀ := by
      exact
        (finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
          (A := k) (G := H) hQ).symm
    have hscalarH :
        projectiveGrothendieckScalarExtensionHom A K [Q.residueFieldReduction]ₚ₀ =
          [Q.scalarExtension K]₀ := by
      have hred :
          projectiveGrothendieckReductionEquiv (A := A) (G := H) [Q]ₚ₀ =
            [Q.residueFieldReduction]ₚ₀ := by
        change projectiveGrothendieckReductionHom (A := A) (G := H) [Q]ₚ₀ =
          [Q.residueFieldReduction]ₚ₀
        exact projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := H) Q
      have hsymm :
          (projectiveGrothendieckReductionEquiv (A := A) (G := H)).symm
              [Q.residueFieldReduction]ₚ₀ = [Q]ₚ₀ := by
        exact
          (projectiveGrothendieckReductionEquiv (A := A) (G := H)).symm_apply_eq.2
            hred.symm
      rw [projectiveGrothendieckScalarExtensionHom_apply, hsymm]
      exact projectiveGrothendieckBaseChangeHom_projectiveClass_eq (K := K) Q
    have hscalarG :
        projectiveGrothendieckScalarExtensionHom A K
            [(Q.subgroupInductionBase (G := G)).residueFieldReduction]ₚ₀ =
          [(Q.subgroupInductionBase (G := G)).scalarExtension K]₀ := by
      have hred :
          projectiveGrothendieckReductionEquiv (A := A) (G := G)
              [Q.subgroupInductionBase (G := G)]ₚ₀ =
            [(Q.subgroupInductionBase (G := G)).residueFieldReduction]ₚ₀ := by
        change projectiveGrothendieckReductionHom (A := A) (G := G)
            [Q.subgroupInductionBase (G := G)]ₚ₀ =
          [(Q.subgroupInductionBase (G := G)).residueFieldReduction]ₚ₀
        exact
          projectiveGrothendieckReductionHom_projectiveClass_eq
            (A := A) (G := G) (Q.subgroupInductionBase (G := G))
      have hsymm :
          (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm
              [(Q.subgroupInductionBase (G := G)).residueFieldReduction]ₚ₀ =
            [Q.subgroupInductionBase (G := G)]ₚ₀ := by
        exact
          (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_eq.2
            hred.symm
      rw [projectiveGrothendieckScalarExtensionHom_apply, hsymm]
      exact
        projectiveGrothendieckBaseChangeHom_projectiveClass_eq
          (K := K) (Q.subgroupInductionBase (G := G))
    calc
      finiteRep_subgroupInduction (G := G) H
          ((projectiveGrothendieckScalarExtensionHom A K) [F]ₚ₀) =
        finiteRep_subgroupInduction (G := G) H
          ((projectiveGrothendieckScalarExtensionHom A K)
            [Q.residueFieldReduction]ₚ₀) := by
          rw [hF]
      _ = finiteRep_subgroupInduction (G := G) H [Q.scalarExtension K]₀ := by
          rw [hscalarH]
      _ = [(Q.subgroupInductionBase (G := G)).scalarExtension K]₀ := by
          exact finiteRep_subgroupInduction_projective_scalarExtension_class_eq
            (K := K) (G := G) H Q
      _ =
        projectiveGrothendieckScalarExtensionHom A K
          [(Q.subgroupInductionBase (G := G)).residueFieldReduction]ₚ₀ := by
          rw [hscalarG]
      _ =
        projectiveGrothendieckScalarExtensionHom A K
          (projective_subgroupInduction (G := G) H [Q.residueFieldReduction]ₚ₀) := by
          rw [projective_subgroupInduction_residueFieldReduction_class_eq
            (G := G) H Q]
      _ =
        projectiveGrothendieckScalarExtensionHom A K
          (projective_subgroupInduction (G := G) H [F]ₚ₀) := by
          rw [hF]
  · intro b hb
    simpa [map_neg] using congrArg Neg.neg hb
  · intro b c hb hc
    simpa [map_add, hb, hc] using congrArg₂ HAdd.hAdd hb hc

/-- Helper for Theorem 16-16.2-1: once the source-faithful elementary-induction decomposition is
packaged, the global range witness is assembled by summing the induced projective witnesses. -/
private theorem
    mem_projectiveGrothendieckScalarExtension_range_of_elementary_projective_induction_decomposition_local
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {x : R₀[K](G)}
    (hdecomp :
      ∃ (ι : Type (u + 1)) (_ : Fintype ι) (H : ι → Subgroup G)
        (_ : ∀ i, IsElementary (H i)) (y : ∀ i, P₀[k](H i)),
          x = ∑ i, finiteRep_subgroupInduction (G := G) (H i)
            ((projectiveGrothendieckScalarExtensionHom A K) (y i))) :
    x ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range := by
  classical
  rcases hdecomp with ⟨ι, hι, H, _hH, y, rfl⟩
  letI : Fintype ι := hι
  refine ⟨∑ i, projective_subgroupInduction (G := G) (H i) (y i), ?_⟩
  -- Evaluate Serre's map on the summed projective witness and rewrite each term by the
  -- subgroup-induction/scalar-extension compatibility lemma.
  refine
    (map_sum (projectiveGrothendieckScalarExtensionHom A K)
      (fun i ↦ projective_subgroupInduction (G := G) (H i) (y i)) Finset.univ).trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  simpa using
    (projective_scalarExtension_subgroupInduction_eq_subgroupInduction_projective_scalarExtension_local
      (A := A) (K := K) (G := G) (H := H i) (y := y i)).symm

/-- Helper for Theorem 16-16.2-1: a class in the projective scalar-extension range has ordinary
character zero on every `p`-singular element. -/
private theorem character_eq_zero_on_pSingular_of_mem_projectiveGrothendieckScalarExtension_range_local
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {x : R₀[K](G)}
    (hx :
      x ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range) :
    ∀ g : G, ¬ IsPRegular p g → (finiteRepGrothendieckCharacter K G x : G → K) g = 0 := by
  -- Route correction: the forward implication should run through the honest projective generator
  -- case and the cyclic restriction bridge, not through the broken owner-normalization block that
  -- previously occupied this file.
  rcases hx with ⟨y, rfl⟩
  intro g hg
  -- Expand the projective Grothendieck witness additively until only genuine projective
  -- generators remain.
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro F
    obtain ⟨Q, hQ⟩ :=
      residueField_projective_class_has_scalarExtension_lift_local
        (A := A) (K := K) (G := G) F
    change
      (finiteRepGrothendieckCharacter K G
          ((projectiveGrothendieckScalarExtensionHom A K) [F]ₚ₀) : G → K) g = 0
    rw [hQ]
    -- The actual projective lift is the remaining forward core.
    simpa [finiteRepGrothendieckCharacter_class] using
      projective_scalar_extension_character_eq_zero_on_pSingular_local
        (A := A) (K := K) (G := G) (p := p) Q g hg
  · intro b hb
    simpa [map_neg] using congrArg Neg.neg hb
  · intro b c hb hc
    simpa [map_add, hb, hc] using congrArg₂ HAdd.hAdd hb hc

/-- Helper for Theorem 16-16.2-1: vanishing on `p`-singular elements forces membership in the
projective scalar-extension range. -/
private theorem mem_projectiveGrothendieckScalarExtension_range_of_character_zero_on_pSingular_local
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {x : R₀[K](G)}
    (hx :
      ∀ g : G, ¬ IsPRegular p g → (finiteRepGrothendieckCharacter K G x : G → K) g = 0) :
    x ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range := by
  classical
  let e : P_k(G) →+ R₀[K](G) := projectiveGrothendieckScalarExtensionHom A K
  let d : R₀[K](G) →+ R₀[k](G) := decompositionHom A K G
  let n : ℕ := Nat.factorization (Nat.card G) p
  let N : ℕ := p ^ n
  let m : ℕ := ordCompl[p] (Nat.card G)
  have hcard : Nat.card G = p ^ n * m := by
    simpa [n, m] using (Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) p).symm
  have hm : Nat.Coprime p m := by
    simpa [m] using Nat.coprime_ordCompl (Fact.out : Nat.Prime p) (Nat.card_pos (α := G)).ne'
  have hcartan : (N : ℕ) • d x ∈ (cartanHom k G).range := by
    simpa [N, d] using
      cartanHom_surjective_on_p_part_multiples
        (p := p) (G := G) n m hcard hm (d x)
  rcases hcartan with ⟨y, hy⟩
  let z : R₀[K](G) := (N : ℕ) • x - e y
  have hdz : d z = 0 := by
    dsimp [z, d, e]
    rw [map_sub, map_nsmul,
      decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom
        (A := A) (K := K) (G := G) y,
      hy]
    simp [d]
  have hregular :
      ∀ g : G, IsPRegular p g → (finiteRepGrothendieckCharacter K G z : G → K) g = 0 :=
    character_eq_zero_on_pRegular_of_mem_decompositionHom_ker_local
      (A := A) (K := K) (G := G) (p := p) hdz
  have he_singular :
      ∀ g : G, ¬ IsPRegular p g → (finiteRepGrothendieckCharacter K G (e y) : G → K) g = 0 :=
    character_eq_zero_on_pSingular_of_mem_projectiveGrothendieckScalarExtension_range_local
      (A := A) (K := K) (G := G) (p := p) ⟨y, rfl⟩
  have hsingular :
      ∀ g : G, ¬ IsPRegular p g → (finiteRepGrothendieckCharacter K G z : G → K) g = 0 := by
    intro g hg
    have hxg := hx g hg
    have hyg := he_singular g hg
    have hNxg :
        (finiteRepGrothendieckCharacter K G ((N : ℕ) • x) : G → K) g = 0 := by
      rw [map_nsmul]
      change ((N • finiteRepGrothendieckCharacter K G x : R[K](G)) : G → K) g = 0
      simp [hxg]
    have hNxg_mul :
        (finiteRepGrothendieckCharacter K G ((N : R₀[K](G)) * x) : G → K) g = 0 := by
      rw [← nsmul_eq_mul N x]
      exact hNxg
    calc
      (finiteRepGrothendieckCharacter K G z : G → K) g =
          (finiteRepGrothendieckCharacter K G ((N : ℕ) • x - e y) : G → K) g := rfl
      _ =
          (finiteRepGrothendieckCharacter K G ((N : ℕ) • x) -
            finiteRepGrothendieckCharacter K G (e y) : R[K](G)) g := by
            rw [map_sub]
      _ = 0 := by
            simp [hNxg_mul, hyg]
  have hz : z = 0 :=
    eq_zero_of_character_eq_zero_on_pRegular_and_pSingular_local
      (K := K) (G := G) (p := p) hregular hsingular
  have hNx : (N : ℕ) • x = e y := by
    exact sub_eq_zero.mp hz
  obtain ⟨s, hs⟩ :=
    projectiveGrothendieckScalarExtensionHom_split_injective
      (A := A) (K := K) (G := G)
  have hsy : (N : ℕ) • s x = y := by
    calc
      (N : ℕ) • s x = s ((N : ℕ) • x) := (map_nsmul s N x).symm
      _ = s (e y) := by rw [hNx]
      _ = y := hs y
  have hdiff_nsmul : (N : ℕ) • (x - e (s x)) = 0 := by
    calc
      (N : ℕ) • (x - e (s x)) = (N : ℕ) • x - (N : ℕ) • e (s x) := by
        simpa using (nsmul_sub x (e (s x)) N)
      _ = e y - e ((N : ℕ) • s x) := by
        rw [hNx, map_nsmul]
      _ = 0 := by
        rw [hsy]
        simp
  have hN_ne : N ≠ 0 := by
    exact pow_ne_zero n (Fact.out : Nat.Prime p).ne_zero
  have hdiff : x - e (s x) = 0 :=
    finiteRepGrothendieckClass_eq_zero_of_nsmul_eq_zero_local
      (K := K) (G := G) (N := N) hN_ne hdiff_nsmul
  refine ⟨s x, ?_⟩
  exact (sub_eq_zero.mp hdiff).symm

-- Proof sketch: one direction uses projective-character vanishing for classes in the image of
-- `e`, and the converse identifies Serre's image with the kernel cut out by vanishing on
-- `p`-singular elements.
/-- Theorem 16-16.2-1: an element of `R_K(G)` lies in the image of
Serre's scalar-extension homomorphism `e : P_k(G) → R_K(G)` exactly when its ordinary character is
zero on every `p`-singular element of `G`. Here `k = IsLocalRing.ResidueField A`. -/
theorem mem_projectiveGrothendieckScalarExtension_range_iff_character_eq_zero_on_pSingular
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (x : R₀[K](G)) :
    x ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range ↔
      ∀ g : G, ¬ IsPRegular p g → (finiteRepGrothendieckCharacter K G x : G → K) g = 0 := by
  constructor
  · intro hx
    -- The forward direction is packaged in the local range-to-vanishing helper above.
    exact
      character_eq_zero_on_pSingular_of_mem_projectiveGrothendieckScalarExtension_range_local
        hx
  · intro hx
    -- The converse is packaged in the local vanishing-to-range helper above.
    exact
      mem_projectiveGrothendieckScalarExtension_range_of_character_zero_on_pSingular_local
        (A := A) (K := K) (G := G) (p := p) hx

/-- If a Grothendieck class lies in the image of Serre's projective scalar-extension map, then its
ordinary character vanishes on every `p`-singular element. This is the public forward direction of
Theorem `16-16.2-1`, exposed so later files can follow Serre's local-owner route directly. -/
theorem character_eq_zero_on_pSingular_of_mem_projectiveGrothendieckScalarExtension_range
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {x : R₀[K](G)}
    (hx :
      x ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range) :
    ∀ g : G, ¬ IsPRegular p g → (finiteRepGrothendieckCharacter K G x : G → K) g = 0 := by
  -- Reuse the local forward-direction proof packaged just above.
  exact
    character_eq_zero_on_pSingular_of_mem_projectiveGrothendieckScalarExtension_range_local
      hx

end

end Representation
