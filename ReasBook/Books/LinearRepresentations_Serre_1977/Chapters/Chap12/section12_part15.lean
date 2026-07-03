import Mathlib
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_12_12_5_1 (from Chap12) -/
open scoped BigOperators Representation SubgroupInduction

noncomputable section

universe u v w

namespace Representation

open CategoryTheory

section

variable (K : Type v) [Field K] [CharZero K]
variable (G : Type u) [Group G] [Finite G]
variable (A : Type w) [CommRing A] [Algebra A K]

private local instance : Fintype G := Fintype.ofFinite G

private local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

local notation "CycSub" => { H : Subgroup G // IsCyclic H }

/-- The induction map
`A ⊗ Ind : ⨁_{H cyclic} (A ⊗ R_K(H)) → A ⊗ R_K(G)` on the direct sum of the scalar-extended
character rings of the cyclic subgroups of `G`. -/
def cyclicSubgroupInduction :
    (Π₀ H : CycSub, A ⊗R[K](H.1)) →ₗ[A] A ⊗R[K](G) :=
  open Classical in
  DFinsupp.lsum A fun H ↦ H.1.characterRingOverFieldAlgebraScalarExtensionInduction

end

section

variable {K : Type v} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

private local instance : Fintype G := Fintype.ofFinite G

private local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

local notation "CycSub" => { H : Subgroup G // IsCyclic H }

private local instance : Fintype CycSub := Fintype.ofFinite CycSub

private local instance : DecidableEq CycSub := Classical.decEq _

private local instance (H : CycSub) (χ : ℚ⊗R[K](H.1)) : Decidable (χ ≠ 0) := by
  classical
  infer_instance

/-- Helper for Theorem 12-12.5-1: every element of `ℚ ⊗ R_K(G)` is a class function. -/
lemma isClassFunction_of_mem_characterRingOverFieldScalarExtension
    {f : G → K} (hf : f ∈ ℚ⊗R[K](G)) :
    _root_.IsClassFunction f := by
  -- The scalar extension is the rational span of actual characters, so class-function invariance
  -- is preserved by the span operations.
  induction hf using Submodule.span_induction with
  | mem ψ hψ =>
      exact isClassFunction_of_mem_characterRingOverField ψ (by simpa using hψ)
  | zero =>
      simpa using (inferInstance : _root_.IsClassFunction (fun _ : G ↦ (0 : K)))
  | add f g _ _ hf hg =>
      letI : _root_.IsClassFunction f := hf
      letI : _root_.IsClassFunction g := hg
      simpa using (inferInstance : _root_.IsClassFunction (f + g))
  | smul a f _ hf =>
      letI : _root_.IsClassFunction f := hf
      simpa using (inferInstance : _root_.IsClassFunction (a • f))

/-- Helper for Theorem 12-12.5-1: on the top subgroup, the subgroup version of `θ` agrees with
the ambient one over an arbitrary characteristic-zero field. -/
lemma top_cyclicGroupTheta_eq_overField {K : Type v} [Field K] {G : Type u} [Group G] [Finite G] :
    (fun g : G ↦ ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → K) ⟨g, Subgroup.mem_top g⟩)) =
      (θ[G] : G → K) := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype (⊤ : Subgroup G) := Fintype.ofFinite _
  ext g
  have hsub :
      Subgroup.zpowers (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)) = ⊤ ↔
        Subgroup.zpowers g = (⊤ : Subgroup G) := by
    rw [← Subgroup.map_subtype_inj]
    rw [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, (⊤ : Subgroup G).range_subtype]
    simp
  by_cases hg : Subgroup.zpowers g = (⊤ : Subgroup G)
  · have hg' : Subgroup.zpowers (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)) = ⊤ := hsub.mpr hg
    simp [Representation.cyclicGroupTheta, hg, hg', Nat.card_eq_fintype_card]
  · have hg' : Subgroup.zpowers (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)) ≠ ⊤ := by
      intro h
      exact hg (hsub.mp h)
    simp [Representation.cyclicGroupTheta, hg, hg']

/-- Helper for Theorem 12-12.5-1: on a finite commutative group, the `H = ⊤` summand in LinearRepresentations_Serre_1977's
induction formula is exactly the original auxiliary function `θ`. -/
lemma top_induced_cyclicGroupTheta_eq_overField {G : Type u} [CommGroup G] [Finite G] :
    Ind[(⊤ : Subgroup G)]((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → K)) = (θ[G] : G → K) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hcard : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  ext g
  let gtop : (⊤ : Subgroup G) := ⟨g, Subgroup.mem_top g⟩
  -- In a commutative group every conjugate of `g` is `g`, so the induction sum is constant.
  calc
    Ind[(⊤ : Subgroup G)]((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → K)) g
        = ((Nat.card (⊤ : Subgroup G) : K)⁻¹) *
            ∑ s : G,
              if hs : s⁻¹ * g * s ∈ (⊤ : Subgroup G) then
                ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → K) ⟨s⁻¹ * g * s, hs⟩)
              else 0 := by
            rfl
    _ = (Nat.card G : K)⁻¹ *
            ∑ s : G,
              if hs : s⁻¹ * g * s ∈ (⊤ : Subgroup G) then
                ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → K) ⟨s⁻¹ * g * s, hs⟩)
              else 0 := by
            simp [Nat.card_eq_fintype_card]
    _ = (Nat.card G : K)⁻¹ * ∑ _s : G, ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → K) gtop) := by
          refine congrArg ((Nat.card G : K)⁻¹ * ·) ?_
          refine Fintype.sum_congr
            (fun s : G ↦
              if hs : s⁻¹ * g * s ∈ (⊤ : Subgroup G) then
                ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → K) ⟨s⁻¹ * g * s, hs⟩)
              else 0)
            (fun _s : G ↦ ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → K) gtop))
            ?_
          intro s
          have hs : s⁻¹ * g * s = g := by
            calc
              s⁻¹ * g * s = s⁻¹ * s * g := by
                ac_rfl
              _ = g := by
                simp
          have hsub :
              (⟨s⁻¹ * g * s, Subgroup.mem_top _⟩ : (⊤ : Subgroup G)) = gtop := by
            apply Subtype.ext
            simp [gtop, hs]
          simp [hs, gtop]
    _ = (Nat.card G : K)⁻¹ *
          ((Nat.card G : K) * ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → K) gtop)) := by
          simp [Finset.sum_const, Nat.card_eq_fintype_card, nsmul_eq_mul]
    _ = (((Nat.card G : K)⁻¹ * (Nat.card G : K)) *
          ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → K) gtop)) := by
          rw [mul_assoc]
    _ = ((θ[(⊤ : Subgroup G)] : (⊤ : Subgroup G) → K) gtop) := by
          rw [inv_mul_cancel₀ hcard, one_mul]
    _ = (θ[G] : G → K) g := by
          simpa [gtop] using congrFun (top_cyclicGroupTheta_eq_overField (K := K) (G := G)) g

/-- Helper for Theorem 12-12.5-1: the auxiliary cyclic class function `θ[H]` belongs to
`ℚ ⊗ R_K(H)` for every cyclic subgroup `H ≤ G`. -/
lemma cyclicGroupTheta_mem_characterRingOverFieldScalarExtension
    (H : Subgroup G) (hH : IsCyclic H) :
    (θ[H] : H → K) ∈ ℚ⊗R[K](H) := by
  classical
  let _ : CommGroup H := IsCyclic.commGroup
  let P : ℕ → Prop := fun n ↦
    ∀ (A : Type u) (_ : Group A) (_ : Finite A) (_ : IsCyclic A),
      Nat.card A = n → (θ[A] : A → K) ∈ ℚ⊗R[K](A)
  have hstrong : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih A _ _ hAcyc hAcard
    let _ : CommGroup A := IsCyclic.commGroup
    let _ : Fintype A := Fintype.ofFinite A
    let S : Finset (Subgroup A) := Subgroup.cyclicSubgroups A
    have htop : (⊤ : Subgroup A) ∈ S := by
      simpa [S] using (Subgroup.mem_cyclicSubgroups.2 inferInstance :
        (⊤ : Subgroup A) ∈ Subgroup.cyclicSubgroups A)
    -- Split LinearRepresentations_Serre_1977's cyclic sum into the top subgroup term and the proper subgroup contribution.
    have hsplit :
        Finset.sum S (fun J ↦ Ind[J]((θ[J] : J → K))) =
          Ind[(⊤ : Subgroup A)]((θ[(⊤ : Subgroup A)] : (⊤ : Subgroup A) → K)) +
            Finset.sum (S.erase ⊤) (fun J ↦ Ind[J]((θ[J] : J → K))) := by
      rw [← Finset.insert_erase htop]
      simp
    have hsum :
        Ind[(⊤ : Subgroup A)]((θ[(⊤ : Subgroup A)] : (⊤ : Subgroup A) → K)) +
            Finset.sum (S.erase ⊤) (fun J ↦ Ind[J]((θ[J] : J → K))) =
          (Nat.card A : K) • (1 : A → K) := by
      exact hsplit.symm.trans
        (sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one (G := A) (K := K))
    -- Every proper cyclic subgroup term is already in the scalar extension by the strong
    -- induction hypothesis, and induction preserves that scalar extension.
    have hproper :
        Finset.sum (S.erase ⊤) (fun J ↦ Ind[J]((θ[J] : J → K))) ∈ ℚ⊗R[K](A) := by
      refine (ℚ⊗R[K](A)).sum_mem ?_
      intro J hJ
      have hJne : J ≠ ⊤ := (Finset.mem_erase.mp hJ).1
      have hthetaJ : (θ[J] : J → K) ∈ ℚ⊗R[K](J) := by
        have hlt : Nat.card J < n := by
          rw [← hAcard]
          let _ : Fintype J := Fintype.ofFinite J
          have hex : ∃ x : A, x ∉ J := by
            by_cases hforall : ∀ x : A, x ∈ J
            · exact False.elim (hJne (by
                ext x
                simp [hforall x]))
            · exact not_forall.mp hforall
          rcases hex with ⟨x, hx⟩
          rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
          simpa using (Fintype.card_subtype_lt (p := fun y : A ↦ y ∈ J) hx)
        simpa using ih (Nat.card J) hlt (A := ↥J) inferInstance inferInstance inferInstance rfl
      exact Subgroup.inducedClassFunction_mem_characterRingOverFieldAlgebraScalarExtension
        (A := ℚ) (K := K) J ⟨(θ[J] : J → K), hthetaJ⟩
    -- The constant term is a scalar in the owner `ℚ ⊗ R_K(A)`.
    have hconst : (Nat.card A : K) • (1 : A → K) ∈ ℚ⊗R[K](A) := by
      have hconst' :
          algebraMap ℚ (A → K) (Nat.card A : ℚ) ∈ ℚ⊗R[K](A) :=
        algebraMap_mem_characterRingOverFieldScalarExtension (K := K) (G := A)
          (Nat.card A : ℚ)
      convert hconst' using 1
      ext a
      simp [Pi.smul_apply]
    -- Rewrite LinearRepresentations_Serre_1977's identity as `θ[A] = |A| • 1 - (proper subgroup sum)`.
    have htheta_eq :
        (θ[A] : A → K) =
          (Nat.card A : K) • (1 : A → K) -
            Finset.sum (S.erase ⊤) (fun J ↦ Ind[J]((θ[J] : J → K))) := by
      have htop_theta :
          Ind[(⊤ : Subgroup A)]((θ[(⊤ : Subgroup A)] : (⊤ : Subgroup A) → K)) =
            (θ[A] : A → K) :=
        top_induced_cyclicGroupTheta_eq_overField (K := K) (G := A)
      rw [← htop_theta]
      exact eq_sub_iff_add_eq.2 hsum
    exact htheta_eq.symm ▸ (ℚ⊗R[K](A)).sub_mem hconst hproper
  have hH' : P (Nat.card H) := hstrong (Nat.card H)
  have hHH : (θ[H] : H → K) ∈ ℚ⊗R[K](H) := by
    exact hH' ↥H inferInstance inferInstance hH rfl
  simpa using hHH

/-- Helper for Theorem 12-12.5-1: restricting an element of `ℚ ⊗ R_K(G)` to a subgroup lands in
`ℚ ⊗ R_K(H)`. -/
lemma restrict_mem_characterRingOverFieldScalarExtension
    (H : Subgroup G) {f : G → K} (hf : f ∈ ℚ⊗R[K](G)) :
    (fun h : H ↦ f h) ∈ ℚ⊗R[K](H) := by
  -- Restrict the rational span generator-by-generator.
  induction hf using Submodule.span_induction with
  | mem χ hχ =>
      have hχ_mem : χ ∈ R[K](G) := by
        simpa using hχ
      have hχ_restrict : (fun h : H ↦ χ h) ∈ R[K](H) := by
        -- Restriction preserves the character-ring generators, hence the whole adjoin.
        refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ_mem
        · intro ψ hψ
          rcases hψ with ⟨ρ, hρfd, -, rfl⟩
          change (Rep.res H.subtype ρ).ρ.character ∈ R[K](H)
          letI : FiniteDimensional K ρ := hρfd
          letI : FiniteDimensional K (Rep.res H.subtype ρ) := by
            infer_instance
          exact rep_character_mem_characterRingOverField (Rep.res H.subtype ρ)
        · intro n
          exact (R[K](H)).algebraMap_mem n
        · intro f g _ _ hf hg
          simpa using (R[K](H)).add_mem hf hg
        · intro f g _ _ hf hg
          simpa using (R[K](H)).mul_mem hf hg
      exact mem_characterRingOverFieldScalarExtension_of_mem_characterRingOverField hχ_restrict
  | zero =>
      exact zero_mem (ℚ⊗R[K](H))
  | add f g _ _ hf hg =>
      simpa using (ℚ⊗R[K](H)).add_mem hf hg
  | smul a f _ hf =>
      simpa using (ℚ⊗R[K](H)).smul_mem a hf

/-- Helper for Theorem 12-12.5-1: multiplying an induced class function by a global element of
`ℚ ⊗ R_K(G)` is the same as inducing the product with the restricted function. -/
lemma induced_mul_eq_induced_mul_restrict_overField
    (H : Subgroup G) (ψ : H → K) {φ : G → K}
    (hφ : φ ∈ ℚ⊗R[K](G)) :
    Ind[H](fun h : H ↦ ψ h * φ h) = Ind[H](ψ) * φ := by
  -- The only input is that `φ` is a class function, which follows from scalar-extension
  -- membership.
  let hφClass : _root_.IsClassFunction φ :=
    isClassFunction_of_mem_characterRingOverFieldScalarExtension (K := K) hφ
  ext x
  simp only [Pi.mul_apply, Subgroup.inducedClassFunction]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro s hs
  by_cases hsx : s⁻¹ * x * s ∈ H
  · have hsx' : s⁻¹ * (x * s) ∈ H := by
      simpa [mul_assoc] using hsx
    have hsconj_eq : s * (s⁻¹ * x * s) * s⁻¹ = x := by
      group
    have hsconj : IsConj (s⁻¹ * x * s) x := by
      exact isConj_iff.2 ⟨s, hsconj_eq⟩
    have hφconj : φ (s⁻¹ * x * s) = φ x := by
      exact hφClass.eq_of_isConj hsconj
    have hφconj' : φ (s⁻¹ * (x * s)) = φ x := by
      simpa [mul_assoc] using hφconj
    simp [hsx', hφconj', mul_comm, mul_assoc]
  · simp [hsx]

/-- Helper for Theorem 12-12.5-1: each cyclic summand used in the Artin decomposition stays in
the appropriate subgroup scalar extension after multiplying by the restricted global factor. -/
lemma cyclicGroupTheta_mul_restrict_mem_characterRingOverFieldScalarExtension
    (H : CycSub) (φ : ℚ⊗R[K](G)) :
    (fun h : H.1 ↦ (θ[H.1] : H.1 → K) h * (φ : G → K) h) ∈ ℚ⊗R[K](H.1) := by
  -- Combine the cyclic `θ` membership with restriction and multiplicative closure.
  have htheta : (θ[H.1] : H.1 → K) ∈ ℚ⊗R[K](H.1) :=
    cyclicGroupTheta_mem_characterRingOverFieldScalarExtension (K := K) H.1 H.2
  have hrestrict : (fun h : H.1 ↦ (φ : G → K) h) ∈ ℚ⊗R[K](H.1) :=
    restrict_mem_characterRingOverFieldScalarExtension (K := K) (G := G) H.1 φ.2
  exact mul_mem_characterRingOverFieldScalarExtension htheta hrestrict

/-- Helper for Theorem 12-12.5-1: on a single cyclic direct-sum summand, the total induction map
is the corresponding subgroup induction map. -/
lemma cyclicSubgroupInduction_single
    (H : CycSub) (χ : ℚ⊗R[K](H.1)) :
    cyclicSubgroupInduction (A := ℚ) K G (DFinsupp.single H χ) =
      H.1.characterRingOverFieldAlgebraScalarExtensionInduction χ := by
  classical
  -- This is the owner-side `DFinsupp.single` evaluation formula for the total induction map.
  rw [cyclicSubgroupInduction, DFinsupp.lsum]
  exact DFinsupp.sumAddHom_single
    (fun H ↦ (H.1.characterRingOverFieldAlgebraScalarExtensionInduction).toAddMonoidHom) H χ

/-- Helper for Theorem 12-12.5-1: LinearRepresentations_Serre_1977's cyclic-subgroup identity rewritten on the actual owner
index `CycSub`. -/
lemma cyclicSubgroup_sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one
    {K : Type v} [Field K] :
    ∑ H : CycSub, Ind[H.1]((θ[H.1] : H.1 → K)) = (Nat.card G : K) • (1 : G → K) := by
  classical
  -- Reindex the Chapter 9 cyclic-subgroup sum from the filtered subgroup finset to the subtype of
  -- cyclic subgroups used by the direct-sum owner.
  calc
    ∑ H : CycSub, Ind[H.1]((θ[H.1] : H.1 → K))
        = ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H]) := by
            symm
            refine Finset.sum_subtype (M := G → K) (s := Subgroup.cyclicSubgroups G) ?_
              (fun H ↦ Ind[H](θ[H]))
            intro H
            exact
              (Subgroup.mem_cyclicSubgroups : H ∈ Subgroup.cyclicSubgroups G ↔ IsCyclic H)
    _ = (Nat.card G : K) • (1 : G → K) := by
          exact sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one (G := G) (K := K)

/-- Helper for Theorem 12-12.5-1: multiplying LinearRepresentations_Serre_1977's cyclic `θ`-identity by any
`φ ∈ ℚ ⊗ R_K(G)` produces a direct-sum preimage of `(Nat.card G : ℚ) • φ`. -/
lemma exists_cyclicSubgroupInduction_preimage_groupOrder_smul
    (φ : ℚ⊗R[K](G)) :
    ∃ ξ : Π₀ H : CycSub, ℚ⊗R[K](H.1),
      cyclicSubgroupInduction (A := ℚ) K G ξ = (Nat.card G : ℚ) • φ := by
  classical
  let χ : (H : CycSub) → ℚ⊗R[K](H.1) := fun H ↦
    ⟨fun h : H.1 ↦ (θ[H.1] : H.1 → K) h * (φ : G → K) h,
      cyclicGroupTheta_mul_restrict_mem_characterRingOverFieldScalarExtension (K := K) (G := G)
        H φ⟩
  let ξ : Π₀ H : CycSub, ℚ⊗R[K](H.1) := ∑ H : CycSub, DFinsupp.single H (χ H)
  refine ⟨ξ, ?_⟩
  -- Route correction: package the cyclic summands as a canonical finite sum of `DFinsupp.single`
  -- terms, then evaluate the owner map summand-by-summand.
  apply Subtype.ext
  ext g
  -- First expand the total induction map over the finite family of cyclic subgroups.
  calc
    ((cyclicSubgroupInduction (A := ℚ) K G ξ : ℚ⊗R[K](G)) : G → K) g
        = (((∑ H : CycSub, H.1.characterRingOverFieldAlgebraScalarExtensionInduction (χ H) :
              ℚ⊗R[K](G)) : ℚ⊗R[K](G)) : G → K) g := by
            dsimp [ξ]
            rw [map_sum]
            simp [cyclicSubgroupInduction_single]
    _ = (∑ H : CycSub, Ind[H.1]((χ H : H.1 → K)) g) := by
          simp
    _ = (∑ H : CycSub,
          (Ind[H.1](fun h : H.1 ↦ (θ[H.1] : H.1 → K) h * (φ : G → K) h)) g) := by
          refine Finset.sum_congr rfl ?_
          intro H hH
          simp [χ]
    _ = (∑ H : CycSub, (Ind[H.1]((θ[H.1] : H.1 → K)) * (φ : G → K)) g) := by
          refine Finset.sum_congr rfl ?_
          intro H hH
          rw [induced_mul_eq_induced_mul_restrict_overField (K := K) (G := G) H.1
            (θ[H.1] : H.1 → K) φ.2]
    _ = (((∑ H : CycSub, Ind[H.1]((θ[H.1] : H.1 → K))) * (φ : G → K)) g) := by
          simp [Pi.mul_apply, Finset.sum_mul]
    _ = ((((Nat.card G : K) • (1 : G → K)) * (φ : G → K)) g) := by
          rw [cyclicSubgroup_sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one (K := K) (G := G)]
    _ = (((Nat.card G : ℚ) • φ : ℚ⊗R[K](G)) : G → K) g := by
          simp [Pi.smul_apply, Pi.mul_apply, Rat.smul_def]

/-- Helper for Theorem 12-12.5-1: a preimage of the group-order multiple rescales to a preimage
of the original class function. -/
lemma cyclicSubgroupInduction_rescale_preimage
    {φ : ℚ⊗R[K](G)} {ξ : Π₀ H : CycSub, ℚ⊗R[K](H.1)}
    (hξ : cyclicSubgroupInduction (A := ℚ) K G ξ = (Nat.card G : ℚ) • φ) :
    cyclicSubgroupInduction (A := ℚ) K G (((Nat.card G : ℚ)⁻¹) • ξ) = φ := by
  have hcard : (Nat.card G : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  -- Use linearity of the induction map, then cancel the nonzero rational scalar.
  calc
    cyclicSubgroupInduction (A := ℚ) K G (((Nat.card G : ℚ)⁻¹) • ξ)
        = ((Nat.card G : ℚ)⁻¹) • cyclicSubgroupInduction (A := ℚ) K G ξ := by
            rw [map_smul]
    _ = ((Nat.card G : ℚ)⁻¹) • ((Nat.card G : ℚ) • φ) := by
          rw [hξ]
    _ = φ := by
          rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]

-- Proof sketch: either dualize to the restriction map on cyclic subgroups and prove that dual map
-- injective, or use the Artin-type identity expressing the unit character as a sum of inductions
-- from cyclic subgroups and conclude that the image is the whole ring ideal `ℚ ⊗ R_K(G)`.
/-- Theorem 12-12.5-1: if `T` is the set of cyclic subgroups of `G`, then the induction map
`ℚ ⊗ Ind : ⨁_{H ∈ T} (ℚ ⊗ R_K(H)) → ℚ ⊗ R_K(G)` is surjective. -/
theorem cyclicSubgroupInductionOverField_surjective :
    Function.Surjective (cyclicSubgroupInduction (A := ℚ) K G) := by
  intro φ
  -- First obtain a preimage of `(Nat.card G : ℚ) • φ` from the cyclic `θ`-decomposition.
  obtain ⟨ξ, hξ⟩ :=
    exists_cyclicSubgroupInduction_preimage_groupOrder_smul (K := K) (G := G) φ
  -- Then divide by the nonzero rational scalar in the source.
  refine ⟨((Nat.card G : ℚ)⁻¹) • ξ, ?_⟩
  exact cyclicSubgroupInduction_rescale_preimage (K := K) (G := G) hξ

end

end Representation

end

/-! ### Definition_12_12_6_1 (from Chap12) -/
noncomputable section

universe u

section Group

open Representation

variable {G : Type u} [Group G]

namespace Subgroup

-- Source/core/bridge triage:
-- * source-facing: `IsGammaPElementaryDecomposition ΓK p C P`, `IsGammaPElementary ΓK p H`, and
--   `IsGammaElementary ΓK H`.
-- * core/canonical: `IsPGroup`, `Subgroup.IsComplement'`, and the Chapter 10 owner
--   `IsPElementaryDecomposition` used for the trivial-`Γ_K` comparison.
-- * bridge/view: the `Γ_K = ⊥` comparison with ordinary `p`-elementary subgroups.
--
-- Relative to Chapter 10, the genuinely new primitive datum is the `Γ_K`-power-conjugation
-- condition. The subgroup-theoretic decomposition data stay in the same canonical owner layer as
-- before: prime `p`, finite `p`-group factor, cyclic prime-to-`p` factor, and complementarity.

/-- Helper for Definition 12-12.6-1: the natural-number representative of a `Γ_K` exponent unit.
-/
private abbrev gamma_power_exponent_unit
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} (t : ΓK) : ℕ :=
  ((t : (ZMod (Monoid.exponent G))ˣ) : ZMod (Monoid.exponent G)).val

/-- Helper for Definition 12-12.6-1: elements of `Γ_K` act on `G` by exponentiation using their
chosen representatives modulo `Monoid.exponent G`. -/
private instance gammaSubgroupPow
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} : Pow G ΓK where
  pow x t := x ^ gamma_power_exponent_unit (G := G) t

/-- Helper for Definition 12-12.6-1: the `Γ_K` power action unfolds to ordinary natural-number
exponentiation. -/
private theorem pow_subgroup_eq_pow_nat
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} (x : G) (t : ΓK) :
    (x ^ t : G) = x ^ gamma_power_exponent_unit (G := G) t := rfl

/-- A pair of subgroups `C` and `P` inside `H` gives a `Γ_K`-`p`-elementary decomposition if `p`
is prime, `C` is cyclic of order prime to `p`, `P` is a finite `p`-group, `C` and `P` are
complementary in `H`, and conjugation by every element of `P` acts on `C` through a power map
coming from `Γ_K`. -/
def IsGammaPElementaryDecomposition (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (p : ℕ)
    {H : Subgroup G} (C P : Subgroup H) : Prop :=
  Nat.Prime p ∧
    Finite P ∧
      IsCyclic C ∧
        Nat.Coprime p (Nat.card C) ∧
          IsPGroup p P ∧
            C.IsComplement' P ∧
              ∀ y : P, ∃ t : ΓK, ∀ x : C,
                (((y : H) : G) * ((x : H) : G) * ((y : H) : G)⁻¹ =
                  ((x : H) : G) ^ t)

namespace IsGammaPElementaryDecomposition

variable {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {p : ℕ} {H : Subgroup G} {C P : Subgroup H}

/-- The prime attached to a `Γ_K`-`p`-elementary decomposition. -/
theorem prime (h : IsGammaPElementaryDecomposition ΓK p C P) : Nat.Prime p := by
  rcases h with ⟨hp, -, -, -, -, -, -⟩
  exact hp

/-- Helper for Definition 12-12.6-1: the cyclic factor in a `Γ_K`-`p`-elementary decomposition
is finite. -/
theorem finite_cyclic_factor (h : IsGammaPElementaryDecomposition ΓK p C P) : Finite C := by
  rcases h with ⟨hp, -, -, hcoprime, -, -, -⟩
  by_contra hC
  -- An infinite cyclic factor has `Nat.card C = 0`, contradicting coprimality with a prime.
  have hInf : Infinite C := not_finite_iff_infinite.mp hC
  letI : Infinite C := hInf
  have hc : Nat.Coprime p 0 := by
    simpa [Nat.card_eq_zero_of_infinite] using hcoprime
  rw [Nat.coprime_zero_right] at hc
  exact hp.ne_one hc

/-- The `p`-group factor in a `Γ_K`-`p`-elementary decomposition is finite. -/
theorem finite_pGroup_factor (h : IsGammaPElementaryDecomposition ΓK p C P) : Finite P := by
  rcases h with ⟨-, hP, -, -, -, -, -⟩
  exact hP

/-- The cyclic factor in a `Γ_K`-`p`-elementary decomposition is cyclic. -/
theorem cyclic (h : IsGammaPElementaryDecomposition ΓK p C P) : IsCyclic C := by
  rcases h with ⟨-, -, hC, -, -, -, -⟩
  exact hC

/-- The cyclic factor has order prime to `p`. -/
theorem coprime_card (h : IsGammaPElementaryDecomposition ΓK p C P) :
    Nat.Coprime p (Nat.card C) := by
  rcases h with ⟨-, -, -, hcoprime, -, -, -⟩
  exact hcoprime

/-- The second factor is a `p`-group. -/
theorem isPGroup (h : IsGammaPElementaryDecomposition ΓK p C P) : IsPGroup p P := by
  rcases h with ⟨-, -, -, -, hP, -, -⟩
  exact hP

/-- Conjugation by elements of the `p`-group factor acts on the cyclic factor by `Γ_K`-power
maps. -/
theorem conjugation_eq_pow (h : IsGammaPElementaryDecomposition ΓK p C P) :
    ∀ y : P, ∃ t : ΓK, ∀ x : C,
      (((y : H) : G) * ((x : H) : G) * ((y : H) : G)⁻¹ =
        ((x : H) : G) ^ t) :=
  by
    rcases h with ⟨-, -, -, -, -, -, hgamma⟩
    exact hgamma

/-- The two factors are complementary subgroups of `H`. -/
theorem isComplement (h : IsGammaPElementaryDecomposition ΓK p C P) : C.IsComplement' P := by
  rcases h with ⟨-, -, -, -, -, hcomp, -⟩
  exact hcomp

@[simp] theorem pow_bot_eq_self
    (x : G) (t : (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ)) :
    x ^ t = x := by
  have ht : t = 1 := Subsingleton.elim _ _
  subst ht
  rw [pow_subgroup_eq_pow_nat]
  change x ^ (((1 : (ZMod (Monoid.exponent G))ˣ) : ZMod (Monoid.exponent G)).val) = x
  have hpow : x ^ (1 % Monoid.exponent G) = x ^ 1 := by
    simpa using (Eq.symm (@Monoid.pow_eq_mod_exponent G _ 1 x))
  simpa [ZMod.val_one_eq_one_mod] using hpow

/-- For `Γ_K = {1}`, a `Γ_K`-`p`-elementary decomposition is exactly an ordinary
`p`-elementary decomposition. -/
theorem bot_iff_isPElementaryDecomposition :
    IsGammaPElementaryDecomposition (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) p C P ↔
      IsPElementaryDecomposition p C P := by
  constructor
  · intro h
    refine ⟨h.prime, h.finite_pGroup_factor, h.cyclic, h.coprime_card, h.isPGroup, ?_,
      h.isComplement⟩
    rw [Subgroup.le_centralizer_iff]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases h.conjugation_eq_pow ⟨y, hy⟩ with ⟨t, ht⟩
    have hxpow : ((x : H) : G) ^ t = ((x : H) : G) := pow_bot_eq_self _ _
    have hconj : ((y : H) : G) * ((x : H) : G) * ((y : H) : G)⁻¹ = ((x : H) : G) := by
      simpa [hxpow] using ht ⟨x, hx⟩
    have hcomm : ((y : H) : G) * ((x : H) : G) = ((x : H) : G) * ((y : H) : G) :=
      (mul_inv_eq_iff_eq_mul).mp (by simpa [mul_assoc] using hconj)
    apply Subtype.ext
    exact hcomm.symm
  · intro h
    refine ⟨h.prime, h.finite_pGroup_factor, h.cyclic, h.coprime_card, h.isPGroup,
      h.isComplement, ?_⟩
    intro y
    let tOne : (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) := ⟨1, by simp⟩
    refine ⟨tOne, ?_⟩
    intro x
    have hyx : ((y : H) : G) * ((x : H) : G) = ((x : H) : G) * ((y : H) : G) := by
      simpa using congrArg (fun z : H ↦ ((z : H) : G))
        (h.commute x y).eq.symm
    have hxpow : ((x : H) : G) ^ tOne = ((x : H) : G) := pow_bot_eq_self _ _
    calc
      ((y : H) : G) * ((x : H) : G) * ((y : H) : G)⁻¹
          = ((x : H) : G) * ((y : H) : G) * ((y : H) : G)⁻¹ := by rw [hyx]
      _ = ((x : H) : G) := by simp [mul_assoc]
      _ = ((x : H) : G) ^ tOne := by
        symm
        exact hxpow

end IsGammaPElementaryDecomposition

/-- A subgroup `H` of `G` is `Γ_K`-`p`-elementary if it admits a `Γ_K`-`p`-elementary
decomposition by a cyclic prime-to-`p` factor and a finite `p`-group factor whose conjugation
action is given by `Γ_K`-power maps. -/
def IsGammaPElementary (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (p : ℕ)
    (H : Subgroup G) : Prop :=
  ∃ C P : Subgroup H, IsGammaPElementaryDecomposition ΓK p C P

/-- Definition 12-12.6-1: a subgroup `H` of `G` is `Γ_K`-elementary if it is `Γ_K`-`p`-elementary
for some prime number `p`. -/
def IsGammaElementary (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (H : Subgroup G) : Prop :=
  ∃ p : ℕ, IsGammaPElementary ΓK p H

-- Proof sketch: unfold `IsGammaPElementary` and read off the cyclic factor `C`, the `p`-group
-- factor `P`, and the accompanying `Γ_K`-power-conjugation condition from the existential data.
theorem IsGammaPElementary.prime
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {p : ℕ} {H : Subgroup G}
    (hH : IsGammaPElementary ΓK p H) : Nat.Prime p := by
  rcases hH with ⟨_, _, h⟩
  exact h.prime

/-- A `Γ_K`-`p`-elementary subgroup is, in particular, `Γ_K`-elementary. -/
theorem IsGammaPElementary.isGammaElementary
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {p : ℕ} {H : Subgroup G}
    (hH : IsGammaPElementary ΓK p H) :
    IsGammaElementary ΓK H :=
  ⟨p, hH⟩

-- Proof sketch: unfold `IsGammaElementary` and keep the prime `p` together with the witness that
-- `H` is `Γ_K`-`p`-elementary.
/-- A `Γ_K`-elementary subgroup is `Γ_K`-`p`-elementary for some prime `p`. -/
theorem IsGammaElementary.exists_prime_and_pElementary
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {H : Subgroup G} (hH : IsGammaElementary ΓK H) :
    ∃ p : ℕ, Nat.Prime p ∧ IsGammaPElementary ΓK p H := by
  rcases hH with ⟨p, hp⟩
  exact ⟨p, hp.prime, hp⟩

-- Proof sketch: if `Γ_K = {1}`, then the only allowed power map is the identity modulo
-- `Monoid.exponent G`, so the conjugation condition says that the cyclic factor commutes with the
-- `p`-group factor; this is exactly LinearRepresentations_Serre_1977's earlier definition of an ordinary `p`-elementary
-- subgroup, and conversely.
/-- For the trivial subgroup `Γ_K = {1}`, `Γ_K`-`p`-elementary subgroups are exactly the ordinary
`p`-elementary subgroups from Chapter 10. -/
theorem IsGammaPElementary.bot_iff_isPElementary
    (p : ℕ) (H : Subgroup G) :
    IsGammaPElementary (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) p H ↔ IsPElementary p H := by
  constructor
  · rintro ⟨C, P, h⟩
    exact ⟨C, P, IsGammaPElementaryDecomposition.bot_iff_isPElementaryDecomposition.mp h⟩
  · rintro ⟨C, P, h⟩
    exact ⟨C, P, IsGammaPElementaryDecomposition.bot_iff_isPElementaryDecomposition.mpr h⟩

end Subgroup

end Group

/-! ### Exercise_12_12_6_6 (from Chap12) -/
open scoped BigOperators Representation SubgroupInduction

noncomputable section

universe u v w

namespace Subgroup

section

open Representation

variable {K : Type v} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

omit [Finite G] [CharZero K] in
/-- Helper for Exercise 12-12.6-6: restricting a bundled class function to a subgroup remains a
bundled class function. -/
private theorem classFunctionRestriction_mem (H : Subgroup G) (χ : classFunctionSubmodule K G) :
    ((LinearMap.funLeft K K H.subtype).comp (classFunctionSubmodule K G).subtype) χ ∈
      classFunctionSubmodule K H := by
  change IsClassFunction (fun h : H ↦ (χ : G → K) h)
  letI : IsClassFunction (χ : G → K) := (mem_classFunctionSubmodule_iff K _).1 χ.2
  refine ⟨fun {u v} huv ↦ ?_⟩
  have huvH : IsConj u v := (ConjClasses.mk_eq_mk_iff_isConj).1 huv
  have huvG : IsConj (u : G) (v : G) := by
    rw [isConj_iff] at huvH ⊢
    rcases huvH with ⟨c, hc⟩
    exact ⟨(c : G), by simpa using congrArg Subtype.val hc⟩
  exact (inferInstance : IsClassFunction (χ : G → K)).eq_of_isConj huvG

omit [Finite G] [CharZero K] in
/-- Helper for Exercise 12-12.6-6: restriction of a bundled class function to a subgroup. -/
private def classFunctionRestriction (H : Subgroup G) :
    classFunctionSubmodule K G →ₗ[K] classFunctionSubmodule K H :=
  LinearMap.codRestrict (classFunctionSubmodule K H)
    ((LinearMap.funLeft K K H.subtype).comp (classFunctionSubmodule K G).subtype)
    (classFunctionRestriction_mem H)

omit [Finite G] [CharZero K] in
/-- Helper for Exercise 12-12.6-6: evaluating the bundled restriction map just reuses the same
group element inside `G`. -/
@[simp] private theorem classFunctionRestriction_apply
    (H : Subgroup G) (χ : classFunctionSubmodule K G) (h : H) :
    (H.classFunctionRestriction χ : H → K) h = (χ : G → K) h :=
  rfl

-- Source/core/bridge triage: the exercise is `source-facing`, so the owner here is the intrinsic
-- `K`-valued ring `R̄[K](G)`. The algebraic-closure realization
-- `overlineCharacterRingOverField K G` is only a bridge/view and should not own the main
-- induction API.
-- Proof sketch: if `χ ∈ R̄[K](H)`, then its coefficientwise image in `AlgebraicClosure K`
-- belongs to `R[AlgebraicClosure K](H)` by `mem_overlineCharacterRingInExtension_iff`. Theorem
-- `12-12.6-2`
-- puts the induced closure-valued class function in `R[AlgebraicClosure K](G)`, and the
-- coefficientwise embedding commutes with induction, so the induced `K`-valued class function
-- lies in `R̄[K](G)`.
/-- Inducing a virtual character in `\overline{R}_K(H)` gives an element of
`\overline{R}_K(G)`. -/
theorem inducedClassFunction_mem_overlineCharacterRing
    (H : Subgroup G) (χ : R̄[K](H)) :
    Ind[H]((χ : H → K)) ∈ R̄[K](G) := by
  -- Move the source character to the algebraic closure, where induction already preserves the
  -- honest character ring.
  let χL : H → AlgebraicClosure K := fun h ↦ algebraMap K (AlgebraicClosure K) ((χ : H → K) h)
  have hχL : χL ∈ R[AlgebraicClosure K](H) := by
    simpa [χL] using
      (mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) (χ : H → K)).1 χ.2
  -- Coefficientwise extension commutes with the induction formula, so the target is the induced
  -- algebraic-closure-valued virtual character.
  have hInd :
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G)
          (Ind[H]((χ : H → K))) =
        Ind[H](χL) := by
    ext g
    classical
    rw [Subgroup.inducedClassFunction, Subgroup.inducedClassFunction]
    change
      algebraMap K (AlgebraicClosure K)
          ((Nat.card H : K)⁻¹ *
            ∑ s : G, if hsg : s⁻¹ * g * s ∈ H then (χ : H → K) ⟨s⁻¹ * g * s, hsg⟩ else 0) =
        (Nat.card H : AlgebraicClosure K)⁻¹ *
          ∑ s : G, if hsg : s⁻¹ * g * s ∈ H then χL ⟨s⁻¹ * g * s, hsg⟩ else 0
    rw [map_mul]
    have hsum :
        algebraMap K (AlgebraicClosure K)
            (∑ s : G, if hsg : s⁻¹ * g * s ∈ H then (χ : H → K) ⟨s⁻¹ * g * s, hsg⟩ else 0) =
          ∑ s : G, if hsg : s⁻¹ * g * s ∈ H then χL ⟨s⁻¹ * g * s, hsg⟩ else 0 := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro s hs
      by_cases hsg : s⁻¹ * g * s ∈ H
      · simp [hsg, χL]
      · simp [hsg]
    rw [map_inv₀, map_natCast, hsum]
  refine (mem_overlineCharacterRingInExtension_iff
    K (AlgebraicClosure K) (Ind[H]((χ : H → K)))).2 ?_
  exact hInd ▸
    Subgroup.inducedClassFunction_mem_characterRingOverField
      (K := AlgebraicClosure K) H ⟨χL, hχL⟩

/-- The canonical `ℤ`-linear induction map `\overline{R}_K(H) → \overline{R}_K(G)`. -/
def overlineCharacterRingInduction (H : Subgroup G) (K : Type v) [Field K] [CharZero K] :
    R̄[K](H) →ₗ[ℤ] R̄[K](G) :=
  LinearMap.codRestrict
    (R̄[K](G)).toSubmodule
    ((((classFunctionSubmodule K G).subtype.comp H.classFunctionInduction).restrictScalars ℤ).comp
      (R̄[K](H)).toSubmodule.subtype)
    (inducedClassFunction_mem_overlineCharacterRing H)

-- Proof sketch: this is immediate from the definition of `H.overlineCharacterRingInduction K`.
/-- Evaluating the integral subgroup induction map recovers the induced `K`-valued class
function. -/
@[simp] theorem overlineCharacterRingInduction_apply
    (H : Subgroup G) (χ : R̄[K](H)) :
    ((H.overlineCharacterRingInduction K χ : R̄[K](G)) : G → K) =
      Ind[H]((χ : H → K)) :=
  rfl

end

end Subgroup

namespace Representation

section

variable {K : Type v} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G

local instance
    (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) :
    DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary ΓK H } :=
  Classical.decEq _

-- Proof sketch: follow the proof of Proposition `12-12.6-4`. Write the unit element of
-- `R[AlgebraicClosure K](G)` as a finite sum of inductions from `Γ_K`-elementary subgroups,
-- multiply by a given element of `R̄[K](G)`, and use closure of `R̄[K](H)` under multiplication
-- by restriction to keep every subgroup summand in the source-facing owner.
section

variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

omit [CharZero K] [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Exercise 12-12.6-6: multiplying an induced class function by a global class
function is the same as inducing the product with the restricted factor. -/
private lemma induced_mul_eq_induced_mul_classFunctionRestriction_overField
    (H : Subgroup G) (ψ : H → K) (φ : classFunctionSubmodule K G) :
    Ind[H](ψ) * (φ : G → K) =
      Ind[H](fun h : H ↦ ψ h * (H.classFunctionRestriction φ : H → K) h) := by
  classical
  -- Compare the two induced class functions pointwise, replacing the global class-function value
  -- by its conjugacy-invariant value on the subgroup element contributing to induction.
  ext x
  simp only [Pi.mul_apply, Subgroup.inducedClassFunction]
  rw [mul_assoc, Finset.sum_mul]
  have hsum :
      ∑ s : G, (if hsx : s⁻¹ * x * s ∈ H then ψ ⟨s⁻¹ * x * s, hsx⟩ else 0) * (φ : G → K) x =
        ∑ s : G, if hsx : s⁻¹ * x * s ∈ H then
          ψ ⟨s⁻¹ * x * s, hsx⟩ * (H.classFunctionRestriction φ : H → K) ⟨s⁻¹ * x * s, hsx⟩
        else 0 := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    by_cases hsx : s⁻¹ * x * s ∈ H
    · have hsx' : s⁻¹ * (x * s) ∈ H := by
        simpa [mul_assoc] using hsx
      have hφ :
          (φ : G → K) (s⁻¹ * x * s) = (φ : G → K) x := by
        exact ((mem_classFunctionSubmodule_iff K _).1 φ.2).eq_of_isConj <|
          isConj_iff.2 ⟨s, by group⟩
      have hφ' :
          (φ : G → K) (s⁻¹ * (x * s)) = (φ : G → K) x := by
        simpa [mul_assoc] using hφ
      simp [hsx', Subgroup.classFunctionRestriction_apply, hφ', mul_comm, mul_assoc]
    · simp [hsx]
  rw [hsum]

omit [CharZero K] in
/-- Helper for Exercise 12-12.6-6: descent along `K ↪ AlgebraicClosure K` is injective on
coefficients. -/
private theorem algebraMap_algebraicClosure_injective :
    Function.Injective (algebraMap K (AlgebraicClosure K)) := by
  exact (algebraMap K (AlgebraicClosure K)).injective

omit [Finite G] [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Exercise 12-12.6-6: precomposition along a function produces the canonical
`ℤ`-algebra hom on function spaces. -/
private def precompAlgHom {α β : Type*} (f : α → β) :
    (β → K) →ₐ[ℤ] α → K where
  toFun := LinearMap.funLeft ℤ K f
  map_zero' := rfl
  map_one' := rfl
  map_add' χ ψ := by
    ext x
    rfl
  map_mul' χ ψ := by
    ext x
    rfl
  commutes' n := by
    ext x
    rfl

omit [Finite G] [CharZero K] [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Exercise 12-12.6-6: restricting a finite-dimensional representation preserves
finite-dimensionality. -/
private theorem finiteDimensional_res
    {H J : Type u} [Monoid H] [Monoid J] (f : H →* J)
    (ρ : Rep.{max u v} K J) [FiniteDimensional K ρ] :
    FiniteDimensional K (Rep.res f ρ) := by
  infer_instance

omit [Finite G] [CharZero K] [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Exercise 12-12.6-6: precomposition of an honest virtual character stays in the
honest character ring. -/
private theorem precomp_mem_characterRingOverField
    {H J : Type u} [Group H] [Group J] (f : H →* J) (χ : R[K](J)) :
    precompAlgHom (K := K) f χ ∈ R[K](H) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ χ.2
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, -, rfl⟩
    change (Rep.res f ρ).ρ.character ∈ R[K](H)
    letI : FiniteDimensional K ρ := hρfd
    letI : FiniteDimensional K (Rep.res f ρ) := finiteDimensional_res (K := K) f ρ
    exact Representation.rep_character_mem_characterRingOverField (Rep.res f ρ)
  · intro n
    exact (R[K](H)).algebraMap_mem n
  · intro x y _ _ hx hy
    simpa using (R[K](H)).add_mem hx hy
  · intro x y _ _ hx hy
    simpa using (R[K](H)).mul_mem hx hy

omit [Finite G] [CharZero K] [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Exercise 12-12.6-6: restricting an honest virtual character to a subgroup stays in
the honest character ring. -/
private theorem restrict_mem_characterRingOverField_of_mem
    (H : Subgroup G) {χ : G → K} (hχ : χ ∈ R[K](G)) :
    (fun h : H ↦ χ h) ∈ R[K](H) := by
  let χR : R[K](G) := ⟨χ, hχ⟩
  simpa [χR, precompAlgHom] using
    precomp_mem_characterRingOverField (K := K) H.subtype χR

omit [Finite G] [CharZero K] [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Exercise 12-12.6-6: every element of `\overline{R}_K(G)` is a class function. -/
private theorem isClassFunction_of_mem_overlineCharacterRing
    {χ : G → K} (hχ : χ ∈ R̄[K](G)) :
    IsClassFunction χ := by
  let χL : G → AlgebraicClosure K := fun g ↦ algebraMap K (AlgebraicClosure K) (χ g)
  have hχL : χL ∈ R[AlgebraicClosure K](G) := by
    -- Overline-membership is defined by honest character-ring membership after extending
    -- coefficients to the algebraic closure.
    rw [mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χ] at hχ
    simpa [χL] using hχ
  have hχL_class : IsClassFunction χL :=
    Representation.isClassFunction_of_mem_characterRingOverField χL hχL
  refine ⟨fun {x y} hxy ↦ ?_⟩
  -- Descend conjugacy invariance coefficientwise through the injective scalar extension.
  have hxyL :
      algebraMap K (AlgebraicClosure K) (χ x) =
        algebraMap K (AlgebraicClosure K) (χ y) := by
    change χL x = χL y
    exact hχL_class.factorsThrough hxy
  exact algebraMap_algebraicClosure_injective (K := K) hxyL

omit [Finite G] [CharZero K] in
/-- Helper for Exercise 12-12.6-6: restricting an overline virtual character to a subgroup stays
in the overline character ring. -/
private theorem restrict_mem_overlineCharacterRing
    (H : Subgroup G) {χ : G → K} (hχ : χ ∈ R̄[K](G)) :
    (fun h : H ↦ χ h) ∈ R̄[K](H) := by
  let χL : G → AlgebraicClosure K := fun g ↦ algebraMap K (AlgebraicClosure K) (χ g)
  have hχL : χL ∈ R[AlgebraicClosure K](G) := by
    -- First lift to the algebraic closure, where the restriction theorem is already available.
    rw [mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χ] at hχ
    simpa [χL] using hχ
  have hχLH : (fun h : H ↦ χL h) ∈ R[AlgebraicClosure K](H) := by
    -- The lifted character remains a virtual character after restricting to the subgroup.
    exact restrict_mem_characterRingOverField_of_mem (K := AlgebraicClosure K) H hχL
  -- Descend the restricted algebraic-closure-valued virtual character back to the source-facing
  -- owner `R̄[K](H)`.
  rw [mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) (fun h : H ↦ χ h)]
  simpa [χL] using hχLH

variable (K : IntermediateField ℚ L)

local notation "ΓK" => Γ[K](G)

/-- Helper for Exercise 12-12.6-6: classical decidability on the overline direct-sum
coefficients. -/
local instance
    (H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }) (χ : R̄[K](H.1)) :
    Decidable (χ ≠ 0) := by
  classical
  infer_instance

set_option maxHeartbeats 400000 in
-- The endgame expands a `DFinsupp` witness into a finite sum and then rewrites each summand
-- through induction-restriction identities; the extra heartbeats keep that normalization stable.
/-- Exercise 12-12.6-6: the induction map
`Ind : ⨁_{H ∈ X_K} \overline{R}_K(H) → \overline{R}_K(G)`
is surjective, where
`Γ_K = Γ[K](G) ⊆ (ℤ / mℤ)ˣ` and `X_K` is the set of `Γ_K`-elementary
subgroups of `G`. -/
theorem gammaElementarySubgroupOverlineCharacterRingInduction_surjective
    :
    Function.Surjective
      (DFinsupp.lsum ℤ
        (fun H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H } ↦
          H.1.overlineCharacterRingInduction K)) := by
  intro χ
  obtain ⟨ξ, hξ⟩ := gammaElementarySubgroupInductionOverField_surjective (G := G) (L := L)
    K (1 : R[K](G))
  have hχcf_mem : (χ : G → K) ∈ classFunctionSubmodule K G := by
    -- Package the source function into the canonical class-function owner before replaying the
    -- Proposition `12-12.6-4` induction identity.
    rw [mem_classFunctionSubmodule_iff K]
    exact isClassFunction_of_mem_overlineCharacterRing (K := K) χ.2
  let χcf : classFunctionSubmodule K G := ⟨(χ : G → K), hχcf_mem⟩
  let ηFun :
      (H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }) → R̄[K](H.1) :=
    fun H ↦
      let hη_mem :
          (fun h : H.1 ↦ (ξ H : H.1 → K) h * (H.1.classFunctionRestriction χcf : H.1 → K) h) ∈
            R̄[K](H.1) := by
        -- Each summand is the product of an honest subgroup virtual character with the restricted
        -- overline virtual character.
        refine (R̄[K](H.1)).mul_mem ?_ ?_
        · exact (characterRingOverField_le_overlineCharacterRing K H.1) (ξ H).2
        · exact restrict_mem_overlineCharacterRing (K := K) H.1 χ.2
      ⟨fun h : H.1 ↦ (ξ H : H.1 → K) h * (H.1.classFunctionRestriction χcf : H.1 → K) h,
        hη_mem⟩
  let η : Π₀ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, R̄[K](H.1) :=
    DFinsupp.equivFunOnFintype.symm ηFun
  have hone :
      ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, Ind[H.1]((ξ H : H.1 → K)) =
        (1 : G → K) := by
    -- Rewrite the Brauer-induction witness as an equality of ambient functions.
    have hξ_fun :
        ((gammaElementarySubgroupInductionOverField K ΓK ξ : R[K](G)) : G → K) =
          (1 : G → K) := by
      simpa using congrArg ((↑) : R[K](G) → G → K) hξ
    rw [gammaElementarySubgroupInductionOverField_apply] at hξ_fun
    simpa [Subgroup.characterRingOverFieldInduction_apply] using hξ_fun
  have hη_sum :
      η.sum (fun H ↦ (H.1.overlineCharacterRingInduction K).toAddMonoidHom) =
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          H.1.overlineCharacterRingInduction K (ηFun H) := by
    -- Convert the `DFinsupp` witness to the equivalent finite family before expanding the sum.
    have hη :
        DFinsupp.equivFunOnFintype η = ηFun := by
      funext H
      simpa [η] using congrFun (DFinsupp.equivFunOnFintype.apply_symm_apply ηFun) H
    calc
      η.sum (fun H ↦ (H.1.overlineCharacterRingInduction K).toAddMonoidHom) =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            H.1.overlineCharacterRingInduction K (DFinsupp.equivFunOnFintype η H) := by
              exact DFinsupp.sum_eq_sum_fintype
                (v := η)
                (f := fun H ψH ↦ (H.1.overlineCharacterRingInduction K).toAddMonoidHom ψH)
                (hf := fun H ↦ by simp)
      _ =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            H.1.overlineCharacterRingInduction K (ηFun H) := by
              rw [hη]
  refine ⟨η, ?_⟩
  let ψG : R̄[K](G) :=
    DFinsupp.lsum ℤ
      (fun H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H } ↦
        H.1.overlineCharacterRingInduction K) η
  have hψG_bundled :
      ψG =
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          H.1.overlineCharacterRingInduction K (ηFun H) := by
    -- Expand the direct-sum induction map only after normalizing the owner from `DFinsupp` to a
    -- finite family.
    calc
      ψG =
          (DFinsupp.sumAddHom fun H =>
            (H.1.overlineCharacterRingInduction K).toAddMonoidHom) η := by
            rfl
      _ = η.sum (fun H ψH ↦ (H.1.overlineCharacterRingInduction K).toAddMonoidHom ψH) := by
            rw [DFinsupp.sumAddHom_apply]
      _ =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            H.1.overlineCharacterRingInduction K (ηFun H) := hη_sum
  have hψG_pointwise (g : G) :
      (ψG : G → K) g =
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          Ind[H.1]((ηFun H : H.1 → K)) g := by
    -- Evaluate the bundled equality termwise using the explicit formula for subgroup induction.
    have hcoerce :
        (ψG : G → K) =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            Ind[H.1]((ηFun H : H.1 → K)) := by
      simpa [Subgroup.overlineCharacterRingInduction_apply] using
        congrArg ((↑) : R̄[K](G) → G → K) hψG_bundled
    simpa using congrFun hcoerce g
  have hψG :
      (ψG : G → K) = (χ : G → K) := by
    -- Multiply the decomposition of `1` by `χ`, then push the factor inside each induction using
    -- the Proposition `12-12.6-4` class-function identity.
    funext g
    rw [hψG_pointwise g]
    apply Subtype.ext
    change
      (((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          Ind[H.1]((ηFun H : H.1 → K)) g : K) : L) =
        (((χ : G → K) g : K) : L))
    calc
      (((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          Ind[H.1]((ηFun H : H.1 → K)) g : K) : L))
          =
            ((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
                (Ind[H.1]((ξ H : H.1 → K)) * (χ : G → K)) g : K) : L) := by
              refine congrArg (fun z : K => (z : L)) ?_
              refine Finset.sum_congr rfl ?_
              intro H hH
              have hterm :
                  Ind[H.1]((ηFun H : H.1 → K)) =
                    Ind[H.1]((ξ H : H.1 → K)) * (χcf : G → K) := by
                simpa [ηFun, χcf, Subgroup.classFunctionRestriction_apply] using
                  (induced_mul_eq_induced_mul_classFunctionRestriction_overField
                    (H := H.1) (ψ := (ξ H : H.1 → K)) (φ := χcf)).symm
              rw [hterm]
        _ =
            ((((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
                Ind[H.1]((ξ H : H.1 → K))) * (χ : G → K)) g : K) : L) := by
              refine congrArg (fun z : K => (z : L)) ?_
              simp [Pi.mul_apply, Finset.sum_mul]
        _ = ((((1 : G → K) * (χ : G → K)) g : K) : L) := by
              rw [hone]
        _ = (((χ : G → K) g : K) : L) := by
              simp
  exact Subtype.ext hψG

end

end

end Representation

/-! ### Proposition_12_12_6_4 (from Chap12) -/
noncomputable section

universe u v

open CategoryTheory
open scoped BigOperators Representation SubgroupInduction

namespace Subgroup

section

variable {G : Type u} [Group G]

/-- Internal owner for precomposition on function algebras. The public mathematical content of
this file is the induced restriction on `R[K](G)`, not this raw function-space bridge. -/
private def precompAlgHom {α β : Type*} (K : Type v) [Field K] (f : α → β) :
    (β → K) →ₐ[ℤ] α → K where
  toFun := LinearMap.funLeft ℤ K f
  map_zero' := rfl
  map_one' := rfl
  map_add' χ ψ := by
    ext x
    rfl
  map_mul' χ ψ := by
    ext x
    rfl
  commutes' n := by
    ext x
    rfl

private theorem finiteDimensional_res
    {H J : Type u} [Monoid H] [Monoid J] (K : Type v) [Field K]
    (f : H →* J) (ρ : Rep.{max u v} K J) [FiniteDimensional K ρ] :
    FiniteDimensional K (Rep.res f ρ) := by
  -- Restriction does not change the underlying `K`-vector space, so finite-dimensionality is
  -- inherited by instance search.
  infer_instance

private theorem precomp_mem_characterRingOverField
    {H J : Type u} [Group H] [Group J] (K : Type v) [Field K]
    (f : H →* J) (χ : R[K](J)) :
    precompAlgHom K f χ ∈ R[K](H) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ χ.2
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, -, rfl⟩
    change (Rep.res f ρ).ρ.character ∈ R[K](H)
    letI : FiniteDimensional K ρ := hρfd
    letI : FiniteDimensional K (Rep.res f ρ) := finiteDimensional_res K f ρ
    exact Representation.rep_character_mem_characterRingOverField (Rep.res f ρ)
  · intro n
    exact (R[K](H)).algebraMap_mem n
  · intro x y _ _ hx hy
    simpa using (R[K](H)).add_mem hx hy
  · intro x y _ _ hx hy
    simpa using (R[K](H)).mul_mem hx hy

-- Proof sketch: write `χ` as an integral linear combination of irreducible `K`-characters of
-- `G`. Restrict each generator along `H.subtype`; this is the character of the restricted
-- representation, hence lies in `R_K(H)`. The result follows by `ℤ`-linearity of the span
-- defining `characterRingOverField K`.
/-- Restricting an element of LinearRepresentations_Serre_1977's representation ring `R_K(G)` to a subgroup `H` gives an
element of `R_K(H)`. -/
theorem restrict_mem_characterRingOverField
    (K : Type v) [Field K] (H : Subgroup G) (χ : R[K](G)) :
    (fun h : H ↦ (χ : G → K) h) ∈ R[K](H) := by
  simpa using precomp_mem_characterRingOverField K H.subtype χ

/-- The canonical restriction algebra hom `R_K(G) → R_K(H)` attached to a subgroup `H ≤ G`. -/
def characterRingOverFieldRestriction (H : Subgroup G) (K : Type v) [Field K] :
    R[K](G) →ₐ[ℤ] R[K](H) :=
  (((precompAlgHom K H.subtype).comp (R[K](G)).val).codRestrict (R[K](H))
    (restrict_mem_characterRingOverField K H))

scoped[Representation] notation:max H " ↾R[" K "]" =>
  Subgroup.characterRingOverFieldRestriction H K

-- Proof sketch: `(H ↾R[K])` is defined by pointwise evaluation along `H.subtype`.
/-- Evaluating `(H ↾R[K]) χ` at `h ∈ H` just evaluates `χ` at the same group element. -/
@[simp] theorem characterRingOverFieldRestriction_apply
    (K : Type v) [Field K] (H : Subgroup G) (χ : R[K](G)) (h : H) :
    (((H ↾R[K]) χ : R[K](H)) : H → K) h = (χ : G → K) h :=
  rfl

-- Proof sketch: this is the same precomposition argument as
-- `restrict_mem_characterRingOverField`, now applied to the subgroup inclusion `H ↪ J`.
/-- Restricting an element of `R_K(J)` along an inclusion `H ≤ J` gives an element of `R_K(H)`. -/
theorem restrict_mem_characterRingOverFieldOfLe
    (K : Type v) [Field K] {H J : Subgroup G} (h : H ≤ J) (χ : R[K](J)) :
    (fun x : H ↦ (χ : J → K) (Subgroup.inclusion h x)) ∈ R[K](H) := by
  simpa using precomp_mem_characterRingOverField K (Subgroup.inclusion h) χ

/-- The canonical restriction map `R_K(J) → R_K(H)` attached to an inclusion `H ≤ J`. -/
def characterRingOverFieldRestrictionOfLe
    {H J : Subgroup G} (h : H ≤ J) (K : Type v) [Field K] :
    R[K](J) →ₐ[ℤ] R[K](H) :=
  (((precompAlgHom K (Subgroup.inclusion h)).comp (R[K](J)).val).codRestrict (R[K](H))
    (restrict_mem_characterRingOverFieldOfLe K h))

scoped[Representation] notation:max h " ↾R[" K "]" =>
  Subgroup.characterRingOverFieldRestrictionOfLe h K

-- Proof sketch: `(h ↾R[K])` is defined by evaluating `χ` on `H` through the inclusion `H ↪ J`.
/-- Evaluating `(h ↾R[K]) χ` at `x ∈ H` evaluates `χ` at the same group element viewed in `J`. -/
@[simp] theorem characterRingOverFieldRestrictionOfLe_apply
    {H J : Subgroup G} (h : H ≤ J) (K : Type v) [Field K] (χ : R[K](J)) (x : H) :
    (((h ↾R[K]) χ : R[K](H)) : H → K) x =
      (χ : J → K) (Subgroup.inclusion h x) :=
  rfl

end

end Subgroup

namespace Representation

section

variable {G : Type u} [Group G] [Finite G]
variable {L : Type v} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

local instance instFintypeGammaElementaryRestriction : Fintype G := Fintype.ofFinite G

/-- Helper for Proposition 12-12.6-4: multiplying an induced `K`-valued class function by a
global bundled class function is the same as inducing the product with the canonical restriction
of the global factor. -/
lemma induced_mul_eq_induced_mul_classFunctionRestriction_overField
    {K : Type v} [Field K] (H : Subgroup G) (ψ : H → K) (φ : classFunctionSubmodule K G) :
    Ind[H](ψ) * (φ : G → K) =
      Ind[H](fun h : H ↦ ψ h * (H.classFunctionRestriction φ : H → K) h) := by
  classical
  -- Compare both sides pointwise and replace the ambient value of `φ` by its conjugacy-invariant
  -- value on the subgroup element contributing to the induction summand.
  ext x
  simp only [Pi.mul_apply, Subgroup.inducedClassFunction]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro s hs
  by_cases hsx : s⁻¹ * x * s ∈ H
  · have hsx' : s⁻¹ * (x * s) ∈ H := by
      simpa [mul_assoc] using hsx
    have hφ :
        (φ : G → K) (s⁻¹ * x * s) = (φ : G → K) x := by
      exact ((mem_classFunctionSubmodule_iff K _).1 φ.2).eq_of_isConj <|
        isConj_iff.2 ⟨s, by group⟩
    have hφ' :
        (φ : G → K) (s⁻¹ * (x * s)) = (φ : G → K) x := by
      simpa [mul_assoc] using hφ
    simp [hsx', hφ', mul_comm, mul_assoc]
  · simp [hsx]

omit [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Proposition 12-12.6-4: normalize the `DFinsupp` witness for gamma-elementary
induction into the corresponding ordinary finite sum over gamma-elementary subgroups. -/
lemma gamma_elementary_induction_sum_as_fintype_sum
    {K : IntermediateField ℚ L}
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ}
    [Fintype { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }]
    [DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }]
    [(H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }) →
      (χ : R[K](H.1)) → Decidable (χ ≠ 0)]
    (χ : (H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }) → R[K](H.1))
    (η : Π₀ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, R[K](H.1))
    (hη : DFinsupp.equivFunOnFintype η = χ) :
    η.sum (fun H ↦ (H.1.characterRingOverFieldInduction K).toAddMonoidHom) =
      ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
        H.1.characterRingOverFieldInduction K (χ H) := by
  classical
  -- Replace the direct-sum object by the equivalent finitely indexed family before applying
  -- induction termwise on the gamma-elementary support.
  calc
    η.sum (fun H ↦ (H.1.characterRingOverFieldInduction K).toAddMonoidHom) =
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          H.1.characterRingOverFieldInduction K (DFinsupp.equivFunOnFintype η H) := by
          exact DFinsupp.sum_eq_sum_fintype
            (v := η)
            (f := fun H ψH ↦ (H.1.characterRingOverFieldInduction K).toAddMonoidHom ψH)
            (hf := fun H => by simp)
    _ =
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          H.1.characterRingOverFieldInduction K (χ H) := by
          rw [hη]

omit [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
/-- Helper for Proposition 12-12.6-4: multiplying Brauer's decomposition of `1` by `φ` turns the
induced sum of the modified subgroup terms back into `φ`. -/
lemma psi_eq_phi_from_brauer_decomposition
    {K : IntermediateField ℚ L}
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ}
    [Fintype { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }]
    (φ : classFunctionSubmodule K G)
    (ξ χ : (H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }) → R[K](H.1))
    (hχ :
      ∀ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
        (χ H : H.1 → K) =
          fun h : H.1 ↦
            (ξ H : H.1 → K) h * (H.1.classFunctionRestriction φ : H.1 → K) h)
    (hone :
      ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, Ind[H.1]((ξ H : H.1 → K)) =
        (1 : G → K)) :
    ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, Ind[H.1]((χ H : H.1 → K)) =
      (φ : G → K) := by
  classical
  -- Route correction: first prove the ambient function identity obtained by multiplying the
  -- Brauer decomposition of `1`, and only afterwards package it back into `R[K](G)`.
  funext g
  apply Subtype.ext
  calc
    ((((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
        Ind[H.1]((χ H : H.1 → K))) g : K) : L))
        =
          (((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
              Ind[H.1]((χ H : H.1 → K)) g : K) : L)) := by
            -- Expand the evaluation of the finite sum before rewriting each summand.
            refine congrArg (fun z : K ↦ (z : L)) ?_
            simp [Finset.sum_apply]
    _ =
          ((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
              (Ind[H.1]((ξ H : H.1 → K)) * (φ : G → K)) g : K) : L) := by
            -- Rewrite each summand using the induction-restriction compatibility lemma.
            refine congrArg (fun z : K ↦ (z : L)) ?_
            refine Finset.sum_congr rfl ?_
            intro H hH
            rw [hχ H]
            rw [← induced_mul_eq_induced_mul_classFunctionRestriction_overField
              (H := H.1) (ψ := (ξ H : H.1 → K)) (φ := φ)]
    _ =
        ((((∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            Ind[H.1]((ξ H : H.1 → K))) * (φ : G → K)) g : K) : L) := by
            -- Factor the common multiplicative term `φ` out of the finite sum.
            refine congrArg (fun z : K ↦ (z : L)) ?_
            simp [Pi.mul_apply, Finset.sum_mul]
    _ = ((((1 : G → K) * (φ : G → K)) g : K) : L) := by
          rw [hone]
    _ = (((φ : G → K) g : K) : L) := by
          simp

-- Proof sketch: the forward implication is `restrict_mem_characterRingOverField`. For the reverse
-- implication, use Theorem `12-12.6-2` to write the unit element of `R_K(G)` as a finite sum of
-- inductions from `Γ_K`-elementary subgroups, multiply by the class function `φ`, and use the
-- class-function induction identity `φ ⋅ Ind = Ind (Res φ ⋅ -)` to conclude from the restriction
-- hypothesis that every summand lies in `R_K(G)`.
--
-- Source/core/bridge triage:
-- * source-facing: the detection criterion for membership in `R_K(G)`.
-- * core/canonical owner: bundled `K`-valued class functions `classFunctionSubmodule K G`.
-- * bridge/view: the underlying function coercion `classFunctionSubmodule K G → G → K`.
--
-- Primitive data are the bundled class function `φ` and the restriction-membership hypotheses on
-- `Γ_K`-elementary subgroups. The raw function `(φ : G → K)` and the pointwise restrictions
-- `H.classFunctionRestriction φ` are derived API.
/-- Proposition 12-12.6-4: let `L / ℚ` be a cyclotomic realization for the exponent of `G`, and
let `K ⊆ L` be an intermediate field, with associated subgroup
`Γ_K = Γ[K](G) ⊆ (ℤ / mℤ)ˣ`, where `m = Monoid.exponent G`. A `K`-valued class
function on `G` belongs to `R[K](G)` if and only if, for every `Γ_K`-elementary subgroup `H ≤ G`,
its restriction to `H` belongs to `R[K](H)`. -/
theorem classFunction_mem_characterRingOverField_iff_restrict_mem_on_gammaElementarySubgroups
    (K : IntermediateField ℚ L) (φ : classFunctionSubmodule K G) :
    (φ : G → K) ∈ R[K](G) ↔
      ∀ H : Subgroup G, Subgroup.IsGammaElementary (Γ[K](G)) H →
        (H.classFunctionRestriction φ : H → K) ∈ R[K](H) := by
  let ΓK := Γ[K](G)
  constructor
  · intro hφ H hH
    -- Apply the canonical restriction map to the ambient virtual character and identify the
    -- resulting function with the canonical class-function restriction.
    have hrestrict : (fun h : H ↦ (φ : G → K) h) ∈ R[K](H) :=
      (((H ↾R[K]) ⟨(φ : G → K), hφ⟩ : R[K](H)) : R[K](H)).2
    simpa [Subgroup.classFunctionRestriction_apply] using hrestrict
  · intro hres
    classical
    obtain ⟨ξ, hξ⟩ := gammaElementarySubgroupInductionOverField_surjective (G := G) (L := L)
      K (1 : R[K](G))
    let _ : DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary ΓK H } := Classical.decEq _
    let _ :
        (H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }) →
          (χ : R[K](H.1)) → Decidable (χ ≠ 0) := fun H χ => by
      classical
      infer_instance
    let χ : (H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }) → R[K](H.1) := fun H ↦
      ⟨fun h : H.1 ↦ (ξ H : H.1 → K) h * (H.1.classFunctionRestriction φ : H.1 → K) h,
        (R[K](H.1)).mul_mem (ξ H).2 (hres H.1 H.2)⟩
    let η : Π₀ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, R[K](H.1) :=
      DFinsupp.equivFunOnFintype.symm χ
    have hone :
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, Ind[H.1]((ξ H : H.1 → K)) =
          (1 : G → K) := by
      -- Re-express the surjective Brauer-induction witness as an equality of ambient functions.
      have hξ_fun :
          ((gammaElementarySubgroupInductionOverField K (Γ[K](G)) ξ : R[K](G)) : G → K) =
            (1 : G → K) := by
        simpa using congrArg ((↑) : R[K](G) → G → K) hξ
      rw [gammaElementarySubgroupInductionOverField_apply] at hξ_fun
      simpa [Subgroup.characterRingOverFieldInduction_apply] using hξ_fun
    have hχ :
        ∀ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
          (χ H : H.1 → K) =
            fun h : H.1 ↦
              (ξ H : H.1 → K) h * (H.1.classFunctionRestriction φ : H.1 → K) h := by
      -- The modified subgroup family `χ` was defined exactly by multiplying `ξ H` with the
      -- restricted class function on `H`.
      intro H
      rfl
    have hη : DFinsupp.equivFunOnFintype η = χ := by
      -- `η` is the direct-sum packaging of the finitely indexed family `χ`.
      funext H
      simpa [η] using congrFun (DFinsupp.equivFunOnFintype.apply_symm_apply χ) H
    let ψG : R[K](G) := gammaElementarySubgroupInductionOverField K ΓK η
    have hψG_sum :
        η.sum (fun H ↦ (H.1.characterRingOverFieldInduction K).toAddMonoidHom) =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            H.1.characterRingOverFieldInduction K (χ H) :=
      gamma_elementary_induction_sum_as_fintype_sum (K := K) (ΓK := ΓK) χ η hη
    have hψG_bundled :
        ψG =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            H.1.characterRingOverFieldInduction K (χ H) := by
      -- Expand the direct-sum Brauer witness only after the `DFinsupp` owner has been normalized.
      simpa [ψG, gammaElementarySubgroupInductionOverField_apply] using hψG_sum
    have hψG_pointwise (g : G) :
        (ψG : G → K) g =
          ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
            Ind[H.1]((χ H : H.1 → K)) g :=
        by
      -- Evaluate the bundled equality at `g` after each summand is in canonical induced form.
      have hcoerce :
          ((ψG : R[K](G)) : G → K) =
            ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H },
              Ind[H.1]((χ H : H.1 → K)) := by
        simpa [Subgroup.characterRingOverFieldInduction_apply] using
          congrArg ((↑) : R[K](G) → G → K) hψG_bundled
      simpa using congrFun hcoerce g
    have hsum_eq_phi :
        ∑ H : { H : Subgroup G // Subgroup.IsGammaElementary ΓK H }, Ind[H.1]((χ H : H.1 → K)) =
          (φ : G → K) :=
      psi_eq_phi_from_brauer_decomposition (ΓK := ΓK) φ ξ χ hχ hone
    have hψG : (ψG : G → K) = (φ : G → K) := by
      -- Compare `ψG` with the normalized finite sum, then use the Brauer-multiplication helper to
      -- identify that sum with `φ`.
      funext g
      rw [hψG_pointwise g]
      simpa using congrFun hsum_eq_phi g
    -- Package the reconstructed ambient function back into `R[K](G)`.
    simpa [ψG, hψG] using ψG.2

end

end Representation
