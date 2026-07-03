import Mathlib
import LinearRepresentations_Serre_1977.Chap09.Proposition_9_9_4_2
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension

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
