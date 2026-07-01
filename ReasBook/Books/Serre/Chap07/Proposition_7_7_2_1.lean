import Mathlib
import Serre.Chap02.Remark_2_2_1_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u v w

namespace Subgroup

section

variable {G : Type u} [Group G] [Finite G]
variable {K : Type v} [Semifield K]

local instance : Fintype G := Fintype.ofFinite G

/-- The class function on `G` induced from a `K`-valued function on the subgroup `H`; this is
Serre's `Ind_H^G(f)` or `Ind(f)`. -/
def inducedClassFunction (H : Subgroup G) (f : H → K) : G → K :=
  let _ : DecidablePred fun x : G ↦ x ∈ H := Classical.decPred _
  fun g ↦
    ((Nat.card H : K)⁻¹) *
      ∑ s : G,
        if hsg : s⁻¹ * g * s ∈ H then
          f ⟨s⁻¹ * g * s, hsg⟩
        else 0

scoped[SubgroupInduction] notation "Ind[" H "](" f ")" => Subgroup.inducedClassFunction H f

open scoped SubgroupInduction

-- Proof sketch: expand `inducedClassFunction` at two conjugate elements of `G` and reindex the
-- defining sum by multiplying the conjugating variable.
/-- Proposition 7-7.2-1 (1): the induced function on `G` is a class function. The source
hypothesis that `f` be a class function is mathematically redundant. -/
theorem inducedClassFunction_isClassFunction (H : Subgroup G) (f : H → K) :
    IsClassFunction (Ind[H](f)) := by
  refine ⟨?_⟩
  intro x y hxy
  rcases isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.mp hxy) with ⟨c, rfl⟩
  simp only [Subgroup.inducedClassFunction]
  congr 1
  let _ : DecidablePred fun z : G ↦ z ∈ H := Classical.decPred _
  let φ : G → K := fun s ↦
    if hs : s⁻¹ * x * s ∈ H then
      f ⟨s⁻¹ * x * s, hs⟩
    else 0
  let ψ : G → K := fun t ↦
    if ht : t⁻¹ * (c * x * c⁻¹) * t ∈ H then
      f ⟨t⁻¹ * (c * x * c⁻¹) * t, ht⟩
    else 0
  change ∑ s : G, φ s = ∑ t : G, ψ t
  simpa [φ, ψ] using
    Fintype.sum_bijective (c * ·) (Group.mulLeft_bijective c) _ _ fun s ↦ by
      change φ s = ψ (c * s)
      have hs' : s⁻¹ * c⁻¹ * (c * x * c⁻¹) * (c * s) = s⁻¹ * x * s := by
        group
      by_cases h : s⁻¹ * x * s ∈ H
      · have h'' : s⁻¹ * c⁻¹ * (c * x * c⁻¹) * (c * s) ∈ H := by
          simpa [hs'] using h
        have hsub :
            (⟨s⁻¹ * c⁻¹ * (c * x * c⁻¹) * (c * s), h''⟩ : H) = ⟨s⁻¹ * x * s, h⟩ := by
          apply Subtype.ext
          simp [hs']
        simpa [φ, ψ, h, h''] using congrArg f hsub.symm
      · have h'' : ¬ (s⁻¹ * c⁻¹ * (c * x * c⁻¹) * (c * s) ∈ H) := by
          simpa [hs'] using h
        simp [φ, ψ, h, h'']

instance (H : Subgroup G) (f : H → K) :
    IsClassFunction (Ind[H](f)) :=
  inducedClassFunction_isClassFunction H f

/-- Induction of subgroup functions is additive. -/
theorem inducedClassFunction_map_add (H : Subgroup G) (f₁ f₂ : H → K) :
    Ind[H](f₁ + f₂) = Ind[H](f₁) + Ind[H](f₂) := by
  ext g
  simp only [Subgroup.inducedClassFunction, Pi.add_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr with s
  by_cases h : s⁻¹ * g * s ∈ H <;> simp [h]

/-- Induction of subgroup functions commutes with scalar multiplication. -/
theorem inducedClassFunction_map_smul {S : Type*} [Monoid S] [DistribMulAction S K]
    [SMulCommClass S K K]
    (H : Subgroup G) (a : S) (f : H → K) :
    Ind[H](a • f) = a • Ind[H](f) := by
  ext g
  simp only [Subgroup.inducedClassFunction, Pi.smul_apply]
  rw [← mul_smul_comm, Finset.smul_sum]
  congr with s
  by_cases h : s⁻¹ * g * s ∈ H <;> simp [h]

/-- The canonical `K`-linear induction map from subgroup functions to `K`-valued class functions
on `G`. -/
def classFunctionInduction (H : Subgroup G) :
    (H → K) →ₗ[K] classFunctionSubmodule K G :=
  LinearMap.codRestrict
    (classFunctionSubmodule K G)
    { toFun := inducedClassFunction H
      map_add' := inducedClassFunction_map_add H
      map_smul' := inducedClassFunction_map_smul H }
    (fun f ↦ (mem_classFunctionSubmodule_iff K _).2 <| inducedClassFunction_isClassFunction H f)

/-- Evaluating the class-function induction map gives the induced class function. -/
@[simp] theorem classFunctionInduction_apply (H : Subgroup G) (f : H → K) :
    (H.classFunctionInduction f : G → K) = Ind[H](f) :=
  rfl

end

section

variable {G : Type u} [Group G] [Finite G]
variable {K : Type v} [Field K]
variable {W : Type (max w v)} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

open scoped SubgroupInduction

local instance : Fintype G := Fintype.ofFinite G
local instance (H : Subgroup G) : DecidablePred fun g : G ↦ g ∈ H := Classical.decPred _
attribute [local instance] Classical.propDecidable

/-- Helper for Proposition 7-7.2-1: when `ψ` is a class function on `H`, the induction summand at
`r * t` depends only on the left coset representative `r`. -/
lemma induced_class_function_summand_right_mul_eq
    (H : Subgroup G) (ψ : H → K) (hψ : IsClassFunction ψ) (x r : G) (t : H) :
    (if hrt : (r * t : G)⁻¹ * x * (r * t : G) ∈ H then
      ψ ⟨(r * t : G)⁻¹ * x * (r * t : G), hrt⟩
    else 0) =
      (if hr : r⁻¹ * x * r ∈ H then
        ψ ⟨r⁻¹ * x * r, hr⟩
      else 0) := by
  -- The summand only depends on the left coset because right multiplication by `t ∈ H`
  -- conjugates `r⁻¹ * x * r` inside `H`.
  by_cases hr : r⁻¹ * x * r ∈ H
  · have hrt : (r * t : G)⁻¹ * x * (r * t : G) ∈ H := by
      simpa [mul_assoc] using H.mul_mem (H.mul_mem (H.inv_mem t.2) hr) t.2
    have hconj :
        IsConj
          (⟨(r * t : G)⁻¹ * x * (r * t : G), hrt⟩ : H)
          ⟨r⁻¹ * x * r, hr⟩ := by
      refine isConj_iff.2 ?_
      refine ⟨t, ?_⟩
      apply Subtype.ext
      simp [mul_assoc]
    rw [dif_pos hrt, dif_pos hr]
    exact hψ.eq_of_isConj hconj
  · have hrt : ¬ (r * t : G)⁻¹ * x * (r * t : G) ∈ H := by
      intro hrt
      apply hr
      simpa [mul_assoc] using H.mul_mem (H.mul_mem t.2 hrt) (H.inv_mem t.2)
    rw [dif_neg hrt, dif_neg hr]

/-- Helper for Proposition 7-7.2-1: a left transversal rewrites the normalized full-group
definition of `Ind[H](ψ)` as the standard sum over representatives. -/
lemma induced_class_function_eq_sum_over_left_transversal
    (H : Subgroup G) [NeZero (Nat.card H : K)] (ψ : H → K) (hψ : IsClassFunction ψ)
    (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G)) (x : G) :
    Ind[H](ψ) x =
      ∑ r ∈ R,
        if hr : r⁻¹ * x * r ∈ H then
          ψ ⟨r⁻¹ * x * r, hr⟩
        else 0 := by
  classical
  let summand : G → K := fun s ↦
    if hs : s⁻¹ * x * s ∈ H then
      ψ ⟨s⁻¹ * x * s, hs⟩
    else 0
  have hsum :
      ∑ s : G, summand s = ∑ p : ↥(R : Set G) × H, summand (p.1 * p.2) := by
    -- The complement equivalence rewrites the full group sum as a double sum over representatives
    -- and subgroup elements.
    refine Fintype.sum_equiv hR.equiv summand (fun p ↦ summand (p.1 * p.2)) ?_
    intro s
    simpa using congrArg summand (hR.equiv_fst_mul_equiv_snd s).symm
  have hinner (r : ↥(R : Set G)) :
      ∑ t : H, summand ((r : G) * t) = (Nat.card H : K) * summand r := by
    have hconst (t : H) : summand ((r : G) * t) = summand r := by
      simpa [summand] using
        induced_class_function_summand_right_mul_eq
          (H := H) (ψ := ψ) hψ x (r : G) t
    calc
      ∑ t : H, summand ((r : G) * t) = ∑ _t : H, summand r := by
          simpa using
            (Fintype.sum_congr
              (fun t : H ↦ summand ((r : G) * t))
              (fun _t : H ↦ summand r)
              hconst)
      _ = (Nat.card H : K) * summand r := by
          simp [Nat.card_eq_fintype_card]
  have hcard : (Nat.card H : K) ≠ 0 := NeZero.ne _
  calc
    Ind[H](ψ) x = ((Nat.card H : K)⁻¹) * ∑ s : G, summand s := by
      simp [Subgroup.inducedClassFunction, summand]
    _ = ((Nat.card H : K)⁻¹) * ∑ p : ↥(R : Set G) × H, summand (p.1 * p.2) := by
      rw [hsum]
    _ = ((Nat.card H : K)⁻¹) *
          ∑ r : ↥(R : Set G), ∑ t : H, summand ((r : G) * t) := by
      rw [Fintype.sum_prod_type]
    _ = ((Nat.card H : K)⁻¹) *
          ∑ r : ↥(R : Set G), (Nat.card H : K) * summand r := by
      simpa using
        congrArg (((Nat.card H : K)⁻¹) * ·)
          (Fintype.sum_congr
            (fun r : ↥(R : Set G) ↦ ∑ t : H, summand ((r : G) * t))
            (fun r : ↥(R : Set G) ↦ (Nat.card H : K) * summand r)
            hinner)
    _ = ∑ r : ↥(R : Set G), summand r := by
      calc
        ((Nat.card H : K)⁻¹) * ∑ r : ↥(R : Set G), (Nat.card H : K) * summand r
            = ∑ r : ↥(R : Set G), ((Nat.card H : K)⁻¹) * ((Nat.card H : K) * summand r) := by
                simp [Finset.mul_sum]
        _ = ∑ r : ↥(R : Set G), summand r := by
              refine Fintype.sum_congr
                (fun r : ↥(R : Set G) ↦ ((Nat.card H : K)⁻¹) * ((Nat.card H : K) * summand r))
                (fun r : ↥(R : Set G) ↦ summand r)
                ?_
              intro r
              calc
                ((Nat.card H : K)⁻¹) * ((Nat.card H : K) * summand r)
                    = (((Nat.card H : K)⁻¹) * (Nat.card H : K)) * summand r := by
                        ac_rfl
                _ = summand r := by
                      rw [inv_mul_cancel₀ hcard, one_mul]
    _ = ∑ r ∈ R,
          if hr : r⁻¹ * x * r ∈ H then
            ψ ⟨r⁻¹ * x * r, hr⟩
          else 0 := by
      let attachSum : K := R.attach.sum fun r ↦ summand r
      have hattach :
          attachSum =
            ∑ r ∈ R,
              if hr : r⁻¹ * x * r ∈ H then
                ψ ⟨r⁻¹ * x * r, hr⟩
              else 0 := by
        dsimp [attachSum]
        rw [← Finset.sum_attach (s := R)
          (f := fun r : G ↦
            if hr : r⁻¹ * x * r ∈ H then
              ψ ⟨r⁻¹ * x * r, hr⟩
            else 0)]
      change attachSum = _
      exact hattach

/-- Helper for Proposition 7-7.2-1: the representative of `u * r` in the chosen left
transversal. -/
noncomputable def representative_target
    (H : Subgroup G) (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G))
    (u : G) (r : ↥(R : Set G)) : ↥(R : Set G) :=
  (hR.equiv (u * r)).fst

/-- Helper for Proposition 7-7.2-1: the subgroup element in the decomposition
`u * r = representative_target * representative_element`. -/
noncomputable def representative_element
    (H : Subgroup G) (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G))
    (u : G) (r : ↥(R : Set G)) : H :=
  (hR.equiv (u * r)).snd

/-- Helper for Proposition 7-7.2-1: a representative is fixed by multiplication by `u` exactly
when the corresponding conjugate lies in `H`. -/
lemma representative_target_eq_self_iff
    (H : Subgroup G) (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G))
    (u : G) (r : ↥(R : Set G)) :
    representative_target H R hR u r = r ↔ (r : G)⁻¹ * u * r ∈ H := by
  constructor
  · intro hr
    change (hR.equiv (u * r)).fst = r at hr
    have hdecomp := hR.equiv_fst_mul_equiv_snd (u * r)
    rw [hr] at hdecomp
    have ht :
        (((representative_element H R hR u r : H) : G)) = (r : G)⁻¹ * u * r := by
      change (((hR.equiv (u * r)).snd : H) : G) = (r : G)⁻¹ * u * r
      calc
        (((hR.equiv (u * r)).snd : H) : G)
            = (r : G)⁻¹ * ((r : G) * (((hR.equiv (u * r)).snd : H) : G)) := by
                simp
        _ = (r : G)⁻¹ * (u * r) := by
              rw [hdecomp]
        _ = (r : G)⁻¹ * u * r := by
              simp [mul_assoc]
    simpa [ht] using (representative_element H R hR u r).property
  · intro hur
    have hleft : LeftCosetEquivalence H (u * r : G) (r : G) := by
      simpa [LeftCosetEquivalence, leftCoset_eq_iff, mul_assoc] using H.inv_mem hur
    have hfst :
        (hR.equiv (u * r)).fst = (hR.equiv (r : G)).fst :=
      (hR.equiv_fst_eq_iff_leftCosetEquivalence).2 hleft
    have h1H : (1 : G) ∈ H := by
      simp
    change (hR.equiv (u * r)).fst = r
    exact hfst.trans (hR.equiv_fst_eq_self_of_mem_of_one_mem h1H r.property)

/-- Helper for Proposition 7-7.2-1: if `u` fixes the representative `r`, then the subgroup term in
the complement decomposition is exactly `r⁻¹ * u * r`. -/
lemma representative_element_eq_conj_of_target_eq_self
    (H : Subgroup G) (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G))
    (u : G) (r : ↥(R : Set G))
    (hr : representative_target H R hR u r = r) :
    representative_element H R hR u r =
      ⟨(r : G)⁻¹ * u * r, (representative_target_eq_self_iff H R hR u r).1 hr⟩ := by
  ext
  -- Once the representative is fixed, the complement decomposition identifies the subgroup factor.
  change (hR.equiv (u * r)).fst = r at hr
  have hdecomp := hR.equiv_fst_mul_equiv_snd (u * r)
  rw [hr] at hdecomp
  change (((hR.equiv (u * r)).snd : H) : G) = (r : G)⁻¹ * u * r
  calc
    (((hR.equiv (u * r)).snd : H) : G)
        = (r : G)⁻¹ * ((r : G) * (((hR.equiv (u * r)).snd : H) : G)) := by
            simp
    _ = (r : G)⁻¹ * (u * r) := by
          rw [hdecomp]
    _ = (r : G)⁻¹ * u * r := by
          simp [mul_assoc]

/-- Helper for Proposition 7-7.2-1: the inverse translate of the target representative decomposes
as the original representative times the inverse subgroup element from `u * r = r_u * t_u`. -/
lemma representative_inverse_target_decomposition
    (H : Subgroup G) (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G))
    (u : G) (r : ↥(R : Set G)) :
    hR.equiv (u⁻¹ * representative_target H R hR u r) =
      (r, (representative_element H R hR u r)⁻¹) := by
  -- Rewriting the complement decomposition of `u * r` yields the inverse translate directly.
  apply hR.equiv.symm.injective
  simp only [Subgroup.IsComplement.equiv_symm_apply]
  rw [hR.equiv_fst_mul_equiv_snd]
  have hdecomp :
      (representative_target H R hR u r : G) *
          (((representative_element H R hR u r : H) : G)) =
        u * r :=
    hR.equiv_fst_mul_equiv_snd (u * r)
  calc
    u⁻¹ * representative_target H R hR u r
        = u⁻¹ * (representative_target H R hR u r *
            (((representative_element H R hR u r : H) : G) *
              (((representative_element H R hR u r)⁻¹ : H) : G))) := by
            simp
    _ = u⁻¹ * (((representative_target H R hR u r : G) *
            (((representative_element H R hR u r : H) : G))) *
              (((representative_element H R hR u r)⁻¹ : H) : G)) := by
          simp [mul_assoc]
    _ = u⁻¹ * ((u * r) * (((representative_element H R hR u r)⁻¹ : H) : G)) := by
          rw [hdecomp]
    _ = (r : G) * (((representative_element H R hR u r)⁻¹ : H) : G) := by
          simp [mul_assoc]

/-- Helper for Proposition 7-7.2-1: the representative in the decomposition of `u⁻¹ * s` is `r`
exactly when `s` is the target representative attached to `u * r`. -/
lemma representative_inverse_fst_eq_iff
    (H : Subgroup G) (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G))
    (u : G) (r s : ↥(R : Set G)) :
    (hR.equiv (u⁻¹ * s : G)).fst = r ↔ s = representative_target H R hR u r := by
  constructor
  · intro hs
    have hdecomp := hR.equiv_fst_mul_equiv_snd (u⁻¹ * s : G)
    rw [hs] at hdecomp
    have hs_eq :
        (s : G) = u * r * (((hR.equiv (u⁻¹ * s : G)).snd : H) : G) := by
      have hs_eq' :
          u * ((r : G) * (((hR.equiv (u⁻¹ * s : G)).snd : H) : G)) = (s : G) := by
        simpa [mul_assoc] using congrArg (fun x : G ↦ u * x) hdecomp
      simpa [mul_assoc] using hs_eq'.symm
    have hs_mem : (s : G)⁻¹ * (u * r) ∈ H := by
      rw [hs_eq]
      simp [mul_assoc]
    have hleft : LeftCosetEquivalence H (s : G) (u * r : G) := by
      simpa [LeftCosetEquivalence, leftCoset_eq_iff] using hs_mem
    have hfst :
        (hR.equiv (s : G)).fst = (hR.equiv (u * r : G)).fst :=
      (hR.equiv_fst_eq_iff_leftCosetEquivalence).2 hleft
    have h1H : (1 : G) ∈ H := by
      simp
    have hs_self :
        (hR.equiv (s : G)).fst = s :=
      hR.equiv_fst_eq_self_of_mem_of_one_mem h1H s.property
    exact hs_self.symm.trans hfst
  · intro hs
    subst s
    simpa using congrArg Prod.fst (representative_inverse_target_decomposition H R hR u r)

/-- Helper for Proposition 7-7.2-1: the coinduced function defined from representative coordinates
really lies in the coinduced model. -/
theorem coind_representative_preimage_mem
    (H : Subgroup G) (θ : Representation K H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G)) (ξ : ↥(R : Set G) → W) :
    (fun g ↦
      let x := hR.equiv g⁻¹
      θ x.2⁻¹ (ξ x.1)) ∈ Representation.coindV H.subtype θ := by
  intro h g
  -- Move the subgroup factor in the complement decomposition into the coefficient of `θ`.
  simpa [mul_assoc, ← Module.End.mul_apply, ← map_mul] using
    congrArg
      (fun x : ↥(R : Set G) × H ↦ θ x.2⁻¹ (ξ x.1))
      (hR.equiv_mul_right g⁻¹ h⁻¹)

/-- Helper for Proposition 7-7.2-1: reconstruct a coinduced function from its values on inverse
representatives. -/
noncomputable def coind_representative_preimage
    (H : Subgroup G) (θ : Representation K H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G)) (ξ : ↥(R : Set G) → W) :
    Representation.coindV H.subtype θ :=
  ⟨fun g ↦
      let x := hR.equiv g⁻¹
      θ x.2⁻¹ (ξ x.1),
    coind_representative_preimage_mem H θ R hR ξ⟩

/-- Helper for Proposition 7-7.2-1: evaluation at inverse representatives is additive. -/
theorem coind_representative_equiv_map_add
    (H : Subgroup G) (θ : Representation K H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G))
    (f g : Representation.coindV H.subtype θ) :
    (fun r : ↥(R : Set G) ↦ (f + g).1 ((r : G)⁻¹)) =
      (fun r : ↥(R : Set G) ↦ f.1 ((r : G)⁻¹) + g.1 ((r : G)⁻¹)) := by
  ext r
  simp

/-- Helper for Proposition 7-7.2-1: evaluation at inverse representatives commutes with scalar
multiplication. -/
theorem coind_representative_equiv_map_smul
    (H : Subgroup G) (θ : Representation K H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G))
    (a : K) (f : Representation.coindV H.subtype θ) :
    (fun r : ↥(R : Set G) ↦ (a • f).1 ((r : G)⁻¹)) =
      (fun r : ↥(R : Set G) ↦ a • f.1 ((r : G)⁻¹)) := by
  ext r
  simp

/-- Helper for Proposition 7-7.2-1: reconstructing a coinduced function from its representative
coordinates is inverse to evaluation on inverse representatives. -/
theorem coind_representative_equiv_left_inv
    (H : Subgroup G) (θ : Representation K H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G))
    (f : Representation.coindV H.subtype θ) :
    coind_representative_preimage H θ R hR (fun r ↦ f.1 ((r : G)⁻¹)) = f := by
  ext g
  let x := hR.equiv g⁻¹
  have hg : ((x.2 : H) : G)⁻¹ * ((x.1 : (R : Set G)) : G)⁻¹ = g := by
    simpa [x, mul_inv_rev] using congrArg Inv.inv (hR.equiv_fst_mul_equiv_snd g⁻¹)
  -- The complement decomposition of `g⁻¹` rewrites `g` into the coinduction relation.
  change θ x.2⁻¹ (f.1 (((x.1 : ↥(R : Set G)) : G)⁻¹)) = f.1 g
  simpa [hg] using
    ((f.2 x.2⁻¹ (((x.1 : ↥(R : Set G)) : G)⁻¹)).symm)

/-- Helper for Proposition 7-7.2-1: the chosen coordinates recover the original function on the
representative set. -/
theorem coind_representative_equiv_right_inv
    (H : Subgroup G) (θ : Representation K H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G))
    (ξ : ↥(R : Set G) → W) :
    (fun r : ↥(R : Set G) ↦ (coind_representative_preimage H θ R hR ξ).1 ((r : G)⁻¹)) = ξ := by
  ext r
  have h1H : (1 : G) ∈ H := by
    simp
  have hfst :
      (hR.equiv (r : G)).fst = r :=
    hR.equiv_fst_eq_self_of_mem_of_one_mem h1H r.property
  have hsnd :
      (hR.equiv (r : G)).snd = (1 : H) :=
    hR.equiv_snd_eq_one_of_mem_of_one_mem h1H r.property
  -- At an inverse representative the complement decomposition is the trivial one `r * 1`.
  dsimp [coind_representative_preimage]
  simp [hfst, hsnd]

/-- Helper for Proposition 7-7.2-1: evaluating a coinduced function on inverse representatives
identifies the coinduced model with `W`-valued functions on the representative set. -/
noncomputable def coind_representative_equiv
    (H : Subgroup G) (θ : Representation K H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G)) :
    Representation.coindV H.subtype θ ≃ₗ[K] (↥(R : Set G) → W) :=
  { toFun := fun f r ↦ f.1 ((r : G)⁻¹)
    invFun := coind_representative_preimage H θ R hR
    map_add' := coind_representative_equiv_map_add H θ R hR
    map_smul' := coind_representative_equiv_map_smul H θ R hR
    left_inv := coind_representative_equiv_left_inv H θ R hR
    right_inv := coind_representative_equiv_right_inv H θ R hR }

/-- Helper for Proposition 7-7.2-1: after transporting the coinduced action to representative
coordinates, a basis vector at `r` moves to the target representative with the subgroup-twisted
coefficient. -/
lemma coind_representative_equiv_action_single
    (H : Subgroup G) (θ : Representation K H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G)) (u : G)
    [DecidableEq ↥(R : Set G)]
    (r : ↥(R : Set G)) (w : W) :
    let T_u : (↥(R : Set G) → W) →ₗ[K] (↥(R : Set G) → W) :=
      (coind_representative_equiv H θ R hR).conj ((θ.coind H.subtype) u)
    T_u (Pi.single r w) =
      Pi.single (representative_target H R hR u r)
        (θ (representative_element H R hR u r) w) := by
  classical
  -- Evaluate the conjugated coinduced action at each representative coordinate.
  ext s
  simp only [LinearEquiv.conj_apply_apply, Pi.single_apply]
  show
    (((θ.coind H.subtype) u) ((coind_representative_equiv H θ R hR).symm (Pi.single r w))).1
        ((s : G)⁻¹) =
      if s = representative_target H R hR u r then
        θ (representative_element H R hR u r) w
      else 0
  change
    ((coind_representative_equiv H θ R hR).symm (Pi.single r w)).1 ((s : G)⁻¹ * u) =
      if s = representative_target H R hR u r then
        θ (representative_element H R hR u r) w
      else 0
  by_cases hs : s = representative_target H R hR u r
  · subst s
    have hpair :
        hR.equiv ((((representative_target H R hR u r : G)⁻¹) * u)⁻¹) =
          (r, (representative_element H R hR u r)⁻¹) := by
      simpa [representative_target, representative_element, mul_inv_rev] using
        representative_inverse_target_decomposition H R hR u r
    rw [if_pos rfl]
    dsimp [coind_representative_equiv]
    change
      (let x := hR.equiv ((((representative_target H R hR u r : G)⁻¹) * u)⁻¹)
        ; θ x.2⁻¹ (((Pi.single r w : ↥(R : Set G) → W) x.1))) =
      θ (representative_element H R hR u r) w
    rw [hpair]
    simp [representative_target, representative_element]
  · rw [if_neg hs]
    have hfst_ne : (hR.equiv (u⁻¹ * s : G)).fst ≠ r := by
      intro hfst
      exact hs ((representative_inverse_fst_eq_iff H R hR u r s).1 hfst)
    dsimp [coind_representative_equiv]
    change
      (let x := hR.equiv ((((s : G)⁻¹) * u)⁻¹)
        ; θ x.2⁻¹ (((Pi.single r w : ↥(R : Set G) → W) x.1))) = 0
    simp [coind_representative_preimage, hfst_ne, mul_inv_rev]

/-- Helper for Proposition 7-7.2-1: each diagonal entry of the transported coinduced action is
zero off the fixed-point locus, and on a fixed representative it is the matching diagonal entry of
the subgroup action. -/
lemma representative_action_diag_entry
    (H : Subgroup G) (θ : Representation K H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G)) (u : G)
    [DecidableEq ↥(R : Set G)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bW : Module.Basis ι K W) (r : ↥(R : Set G)) (i : ι) :
    let T_u : (↥(R : Set G) → W) →ₗ[K] (↥(R : Set G) → W) :=
      (coind_representative_equiv H θ R hR).conj ((θ.coind H.subtype) u)
    LinearMap.toMatrix (Pi.basis fun _ ↦ bW) (Pi.basis fun _ ↦ bW) T_u ⟨r, i⟩ ⟨r, i⟩ =
      if hfix : representative_target H R hR u r = r then
        LinearMap.toMatrix bW bW (θ (representative_element H R hR u r)) i i
      else 0 := by
  classical
  let T_u : (↥(R : Set G) → W) →ₗ[K] (↥(R : Set G) → W) :=
    (coind_representative_equiv H θ R hR).conj ((θ.coind H.subtype) u)
  -- The diagonal entry is the `⟨r,i⟩`-coordinate of the image of the corresponding basis vector.
  change LinearMap.toMatrix (Pi.basis fun _ ↦ bW) (Pi.basis fun _ ↦ bW) T_u ⟨r, i⟩ ⟨r, i⟩ = _
  rw [LinearMap.toMatrix_apply]
  rw [Pi.basis_apply]
  have haction :
      T_u (Pi.single r (bW i)) =
        Pi.single (representative_target H R hR u r)
          (θ (representative_element H R hR u r) (bW i)) := by
    simpa [T_u] using coind_representative_equiv_action_single H θ R hR u r (bW i)
  rw [haction]
  rw [Pi.basis_repr]
  by_cases hfix : representative_target H R hR u r = r
  · rw [hfix]
    simp [LinearMap.toMatrix_apply]
  · simpa [hfix]

/-- Helper for Proposition 7-7.2-1: the trace of the transported coinduced action is the sum of
the subgroup characters over the representatives fixed by `u`. -/
lemma trace_representative_action_eq_sum
    (H : Subgroup G) (θ : Representation K H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G)) (u : G)
    [DecidableEq ↥(R : Set G)] :
    let T_u : (↥(R : Set G) → W) →ₗ[K] (↥(R : Set G) → W) :=
      (coind_representative_equiv H θ R hR).conj ((θ.coind H.subtype) u)
    LinearMap.trace K (↥(R : Set G) → W) T_u =
      ∑ r : ↥(R : Set G),
        if hfix : representative_target H R hR u r = r then
          θ.character (representative_element H R hR u r)
        else 0 := by
  classical
  let T_u : (↥(R : Set G) → W) →ₗ[K] (↥(R : Set G) → W) :=
    (coind_representative_equiv H θ R hR).conj ((θ.coind H.subtype) u)
  let bW := Module.Free.chooseBasis K W
  -- The product basis turns the global trace into a sum of diagonal blocks indexed by
  -- representatives and basis vectors of `W`.
  change LinearMap.trace K (↥(R : Set G) → W) T_u =
      ∑ r : ↥(R : Set G),
        if hfix : representative_target H R hR u r = r then
          θ.character (representative_element H R hR u r)
        else 0
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basis fun _ ↦ bW) T_u]
  rw [Matrix.trace, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  simp_rw [Matrix.diag_apply]
  refine Finset.sum_congr rfl ?_
  intro r _
  by_cases hfix : representative_target H R hR u r = r
  · simp [hfix]
    have hdiag :
        ∀ i,
          LinearMap.toMatrix (Pi.basis fun _ ↦ bW) (Pi.basis fun _ ↦ bW) T_u ⟨r, i⟩ ⟨r, i⟩ =
            LinearMap.toMatrix bW bW (θ (representative_element H R hR u r)) i i := by
      intro i
      simpa [T_u, hfix] using
        representative_action_diag_entry (H := H) (θ := θ) (R := R) (hR := hR) (u := u)
          (bW := bW) (r := r) (i := i)
    calc
      ∑ s,
          LinearMap.toMatrix (Pi.basis fun _ ↦ bW) (Pi.basis fun _ ↦ bW) T_u ⟨r, s⟩ ⟨r, s⟩
          =
          ∑ s, LinearMap.toMatrix bW bW (θ (representative_element H R hR u r)) s s := by
            refine Finset.sum_congr rfl ?_
            intro s _
            exact hdiag s
      _ = θ.character (representative_element H R hR u r) := by
            simpa [Representation.character, Matrix.trace] using
              (LinearMap.trace_eq_matrix_trace K bW
                (θ (representative_element H R hR u r))).symm
  · simp [hfix]
    have hdiag :
        ∀ i,
          LinearMap.toMatrix (Pi.basis fun _ ↦ bW) (Pi.basis fun _ ↦ bW) T_u ⟨r, i⟩ ⟨r, i⟩ = 0 := by
      intro i
      simpa [T_u, hfix] using
        representative_action_diag_entry (H := H) (θ := θ) (R := R) (hR := hR) (u := u)
          (bW := bW) (r := r) (i := i)
    calc
      ∑ s,
          LinearMap.toMatrix (Pi.basis fun _ ↦ bW) (Pi.basis fun _ ↦ bW) T_u ⟨r, s⟩ ⟨r, s⟩
          = ∑ s, (0 : K) := by
              refine Finset.sum_congr rfl ?_
              intro s _
              exact hdiag s
      _ = 0 := by
            simp

/-- Helper for Proposition 7-7.2-1: the subtype-indexed fixed-representative sum is exactly the
textbook `Finset` sum over `r ∈ R` with the condition `r⁻¹ * u * r ∈ H`. -/
lemma representative_subtype_sum_eq_finset_sum
    (H : Subgroup G) (θ : Representation K H W) (R : Finset G)
    (hR : IsComplement (R : Set G) (H : Set G)) (u : G)
    [DecidableEq ↥(R : Set G)] :
    (∑ r : ↥(R : Set G),
      if hfix : representative_target H R hR u r = r then
        θ.character (representative_element H R hR u r)
      else 0) =
      ∑ r ∈ R,
        if hur : r⁻¹ * u * r ∈ H then
          θ.character ⟨r⁻¹ * u * r, hur⟩
        else 0 := by
  classical
  -- Rewrite the subtype sum as the corresponding `Finset.attach` sum, then use the fixed-point
  -- criterion and identify the subgroup term with the expected conjugate.
  let attachSum : K := R.attach.sum fun r ↦
      if hfix : representative_target H R hR u r = r then
        θ.character (representative_element H R hR u r)
      else 0
  have hattach :
      attachSum =
        ∑ r ∈ R,
          if hur : r⁻¹ * u * r ∈ H then
            θ.character ⟨r⁻¹ * u * r, hur⟩
          else 0 := by
    dsimp [attachSum]
    rw [← Finset.sum_attach (s := R)
      (f := fun r : G ↦
        if hur : r⁻¹ * u * r ∈ H then
          θ.character ⟨r⁻¹ * u * r, hur⟩
        else 0)]
    refine Finset.sum_congr rfl ?_
    intro r hr
    by_cases hfix : representative_target H R hR u r = r
    · have hur : (r : G)⁻¹ * u * r ∈ H :=
        (representative_target_eq_self_iff H R hR u r).1 hfix
      have hchar :
          θ.character (representative_element H R hR u r) =
            θ.character ⟨(r : G)⁻¹ * u * r, hur⟩ := by
        simpa using congrArg θ.character
          (representative_element_eq_conj_of_target_eq_self H R hR u r hfix)
      simpa [hfix, hur] using hchar
    · have hur : ¬ ((r : G)⁻¹ * u * r ∈ H) := by
        intro hur
        exact hfix ((representative_target_eq_self_iff H R hR u r).2 hur)
      simpa [hfix, hur]
  change attachSum = ∑ r ∈ R, if hur : r⁻¹ * u * r ∈ H then θ.character ⟨r⁻¹ * u * r, hur⟩ else 0
  exact hattach

/-- Helper for Proposition 7-7.2-1: the character of the induced representation should be computed
through the same left-transversal representative sum as `Ind[H](θ.character)`. -/
lemma induced_character_eq_sum_over_left_transversal
    (H : Subgroup G) (θ : Representation K H W)
    (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G)) (u : G) :
    (Representation.ind H.subtype θ).character u =
      ∑ r ∈ R,
        if hur : r⁻¹ * u * r ∈ H then
          θ.character ⟨r⁻¹ * u * r, hur⟩
        else 0 := by
  classical
  letI : H.FiniteIndex := (hR.finite_left_iff).1 inferInstance
  calc
    (Representation.ind H.subtype θ).character u = (θ.coind H.subtype).character u := by
      -- Finite index identifies the induced and coinduced character values.
      simpa [Rep.of_ρ] using congrFun
        (Representation.char_iso
          (Representation.equivOfIso
            (Rep.indCoindIso (k := K) (S := H) (A := Rep.of θ)))) u
    _ = ∑ r : ↥(R : Set G),
          if hfix : representative_target H R hR u r = r then
            θ.character (representative_element H R hR u r)
          else 0 := by
        -- Rewrite the raw coinduced trace through representative coordinates.
        rw [Representation.character]
        have hcoord :
            LinearMap.trace K ↥(Representation.coindV H.subtype θ) ((θ.coind H.subtype) u)
              =
              LinearMap.trace K (↥(R : Set G) → W)
                ((coind_representative_equiv H θ R hR).conj ((θ.coind H.subtype) u)) := by
          simpa using
            (LinearMap.trace_conj' ((θ.coind H.subtype) u)
              (coind_representative_equiv H θ R hR)).symm
        exact hcoord.trans (trace_representative_action_eq_sum H θ R hR u)
    _ = ∑ r ∈ R,
          if hur : r⁻¹ * u * r ∈ H then
            θ.character ⟨r⁻¹ * u * r, hur⟩
          else 0 := by
        -- Translate the fixed-representative condition back into the textbook conjugacy condition.
        simpa using representative_subtype_sum_eq_finset_sum (H := H) (θ := θ) (R := R) (hR := hR) (u := u)

-- Proof sketch: apply the explicit induced-character formula for `Representation.ind H.subtype θ`
-- and compare it term-by-term with the definition of `Ind[H](θ.character)`. Because
-- `Ind[H](f)` is normalized by `((Nat.card H : K)⁻¹)`, this bridge to induced characters is valid
-- whenever `(Nat.card H : K)` is nonzero.
/-- Proposition 7-7.2-1 (2): if `f` is the character of a finite-dimensional `K`-representation
`θ` of `H`, then the induced function `Ind(f)` is the character of the induced representation
`Ind(θ)` of `G`. -/
theorem inducedClassFunction_eq_character_ind
    (H : Subgroup G) [NeZero (Nat.card H : K)] (θ : Representation K H W) :
    Ind[H](θ.character) = (Representation.ind H.subtype θ).character := by
  classical
  obtain ⟨S, hS, h1S⟩ := H.exists_isComplement_left (1 : G)
  let R : Finset G := (Set.toFinite S).toFinset
  have hR : IsComplement (R : Set G) (H : Set G) := by
    simpa [R] using hS
  have hθ : IsClassFunction θ.character := by
    refine ⟨?_⟩
    intro x y hxy
    rcases isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.mp hxy) with ⟨a, rfl⟩
    exact (θ.char_conj x a).symm
  ext x
  -- Both sides reduce to the same left-transversal sum over the representatives in `R`.
  rw [induced_class_function_eq_sum_over_left_transversal
    (H := H) (ψ := θ.character) hθ (R := R) (hR := hR) (x := x)]
  rw [induced_character_eq_sum_over_left_transversal
    (H := H) (θ := θ) (R := R) (hR := hR) (u := x)]

end

end Subgroup
