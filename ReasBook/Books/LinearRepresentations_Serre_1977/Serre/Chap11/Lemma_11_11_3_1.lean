import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap02.Remark_2_2_1_2
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise SubgroupInduction

noncomputable section

universe u v

section

variable {G : Type u} [Group G]
variable {A : Type v} [AddCommMonoid A]

attribute [local instance] Classical.propDecidable

private def leftCosetInductionSummand
    (H : Subgroup G) (ψ : H → A) (x a : G) : A :=
  if ha : a⁻¹ * x * a ∈ H then ψ ⟨a⁻¹ * x * a, ha⟩ else 0

-- Proof sketch: if `a` and `b` lie in the same left coset of `H`, then `b = a * h` for some
-- `h ∈ H`. Hence `b⁻¹ * x * b` is `H`-conjugate to `a⁻¹ * x * a`, so a class function on `H`
-- takes the same value on both representatives; the zero branch is preserved because membership in
-- `H` is stable under conjugation by its own elements.
/-- The standard induction summand attached to a left coset of `H` depends only on that coset when
`ψ` is a class function on `H`. -/
private theorem inducedClassFunctionLeftCosetSummand_wellDefined
    (H : Subgroup G) (ψ : H → A) (hψ : IsClassFunction ψ) (x a b : G)
    (hab : QuotientGroup.leftRel H a b) :
    leftCosetInductionSummand H ψ x a =
      leftCosetInductionSummand H ψ x b := by
  rw [QuotientGroup.leftRel_apply] at hab
  let t : H := ⟨a⁻¹ * b, hab⟩
  have hb : (a * t : G) = b := by
    change a * (a⁻¹ * b) = b
    group
  -- Replace `b` by `a * t`; right multiplication by `t ∈ H` only conjugates inside `H`.
  rw [← hb]
  by_cases ha : a⁻¹ * x * a ∈ H
  · have hat : (a * t : G)⁻¹ * x * (a * t : G) ∈ H := by
      simpa [mul_assoc] using H.mul_mem (H.mul_mem (H.inv_mem t.2) ha) t.2
    have hconj :
        IsConj
          (⟨(a * t : G)⁻¹ * x * (a * t : G), hat⟩ : H)
          ⟨a⁻¹ * x * a, ha⟩ := by
      refine isConj_iff.2 ?_
      refine ⟨t, ?_⟩
      apply Subtype.ext
      simp [mul_assoc]
    -- On the nonzero branch, `ψ` takes the same value on these `H`-conjugate elements.
    rw [leftCosetInductionSummand, leftCosetInductionSummand, dif_pos ha, dif_pos hat]
    exact hψ.eq_of_isConj hconj.symm
  · have hat : ¬ (a * t : G)⁻¹ * x * (a * t : G) ∈ H := by
      intro hat
      apply ha
      simpa [mul_assoc] using H.mul_mem (H.mul_mem t.2 hat) (H.inv_mem t.2)
    -- The zero branch is preserved because conjugation by an element of `H` preserves membership.
    rw [leftCosetInductionSummand, leftCosetInductionSummand, dif_neg ha, dif_neg hat]

end

namespace Subgroup

section

variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [AddCommMonoid A]

/-- Internal left-coset sum computing induction from `H` to `G`. -/
private def leftCosetInductionSum
    (H : Subgroup G) (ψ : H → A) (hψ : IsClassFunction ψ) (x : G) : A :=
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let _ : DecidablePred fun a : G ↦ a⁻¹ * x * a ∈ H := Classical.decPred _
  ∑ q : G ⧸ H,
    Quotient.lift
      (leftCosetInductionSummand H ψ x)
      (fun a b hab ↦ inducedClassFunctionLeftCosetSummand_wellDefined H ψ hψ x a b hab) q

section FieldBridge

variable {K : Type v} [Field K]

-- Source/core/bridge triage:
-- * source-facing: `leftCosetInductionSum` is Serre's quotient-indexed left-coset formula.
-- * core/canonical: `Ind[H](ψ)` is the owner declaration for induced class functions.
-- * bridge/view: this theorem identifies the source-facing quotient sum with the canonical owner.
-- Proof sketch: partition the defining sum of `Ind[H](ψ) x` over the left cosets of `H`. The
-- summand is constant on each coset by `inducedClassFunctionLeftCosetSummand_wellDefined`, so the
-- group sum is `|H|` times the quotient sum, and the prefactor `(Nat.card H : K)⁻¹` cancels once
-- the normalization scalar is nonzero.
/-- Internal bridge from the canonical induced class function to the left-coset formula. -/
private theorem inducedClassFunction_eq_leftCosetInductionSum
    (H : Subgroup G) [NeZero (Nat.card H : K)] (ψ : H → K) (hψ : IsClassFunction ψ) (x : G) :
    Ind[H](ψ) x = leftCosetInductionSum H ψ hψ x := by
  classical
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let R : Finset G := Finset.univ.image (fun q : G ⧸ H ↦ q.out)
  have hR :
      Subgroup.IsComplement (R : Set G) (H : Set G) := by
    -- The chosen `Quotient.out` representatives form a left transversal for `H`.
    rw [show (R : Set G) = Set.range (Quotient.out : G ⧸ H → G) by
      ext g
      constructor
      · intro hg
        rcases Finset.mem_image.mp hg with ⟨q, -, rfl⟩
        exact ⟨q, rfl⟩
      · rintro ⟨q, rfl⟩
        exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩]
    exact Subgroup.isComplement_range_left fun q ↦ Quotient.out_eq' q
  have hsum :
      leftCosetInductionSum H ψ hψ x =
        ∑ r ∈ R,
          if hr : r⁻¹ * x * r ∈ H then
            ψ ⟨r⁻¹ * x * r, hr⟩
          else 0 := by
    -- Rewrite the quotient sum by summing over the chosen representatives `q.out`.
    unfold leftCosetInductionSum
    simp only
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro q hq
      calc
        Quotient.lift (leftCosetInductionSummand H ψ x)
            (fun a b hab ↦ inducedClassFunctionLeftCosetSummand_wellDefined H ψ hψ x a b hab) q
            =
            Quotient.lift (leftCosetInductionSummand H ψ x)
              (fun a b hab ↦ inducedClassFunctionLeftCosetSummand_wellDefined H ψ hψ x a b hab)
              (Quotient.mk'' q.out) := by rw [Quotient.out_eq' q]
        _ = leftCosetInductionSummand H ψ x q.out := rfl
    · intro q₁ _ q₂ _ hq
      calc
        q₁ = (q₁.out : G ⧸ H) := (Quotient.out_eq' q₁).symm
        _ = (q₂.out : G ⧸ H) := by simp [hq]
        _ = q₂ := Quotient.out_eq' q₂
  -- The canonical induced value and the quotient-indexed sum now match the same transversal sum.
  rw [Subgroup.induced_class_function_eq_sum_over_left_transversal
    (H := H) (ψ := ψ) hψ R hR x]
  exact hsum.symm

end FieldBridge

section

variable {p : ℕ} [Fact p.Prime]

-- Source/core/bridge triage:
-- * source-facing: Serre's congruence for the value of the induced character at `x`.
-- * core/canonical: `Ind[H](fun h ↦ (ψ h : ℂ)) x`.
-- * bridge/view: `leftCosetInductionSum` from above remains only the quotient-indexed formula for
--   computing that owner.
--
-- Primitive data: the integral-coefficient class function `ψ : H → integralClosure ℤ ℂ`.
-- Derived API: the induced-value congruence below, expressed in the canonical coefficient ring
-- `integralClosure ℤ ℂ` where modulo-`p` membership is meaningful, together with the comparison to
-- the canonical owner `Ind[H](fun h ↦ (ψ h : ℂ)) x`.
--
-- Proof sketch: compare `Ind[H](fun h ↦ (ψ h : ℂ)) x` with the source-facing left-coset sum of
-- `ψ` and use that the latter is already an element of `integralClosure ℤ ℂ`. Rewrite the induced
-- value at `x` as the sum over the `H`-conjugacy classes inside the `G`-conjugacy class of `x`.
-- Each coefficient is the index of `H ∩ Z(y)` in `Z(y)`, and if one coefficient were not divisible
-- by `p`, the corresponding `H`-class would contain a conjugate of the associated `p`-elementary
-- subgroup of `x`, contradicting the hypothesis on `H`.
/-- Internal coercion bridge from the integral left-coset formula to the complex-valued one. -/
private theorem coe_leftCosetInductionSum
    (H : Subgroup G) (ψ : H → integralClosure ℤ ℂ) (hψ : IsClassFunction ψ) (x : G) :
    ↑((leftCosetInductionSum H ψ hψ x : integralClosure ℤ ℂ)) =
      leftCosetInductionSum H (fun h ↦ (ψ h : ℂ))
        (hψ.comp ((↑) : integralClosure ℤ ℂ → ℂ))
        x := by
  -- Coercion commutes with the quotient-indexed sum and with each summand.
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let f : integralClosure ℤ ℂ →+* ℂ := algebraMap (integralClosure ℤ ℂ) ℂ
  unfold leftCosetInductionSum
  calc
    ↑(∑ q : G ⧸ H,
        Quotient.lift
          (leftCosetInductionSummand H ψ x)
          (fun a b hab ↦
            inducedClassFunctionLeftCosetSummand_wellDefined H ψ hψ x a b hab)
          q)
        =
        f (∑ q : G ⧸ H,
          Quotient.lift
            (leftCosetInductionSummand H ψ x)
            (fun a b hab ↦
              inducedClassFunctionLeftCosetSummand_wellDefined H ψ hψ x a b hab)
            q) := rfl
    _ =
        ∑ q : G ⧸ H,
          f (Quotient.lift
            (leftCosetInductionSummand H ψ x)
            (fun a b hab ↦
              inducedClassFunctionLeftCosetSummand_wellDefined H ψ hψ x a b hab)
            q) := by
          rw [map_sum]
    _ =
        ∑ q : G ⧸ H,
          Quotient.lift
            (leftCosetInductionSummand H (fun h ↦ (ψ h : ℂ)) x)
            (fun a b hab ↦
              inducedClassFunctionLeftCosetSummand_wellDefined H
                (fun h ↦ (ψ h : ℂ))
                (hψ.comp ((↑) : integralClosure ℤ ℂ → ℂ)) x a b hab)
            q := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          have hlift :
              Quotient.lift (leftCosetInductionSummand H ψ x)
                (fun a b hab ↦ inducedClassFunctionLeftCosetSummand_wellDefined H ψ hψ x a b hab)
                q =
                leftCosetInductionSummand H ψ x q.out := by
            calc
              Quotient.lift (leftCosetInductionSummand H ψ x)
                  (fun a b hab ↦ inducedClassFunctionLeftCosetSummand_wellDefined H ψ hψ x a b hab)
                  q
                  =
                  Quotient.lift (leftCosetInductionSummand H ψ x)
                    (fun a b hab ↦
                      inducedClassFunctionLeftCosetSummand_wellDefined H ψ hψ x a b hab)
                    (Quotient.mk'' q.out) := by rw [Quotient.out_eq' q]
              _ = leftCosetInductionSummand H ψ x q.out := rfl
          have hqout :
              f (Quotient.lift (leftCosetInductionSummand H ψ x)
                (fun a b hab ↦ inducedClassFunctionLeftCosetSummand_wellDefined H ψ hψ x a b hab)
                q) =
                leftCosetInductionSummand H (fun h ↦ (ψ h : ℂ)) x q.out := by
            calc
              f (Quotient.lift (leftCosetInductionSummand H ψ x)
                  (fun a b hab ↦ inducedClassFunctionLeftCosetSummand_wellDefined H ψ hψ x a b hab)
                  q)
                  = f (leftCosetInductionSummand H ψ x q.out) := by rw [hlift]
              _ = leftCosetInductionSummand H (fun h ↦ (ψ h : ℂ)) x q.out := by
                    by_cases ha : q.out⁻¹ * x * q.out ∈ H
                    · simp [f, leftCosetInductionSummand, ha]
                    · simp [f, leftCosetInductionSummand, ha]
          calc
            f (Quotient.lift (leftCosetInductionSummand H ψ x)
              (fun a b hab ↦ inducedClassFunctionLeftCosetSummand_wellDefined H ψ hψ x a b hab) q)
                = leftCosetInductionSummand H (fun h ↦ (ψ h : ℂ)) x q.out := hqout
            _ = Quotient.lift
                  (leftCosetInductionSummand H (fun h ↦ (ψ h : ℂ)) x)
                  (fun a b hab ↦
                    inducedClassFunctionLeftCosetSummand_wellDefined H
                      (fun h ↦ (ψ h : ℂ))
                      (hψ.comp ((↑) : integralClosure ℤ ℂ → ℂ)) x a b hab)
                  (Quotient.mk'' q.out) := rfl
            _ = Quotient.lift
                  (leftCosetInductionSummand H (fun h ↦ (ψ h : ℂ)) x)
                  (fun a b hab ↦
                    inducedClassFunctionLeftCosetSummand_wellDefined H
                      (fun h ↦ (ψ h : ℂ))
                      (hψ.comp ((↑) : integralClosure ℤ ℂ → ℂ)) x a b hab)
                  q := by rw [Quotient.out_eq' q]
    _ = leftCosetInductionSum H (fun h ↦ (ψ h : ℂ))
          (hψ.comp ((↑) : integralClosure ℤ ℂ → ℂ)) x := by
          simp [leftCosetInductionSum]

/-- Every value of the induced class function from an integral-coefficient class function is an
algebraic integer. -/
theorem inducedClassFunction_apply_isIntegral
    (H : Subgroup G) (ψ : H → integralClosure ℤ ℂ) (hψ : IsClassFunction ψ) (x : G) :
    IsIntegral ℤ (Ind[H](fun h ↦ (ψ h : ℂ)) x) := by
  -- Compare the canonical induced value with the integral quotient formula.
  let _ : Fintype H := Fintype.ofFinite H
  have hcard_nat : Nat.card H ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero
  have hcard : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast hcard_nat
  letI : NeZero (Nat.card H : ℂ) := ⟨hcard⟩
  rw [inducedClassFunction_eq_leftCosetInductionSum
    (H := H) (ψ := fun h ↦ (ψ h : ℂ))
    (hψ := hψ.comp ((↑) : integralClosure ℤ ℂ → ℂ)) (x := x)]
  rw [← coe_leftCosetInductionSum (H := H) (ψ := ψ) hψ x]
  exact (leftCosetInductionSum H ψ hψ x).2

/-- Helper for Lemma 11-11.3-1: the quotient-valued summand whose total sum is Serre's
left-coset induction formula. -/
private def leftCosetInductionQuotientValue
    (H : Subgroup G) (ψ : H → integralClosure ℤ ℂ) (hψ : IsClassFunction ψ) (x : G) :
    G ⧸ H → integralClosure ℤ ℂ :=
  Quotient.lift
    (leftCosetInductionSummand H ψ x)
    (fun a b hab ↦ inducedClassFunctionLeftCosetSummand_wellDefined H ψ hψ x a b hab)

omit [Finite G] in
/-- Helper for Lemma 11-11.3-1: evaluating the quotient summand on the chosen representative
`q.out` recovers the original left-coset summand. -/
private theorem leftCosetInductionQuotientValue_out
    (H : Subgroup G) (ψ : H → integralClosure ℤ ℂ) (hψ : IsClassFunction ψ)
    (x : G) (q : G ⧸ H) :
    leftCosetInductionQuotientValue H ψ hψ x q =
      leftCosetInductionSummand H ψ x q.out := by
  -- Replace the quotient class by its chosen representative.
  have hmk :
      leftCosetInductionQuotientValue H ψ hψ x (Quotient.mk'' q.out) =
        leftCosetInductionSummand H ψ x q.out := by
    unfold leftCosetInductionQuotientValue
    rfl
  calc
    leftCosetInductionQuotientValue H ψ hψ x q
        =
        leftCosetInductionQuotientValue H ψ hψ x (Quotient.mk'' q.out) := by
          rw [Quotient.out_eq' q]
    _ = leftCosetInductionSummand H ψ x q.out := hmk

/-- Helper for Lemma 11-11.3-1: the total left-coset sum is the sum of the quotient-valued
summand over `G ⧸ H`. -/
private theorem leftCosetInductionSum_eq_sum_quotientValue
    (H : Subgroup G) (ψ : H → integralClosure ℤ ℂ) (hψ : IsClassFunction ψ)
    [Fintype (G ⧸ H)]
    (x : G) :
    leftCosetInductionSum H ψ hψ x =
      ∑ q : G ⧸ H, leftCosetInductionQuotientValue H ψ hψ x q := by
  -- This is only a repackaging of the existing quotient formula.
  have huniv :
      @Finset.univ (G ⧸ H) (Fintype.ofFinite (G ⧸ H)) =
        (Finset.univ : Finset (G ⧸ H)) := by
    ext q
    simp
  simp [leftCosetInductionSum, leftCosetInductionQuotientValue, huniv]

omit [Finite G] in
/-- Helper for Lemma 11-11.3-1: if a left coset is fixed by left multiplication by `g`, then the
conjugate `q.out⁻¹ * g * q.out` lies in `H`. -/
private theorem conjugate_mem_subgroup_of_smul_eq
    (H : Subgroup G) (q : G ⧸ H) (g : G) (hq : g • q = q) :
    q.out⁻¹ * g * q.out ∈ H := by
  have hsmul :
      g • q = g • (QuotientGroup.mk q.out : G ⧸ H) := by
    exact congrArg (fun z : G ⧸ H ↦ g • z) (Quotient.out_eq' q).symm
  have hcoset :
      (QuotientGroup.mk q.out : G ⧸ H) = QuotientGroup.mk (g * q.out) := by
    -- Rewrite both sides using the distinguished representative `q.out`.
    calc
      (QuotientGroup.mk q.out : G ⧸ H) = q := Quotient.out_eq' q
      _ = g • q := hq.symm
      _ = g • (QuotientGroup.mk q.out : G ⧸ H) := hsmul
      _ = QuotientGroup.mk (g * q.out) := rfl
  have hmem : q.out⁻¹ * (g * q.out) ∈ H := QuotientGroup.eq.mp hcoset
  simpa [mul_assoc] using hmem

omit [Finite G] [Fact p.Prime] in
/-- Helper for Lemma 11-11.3-1: the quotient summand is constant on the `P`-orbit of a left
coset because every element of `P` centralizes `x`. -/
private theorem leftCosetInductionQuotientValue_smul
    (H : Subgroup G) (x : G) (P : Sylow p (Subgroup.centralizer {(x : G)}))
    (ψ : H → integralClosure ℤ ℂ) (hψ : IsClassFunction ψ)
    (u : P) (q : G ⧸ H) :
    leftCosetInductionQuotientValue H ψ hψ x ((u : G) • q) =
      leftCosetInductionQuotientValue H ψ hψ x q := by
  have hu_comm : (u : G) * x = x * (u : G) := by
    exact Subgroup.mem_centralizer_singleton_iff.mp u.1.2
  have hu_conj : (u : G)⁻¹ * x * (u : G) = x := by
    calc
      (u : G)⁻¹ * x * (u : G) = (u : G)⁻¹ * ((u : G) * x) := by
        simp [hu_comm, mul_assoc]
      _ = x := by simp
  have hq_repr :
      (QuotientGroup.mk ((u : G) * q.out) : G ⧸ H) = (u : G) • q := by
    -- The coset `u • q` is represented by `(u : G) * q.out`.
    calc
      (QuotientGroup.mk ((u : G) * q.out) : G ⧸ H)
          = (u : G) • (QuotientGroup.mk q.out : G ⧸ H) := rfl
      _ = (u : G) • q := congrArg (fun z : G ⧸ H ↦ (u : G) • z) (Quotient.out_eq' q)
  have hleft :
      leftCosetInductionQuotientValue H ψ hψ x ((u : G) • q) =
        leftCosetInductionSummand H ψ x ((u : G) * q.out) := by
    rw [← hq_repr]
    unfold leftCosetInductionQuotientValue
    rfl
  have hsummand :
      leftCosetInductionSummand H ψ x ((u : G) * q.out) =
        leftCosetInductionSummand H ψ x q.out := by
    -- The branch condition and the evaluated element are unchanged after multiplying by `u`.
    have hconj :
        q.out⁻¹ * (u : G)⁻¹ * x * ((u : G) * q.out) =
          q.out⁻¹ * x * q.out := by
      calc
        q.out⁻¹ * (u : G)⁻¹ * x * ((u : G) * q.out)
            = q.out⁻¹ * ((u : G)⁻¹ * x * (u : G)) * q.out := by
                simp [mul_assoc]
        _ = q.out⁻¹ * x * q.out := by rw [hu_conj]
    rw [leftCosetInductionSummand, leftCosetInductionSummand]
    rw [show ((u : G) * q.out)⁻¹ * x * ((u : G) * q.out) =
      q.out⁻¹ * (u : G)⁻¹ * x * ((u : G) * q.out) by simp [mul_assoc]]
    rw [hconj]
  -- Evaluate `F` at the explicit representative and then use the summand identity.
  rw [hleft, leftCosetInductionQuotientValue_out]
  exact hsummand

omit [Finite G] [Fact p.Prime] in
/-- Helper for Lemma 11-11.3-1: a nonzero quotient summand forces the conjugate `q.out⁻¹ * x *
q.out` to lie in `H`, because only the nonzero branch of the summand can contribute. -/
private theorem mem_of_leftCosetInductionQuotientValue_ne_zero
    (H : Subgroup G) (ψ : H → integralClosure ℤ ℂ) (hψ : IsClassFunction ψ)
    (x : G) (q : G ⧸ H)
    (hqv : leftCosetInductionQuotientValue H ψ hψ x q ≠ 0) :
    q.out⁻¹ * x * q.out ∈ H := by
  -- Evaluate the quotient summand on `q.out` and rule out the zero branch.
  by_contra hx_mem
  apply hqv
  rw [leftCosetInductionQuotientValue_out]
  simp [leftCosetInductionSummand, hx_mem]

omit [Finite G] [Fact p.Prime] in
/-- Helper for Lemma 11-11.3-1: a `P`-fixed coset cannot support a nonzero quotient summand,
because that would place a conjugate of the associated `p`-elementary subgroup inside `H`. -/
private theorem leftCosetInductionValue_eq_zero_of_mem_fixedPoints
    (H : Subgroup G) (x : G) (P : Sylow p (Subgroup.centralizer {(x : G)}))
    (hH : ∀ g : G, ¬ MulAut.conj g • associatedPElementarySubgroup p x P ≤ H)
    (ψ : H → integralClosure ℤ ℂ) (hψ : IsClassFunction ψ)
    (q : G ⧸ H) (hq : q ∈ MulAction.fixedPoints P (G ⧸ H)) :
    leftCosetInductionQuotientValue H ψ hψ x q = 0 := by
  by_contra hqv
  let r : G := q.out
  have hfixed : ∀ u : P, (u : G) • q = q := MulAction.mem_fixedPoints.mp hq
  have hx_mem : r⁻¹ * x * r ∈ H := by
    -- A nonzero value must come from the nonzero branch of the quotient summand.
    simpa [r] using mem_of_leftCosetInductionQuotientValue_ne_zero H ψ hψ x q hqv
  have hu_mem : ∀ u : P, r⁻¹ * (u : G) * r ∈ H := by
    intro u
    -- A fixed coset forces each `u ∈ P` into the conjugate subgroup `r H r⁻¹`.
    simpa [r] using
      conjugate_mem_subgroup_of_smul_eq H q (u : G) (hfixed u)
  have hzpowers :
      MulAut.conj r⁻¹ • Subgroup.zpowers x ≤ H := by
    -- The cyclic factor already lands in `H` because `r⁻¹ * x * r ∈ H`.
    change Subgroup.map (MulAut.conj r⁻¹ : G →* G) (Subgroup.zpowers x) ≤ H
    rw [MonoidHom.map_zpowers]
    refine Subgroup.zpowers_le.2 ?_
    simpa [r] using hx_mem
  have hmap :
      MulAut.conj r⁻¹ •
          Subgroup.map (Subgroup.centralizer {(x : G)}).subtype
            (P : Subgroup (Subgroup.centralizer {(x : G)})) ≤
        H := by
    -- The `P`-factor lands in `H` because every `u ∈ P` fixes the left coset.
    change
      Subgroup.map (MulAut.conj r⁻¹ : G →* G)
          (Subgroup.map (Subgroup.centralizer {(x : G)}).subtype
            (P : Subgroup (Subgroup.centralizer {(x : G)}))) ≤
        H
    intro y hy
    rcases Subgroup.mem_map.1 hy with ⟨z, hz, rfl⟩
    rcases Subgroup.mem_map.1 hz with ⟨u, hu, rfl⟩
    simpa [r] using hu_mem ⟨u, hu⟩
  have hconj_assoc :
      MulAut.conj r⁻¹ • associatedPElementarySubgroup p x P ≤ H := by
    -- The associated subgroup is the join of the cyclic part and the `P`-part handled above.
    change Subgroup.map (MulAut.conj r⁻¹ : G →* G) (associatedPElementarySubgroup p x P) ≤ H
    rw [show associatedPElementarySubgroup p x P =
      Subgroup.zpowers x ⊔
        Subgroup.map (Subgroup.centralizer {(x : G)}).subtype
          (P : Subgroup (Subgroup.centralizer {(x : G)})) by rfl]
    rw [Subgroup.map_sup]
    exact sup_le hzpowers hmap
  exact hH r⁻¹ hconj_assoc

/-- Helper for Lemma 11-11.3-1: reindex the quotient induction sum by the finite image of the
quotient summand. -/
private theorem leftCosetInductionSum_eq_sum_over_value_fibers
    (H : Subgroup G) (ψ : H → integralClosure ℤ ℂ) (hψ : IsClassFunction ψ)
    [Fintype (G ⧸ H)]
    (x : G) :
    leftCosetInductionSum H ψ hψ x =
      ∑ a ∈ (Finset.univ : Finset (G ⧸ H)).image (leftCosetInductionQuotientValue H ψ hψ x),
        (Nat.card { q : G ⧸ H // leftCosetInductionQuotientValue H ψ hψ x q = a } :
          integralClosure ℤ ℂ) * a := by
  classical
  let F : G ⧸ H → integralClosure ℤ ℂ := leftCosetInductionQuotientValue H ψ hψ x
  have hfiberwise :
      ∑ a ∈ (Finset.univ : Finset (G ⧸ H)).image F,
          ∑ q ∈ (Finset.univ : Finset (G ⧸ H)) with F q = a, F q
        =
      ∑ q : G ⧸ H, F q := by
    -- Partition the quotient sum by the value taken by `F`.
    simpa [F] using
      (Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (G ⧸ H)))
        (t := (Finset.univ : Finset (G ⧸ H)).image F)
        (g := F)
        (fun q hq ↦ Finset.mem_image_of_mem F hq)
        (fun q : G ⧸ H ↦ F q))
  have hcoeff :
      ∀ a ∈ (Finset.univ : Finset (G ⧸ H)).image F,
        ∑ q ∈ (Finset.univ : Finset (G ⧸ H)) with F q = a, F q =
          (Nat.card { q : G ⧸ H // F q = a } : integralClosure ℤ ℂ) * a := by
    intro a ha
    let fiber : Finset (G ⧸ H) := (Finset.univ : Finset (G ⧸ H)).filter (fun q ↦ F q = a)
    have hfiber_mem : ∀ q : G ⧸ H, q ∈ fiber ↔ F q = a := by
      intro q
      simp [fiber]
    have hsum_const :
        ∑ q ∈ fiber, F q = (fiber.card : integralClosure ℤ ℂ) * a := by
      -- Every term on this fiber is equal to the common value `a`.
      calc
        ∑ q ∈ fiber, F q = ∑ q ∈ fiber, a := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          exact hfiber_mem q |>.mp hq
        _ = fiber.card • a := by rw [Finset.sum_const]
        _ = (fiber.card : integralClosure ℤ ℂ) * a := by rw [nsmul_eq_mul]
    have hcard :
        fiber.card = Nat.card { q : G ⧸ H // F q = a } := by
      -- The filtered finset and the subtype fiber have the same cardinality.
      let _ : Fintype { q : G ⧸ H // F q = a } := Fintype.ofFinset fiber (hfiber_mem ·)
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_ofFinset fiber (hfiber_mem ·)).symm
    calc
      ∑ q ∈ (Finset.univ : Finset (G ⧸ H)) with F q = a, F q
          = ∑ q ∈ fiber, F q := by simp [fiber]
      _ = (fiber.card : integralClosure ℤ ℂ) * a := hsum_const
      _ = (Nat.card { q : G ⧸ H // F q = a } : integralClosure ℤ ℂ) * a := by
            rw [hcard]
  calc
    leftCosetInductionSum H ψ hψ x = ∑ q : G ⧸ H, F q := by
      simpa [F] using leftCosetInductionSum_eq_sum_quotientValue H ψ hψ x
    _ =
        ∑ a ∈ (Finset.univ : Finset (G ⧸ H)).image F,
          ∑ q ∈ (Finset.univ : Finset (G ⧸ H)) with F q = a, F q := by
            symm
            exact hfiberwise
    _ =
        ∑ a ∈ (Finset.univ : Finset (G ⧸ H)).image F,
          (Nat.card { q : G ⧸ H // F q = a } : integralClosure ℤ ℂ) * a := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            exact hcoeff a ha

/-- Helper for Lemma 11-11.3-1: every nonzero value fiber of the quotient summand has cardinal
divisible by `p`. -/
private theorem prime_dvd_card_leftCosetInduction_value_fiber
    (H : Subgroup G) (x : G) (P : Sylow p (Subgroup.centralizer {(x : G)}))
    (hH : ∀ g : G, ¬ MulAut.conj g • associatedPElementarySubgroup p x P ≤ H)
    (ψ : H → integralClosure ℤ ℂ) (hψ : IsClassFunction ψ)
    {a : integralClosure ℤ ℂ}
    (ha : a ≠ 0) :
    p ∣ Nat.card { q : G ⧸ H // leftCosetInductionQuotientValue H ψ hψ x q = a } := by
  classical
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let F : G ⧸ H → integralClosure ℤ ℂ := leftCosetInductionQuotientValue H ψ hψ x
  let fiber : Type u := { q : G ⧸ H // F q = a }
  letI : MulAction P fiber := {
    smul u q := ⟨(u : G) • q.1, by
      simpa [F, leftCosetInductionQuotientValue_smul]
        using q.2⟩
    one_smul q := by
      apply Subtype.ext
      change ((1 : P) • q.1) = q.1
      exact one_smul P q.1
    mul_smul u v q := by
      apply Subtype.ext
      simpa using (mul_smul u v q.1)
  }
  have hfixed_empty : IsEmpty ↥(MulAction.fixedPoints P fiber) := by
    refine ⟨fun y ↦ ?_⟩
    have hy_fixed : y.1.1 ∈ MulAction.fixedPoints P (G ⧸ H) := by
      rw [MulAction.mem_fixedPoints]
      intro u
      exact congrArg Subtype.val ((MulAction.mem_fixedPoints.mp y.2) u)
    have hy_zero :
        leftCosetInductionQuotientValue H ψ hψ x y.1.1 = 0 := by
      exact leftCosetInductionValue_eq_zero_of_mem_fixedPoints H x P hH ψ hψ y.1.1 hy_fixed
    exact ha <| by
      calc
        a = leftCosetInductionQuotientValue H ψ hψ x y.1.1 := by symm; exact y.1.2
        _ = 0 := hy_zero
  letI : IsEmpty ↥(MulAction.fixedPoints P fiber) := hfixed_empty
  have hmod : Nat.card fiber ≡ Nat.card ↑(MulAction.fixedPoints P fiber) [MOD p] := by
    simpa [fiber] using P.isPGroup'.card_modEq_card_fixedPoints fiber
  exact Nat.modEq_zero_iff_dvd.mp <| by simpa [fiber] using hmod

omit [Fact p.Prime] in
/-- Helper for Lemma 11-11.3-1: if a multiplicity is divisible by `p`, then the corresponding
fiber contribution already lies in the principal ideal `(p)`. -/
private theorem natCast_mul_mem_span_prime
    {n : ℕ} {a : integralClosure ℤ ℂ} (hn : p ∣ n) :
    (n : integralClosure ℤ ℂ) * a ∈
      Ideal.span ({(p : integralClosure ℤ ℂ)} : Set (integralClosure ℤ ℂ)) := by
  rcases hn with ⟨k, rfl⟩
  -- Factor the coefficient through `p` and use the generator characterization of `(p)`.
  rw [Ideal.mem_span_singleton']
  refine ⟨(k : integralClosure ℤ ℂ) * a, ?_⟩
  calc
    ((k : integralClosure ℤ ℂ) * a) * (p : integralClosure ℤ ℂ)
        = ((p * k : ℕ) : integralClosure ℤ ℂ) * a := by
            simp [Nat.cast_mul, mul_left_comm, mul_comm]
    _ = (((p * k : ℕ) : ℕ) : integralClosure ℤ ℂ) * a := rfl

/-- Helper for Lemma 11-11.3-1: every coefficient arising from a value fiber of the quotient
summand already lies in the principal ideal `(p)`. -/
private theorem leftCosetInduction_value_fiber_term_mem_span_prime
    (H : Subgroup G) (x : G) (P : Sylow p (Subgroup.centralizer {(x : G)}))
    (hH : ∀ g : G, ¬ MulAut.conj g • associatedPElementarySubgroup p x P ≤ H)
    (ψ : H → integralClosure ℤ ℂ) (hψ : IsClassFunction ψ)
    {a : integralClosure ℤ ℂ} :
    (Nat.card { q : G ⧸ H // leftCosetInductionQuotientValue H ψ hψ x q = a } :
      integralClosure ℤ ℂ) * a ∈
      Ideal.span ({(p : integralClosure ℤ ℂ)} : Set (integralClosure ℤ ℂ)) := by
  by_cases ha : a = 0
  · -- The zero fiber contributes the zero element, which is already in `(p)`.
    simp [ha]
  · -- A nonzero fiber contributes a multiple of `p` by the `P`-set counting argument above.
    exact natCast_mul_mem_span_prime
      (p := p)
      (n := Nat.card { q : G ⧸ H // leftCosetInductionQuotientValue H ψ hψ x q = a })
      (a := a)
      (prime_dvd_card_leftCosetInduction_value_fiber H x P hH ψ hψ ha)

/-- Lemma 11-11.3-1: if `x` is a `p'`-element and `H` contains no conjugate of the associated
`p`-elementary subgroup built from `x` and a Sylow `p`-subgroup of its centralizer, then the
canonical induced value `Ind[H](fun h ↦ (ψ h : ℂ)) x`, viewed in the ring of algebraic integers of
`ℂ`,
is congruent to `0` modulo `p`. The quotient-indexed left-coset formula above is only a bridge for
computing this owner. -/
theorem inducedClassFunction_apply_mem_span_prime_of_no_conjugate_associatedPElementary
    (H : Subgroup G) (x : G) (hx : IsPRegular p x)
    (P : Sylow p (Subgroup.centralizer {(x : G)}))
    (hH : ∀ g : G, ¬ MulAut.conj g • associatedPElementarySubgroup p x P ≤ H)
    (ψ : H → integralClosure ℤ ℂ) (hψ : IsClassFunction ψ) :
    (⟨Ind[H](fun h ↦ (ψ h : ℂ)) x, H.inducedClassFunction_apply_isIntegral ψ hψ x⟩ :
      integralClosure ℤ ℂ) ∈
      Ideal.span ({(p : integralClosure ℤ ℂ)} : Set (integralClosure ℤ ℂ)) := by
  classical
  -- The textbook statement keeps the `p'`-regularity hypothesis explicit, even though this route
  -- only needs the associated `p`-elementary subgroup already built from `x` and `P`.
  let _ : IsPRegular p x := hx
  let _ : Fintype H := Fintype.ofFinite H
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let F : G ⧸ H → integralClosure ℤ ℂ := leftCosetInductionQuotientValue H ψ hψ x
  have hcard_nat : Nat.card H ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero
  have hcard : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast hcard_nat
  letI : NeZero (Nat.card H : ℂ) := ⟨hcard⟩
  have hsum_mem :
      ∑ a ∈ (Finset.univ : Finset (G ⧸ H)).image F,
          (Nat.card { q : G ⧸ H // F q = a } : integralClosure ℤ ℂ) * a ∈
        Ideal.span ({(p : integralClosure ℤ ℂ)} : Set (integralClosure ℤ ℂ)) := by
    -- Sum the fiber contributions inside the principal ideal `(p)`.
    refine Ideal.sum_mem _ ?_
    intro a ha
    simpa [F] using leftCosetInduction_value_fiber_term_mem_span_prime H x P hH ψ hψ
  have hsum_eq :
      leftCosetInductionSum H ψ hψ x =
        ∑ a ∈ (Finset.univ : Finset (G ⧸ H)).image F,
          (Nat.card { q : G ⧸ H // F q = a } : integralClosure ℤ ℂ) * a := by
    simpa [F] using leftCosetInductionSum_eq_sum_over_value_fibers H ψ hψ x
  have howner_eq :
      (⟨Ind[H](fun h ↦ (ψ h : ℂ)) x, H.inducedClassFunction_apply_isIntegral ψ hψ x⟩ :
        integralClosure ℤ ℂ) =
      leftCosetInductionSum H ψ hψ x := by
    -- The canonical induced value agrees with the integral quotient formula.
    apply Subtype.ext
    calc
      (Ind[H](fun h ↦ (ψ h : ℂ)) x : ℂ)
          = leftCosetInductionSum H (fun h ↦ (ψ h : ℂ))
              (hψ.comp ((↑) : integralClosure ℤ ℂ → ℂ)) x := by
                rw [inducedClassFunction_eq_leftCosetInductionSum
                  (H := H) (ψ := fun h ↦ (ψ h : ℂ))
                  (hψ := hψ.comp ((↑) : integralClosure ℤ ℂ → ℂ)) (x := x)]
      _ = ↑(leftCosetInductionSum H ψ hψ x) := by
            symm
            exact coe_leftCosetInductionSum H ψ hψ x
  rw [howner_eq, hsum_eq]
  exact hsum_mem

end

end

end Subgroup
