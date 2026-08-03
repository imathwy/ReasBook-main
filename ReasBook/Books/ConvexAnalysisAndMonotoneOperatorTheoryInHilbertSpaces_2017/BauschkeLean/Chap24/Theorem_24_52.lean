import Mathlib
import BauschkeLean.Chap17.Definition_17_1
import BauschkeLean.Chap17.Proposition_17_16
import BauschkeLean.Chap16.Theorem_16_58
import BauschkeLean.Chap24.Definition_24_48
import BauschkeLean.Chap24.Proposition_24_49

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

namespace ERealFunction

noncomputable section

section RealProximalThresholding

variable {Ω : Set ℝ}
variable {φ : ℝ → Set.Ioi (⊥ : EReal)}

-- Semantic recall note: `lean_leansearch` did not surface a dedicated proximal-thresholding owner;
-- local Chapter 24 precedent uses the source-facing owner `Function.IsProximalThresholderOn` and
-- the support-function summand `properIoi (σ[Ω]) ...` for `Γ₀(ℝ)` statements. On the scalar
-- derivative side, the primitive data are local finiteness near `0`, encoded canonically as
-- `0 ∈ interior (effectiveDomain ψ)`, together with `HasDerivAt ... 0 0`.

/-- Helper for Theorem 24.52: the scalar directional derivative owner used to read the zero-slice
from positive directional difference quotients. -/
noncomputable def directionalDerivative
    (f : ℝ → Set.Ioi (⊥ : EReal)) (x y : ℝ) : EReal :=
  sInf (Set.range (directionalDifferenceQuotient f x y))

notation:arg f "′(" x "; " y ")" => directionalDerivative f x y

/-- Helper for Theorem 24.52: the scalar right derivative is the directional derivative along
`1`. -/
noncomputable abbrev rightDerivative
    (f : ℝ → Set.Ioi (⊥ : EReal)) (x : ℝ) : EReal :=
  f′(x; 1)

notation:arg f "′₊(" x ")" => rightDerivative f x

/-- Helper for Theorem 24.52: the scalar left derivative is the negative directional derivative
along `-1`. -/
noncomputable abbrev leftDerivative
    (f : ℝ → Set.Ioi (⊥ : EReal)) (x : ℝ) : EReal :=
  -f′(x; -1)

notation:arg f "′₋(" x ")" => leftDerivative f x

/-- Helper for Theorem 24.52: the scalar directional derivative is the infimum of the positive-ray
difference quotients. -/
private theorem directionalDerivative_eq_sInf_imageIoi
    (f : ℝ → Set.Ioi (⊥ : EReal)) (x y : ℝ) :
    directionalDerivative f x y =
      sInf ((fun α : ℝ ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α) '' Set.Ioi (0 : ℝ)) := by
  rw [directionalDerivative]
  congr 1
  ext ξ
  constructor
  · intro hξ
    rcases hξ with ⟨α, rfl⟩
    exact ⟨(α : ℝ), α.2, by simp [directionalDifferenceQuotient]⟩
  · intro hξ
    rcases hξ with ⟨α, hα, hξ⟩
    refine ⟨⟨α, hα⟩, ?_⟩
    simpa [directionalDifferenceQuotient] using hξ

/-- Helper for Theorem 24.52: positive rescaling of the direction rescales both the directional
quotient limit and the derivative value. -/
private theorem hasDirectionalDerivativeAt_smulPos
    {f : ℝ → Set.Ioi (⊥ : EReal)} {x y : ℝ} {ξ : EReal} {c : ℝ}
    (h : HasDirectionalDerivativeAt f x y ξ) (hc : 0 < c) :
    HasDirectionalDerivativeAt f x (c • y) (ξ * c) := by
  rcases h with ⟨hx, hξ⟩
  refine ⟨hx, ?_⟩
  let q : ℝ → EReal := fun α ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α
  have htendsto_id :
      Filter.Tendsto id (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) :=
    Filter.tendsto_id
  have hcomp : Filter.Tendsto (fun α : ℝ ↦ q (α * c)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ξ) := by
    refine hξ.comp ?_
    simpa using Filter.TendstoNhdsWithinIoi.mul_const hc htendsto_id
  have hmul :
      Filter.Tendsto (fun α : ℝ ↦ q (α * c) * c) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (ξ * c)) := by
    exact EReal.Tendsto.mul_const hcomp (Or.inr (EReal.coe_ne_bot c)) (Or.inr (EReal.coe_ne_top c))
  have hEq : Filter.EventuallyEq (nhdsWithin 0 (Set.Ioi 0))
      (fun α : ℝ ↦ ((f (x + α • (c • y)) : EReal) - (f x : EReal)) / α)
      (fun α ↦ q (α * c) * c) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro α hα
    have hc0 : c ≠ 0 := hc.ne'
    have hcoeff : ((((α * c : ℝ) : EReal)⁻¹) * c) = ((α : EReal)⁻¹) := by
      rw [← EReal.coe_inv (α * c), ← EReal.coe_mul, ← EReal.coe_inv α]
      exact congrArg (fun t : ℝ ↦ (t : EReal)) <| by
        calc
          (α * c)⁻¹ * c = c / (α * c) := by
            rw [div_eq_mul_inv, mul_comm]
          _ = α⁻¹ := by
            simpa [mul_comm] using (div_mul_cancel_left₀ hc0 α)
    calc
      ((f (x + α • (c • y)) : EReal) - (f x : EReal)) / α
          = (((f (x + (α * c) • y) : EReal) - (f x : EReal)) / α) := by
              congr 1
              congr 1
              simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
      _ = ((f (x + (α * c) • y) : EReal) - (f x : EReal)) * ((α : EReal)⁻¹) := by
            rw [div_eq_mul_inv]
      _ = ((f (x + (α * c) • y) : EReal) - (f x : EReal)) *
            ((((α * c : ℝ) : EReal)⁻¹) * c) := by
              rw [hcoeff]
      _ =
          ((((f (x + (α * c) • y) : EReal) - (f x : EReal)) / ((α * c : ℝ) : EReal)) * c) := by
            rw [div_eq_mul_inv]
            exact (mul_assoc _ _ _).symm
      _ = q (α * c) * c := by
            simp [q]
  exact Filter.Tendsto.congr' hEq.symm hmul

/-- Helper for Theorem 24.52: for convex scalar owners, the positive directional quotient tends to
the canonical directional derivative. -/
private theorem directionalDifferenceQuotient_tendsto_directionalDerivative
    (f : ℝ → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : ℝ} (hx : x ∈ effectiveDomain f) (y : ℝ) :
    Filter.Tendsto
      (fun α : ℝ ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f′(x; y))) := by
  let g : ℝ → EReal := fun α ↦
    if hα : 0 < α then directionalDifferenceQuotient f x y ⟨α, hα⟩ else ⊥
  have hmono : Monotone g := by
    intro α β hαβ
    by_cases hβ : 0 < β
    · by_cases hα : 0 < α
      · have hsub : (⟨α, hα⟩ : Set.Ioi (0 : ℝ)) ≤ ⟨β, hβ⟩ := hαβ
        simpa [g, hα, hβ] using directionalDifferenceQuotient_monotone f hconv hx y hsub
      · simp [g, hα, hβ]
    · have hβ_nonpos : β ≤ 0 := le_of_not_gt hβ
      have hα_nonpos : α ≤ 0 := le_trans hαβ hβ_nonpos
      have hα : ¬ 0 < α := not_lt.mpr hα_nonpos
      simp [g, hα, hβ]
  have htendsto : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f′(x; y))) := by
    have himage :
        g '' Set.Ioi (0 : ℝ) =
          (fun α : ℝ ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α) '' Set.Ioi (0 : ℝ) := by
      ext ξ
      constructor
      · intro hξ
        rcases hξ with ⟨α, hα, rfl⟩
        have hα' : 0 < α := hα
        refine ⟨α, hα, by simp [g, directionalDifferenceQuotient, hα']⟩
      · intro hξ
        rcases hξ with ⟨α, hα, rfl⟩
        have hα' : 0 < α := hα
        refine ⟨α, hα, by simp [g, directionalDifferenceQuotient, hα']⟩
    rw [directionalDerivative_eq_sInf_imageIoi f x y]
    simpa [himage] using hmono.tendsto_nhdsGT (0 : ℝ)
  have hEq : Filter.EventuallyEq (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (fun α : ℝ ↦ ((f (x + α • y) : EReal) - (f x : EReal)) / α)
      g := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro α hα
    have hα' : 0 < α := hα
    simp [g, directionalDifferenceQuotient, hα']
  exact Filter.Tendsto.congr' hEq.symm htendsto

/-- Helper for Theorem 24.52: at an effective-domain point of a convex scalar owner, the source
directional derivative exists with the canonical infimum value. -/
private theorem hasDirectionalDerivativeAt_directionalDerivative
    {f : ℝ → Set.Ioi (⊥ : EReal)} (hconv : ConvexOn f (effectiveDomain f))
    {x : ℝ} (hx : x ∈ effectiveDomain f) (y : ℝ) :
    HasDirectionalDerivativeAt f x y (f′(x; y)) := by
  exact ⟨hx, directionalDifferenceQuotient_tendsto_directionalDerivative f hconv hx y⟩

/-- Helper for Theorem 24.52: if `(∂ φ) 0 = Ω` and `Ω` is nonempty, then `0` lies in the
effective domain of `φ`. -/
lemma zero_mem_effectiveDomain_of_subdifferential_zero_eq
    (hΩ_nonempty : Ω.Nonempty) (hφ : φ ∈ Γ₀(ℝ)) (hsub : (∂ φ) 0 = Ω) :
    0 ∈ effectiveDomain φ := by
  rcases hΩ_nonempty with ⟨u, hu⟩
  have hdom : (0 : ℝ) ∈ SetValuedOperator.dom (∂ φ) := by
    -- Read nonemptiness of `(∂ φ) 0` from the identified thresholder set `Ω`.
    refine ⟨u, ?_⟩
    simpa [hsub] using hu
  -- The subdifferential domain of a `Γ₀` function stays inside its effective domain.
  exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hφ hdom

/-- Helper for Theorem 24.52: the scalar zero-slice interval is the real preimage of an
extended-real interval under `Real.toEReal`. -/
private def realPreimageIcc (a b : EReal) : Set ℝ :=
  Set.preimage Real.toEReal (Set.Icc a b)

/-- Helper for Theorem 24.52: the canonical zero-slice interval determined by the one-sided
derivatives of `φ` at `0`. -/
private def zeroSliceInterval (φ : ℝ → Set.Ioi (⊥ : EReal)) : Set ℝ :=
  realPreimageIcc (leftDerivative φ 0) (rightDerivative φ 0)

/-- Helper for Theorem 24.52: the normalized zero-slice of `Ω` splits into the four endpoint
shapes determined by the one-sided derivatives of `φ` at `0`. -/
private lemma subdifferentialZeroEndpointCases
    (hΩ_nonempty : Ω.Nonempty)
    (hzero_mem : 0 ∈ effectiveDomain φ)
    (hφ : φ ∈ Γ₀(ℝ))
    (hΩ_interval : Ω = zeroSliceInterval φ) :
    ((leftDerivative φ 0 = ⊥ ∧ rightDerivative φ 0 = ⊤ ∧ Ω = Set.univ) ∨
      (∃ b : ℝ, leftDerivative φ 0 = ⊥ ∧ rightDerivative φ 0 = (b : EReal) ∧ Ω = Set.Iic b) ∨
      (∃ a : ℝ, leftDerivative φ 0 = (a : EReal) ∧ rightDerivative φ 0 = ⊤ ∧ Ω = Set.Ici a) ∨
      (∃ a b : ℝ, leftDerivative φ 0 = (a : EReal) ∧
        rightDerivative φ 0 = (b : EReal) ∧ Ω = Set.Icc a b)) := by
  rcases hΩ_nonempty with ⟨u, huΩ⟩
  have hu_slice : u ∈ zeroSliceInterval φ := by
    simpa [hΩ_interval] using huΩ
  have hu_bounds :
      (leftDerivative φ 0) ≤ ((u : ℝ) : EReal) ∧
        ((u : ℝ) : EReal) ≤ rightDerivative φ 0 := by
    simpa [zeroSliceInterval, realPreimageIcc, Set.mem_preimage, Set.mem_Icc] using hu_slice
  have hleft_ne_top : leftDerivative φ 0 ≠ ⊤ := by
    intro htop
    have : (⊤ : EReal) ≤ ((u : ℝ) : EReal) := by
      simpa [htop] using hu_bounds.1
    simp at this
  have hright_ne_bot : rightDerivative φ 0 ≠ ⊥ := by
    intro hbot
    have : (((u : ℝ) : EReal) ≤ (⊥ : EReal)) := by
      simpa [hbot] using hu_bounds.2
    simp at this
  by_cases hleft_bot : leftDerivative φ 0 = ⊥
  · by_cases hright_top : rightDerivative φ 0 = ⊤
    · left
      constructor
      · exact hleft_bot
      constructor
      · exact hright_top
      · -- Both infinite endpoints collapse the zero slice to all of `ℝ`.
        ext x
        simp [zeroSliceInterval, realPreimageIcc, hleft_bot, hright_top, hΩ_interval]
    · right
      left
      let b : ℝ := (rightDerivative φ 0).toReal
      have hright_eq : rightDerivative φ 0 = (b : EReal) := by
        dsimp [b]
        symm
        simpa using EReal.coe_toReal hright_top hright_ne_bot
      refine ⟨b, hleft_bot, hright_eq, ?_⟩
      -- With left endpoint `⊥` and finite right endpoint, the zero slice is `Set.Iic b`.
      ext x
      simp [zeroSliceInterval, realPreimageIcc, hleft_bot, hright_eq, hΩ_interval]
  · by_cases hright_top : rightDerivative φ 0 = ⊤
    · right
      right
      left
      let a : ℝ := (leftDerivative φ 0).toReal
      have hleft_eq : leftDerivative φ 0 = (a : EReal) := by
        dsimp [a]
        symm
        simpa using EReal.coe_toReal hleft_ne_top hleft_bot
      refine ⟨a, hleft_eq, hright_top, ?_⟩
      -- With finite left endpoint and right endpoint `⊤`, the zero slice is `Set.Ici a`.
      ext x
      simp [zeroSliceInterval, realPreimageIcc, hleft_eq, hright_top, hΩ_interval]
    · right
      right
      right
      let a : ℝ := (leftDerivative φ 0).toReal
      let b : ℝ := (rightDerivative φ 0).toReal
      have hleft_eq : leftDerivative φ 0 = (a : EReal) := by
        dsimp [a]
        symm
        simpa using EReal.coe_toReal hleft_ne_top hleft_bot
      have hright_eq : rightDerivative φ 0 = (b : EReal) := by
        dsimp [b]
        symm
        simpa using EReal.coe_toReal hright_top hright_ne_bot
      refine ⟨a, b, hleft_eq, hright_eq, ?_⟩
      -- Finite endpoints give the bounded interval `Set.Icc a b`.
      ext x
      simp [zeroSliceInterval, realPreimageIcc, hleft_eq, hright_eq, hΩ_interval]

/-- Helper for Theorem 24.52: a convex subset of `ℝ` containing one negative and one positive
point contains an open interval around `0`. -/
private lemma zero_memInterior_of_convex_with_neg_and_pos
    {S : Set ℝ} (hconv : Convex ℝ S)
    (hneg : ∃ n : ℝ, n < 0 ∧ n ∈ S)
    (hpos : ∃ p : ℝ, 0 < p ∧ p ∈ S) :
    0 ∈ interior S := by
  rcases hneg with ⟨n, hn_neg, hn_mem⟩
  rcases hpos with ⟨p, hp_pos, hp_mem⟩
  have hsubset : Set.Ioo n p ⊆ S := by
    intro x hx
    exact hconv.ordConnected.out hn_mem hp_mem ⟨hx.1.le, hx.2.le⟩
  have hzero_mem : (0 : ℝ) ∈ Set.Ioo n p := by
    exact ⟨hn_neg, hp_pos⟩
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hzero_mem) hsubset

/-- Helper for Theorem 24.52: tilting by the endpoint `b` turns the `Iic b` zero-slice into
`Iic 0`. -/
private lemma affineTilt_subdifferentialZero_eq_Iic_zero
    {b : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIic : (∂ φ) 0 = Set.Iic b) :
    (∂ affineTiltIoi φ hφ b) 0 = Set.Iic 0 := by
  ext u
  rw [mem_subdifferential_affineTiltIoi_iff (f := φ) (hf := hφ) (v := b) (z := 0) (u := u)]
  simpa [hsubIic, Set.mem_Iic, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

/-- Helper for Theorem 24.52: tilting by the endpoint `a` turns the `Ici a` zero-slice into
`Ici 0`. -/
private lemma affineTilt_subdifferentialZero_eq_Ici_zero
    {a : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIci : (∂ φ) 0 = Set.Ici a) :
    (∂ affineTiltIoi φ hφ a) 0 = Set.Ici 0 := by
  ext u
  rw [mem_subdifferential_affineTiltIoi_iff (f := φ) (hf := hφ) (v := a) (z := 0) (u := u)]
  simpa [hsubIci, Set.mem_Ici, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

/-- Helper for Theorem 24.52: affine tilting shifts a bounded zero-slice by subtracting the tilt
parameter from both endpoints. -/
private lemma affineTilt_subdifferentialZero_eq_Icc_shift
    {a b v : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIcc : (∂ φ) 0 = Set.Icc a b) :
    (∂ affineTiltIoi φ hφ v) 0 = Set.Icc (a - v) (b - v) := by
  ext u
  rw [mem_subdifferential_affineTiltIoi_iff (f := φ) (hf := hφ) (v := v) (z := 0) (u := u)]
  rw [hsubIcc, Set.mem_Icc, Set.mem_Icc]
  constructor
  · intro hu
    constructor <;> linarith
  · intro hu
    constructor <;> linarith

/-- Helper for Theorem 24.52: an `Iic b` zero-slice pins down the left and right derivatives at
`0`. -/
private lemma oneSidedDerivatives_of_subdifferentialZero_eq_Iic
    {ψ : ℝ → Set.Ioi (⊥ : EReal)} {b : ℝ}
    (hψ : ψ ∈ Γ₀(ℝ)) (hsubIic : (∂ ψ) 0 = Set.Iic b) :
    leftDerivative ψ 0 = ⊥ ∧ rightDerivative ψ 0 = (b : EReal) := by
  have hzero_mem : 0 ∈ effectiveDomain ψ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Iic b) ⟨b, by simp⟩ hψ hsubIic
  have hΩ_interval : Set.Iic b = zeroSliceInterval ψ := by
    calc
      Set.Iic b = (∂ ψ) 0 := hsubIic.symm
      _ = zeroSliceInterval ψ := by
        simpa [zeroSliceInterval, realPreimageIcc] using
          (subdifferential_eq_Icc_oneSidedDerivatives (f := ψ) (hconv := hψ.2) hzero_mem)
  rcases
      subdifferentialZeroEndpointCases
        (Ω := Set.Iic b) ⟨b, by simp⟩ hzero_mem hψ hΩ_interval with
    hUniv | hIic | hIci | hIcc
  · rcases hUniv with ⟨_, _, hΩ_univ⟩
    have hbplus : b + 1 ∈ Set.Iic b := by
      simpa [hΩ_univ] using (Set.mem_univ (b + 1))
    have hb_le : b + 1 ≤ b := hbplus
    linarith
  · rcases hIic with ⟨c, hleft_bot, hright_eq, hΩ_eq⟩
    have hbc : b ≤ c := by
      have : b ∈ Set.Iic c := by
        simpa [hΩ_eq] using (show b ∈ Set.Iic b by simp)
      exact this
    have hcb : c ≤ b := by
      have : c ∈ Set.Iic b := by
        simpa [hΩ_eq] using (show c ∈ Set.Iic c by simp)
      exact this
    have hcb_eq : c = b := by linarith
    constructor
    · exact hleft_bot
    · simpa [hcb_eq] using hright_eq
  · rcases hIci with ⟨a, _, _, hΩ_eq⟩
    have hab : a ≤ b := by
      have : a ∈ Set.Iic b := by
        simpa [hΩ_eq] using (show a ∈ Set.Ici a by simp)
      exact this
    have hbplus : b + 1 ∈ Set.Ici a := by
      change a ≤ b + 1
      linarith
    have : b + 1 ∈ Set.Iic b := by
      simpa [hΩ_eq] using hbplus
    have hb_le : b + 1 ≤ b := this
    linarith
  · rcases hIcc with ⟨a, c, _, _, hΩ_eq⟩
    have hab : a ≤ b := by
      have : b ∈ Set.Icc a c := by
        simpa [hΩ_eq] using (show b ∈ Set.Iic b by simp)
      exact this.1
    have haminus : a - 1 ∈ Set.Iic b := by
      change a - 1 ≤ b
      linarith
    have : a - 1 ∈ Set.Icc a c := by
      simpa [hΩ_eq] using haminus
    have ha_le : a ≤ a - 1 := this.1
    linarith

/-- Helper for Theorem 24.52: an `Ici a` zero-slice pins down the left and right derivatives at
`0`. -/
private lemma oneSidedDerivatives_of_subdifferentialZero_eq_Ici
    {ψ : ℝ → Set.Ioi (⊥ : EReal)} {a : ℝ}
    (hψ : ψ ∈ Γ₀(ℝ)) (hsubIci : (∂ ψ) 0 = Set.Ici a) :
    leftDerivative ψ 0 = (a : EReal) ∧ rightDerivative ψ 0 = ⊤ := by
  have hzero_mem : 0 ∈ effectiveDomain ψ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Ici a) ⟨a, by simp⟩ hψ hsubIci
  have hΩ_interval : Set.Ici a = zeroSliceInterval ψ := by
    calc
      Set.Ici a = (∂ ψ) 0 := hsubIci.symm
      _ = zeroSliceInterval ψ := by
        simpa [zeroSliceInterval, realPreimageIcc] using
          (subdifferential_eq_Icc_oneSidedDerivatives (f := ψ) (hconv := hψ.2) hzero_mem)
  rcases
      subdifferentialZeroEndpointCases
        (Ω := Set.Ici a) ⟨a, by simp⟩ hzero_mem hψ hΩ_interval with
    hUniv | hIic | hIci | hIcc
  · rcases hUniv with ⟨_, _, hΩ_univ⟩
    have haminus : a - 1 ∈ Set.Ici a := by
      simpa [hΩ_univ] using (Set.mem_univ (a - 1))
    have ha_le : a ≤ a - 1 := haminus
    linarith
  · rcases hIic with ⟨b, _, _, hΩ_eq⟩
    have hab : a ≤ b := by
      have : a ∈ Set.Iic b := by
        simpa [hΩ_eq] using (show a ∈ Set.Ici a by simp)
      exact this
    have hbplus : b + 1 ∈ Set.Ici a := by
      change a ≤ b + 1
      linarith
    have : b + 1 ∈ Set.Iic b := by
      simpa [hΩ_eq] using hbplus
    have hb_le : b + 1 ≤ b := this
    linarith
  · rcases hIci with ⟨c, hleft_eq, hright_top, hΩ_eq⟩
    have hca : c ≤ a := by
      have : a ∈ Set.Ici c := by
        simpa [hΩ_eq] using (show a ∈ Set.Ici a by simp)
      exact this
    have hac : a ≤ c := by
      have : c ∈ Set.Ici a := by
        simpa [hΩ_eq] using (show c ∈ Set.Ici c by simp)
      exact this
    have hca_eq : c = a := by linarith
    constructor
    · simpa [hca_eq] using hleft_eq
    · exact hright_top
  · rcases hIcc with ⟨c, b, _, _, hΩ_eq⟩
    have hca : c ≤ a := by
      have : a ∈ Set.Icc c b := by
        simpa [hΩ_eq] using (show a ∈ Set.Ici a by simp)
      exact this.1
    have hab : a ≤ b := by
      have : a ∈ Set.Icc c b := by
        simpa [hΩ_eq] using (show a ∈ Set.Ici a by simp)
      exact this.2
    have hbplus : b + 1 ∈ Set.Ici a := by
      change a ≤ b + 1
      linarith
    have : b + 1 ∈ Set.Icc c b := by
      simpa [hΩ_eq] using hbplus
    have hb_le : b + 1 ≤ b := this.2
    linarith

/-- Helper for Theorem 24.52: a bounded zero-slice identifies both one-sided derivatives at `0`
with the interval endpoints. -/
private lemma oneSidedDerivatives_of_subdifferentialZero_eq_Icc
    {ψ : ℝ → Set.Ioi (⊥ : EReal)} {a b : ℝ}
    (hab : a ≤ b) (hψ : ψ ∈ Γ₀(ℝ)) (hsubIcc : (∂ ψ) 0 = Set.Icc a b) :
    leftDerivative ψ 0 = (a : EReal) ∧ rightDerivative ψ 0 = (b : EReal) := by
  have hzero_mem : 0 ∈ effectiveDomain ψ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Icc a b) (Set.nonempty_Icc.2 hab) hψ hsubIcc
  have hΩ_interval : Set.Icc a b = zeroSliceInterval ψ := by
    calc
      Set.Icc a b = (∂ ψ) 0 := hsubIcc.symm
      _ = zeroSliceInterval ψ := by
        simpa [zeroSliceInterval, realPreimageIcc] using
          (subdifferential_eq_Icc_oneSidedDerivatives (f := ψ) (hconv := hψ.2) hzero_mem)
  rcases
      subdifferentialZeroEndpointCases
        (Ω := Set.Icc a b) (Set.nonempty_Icc.2 hab) hzero_mem hψ hΩ_interval with
    hUniv | hIic | hIci | hIcc
  · rcases hUniv with ⟨_, _, hΩ_univ⟩
    have hbplus : b + 1 ∈ Set.Icc a b := by
      simpa [hΩ_univ] using (Set.mem_univ (b + 1))
    linarith [hbplus.2]
  · rcases hIic with ⟨c, _, _, hΩ_eq⟩
    have hac : a ≤ c := by
      have : a ∈ Set.Iic c := by
        simpa [hΩ_eq] using (show a ∈ Set.Icc a b by exact ⟨le_rfl, hab⟩)
      exact this
    have haminus : a - 1 ∈ Set.Iic c := by
      change a - 1 ≤ c
      linarith
    have : a - 1 ∈ Set.Icc a b := by
      simpa [hΩ_eq] using haminus
    have ha_le : a ≤ a - 1 := this.1
    linarith
  · rcases hIci with ⟨c, _, _, hΩ_eq⟩
    have hcb : c ≤ b := by
      have : b ∈ Set.Ici c := by
        simpa [hΩ_eq] using (show b ∈ Set.Icc a b by exact ⟨hab, le_rfl⟩)
      exact this
    have hbplus : b + 1 ∈ Set.Ici c := by
      change c ≤ b + 1
      linarith
    have : b + 1 ∈ Set.Icc a b := by
      simpa [hΩ_eq] using hbplus
    linarith [this.2]
  · rcases hIcc with ⟨c, d, hleft_eq, hright_eq, hΩ_eq⟩
    have ha_mem : a ∈ Set.Icc c d := by
      simpa [hΩ_eq] using (show a ∈ Set.Icc a b by exact ⟨le_rfl, hab⟩)
    have hcd : c ≤ d := le_trans ha_mem.1 ha_mem.2
    have hc_mem : c ∈ Set.Icc a b := by
      simpa [hΩ_eq] using (show c ∈ Set.Icc c d by exact ⟨le_rfl, hcd⟩)
    have hb_mem : b ∈ Set.Icc c d := by
      simpa [hΩ_eq] using (show b ∈ Set.Icc a b by exact ⟨hab, le_rfl⟩)
    have hd_mem : d ∈ Set.Icc a b := by
      simpa [hΩ_eq] using (show d ∈ Set.Icc c d by exact ⟨hcd, le_rfl⟩)
    have hca : c = a := by
      linarith [ha_mem.1, hc_mem.1]
    have hdb : d = b := by
      linarith [hb_mem.2, hd_mem.2]
    constructor
    · simpa [hca] using hleft_eq
    · simpa [hdb] using hright_eq

/-- Helper for Theorem 24.52: the tilted `Set.Iic b` branch has right derivative `0` at the
origin. -/
private lemma affineTilt_rightDerivative_zero_of_subdifferentialZero_eq_Iic
    {b : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIic : (∂ φ) 0 = Set.Iic b) :
    rightDerivative (affineTiltIoi φ hφ b) 0 = 0 := by
  have htilt :
      affineTiltIoi φ hφ b ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) b
  have hsub0 :
      (∂ affineTiltIoi φ hφ b) 0 = Set.Iic 0 :=
    affineTilt_subdifferentialZero_eq_Iic_zero (φ := φ) (hφ := hφ) hsubIic
  exact (oneSidedDerivatives_of_subdifferentialZero_eq_Iic (hψ := htilt) hsub0).2

/-- Helper for Theorem 24.52: the tilted `Set.Ici a` branch has left derivative `0` at the
origin. -/
private lemma affineTilt_leftDerivative_zero_of_subdifferentialZero_eq_Ici
    {a : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIci : (∂ φ) 0 = Set.Ici a) :
    leftDerivative (affineTiltIoi φ hφ a) 0 = 0 := by
  have htilt :
      affineTiltIoi φ hφ a ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) a
  have hsub0 :
      (∂ affineTiltIoi φ hφ a) 0 = Set.Ici 0 :=
    affineTilt_subdifferentialZero_eq_Ici_zero (φ := φ) (hφ := hφ) hsubIci
  exact (oneSidedDerivatives_of_subdifferentialZero_eq_Ici (hψ := htilt) hsub0).1

/-- Helper for Theorem 24.52: the bounded affine-tilt branch reads off its endpoint derivatives at
the origin from the shifted zero-slice. -/
private lemma affineTilt_oneSidedDerivatives_of_subdifferentialZero_eq_Icc
    {a b v : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ)) (hsubIcc : (∂ φ) 0 = Set.Icc a b) :
    leftDerivative (affineTiltIoi φ hφ v) 0 = ((a - v : ℝ) : EReal) ∧
      rightDerivative (affineTiltIoi φ hφ v) 0 = ((b - v : ℝ) : EReal) := by
  have htilt :
      affineTiltIoi φ hφ v ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) v
  have hshift :
      (∂ affineTiltIoi φ hφ v) 0 = Set.Icc (a - v) (b - v) :=
    affineTilt_subdifferentialZero_eq_Icc_shift (φ := φ) (hφ := hφ) (v := v) hsubIcc
  have hshift_le : a - v ≤ b - v := by
    linarith
  exact
    oneSidedDerivatives_of_subdifferentialZero_eq_Icc
      (hψ := htilt) hshift_le hshift

/-- Helper for Theorem 24.52: the normalized `Set.Iic 0` affine-tilt branch has right derivative
`0` in the source sense. -/
private lemma affineTilt_hasRightDerivativeAtZero_of_subdifferentialZero_eq_Iic
    {b : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIic : (∂ φ) 0 = Set.Iic b) :
    HasRightDerivativeAt (affineTiltIoi φ hφ b) 0 0 := by
  let ψ := affineTiltIoi φ hφ b
  have hψ : ψ ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) b
  have hsub0 :
      (∂ ψ) 0 = Set.Iic 0 := by
    simpa [ψ] using affineTilt_subdifferentialZero_eq_Iic_zero (φ := φ) (hφ := hφ) hsubIic
  have hzero_mem : 0 ∈ effectiveDomain ψ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Iic 0) ⟨0, by simp⟩ hψ hsub0
  have hright : rightDerivative ψ 0 = 0 :=
    affineTilt_rightDerivative_zero_of_subdifferentialZero_eq_Iic (φ := φ) (hφ := hφ) hsubIic
  -- Once the canonical right derivative is normalized to `0`, Proposition 17.2 supplies the
  -- corresponding source-facing right derivative witness.
  simpa [HasRightDerivativeAt, ψ, rightDerivative, hright] using
    (hasDirectionalDerivativeAt_directionalDerivative (f := ψ) hψ.2 hzero_mem (1 : ℝ))

/-- Helper for Theorem 24.52: the normalized `Set.Ici 0` affine-tilt branch has left derivative
`0` in the source sense. -/
private lemma affineTilt_hasLeftDerivativeAtZero_of_subdifferentialZero_eq_Ici
    {a : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIci : (∂ φ) 0 = Set.Ici a) :
    HasLeftDerivativeAt (affineTiltIoi φ hφ a) 0 0 := by
  let ψ := affineTiltIoi φ hφ a
  have hψ : ψ ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) a
  have hsub0 :
      (∂ ψ) 0 = Set.Ici 0 := by
    simpa [ψ] using affineTilt_subdifferentialZero_eq_Ici_zero (φ := φ) (hφ := hφ) hsubIci
  have hzero_mem : 0 ∈ effectiveDomain ψ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Ici 0) ⟨0, by simp⟩ hψ hsub0
  have hleft : leftDerivative ψ 0 = 0 :=
    affineTilt_leftDerivative_zero_of_subdifferentialZero_eq_Ici (φ := φ) (hφ := hφ) hsubIci
  have hdir : directionalDerivative ψ 0 (-1) = 0 := by
    simpa [leftDerivative] using congrArg Neg.neg hleft
  -- The left derivative owner is the directional derivative along `-1` with the sign convention
  -- already built into `HasLeftDerivativeAt`.
  simpa [HasLeftDerivativeAt, ψ, hdir] using
    (hasDirectionalDerivativeAt_directionalDerivative (f := ψ) hψ.2 hzero_mem (-1 : ℝ))

/-- Helper for Theorem 24.52: in the bounded case, the left tilted branch has left derivative `0`
at the origin. -/
private lemma affineTilt_hasLeftDerivativeAtZero_of_subdifferentialZero_eq_Icc
    {a b : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ)) (hsubIcc : (∂ φ) 0 = Set.Icc a b) :
    HasLeftDerivativeAt (affineTiltIoi φ hφ a) 0 0 := by
  let ψ := affineTiltIoi φ hφ a
  have hψ : ψ ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) a
  have hsub0 :
      (∂ ψ) 0 = Set.Icc 0 (b - a) := by
    simpa [ψ] using
      affineTilt_subdifferentialZero_eq_Icc_shift
        (φ := φ) (hφ := hφ) (v := a) hsubIcc
  have hzero_mem : 0 ∈ effectiveDomain ψ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Icc 0 (b - a)) (by
        refine ⟨0, ?_⟩
        constructor
        · simp
        · linarith) hψ hsub0
  have hleft :
      leftDerivative ψ 0 = 0 := by
    simpa [ψ] using
      (affineTilt_oneSidedDerivatives_of_subdifferentialZero_eq_Icc
        (φ := φ) (hab := hab) (hφ := hφ) (v := a) hsubIcc).1
  have hdir : directionalDerivative ψ 0 (-1) = 0 := by
    simpa [leftDerivative] using congrArg Neg.neg hleft
  -- The left branch is the affine tilt by `a`, and its shifted left endpoint is `0`.
  simpa [HasLeftDerivativeAt, ψ, hdir] using
    (hasDirectionalDerivativeAt_directionalDerivative (f := ψ) hψ.2 hzero_mem (-1 : ℝ))

/-- Helper for Theorem 24.52: in the bounded case, the right tilted branch has right derivative
`0` at the origin. -/
private lemma affineTilt_hasRightDerivativeAtZero_of_subdifferentialZero_eq_Icc
    {a b : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ)) (hsubIcc : (∂ φ) 0 = Set.Icc a b) :
    HasRightDerivativeAt (affineTiltIoi φ hφ b) 0 0 := by
  let ψ := affineTiltIoi φ hφ b
  have hψ : ψ ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) b
  have hsub0 :
      (∂ ψ) 0 = Set.Icc (a - b) 0 := by
    simpa [ψ] using
      affineTilt_subdifferentialZero_eq_Icc_shift
        (φ := φ) (hφ := hφ) (v := b) hsubIcc
  have hzero_mem : 0 ∈ effectiveDomain ψ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Icc (a - b) 0) (by
        refine ⟨0, ?_⟩
        constructor
        · linarith
        · simp) hψ hsub0
  have hright :
      rightDerivative ψ 0 = 0 := by
    simpa [ψ] using
      (affineTilt_oneSidedDerivatives_of_subdifferentialZero_eq_Icc
        (φ := φ) (hab := hab) (hφ := hφ) (v := b) hsubIcc).2
  -- The right branch is the affine tilt by `b`, and its shifted right endpoint is `0`.
  simpa [HasRightDerivativeAt, ψ, rightDerivative, hright] using
    (hasDirectionalDerivativeAt_directionalDerivative (f := ψ) hψ.2 hzero_mem (1 : ℝ))

/-- Helper for Theorem 24.52: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul (x y : ℝ) : ⟪x, y⟫_ℝ = x * y := by
  calc
    ⟪x, y⟫_ℝ = (starRingEnd ℝ) x * y := RCLike.inner_apply' x y
    _ = x * y := by simp

/-- Helper for Theorem 24.52: at finite points, a subgradient inequality at `0` can be read in
`ℝ`. -/
private lemma real_subgradient_inequality_at_zero
    {u x : ℝ}
    (hzero_mem : 0 ∈ effectiveDomain φ) (hx : x ∈ effectiveDomain φ) (hu : u ∈ (∂ φ) 0) :
    x * u + (φ 0 : EReal).toReal ≤ (φ x : EReal).toReal := by
  have hineq :=
    (mem_subdifferential_iff (f := φ) (x := (0 : ℝ)) (u := u)).1 hu x
  have hφ0_top : (φ 0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hzero_mem)
  have hφ0_bot : (φ 0 : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (φ 0 : EReal) from (φ 0).2)
  have hφx_top : (φ x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hφx_bot : (φ x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (φ x : EReal) from (φ x).2)
  have hcast :
      (((x * u + (φ 0 : EReal).toReal : ℝ) : EReal) ≤
        (((φ x : EReal).toReal : ℝ) : EReal)) := by
    -- Rewrite the extended-real inequality through the finite values at `0` and `x`.
    simpa [sub_zero, real_inner_eq_mul, EReal.coe_add,
      EReal.coe_toReal hφ0_top hφ0_bot, EReal.coe_toReal hφx_top hφx_bot] using hineq
  exact EReal.coe_le_coe_iff.mp hcast

/-- Helper for Theorem 24.52: if every real number is a subgradient of `φ` at `0`, then the only
finite point of `φ` is `0`. -/
private lemma effectiveDomain_eq_singleton_zero_of_subdifferential_zero_eq_univ
    (hzero_mem : 0 ∈ effectiveDomain φ) (hsub_univ : (∂ φ) 0 = Set.univ) :
    effectiveDomain φ = ({0} : Set ℝ) := by
  ext x
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · simpa [hx0]
    · have hu :
          (((φ x : EReal).toReal - (φ 0 : EReal).toReal + 1) / x) ∈ (∂ φ) 0 := by
        simpa [hsub_univ]
      have hineq :=
        real_subgradient_inequality_at_zero
          (x := x)
          hzero_mem
          hx
          hu
      have hx_ne : x ≠ 0 := hx0
      have hcalc :
          x * (((φ x : EReal).toReal - (φ 0 : EReal).toReal + 1) / x) +
              (φ 0 : EReal).toReal =
            (φ x : EReal).toReal + 1 := by
        field_simp [hx_ne]
        ring
      rw [hcalc] at hineq
      linarith
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    simpa [hx] using hzero_mem

/-- Helper for Theorem 24.52: if the effective domain is exactly `{0}`, then every real number is a
subgradient at `0`. -/
private lemma subdifferential_zero_eq_univ_of_effectiveDomain_eq_singleton_zero
    (hdom_zero : effectiveDomain φ = ({0} : Set ℝ)) :
    (∂ φ) 0 = Set.univ := by
  ext u
  constructor
  · intro hu
    simp
  · intro _
    rw [mem_subdifferential_iff]
    intro y
    by_cases hy : y = 0
    · subst hy
      simp
    · have hy_not_mem : y ∉ effectiveDomain φ := by
        rw [hdom_zero]
        simpa [Set.mem_singleton_iff] using hy
      have hφy_top : (φ y : EReal) = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy_not_mem))
      -- Outside the singleton effective domain, the target value is `⊤`, so the inequality is
      -- automatic.
      change ((⟪y - 0, u⟫_ℝ : EReal) + (φ 0 : EReal) ≤ (φ y : EReal))
      rw [hφy_top]
      exact le_top

/-- Helper for Theorem 24.52: an `Iic` zero-slice forces the effective domain onto the nonnegative
half-line and contains a strictly positive point. -/
private lemma effectiveDomain_nonneg_and_posWitness_of_subdifferentialZero_Iic
    {b : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIic : (∂ φ) 0 = Set.Iic b) :
    effectiveDomain φ ⊆ Set.Ici 0 ∧ ∃ p : ℝ, 0 < p ∧ p ∈ effectiveDomain φ := by
  have hzero_mem : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Iic b)
      ⟨b, by simp⟩
      hφ
      hsubIic
  have hnonneg : effectiveDomain φ ⊆ Set.Ici 0 := by
    intro x hx
    by_cases hx_nonneg : 0 ≤ x
    · exact hx_nonneg
    · have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
      let t : ℝ := ((φ x : EReal).toReal - (φ 0 : EReal).toReal) / x
      let u : ℝ := min b (t - 1)
      have hu : u ∈ (∂ φ) 0 := by
        simpa [hsubIic, u] using (min_le_left b (t - 1))
      have hineq :=
        real_subgradient_inequality_at_zero
          (x := x)
          hzero_mem
          hx
          hu
      have hxu :
          x * (t - 1) ≤ x * u := by
        have hu_le : u ≤ t - 1 := by
          simp [u]
        exact mul_le_mul_of_nonpos_left hu_le hx_neg.le
      have hx_ne : x ≠ 0 := ne_of_lt hx_neg
      have hcalc :
          x * (t - 1) + (φ 0 : EReal).toReal = (φ x : EReal).toReal - x := by
        dsimp [t]
        field_simp [hx_ne]
        ring
      have hcontra :
          (φ x : EReal).toReal - x ≤ (φ x : EReal).toReal := by
        have hstep :
            x * (t - 1) + (φ 0 : EReal).toReal ≤ x * u + (φ 0 : EReal).toReal := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hxu (φ 0 : EReal).toReal
        have hbound :
            x * (t - 1) + (φ 0 : EReal).toReal ≤ (φ x : EReal).toReal :=
          le_trans hstep hineq
        simpa [hcalc] using hbound
      linarith
  have hnot_singleton : effectiveDomain φ ≠ ({0} : Set ℝ) := by
    intro hdom_zero
    have hsub_univ :
        (∂ φ) 0 = Set.univ :=
      subdifferential_zero_eq_univ_of_effectiveDomain_eq_singleton_zero hdom_zero
    have hcontra : Set.Iic b = Set.univ := by
      exact hsubIic.symm.trans hsub_univ
    have hbplus : b + 1 ∈ Set.Iic b := by
      simpa [hcontra] using (Set.mem_univ (b + 1))
    have hb_le : b + 1 ≤ b := hbplus
    linarith
  have hnonzero :
      ∃ x : ℝ, x ∈ effectiveDomain φ ∧ x ≠ 0 := by
    by_contra hno
    apply hnot_singleton
    ext x
    constructor
    · intro hx
      by_cases hx0 : x = 0
      · simpa [hx0]
      · exact False.elim (hno ⟨x, hx, hx0⟩)
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      simpa [hx] using hzero_mem
  rcases hnonzero with ⟨p, hp, hp_ne⟩
  have hp_nonneg : 0 ≤ p := hnonneg hp
  have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp_ne)
  exact ⟨hnonneg, ⟨p, hp_pos, hp⟩⟩

/-- Helper for Theorem 24.52: an `Ici` zero-slice forces the effective domain onto the nonpositive
half-line and contains a strictly negative point. -/
private lemma effectiveDomain_nonpos_and_negWitness_of_subdifferentialZero_Ici
    {a : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIci : (∂ φ) 0 = Set.Ici a) :
    effectiveDomain φ ⊆ Set.Iic 0 ∧ ∃ n : ℝ, n < 0 ∧ n ∈ effectiveDomain φ := by
  have hzero_mem : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Ici a)
      ⟨a, by simp⟩
      hφ
      hsubIci
  have hnonpos : effectiveDomain φ ⊆ Set.Iic 0 := by
    intro x hx
    by_cases hx_nonpos : x ≤ 0
    · exact hx_nonpos
    · have hx_pos : 0 < x := lt_of_not_ge hx_nonpos
      let t : ℝ := ((φ x : EReal).toReal - (φ 0 : EReal).toReal) / x
      let u : ℝ := max a (t + 1)
      have hu : u ∈ (∂ φ) 0 := by
        simpa [hsubIci, u] using (le_max_left a (t + 1))
      have hineq :=
        real_subgradient_inequality_at_zero
          (x := x)
          hzero_mem
          hx
          hu
      have hxu :
          x * (t + 1) ≤ x * u := by
        have hu_ge : t + 1 ≤ u := by
          simp [u]
        exact mul_le_mul_of_nonneg_left hu_ge hx_pos.le
      have hx_ne : x ≠ 0 := ne_of_gt hx_pos
      have hcalc :
          x * (t + 1) + (φ 0 : EReal).toReal = (φ x : EReal).toReal + x := by
        dsimp [t]
        field_simp [hx_ne]
        ring
      have hcontra :
          (φ x : EReal).toReal + x ≤ (φ x : EReal).toReal := by
        have hstep :
            x * (t + 1) + (φ 0 : EReal).toReal ≤ x * u + (φ 0 : EReal).toReal := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hxu (φ 0 : EReal).toReal
        have hbound :
            x * (t + 1) + (φ 0 : EReal).toReal ≤ (φ x : EReal).toReal :=
          le_trans hstep hineq
        simpa [hcalc] using hbound
      linarith
  have hnot_singleton : effectiveDomain φ ≠ ({0} : Set ℝ) := by
    intro hdom_zero
    have hsub_univ :
        (∂ φ) 0 = Set.univ :=
      subdifferential_zero_eq_univ_of_effectiveDomain_eq_singleton_zero hdom_zero
    have hcontra : Set.Ici a = Set.univ := by
      exact hsubIci.symm.trans hsub_univ
    have haminus : a - 1 ∈ Set.Ici a := by
      simpa [hcontra] using (Set.mem_univ (a - 1))
    have ha_le : a ≤ a - 1 := haminus
    linarith
  have hnonzero :
      ∃ x : ℝ, x ∈ effectiveDomain φ ∧ x ≠ 0 := by
    by_contra hno
    apply hnot_singleton
    ext x
    constructor
    · intro hx
      by_cases hx0 : x = 0
      · simpa [hx0]
      · exact False.elim (hno ⟨x, hx, hx0⟩)
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      simpa [hx] using hzero_mem
  rcases hnonzero with ⟨n, hn, hn_ne⟩
  have hn_nonpos : n ≤ 0 := hnonpos hn
  have hn_neg : n < 0 := lt_of_le_of_ne hn_nonpos hn_ne
  exact ⟨hnonpos, ⟨n, hn_neg, hn⟩⟩

/-- Helper for Theorem 24.52: a bounded zero-slice forces finite points of `φ` on both sides of
the origin. -/
private lemma effectiveDomain_twoSidedWitnesses_of_subdifferentialZero_Icc
    {a b : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ)) (hsubIcc : (∂ φ) 0 = Set.Icc a b) :
    ∃ n p : ℝ, n < 0 ∧ n ∈ effectiveDomain φ ∧ 0 < p ∧ p ∈ effectiveDomain φ := by
  -- Route correction: this bounded-interval geometry lemma is the first remaining blocker in the
  -- `Set.Icc` branch. The intended proof shows that a one-sided domain would enlarge the zero
  -- slice beyond `Set.Icc a b`, then extracts witnesses from the negated subset statements.
  have hzero_mem : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Icc a b)
      ⟨a, by simp [hab]⟩
      hφ
      hsubIcc
  have ha_sub : a ∈ (∂ φ) 0 := by
    simpa [hsubIcc] using (show a ∈ Set.Icc a b by exact ⟨le_rfl, hab⟩)
  have hb_sub : b ∈ (∂ φ) 0 := by
    simpa [hsubIcc] using (show b ∈ Set.Icc a b by exact ⟨hab, le_rfl⟩)
  have hnot_nonneg : ¬ effectiveDomain φ ⊆ Set.Ici 0 := by
    intro hdom_nonneg
    have hsub_left : a - 1 ∈ (∂ φ) 0 := by
      rw [mem_subdifferential_iff]
      intro y
      by_cases hy : y ∈ effectiveDomain φ
      · have hy_nonneg : 0 ≤ y := hdom_nonneg hy
        -- On the nonnegative side, lowering the slope from `a` to `a - 1` preserves the
        -- supporting inequality at `0`.
        have hineq_a :
            (((y * a : ℝ) : EReal) + (φ 0 : EReal) ≤ (φ y : EReal)) := by
          have hineq_a_raw :=
            (mem_subdifferential_iff (f := φ) (x := (0 : ℝ)) (u := a)).1 ha_sub y
          simpa [sub_zero, real_inner_eq_mul] using hineq_a_raw
        have hmul :
            (((y * (a - 1) : ℝ) : EReal) ≤ ((y * a : ℝ) : EReal)) := by
          exact EReal.coe_le_coe <|
            mul_le_mul_of_nonneg_left (show a - 1 ≤ a by linarith) hy_nonneg
        have hstep :
            (((y * (a - 1) : ℝ) : EReal) + (φ 0 : EReal)) ≤
              (((y * a : ℝ) : EReal) + (φ 0 : EReal)) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hmul (φ 0 : EReal)
        have hbound :
            (((y * (a - 1) : ℝ) : EReal) + (φ 0 : EReal)) ≤ (φ y : EReal) :=
          le_trans hstep hineq_a
        simpa [sub_zero, real_inner_eq_mul] using hbound
      · have hφy_top : (φ y : EReal) = ⊤ := by
          exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))
        -- Outside the effective domain, the target value is `⊤`, so the inequality is automatic.
        change ((⟪y - 0, a - 1⟫_ℝ : EReal) + (φ 0 : EReal) ≤ (φ y : EReal))
        rw [hφy_top]
        exact le_top
    have hleft_mem : a - 1 ∈ Set.Icc a b := by
      simpa [hsubIcc] using hsub_left
    linarith [hleft_mem.1]
  have hnot_nonpos : ¬ effectiveDomain φ ⊆ Set.Iic 0 := by
    intro hdom_nonpos
    have hsub_right : b + 1 ∈ (∂ φ) 0 := by
      rw [mem_subdifferential_iff]
      intro y
      by_cases hy : y ∈ effectiveDomain φ
      · have hy_nonpos : y ≤ 0 := hdom_nonpos hy
        -- On the nonpositive side, raising the slope from `b` to `b + 1` still preserves the
        -- supporting inequality at `0`.
        have hineq_b :
            (((y * b : ℝ) : EReal) + (φ 0 : EReal) ≤ (φ y : EReal)) := by
          have hineq_b_raw :=
            (mem_subdifferential_iff (f := φ) (x := (0 : ℝ)) (u := b)).1 hb_sub y
          simpa [sub_zero, real_inner_eq_mul] using hineq_b_raw
        have hmul :
            (((y * (b + 1) : ℝ) : EReal) ≤ ((y * b : ℝ) : EReal)) := by
          exact EReal.coe_le_coe <|
            mul_le_mul_of_nonpos_left (show b ≤ b + 1 by linarith) hy_nonpos
        have hstep :
            (((y * (b + 1) : ℝ) : EReal) + (φ 0 : EReal)) ≤
              (((y * b : ℝ) : EReal) + (φ 0 : EReal)) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hmul (φ 0 : EReal)
        have hbound :
            (((y * (b + 1) : ℝ) : EReal) + (φ 0 : EReal)) ≤ (φ y : EReal) :=
          le_trans hstep hineq_b
        simpa [sub_zero, real_inner_eq_mul] using hbound
      · have hφy_top : (φ y : EReal) = ⊤ := by
          exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))
        -- Outside the effective domain, the target value is `⊤`, so the inequality is automatic.
        change ((⟪y - 0, b + 1⟫_ℝ : EReal) + (φ 0 : EReal) ≤ (φ y : EReal))
        rw [hφy_top]
        exact le_top
    have hright_mem : b + 1 ∈ Set.Icc a b := by
      simpa [hsubIcc] using hsub_right
    linarith [hright_mem.2]
  have hneg_exists : ∃ n : ℝ, n ∈ effectiveDomain φ ∧ n < 0 := by
    by_contra hneg
    apply hnot_nonneg
    intro x hx
    by_cases hx_nonneg : 0 ≤ x
    · exact hx_nonneg
    · exact False.elim (hneg ⟨x, hx, lt_of_not_ge hx_nonneg⟩)
  have hpos_exists : ∃ p : ℝ, p ∈ effectiveDomain φ ∧ 0 < p := by
    by_contra hpos
    apply hnot_nonpos
    intro x hx
    by_cases hx_nonpos : x ≤ 0
    · exact hx_nonpos
    · exact False.elim (hpos ⟨x, hx, lt_of_not_ge hx_nonpos⟩)
  -- The failed one-sided alternatives leave concrete finite points on both sides of `0`.
  rcases hneg_exists with ⟨n, hn_mem, hn_neg⟩
  rcases hpos_exists with ⟨p, hp_mem, hp_pos⟩
  exact ⟨n, p, hn_neg, hn_mem, hp_pos, hp_mem⟩

/-- Helper for Theorem 24.52: the support functions of half-lines in `ℝ` are the expected
piecewise affine or `+∞` formulas. -/
private lemma supportFunction_ray_eq_piecewise (a b ξ : ℝ) :
    (σ[Set.Iic b] ξ = if ξ < 0 then ⊤ else ((b * ξ : ℝ) : EReal)) ∧
      (σ[Set.Ici a] ξ = if 0 < ξ then ⊤ else ((a * ξ : ℝ) : EReal)) := by
  constructor
  · have hinner :
        (fun x : ℝ ↦ (⟪x, ξ⟫_ℝ : EReal)) =
          fun x : ℝ ↦ ((x * ξ : ℝ) : EReal) := by
        funext x
        simp [real_inner_eq_mul]
    by_cases hξ_neg : ξ < 0
    · rw [supportFunction_eq_sSup_image, hinner, if_pos hξ_neg, EReal.eq_top_iff_forall_lt]
      intro M
      have hξ_ne : ξ ≠ 0 := ne_of_lt hξ_neg
      let t : ℝ := (|M| + |b * ξ| + 1) / (-ξ)
      have ht_nonneg : 0 ≤ t := by
        dsimp [t]
        have hden : 0 < -ξ := by linarith
        positivity
      have hmem : b - t ∈ Set.Iic b := by
        show b - t ≤ b
        linarith
      have hvalue :
          M < (b - t) * ξ := by
        have hrewrite :
            (b - t) * ξ = b * ξ + (|M| + |b * ξ| + 1) := by
          dsimp [t]
          field_simp [hξ_ne]
          ring
        rw [hrewrite]
        have hM_abs : M ≤ |M| := le_abs_self M
        have hb_abs : -( |b * ξ| ) ≤ b * ξ := neg_abs_le (b * ξ)
        linarith
      exact lt_of_lt_of_le
        (show (M : EReal) < (((b - t) * ξ : ℝ) : EReal) by
          exact_mod_cast hvalue)
        (le_sSup (Set.mem_image_of_mem (fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) hmem))
    · have hξ_nonneg : 0 ≤ ξ := le_of_not_gt hξ_neg
      have hsSup :
          sSup ((fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) '' Set.Iic b) =
            ((b * ξ : ℝ) : EReal) := by
        apply le_antisymm
        · refine sSup_le ?_
          rintro _ ⟨x, hx, rfl⟩
          exact EReal.coe_le_coe <| mul_le_mul_of_nonneg_right hx hξ_nonneg
        · exact le_sSup (Set.mem_image_of_mem (fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) (show b ∈ Set.Iic b by simp))
      rw [supportFunction_eq_sSup_image, hinner, hsSup]
      simp [hξ_neg]
  · have hinner :
        (fun x : ℝ ↦ (⟪x, ξ⟫_ℝ : EReal)) =
          fun x : ℝ ↦ ((x * ξ : ℝ) : EReal) := by
        funext x
        simp [real_inner_eq_mul]
    by_cases hξ_pos : 0 < ξ
    · rw [supportFunction_eq_sSup_image, hinner, if_pos hξ_pos, EReal.eq_top_iff_forall_lt]
      intro M
      let t : ℝ := (|M| + |a * ξ| + 1) / ξ
      have ht_nonneg : 0 ≤ t := by
        dsimp [t]
        positivity
      have hmem : a + t ∈ Set.Ici a := by
        show a ≤ a + t
        linarith
      have hvalue :
          M < (a + t) * ξ := by
        have hrewrite :
            (a + t) * ξ = a * ξ + (|M| + |a * ξ| + 1) := by
          dsimp [t]
          field_simp [hξ_pos.ne']
        rw [hrewrite]
        have hM_abs : M ≤ |M| := le_abs_self M
        have ha_abs : -( |a * ξ| ) ≤ a * ξ := neg_abs_le (a * ξ)
        linarith
      exact lt_of_lt_of_le
        (show (M : EReal) < (((a + t) * ξ : ℝ) : EReal) by
          exact_mod_cast hvalue)
        (le_sSup (Set.mem_image_of_mem (fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) hmem))
    · have hξ_nonpos : ξ ≤ 0 := le_of_not_gt hξ_pos
      have hsSup :
          sSup ((fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) '' Set.Ici a) =
            ((a * ξ : ℝ) : EReal) := by
        apply le_antisymm
        · refine sSup_le ?_
          rintro _ ⟨x, hx, rfl⟩
          exact EReal.coe_le_coe <| mul_le_mul_of_nonpos_right hx hξ_nonpos
        · exact le_sSup (Set.mem_image_of_mem (fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) (show a ∈ Set.Ici a by simp))
      rw [supportFunction_eq_sSup_image, hinner, hsSup]
      simp [hξ_pos]

/-- Helper for Theorem 24.52: the support function of a bounded interval in `ℝ` is given by the
relevant endpoint according to the sign of `ξ`. -/
private lemma supportFunction_Icc_eq_piecewise (a b ξ : ℝ) :
    a ≤ b →
      σ[Set.Icc a b] ξ = if ξ < 0 then ((a * ξ : ℝ) : EReal) else ((b * ξ : ℝ) : EReal) := by
  intro hab
  have hinner :
      (fun x : ℝ ↦ (⟪x, ξ⟫_ℝ : EReal)) =
        fun x : ℝ ↦ ((x * ξ : ℝ) : EReal) := by
      funext x
      simp [real_inner_eq_mul]
  by_cases hξ_neg : ξ < 0
  · have hanti :
        AntitoneOn (fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) (Set.Icc a b) := by
      intro x hx y hy hxy
      have hmul : y * ξ ≤ x * ξ := mul_le_mul_of_nonpos_right hxy hξ_neg.le
      simpa using (EReal.coe_le_coe hmul)
    have hsSup :
        sSup ((fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) '' Set.Icc a b) =
          (((a : ℝ) * ξ : ℝ) : EReal) :=
      AntitoneOn.sSup_image_Icc hab hanti
    rw [supportFunction_eq_sSup_image, hinner, hsSup, if_pos hξ_neg]
  · have hξ_nonneg : 0 ≤ ξ := le_of_not_gt hξ_neg
    have hmono :
        MonotoneOn (fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) (Set.Icc a b) := by
      intro x hx y hy hxy
      have hmul : x * ξ ≤ y * ξ := mul_le_mul_of_nonneg_right hxy hξ_nonneg
      simpa using (EReal.coe_le_coe hmul)
    have hsSup :
        sSup ((fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) '' Set.Icc a b) =
          (((b : ℝ) * ξ : ℝ) : EReal) :=
      MonotoneOn.sSup_image_Icc hab hmono
    rw [supportFunction_eq_sSup_image, hinner, hsSup, if_neg hξ_neg]

/-- Helper for Theorem 24.52: the constant residual branch used in the source proof. -/
private noncomputable abbrev originConstantResidual
    (φ : ℝ → Set.Ioi (⊥ : EReal)) : ℝ → Set.Ioi (⊥ : EReal) :=
  (fun _ : ℝ ↦ (φ 0 : EReal).toReal).toEReal

/-- Helper for Theorem 24.52: the source residual for the `Set.Iic b` branch. -/
private noncomputable def halflineResidualIic
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (b : ℝ) :
    ℝ → Set.Ioi (⊥ : EReal) :=
  fun ξ ↦ if ξ ≤ 0 then originConstantResidual φ ξ else affineTiltIoi φ hφ b ξ

/-- Helper for Theorem 24.52: the source residual for the `Set.Ici a` branch. -/
private noncomputable def halflineResidualIci
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (a : ℝ) :
    ℝ → Set.Ioi (⊥ : EReal) :=
  fun ξ ↦ if 0 ≤ ξ then originConstantResidual φ ξ else affineTiltIoi φ hφ a ξ

/-- Helper for Theorem 24.52: the source residual for the bounded interval `Set.Icc a b`. -/
private noncomputable def intervalResidualIcc
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (a b : ℝ) :
    ℝ → Set.Ioi (⊥ : EReal) :=
  fun ξ ↦
    if ξ < 0 then
      affineTiltIoi φ hφ a ξ
    else if 0 < ξ then
      affineTiltIoi φ hφ b ξ
    else
      originConstantResidual φ ξ

/-- Helper for Theorem 24.52: the `Set.Iic b` residual from the source proof recombines with the
support function of `Set.Iic b` to recover `φ`. -/
private lemma halflineResidualIic_add_supportFunction_eq
    {b : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIic : (∂ φ) 0 = Set.Iic b) :
    φ =
      halflineResidualIic φ hφ b +
        properIoi (σ[Set.Iic b]) (isProper_supportFunction_of_nonempty (Set.Iic b) ⟨b, by simp⟩) := by
  funext ξ
  apply Subtype.ext
  change
    (φ ξ : EReal) =
      (halflineResidualIic φ hφ b ξ : EReal) +
        σ[Set.Iic b] ξ
  have hsupport := (supportFunction_ray_eq_piecewise (a := 0) (b := b) ξ).1
  have hzero_memφ : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Iic b) ⟨b, by simp⟩ hφ hsubIic
  rcases effectiveDomain_nonneg_and_posWitness_of_subdifferentialZero_Iic hφ hsubIic with
    ⟨hdom_nonneg, _⟩
  by_cases hξ_nonpos : ξ ≤ 0
  · by_cases hξ_neg : ξ < 0
    · have hξ_not_mem : ξ ∉ effectiveDomain φ := by
        intro hξ_mem
        exact not_lt_of_ge (hdom_nonneg hξ_mem) hξ_neg
      have hφ_top : (φ ξ : EReal) = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hξ_not_mem))
      -- On the negative side, the support function is `⊤`, so the sum recovers `φ ξ = ⊤`.
      simp [halflineResidualIic, originConstantResidual, hξ_nonpos, hsupport, hξ_neg, hφ_top]
    · have hξ_zero : ξ = 0 := by linarith
      subst hξ_zero
      have hφ0_top : (φ 0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hzero_memφ)
      have hφ0_bot : (φ 0 : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (φ 0 : EReal) from (φ 0).2)
      -- At the origin, the residual is the constant value and the support function vanishes.
      simpa [halflineResidualIic, originConstantResidual, hsupport] using
        (EReal.coe_toReal hφ0_top hφ0_bot).symm
  · have hξ_pos : 0 < ξ := lt_of_not_ge hξ_nonpos
    have hσ : σ[Set.Iic b] ξ = (((b * ξ : ℝ)) : EReal) := by
      simpa [hξ_pos.ne', not_lt.mpr hξ_pos.le] using hsupport
    by_cases hξ_mem : ξ ∈ effectiveDomain φ
    · have hφξ_top : (φ ξ : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hξ_mem)
      have hφξ_bot : (φ ξ : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (φ ξ : EReal) from (φ ξ).2)
      have hsum :
          (halflineResidualIic φ hφ b ξ : EReal) + σ[Set.Iic b] ξ =
            ((((φ ξ : EReal).toReal : ℝ) : EReal)) := by
        rw [halflineResidualIic, if_neg hξ_nonpos, hσ]
        rw [affineTiltIoi_apply, affineTiltEReal_apply, real_inner_eq_mul]
        change
          (φ ξ : EReal) + (((-(ξ * b) : ℝ)) : EReal) + (((b * ξ : ℝ)) : EReal) =
            ((((φ ξ : EReal).toReal : ℝ) : EReal))
        rw [← EReal.coe_toReal hφξ_top hφξ_bot, ← EReal.coe_add, ← EReal.coe_add]
        simp
        exact_mod_cast by ring
      -- On the positive side, the affine tilt and the support value cancel exactly.
      exact (EReal.coe_toReal hφξ_top hφξ_bot).symm.trans hsum.symm
    · have hξ_tilt_not_mem : ξ ∉ effectiveDomain (affineTiltIoi φ hφ b) := by
        simpa [effectiveDomain_affineTiltIoi] using hξ_mem
      have hξ_tilt_top : (affineTiltIoi φ hφ b ξ : EReal) = ⊤ := by
        exact le_antisymm le_top
          (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hξ_tilt_not_mem))
      have hφ_top : (φ ξ : EReal) = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hξ_mem))
      -- If the positive point is outside the effective domain, both sides are `⊤`.
      rw [hφ_top, halflineResidualIic, if_neg hξ_nonpos, hξ_tilt_top, hσ]
      simpa using (EReal.top_add_of_ne_bot (EReal.coe_ne_bot (b * ξ))).symm

/-- Helper for Theorem 24.52: the `Set.Ici a` residual from the source proof recombines with the
support function of `Set.Ici a` to recover `φ`. -/
private lemma halflineResidualIci_add_supportFunction_eq
    {a : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIci : (∂ φ) 0 = Set.Ici a) :
    φ =
      halflineResidualIci φ hφ a +
        properIoi (σ[Set.Ici a]) (isProper_supportFunction_of_nonempty (Set.Ici a) ⟨a, by simp⟩) := by
  funext ξ
  apply Subtype.ext
  change
    (φ ξ : EReal) =
      (halflineResidualIci φ hφ a ξ : EReal) +
        σ[Set.Ici a] ξ
  have hsupport := (supportFunction_ray_eq_piecewise (a := a) (b := 0) ξ).2
  have hzero_memφ : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Ici a) ⟨a, by simp⟩ hφ hsubIci
  rcases effectiveDomain_nonpos_and_negWitness_of_subdifferentialZero_Ici hφ hsubIci with
    ⟨hdom_nonpos, _⟩
  by_cases hξ_nonneg : 0 ≤ ξ
  · by_cases hξ_pos : 0 < ξ
    · have hξ_not_mem : ξ ∉ effectiveDomain φ := by
        intro hξ_mem
        exact not_lt_of_ge (hdom_nonpos hξ_mem) hξ_pos
      have hφ_top : (φ ξ : EReal) = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hξ_not_mem))
      -- On the positive side, the support function is `⊤`, so the sum recovers `φ ξ = ⊤`.
      simp [halflineResidualIci, originConstantResidual, hξ_nonneg, hsupport, hξ_pos, hφ_top]
    · have hξ_zero : ξ = 0 := by linarith
      subst hξ_zero
      have hφ0_top : (φ 0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hzero_memφ)
      have hφ0_bot : (φ 0 : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (φ 0 : EReal) from (φ 0).2)
      -- At the origin, the residual is the constant value and the support function vanishes.
      simpa [halflineResidualIci, originConstantResidual, hsupport] using
        (EReal.coe_toReal hφ0_top hφ0_bot).symm
  · have hξ_neg : ξ < 0 := lt_of_not_ge hξ_nonneg
    have hσ : σ[Set.Ici a] ξ = (((a * ξ : ℝ)) : EReal) := by
      simpa [not_lt.mpr hξ_neg.le] using hsupport
    by_cases hξ_mem : ξ ∈ effectiveDomain φ
    · have hφξ_top : (φ ξ : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hξ_mem)
      have hφξ_bot : (φ ξ : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (φ ξ : EReal) from (φ ξ).2)
      have hsum :
          (halflineResidualIci φ hφ a ξ : EReal) + σ[Set.Ici a] ξ =
            ((((φ ξ : EReal).toReal : ℝ) : EReal)) := by
        rw [halflineResidualIci, if_neg hξ_nonneg, hσ]
        rw [affineTiltIoi_apply, affineTiltEReal_apply, real_inner_eq_mul]
        change
          (φ ξ : EReal) + (((-(ξ * a) : ℝ)) : EReal) + (((a * ξ : ℝ)) : EReal) =
            ((((φ ξ : EReal).toReal : ℝ) : EReal))
        rw [← EReal.coe_toReal hφξ_top hφξ_bot, ← EReal.coe_add, ← EReal.coe_add]
        simp
        exact_mod_cast by ring
      -- On the negative side, the affine tilt and the support value cancel exactly.
      exact (EReal.coe_toReal hφξ_top hφξ_bot).symm.trans hsum.symm
    · have hξ_tilt_not_mem : ξ ∉ effectiveDomain (affineTiltIoi φ hφ a) := by
        simpa [effectiveDomain_affineTiltIoi] using hξ_mem
      have hξ_tilt_top : (affineTiltIoi φ hφ a ξ : EReal) = ⊤ := by
        exact le_antisymm le_top
          (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hξ_tilt_not_mem))
      have hφ_top : (φ ξ : EReal) = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hξ_mem))
      -- If the negative point is outside the effective domain, both sides are `⊤`.
      rw [hφ_top, halflineResidualIci, if_neg hξ_nonneg, hξ_tilt_top, hσ]
      simpa using (EReal.top_add_of_ne_bot (EReal.coe_ne_bot (a * ξ))).symm

/-- Helper for Theorem 24.52: the bounded residual from the source proof recombines with the
support function of `Set.Icc a b` to recover `φ`. -/
private lemma intervalResidualIcc_add_supportFunction_eq
    {a b : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ)) (hsubIcc : (∂ φ) 0 = Set.Icc a b) :
    φ =
      intervalResidualIcc φ hφ a b +
        properIoi (σ[Set.Icc a b])
          (isProper_supportFunction_of_nonempty (Set.Icc a b) (Set.nonempty_Icc.2 hab)) := by
  funext ξ
  apply Subtype.ext
  change
    (φ ξ : EReal) =
      (intervalResidualIcc φ hφ a b ξ : EReal) +
        σ[Set.Icc a b] ξ
  have hsupport := supportFunction_Icc_eq_piecewise a b ξ hab
  have hzero_mem : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Icc a b) (Set.nonempty_Icc.2 hab) hφ hsubIcc
  by_cases hξ_neg : ξ < 0
  · by_cases hξ_mem : ξ ∈ effectiveDomain φ
    · have hφξ_top : (φ ξ : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hξ_mem)
      have hφξ_bot : (φ ξ : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (φ ξ : EReal) from (φ ξ).2)
      have hσ : σ[Set.Icc a b] ξ = (((a * ξ : ℝ)) : EReal) := by
        simpa [hξ_neg] using hsupport
      have hsum :
          (intervalResidualIcc φ hφ a b ξ : EReal) + σ[Set.Icc a b] ξ =
            ((((φ ξ : EReal).toReal : ℝ) : EReal)) := by
        rw [intervalResidualIcc, if_pos hξ_neg, hσ]
        rw [affineTiltIoi_apply, affineTiltEReal_apply, real_inner_eq_mul]
        change
          (φ ξ : EReal) + (((-(ξ * a) : ℝ)) : EReal) + (((a * ξ : ℝ)) : EReal) =
            ((((φ ξ : EReal).toReal : ℝ) : EReal))
        rw [← EReal.coe_toReal hφξ_top hφξ_bot, ← EReal.coe_add, ← EReal.coe_add]
        simp
        exact_mod_cast by ring
      -- On the negative side, the left affine tilt cancels the left support value.
      exact (EReal.coe_toReal hφξ_top hφξ_bot).symm.trans hsum.symm
    · have hξ_tilt_not_mem : ξ ∉ effectiveDomain (affineTiltIoi φ hφ a) := by
        simpa [effectiveDomain_affineTiltIoi] using hξ_mem
      have hξ_tilt_top : (affineTiltIoi φ hφ a ξ : EReal) = ⊤ := by
        exact le_antisymm le_top
          (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hξ_tilt_not_mem))
      have hφ_top : (φ ξ : EReal) = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hξ_mem))
      have hσ : σ[Set.Icc a b] ξ = (((a * ξ : ℝ)) : EReal) := by
        simpa [hξ_neg] using hsupport
      -- Outside the effective domain, the negative branch is `⊤` on both sides.
      rw [hφ_top, intervalResidualIcc, if_pos hξ_neg, hξ_tilt_top, hσ]
      simpa using (EReal.top_add_of_ne_bot (EReal.coe_ne_bot (a * ξ))).symm
  · by_cases hξ_pos : 0 < ξ
    · by_cases hξ_mem : ξ ∈ effectiveDomain φ
      · have hφξ_top : (φ ξ : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hξ_mem)
        have hφξ_bot : (φ ξ : EReal) ≠ ⊥ := by
          exact ne_of_gt (show (⊥ : EReal) < (φ ξ : EReal) from (φ ξ).2)
        have hσ : σ[Set.Icc a b] ξ = (((b * ξ : ℝ)) : EReal) := by
          simpa [not_lt.mpr hξ_pos.le] using hsupport
        have hsum :
            (intervalResidualIcc φ hφ a b ξ : EReal) + σ[Set.Icc a b] ξ =
              ((((φ ξ : EReal).toReal : ℝ) : EReal)) := by
          rw [intervalResidualIcc, if_neg hξ_neg, if_pos hξ_pos, hσ]
          rw [affineTiltIoi_apply, affineTiltEReal_apply, real_inner_eq_mul]
          change
            (φ ξ : EReal) + (((-(ξ * b) : ℝ)) : EReal) + (((b * ξ : ℝ)) : EReal) =
              ((((φ ξ : EReal).toReal : ℝ) : EReal))
          rw [← EReal.coe_toReal hφξ_top hφξ_bot, ← EReal.coe_add, ← EReal.coe_add]
          simp
          exact_mod_cast by ring
        -- On the positive side, the right affine tilt cancels the right support value.
        exact (EReal.coe_toReal hφξ_top hφξ_bot).symm.trans hsum.symm
      · have hξ_tilt_not_mem : ξ ∉ effectiveDomain (affineTiltIoi φ hφ b) := by
          simpa [effectiveDomain_affineTiltIoi] using hξ_mem
        have hξ_tilt_top : (affineTiltIoi φ hφ b ξ : EReal) = ⊤ := by
          exact le_antisymm le_top
            (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hξ_tilt_not_mem))
        have hφ_top : (φ ξ : EReal) = ⊤ := by
          exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hξ_mem))
        have hσ : σ[Set.Icc a b] ξ = (((b * ξ : ℝ)) : EReal) := by
          simpa [not_lt.mpr hξ_pos.le] using hsupport
        -- Outside the effective domain, the positive branch is `⊤` on both sides.
        rw [hφ_top, intervalResidualIcc, if_neg hξ_neg, if_pos hξ_pos, hξ_tilt_top, hσ]
        simpa using (EReal.top_add_of_ne_bot (EReal.coe_ne_bot (b * ξ))).symm
    · have hξ_zero : ξ = 0 := by linarith
      subst hξ_zero
      have hφ0_top : (φ 0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hzero_mem)
      have hφ0_bot : (φ 0 : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (φ 0 : EReal) from (φ 0).2)
      -- At the origin, the bounded residual is the constant branch and the support function is `0`.
      simpa [intervalResidualIcc, originConstantResidual, hsupport] using
        (EReal.coe_toReal hφ0_top hφ0_bot).symm

/-- Helper for Theorem 24.52: the `Set.Iic b` residual is finite on an interval around `0`. -/
private lemma zero_memInterior_effectiveDomain_halflineResidualIic
    {b : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIic : (∂ φ) 0 = Set.Iic b) :
    0 ∈ interior (effectiveDomain (halflineResidualIic φ hφ b)) := by
  have hzero_mem : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Iic b) ⟨b, by simp⟩ hφ hsubIic
  rcases effectiveDomain_nonneg_and_posWitness_of_subdifferentialZero_Iic hφ hsubIic with
    ⟨_hnonneg, p, hp_pos, hp_mem⟩
  have hsegment :
      Set.Icc (0 : ℝ) p ⊆ effectiveDomain φ := by
    intro x hx
    exact hφ.2.convex_effectiveDomain.ordConnected.out hzero_mem hp_mem hx
  rw [mem_interior_iff_mem_nhds]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1) p := by
    constructor <;> linarith
  refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds hmem) ?_
  intro x hx
  by_cases hx_nonpos : x ≤ 0
  · rw [mem_effectiveDomain_iff]
    simp [halflineResidualIic, originConstantResidual, hx_nonpos]
  · have hx_pos : 0 < x := lt_of_not_ge hx_nonpos
    have hx_memφ : x ∈ effectiveDomain φ := hsegment ⟨hx_pos.le, hx.2.le⟩
    have hx_memTilt : x ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
      simpa [effectiveDomain_affineTiltIoi] using hx_memφ
    simpa [mem_effectiveDomain_iff, halflineResidualIic, hx_nonpos] using hx_memTilt

/-- Helper for Theorem 24.52: the `Set.Ici a` residual is finite on an interval around `0`. -/
private lemma zero_memInterior_effectiveDomain_halflineResidualIci
    {a : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIci : (∂ φ) 0 = Set.Ici a) :
    0 ∈ interior (effectiveDomain (halflineResidualIci φ hφ a)) := by
  have hzero_mem : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Ici a) ⟨a, by simp⟩ hφ hsubIci
  rcases effectiveDomain_nonpos_and_negWitness_of_subdifferentialZero_Ici hφ hsubIci with
    ⟨_hnonpos, n, hn_neg, hn_mem⟩
  have hsegment :
      Set.Icc n (0 : ℝ) ⊆ effectiveDomain φ := by
    intro x hx
    exact hφ.2.convex_effectiveDomain.ordConnected.out hn_mem hzero_mem hx
  rw [mem_interior_iff_mem_nhds]
  have hmem : (0 : ℝ) ∈ Set.Ioo n 1 := by
    constructor <;> linarith
  refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds hmem) ?_
  intro x hx
  by_cases hx_nonneg : 0 ≤ x
  · rw [mem_effectiveDomain_iff]
    simp [halflineResidualIci, originConstantResidual, hx_nonneg]
  · have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
    have hx_memφ : x ∈ effectiveDomain φ := hsegment ⟨hx.1.le, hx_neg.le⟩
    have hx_memTilt : x ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
      simpa [effectiveDomain_affineTiltIoi] using hx_memφ
    simpa [mem_effectiveDomain_iff, halflineResidualIci, hx_nonneg] using hx_memTilt

/-- Helper for Theorem 24.52: the bounded residual has the same effective domain as `φ`, so the
two-sided finite witnesses place `0` in its interior. -/
private lemma effectiveDomain_intervalResidualIcc_eq
    {a b : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hzero_mem : 0 ∈ effectiveDomain φ) :
    effectiveDomain (intervalResidualIcc φ hφ a b) = effectiveDomain φ := by
  ext ξ
  by_cases hξ_neg : ξ < 0
  · -- On the negative branch, the residual is exactly the left affine tilt.
    rw [mem_effectiveDomain_iff, intervalResidualIcc, if_pos hξ_neg, mem_effectiveDomain_iff]
    have hiff : ξ ∈ effectiveDomain (affineTiltIoi φ hφ a) ↔ ξ ∈ effectiveDomain φ := by
      rw [effectiveDomain_affineTiltIoi]
    simpa [mem_effectiveDomain_iff] using hiff
  · by_cases hξ_pos : 0 < ξ
    · -- On the positive branch, the residual is exactly the right affine tilt.
      rw [mem_effectiveDomain_iff, intervalResidualIcc, if_neg hξ_neg, if_pos hξ_pos,
        mem_effectiveDomain_iff]
      have hiff : ξ ∈ effectiveDomain (affineTiltIoi φ hφ b) ↔ ξ ∈ effectiveDomain φ := by
        rw [effectiveDomain_affineTiltIoi]
      simpa [mem_effectiveDomain_iff] using hiff
    · have hξ_zero : ξ = 0 := by linarith
      subst hξ_zero
      -- At the origin, the residual is constant and `hzero_mem` supplies finiteness of `φ 0`.
      simpa [intervalResidualIcc, originConstantResidual, mem_effectiveDomain_iff] using hzero_mem

/-- Helper for Theorem 24.52: the bounded residual has the same effective domain as `φ`, so the
two-sided finite witnesses place `0` in its interior. -/
private lemma zero_memInterior_effectiveDomain_intervalResidualIcc
    {a b : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ)) (hsubIcc : (∂ φ) 0 = Set.Icc a b) :
    0 ∈ interior (effectiveDomain (intervalResidualIcc φ hφ a b)) := by
  have hzero_mem : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Icc a b) (Set.nonempty_Icc.2 hab) hφ hsubIcc
  have hdom_eq :
      effectiveDomain (intervalResidualIcc φ hφ a b) = effectiveDomain φ :=
    effectiveDomain_intervalResidualIcc_eq (φ := φ) (hφ := hφ) (a := a) (b := b) hzero_mem
  rcases effectiveDomain_twoSidedWitnesses_of_subdifferentialZero_Icc hab hφ hsubIcc with
    ⟨n, p, hn_neg, hn_mem, hp_pos, hp_mem⟩
  -- Transport the bounded residual back to the original effective domain and use convexity there.
  rw [hdom_eq]
  exact
    zero_memInterior_of_convex_with_neg_and_pos
      hφ.2.convex_effectiveDomain
      ⟨n, hn_neg, hn_mem⟩
      ⟨p, hp_pos, hp_mem⟩

/-- Helper for Theorem 24.52: a convex effective domain containing `0` and a positive point gives
an eventual right-neighborhood inside the domain. -/
private lemma effectiveDomain_mem_nhdsWithin_right_of_posWitness
    {ψ : ℝ → Set.Ioi (⊥ : EReal)}
    (hconv : Convex ℝ (effectiveDomain ψ))
    (hzero_mem : 0 ∈ effectiveDomain ψ)
    {p : ℝ} (hp_pos : 0 < p) (hp_mem : p ∈ effectiveDomain ψ) :
    effectiveDomain ψ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
  have hsegment : Set.Icc (0 : ℝ) p ⊆ effectiveDomain ψ := by
    intro x hx
    exact hconv.ordConnected.out hzero_mem hp_mem hx
  -- Intersect a small ambient neighborhood with the right filter and stay inside the segment.
  refine mem_nhdsWithin.2 ⟨Set.Iio p, isOpen_Iio, hp_pos, ?_⟩
  intro x hx
  exact hsegment ⟨hx.2.le, hx.1.le⟩

/-- Helper for Theorem 24.52: a convex effective domain containing `0` and a negative point gives
an eventual left-neighborhood inside the domain. -/
private lemma effectiveDomain_mem_nhdsWithin_left_of_negWitness
    {ψ : ℝ → Set.Ioi (⊥ : EReal)}
    (hconv : Convex ℝ (effectiveDomain ψ))
    (hzero_mem : 0 ∈ effectiveDomain ψ)
    {n : ℝ} (hn_neg : n < 0) (hn_mem : n ∈ effectiveDomain ψ) :
    effectiveDomain ψ ∈ nhdsWithin (0 : ℝ) (Set.Iio 0) := by
  have hsegment : Set.Icc n (0 : ℝ) ⊆ effectiveDomain ψ := by
    intro x hx
    exact hconv.ordConnected.out hn_mem hzero_mem hx
  -- Intersect a small ambient neighborhood with the left filter and stay inside the segment.
  refine mem_nhdsWithin.2 ⟨Set.Ioi n, isOpen_Ioi, hn_neg, ?_⟩
  intro x hx
  exact hsegment ⟨hx.1.le, hx.2.le⟩

/-- Helper for Theorem 24.52: when both quotient endpoints stay in the effective domain, the
directional difference quotient is the coercion of the corresponding real secant quotient. -/
private theorem directionalDifferenceQuotient_eq_coeToRealQuotient
    (f : ℝ → Set.Ioi (⊥ : EReal)) {x d : ℝ} (hx : x ∈ effectiveDomain f)
    (a : Set.Ioi (0 : ℝ)) (ha : x + (a : ℝ) • d ∈ effectiveDomain f) :
    directionalDifferenceQuotient f x d a =
      ((((f (x + (a : ℝ) • d) : EReal).toReal - (f x : EReal).toReal) / (a : ℝ) : ℝ) :
        EReal) := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hxa_top : (f (x + (a : ℝ) • d) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp ha)
  have hxa_bot : (f (x + (a : ℝ) • d) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + (a : ℝ) • d) : EReal) from (f _).2)
  -- Make both endpoint values finite before collapsing the quotient back to `ℝ`.
  rw [directionalDifferenceQuotient, ← EReal.coe_toReal hxa_top hxa_bot,
    ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_sub, ← EReal.coe_div]
  simp

/-- Helper for Theorem 24.52: differentiability of the finite representative at `0`, together
with local finiteness there, upgrades to lower semicontinuity of the packaged `EReal` function. -/
private lemma lowerSemicontinuousAtAsEReal_zero_of_hasDerivAtZero
    {ψ : ℝ → Set.Ioi (⊥ : EReal)}
    (hzero_int : 0 ∈ interior (effectiveDomain ψ))
    (hderiv : HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0) :
    LowerSemicontinuousAt ψ.asEReal 0 := by
  let G : ℝ → EReal := fun y ↦ (((ψ y : EReal).toReal : ℝ) : EReal)
  have hGcontAt : ContinuousAt G 0 := by
    -- The real-valued representative is continuous at `0`, and coercion preserves continuity.
    simpa [G] using (continuous_coe_real_ereal.continuousAt.comp hderiv.continuousAt)
  have hEq : G =ᶠ[nhds (0 : ℝ)] ψ.asEReal := by
    -- On a neighborhood inside the effective domain, `EReal.toReal` followed by coercion is exact.
    filter_upwards [mem_interior_iff_mem_nhds.mp hzero_int] with y hy
    have hy_top : (ψ y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (ψ y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (ψ y : EReal) from (ψ y).2)
    simpa [G, Function.asEReal_apply] using (EReal.coe_toReal hy_top hy_bot)
  -- Eventual equality transfers continuity to the packaged `EReal` spelling.
  exact (hGcontAt.congr hEq).lowerSemicontinuousAt

/-- Helper for Theorem 24.52: a source-facing right derivative with an eventual right-domain
neighborhood upgrades to a right derivative of the finite real representative. -/
private lemma hasDerivWithinAt_toReal_of_hasRightDerivativeAt_zero
    {ψ : ℝ → Set.Ioi (⊥ : EReal)}
    (hdom_right : effectiveDomain ψ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (hright : HasRightDerivativeAt ψ 0 0) :
    HasDerivWithinAt (fun y ↦ (ψ y : EReal).toReal) 0 (Set.Ioi 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  have hEq :
      Filter.EventuallyEq (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (fun y : ℝ ↦ ((((slope (fun z ↦ (ψ z : EReal).toReal) 0 y) : ℝ)) : EReal))
        (fun y : ℝ ↦ ((ψ (0 + y • (1 : ℝ)) : EReal) - (ψ 0 : EReal)) / y) := by
    -- Rewrite the source quotient into the ordinary real slope once the right branch is finite.
    filter_upwards [hdom_right, self_mem_nhdsWithin] with y hy_dom hy_pos
    have hy_dom' : 0 + y • (1 : ℝ) ∈ effectiveDomain ψ := by
      simpa [smul_eq_mul, one_mul] using hy_dom
    have hquot :=
      directionalDifferenceQuotient_eq_coeToRealQuotient
        (f := ψ) (x := 0) (d := 1) hright.1 ⟨y, hy_pos⟩ hy_dom'
    simpa [directionalDifferenceQuotient, slope_def_field, smul_eq_mul, one_mul] using hquot.symm
  have hslope_ereal :
      Filter.Tendsto
        (fun y : ℝ ↦ ((((slope (fun z ↦ (ψ z : EReal).toReal) 0 y) : ℝ)) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (0 : EReal)) := by
    exact Filter.Tendsto.congr' hEq.symm hright.2
  -- Drop the `EReal` coercion once the slope is known to stay finite near `0`.
  exact (EReal.tendsto_coe).1 hslope_ereal

/-- Helper for Theorem 24.52: a source-facing left derivative with an eventual left-domain
neighborhood upgrades to a left derivative of the finite real representative. -/
private lemma hasDerivWithinAt_toReal_of_hasLeftDerivativeAt_zero
    {ψ : ℝ → Set.Ioi (⊥ : EReal)}
    (hdom_left : effectiveDomain ψ ∈ nhdsWithin (0 : ℝ) (Set.Iio 0))
    (hleft : HasLeftDerivativeAt ψ 0 0) :
    HasDerivWithinAt (fun y ↦ (ψ y : EReal).toReal) 0 (Set.Iio 0) 0 := by
  let ψneg : ℝ → Set.Ioi (⊥ : EReal) := fun y ↦ ψ (-y)
  have hmaps_right : Set.MapsTo Neg.neg (Set.Ioi (0 : ℝ)) (Set.Iio 0) := by
    intro y hy
    show -y < 0
    have hy' : 0 < y := hy
    linarith
  have hdom_neg : effectiveDomain ψneg ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    have hneg_tendsto :
        Filter.Tendsto Neg.neg (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin (0 : ℝ) (Set.Iio 0)) := by
      simpa using
        (ContinuousWithinAt.tendsto_nhdsWithin
          (hasDerivWithinAt_neg (s := Set.Ioi (0 : ℝ)) (x := (0 : ℝ))).continuousWithinAt
          hmaps_right)
    have hpre : Neg.neg ⁻¹' effectiveDomain ψ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      hneg_tendsto hdom_left
    simpa [ψneg, effectiveDomain, Set.preimage, Set.mem_setOf_eq]
      using hpre
  have hright_neg : HasRightDerivativeAt ψneg 0 0 := by
    -- Route correction: convert the left derivative into a right derivative after precomposing
    -- by `Neg.neg`, then reuse the right-hand bridge instead of redoing the filter algebra.
    refine ⟨?_, ?_⟩
    · simpa [ψneg, mem_effectiveDomain_iff] using hleft.1
    · simpa [ψneg, HasRightDerivativeAt, HasLeftDerivativeAt, HasDirectionalDerivativeAt,
        smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hleft.2
  have hderiv_neg :
      HasDerivWithinAt (fun y ↦ (ψneg y : EReal).toReal) 0 (Set.Ioi 0) 0 :=
    hasDerivWithinAt_toReal_of_hasRightDerivativeAt_zero hdom_neg hright_neg
  have hmaps_left : Set.MapsTo Neg.neg (Set.Iio (0 : ℝ)) (Set.Ioi 0) := by
    intro y hy
    show 0 < -y
    have hy' : y < 0 := hy
    linarith
  have hderiv_neg' :
      HasDerivWithinAt (fun y ↦ (ψneg y : EReal).toReal) 0 (Set.Ioi 0) (-0) := by
    simpa using hderiv_neg
  have hpullIic :
      HasDerivWithinAt ((fun y ↦ (ψneg y : EReal).toReal) ∘ Neg.neg) 0 (Set.Iic 0) 0 := by
    simpa using
      hderiv_neg'.comp (x := 0)
        (hasDerivWithinAt_neg (s := Set.Iio (0 : ℝ)) (x := (0 : ℝ)))
        hmaps_left
  have hpull :
      HasDerivWithinAt ((fun y ↦ (ψneg y : EReal).toReal) ∘ Neg.neg) 0 (Set.Iio 0) 0 :=
    hpullIic.Iio_of_Iic
  -- Composing twice with negation recovers the original finite representative on the left side.
  convert hpull using 1
  ext y
  simp [ψneg, Function.comp]

/-- Helper for Theorem 24.52: matching within-derivatives on `Set.Iic 0` and `Set.Ioi 0` glue to
an ordinary derivative at `0`. -/
private lemma hasDerivAt_zero_of_hasDerivWithinAt_Iic_Ioi
    {f : ℝ → ℝ} {f' : ℝ}
    (hleft : HasDerivWithinAt f f' (Set.Iic 0) 0)
    (hright : HasDerivWithinAt f f' (Set.Ioi 0) 0) :
    HasDerivAt f f' 0 := by
  have hunion : HasDerivWithinAt f f' (Set.Iic 0 ∪ Set.Ioi 0) 0 :=
    hleft.union hright
  have huniv : HasDerivWithinAt f f' Set.univ 0 := by
    simpa [Set.Iic_union_Ioi] using hunion
  exact (hasDerivWithinAt_univ.mp huniv)

/-- Helper for Theorem 24.52: at the origin, affine tilting preserves the finite value `φ 0`
after passing through `EReal.toReal`. -/
private lemma affineTiltIoi_zero_asEReal'
    {u : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hzero_mem : 0 ∈ effectiveDomain φ) :
    (affineTiltIoi φ hφ u 0 : EReal) = ((((φ 0 : EReal).toReal : ℝ)) : EReal) := by
  rw [affineTiltIoi_apply, affineTiltEReal_apply, real_inner_eq_mul]
  have hφ0_top : (φ 0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hzero_mem)
  have hφ0_bot : (φ 0 : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (φ 0 : EReal) from (φ 0).2)
  simpa using (EReal.coe_toReal hφ0_top hφ0_bot).symm

/-- Helper for Theorem 24.52: the `Set.Iic b` residual has derivative `0` at the origin on its
finite real representative. -/
private lemma halflineResidualIic_hasDerivAtZero
    {b : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIic : (∂ φ) 0 = Set.Iic b) :
    HasDerivAt (fun y ↦ (halflineResidualIic φ hφ b y : EReal).toReal) 0 0 := by
  have hzero_mem : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Iic b) ⟨b, by simp⟩ hφ hsubIic
  have hleft_const :
      HasDerivWithinAt (fun y ↦ (originConstantResidual φ y : EReal).toReal) 0 (Set.Iic 0) 0 := by
    -- The nonpositive branch is literally constant.
    simpa [originConstantResidual] using
      (hasDerivWithinAt_const (s := Set.Iic (0 : ℝ)) (x := (0 : ℝ))
        (c := (φ 0 : EReal).toReal))
  have hleft_residual :
      HasDerivWithinAt (fun y ↦ (halflineResidualIic φ hφ b y : EReal).toReal) 0 (Set.Iic 0) 0 := by
    have hEq :
        Filter.EventuallyEq (nhdsWithin (0 : ℝ) (Set.Iic 0))
          (fun y ↦ (halflineResidualIic φ hφ b y : EReal).toReal)
          (fun y ↦ (originConstantResidual φ y : EReal).toReal) := by
      apply eventuallyEq_nhdsWithin_of_eqOn
      intro y hy
      have hy_nonpos : y ≤ 0 := hy
      simpa using congrArg EReal.toReal
        (show (halflineResidualIic φ hφ b y : EReal) = (originConstantResidual φ y : EReal) by
          simp [halflineResidualIic, hy_nonpos])
    exact hleft_const.congr_of_eventuallyEq_of_mem hEq (by simp)
  have htilt_gamma :
      affineTiltIoi φ hφ b ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) b
  rcases effectiveDomain_nonneg_and_posWitness_of_subdifferentialZero_Iic hφ hsubIic with
    ⟨_, p, hp_pos, hp_mem⟩
  have hzero_mem_tilt : 0 ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
    simpa [effectiveDomain_affineTiltIoi] using hzero_mem
  have hp_mem_tilt : p ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
    simpa [effectiveDomain_affineTiltIoi] using hp_mem
  have hdom_right :
      effectiveDomain (affineTiltIoi φ hφ b) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    effectiveDomain_mem_nhdsWithin_right_of_posWitness
      htilt_gamma.2.convex_effectiveDomain hzero_mem_tilt hp_pos hp_mem_tilt
  have hright_tilt :
      HasDerivWithinAt (fun y ↦ (affineTiltIoi φ hφ b y : EReal).toReal) 0 (Set.Ioi 0) 0 :=
    hasDerivWithinAt_toReal_of_hasRightDerivativeAt_zero hdom_right
      (affineTilt_hasRightDerivativeAtZero_of_subdifferentialZero_eq_Iic
        (φ := φ) (hφ := hφ) hsubIic)
  have hzero_eq :
      (fun y ↦ (halflineResidualIic φ hφ b y : EReal).toReal) 0 =
        (fun y ↦ (affineTiltIoi φ hφ b y : EReal).toReal) 0 := by
    have hEqE :
        (halflineResidualIic φ hφ b 0 : EReal) = (affineTiltIoi φ hφ b 0 : EReal) := by
      rw [halflineResidualIic, if_pos (show (0 : ℝ) ≤ 0 by simp)]
      simpa using
        (affineTiltIoi_zero_asEReal' (φ := φ) (hφ := hφ) (hzero_mem := hzero_mem) (u := b)).symm
    exact congrArg EReal.toReal hEqE
  have hright_residual :
      HasDerivWithinAt (fun y ↦ (halflineResidualIic φ hφ b y : EReal).toReal) 0 (Set.Ioi 0) 0 := by
    have hEq :
        Filter.EventuallyEq (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (fun y ↦ (halflineResidualIic φ hφ b y : EReal).toReal)
          (fun y ↦ (affineTiltIoi φ hφ b y : EReal).toReal) := by
      apply eventuallyEq_nhdsWithin_of_eqOn
      intro y hy
      have hy_pos : 0 < y := hy
      simpa using congrArg EReal.toReal
        (show (halflineResidualIic φ hφ b y : EReal) = (affineTiltIoi φ hφ b y : EReal) by
          simp [halflineResidualIic, not_le.mpr hy_pos])
    exact hright_tilt.congr_of_eventuallyEq hEq hzero_eq
  -- Glue the left constant branch and the right affine-tilt branch across the origin.
  exact hasDerivAt_zero_of_hasDerivWithinAt_Iic_Ioi hleft_residual hright_residual

/-- Helper for Theorem 24.52: the `Set.Ici a` residual has derivative `0` at the origin on its
finite real representative. -/
private lemma halflineResidualIci_hasDerivAtZero
    {a : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIci : (∂ φ) 0 = Set.Ici a) :
    HasDerivAt (fun y ↦ (halflineResidualIci φ hφ a y : EReal).toReal) 0 0 := by
  have hzero_mem : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Ici a) ⟨a, by simp⟩ hφ hsubIci
  have htilt_gamma :
      affineTiltIoi φ hφ a ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) a
  rcases effectiveDomain_nonpos_and_negWitness_of_subdifferentialZero_Ici hφ hsubIci with
    ⟨_, n, hn_neg, hn_mem⟩
  have hzero_mem_tilt : 0 ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
    simpa [effectiveDomain_affineTiltIoi] using hzero_mem
  have hn_mem_tilt : n ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
    simpa [effectiveDomain_affineTiltIoi] using hn_mem
  have hdom_left :
      effectiveDomain (affineTiltIoi φ hφ a) ∈ nhdsWithin (0 : ℝ) (Set.Iio 0) :=
    effectiveDomain_mem_nhdsWithin_left_of_negWitness
      htilt_gamma.2.convex_effectiveDomain hzero_mem_tilt hn_neg hn_mem_tilt
  have hleft_tilt_iio :
      HasDerivWithinAt (fun y ↦ (affineTiltIoi φ hφ a y : EReal).toReal) 0 (Set.Iio 0) 0 :=
    hasDerivWithinAt_toReal_of_hasLeftDerivativeAt_zero hdom_left
      (affineTilt_hasLeftDerivativeAtZero_of_subdifferentialZero_eq_Ici
        (φ := φ) (hφ := hφ) hsubIci)
  have hleft_tilt :
      HasDerivWithinAt (fun y ↦ (affineTiltIoi φ hφ a y : EReal).toReal) 0 (Set.Iic 0) 0 :=
    hleft_tilt_iio.Iic_of_Iio
  have hzero_eq_left :
      (fun y ↦ (halflineResidualIci φ hφ a y : EReal).toReal) 0 =
        (fun y ↦ (affineTiltIoi φ hφ a y : EReal).toReal) 0 := by
    have hEqE :
        (halflineResidualIci φ hφ a 0 : EReal) = (affineTiltIoi φ hφ a 0 : EReal) := by
      rw [halflineResidualIci, if_pos (show (0 : ℝ) ≤ 0 by simp)]
      simpa using
        (affineTiltIoi_zero_asEReal' (φ := φ) (hφ := hφ) (hzero_mem := hzero_mem) (u := a)).symm
    exact congrArg EReal.toReal hEqE
  have hleft_residual :
      HasDerivWithinAt (fun y ↦ (halflineResidualIci φ hφ a y : EReal).toReal) 0 (Set.Iic 0) 0 := by
    have hEq :
        Filter.EventuallyEq (nhdsWithin (0 : ℝ) (Set.Iic 0))
          (fun y ↦ (halflineResidualIci φ hφ a y : EReal).toReal)
          (fun y ↦ (affineTiltIoi φ hφ a y : EReal).toReal) := by
      apply eventuallyEq_nhdsWithin_of_eqOn
      intro y hy
      by_cases hy_neg : y < 0
      · simpa using congrArg EReal.toReal
          (show (halflineResidualIci φ hφ a y : EReal) = (affineTiltIoi φ hφ a y : EReal) by
            simp [halflineResidualIci, not_le.mpr hy_neg])
      · have hy_zero : y = 0 := by
          exact le_antisymm hy (le_of_not_gt hy_neg)
        subst hy_zero
        exact hzero_eq_left
    exact hleft_tilt.congr_of_eventuallyEq_of_mem hEq (by simp)
  have hright_const :
      HasDerivWithinAt (fun y ↦ (originConstantResidual φ y : EReal).toReal) 0 (Set.Ioi 0) 0 := by
    -- The nonnegative branch is constant on the right.
    simpa [originConstantResidual] using
      (hasDerivWithinAt_const (s := Set.Ioi (0 : ℝ)) (x := (0 : ℝ))
        (c := (φ 0 : EReal).toReal))
  have hright_residual :
      HasDerivWithinAt (fun y ↦ (halflineResidualIci φ hφ a y : EReal).toReal) 0 (Set.Ioi 0) 0 := by
    have hEq :
        Filter.EventuallyEq (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (fun y ↦ (halflineResidualIci φ hφ a y : EReal).toReal)
          (fun y ↦ (originConstantResidual φ y : EReal).toReal) := by
      apply eventuallyEq_nhdsWithin_of_eqOn
      intro y hy
      have hy_pos : 0 < y := hy
      simpa using congrArg EReal.toReal
        (show (halflineResidualIci φ hφ a y : EReal) = (originConstantResidual φ y : EReal) by
          simp [halflineResidualIci, hy_pos.le])
    exact hright_const.congr_of_eventuallyEq hEq (by simp [halflineResidualIci, originConstantResidual])
  -- Glue the left affine-tilt branch and the constant right branch across the origin.
  exact hasDerivAt_zero_of_hasDerivWithinAt_Iic_Ioi hleft_residual hright_residual

/-- Helper for Theorem 24.52: the bounded residual has derivative `0` at the origin on its finite
real representative. -/
private lemma intervalResidualIcc_hasDerivAtZero
    {a b : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ)) (hsubIcc : (∂ φ) 0 = Set.Icc a b) :
    HasDerivAt (fun y ↦ (intervalResidualIcc φ hφ a b y : EReal).toReal) 0 0 := by
  have hzero_mem : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Icc a b) (Set.nonempty_Icc.2 hab) hφ hsubIcc
  have hleft_gamma :
      affineTiltIoi φ hφ a ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) a
  have hright_gamma :
      affineTiltIoi φ hφ b ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) b
  rcases effectiveDomain_twoSidedWitnesses_of_subdifferentialZero_Icc hab hφ hsubIcc with
    ⟨n, p, hn_neg, hn_mem, hp_pos, hp_mem⟩
  have hzero_left : 0 ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
    simpa [effectiveDomain_affineTiltIoi] using hzero_mem
  have hzero_right : 0 ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
    simpa [effectiveDomain_affineTiltIoi] using hzero_mem
  have hn_mem_left : n ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
    simpa [effectiveDomain_affineTiltIoi] using hn_mem
  have hp_mem_right : p ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
    simpa [effectiveDomain_affineTiltIoi] using hp_mem
  have hdom_left :
      effectiveDomain (affineTiltIoi φ hφ a) ∈ nhdsWithin (0 : ℝ) (Set.Iio 0) :=
    effectiveDomain_mem_nhdsWithin_left_of_negWitness
      hleft_gamma.2.convex_effectiveDomain hzero_left hn_neg hn_mem_left
  have hdom_right :
      effectiveDomain (affineTiltIoi φ hφ b) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    effectiveDomain_mem_nhdsWithin_right_of_posWitness
      hright_gamma.2.convex_effectiveDomain hzero_right hp_pos hp_mem_right
  have hleft_tilt_iio :
      HasDerivWithinAt (fun y ↦ (affineTiltIoi φ hφ a y : EReal).toReal) 0 (Set.Iio 0) 0 :=
    hasDerivWithinAt_toReal_of_hasLeftDerivativeAt_zero hdom_left
      (affineTilt_hasLeftDerivativeAtZero_of_subdifferentialZero_eq_Icc
        (φ := φ) (hab := hab) (hφ := hφ) hsubIcc)
  have hleft_tilt :
      HasDerivWithinAt (fun y ↦ (affineTiltIoi φ hφ a y : EReal).toReal) 0 (Set.Iic 0) 0 :=
    hleft_tilt_iio.Iic_of_Iio
  have hzero_eq_left :
      (fun y ↦ (intervalResidualIcc φ hφ a b y : EReal).toReal) 0 =
        (fun y ↦ (affineTiltIoi φ hφ a y : EReal).toReal) 0 := by
    have hEqE :
        (intervalResidualIcc φ hφ a b 0 : EReal) = (affineTiltIoi φ hφ a 0 : EReal) := by
      simp [intervalResidualIcc]
      simpa using
        (affineTiltIoi_zero_asEReal' (φ := φ) (hφ := hφ) (hzero_mem := hzero_mem) (u := a)).symm
    exact congrArg EReal.toReal hEqE
  have hleft_residual :
      HasDerivWithinAt (fun y ↦ (intervalResidualIcc φ hφ a b y : EReal).toReal) 0 (Set.Iic 0) 0 := by
    have hEq :
        Filter.EventuallyEq (nhdsWithin (0 : ℝ) (Set.Iic 0))
          (fun y ↦ (intervalResidualIcc φ hφ a b y : EReal).toReal)
          (fun y ↦ (affineTiltIoi φ hφ a y : EReal).toReal) := by
      apply eventuallyEq_nhdsWithin_of_eqOn
      intro y hy
      by_cases hy_neg : y < 0
      · simpa using congrArg EReal.toReal
          (show (intervalResidualIcc φ hφ a b y : EReal) = (affineTiltIoi φ hφ a y : EReal) by
            simp [intervalResidualIcc, hy_neg])
      · have hy_zero : y = 0 := by
          exact le_antisymm hy (le_of_not_gt hy_neg)
        subst hy_zero
        exact hzero_eq_left
    exact hleft_tilt.congr_of_eventuallyEq_of_mem hEq (by simp)
  have hright_tilt :
      HasDerivWithinAt (fun y ↦ (affineTiltIoi φ hφ b y : EReal).toReal) 0 (Set.Ioi 0) 0 :=
    hasDerivWithinAt_toReal_of_hasRightDerivativeAt_zero hdom_right
      (affineTilt_hasRightDerivativeAtZero_of_subdifferentialZero_eq_Icc
        (φ := φ) (hab := hab) (hφ := hφ) hsubIcc)
  have hzero_eq_right :
      (fun y ↦ (intervalResidualIcc φ hφ a b y : EReal).toReal) 0 =
        (fun y ↦ (affineTiltIoi φ hφ b y : EReal).toReal) 0 := by
    have hEqE :
        (intervalResidualIcc φ hφ a b 0 : EReal) = (affineTiltIoi φ hφ b 0 : EReal) := by
      simp [intervalResidualIcc]
      simpa using
        (affineTiltIoi_zero_asEReal' (φ := φ) (hφ := hφ) (hzero_mem := hzero_mem) (u := b)).symm
    exact congrArg EReal.toReal hEqE
  have hright_residual :
      HasDerivWithinAt (fun y ↦ (intervalResidualIcc φ hφ a b y : EReal).toReal) 0 (Set.Ioi 0) 0 := by
    have hEq :
        Filter.EventuallyEq (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (fun y ↦ (intervalResidualIcc φ hφ a b y : EReal).toReal)
          (fun y ↦ (affineTiltIoi φ hφ b y : EReal).toReal) := by
      apply eventuallyEq_nhdsWithin_of_eqOn
      intro y hy
      have hy_pos : 0 < y := hy
      simpa using congrArg EReal.toReal
        (show (intervalResidualIcc φ hφ a b y : EReal) = (affineTiltIoi φ hφ b y : EReal) by
          simp [intervalResidualIcc, hy_pos, not_lt.mpr hy_pos.le])
    exact hright_tilt.congr_of_eventuallyEq hEq hzero_eq_right
  -- Glue the left and right affine-tilt branches after normalizing the origin value.
  exact hasDerivAt_zero_of_hasDerivWithinAt_Iic_Ioi hleft_residual hright_residual

/-- Helper for Theorem 24.52: lower semicontinuity transfers across eventual equality on a
neighborhood. -/
private lemma lowerSemicontinuousAt_congr
    {f g : ℝ → EReal} {x : ℝ}
    (hf : LowerSemicontinuousAt f x) (hEq : f =ᶠ[nhds x] g) :
    LowerSemicontinuousAt g x := by
  intro y hy
  have hEqx : f x = g x := hEq.eq_of_nhds
  have hy' : f x > y := by
    simpa [hEqx] using hy
  -- Rewrite the pointwise lower-semicontinuity test through the eventual equality.
  filter_upwards [hf y hy', hEq] with z hz hzEq
  simpa [hzEq] using hz

/-- Helper for Theorem 24.52: on the nonpositive half-line, `halflineResidualIic` is the constant
branch from the source proof. -/
private lemma halflineResidualIic_apply_of_nonpos
    {b x : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hx : x ≤ 0) :
    halflineResidualIic φ hφ b x = originConstantResidual φ x := by
  -- The `Iic` residual chooses the constant branch on `(-∞, 0]`.
  simp [halflineResidualIic, hx]

/-- Helper for Theorem 24.52: on the positive half-line, `halflineResidualIic` agrees with the
tilted branch. -/
private lemma halflineResidualIic_apply_of_pos
    {b x : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hx : 0 < x) :
    halflineResidualIic φ hφ b x = affineTiltIoi φ hφ b x := by
  simp [halflineResidualIic, not_le.mpr hx]

/-- Helper for Theorem 24.52: on the nonnegative half-line, `halflineResidualIci` is the constant
branch from the source proof. -/
private lemma halflineResidualIci_apply_of_nonneg
    {a x : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hx : 0 ≤ x) :
    halflineResidualIci φ hφ a x = originConstantResidual φ x := by
  -- The `Ici` residual chooses the constant branch on `[0, ∞)`.
  simp [halflineResidualIci, hx]

/-- Helper for Theorem 24.52: on the negative half-line, `halflineResidualIci` agrees with the
tilted branch. -/
private lemma halflineResidualIci_apply_of_neg
    {a x : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hx : x < 0) :
    halflineResidualIci φ hφ a x = affineTiltIoi φ hφ a x := by
  simp [halflineResidualIci, not_le.mpr hx]

/-- Helper for Theorem 24.52: on the negative half-line, the bounded residual agrees with its
left affine-tilt branch. -/
private lemma intervalResidualIcc_apply_of_neg
    {a b x : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hx : x < 0) :
    intervalResidualIcc φ hφ a b x = affineTiltIoi φ hφ a x := by
  simp [intervalResidualIcc, hx]

/-- Helper for Theorem 24.52: on the positive half-line, the bounded residual agrees with its
right affine-tilt branch. -/
private lemma intervalResidualIcc_apply_of_pos
    {a b x : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hx : 0 < x) :
    intervalResidualIcc φ hφ a b x = affineTiltIoi φ hφ b x := by
  simp [intervalResidualIcc, hx, not_lt.mpr hx.le]

/-- Helper for Theorem 24.52: every finite point of `φ` lies above the affine support plane at
`0`, so the affine tilt dominates the constant residual value. -/
private lemma originConstantResidual_le_affineTiltIoi_of_mem_subdifferential_zero
    {u x : ℝ} (hφ : φ ∈ Γ₀(ℝ))
    (hzero_mem : 0 ∈ effectiveDomain φ) (hx : x ∈ effectiveDomain φ) (hu : u ∈ (∂ φ) 0) :
    (originConstantResidual φ x : EReal) ≤ affineTiltIoi φ hφ u x := by
  have hreal :
      ((φ 0 : EReal).toReal : ℝ) ≤ (φ x : EReal).toReal - x * u := by
    -- Repackage the real subgradient inequality at `0` into the tilted source normalization.
    have hineq :=
      real_subgradient_inequality_at_zero
        (φ := φ) (u := u) (x := x) hzero_mem hx hu
    linarith
  have hx_top : (φ x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (φ x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (φ x : EReal) from (φ x).2)
  have htilt :
      (affineTiltIoi φ hφ u x : EReal) =
        (((φ x : EReal).toReal - x * u : ℝ) : EReal) := by
    -- Once the point is finite, the affine tilt is just real subtraction followed by coercion.
    rw [affineTiltIoi_apply]
    have hvalue :
        affineTiltEReal (fun y : ℝ ↦ (φ y : EReal)) u x =
          (((φ x : EReal).toReal - x * u : ℝ) : EReal) := by
      rw [affineTiltEReal_apply, real_inner_eq_mul, ← EReal.coe_toReal hx_top hx_bot,
        ← EReal.coe_add]
      simp [sub_eq_add_neg]
    simpa using hvalue
  -- Cast the real support-plane inequality back to `EReal`.
  have hcast :
      (((φ 0 : EReal).toReal : ℝ) : EReal) ≤
        (((φ x : EReal).toReal - x * u : ℝ) : EReal) := by
    exact_mod_cast hreal
  rw [originConstantResidual, htilt]
  exact hcast

/-- Helper for Theorem 24.52: a finite value can be rewritten as the coercion of its real
representative. -/
private lemma value_eq_coe_toReal_of_mem_effectiveDomain
    {f : ℝ → Set.Ioi (⊥ : EReal)} {x : ℝ} (hx : x ∈ effectiveDomain f) :
    (f x : EReal) = ((((f x : EReal).toReal : ℝ)) : EReal) := by
  have htop : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hbot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  simpa using (EReal.coe_toReal htop hbot).symm

/-- Helper for Theorem 24.52: the constant residual is the coercion of the finite value `φ 0`. -/
private lemma originConstantResidual_asEReal
    (x : ℝ) :
    (originConstantResidual φ x : EReal) = ((((φ 0 : EReal).toReal : ℝ)) : EReal) := by
  simp [originConstantResidual]

/-- Helper for Theorem 24.52: the affine tilt agrees with the constant residual at the origin. -/
private lemma affineTiltIoi_zero_asEReal
    {u : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hzero_mem : 0 ∈ effectiveDomain φ) :
    (affineTiltIoi φ hφ u 0 : EReal) = ((((φ 0 : EReal).toReal : ℝ)) : EReal) := by
  have hφ0_top : (φ 0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hzero_mem)
  have hφ0_bot : (φ 0 : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (φ 0 : EReal) from (φ 0).2)
  -- Unfold the affine tilt at `0`, where the linear correction vanishes.
  rw [affineTiltIoi_apply, affineTiltEReal_apply, real_inner_eq_mul]
  simpa using (EReal.coe_toReal hφ0_top hφ0_bot).symm

/-- Helper for Theorem 24.52: the support-plane inequality can be read on real representatives of
the finite affine tilt. -/
private lemma originConstantResidual_le_affineTiltIoi_toReal_of_mem_subdifferential_zero
    {u x : ℝ} (hφ : φ ∈ Γ₀(ℝ))
    (hzero_mem : 0 ∈ effectiveDomain φ) (hx : x ∈ effectiveDomain φ) (hu : u ∈ (∂ φ) 0) :
    (φ 0 : EReal).toReal ≤ (affineTiltIoi φ hφ u x : EReal).toReal := by
  have hx_tilt : x ∈ effectiveDomain (affineTiltIoi φ hφ u) := by
    simpa [effectiveDomain_affineTiltIoi] using hx
  have hbound :=
    originConstantResidual_le_affineTiltIoi_of_mem_subdifferential_zero
      (hφ := hφ) hzero_mem hx hu
  -- Rewrite both finite values through their `toReal` representatives before dropping to `ℝ`.
  rw [originConstantResidual_asEReal (φ := φ) (x := x),
    value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ u) hx_tilt] at hbound
  exact_mod_cast hbound

/-- Helper for Theorem 24.52: a real convex combination of finite values is computed in `EReal`
by coercing the real convex combination. -/
private lemma ereal_convexCombination_eq
    (α s t : ℝ) :
    (α : EReal) * ((s : ℝ) : EReal) + (1 - α : EReal) * ((t : ℝ) : EReal) =
      (((α * s + (1 - α) * t : ℝ)) : EReal) := by
  have hsub : (1 - (α : EReal)) = (((1 - α : ℝ)) : EReal) := by
    norm_num
  rw [hsub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]

/-- Helper for Theorem 24.52: if a larger finite endpoint receives a larger weight, the
corresponding real convex combination increases. -/
private lemma ereal_convexCombination_mono_of_weight
    {c d α β : ℝ} (hcd : c ≤ d) (hαβ : α ≤ β) :
    (((α * d + (1 - α) * c : ℝ)) : EReal) ≤
      (((β * d + (1 - β) * c : ℝ)) : EReal) := by
  have hstep : 0 ≤ (β - α) * (d - c) := by
    exact mul_nonneg (sub_nonneg.mpr hαβ) (sub_nonneg.mpr hcd)
  have hreal :
      α * d + (1 - α) * c ≤ β * d + (1 - β) * c := by
    linarith
  exact_mod_cast hreal

/-- Helper for Theorem 24.52: the `Set.Iic b` residual is finite exactly on the nonpositive
half-line together with the original effective domain. -/
private lemma effectiveDomain_halflineResidualIic_eq
    {b : ℝ} (hφ : φ ∈ Γ₀(ℝ)) :
    effectiveDomain (halflineResidualIic φ hφ b) = Set.Iic 0 ∪ effectiveDomain φ := by
  ext x
  by_cases hx_nonpos : x ≤ 0
  · constructor
    · intro _
      exact Or.inl hx_nonpos
    · intro _
      -- On the constant branch, finiteness is automatic.
      rw [mem_effectiveDomain_iff,
        halflineResidualIic_apply_of_nonpos (φ := φ) (hφ := hφ) (b := b) hx_nonpos]
      simp [originConstantResidual]
  · have hx_pos : 0 < x := lt_of_not_ge hx_nonpos
    rw [mem_effectiveDomain_iff,
      halflineResidualIic_apply_of_pos (φ := φ) (hφ := hφ) (b := b) hx_pos]
    have hiff : x ∈ effectiveDomain (affineTiltIoi φ hφ b) ↔ x ∈ effectiveDomain φ := by
      rw [effectiveDomain_affineTiltIoi]
    -- On the positive branch, the residual has the same effective domain as the affine tilt.
    simpa [mem_effectiveDomain_iff, hx_nonpos] using hiff

/-- Helper for Theorem 24.52: the `Set.Ici a` residual is finite exactly on the nonnegative
half-line together with the original effective domain. -/
private lemma effectiveDomain_halflineResidualIci_eq
    {a : ℝ} (hφ : φ ∈ Γ₀(ℝ)) :
    effectiveDomain (halflineResidualIci φ hφ a) = Set.Ici 0 ∪ effectiveDomain φ := by
  ext x
  by_cases hx_nonneg : 0 ≤ x
  · constructor
    · intro _
      exact Or.inl hx_nonneg
    · intro _
      -- On the constant branch, finiteness is automatic.
      rw [mem_effectiveDomain_iff,
        halflineResidualIci_apply_of_nonneg (φ := φ) (hφ := hφ) (a := a) hx_nonneg]
      simp [originConstantResidual]
  · have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
    rw [mem_effectiveDomain_iff,
      halflineResidualIci_apply_of_neg (φ := φ) (hφ := hφ) (a := a) hx_neg]
    have hiff : x ∈ effectiveDomain (affineTiltIoi φ hφ a) ↔ x ∈ effectiveDomain φ := by
      rw [effectiveDomain_affineTiltIoi]
    -- On the negative branch, the residual has the same effective domain as the affine tilt.
    simpa [mem_effectiveDomain_iff, hx_nonneg] using hiff

/-- Helper for Theorem 24.52: adjoining a convex nonnegative tail to the nonpositive half-line
preserves convexity. -/
private lemma convex_iic_union_of_convex_subset_nonneg
    {S : Set ℝ} (hconv : Convex ℝ S) (hsubset : S ⊆ Set.Ici 0) (hzero : 0 ∈ S) :
    Convex ℝ (Set.Iic 0 ∪ S) := by
  have hS_ord : S.OrdConnected := hconv.ordConnected
  -- The union stays order connected because every mixed-sign interval passes through `0 ∈ S`.
  have hOrd : (Set.Iic 0 ∪ S).OrdConnected := by
    refine Set.ordConnected_iff_uIcc_subset.2 ?_
    intro x hx y hy z hz
    rcases hx with hx_nonpos | hx_mem
    · rcases hy with hy_nonpos | hy_mem
      · left
        rcases le_total x y with hxy | hyx
        · have hz_mem : z ∈ Set.Icc x y := by
            simpa [Set.uIcc_of_le hxy] using hz
          exact le_trans hz_mem.2 hy_nonpos
        · have hz_mem : z ∈ Set.Icc y x := by
            simpa [Set.uIcc_of_ge hyx] using hz
          exact le_trans hz_mem.2 hx_nonpos
      · have hy_nonneg : 0 ≤ y := hsubset hy_mem
        have hxy : x ≤ y := le_trans hx_nonpos hy_nonneg
        have hz_mem : z ∈ Set.Icc x y := by
          simpa [Set.uIcc_of_le hxy] using hz
        by_cases hz_nonpos : z ≤ 0
        · exact Or.inl hz_nonpos
        · right
          have hz_nonneg : 0 ≤ z := (lt_of_not_ge hz_nonpos).le
          exact hS_ord.out hzero hy_mem ⟨hz_nonneg, hz_mem.2⟩
    · rcases hy with hy_nonpos | hy_mem
      · have hx_nonneg : 0 ≤ x := hsubset hx_mem
        have hyx : y ≤ x := le_trans hy_nonpos hx_nonneg
        have hz_mem : z ∈ Set.Icc y x := by
          simpa [Set.uIcc_of_ge hyx] using hz
        by_cases hz_nonpos : z ≤ 0
        · exact Or.inl hz_nonpos
        · right
          have hz_nonneg : 0 ≤ z := (lt_of_not_ge hz_nonpos).le
          exact hS_ord.out hzero hx_mem ⟨hz_nonneg, hz_mem.2⟩
      · right
        rcases le_total x y with hxy | hyx
        · have hz_mem : z ∈ Set.Icc x y := by
            simpa [Set.uIcc_of_le hxy] using hz
          exact hS_ord.out hx_mem hy_mem hz_mem
        · have hz_mem : z ∈ Set.Icc y x := by
            simpa [Set.uIcc_of_ge hyx] using hz
          exact hS_ord.out hy_mem hx_mem hz_mem
  exact hOrd.convex

/-- Helper for Theorem 24.52: adjoining a convex nonpositive tail to the nonnegative half-line
preserves convexity. -/
private lemma convex_ici_union_of_convex_subset_nonpos
    {S : Set ℝ} (hconv : Convex ℝ S) (hsubset : S ⊆ Set.Iic 0) (hzero : 0 ∈ S) :
    Convex ℝ (Set.Ici 0 ∪ S) := by
  have hS_ord : S.OrdConnected := hconv.ordConnected
  -- The symmetric union is order connected for the same reason: mixed-sign intervals contain `0`.
  have hOrd : (Set.Ici 0 ∪ S).OrdConnected := by
    refine Set.ordConnected_iff_uIcc_subset.2 ?_
    intro x hx y hy z hz
    rcases hx with hx_nonneg | hx_mem
    · rcases hy with hy_nonneg | hy_mem
      · left
        rcases le_total x y with hxy | hyx
        · have hz_mem : z ∈ Set.Icc x y := by
            simpa [Set.uIcc_of_le hxy] using hz
          exact le_trans hx_nonneg hz_mem.1
        · have hz_mem : z ∈ Set.Icc y x := by
            simpa [Set.uIcc_of_ge hyx] using hz
          exact le_trans hy_nonneg hz_mem.1
      · have hy_nonpos : y ≤ 0 := hsubset hy_mem
        have hyx : y ≤ x := le_trans hy_nonpos hx_nonneg
        have hz_mem : z ∈ Set.Icc y x := by
          simpa [Set.uIcc_of_ge hyx] using hz
        by_cases hz_nonneg : 0 ≤ z
        · exact Or.inl hz_nonneg
        · right
          have hz_nonpos : z ≤ 0 := (lt_of_not_ge hz_nonneg).le
          exact hS_ord.out hy_mem hzero ⟨hz_mem.1, hz_nonpos⟩
    · rcases hy with hy_nonneg | hy_mem
      · have hx_nonpos : x ≤ 0 := hsubset hx_mem
        have hxy : x ≤ y := le_trans hx_nonpos hy_nonneg
        have hz_mem : z ∈ Set.Icc x y := by
          simpa [Set.uIcc_of_le hxy] using hz
        by_cases hz_nonneg : 0 ≤ z
        · exact Or.inl hz_nonneg
        · right
          have hz_nonpos : z ≤ 0 := (lt_of_not_ge hz_nonneg).le
          exact hS_ord.out hx_mem hzero ⟨hz_mem.1, hz_nonpos⟩
      · right
        rcases le_total x y with hxy | hyx
        · have hz_mem : z ∈ Set.Icc x y := by
            simpa [Set.uIcc_of_le hxy] using hz
          exact hS_ord.out hx_mem hy_mem hz_mem
        · have hz_mem : z ∈ Set.Icc y x := by
            simpa [Set.uIcc_of_ge hyx] using hz
          exact hS_ord.out hy_mem hx_mem hz_mem
  exact hOrd.convex

/-- Helper for Theorem 24.52: the `Set.Iic b` residual is lower semicontinuous by branchwise
agreement with the constant and affine-tilt pieces, plus the zero-junction derivative package. -/
private lemma halflineResidualIic_lowerSemicontinuous
    {b : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIic : (∂ φ) 0 = Set.Iic b) :
    LowerSemicontinuous (fun x ↦ (halflineResidualIic φ hφ b x : EReal)) := by
  let ψ := halflineResidualIic φ hφ b
  have hconst_lsc : LowerSemicontinuous (fun x ↦ (originConstantResidual φ x : EReal)) := by
    simpa [originConstantResidual, Function.asEReal] using
      (continuous_const : Continuous fun _ : ℝ ↦ ((φ 0 : EReal).toReal : EReal)).lowerSemicontinuous
  have htilt_gamma :
      affineTiltIoi φ hφ b ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) b
  have htilt_lsc :
      LowerSemicontinuous (fun x ↦ (affineTiltIoi φ hφ b x : EReal)) :=
    (mem_gammaZero_iff.mp htilt_gamma).1
  intro x
  by_cases hx_neg : x < 0
  · have hEq :
        (fun y ↦ (originConstantResidual φ y : EReal)) =ᶠ[nhds x]
          fun y ↦ (ψ y : EReal) := by
      filter_upwards [isOpen_Iio.mem_nhds hx_neg] with y hy
      simpa [ψ, halflineResidualIic_apply_of_nonpos (φ := φ) (hφ := hφ) (b := b) hy.le]
    exact lowerSemicontinuousAt_congr (hf := hconst_lsc.lowerSemicontinuousAt x) hEq
  · by_cases hx_zero : x = 0
    · subst hx_zero
      have hzero_int :
          0 ∈ interior (effectiveDomain ψ) := by
        simpa [ψ] using zero_memInterior_effectiveDomain_halflineResidualIic hφ hsubIic
      have hderiv :
          HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 := by
        simpa [ψ] using halflineResidualIic_hasDerivAtZero (φ := φ) (hφ := hφ) hsubIic
      simpa [ψ, Function.asEReal] using
        lowerSemicontinuousAtAsEReal_zero_of_hasDerivAtZero hzero_int hderiv
    · have hx_pos : 0 < x := lt_of_le_of_ne (le_of_not_gt hx_neg) (Ne.symm hx_zero)
      have hEq :
          (fun y ↦ (affineTiltIoi φ hφ b y : EReal)) =ᶠ[nhds x]
            fun y ↦ (ψ y : EReal) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx_pos] with y hy
        simpa [ψ, halflineResidualIic_apply_of_pos (φ := φ) (hφ := hφ) (b := b) hy]
      exact lowerSemicontinuousAt_congr (hf := htilt_lsc.lowerSemicontinuousAt x) hEq

/-- Helper for Theorem 24.52: the `Set.Ici a` residual is lower semicontinuous by branchwise
agreement with the affine-tilt and constant pieces, plus the zero-junction derivative package. -/
private lemma halflineResidualIci_lowerSemicontinuous
    {a : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIci : (∂ φ) 0 = Set.Ici a) :
    LowerSemicontinuous (fun x ↦ (halflineResidualIci φ hφ a x : EReal)) := by
  let ψ := halflineResidualIci φ hφ a
  have hconst_lsc : LowerSemicontinuous (fun x ↦ (originConstantResidual φ x : EReal)) := by
    simpa [originConstantResidual, Function.asEReal] using
      (continuous_const : Continuous fun _ : ℝ ↦ ((φ 0 : EReal).toReal : EReal)).lowerSemicontinuous
  have htilt_gamma :
      affineTiltIoi φ hφ a ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) a
  have htilt_lsc :
      LowerSemicontinuous (fun x ↦ (affineTiltIoi φ hφ a x : EReal)) :=
    (mem_gammaZero_iff.mp htilt_gamma).1
  intro x
  by_cases hx_neg : x < 0
  · have hEq :
        (fun y ↦ (affineTiltIoi φ hφ a y : EReal)) =ᶠ[nhds x]
          fun y ↦ (ψ y : EReal) := by
      filter_upwards [isOpen_Iio.mem_nhds hx_neg] with y hy
      simpa [ψ, halflineResidualIci_apply_of_neg (φ := φ) (hφ := hφ) (a := a) hy]
    exact lowerSemicontinuousAt_congr (hf := htilt_lsc.lowerSemicontinuousAt x) hEq
  · by_cases hx_zero : x = 0
    · subst hx_zero
      have hzero_int :
          0 ∈ interior (effectiveDomain ψ) := by
        simpa [ψ] using zero_memInterior_effectiveDomain_halflineResidualIci hφ hsubIci
      have hderiv :
          HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 := by
        simpa [ψ] using halflineResidualIci_hasDerivAtZero (φ := φ) (hφ := hφ) hsubIci
      simpa [ψ, Function.asEReal] using
        lowerSemicontinuousAtAsEReal_zero_of_hasDerivAtZero hzero_int hderiv
    · have hx_pos : 0 < x := lt_of_le_of_ne (le_of_not_gt hx_neg) (Ne.symm hx_zero)
      have hEq :
          (fun y ↦ (originConstantResidual φ y : EReal)) =ᶠ[nhds x]
            fun y ↦ (ψ y : EReal) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx_pos] with y hy
        simpa [ψ, halflineResidualIci_apply_of_nonneg (φ := φ) (hφ := hφ) (a := a) hy.le]
      exact lowerSemicontinuousAt_congr (hf := hconst_lsc.lowerSemicontinuousAt x) hEq

/-- Helper for Theorem 24.52: the bounded residual is lower semicontinuous by matching the left
and right affine-tilt branches away from `0`, and by the zero-junction derivative package at
`0`. -/
private lemma intervalResidualIcc_lowerSemicontinuous
    {a b : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ)) (hsubIcc : (∂ φ) 0 = Set.Icc a b) :
    LowerSemicontinuous (fun x ↦ (intervalResidualIcc φ hφ a b x : EReal)) := by
  let ψ := intervalResidualIcc φ hφ a b
  have hleft_gamma :
      affineTiltIoi φ hφ a ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) a
  have hright_gamma :
      affineTiltIoi φ hφ b ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) b
  have hleft_lsc :
      LowerSemicontinuous (fun x ↦ (affineTiltIoi φ hφ a x : EReal)) :=
    (mem_gammaZero_iff.mp hleft_gamma).1
  have hright_lsc :
      LowerSemicontinuous (fun x ↦ (affineTiltIoi φ hφ b x : EReal)) :=
    (mem_gammaZero_iff.mp hright_gamma).1
  intro x
  by_cases hx_neg : x < 0
  · have hEq :
        (fun y ↦ (affineTiltIoi φ hφ a y : EReal)) =ᶠ[nhds x]
          fun y ↦ (ψ y : EReal) := by
      filter_upwards [isOpen_Iio.mem_nhds hx_neg] with y hy
      simpa [ψ, intervalResidualIcc_apply_of_neg (φ := φ) (hφ := hφ) (a := a) (b := b) hy]
    exact lowerSemicontinuousAt_congr (hf := hleft_lsc.lowerSemicontinuousAt x) hEq
  · by_cases hx_zero : x = 0
    · subst hx_zero
      have hzero_int :
          0 ∈ interior (effectiveDomain ψ) := by
        simpa [ψ] using zero_memInterior_effectiveDomain_intervalResidualIcc hab hφ hsubIcc
      have hderiv :
          HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 := by
        simpa [ψ] using intervalResidualIcc_hasDerivAtZero
          (φ := φ) (hab := hab) (hφ := hφ) hsubIcc
      simpa [ψ, Function.asEReal] using
        lowerSemicontinuousAtAsEReal_zero_of_hasDerivAtZero hzero_int hderiv
    · have hx_pos : 0 < x := lt_of_le_of_ne (le_of_not_gt hx_neg) (Ne.symm hx_zero)
      have hEq :
          (fun y ↦ (affineTiltIoi φ hφ b y : EReal)) =ᶠ[nhds x]
            fun y ↦ (ψ y : EReal) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx_pos] with y hy
        simpa [ψ, intervalResidualIcc_apply_of_pos (φ := φ) (hφ := hφ) (a := a) (b := b) hy]
      exact lowerSemicontinuousAt_congr (hf := hright_lsc.lowerSemicontinuousAt x) hEq

/-- Helper for Theorem 24.52: if a mixed-sign convex combination lands on the negative side, the
left affine tilt controls it by comparing the origin value with the affine support plane at `0`. -/
private lemma affineTiltIoi_constantMixedSignConvexBound_of_neg
    {u x y α : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hzero_mem : 0 ∈ effectiveDomain φ)
    (hu : u ∈ (∂ φ) 0) (hx : x ∈ effectiveDomain φ) (hx_neg : x < 0) (hy_pos : 0 < y)
    (hα0 : 0 < α) (hα1 : α < 1) (hz_neg : α * x + (1 - α) * y < 0) :
    (affineTiltIoi φ hφ u (α * x + (1 - α) * y) : EReal) ≤
      (α : EReal) * (affineTiltIoi φ hφ u x : EReal) +
        (1 - α : EReal) * (originConstantResidual φ y : EReal) := by
  let z : ℝ := α * x + (1 - α) * y
  have hz_eq : α * x + (1 - α) * y = z := rfl
  have htilt_gamma :
      affineTiltIoi φ hφ u ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) u
  have hzero_tilt : 0 ∈ effectiveDomain (affineTiltIoi φ hφ u) := by
    simpa [effectiveDomain_affineTiltIoi] using hzero_mem
  have hx_tilt : x ∈ effectiveDomain (affineTiltIoi φ hφ u) := by
    simpa [effectiveDomain_affineTiltIoi] using hx
  have hz_le_zero : z ≤ 0 := hz_neg.le
  have hx_le_z : x ≤ z := by
    dsimp [z]
    nlinarith [hα1, hy_pos]
  have hzφ : z ∈ effectiveDomain φ := by
    -- The negative target stays on the segment joining the finite negative point `x` to `0`.
    exact hφ.2.convex_effectiveDomain.ordConnected.out hx hzero_mem ⟨hx_le_z, hz_le_zero⟩
  have hz_tilt : z ∈ effectiveDomain (affineTiltIoi φ hφ u) := by
    simpa [effectiveDomain_affineTiltIoi] using hzφ
  let t : ℝ := z / x
  have hx_ne : x ≠ 0 := ne_of_lt hx_neg
  have ht_pos : 0 < t := by
    dsimp [t]
    exact div_pos_of_neg_of_neg hz_neg hx_neg
  have ht_lt_one : t < 1 := by
    dsimp [t]
    have hx_lt_z : x < z := by
      dsimp [z]
      nlinarith [hα1, hy_pos]
    exact (div_lt_one_of_neg hx_neg).2 hx_lt_z
  have hz_repr : t * x + (1 - t) * 0 = z := by
    dsimp [t]
    field_simp [hx_ne]
    ring
  have hz_mul : t * x = z := by
    simpa using hz_repr
  have htilt_ineq :=
    htilt_gamma.2.ineq (x := x) hx_tilt (y := 0) hzero_tilt ht_pos ht_lt_one
  have htilt_ineq' :
      (affineTiltIoi φ hφ u z : EReal) ≤
        (t : EReal) * (affineTiltIoi φ hφ u x : EReal) +
          (1 - t : EReal) * (affineTiltIoi φ hφ u 0 : EReal) := by
    -- Keep the Jensen step entirely inside the affine-tilt owner.
    simpa [smul_eq_mul, hz_mul] using htilt_ineq
  let c : ℝ := (φ 0 : EReal).toReal
  let gx : ℝ := (affineTiltIoi φ hφ u x : EReal).toReal
  have hcx : c ≤ gx := by
    simpa [c, gx] using
      originConstantResidual_le_affineTiltIoi_toReal_of_mem_subdifferential_zero
        (φ := φ) (hφ := hφ) (u := u) hzero_mem hx hu
  have ht_le_α : t ≤ α := by
    dsimp [t]
    refine (div_le_iff_of_neg hx_neg).2 ?_
    dsimp [z]
    nlinarith [hα1, hy_pos]
  have hcompare :
      (((t * gx + (1 - t) * c : ℝ)) : EReal) ≤
        (((α * gx + (1 - α) * c : ℝ)) : EReal) :=
    ereal_convexCombination_mono_of_weight hcx ht_le_α
  have htilt_ineq'' :
      (affineTiltIoi φ hφ u z : EReal) ≤
        (((t * gx + (1 - t) * c : ℝ)) : EReal) := by
    rw [value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ u) hx_tilt,
      affineTiltIoi_zero_asEReal (φ := φ) (hφ := hφ) (hzero_mem := hzero_mem) (u := u),
      ereal_convexCombination_eq] at htilt_ineq'
    exact htilt_ineq'
  -- Rewrite the constant side only at the end, after the affine-owner Jensen step is fixed.
  rw [hz_eq,
    value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ u) hx_tilt,
    originConstantResidual_asEReal (φ := φ) (x := y),
    ereal_convexCombination_eq]
  exact le_trans htilt_ineq'' hcompare

/-- Helper for Theorem 24.52: if a mixed-sign convex combination lands on the positive side, the
right affine tilt controls it by comparing the origin value with the affine support plane at `0`. -/
private lemma affineTiltIoi_constantMixedSignConvexBound_of_pos
    {u x y α : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hzero_mem : 0 ∈ effectiveDomain φ)
    (hu : u ∈ (∂ φ) 0) (hy : y ∈ effectiveDomain φ) (hx_neg : x < 0) (hy_pos : 0 < y)
    (hα0 : 0 < α) (hα1 : α < 1) (hz_pos : 0 < α * x + (1 - α) * y) :
    (affineTiltIoi φ hφ u (α * x + (1 - α) * y) : EReal) ≤
      (α : EReal) * (originConstantResidual φ x : EReal) +
        (1 - α : EReal) * (affineTiltIoi φ hφ u y : EReal) := by
  let z : ℝ := α * x + (1 - α) * y
  have hz_eq : α * x + (1 - α) * y = z := rfl
  have htilt_gamma :
      affineTiltIoi φ hφ u ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) u
  have hzero_tilt : 0 ∈ effectiveDomain (affineTiltIoi φ hφ u) := by
    simpa [effectiveDomain_affineTiltIoi] using hzero_mem
  have hy_tilt : y ∈ effectiveDomain (affineTiltIoi φ hφ u) := by
    simpa [effectiveDomain_affineTiltIoi] using hy
  have hz_nonneg : 0 ≤ z := hz_pos.le
  have hz_le_y : z ≤ y := by
    dsimp [z]
    nlinarith [hα0, hx_neg]
  have hzφ : z ∈ effectiveDomain φ := by
    -- The positive target stays on the segment joining `0` to the finite positive point `y`.
    exact hφ.2.convex_effectiveDomain.ordConnected.out hzero_mem hy ⟨hz_nonneg, hz_le_y⟩
  have hz_tilt : z ∈ effectiveDomain (affineTiltIoi φ hφ u) := by
    simpa [effectiveDomain_affineTiltIoi] using hzφ
  let t : ℝ := z / y
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have ht_pos : 0 < t := by
    dsimp [t]
    exact div_pos hz_pos hy_pos
  have ht_lt_one : t < 1 := by
    dsimp [t]
    have hz_lt_y : z < y := by
      dsimp [z]
      nlinarith [hα0, hx_neg]
    have hz_lt_one_mul_y : z < 1 * y := by
      simpa using hz_lt_y
    exact (div_lt_iff₀ hy_pos).2 hz_lt_one_mul_y
  have hz_repr : t * y + (1 - t) * 0 = z := by
    dsimp [t]
    field_simp [hy_ne]
    ring
  have hz_mul : t * y = z := by
    simpa using hz_repr
  have htilt_ineq :=
    htilt_gamma.2.ineq (x := y) hy_tilt (y := 0) hzero_tilt ht_pos ht_lt_one
  have htilt_ineq' :
      (affineTiltIoi φ hφ u z : EReal) ≤
        (t : EReal) * (affineTiltIoi φ hφ u y : EReal) +
          (1 - t : EReal) * (affineTiltIoi φ hφ u 0 : EReal) := by
    -- Keep the Jensen step entirely inside the affine-tilt owner.
    simpa [smul_eq_mul, hz_mul] using htilt_ineq
  let c : ℝ := (φ 0 : EReal).toReal
  let gy : ℝ := (affineTiltIoi φ hφ u y : EReal).toReal
  have hcy : c ≤ gy := by
    simpa [c, gy] using
      originConstantResidual_le_affineTiltIoi_toReal_of_mem_subdifferential_zero
        (φ := φ) (hφ := hφ) (u := u) hzero_mem hy hu
  have ht_le_1mα : t ≤ 1 - α := by
    dsimp [t]
    refine (div_le_iff₀ hy_pos).2 ?_
    dsimp [z]
    nlinarith [hα0, hx_neg]
  have hcompare :
      (((t * gy + (1 - t) * c : ℝ)) : EReal) ≤
        (((α * c + (1 - α) * gy : ℝ)) : EReal) := by
    convert
      (ereal_convexCombination_mono_of_weight (c := c) (d := gy) (α := t) (β := 1 - α)
        hcy ht_le_1mα) using 1 <;> ring
  have htilt_ineq'' :
      (affineTiltIoi φ hφ u z : EReal) ≤
        (((t * gy + (1 - t) * c : ℝ)) : EReal) := by
    rw [value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ u) hy_tilt,
      affineTiltIoi_zero_asEReal (φ := φ) (hφ := hφ) (hzero_mem := hzero_mem) (u := u),
      ereal_convexCombination_eq] at htilt_ineq'
    exact htilt_ineq'
  -- Rewrite the constant side only at the end, after the affine-owner Jensen step is fixed.
  rw [hz_eq,
    originConstantResidual_asEReal (φ := φ) (x := x),
    value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ u) hy_tilt,
    ereal_convexCombination_eq]
  exact le_trans htilt_ineq'' hcompare

/-- Helper for Theorem 24.52: the `Set.Iic b` residual belongs to `Γ₀(ℝ)` by gluing the constant
and affine-tilt branches across the origin. -/
private lemma halflineResidualIic_mem_gammaZero
    {b : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIic : (∂ φ) 0 = Set.Iic b) :
    halflineResidualIic φ hφ b ∈ Γ₀(ℝ) := by
  rw [mem_gammaZero_iff]
  constructor
  · -- Lower semicontinuity is already packaged by the branchwise neighborhood analysis.
    simpa using halflineResidualIic_lowerSemicontinuous (φ := φ) (hφ := hφ) hsubIic
  · have hzero_mem : 0 ∈ effectiveDomain φ :=
      zero_mem_effectiveDomain_of_subdifferential_zero_eq
        (Ω := Set.Iic b) ⟨b, by simp⟩ hφ hsubIic
    rcases effectiveDomain_nonneg_and_posWitness_of_subdifferentialZero_Iic hφ hsubIic with
      ⟨hdom_nonneg, p, hp_pos, hp_mem⟩
    have hdom_eq :
        effectiveDomain (halflineResidualIic φ hφ b) = Set.Iic 0 ∪ effectiveDomain φ :=
      effectiveDomain_halflineResidualIic_eq (φ := φ) (hφ := hφ) (b := b)
    have hdom_convex : Convex ℝ (effectiveDomain (halflineResidualIic φ hφ b)) := by
      rw [hdom_eq]
      exact
        convex_iic_union_of_convex_subset_nonneg hφ.2.convex_effectiveDomain hdom_nonneg
          hzero_mem
    have htilt_gamma :
        affineTiltIoi φ hφ b ∈ Γ₀(ℝ) :=
      affine_tilt_mem_gammaZero (f := φ) (hf := hφ) b
    have hzero_tilt : 0 ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
      simpa [effectiveDomain_affineTiltIoi] using hzero_mem
    have hb_sub : b ∈ (∂ φ) 0 := by
      simpa [hsubIic] using (show b ∈ Set.Iic b by simp)
    refine ⟨⟨0, interior_subset <|
      zero_memInterior_effectiveDomain_halflineResidualIic (φ := φ) (hφ := hφ) hsubIic⟩,
      subset_rfl, ?_⟩
    intro x hx y hy α hα0 hα1
    let z : ℝ := α * x + (1 - α) * y
    have hz_eq : α * x + (1 - α) * y = z := rfl
    have hz_smul : α • x + (1 - α) • y = z := by
      simpa [z, smul_eq_mul]
    have hα_nonneg : 0 ≤ α := hα0.le
    have h1α_pos : 0 < 1 - α := sub_pos.mpr hα1
    have h1α_nonneg : 0 ≤ 1 - α := h1α_pos.le
    have hz : z ∈ effectiveDomain (halflineResidualIic φ hφ b) := by
      exact hdom_convex hx hy hα_nonneg h1α_nonneg (by simpa [z, smul_eq_mul])
    rw [hdom_eq] at hx hy hz
    by_cases hx_nonpos : x ≤ 0
    · by_cases hy_nonpos : y ≤ 0
      · let c : ℝ := (φ 0 : EReal).toReal
        have hz_nonpos : z ≤ 0 := by
          dsimp [z]
          nlinarith [hα_nonneg, h1α_nonneg, hx_nonpos, hy_nonpos]
        -- When both endpoints stay on the constant branch, the convexity inequality is equality.
        rw [hz_smul,
          halflineResidualIic_apply_of_nonpos (φ := φ) (hφ := hφ) (b := b) hz_nonpos,
          halflineResidualIic_apply_of_nonpos (φ := φ) (hφ := hφ) (b := b) hx_nonpos,
          halflineResidualIic_apply_of_nonpos (φ := φ) (hφ := hφ) (b := b) hy_nonpos,
          originConstantResidual_asEReal (φ := φ) (x := z),
          originConstantResidual_asEReal (φ := φ) (x := x),
          originConstantResidual_asEReal (φ := φ) (x := y),
          ereal_convexCombination_eq]
        have hconst : α * c + (1 - α) * c = c := by
          ring
        simpa [c, hconst]
      · have hy_pos : 0 < y := lt_of_not_ge hy_nonpos
        have hyφ : y ∈ effectiveDomain φ := by
          rcases hy with hy_nonpos' | hyφ
          · exact False.elim (not_le_of_gt hy_pos hy_nonpos')
          · exact hyφ
        have hy_tilt : y ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
          simpa [effectiveDomain_affineTiltIoi] using hyφ
        by_cases hz_nonpos : z ≤ 0
        · let c : ℝ := (φ 0 : EReal).toReal
          let gy : ℝ := (affineTiltIoi φ hφ b y : EReal).toReal
          have hcy : c ≤ gy := by
            simpa [c, gy] using
              originConstantResidual_le_affineTiltIoi_toReal_of_mem_subdifferential_zero
                (φ := φ) (hφ := hφ) (u := b) hzero_mem hyφ hb_sub
          -- The target stays on the constant branch, so only the positive endpoint needs the
          -- support-plane comparison.
          rw [hz_smul,
            halflineResidualIic_apply_of_nonpos (φ := φ) (hφ := hφ) (b := b) hz_nonpos,
            halflineResidualIic_apply_of_nonpos (φ := φ) (hφ := hφ) (b := b) hx_nonpos,
            halflineResidualIic_apply_of_pos (φ := φ) (hφ := hφ) (b := b) hy_pos,
            originConstantResidual_asEReal (φ := φ) (x := z),
            originConstantResidual_asEReal (φ := φ) (x := x),
            value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ b) hy_tilt,
            ereal_convexCombination_eq]
          exact_mod_cast (by
            nlinarith [hcy, h1α_nonneg] :
              (φ 0 : EReal).toReal ≤ α * (φ 0 : EReal).toReal + (1 - α) * gy)
        · have hz_pos : 0 < z := lt_of_not_ge hz_nonpos
          by_cases hx_neg : x < 0
          · -- Route correction: use the generic constant-vs-affine mixed-sign lemma instead of
            -- rebuilding the same Jensen arithmetic inside the half-line package.
            simpa [hz_eq,
              halflineResidualIic_apply_of_pos (φ := φ) (hφ := hφ) (b := b) hz_pos,
              halflineResidualIic_apply_of_nonpos (φ := φ) (hφ := hφ) (b := b) hx_nonpos,
              halflineResidualIic_apply_of_pos (φ := φ) (hφ := hφ) (b := b) hy_pos] using
              affineTiltIoi_constantMixedSignConvexBound_of_pos
                (φ := φ) (u := b) hφ hzero_mem hb_sub hyφ hx_neg hy_pos hα0 hα1 hz_pos
          · have hx_zero : x = 0 := by
              linarith
            subst hx_zero
            have hzφ : z ∈ effectiveDomain φ := by
              exact hφ.2.convex_effectiveDomain hzero_mem hyφ hα_nonneg h1α_nonneg
                (by linarith [hz_eq])
            have hz_tilt : z ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
              simpa [effectiveDomain_affineTiltIoi] using hzφ
            have hz_pos_smul : 0 < α • (0 : ℝ) + (1 - α) • y := by
              have : 0 < (1 - α) * y := by
                nlinarith [h1α_pos, hy_pos]
              simpa [smul_eq_mul] using this
            -- When the constant endpoint collapses to `0`, convexity reduces to the right tilt.
            rw [halflineResidualIic_apply_of_pos (φ := φ) (hφ := hφ) (b := b) hz_pos_smul,
              halflineResidualIic_apply_of_nonpos (φ := φ) (hφ := hφ) (b := b)
                (show (0 : ℝ) ≤ 0 by simp),
              halflineResidualIic_apply_of_pos (φ := φ) (hφ := hφ) (b := b) hy_pos,
              originConstantResidual_asEReal (φ := φ) (x := 0)]
            have hineq := htilt_gamma.2.ineq (x := 0) hzero_tilt (y := y) hy_tilt hα0 hα1
            rw [affineTiltIoi_zero_asEReal (φ := φ) (hφ := hφ) (hzero_mem := hzero_mem) (u := b)]
              at hineq
            simpa [smul_eq_mul] using hineq
    · have hx_pos : 0 < x := lt_of_not_ge hx_nonpos
      have hxφ : x ∈ effectiveDomain φ := by
        rcases hx with hx_nonpos' | hxφ
        · exact False.elim (not_le_of_gt hx_pos hx_nonpos')
        · exact hxφ
      have hx_tilt : x ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
        simpa [effectiveDomain_affineTiltIoi] using hxφ
      by_cases hy_nonpos : y ≤ 0
      · by_cases hy_neg : y < 0
        · by_cases hz_nonpos : z ≤ 0
          · let c : ℝ := (φ 0 : EReal).toReal
            let gx : ℝ := (affineTiltIoi φ hφ b x : EReal).toReal
            have hcx : c ≤ gx := by
              simpa [c, gx] using
                originConstantResidual_le_affineTiltIoi_toReal_of_mem_subdifferential_zero
                  (φ := φ) (hφ := hφ) (u := b) hzero_mem hxφ hb_sub
            -- The target lands on the constant branch, so only the positive endpoint contributes
            -- nontrivially.
            rw [hz_smul,
              halflineResidualIic_apply_of_nonpos (φ := φ) (hφ := hφ) (b := b) hz_nonpos,
              halflineResidualIic_apply_of_pos (φ := φ) (hφ := hφ) (b := b) hx_pos,
              halflineResidualIic_apply_of_nonpos (φ := φ) (hφ := hφ) (b := b) hy_nonpos,
              originConstantResidual_asEReal (φ := φ) (x := z),
              value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ b) hx_tilt,
              originConstantResidual_asEReal (φ := φ) (x := y),
              ereal_convexCombination_eq]
            exact_mod_cast (by
              nlinarith [hcx, hα_nonneg] :
                (φ 0 : EReal).toReal ≤ α * gx + (1 - α) * (φ 0 : EReal).toReal)
          · have hz_pos : 0 < z := lt_of_not_ge hz_nonpos
            -- Swap the endpoints to keep the mixed-sign lemma in the `x < 0 < y` orientation.
            have hcoeffEReal : (1 + -(1 + -(α : EReal))) = (α : EReal) := by
              exact_mod_cast (by ring : 1 + -(1 + -α) = α)
            have hz_pos_smul : 0 < α • x + (1 - α) • y := by
              simpa [smul_eq_mul] using hz_pos
            rw [halflineResidualIic_apply_of_pos (φ := φ) (hφ := hφ) (b := b) hz_pos_smul,
              halflineResidualIic_apply_of_pos (φ := φ) (hφ := hφ) (b := b) hx_pos,
              halflineResidualIic_apply_of_nonpos (φ := φ) (hφ := hφ) (b := b) hy_nonpos]
            simpa [smul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, hcoeffEReal] using
              affineTiltIoi_constantMixedSignConvexBound_of_pos
                (φ := φ) (u := b) (x := y) (y := x) (α := 1 - α)
                hφ hzero_mem hb_sub hxφ hy_neg hx_pos h1α_pos (by nlinarith)
                (by
                  simpa [z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                    mul_comm, mul_left_comm, mul_assoc] using hz_pos)
        · have hy_zero : y = 0 := by
            linarith
          subst hy_zero
          have hz_pos : 0 < z := by
            dsimp [z]
            nlinarith [hα0, h1α_nonneg, hx_pos]
          have hzφ : z ∈ effectiveDomain φ := by
            exact hφ.2.convex_effectiveDomain hxφ hzero_mem hα_nonneg h1α_nonneg
              (by nlinarith [hα0, h1α_nonneg, hx_pos, hz_eq])
          have hz_tilt : z ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
            simpa [effectiveDomain_affineTiltIoi] using hzφ
          have hz_pos_smul : 0 < α • x + (1 - α) • (0 : ℝ) := by
            simpa [z, smul_eq_mul] using hz_pos
          -- When the constant endpoint is exactly `0`, convexity again reduces to the right tilt.
          have hineq := htilt_gamma.2.ineq (x := x) hx_tilt (y := 0) hzero_tilt hα0 hα1
          rw [affineTiltIoi_zero_asEReal (φ := φ) (hφ := hφ) (hzero_mem := hzero_mem) (u := b)] at hineq
          rw [halflineResidualIic_apply_of_pos (φ := φ) (hφ := hφ) (b := b) hz_pos_smul,
            halflineResidualIic_apply_of_pos (φ := φ) (hφ := hφ) (b := b) hx_pos,
            halflineResidualIic_apply_of_nonpos (φ := φ) (hφ := hφ) (b := b)
              (show (0 : ℝ) ≤ 0 by simp)]
          simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc,
            originConstantResidual_asEReal (φ := φ) (x := 0)] using hineq
      · have hy_pos : 0 < y := lt_of_not_ge hy_nonpos
        have hyφ : y ∈ effectiveDomain φ := by
          rcases hy with hy_nonpos' | hyφ
          · exact False.elim (not_le_of_gt hy_pos hy_nonpos')
          · exact hyφ
        have hy_tilt : y ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
          simpa [effectiveDomain_affineTiltIoi] using hyφ
        have hzφ : z ∈ effectiveDomain φ := by
          exact hφ.2.convex_effectiveDomain hxφ hyφ hα_nonneg h1α_nonneg
            (by nlinarith [hα0, h1α_pos, hx_pos, hy_pos, hz_eq])
        have hz_tilt : z ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
          simpa [effectiveDomain_affineTiltIoi] using hzφ
        have hz_pos : 0 < z := by
          dsimp [z]
          nlinarith [hα0, h1α_pos, hx_pos, hy_pos]
        -- When both endpoints are positive, the residual is just the right affine tilt.
        simpa [hz_eq, smul_eq_mul,
          halflineResidualIic_apply_of_pos (φ := φ) (hφ := hφ) (b := b) hz_pos,
          halflineResidualIic_apply_of_pos (φ := φ) (hφ := hφ) (b := b) hx_pos,
          halflineResidualIic_apply_of_pos (φ := φ) (hφ := hφ) (b := b) hy_pos] using
          htilt_gamma.2.ineq (x := x) hx_tilt (y := y) hy_tilt hα0 hα1
/-- Helper for Theorem 24.52: the `Set.Ici a` residual belongs to `Γ₀(ℝ)` by the symmetric
branch-gluing argument. -/
private lemma halflineResidualIci_mem_gammaZero
    {a : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIci : (∂ φ) 0 = Set.Ici a) :
    halflineResidualIci φ hφ a ∈ Γ₀(ℝ) := by
  rw [mem_gammaZero_iff]
  constructor
  · -- Lower semicontinuity is already packaged by the branchwise neighborhood analysis.
    simpa using halflineResidualIci_lowerSemicontinuous (φ := φ) (hφ := hφ) hsubIci
  · have hzero_mem : 0 ∈ effectiveDomain φ :=
      zero_mem_effectiveDomain_of_subdifferential_zero_eq
        (Ω := Set.Ici a) ⟨a, by simp⟩ hφ hsubIci
    rcases effectiveDomain_nonpos_and_negWitness_of_subdifferentialZero_Ici hφ hsubIci with
      ⟨hdom_nonpos, n, hn_neg, hn_mem⟩
    have hdom_eq :
        effectiveDomain (halflineResidualIci φ hφ a) = Set.Ici 0 ∪ effectiveDomain φ :=
      effectiveDomain_halflineResidualIci_eq (φ := φ) (hφ := hφ) (a := a)
    have hdom_convex : Convex ℝ (effectiveDomain (halflineResidualIci φ hφ a)) := by
      rw [hdom_eq]
      exact
        convex_ici_union_of_convex_subset_nonpos hφ.2.convex_effectiveDomain hdom_nonpos
          hzero_mem
    have htilt_gamma :
        affineTiltIoi φ hφ a ∈ Γ₀(ℝ) :=
      affine_tilt_mem_gammaZero (f := φ) (hf := hφ) a
    have hzero_tilt : 0 ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
      simpa [effectiveDomain_affineTiltIoi] using hzero_mem
    have ha_sub : a ∈ (∂ φ) 0 := by
      simpa [hsubIci] using (show a ∈ Set.Ici a by simp)
    refine ⟨⟨0, interior_subset <|
      zero_memInterior_effectiveDomain_halflineResidualIci (φ := φ) (hφ := hφ) hsubIci⟩,
      subset_rfl, ?_⟩
    intro x hx y hy α hα0 hα1
    let z : ℝ := α * x + (1 - α) * y
    have hz_eq : α * x + (1 - α) * y = z := rfl
    have hz_smul : α • x + (1 - α) • y = z := by
      simpa [z, smul_eq_mul]
    have hα_nonneg : 0 ≤ α := hα0.le
    have h1α_pos : 0 < 1 - α := sub_pos.mpr hα1
    have h1α_nonneg : 0 ≤ 1 - α := h1α_pos.le
    have hz : z ∈ effectiveDomain (halflineResidualIci φ hφ a) := by
      exact hdom_convex hx hy hα_nonneg h1α_nonneg (by simpa [z, smul_eq_mul])
    rw [hdom_eq] at hx hy hz
    by_cases hx_nonneg : 0 ≤ x
    · by_cases hy_nonneg : 0 ≤ y
      · let c : ℝ := (φ 0 : EReal).toReal
        have hz_nonneg : 0 ≤ z := by
          dsimp [z]
          nlinarith [hα_nonneg, h1α_nonneg, hx_nonneg, hy_nonneg]
        -- When both endpoints stay on the constant branch, the convexity inequality is equality.
        rw [hz_smul,
          halflineResidualIci_apply_of_nonneg (φ := φ) (hφ := hφ) (a := a) hz_nonneg,
          halflineResidualIci_apply_of_nonneg (φ := φ) (hφ := hφ) (a := a) hx_nonneg,
          halflineResidualIci_apply_of_nonneg (φ := φ) (hφ := hφ) (a := a) hy_nonneg,
          originConstantResidual_asEReal (φ := φ) (x := z),
          originConstantResidual_asEReal (φ := φ) (x := x),
          originConstantResidual_asEReal (φ := φ) (x := y),
          ereal_convexCombination_eq]
        have hconst : α * c + (1 - α) * c = c := by
          ring
        simpa [c, hconst]
      · have hy_neg : y < 0 := lt_of_not_ge hy_nonneg
        have hyφ : y ∈ effectiveDomain φ := by
          rcases hy with hy_nonneg' | hyφ
          · exact False.elim (not_le_of_gt hy_neg hy_nonneg')
          · exact hyφ
        have hy_tilt : y ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
          simpa [effectiveDomain_affineTiltIoi] using hyφ
        by_cases hz_nonneg : 0 ≤ z
        · let c : ℝ := (φ 0 : EReal).toReal
          let gy : ℝ := (affineTiltIoi φ hφ a y : EReal).toReal
          have hcy : c ≤ gy := by
            simpa [c, gy] using
              originConstantResidual_le_affineTiltIoi_toReal_of_mem_subdifferential_zero
                (φ := φ) (hφ := hφ) (u := a) hzero_mem hyφ ha_sub
          -- The target stays on the constant branch, so only the negative endpoint needs the
          -- support-plane comparison.
          rw [hz_smul,
            halflineResidualIci_apply_of_nonneg (φ := φ) (hφ := hφ) (a := a) hz_nonneg,
            halflineResidualIci_apply_of_nonneg (φ := φ) (hφ := hφ) (a := a) hx_nonneg,
            halflineResidualIci_apply_of_neg (φ := φ) (hφ := hφ) (a := a) hy_neg,
            originConstantResidual_asEReal (φ := φ) (x := z),
            originConstantResidual_asEReal (φ := φ) (x := x),
            value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ a) hy_tilt,
            ereal_convexCombination_eq]
          exact_mod_cast (by
            nlinarith [hcy, h1α_nonneg] :
              (φ 0 : EReal).toReal ≤ α * (φ 0 : EReal).toReal + (1 - α) * gy)
        · have hz_neg : z < 0 := lt_of_not_ge hz_nonneg
          have hz_neg_swap : (1 - α) * y + (1 - (1 - α)) * x < 0 := by
            simpa [z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
              mul_assoc] using hz_neg
          by_cases hx_pos : 0 < x
          · -- Route correction: use the generic affine-vs-constant mixed-sign lemma instead of
            -- rebuilding the mirrored Jensen arithmetic inside the half-line package.
            have hz_neg_smul : α • x + (1 - α) • y < 0 := by
              simpa [smul_eq_mul] using hz_neg
            have hcoeffEReal : (1 + -(1 + -(α : EReal))) = (α : EReal) := by
              exact_mod_cast (by ring : 1 + -(1 + -α) = α)
            rw [halflineResidualIci_apply_of_neg (φ := φ) (hφ := hφ) (a := a) hz_neg_smul,
              halflineResidualIci_apply_of_nonneg (φ := φ) (hφ := hφ) (a := a) hx_nonneg,
              halflineResidualIci_apply_of_neg (φ := φ) (hφ := hφ) (a := a) hy_neg]
            have hmixed :=
              affineTiltIoi_constantMixedSignConvexBound_of_neg
                (φ := φ) (u := a) (x := y) (y := x) (α := 1 - α)
                hφ hzero_mem ha_sub hyφ hy_neg hx_pos h1α_pos (by nlinarith) hz_neg_swap
            simpa [smul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, hcoeffEReal]
              using hmixed
          · have hx_zero : x = 0 := by
              linarith
            subst hx_zero
            have hzφ' : (1 - α) • y + α • (0 : ℝ) ∈ effectiveDomain φ :=
              hφ.2.convex_effectiveDomain hyφ hzero_mem h1α_nonneg hα_nonneg
                (by simp [z, smul_eq_mul])
            have hzφ : z ∈ effectiveDomain φ := by
              simpa [z, smul_eq_mul, add_comm, add_left_comm, add_assoc] using hzφ'
            have hz_tilt : z ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
              simpa [effectiveDomain_affineTiltIoi] using hzφ
            have hz_neg_smul : α • (0 : ℝ) + (1 - α) • y < 0 := by
              simpa [z, smul_eq_mul] using hz_neg
            -- When the constant endpoint collapses to `0`, convexity reduces to the left tilt.
            rw [halflineResidualIci_apply_of_neg (φ := φ) (hφ := hφ) (a := a) hz_neg_smul,
              halflineResidualIci_apply_of_nonneg (φ := φ) (hφ := hφ) (a := a)
                (show (0 : ℝ) ≤ 0 by simp),
              halflineResidualIci_apply_of_neg (φ := φ) (hφ := hφ) (a := a) hy_neg]
            have hcoeffEReal : (1 + -(1 + -(α : EReal))) = (α : EReal) := by
              exact_mod_cast (by ring : 1 + -(1 + -α) = α)
            have hineq :=
              htilt_gamma.2.ineq (x := y) hy_tilt (y := 0) hzero_tilt h1α_pos (by linarith)
            rw [affineTiltIoi_zero_asEReal (φ := φ) (hφ := hφ) (hzero_mem := hzero_mem) (u := a)]
              at hineq
            simpa [smul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, hcoeffEReal,
              originConstantResidual_asEReal (φ := φ) (x := 0)] using hineq
    · have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
      have hxφ : x ∈ effectiveDomain φ := by
        rcases hx with hx_nonneg' | hxφ
        · exact False.elim (not_le_of_gt hx_neg hx_nonneg')
        · exact hxφ
      have hx_tilt : x ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
        simpa [effectiveDomain_affineTiltIoi] using hxφ
      by_cases hy_nonneg : 0 ≤ y
      · by_cases hz_nonneg : 0 ≤ z
        · let c : ℝ := (φ 0 : EReal).toReal
          let gx : ℝ := (affineTiltIoi φ hφ a x : EReal).toReal
          have hcx : c ≤ gx := by
            simpa [c, gx] using
              originConstantResidual_le_affineTiltIoi_toReal_of_mem_subdifferential_zero
                (φ := φ) (hφ := hφ) (u := a) hzero_mem hxφ ha_sub
          -- The target lands on the constant branch, so only the negative endpoint contributes
          -- nontrivially.
          rw [hz_smul,
            halflineResidualIci_apply_of_nonneg (φ := φ) (hφ := hφ) (a := a) hz_nonneg,
            halflineResidualIci_apply_of_neg (φ := φ) (hφ := hφ) (a := a) hx_neg,
            halflineResidualIci_apply_of_nonneg (φ := φ) (hφ := hφ) (a := a) hy_nonneg,
            originConstantResidual_asEReal (φ := φ) (x := z),
            value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ a) hx_tilt,
            originConstantResidual_asEReal (φ := φ) (x := y),
            ereal_convexCombination_eq]
          exact_mod_cast (by
            nlinarith [hcx, hα_nonneg] :
              (φ 0 : EReal).toReal ≤ α * gx + (1 - α) * (φ 0 : EReal).toReal)
        · have hz_neg : z < 0 := lt_of_not_ge hz_nonneg
          by_cases hy_pos : 0 < y
          · -- Route correction: use the generic affine-vs-constant mixed-sign lemma on the
            -- negative target instead of repeating the same arithmetic locally.
            have hz_neg_smul : α • x + (1 - α) • y < 0 := by
              simpa [hz_smul] using hz_neg
            rw [halflineResidualIci_apply_of_neg (φ := φ) (hφ := hφ) (a := a) hz_neg_smul,
              halflineResidualIci_apply_of_neg (φ := φ) (hφ := hφ) (a := a) hx_neg,
              halflineResidualIci_apply_of_nonneg (φ := φ) (hφ := hφ) (a := a) hy_nonneg]
            simpa [smul_eq_mul] using
              affineTiltIoi_constantMixedSignConvexBound_of_neg
                (φ := φ) (u := a) hφ hzero_mem ha_sub hxφ hx_neg hy_pos hα0 hα1 hz_neg
          · have hy_zero : y = 0 := by
              linarith
            subst hy_zero
            have hzφ' : α • x + (1 - α) • (0 : ℝ) ∈ effectiveDomain φ :=
              hφ.2.convex_effectiveDomain hxφ hzero_mem hα_nonneg h1α_nonneg
                (by simp [z, smul_eq_mul])
            have hzφ : z ∈ effectiveDomain φ := by
              simpa [z, smul_eq_mul, add_comm, add_left_comm, add_assoc] using hzφ'
            have hz_tilt : z ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
              simpa [effectiveDomain_affineTiltIoi] using hzφ
            have hz_neg_smul : α • x + (1 - α) • (0 : ℝ) < 0 := by
              simpa [z, smul_eq_mul] using hz_neg
            -- When the constant endpoint is exactly `0`, convexity again reduces to the left tilt.
            rw [halflineResidualIci_apply_of_neg (φ := φ) (hφ := hφ) (a := a) hz_neg_smul,
              halflineResidualIci_apply_of_neg (φ := φ) (hφ := hφ) (a := a) hx_neg,
              halflineResidualIci_apply_of_nonneg (φ := φ) (hφ := hφ) (a := a)
                (show (0 : ℝ) ≤ 0 by simp)]
            have hineq := htilt_gamma.2.ineq (x := x) hx_tilt (y := 0) hzero_tilt hα0 hα1
            rw [affineTiltIoi_zero_asEReal (φ := φ) (hφ := hφ) (hzero_mem := hzero_mem) (u := a)] at hineq
            simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc,
              originConstantResidual_asEReal (φ := φ) (x := 0)] using hineq
      · have hy_neg : y < 0 := lt_of_not_ge hy_nonneg
        have hyφ : y ∈ effectiveDomain φ := by
          rcases hy with hy_nonneg' | hyφ
          · exact False.elim (not_le_of_gt hy_neg hy_nonneg')
          · exact hyφ
        have hy_tilt : y ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
          simpa [effectiveDomain_affineTiltIoi] using hyφ
        have hzφ : z ∈ effectiveDomain φ := by
          exact hφ.2.convex_effectiveDomain hxφ hyφ hα_nonneg h1α_nonneg
            (by linarith [hz_eq])
        have hz_tilt : z ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
          simpa [effectiveDomain_affineTiltIoi] using hzφ
        have hz_neg_calc : α * x + (1 - α) * y < 0 := by
          nlinarith [hx_neg, hy_neg, hα0, h1α_nonneg]
        have hz_neg : z < 0 := by
          simpa [z] using hz_neg_calc
        have hz_neg_smul : α • x + (1 - α) • y < 0 := by
          simpa [smul_eq_mul] using hz_neg
        -- When both endpoints are negative, the residual is just the left affine tilt.
        rw [halflineResidualIci_apply_of_neg (φ := φ) (hφ := hφ) (a := a) hz_neg_smul,
          halflineResidualIci_apply_of_neg (φ := φ) (hφ := hφ) (a := a) hx_neg,
          halflineResidualIci_apply_of_neg (φ := φ) (hφ := hφ) (a := a) hy_neg]
        simpa [smul_eq_mul] using
          htilt_gamma.2.ineq (x := x) hx_tilt (y := y) hy_tilt hα0 hα1
/-- Helper for Theorem 24.52: the `Set.Iic b` branch packages the already proved zero derivative
for the explicit source residual `halflineResidualIic`. -/
private lemma halflineResidualIic_package
    {b : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIic : (∂ φ) 0 = Set.Iic b) :
    let ψ := halflineResidualIic φ hφ b
    ψ ∈ Γ₀(ℝ) ∧ HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 := by
  let ψ := halflineResidualIic φ hφ b
  have hderiv :
      HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 := by
    simpa [ψ] using halflineResidualIic_hasDerivAtZero (φ := φ) (hφ := hφ) hsubIic
  have hgamma : ψ ∈ Γ₀(ℝ) := by
    -- Route correction: discharge the package through the explicit `Γ₀` companion lemma rather
    -- than redoing the branch-gluing inside the package itself.
    simpa [ψ] using halflineResidualIic_mem_gammaZero (φ := φ) (hφ := hφ) hsubIic
  exact ⟨hgamma, hderiv⟩

/-- Helper for Theorem 24.52: the `Set.Ici a` branch packages the already proved zero derivative
for the explicit source residual `halflineResidualIci`. -/
private lemma halflineResidualIci_package
    {a : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIci : (∂ φ) 0 = Set.Ici a) :
    let ψ := halflineResidualIci φ hφ a
    ψ ∈ Γ₀(ℝ) ∧ HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 := by
  let ψ := halflineResidualIci φ hφ a
  have hderiv :
      HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 := by
    simpa [ψ] using halflineResidualIci_hasDerivAtZero (φ := φ) (hφ := hφ) hsubIci
  have hgamma : ψ ∈ Γ₀(ℝ) := by
    -- Route correction: reuse the dedicated companion lemma once the symmetric branch gluing is
    -- proved.
    simpa [ψ] using halflineResidualIci_mem_gammaZero (φ := φ) (hφ := hφ) hsubIci
  exact ⟨hgamma, hderiv⟩

/-- Helper for Theorem 24.52: when the bounded mixed-sign segment lands on the negative side,
convexity reduces to the left affine tilt plus the support-plane comparison at the origin. -/
private lemma intervalResidualIcc_mixedSignConvexBound_of_neg
    {a b x y α : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ))
    (hsubIcc : (∂ φ) 0 = Set.Icc a b)
    (hx : x ∈ effectiveDomain φ) (hy : y ∈ effectiveDomain φ)
    (hx_neg : x < 0) (hy_pos : 0 < y) (hα0 : 0 < α) (hα1 : α < 1)
    (hz_neg : α * x + (1 - α) * y < 0) :
    (intervalResidualIcc φ hφ a b (α * x + (1 - α) * y) : EReal) ≤
      (α : EReal) * (intervalResidualIcc φ hφ a b x : EReal) +
        (1 - α : EReal) * (intervalResidualIcc φ hφ a b y : EReal) := by
  let z : ℝ := α * x + (1 - α) * y
  have hz_eq : α * x + (1 - α) * y = z := rfl
  have hzero_mem : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Icc a b) (Set.nonempty_Icc.2 hab) hφ hsubIcc
  have ha_sub : a ∈ (∂ φ) 0 := by
    simpa [hsubIcc] using (show a ∈ Set.Icc a b by exact ⟨le_rfl, hab⟩)
  have hb_sub : b ∈ (∂ φ) 0 := by
    simpa [hsubIcc] using (show b ∈ Set.Icc a b by exact ⟨hab, le_rfl⟩)
  have hx_tilt : x ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
    simpa [effectiveDomain_affineTiltIoi] using hx
  have hy_tilt : y ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
    simpa [effectiveDomain_affineTiltIoi] using hy
  let gx : ℝ := (affineTiltIoi φ hφ a x : EReal).toReal
  let gy : ℝ := (affineTiltIoi φ hφ b y : EReal).toReal
  let c : ℝ := (φ 0 : EReal).toReal
  have hcy : c ≤ gy := by
    -- Compare the positive endpoint with the common origin constant through the right support
    -- plane.
    simpa [c, gy] using
      originConstantResidual_le_affineTiltIoi_toReal_of_mem_subdifferential_zero
        (φ := φ) (hφ := hφ) (u := b) hzero_mem hy hb_sub
  have hbase :=
    affineTiltIoi_constantMixedSignConvexBound_of_neg
      (φ := φ) (u := a) hφ hzero_mem ha_sub hx hx_neg hy_pos hα0 hα1 hz_neg
  have hbase' :
      (intervalResidualIcc φ hφ a b z : EReal) ≤ (((α * gx + (1 - α) * c : ℝ)) : EReal) := by
    -- First keep the Jensen step in the left affine-tilt owner, then rewrite the branch values.
    rw [intervalResidualIcc_apply_of_neg (φ := φ) (hφ := hφ) (a := a) (b := b) hz_neg]
    have hbase0 : (affineTiltIoi φ hφ a z : EReal) ≤
        (α : EReal) * (affineTiltIoi φ hφ a x : EReal) +
          (1 - α : EReal) * (originConstantResidual φ y : EReal) := by
      simpa [z] using hbase
    rw [value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ a) hx_tilt,
      originConstantResidual_asEReal (φ := φ) (x := y),
      ereal_convexCombination_eq] at hbase0
    simpa [gx, c] using hbase0
  have hcompare :
      (((α * gx + (1 - α) * c : ℝ)) : EReal) ≤
        (((α * gx + (1 - α) * gy : ℝ)) : EReal) := by
    have h1α_nonneg : 0 ≤ 1 - α := (sub_pos.mpr hα1).le
    exact_mod_cast (by
      nlinarith [hcy, h1α_nonneg] :
        α * gx + (1 - α) * c ≤ α * gx + (1 - α) * gy)
  -- Replace the remaining constant endpoint by the right affine tilt at slope `b`.
  rw [hz_eq,
    intervalResidualIcc_apply_of_neg (φ := φ) (hφ := hφ) (a := a) (b := b) hx_neg,
    intervalResidualIcc_apply_of_pos (φ := φ) (hφ := hφ) (a := a) (b := b) hy_pos,
    value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ a) hx_tilt,
    value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ b) hy_tilt,
    ereal_convexCombination_eq]
  exact le_trans hbase' hcompare
/-- Helper for Theorem 24.52: when the bounded mixed-sign segment lands on the positive side,
convexity reduces to the right affine tilt plus the support-plane comparison at the origin. -/
private lemma intervalResidualIcc_mixedSignConvexBound_of_pos
    {a b x y α : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ))
    (hsubIcc : (∂ φ) 0 = Set.Icc a b)
    (hx : x ∈ effectiveDomain φ) (hy : y ∈ effectiveDomain φ)
    (hx_neg : x < 0) (hy_pos : 0 < y) (hα0 : 0 < α) (hα1 : α < 1)
    (hz_pos : 0 < α * x + (1 - α) * y) :
    (intervalResidualIcc φ hφ a b (α * x + (1 - α) * y) : EReal) ≤
      (α : EReal) * (intervalResidualIcc φ hφ a b x : EReal) +
        (1 - α : EReal) * (intervalResidualIcc φ hφ a b y : EReal) := by
  let z : ℝ := α * x + (1 - α) * y
  have hz_eq : α * x + (1 - α) * y = z := rfl
  have hzero_mem : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Icc a b) (Set.nonempty_Icc.2 hab) hφ hsubIcc
  have ha_sub : a ∈ (∂ φ) 0 := by
    simpa [hsubIcc] using (show a ∈ Set.Icc a b by exact ⟨le_rfl, hab⟩)
  have hb_sub : b ∈ (∂ φ) 0 := by
    simpa [hsubIcc] using (show b ∈ Set.Icc a b by exact ⟨hab, le_rfl⟩)
  have hx_tilt : x ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
    simpa [effectiveDomain_affineTiltIoi] using hx
  have hy_tilt : y ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
    simpa [effectiveDomain_affineTiltIoi] using hy
  let gx : ℝ := (affineTiltIoi φ hφ a x : EReal).toReal
  let gy : ℝ := (affineTiltIoi φ hφ b y : EReal).toReal
  let c : ℝ := (φ 0 : EReal).toReal
  have hcx : c ≤ gx := by
    -- Compare the negative endpoint with the common origin constant through the left support
    -- plane.
    simpa [c, gx] using
      originConstantResidual_le_affineTiltIoi_toReal_of_mem_subdifferential_zero
        (φ := φ) (hφ := hφ) (u := a) hzero_mem hx ha_sub
  have hbase :=
    affineTiltIoi_constantMixedSignConvexBound_of_pos
      (φ := φ) (u := b) hφ hzero_mem hb_sub hy hx_neg hy_pos hα0 hα1 hz_pos
  have hbase' :
      (intervalResidualIcc φ hφ a b z : EReal) ≤ (((α * c + (1 - α) * gy : ℝ)) : EReal) := by
    -- First keep the Jensen step in the right affine-tilt owner, then rewrite the branch values.
    rw [intervalResidualIcc_apply_of_pos (φ := φ) (hφ := hφ) (a := a) (b := b) hz_pos]
    have hbase0 : (affineTiltIoi φ hφ b z : EReal) ≤
        (α : EReal) * (originConstantResidual φ x : EReal) +
          (1 - α : EReal) * (affineTiltIoi φ hφ b y : EReal) := by
      simpa [z] using hbase
    rw [originConstantResidual_asEReal (φ := φ) (x := x),
      value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ b) hy_tilt,
      ereal_convexCombination_eq] at hbase0
    simpa [gy, c] using hbase0
  have hcompare :
      (((α * c + (1 - α) * gy : ℝ)) : EReal) ≤
        (((α * gx + (1 - α) * gy : ℝ)) : EReal) := by
    have hα_nonneg : 0 ≤ α := hα0.le
    exact_mod_cast (by
      nlinarith [hcx, hα_nonneg] :
        α * c + (1 - α) * gy ≤ α * gx + (1 - α) * gy)
  -- Replace the remaining constant endpoint by the left affine tilt at slope `a`.
  rw [hz_eq,
    intervalResidualIcc_apply_of_neg (φ := φ) (hφ := hφ) (a := a) (b := b) hx_neg,
    intervalResidualIcc_apply_of_pos (φ := φ) (hφ := hφ) (a := a) (b := b) hy_pos,
    value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ a) hx_tilt,
    value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ b) hy_tilt,
    ereal_convexCombination_eq]
  exact le_trans hbase' hcompare
/-- Helper for Theorem 24.52: the bounded residual belongs to `Γ₀(ℝ)` by combining the left and
right affine-tilt convexity with the dedicated mixed-sign Jensen adapters. -/
private lemma intervalResidualIcc_convexityCore_of_nonpositiveRight
    {a b x y α β : ℝ} (hφ : φ ∈ Γ₀(ℝ))
    (hx : x ∈ effectiveDomain φ) (hy : y ∈ effectiveDomain φ)
    (hxy : x < y) (hy_nonpos : y ≤ 0)
    (hzero_mem : 0 ∈ effectiveDomain φ)
    (hα0 : 0 < α) (hα1 : α < 1) (hβ_eq : β = 1 - α) :
    (intervalResidualIcc φ hφ a b (α • x + β • y) : EReal) ≤
      (α : EReal) * (intervalResidualIcc φ hφ a b x : EReal) +
        (β : EReal) * (intervalResidualIcc φ hφ a b y : EReal) := by
  have hleft_gamma :
      affineTiltIoi φ hφ a ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) a
  have hzero_left : 0 ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
    simpa [effectiveDomain_affineTiltIoi] using hzero_mem
  by_cases hy_neg : y < 0
  · have hx_neg : x < 0 := lt_of_lt_of_le hxy hy_nonpos
    have hx_tilt : x ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
      simpa [effectiveDomain_affineTiltIoi] using hx
    have hy_tilt : y ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
      simpa [effectiveDomain_affineTiltIoi] using hy
    have hz_neg : α * x + (1 - α) * y < 0 := by
      nlinarith [hα0, hα1, hx_neg, hy_neg]
    have hz_neg_smul : α • x + (1 - α) • y < 0 := by
      simpa [smul_eq_mul] using hz_neg
    -- When the ordered segment stays on the negative side, the bounded residual is the left
    -- affine tilt everywhere.
    rw [hβ_eq,
      intervalResidualIcc_apply_of_neg (φ := φ) (hφ := hφ) (a := a) (b := b) hz_neg_smul,
      intervalResidualIcc_apply_of_neg (φ := φ) (hφ := hφ) (a := a) (b := b) hx_neg,
      intervalResidualIcc_apply_of_neg (φ := φ) (hφ := hφ) (a := a) (b := b) hy_neg]
    simpa [smul_eq_mul] using
      hleft_gamma.2.ineq (x := x) hx_tilt (y := y) hy_tilt hα0 hα1
  · have hy_zero : y = 0 := by
      linarith
    subst hy_zero
    have hx_neg : x < 0 := hxy
    have hx_tilt : x ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
      simpa [effectiveDomain_affineTiltIoi] using hx
    have hz_neg : α * x < 0 := by
      exact mul_neg_of_pos_of_neg hα0 hx_neg
    have hz_neg_smul : α • x + (1 - α) • (0 : ℝ) < 0 := by
      simpa [smul_eq_mul] using hz_neg
    have hzero_apply : intervalResidualIcc φ hφ a b (0 : ℝ) = originConstantResidual φ 0 := by
      simp [intervalResidualIcc]
    -- The right endpoint is the normalized origin value, so convexity again reduces to the
    -- left affine tilt.
    rw [hβ_eq,
      hzero_apply,
      intervalResidualIcc_apply_of_neg (φ := φ) (hφ := hφ) (a := a) (b := b) hz_neg_smul,
      intervalResidualIcc_apply_of_neg (φ := φ) (hφ := hφ) (a := a) (b := b) hx_neg]
    have hineq := hleft_gamma.2.ineq (x := x) hx_tilt (y := 0) hzero_left hα0 hα1
    rw [affineTiltIoi_zero_asEReal (φ := φ) (hφ := hφ) (hzero_mem := hzero_mem) (u := a)] at hineq
    simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc,
      originConstantResidual_asEReal (φ := φ) (x := 0)] using hineq

/-- Helper for Theorem 24.52: if the ordered segment starts on the nonnegative side, the bounded
residual convexity reduces to the right affine-tilt branch. -/
private lemma intervalResidualIcc_convexityCore_of_nonnegativeLeft
    {a b x y α β : ℝ} (hφ : φ ∈ Γ₀(ℝ))
    (hx : x ∈ effectiveDomain φ) (hy : y ∈ effectiveDomain φ)
    (hx_nonneg : 0 ≤ x) (hy_pos : 0 < y)
    (hzero_mem : 0 ∈ effectiveDomain φ)
    (hα0 : 0 < α) (hα1 : α < 1) (hβ_eq : β = 1 - α) :
    (intervalResidualIcc φ hφ a b (α • x + β • y) : EReal) ≤
      (α : EReal) * (intervalResidualIcc φ hφ a b x : EReal) +
        (β : EReal) * (intervalResidualIcc φ hφ a b y : EReal) := by
  have hright_gamma :
      affineTiltIoi φ hφ b ∈ Γ₀(ℝ) :=
    affine_tilt_mem_gammaZero (f := φ) (hf := hφ) b
  have hzero_right : 0 ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
    simpa [effectiveDomain_affineTiltIoi] using hzero_mem
  by_cases hx_pos : 0 < x
  · have hx_tilt : x ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
      simpa [effectiveDomain_affineTiltIoi] using hx
    have hy_tilt : y ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
      simpa [effectiveDomain_affineTiltIoi] using hy
    have hz_pos : 0 < α * x + (1 - α) * y := by
      nlinarith [hα0, hα1, hx_pos, hy_pos]
    have hz_pos_smul : 0 < α • x + (1 - α) • y := by
      simpa [smul_eq_mul] using hz_pos
    -- When the ordered segment stays on the positive side, the bounded residual is the right
    -- affine tilt everywhere.
    rw [hβ_eq,
      intervalResidualIcc_apply_of_pos (φ := φ) (hφ := hφ) (a := a) (b := b) hz_pos_smul,
      intervalResidualIcc_apply_of_pos (φ := φ) (hφ := hφ) (a := a) (b := b) hx_pos,
      intervalResidualIcc_apply_of_pos (φ := φ) (hφ := hφ) (a := a) (b := b) hy_pos]
    simpa [smul_eq_mul] using
      hright_gamma.2.ineq (x := x) hx_tilt (y := y) hy_tilt hα0 hα1
  · have hx_zero : x = 0 := by
      linarith
    subst hx_zero
    have hy_tilt : y ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
      simpa [effectiveDomain_affineTiltIoi] using hy
    have hz_pos : 0 < (1 - α) * y := by
      exact mul_pos (sub_pos.mpr hα1) hy_pos
    have hz_pos_smul : 0 < α • (0 : ℝ) + (1 - α) • y := by
      simpa [smul_eq_mul] using hz_pos
    have hzero_apply : intervalResidualIcc φ hφ a b (0 : ℝ) = originConstantResidual φ 0 := by
      simp [intervalResidualIcc]
    -- The left endpoint is the normalized origin value, so convexity reduces to the right
    -- affine tilt.
    rw [hβ_eq,
      hzero_apply,
      intervalResidualIcc_apply_of_pos (φ := φ) (hφ := hφ) (a := a) (b := b) hz_pos_smul,
      intervalResidualIcc_apply_of_pos (φ := φ) (hφ := hφ) (a := a) (b := b) hy_pos]
    have hineq := hright_gamma.2.ineq (x := 0) hzero_right (y := y) hy_tilt hα0 hα1
    rw [affineTiltIoi_zero_asEReal (φ := φ) (hφ := hφ) (hzero_mem := hzero_mem) (u := b)] at hineq
    simpa [smul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      originConstantResidual_asEReal (φ := φ) (x := 0)] using hineq

/-- Helper for Theorem 24.52: if the ordered segment crosses the origin, the bounded residual
convexity follows from the mixed-sign Jensen adapters and the origin support-plane comparison. -/
private lemma intervalResidualIcc_convexityCore_of_mixedSigns_pos
    {a b x y α β : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ))
    (hsubIcc : (∂ φ) 0 = Set.Icc a b)
    (hx : x ∈ effectiveDomain φ) (hy : y ∈ effectiveDomain φ)
    (hx_neg : x < 0) (hy_pos : 0 < y)
    (hα0 : 0 < α) (hα1 : α < 1) (hβ_eq : β = 1 - α)
    (hz_pos : 0 < α * x + (1 - α) * y) :
    (intervalResidualIcc φ hφ a b (α • x + β • y) : EReal) ≤
      (α : EReal) * (intervalResidualIcc φ hφ a b x : EReal) +
        (β : EReal) * (intervalResidualIcc φ hφ a b y : EReal) := by
  -- The ordered segment crosses the origin and lands on the positive side.
  simpa [smul_eq_mul, hβ_eq,
    intervalResidualIcc_apply_of_neg (φ := φ) (hφ := hφ) (a := a) (b := b) hx_neg,
    intervalResidualIcc_apply_of_pos (φ := φ) (hφ := hφ) (a := a) (b := b) hy_pos,
    intervalResidualIcc_apply_of_pos (φ := φ) (hφ := hφ) (a := a) (b := b) hz_pos] using
    intervalResidualIcc_mixedSignConvexBound_of_pos
      (φ := φ) (a := a) (b := b) hab hφ hsubIcc hx hy hx_neg hy_pos hα0 hα1 hz_pos

/-- Helper for Theorem 24.52: if the ordered mixed-sign segment lands exactly at `0`, compare the
two affine-tilt branches with the common origin constant. -/
private lemma intervalResidualIcc_convexityCore_of_mixedSigns_zero
    {a b x y α β : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ))
    (hsubIcc : (∂ φ) 0 = Set.Icc a b)
    (hx : x ∈ effectiveDomain φ) (hy : y ∈ effectiveDomain φ)
    (hx_neg : x < 0) (hy_pos : 0 < y)
    (hzero_mem : 0 ∈ effectiveDomain φ)
    (hα0 : 0 < α) (hα1 : α < 1) (hβ_eq : β = 1 - α)
    (hz_zero : α * x + (1 - α) * y = 0) :
    (intervalResidualIcc φ hφ a b (α • x + β • y) : EReal) ≤
      (α : EReal) * (intervalResidualIcc φ hφ a b x : EReal) +
        (β : EReal) * (intervalResidualIcc φ hφ a b y : EReal) := by
  have ha_sub : a ∈ (∂ φ) 0 := by
    simpa [hsubIcc] using (show a ∈ Set.Icc a b by exact ⟨le_rfl, hab⟩)
  have hb_sub : b ∈ (∂ φ) 0 := by
    simpa [hsubIcc] using (show b ∈ Set.Icc a b by exact ⟨hab, le_rfl⟩)
  have hzero_apply : intervalResidualIcc φ hφ a b (0 : ℝ) = originConstantResidual φ 0 := by
    simp [intervalResidualIcc]
  have hx_tilt : x ∈ effectiveDomain (affineTiltIoi φ hφ a) := by
    simpa [effectiveDomain_affineTiltIoi] using hx
  have hy_tilt : y ∈ effectiveDomain (affineTiltIoi φ hφ b) := by
    simpa [effectiveDomain_affineTiltIoi] using hy
  let gx : ℝ := (affineTiltIoi φ hφ a x : EReal).toReal
  let gy : ℝ := (affineTiltIoi φ hφ b y : EReal).toReal
  let c : ℝ := (φ 0 : EReal).toReal
  have hcx : c ≤ gx := by
    simpa [c, gx] using
      originConstantResidual_le_affineTiltIoi_toReal_of_mem_subdifferential_zero
        (φ := φ) (hφ := hφ) (u := a) hzero_mem hx ha_sub
  have hcy : c ≤ gy := by
    simpa [c, gy] using
      originConstantResidual_le_affineTiltIoi_toReal_of_mem_subdifferential_zero
        (φ := φ) (hφ := hφ) (u := b) hzero_mem hy hb_sub
  have hz_zero_smul : α • x + (1 - α) • y = (0 : ℝ) := by
    simpa [smul_eq_mul] using hz_zero
  -- At the origin, compare the two side branches directly with the common constant.
  rw [hβ_eq, hz_zero_smul, hzero_apply,
    intervalResidualIcc_apply_of_neg (φ := φ) (hφ := hφ) (a := a) (b := b) hx_neg,
    intervalResidualIcc_apply_of_pos (φ := φ) (hφ := hφ) (a := a) (b := b) hy_pos,
    originConstantResidual_asEReal (φ := φ) (x := 0),
    value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ a) hx_tilt,
    value_eq_coe_toReal_of_mem_effectiveDomain (f := affineTiltIoi φ hφ b) hy_tilt]
  exact_mod_cast (by
    nlinarith [hcx, hcy, hα0.le, (sub_pos.mpr hα1).le] :
      (φ 0 : EReal).toReal ≤ α * gx + (1 - α) * gy)

/-- Helper for Theorem 24.52: if the ordered mixed-sign segment lands on the negative side, use
the dedicated negative mixed-sign Jensen adapter. -/
private lemma intervalResidualIcc_convexityCore_of_mixedSigns_neg
    {a b x y α β : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ))
    (hsubIcc : (∂ φ) 0 = Set.Icc a b)
    (hx : x ∈ effectiveDomain φ) (hy : y ∈ effectiveDomain φ)
    (hx_neg : x < 0) (hy_pos : 0 < y)
    (hα0 : 0 < α) (hα1 : α < 1) (hβ_eq : β = 1 - α)
    (hz_neg : α * x + (1 - α) * y < 0) :
    (intervalResidualIcc φ hφ a b (α • x + β • y) : EReal) ≤
      (α : EReal) * (intervalResidualIcc φ hφ a b x : EReal) +
        (β : EReal) * (intervalResidualIcc φ hφ a b y : EReal) := by
  -- The ordered segment crosses the origin and lands on the negative side.
  simpa [smul_eq_mul, hβ_eq,
    intervalResidualIcc_apply_of_neg (φ := φ) (hφ := hφ) (a := a) (b := b) hx_neg,
    intervalResidualIcc_apply_of_pos (φ := φ) (hφ := hφ) (a := a) (b := b) hy_pos,
    intervalResidualIcc_apply_of_neg (φ := φ) (hφ := hφ) (a := a) (b := b) hz_neg] using
    intervalResidualIcc_mixedSignConvexBound_of_neg
      (φ := φ) (a := a) (b := b) hab hφ hsubIcc hx hy hx_neg hy_pos hα0 hα1 hz_neg

/-- Helper for Theorem 24.52: if the ordered segment crosses the origin, the bounded residual
convexity follows from the mixed-sign Jensen adapters and the origin support-plane comparison. -/
private lemma intervalResidualIcc_convexityCore_of_mixedSigns
    {a b x y α β : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ))
    (hsubIcc : (∂ φ) 0 = Set.Icc a b)
    (hx : x ∈ effectiveDomain φ) (hy : y ∈ effectiveDomain φ)
    (hx_neg : x < 0) (hy_pos : 0 < y)
    (hzero_mem : 0 ∈ effectiveDomain φ)
    (hα0 : 0 < α) (hα1 : α < 1) (hβ_eq : β = 1 - α) :
    (intervalResidualIcc φ hφ a b (α • x + β • y) : EReal) ≤
      (α : EReal) * (intervalResidualIcc φ hφ a b x : EReal) +
        (β : EReal) * (intervalResidualIcc φ hφ a b y : EReal) := by
  by_cases hz_nonneg : 0 ≤ α * x + (1 - α) * y
  · by_cases hz_pos : 0 < α * x + (1 - α) * y
    · exact
        intervalResidualIcc_convexityCore_of_mixedSigns_pos
          (φ := φ) (a := a) (b := b) hab hφ hsubIcc hx hy hx_neg hy_pos hα0 hα1 hβ_eq
          hz_pos
    · have hz_zero : α * x + (1 - α) * y = 0 := by
        linarith
      exact
        intervalResidualIcc_convexityCore_of_mixedSigns_zero
          (φ := φ) (a := a) (b := b) hab hφ hsubIcc hx hy hx_neg hy_pos hzero_mem hα0 hα1
          hβ_eq hz_zero
  · have hz_neg : α * x + (1 - α) * y < 0 := lt_of_not_ge hz_nonneg
    exact
      intervalResidualIcc_convexityCore_of_mixedSigns_neg
        (φ := φ) (a := a) (b := b) hab hφ hsubIcc hx hy hx_neg hy_pos hα0 hα1 hβ_eq hz_neg

/-- Helper for Theorem 24.52: the bounded residual belongs to `Γ₀(ℝ)` by combining the left and
right affine-tilt convexity with the dedicated mixed-sign Jensen adapters. -/
private lemma intervalResidualIcc_convexityCore
    {a b : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ)) (hsubIcc : (∂ φ) 0 = Set.Icc a b) :
    ∀ x ∈ effectiveDomain (intervalResidualIcc φ hφ a b),
      ∀ y ∈ effectiveDomain (intervalResidualIcc φ hφ a b),
        ∀ α : ℝ, 0 < α → α < 1 →
          (intervalResidualIcc φ hφ a b (α • x + (1 - α) • y) : EReal) ≤
            (α : EReal) * (intervalResidualIcc φ hφ a b x : EReal) +
              (1 - α : EReal) * (intervalResidualIcc φ hφ a b y : EReal) := by
  have hzero_mem : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.Icc a b) (Set.nonempty_Icc.2 hab) hφ hsubIcc
  have hdom_eq :
      effectiveDomain (intervalResidualIcc φ hφ a b) = effectiveDomain φ :=
    effectiveDomain_intervalResidualIcc_eq (φ := φ) (hφ := hφ) (a := a) (b := b) hzero_mem
  intro x hx y hy α hα0 hα1
  rw [hdom_eq] at hx hy
  have hxy_or_eq_or_hyx := lt_trichotomy x y
  rcases hxy_or_eq_or_hyx with hxy | rfl | hyx
  · by_cases hy_nonpos : y ≤ 0
    · exact
        intervalResidualIcc_convexityCore_of_nonpositiveRight
          (φ := φ) (a := a) (b := b) hφ hx hy hxy hy_nonpos hzero_mem hα0 hα1 rfl
    · have hy_pos : 0 < y := lt_of_not_ge hy_nonpos
      by_cases hx_nonneg : 0 ≤ x
      · exact
          intervalResidualIcc_convexityCore_of_nonnegativeLeft
            (φ := φ) (a := a) (b := b) hφ hx hy hx_nonneg hy_pos hzero_mem hα0 hα1 rfl
      · have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
        exact
          intervalResidualIcc_convexityCore_of_mixedSigns
            (φ := φ) (a := a) (b := b) hab hφ hsubIcc hx hy hx_neg hy_pos hzero_mem hα0 hα1
            rfl
  · have hcomb : α • x + (1 - α) • x = x := by
      have hcombR : α * x + (1 - α) * x = x := by
        ring
      simpa [smul_eq_mul] using hcombR
    let s : ℝ := (intervalResidualIcc φ hφ a b x : EReal).toReal
    have hxval :
        (intervalResidualIcc φ hφ a b x : EReal) = ((s : ℝ) : EReal) := by
      simpa [s] using
        value_eq_coe_toReal_of_mem_effectiveDomain (f := intervalResidualIcc φ hφ a b)
          (by simpa [hdom_eq] using hx)
    have hs :
        (α : EReal) * ((s : ℝ) : EReal) + (1 - α : EReal) * ((s : ℝ) : EReal) = ((s : ℝ) : EReal) := by
      rw [ereal_convexCombination_eq]
      exact congrArg (fun t : ℝ ↦ (t : EReal)) (by ring : α * s + (1 - α) * s = s)
    rw [hcomb]
    simpa [hxval, hs] using (le_rfl : (((s : ℝ) : EReal)) ≤ (((s : ℝ) : EReal)))
  · have hα' : 0 < 1 - α := sub_pos.mpr hα1
    have hα'' : 1 - α < 1 := by
      linarith
    by_cases hx_nonpos : x ≤ 0
    · have hswap :=
        intervalResidualIcc_convexityCore_of_nonpositiveRight
          (φ := φ) (a := a) (b := b) hφ hy hx hyx hx_nonpos hzero_mem hα' hα'' rfl
      simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using hswap
    · have hx_pos : 0 < x := lt_of_not_ge hx_nonpos
      by_cases hy_nonneg : 0 ≤ y
      · have hswap :=
          intervalResidualIcc_convexityCore_of_nonnegativeLeft
            (φ := φ) (a := a) (b := b) hφ hy hx hy_nonneg hx_pos hzero_mem hα' hα'' rfl
        simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using hswap
      · have hy_neg : y < 0 := lt_of_not_ge hy_nonneg
        have hswap :=
          intervalResidualIcc_convexityCore_of_mixedSigns
            (φ := φ) (a := a) (b := b) hab hφ hsubIcc hy hx hy_neg hx_pos hzero_mem hα' hα''
            rfl
        simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using hswap

/-- Helper for Theorem 24.52: the bounded residual belongs to `Γ₀(ℝ)` by combining the left and
right affine-tilt convexity with the dedicated mixed-sign Jensen adapters. -/
private lemma intervalResidualIcc_mem_gammaZero
    {a b : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ)) (hsubIcc : (∂ φ) 0 = Set.Icc a b) :
    intervalResidualIcc φ hφ a b ∈ Γ₀(ℝ) := by
  rw [mem_gammaZero_iff]
  constructor
  · -- Lower semicontinuity is already packaged by the branchwise neighborhood analysis.
    simpa using intervalResidualIcc_lowerSemicontinuous
      (φ := φ) (hab := hab) (hφ := hφ) hsubIcc
  · have hzero_mem : 0 ∈ effectiveDomain φ :=
      zero_mem_effectiveDomain_of_subdifferential_zero_eq
        (Ω := Set.Icc a b) (Set.nonempty_Icc.2 hab) hφ hsubIcc
    refine ⟨⟨0, show 0 ∈ effectiveDomain (intervalResidualIcc φ hφ a b) from
      interior_subset (zero_memInterior_effectiveDomain_intervalResidualIcc hab hφ hsubIcc)⟩,
      subset_rfl, ?_⟩
    exact intervalResidualIcc_convexityCore (φ := φ) (a := a) (b := b) hab hφ hsubIcc
/-- Helper for Theorem 24.52: the bounded branch packages the already proved zero derivative for
the explicit source residual `intervalResidualIcc`. -/
private lemma intervalResidualIcc_package
    {a b : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ)) (hsubIcc : (∂ φ) 0 = Set.Icc a b) :
    let ψ := intervalResidualIcc φ hφ a b
    ψ ∈ Γ₀(ℝ) ∧ HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 := by
  let ψ := intervalResidualIcc φ hφ a b
  have hderiv :
      HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 := by
    simpa [ψ] using intervalResidualIcc_hasDerivAtZero
      (φ := φ) (hab := hab) (hφ := hφ) hsubIcc
  have hgamma : ψ ∈ Γ₀(ℝ) := by
    -- Route correction: discharge the package through the dedicated bounded `Γ₀` companion lemma
    -- instead of keeping the mixed-sign Jensen split inside the package proof.
    simpa [ψ] using intervalResidualIcc_mem_gammaZero
      (φ := φ) (hab := hab) (hφ := hφ) hsubIcc
  exact ⟨hgamma, hderiv⟩

/-- Helper for Theorem 24.52: the `Set.Iic b` case reduces to the `Γ₀` and derivative package for
the explicit source residual `halflineResidualIic`. -/
private lemma existsResidualWithZeroDeriv_of_subdifferentialZero_eq_Iic
    {b : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIic : (∂ φ) 0 = Set.Iic b) :
    ∃ ψ : ℝ → Set.Ioi (⊥ : EReal),
      ψ ∈ Γ₀(ℝ) ∧
        0 ∈ interior (effectiveDomain ψ) ∧
          HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 ∧
            φ = ψ + properIoi (σ[Set.Iic b]) (isProper_supportFunction_of_nonempty (Set.Iic b) ⟨b, by simp⟩) := by
  let ψ := halflineResidualIic φ hφ b
  have hgeometry : 0 ∈ interior (effectiveDomain ψ) := by
    simpa [ψ] using zero_memInterior_effectiveDomain_halflineResidualIic hφ hsubIic
  have hsplit :
      φ = ψ + properIoi (σ[Set.Iic b]) (isProper_supportFunction_of_nonempty (Set.Iic b) ⟨b, by simp⟩) := by
    simpa [ψ] using
      halflineResidualIic_add_supportFunction_eq (φ := φ) (hφ := hφ) (b := b) hsubIic
  have hpackage :
      ψ ∈ Γ₀(ℝ) ∧ HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 := by
    simpa [ψ] using halflineResidualIic_package (φ := φ) (hφ := hφ) hsubIic
  exact ⟨ψ, hpackage.1, hgeometry, hpackage.2, hsplit⟩

/-- Helper for Theorem 24.52: the `Set.Ici a` case reduces to the `Γ₀` and derivative package for
the explicit source residual `halflineResidualIci`. -/
private lemma existsResidualWithZeroDeriv_of_subdifferentialZero_eq_Ici
    {a : ℝ} (hφ : φ ∈ Γ₀(ℝ)) (hsubIci : (∂ φ) 0 = Set.Ici a) :
    ∃ ψ : ℝ → Set.Ioi (⊥ : EReal),
      ψ ∈ Γ₀(ℝ) ∧
        0 ∈ interior (effectiveDomain ψ) ∧
          HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 ∧
            φ = ψ + properIoi (σ[Set.Ici a]) (isProper_supportFunction_of_nonempty (Set.Ici a) ⟨a, by simp⟩) := by
  let ψ := halflineResidualIci φ hφ a
  have hgeometry : 0 ∈ interior (effectiveDomain ψ) := by
    simpa [ψ] using zero_memInterior_effectiveDomain_halflineResidualIci hφ hsubIci
  have hsplit :
      φ = ψ + properIoi (σ[Set.Ici a]) (isProper_supportFunction_of_nonempty (Set.Ici a) ⟨a, by simp⟩) := by
    simpa [ψ] using
      halflineResidualIci_add_supportFunction_eq (φ := φ) (hφ := hφ) (a := a) hsubIci
  have hpackage :
      ψ ∈ Γ₀(ℝ) ∧ HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 := by
    simpa [ψ] using halflineResidualIci_package (φ := φ) (hφ := hφ) hsubIci
  exact ⟨ψ, hpackage.1, hgeometry, hpackage.2, hsplit⟩

/-- Helper for Theorem 24.52: the bounded interval case reduces to the `Γ₀` and derivative package
for the explicit source residual `intervalResidualIcc`. -/
private lemma existsResidualWithZeroDeriv_of_subdifferentialZero_eq_Icc
    {a b : ℝ} (hab : a ≤ b) (hφ : φ ∈ Γ₀(ℝ)) (hsubIcc : (∂ φ) 0 = Set.Icc a b) :
    ∃ ψ : ℝ → Set.Ioi (⊥ : EReal),
      ψ ∈ Γ₀(ℝ) ∧
        0 ∈ interior (effectiveDomain ψ) ∧
          HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 ∧
            φ = ψ + properIoi (σ[Set.Icc a b])
              (isProper_supportFunction_of_nonempty (Set.Icc a b) (Set.nonempty_Icc.2 hab)) := by
  let ψ := intervalResidualIcc φ hφ a b
  have hgeometry : 0 ∈ interior (effectiveDomain ψ) := by
    simpa [ψ] using zero_memInterior_effectiveDomain_intervalResidualIcc hab hφ hsubIcc
  have hsplit :
      φ = ψ + properIoi (σ[Set.Icc a b])
        (isProper_supportFunction_of_nonempty (Set.Icc a b) (Set.nonempty_Icc.2 hab)) := by
    simpa [ψ] using
      intervalResidualIcc_add_supportFunction_eq (hab := hab) (φ := φ) (hφ := hφ) hsubIcc
  have hpackage :
      ψ ∈ Γ₀(ℝ) ∧ HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 := by
    simpa [ψ] using intervalResidualIcc_package
      (φ := φ) (hab := hab) (hφ := hφ) hsubIcc
  exact ⟨ψ, hpackage.1, hgeometry, hpackage.2, hsplit⟩

/-- Helper for Theorem 24.52: the proper support-function owner of `Set.univ` is the singleton
indicator at `0`. -/
private theorem supportOwner_univ_eq_indicator_singleton_zero :
    properIoi (σ[(Set.univ : Set ℝ)])
      (isProper_supportFunction_of_nonempty (Set.univ : Set ℝ) Set.univ_nonempty) =
        ι[({0} : Set ℝ)] := by
  funext ξ
  apply Subtype.ext
  by_cases hξ : ξ = 0
  · subst hξ
    simp [indicator_apply, supportFunction_zero_eq_zero_of_nonempty]
  · have hσ_top : σ[(Set.univ : Set ℝ)] ξ = ⊤ := by
      rw [supportFunction_eq_sSup_image, EReal.eq_top_iff_forall_lt]
      intro M
      have hlt :
          (M : EReal) <
            ((((M + 1) / ξ) * ξ : ℝ) : EReal) := by
        exact_mod_cast (show M < (((M + 1) / ξ) * ξ : ℝ) by
          field_simp [hξ]
          linarith)
      refine lt_of_lt_of_le hlt ?_
      exact le_sSup ⟨(M + 1) / ξ, by simp, by simp [real_inner_eq_mul, hξ]⟩
    simp [indicator_apply, hξ, hσ_top]

/-- Helper for Theorem 24.52: in the `Set.univ` branch, the constant residual and the support
owner of `Set.univ` recombine to `φ`. -/
private lemma originConstantResidual_add_supportFunction_univ_eq
    (hφ : φ ∈ Γ₀(ℝ)) (hsub_univ : (∂ φ) 0 = Set.univ) :
    φ =
      originConstantResidual φ +
        properIoi (σ[(Set.univ : Set ℝ)])
          (isProper_supportFunction_of_nonempty (Set.univ : Set ℝ) Set.univ_nonempty) := by
  rw [supportOwner_univ_eq_indicator_singleton_zero]
  have hzero_mem : 0 ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_subdifferential_zero_eq
      (Ω := Set.univ) Set.univ_nonempty hφ hsub_univ
  have hdom_zero : effectiveDomain φ = ({0} : Set ℝ) :=
    effectiveDomain_eq_singleton_zero_of_subdifferential_zero_eq_univ hzero_mem hsub_univ
  funext ξ
  apply Subtype.ext
  change (φ ξ : EReal) = (originConstantResidual φ ξ : EReal) + ι[({0} : Set ℝ)] ξ
  by_cases hξ : ξ = 0
  · subst hξ
    have hφ0_top : (φ 0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hzero_mem)
    have hφ0_bot : (φ 0 : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (φ 0 : EReal) from (φ 0).2)
    -- At the origin, the support owner vanishes and the constant residual is `φ 0`.
    simpa [originConstantResidual, indicator_apply] using
      (EReal.coe_toReal hφ0_top hφ0_bot).symm
  · have hξ_not_mem : ξ ∉ effectiveDomain φ := by
      rw [hdom_zero]
      simpa [Set.mem_singleton_iff] using hξ
    have hφ_top : (φ ξ : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hξ_not_mem))
    -- Off the origin, the indicator is `⊤`, so the sum is forced to `⊤` as well.
    rw [hφ_top]
    simp [originConstantResidual, indicator_apply, hξ]

/-- Helper for Theorem 24.52: the constant residual `ξ ↦ φ(0)` belongs to `Γ₀(ℝ)`. -/
private lemma originConstantResidual_mem_gammaZero :
    originConstantResidual φ ∈ Γ₀(ℝ) := by
  rw [mem_gammaZero_iff]
  constructor
  · -- The constant finite branch is continuous, hence lower semicontinuous.
    simpa [originConstantResidual, Function.asEReal] using
      (continuous_const : Continuous fun _ : ℝ ↦ ((φ 0 : EReal).toReal : EReal)).lowerSemicontinuous
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- The effective domain is all of `ℝ`, so it is certainly nonempty.
      refine ⟨0, ?_⟩
      rw [mem_effectiveDomain_iff]
      simp [originConstantResidual]
    · intro x hx y hy a ha0 ha1
      -- The convexity inequality is an equality because every branch has the same value.
      let c : ℝ := (φ 0 : EReal).toReal
      change ((c : ℝ) : EReal) ≤
        (a : EReal) * ((c : ℝ) : EReal) + (1 - a : EReal) * ((c : ℝ) : EReal)
      have hsub : (1 - (a : EReal)) = (((1 - a : ℝ)) : EReal) := by
        norm_num
      have hEq :
          (a : EReal) * ((c : ℝ) : EReal) + (1 - a : EReal) * ((c : ℝ) : EReal) =
            ((c : ℝ) : EReal) := by
        rw [hsub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
        exact_mod_cast (by ring : a * c + (1 - a) * c = c)
      rw [hEq]

/-- Theorem 24.52: on `ℝ`, a nonempty closed interval is represented canonically by a nonempty
closed convex set `Ω`. For `φ ∈ Γ₀(ℝ)`, the proximity operator `Prox_φ` is a proximal
thresholder on `Ω` if and only if `φ = ψ + σ_Ω` for some `ψ ∈ Γ₀(ℝ)` whose finite representative
is finite on a neighborhood of the origin and has derivative `0` there. -/
theorem prox_isProximalThresholderOn_iff_exists_eq_add_supportFunction_and_deriv_zero
    (hΩ_nonempty : Ω.Nonempty) (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hφ : φ ∈ Γ₀(ℝ)) :
    Function.IsProximalThresholderOn (Prox[φ, hφ]) Ω ↔
      ∃ ψ : ℝ → Set.Ioi (⊥ : EReal),
        ψ ∈ Γ₀(ℝ) ∧
          0 ∈ interior (effectiveDomain ψ) ∧
          HasDerivAt (fun y ↦ (ψ y : EReal).toReal) 0 0 ∧
            φ = ψ + properIoi (σ[Ω]) (isProper_supportFunction_of_nonempty Ω hΩ_nonempty) := by
  constructor
  · intro hprox
    -- Route correction: the forward implication now dispatches through the endpoint
    -- classification of `(∂ φ) 0`, and each endpoint shape uses its dedicated residual package.
    have hsub : (∂ φ) 0 = Ω :=
      (prox_isProximalThresholderOn_iff_subdifferential_zero_eq
        (f := φ) (Ω := Ω) (hf := hφ) hΩ_nonempty).1 hprox
    have hzero_mem : 0 ∈ effectiveDomain φ :=
      zero_mem_effectiveDomain_of_subdifferential_zero_eq
        (Ω := Ω) hΩ_nonempty hφ hsub
    have hΩ_interval : Ω = zeroSliceInterval φ := by
      calc
        Ω = (∂ φ) 0 := hsub.symm
        _ = zeroSliceInterval φ := by
          simpa [zeroSliceInterval, realPreimageIcc] using
            (subdifferential_eq_Icc_oneSidedDerivatives
              (f := φ) (hconv := hφ.2) hzero_mem)
    rcases
        subdifferentialZeroEndpointCases
          (Ω := Ω) hΩ_nonempty hzero_mem hφ hΩ_interval with
      hUniv | hIic | hIci | hIcc
    · rcases hUniv with ⟨_hleft_bot, _hright_top, hΩ_univ⟩
      cases hΩ_univ
      have hgeometry : 0 ∈ interior (effectiveDomain (originConstantResidual φ)) := by
        simpa [originConstantResidual, mem_effectiveDomain_iff]
      have hderiv0 : HasDerivAt (fun y ↦ (originConstantResidual φ y : EReal).toReal) 0 0 := by
        -- The `Set.univ` branch uses the constant residual from the source proof.
        simpa [originConstantResidual] using
          (hasDerivAt_const (x := (0 : ℝ)) ((φ 0 : EReal).toReal))
      have hsplit :
          φ =
            originConstantResidual φ +
              properIoi (σ[(Set.univ : Set ℝ)])
                (isProper_supportFunction_of_nonempty (Set.univ : Set ℝ) Set.univ_nonempty) := by
        exact originConstantResidual_add_supportFunction_univ_eq (φ := φ) hφ hsub
      refine ⟨originConstantResidual φ, originConstantResidual_mem_gammaZero (φ := φ),
        hgeometry, hderiv0, ?_⟩
      exact hsplit
    · rcases hIic with ⟨b, _hleft_bot, _hright_eq, hΩ_iic⟩
      cases hΩ_iic
      have hsubIic : (∂ φ) 0 = Set.Iic b := hsub
      rcases existsResidualWithZeroDeriv_of_subdifferentialZero_eq_Iic
          (φ := φ) (hφ := hφ) hsubIic with ⟨ψ, hψ_gamma, hψ_int, hψ_deriv, hψ_eq⟩
      refine ⟨ψ, hψ_gamma, hψ_int, hψ_deriv, ?_⟩
      exact hψ_eq
    · rcases hIci with ⟨a, _hleft_eq, _hright_top, hΩ_ici⟩
      cases hΩ_ici
      have hsubIci : (∂ φ) 0 = Set.Ici a := hsub
      rcases existsResidualWithZeroDeriv_of_subdifferentialZero_eq_Ici
          (φ := φ) (hφ := hφ) hsubIci with ⟨ψ, hψ_gamma, hψ_int, hψ_deriv, hψ_eq⟩
      refine ⟨ψ, hψ_gamma, hψ_int, hψ_deriv, ?_⟩
      exact hψ_eq
    · rcases hIcc with ⟨a, b, _hleft_eq, _hright_eq, hΩ_icc⟩
      cases hΩ_icc
      have hab : a ≤ b := by
        exact Set.nonempty_Icc.mp hΩ_nonempty
      have hsubIcc : (∂ φ) 0 = Set.Icc a b := hsub
      rcases existsResidualWithZeroDeriv_of_subdifferentialZero_eq_Icc
          (φ := φ) (hφ := hφ) hab hsubIcc with ⟨ψ, hψ_gamma, hψ_int, hψ_deriv, hψ_eq⟩
      refine ⟨ψ, hψ_gamma, hψ_int, hψ_deriv, ?_⟩
      exact hψ_eq
  · rintro ⟨ψ, hψ, hzero_int, hderiv0, hsplit⟩
    -- Proposition 24.49 closes the reverse implication once the support split and zero gradient
    -- are packaged in the canonical Chapter 24 form.
    have hgateaux :
        HasGateauxDerivativeAt (fun y ↦ (ψ y : EReal).toReal)
          (InnerProductSpace.toDualMap ℝ ℝ (0 : ℝ)) 0 := by
      simpa [HasGateauxDerivativeAt] using
        hderiv0.hasFDerivAt.hasGateauxDerivativeAt
    have hsub : (∂ φ) 0 = Ω :=
      subdifferential_zero_eq_of_eq_add_supportFunction_and_zero_gradient
        (f := φ) (Ω := Ω) hΩ_nonempty hΩ_closed hΩ_convex ψ hψ hzero_int hgateaux
        hsplit
    exact
      (prox_isProximalThresholderOn_iff_subdifferential_zero_eq
        (f := φ) (Ω := Ω) (hf := hφ) hΩ_nonempty).2 hsub

end RealProximalThresholding

end

end ERealFunction
