import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.LocallyConvex.Separation
import Integer.Chapters.Chap08.subgradient

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Semantic recall note: the Chapter 8 owner for the affine subgradient inequality on a comparison
-- set is `IsSubgradientAtOn` from `Integer.Chapters.Chap08.subgradient`. Exercise 8.9 uses that
-- canonical owner directly at the whole-space comparison set `Set.univ`.

section Exercise89

variable {n : ℕ}

/-- A vector `s` is a subgradient of `g` at `x` when the affine lower bound defined by `s`
holds on all of `ℝ^n`. This is the whole-space specialization of `IsSubgradientAtOn`. -/
abbrev IsSubgradientAt
    (g : (Fin n → ℝ) → ℝ)
    (x s : Fin n → ℝ) : Prop :=
  IsSubgradientAtOn g Set.univ x s

namespace IsSubgradientAt

/-- A whole-space subgradient yields the affine lower bound at every comparison point. -/
theorem ineq
    {g : (Fin n → ℝ) → ℝ}
    {x s : Fin n → ℝ}
    (hs : IsSubgradientAt g x s)
    (y : Fin n → ℝ) :
    g y ≥ g x + ∑ i, s i * (y i - x i) := by
  simpa [IsSubgradientAt, IsSubgradientAtOn] using hs y (by simp)

end IsSubgradientAt

/-- To prove `IsSubgradientAt g x s`, it suffices to establish the affine lower bound at every
comparison point `y`. -/
theorem isSubgradientAt_of_ineq
    {g : (Fin n → ℝ) → ℝ}
    {x s : Fin n → ℝ}
    (hs : ∀ y : Fin n → ℝ, g y ≥ g x + ∑ i, s i * (y i - x i)) :
    IsSubgradientAt g x s := by
  intro y hy
  simpa using hs y

/-- Helper for Exercise 8.9: a continuous linear functional on `Fin n → ℝ` is determined by its
values on the coordinate singletons `Pi.single i 1`. -/
lemma continuousLinearMap_apply_eq_sumSingle
    (ℓ : (Fin n → ℝ) →L[ℝ] ℝ)
    (y : Fin n → ℝ) :
    ℓ y = ∑ i, ℓ (Pi.single i 1) * y i := by
  -- Expand `y` in the standard basis given by the coordinate singletons.
  have hy : y = ∑ i, y i • Pi.single i 1 := by
    ext i
    simp [Pi.single_apply]
  have hℓy : ℓ y = ℓ (∑ i, y i • Pi.single i 1) := by
    exact congrArg ℓ hy
  calc
    ℓ y = ℓ (∑ i, y i • Pi.single i 1) := hℓy
    _ = ∑ i, ℓ (y i • Pi.single i 1) := by
      rw [map_sum]
    _ = ∑ i, ℓ (Pi.single i 1) * y i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [map_smul]
      ring

/-- Helper for Exercise 8.9: a supporting affine functional with negative scalar coefficient on the
epigraph produces a whole-space subgradient. -/
lemma subgradientOfSupportingFunctional
    {g : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ}
    (ℓ : (Fin n → ℝ) →L[ℝ] ℝ)
    {a : ℝ}
    (ha : a < 0)
    (hsupport : ∀ y : Fin n → ℝ, ℓ y + a * g y ≤ ℓ x + a * g x) :
    ∃ s : Fin n → ℝ, IsSubgradientAt g x s := by
  let b : ℝ := (-a)⁻¹
  let s : Fin n → ℝ := fun i ↦ b * ℓ (Pi.single i 1)
  have hb : 0 < b := by
    dsimp [b]
    exact inv_pos.2 (by linarith)
  have hsum (z : Fin n → ℝ) : ∑ i, s i * z i = b * ℓ z := by
    -- Factor the common scalar `b` out of the coordinate expansion of `ℓ`.
    calc
      ∑ i, s i * z i = ∑ i, b * (ℓ (Pi.single i 1) * z i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        dsimp [s]
        ring
      _ = b * ∑ i, ℓ (Pi.single i 1) * z i := by
        rw [Finset.mul_sum]
      _ = b * ℓ z := by
        rw [continuousLinearMap_apply_eq_sumSingle]
  refine ⟨s, isSubgradientAt_of_ineq ?_⟩
  intro y
  -- Rearrange the supporting-functional inequality into the standard subgradient bound.
  have hscaled : ℓ y - ℓ x ≤ (-a) * (g y - g x) := by
    linarith [hsupport y]
  have hdiv : b * (ℓ y - ℓ x) ≤ g y - g x := by
    have hmul := mul_le_mul_of_nonneg_left hscaled (le_of_lt hb)
    have hnegane : (-a) ≠ 0 := by
      linarith
    have hcancel : b * (-a) = 1 := by
      dsimp [b]
      exact inv_mul_cancel₀ hnegane
    calc
      b * (ℓ y - ℓ x) ≤ b * ((-a) * (g y - g x)) := hmul
      _ = (b * (-a)) * (g y - g x) := by
        ring
      _ = g y - g x := by
        rw [hcancel, one_mul]
  have hsumSub : ∑ i, s i * (y i - x i) = b * (ℓ y - ℓ x) := by
    calc
      ∑ i, s i * (y i - x i) = b * ℓ (y - x) := by
        simpa using hsum (y - x)
      _ = b * (ℓ y - ℓ x) := by
        rw [ℓ.map_sub]
  have : g x + b * (ℓ y - ℓ x) ≤ g y := by
    linarith
  simpa [hsumSub] using this

/-- Exercise 8.9. Every convex function `g : ℝ^n → ℝ` admits a subgradient at each point
`λ_star : ℝ^n`. -/
theorem convex_function_has_subgradient_at
    (g : (Fin n → ℝ) → ℝ)
    (lambdaStar : Fin n → ℝ)
    (hconvex : ConvexOn ℝ Set.univ g) :
    ∃ s : Fin n → ℝ, IsSubgradientAt g lambdaStar s := by
  let S : Set ((Fin n → ℝ) × ℝ) := {p | g p.1 < p.2}
  have hcontOn : ContinuousOn g Set.univ := hconvex.continuousOn isOpen_univ
  have hcont : Continuous g := by
    simpa [continuousOn_univ] using hcontOn
  have hSconvex : Convex ℝ S := by
    simpa [S] using hconvex.convex_strict_epigraph
  have hSopen : IsOpen S := by
    -- The strict epigraph is open because `p ↦ g p.1` and `p ↦ p.2` are continuous.
    simpa [S] using isOpen_lt (hcont.comp continuous_fst) continuous_snd
  have hxnot : (lambdaStar, g lambdaStar) ∉ S := by
    simp [S]
  obtain ⟨f, hstrict⟩ := geometric_hahn_banach_open_point hSconvex hSopen hxnot
  let ℓ : (Fin n → ℝ) →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ)
  let a : ℝ := f (0, 1)
  have hprod (y : Fin n → ℝ) (t : ℝ) : f (y, t) = ℓ y + a * t := by
    have hsmul : ((0 : Fin n → ℝ), t) = t • ((0 : Fin n → ℝ), (1 : ℝ)) := by
      ext i <;> simp
    -- Split the product-space functional into its `ℝ^n` part and scalar part.
    calc
      f (y, t) = f ((y, 0) + (0, t)) := by
        simp
      _ = f (y, 0) + f (0, t) := by
        rw [map_add]
      _ = ℓ y + f (0, t) := by
        simp [ℓ]
      _ = ℓ y + a * t := by
        rw [hsmul, map_smul]
        simp [a, mul_comm]
  have hstrictPoint : (lambdaStar, g lambdaStar + 1) ∈ S := by
    simp [S]
  have ha : a < 0 := by
    -- Evaluating the strict support inequality one unit above the graph point forces a negative
    -- coefficient on the vertical coordinate.
    have h := hstrict (lambdaStar, g lambdaStar + 1) hstrictPoint
    simpa [hprod, mul_add, add_comm, add_left_comm, add_assoc] using h
  have htwo : (2 : ℝ) ≠ 0 := by
    norm_num
  have hsupportEpigraph {y : Fin n → ℝ} {t : ℝ} (ht : g y ≤ t) :
      f (y, t) ≤ f (lambdaStar, g lambdaStar) := by
    by_contra hgt
    let δ : ℝ := f (y, t) - f (lambdaStar, g lambdaStar)
    let ε : ℝ := δ / (2 * (-a))
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    have hε : 0 < ε := by
      have hden : 0 < 2 * (-a) := by
        nlinarith
      dsimp [ε]
      exact div_pos hδ hden
    have hmem : (y, t + ε) ∈ S := by
      have : g y < t + ε := by
        linarith
      simp [S, this]
    have hstrict' := hstrict (y, t + ε) hmem
    have hmean : f (y, t + ε) = (f (y, t) + f (lambdaStar, g lambdaStar)) / 2 := by
      have hane : a ≠ 0 := by
        linarith
      -- Choose `ε` so that the shifted value is exactly the midpoint between the two functional
      -- values, contradicting strict separation.
      calc
        f (y, t + ε) = f (y, t) + a * ε := by
          rw [hprod, hprod]
          ring
        _ = (f (y, t) + f (lambdaStar, g lambdaStar)) / 2 := by
          dsimp [ε, δ]
          field_simp [hane, htwo]
          ring
    have hmid : f (lambdaStar, g lambdaStar) < f (y, t + ε) := by
      rw [hmean]
      linarith
    linarith
  have hsupportGraph (y : Fin n → ℝ) :
      ℓ y + a * g y ≤ ℓ lambdaStar + a * g lambdaStar := by
    -- Move from strict epigraph separation to the graph by a vanishing upward perturbation.
    have h := hsupportEpigraph (y := y) (t := g y) le_rfl
    simpa [hprod] using h
  exact subgradientOfSupportingFunctional ℓ ha hsupportGraph

end Exercise89
