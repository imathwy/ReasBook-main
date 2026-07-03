import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_13 (from Chap03) -/
section

/- Definition 3.13 is `source-facing` at the finite-set median set itself. There is no earlier
chapter owner or mathlib owner for this exact notion, so the public root stays `median_set A :
Set ℝ`. The pointwise notion of being a median is expressed directly by membership
`β ∈ median_set A`, and the middle tuple indices below are represented by canonical `Fin.ofNat`
terms rather than local wrapper definitions. -/

/-- Definition 3.13: `median_set A` is the set of real numbers `β` such that at least half of the
elements of the finite nonempty set `A` lie below `β` and at least half lie above `β`. -/
def median_set (A : Finset ℝ) : Set ℝ :=
  {β |
    A.Nonempty ∧
      A.card ≤ 2 * (A.filter (fun a ↦ a ≤ β)).card ∧
        A.card ≤ 2 * (A.filter (fun a ↦ β ≤ a)).card}

/-- Membership in `median_set A` is equivalent to satisfying the two median-count inequalities. -/
@[simp] lemma mem_median_set_iff {A : Finset ℝ} {β : ℝ} :
    β ∈ median_set A ↔
      A.Nonempty ∧
        A.card ≤ 2 * (A.filter (fun a ↦ a ≤ β)).card ∧
          A.card ≤ 2 * (A.filter (fun a ↦ β ≤ a)).card :=
  Iff.rfl

-- Proof sketch: for a strictly increasing tuple of odd length, exactly `m + 1` entries lie below
-- the middle element and exactly `m + 1` entries lie above it, while any other candidate fails
-- one of the two counting inequalities.
/-- For a strictly increasing odd tuple, the median set is the singleton containing the middle
entry. -/
theorem median_set_eq_singleton_of_strictMono_odd (m : ℕ) (a : Fin (2 * m + 1) → ℝ)
    (ha : StrictMono a) :
    median_set (Finset.univ.image a) = ({a (Fin.ofNat (2 * m + 1) m)} : Set ℝ) := sorry

-- Proof sketch: for a strictly increasing tuple of even length `2 * (m + 1)`, the two counting
-- inequalities hold exactly for those `β` between the two middle entries `a_m` and `a_{m+1}`.
/-- For a strictly increasing even tuple, the median set is the closed interval between the two
middle entries. -/
theorem median_set_eq_Icc_of_strictMono_even (m : ℕ) (a : Fin (2 * (m + 1)) → ℝ)
    (ha : StrictMono a) :
    median_set (Finset.univ.image a) =
      Set.Icc (a (Fin.ofNat (2 * (m + 1)) m)) (a (Fin.ofNat (2 * (m + 1)) (m + 1))) := sorry

end

/-! ### Proposition_3_13 (from Chap03) -/
open Matrix
open scoped Gradient Matrix

noncomputable section

section

variable {m : ℕ}

-- Internal elaboration bridge to the owner theorem `FiniteDimensional.complete` for the
-- `H`-weighted normed-space structure induced by `Matrix.toNormedAddCommGroup`.
private theorem posDefMatrixCompleteSpace (H : Matrix (Fin m) (Fin m) ℝ) (hH : H.PosDef) :
    @CompleteSpace (Fin m → ℝ) (H.toNormedAddCommGroup hH).toUniformSpace := by
  sorry

variable (H : Matrix (Fin m) (Fin m) ℝ) (hH : H.PosDef)

/- Proposition 3.13 is a `bridge/view` item in the chapter calculus API. The source-facing input is
the Euclidean Fréchet derivative represented by `D`, while the weighted Hilbert-space owners are
`Matrix.toNormedAddCommGroup`, `Matrix.toInnerProductSpace`, and the canonical completeness result
`FiniteDimensional.complete`. -/

-- Proof sketch: under the `H`-weighted inner product, the derivative functional `v ↦ dotProduct D
-- v` is exactly the Riesz image of `(H⁻¹).mulVec D`. First transfer the Euclidean `HasFDerivAt`
-- hypothesis to the equivalent `H`-weighted norm, then apply the `HasFDerivAt`/`HasGradientAt`
-- bridge in that weighted inner-product structure.

/-- Proposition 3.13: if the Fréchet derivative of `f` at `x` is represented by `D` through the
standard Euclidean dot product on `ℝ^m`, then replacing the inner product by
`⟪u, v⟫ = dotProduct u (H.mulVec v)` for a positive definite matrix `H` changes the gradient to
`(H⁻¹).mulVec D`. -/
theorem hasGradientAt_inv_mulVec_of_posDef_matrix_inner
    {f : (Fin m → ℝ) → ℝ} {x D : Fin m → ℝ}
    (hD : HasFDerivAt f (LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ D)) x) :
    letI := H.toNormedAddCommGroup hH
    letI := H.toInnerProductSpace hH.posSemidef
    letI := posDefMatrixCompleteSpace H hH
    HasGradientAt f ((H⁻¹).mulVec D) x := by
  sorry

-- Proof sketch: apply `HasGradientAt.gradient` to
-- `hasGradientAt_inv_mulVec_of_posDef_matrix_inner`.
/-- The totalized gradient for the `H`-weighted inner product agrees with the vector
`(H⁻¹).mulVec D` whenever the derivative is the Euclidean pairing functional
`v ↦ dotProduct D v`. -/
theorem gradient_eq_inv_mulVec_of_posDef_matrix_inner
    {f : (Fin m → ℝ) → ℝ} {x D : Fin m → ℝ}
    (hD : HasFDerivAt f (LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ D)) x) :
    letI := H.toNormedAddCommGroup hH
    letI := H.toInnerProductSpace hH.posSemidef
    letI := posDefMatrixCompleteSpace H hH
    gradient f x = (H⁻¹).mulVec D := by
  letI := H.toNormedAddCommGroup hH
  letI := H.toInnerProductSpace hH.posSemidef
  letI := posDefMatrixCompleteSpace H hH
  exact (hasGradientAt_inv_mulVec_of_posDef_matrix_inner H hH hD).gradient

end

/-! ### Theorem_3_13 (from Chap03) -/
open InnerProductSpace (toDual)
open scoped Gradient

universe u

noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 3.13 is a `bridge/view` item in the chapter convex-analysis API. The source-facing
owners remain `effective_domain`, `finite_domain`, `is_convex_function`, and the extended-real
differentiability predicate `is_differentiable_at` from Definition 3.10, while the singleton
conclusion naturally lives on the continuous-dual bridge `strongDualSubdifferential`, because
`toDual` lands in `StrongDual ℝ E`. Here differentiability already supplies the interior
finite-domain hypothesis, and for a convex extended-real-valued function that interior finite point
forces the global no-`⊥` property needed by the directional-derivative owner theorem, so that
codomain restriction is derived API rather than primitive public data. -/
recall effective_domain
recall finite_domain
recall is_convex_function
recall is_differentiable_at
recall strongDualSubdifferential

-- Proof sketch: unpack `hdiff` as `x ∈ interior (finite_domain f)` plus differentiability of
-- `y ↦ (f y).toReal` at `x`. For a convex extended-real-valued function, that interior finite point
-- rules out `⊥` globally, so the owner max formula for directional derivatives applies without a
-- primitive public `h_ne_bot` hypothesis. It identifies the directional derivative with the
-- pairing against the gradient. For any `g ∈ strongDualSubdifferential f x`, the max formula bounds
-- `g d` by that directional derivative for every direction `d`, and applying this to both `d` and
-- `-d` forces `g` to coincide with the dual vector represented by
-- `∇ (fun y ↦ (f y).toReal) x`. Nonemptiness of the subdifferential at the interior finite point
-- then gives the stated singleton equality.
/-- Theorem 3.13 (1): if a convex extended-real-valued function is differentiable at a point in the
chapter sense `is_differentiable_at`, then its continuous-dual subdifferential there is the
singleton consisting of the dual vector represented by the gradient. -/
theorem subdifferential_eq_singleton_gradient_of_differentiableAt
    (f : E → EReal) (x : E) (hconvex : is_convex_function f) (hdiff : is_differentiable_at f x) :
    strongDualSubdifferential f x =
      {toDual ℝ E (∇ (fun y ↦ (f y).toReal) x)} := sorry

-- Proof sketch: the interior-point theorem `subdifferential_nonempty_at_interior_point` upgrades
-- the owner-set uniqueness hypothesis `Set.Subsingleton (strongDualSubdifferential f x)` to an
-- actual singleton description. Since `x ∈ interior (finite_domain f)`, it also lies in the
-- interior of `effective_domain f`, and convexity forces the ambient no-`⊥` property needed by
-- the directional-derivative owner theorem, so no stronger primitive hypothesis is needed
-- publicly. Let `g` be that unique subgradient. Translate the function by `x` and subtract the
-- affine functional defined by `g`; the resulting convex function still avoids `⊥` and has unique
-- subgradient `0` at the origin. The max formula then gives vanishing directional derivatives in
-- every direction, and the standard finite-dimensional convex argument upgrades this to
-- differentiability at the origin. Translating back yields differentiability of
-- `y ↦ (f y).toReal` at `x`, and the forward implication identifies the subdifferential with the
-- singleton of the gradient.
/-- Theorem 3.13 (2): if a convex extended-real-valued function has a unique continuous-dual
subgradient at an interior point of its finite domain, then the real-valued map
`y ↦ (f y).toReal` is differentiable there, equivalently `f` is differentiable there in the
chapter sense `is_differentiable_at`, and the subdifferential is the singleton of the
corresponding gradient. -/
theorem differentiableAt_and_subdifferential_eq_singleton_gradient_of_unique_subgradient
    (f : E → EReal) (x : E) (hconvex : is_convex_function f)
    (hx : x ∈ interior (finite_domain f))
    (hunique : (strongDualSubdifferential f x).Subsingleton) :
    is_differentiable_at f x ∧
      strongDualSubdifferential f x =
        {toDual ℝ E (∇ (fun y ↦ (f y).toReal) x)} := sorry
