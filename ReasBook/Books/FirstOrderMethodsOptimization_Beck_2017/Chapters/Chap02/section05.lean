import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_5 (from Chap02) -/
universe u

open Filter Metric
open scoped Topology

variable {E : Type u}

/-- A proper extended-real-valued function never takes the value `-∞` and has nonempty effective
domain. -/
class IsProperExtendedRealFunction (f : E → EReal) : Prop where
  ne_bot : ∀ x, f x ≠ ⊥
  effective_domain_nonempty : (effective_domain f).Nonempty

section

variable [NormedAddCommGroup E]

/-- Definition 2.5: a proper extended-real-valued function is coercive when its values tend to
`∞` along the filter `‖x‖ → ∞`. -/
class IsCoerciveExtendedRealFunction (f : E → EReal) : Prop
    extends IsProperExtendedRealFunction f where
  tendsto_top : Tendsto f (comap norm atTop) (𝓝 (⊤ : EReal))

section

variable [ProperSpace E] {f : E → EReal}

-- Proof sketch: use the coercive field `hf.tendsto_top`, rewrite `comap norm atTop` as
-- `cobounded E` via `comap_norm_atTop`, then identify `cobounded E` with `cocompact E` on a
-- proper space.
/-- On a proper normed group, a coercive extended-real-valued function tends to `∞` along the
cocompact filter. -/
theorem IsCoerciveExtendedRealFunction.tendsto_top_cocompact
    (hf : IsCoerciveExtendedRealFunction f) : Tendsto f (cocompact E) (𝓝 (⊤ : EReal)) := by
  simpa [comap_norm_atTop', cobounded_eq_cocompact] using hf.tendsto_top

/-- On a proper normed group, coercivity supplies the cocompact `Fact` needed for downstream
minimization arguments. -/
instance instFactTendstoTopCocompact [hf : IsCoerciveExtendedRealFunction f] :
    Fact (Tendsto f (cocompact E) (𝓝 (⊤ : EReal))) where
  out := hf.tendsto_top_cocompact

end

end

/-! ### Example_2_5 (from Chap02) -/
universe u

section

open Metric Set

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The distance-based potential `x ↦ (‖x‖² - d_C(x)²) / 2` associated to a set in a real inner
product space. -/
noncomputable def euclidean_distance_potential (C : Set E) : E → ℝ :=
  fun x ↦ (‖x‖ ^ 2 - infDist x C ^ 2) / 2

-- Proof sketch: expand `Metric.infDist` as the infimum of the distance function, use the identity
-- `‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ y x + ‖y‖ ^ 2`, and rewrite a constant minus an infimum
-- as the corresponding supremum.
/-- The distance-based potential agrees with the supremum of the affine functions
`x ↦ inner ℝ y x - ‖y‖² / 2` indexed by `y ∈ C`. -/
theorem euclidean_distance_potential_eq_sSup_affine (C : Set E) (hC : C.Nonempty) (x : E) :
    euclidean_distance_potential C x =
      sSup ((fun y : E ↦ inner ℝ y x - (‖y‖ ^ 2) / 2) '' C) := sorry

-- Proof sketch: if `C = ∅`, then `Metric.infDist x C = 0`, so the function is `x ↦ ‖x‖² / 2`,
-- which is convex. Otherwise rewrite with `euclidean_distance_potential_eq_sSup_affine`; each term
-- `x ↦ inner ℝ y x - ‖y‖² / 2` is affine, hence convex, and a pointwise supremum of such affine
-- functions is convex.
/-- Example 2.5: for a subset `C` of a real inner product space, the function
`x ↦ (‖x‖² - d_C(x)²) / 2` is convex. -/
theorem euclidean_distance_potential_convex (C : Set E) :
    ConvexOn ℝ univ (euclidean_distance_potential C) := sorry

end

/-! ### Lemma_2_5 (from Chap02) -/
open Matrix

section

variable {m n : ℕ}

-- Proof sketch: reduce this formulation to the first Farkas lemma by adjoining the inequality
-- `-dotProduct c x ≤ -1` to `A *ᵥ x ≤ 0`, and conversely evaluate the certificate
-- `Aᵀ *ᵥ y = c` on any `x` with `A *ᵥ x ≤ 0` to obtain `dotProduct c x ≤ 0` from the
-- coordinatewise nonnegativity of `y`.
/-- Lemma 2.5: Farkas's lemma in the implication form. For a real matrix `A` and vector `c`, the
implication `A x ≤ 0 → cᵀ x ≤ 0` for every `x` is equivalent to the existence of a nonnegative
vector `y` with `Aᵀ y = c`; here `ℝ^m_+` is rendered as `Set.Ici (0 : Fin m → ℝ)`. -/
theorem farkas_lemma_second_formulation
    (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    (∀ x : Fin n → ℝ, A *ᵥ x ≤ (0 : Fin m → ℝ) → dotProduct c x ≤ 0) ↔
      ∃ y ∈ Set.Ici (0 : Fin m → ℝ), Aᵀ *ᵥ y = c := sorry

/-- Bridge/view: the certificate in Lemma 2.5 is equivalently membership of `c` in the image of
the positive pointed cone under the transpose linear map `Aᵀ`. -/
theorem farkas_lemma_second_formulation_iff_mem_positive_map
    (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    (∀ x : Fin n → ℝ, A *ᵥ x ≤ (0 : Fin m → ℝ) → dotProduct c x ≤ 0) ↔
      c ∈ (PointedCone.positive ℝ (Fin m → ℝ)).map Aᵀ.mulVecLin := by
  have h_certificate :
      (∃ y ∈ Set.Ici (0 : Fin m → ℝ), Aᵀ *ᵥ y = c) ↔
        c ∈ (PointedCone.positive ℝ (Fin m → ℝ)).map Aᵀ.mulVecLin := by
    rw [PointedCone.mem_map]
    constructor
    · rintro ⟨y, hy, hyc⟩
      refine ⟨y, ?_, ?_⟩
      · simpa using hy
      have hyc' : y ᵥ* A = c := (Matrix.mulVec_transpose A y).symm.trans hyc
      simpa [Matrix.mulVecLin_apply] using hyc'
    · rintro ⟨y, hy, hyc⟩
      refine ⟨y, ?_, ?_⟩
      · simpa using hy
      have hyc' : y ᵥ* A = c := by
        simpa [Matrix.mulVecLin_apply] using hyc
      exact (Matrix.mulVec_transpose A y).trans hyc'
  exact (farkas_lemma_second_formulation c A).trans h_certificate

end

/-! ### Proposition_2_5 (from Chap02) -/
section

-- Proof sketch: write the constraint as `x 0 ≤ -(x 1 ^ 2) / 2`. If `0 < y 0`, then for each fixed
-- `x 1` the pairing is maximized at the boundary value `x 0 = -(x 1 ^ 2) / 2`, reducing the
-- problem to maximizing a concave quadratic in `x 1`, whose maximum is `y 1 ^ 2 / (2 * y 0)`.
-- If `y 0 < 0`, then sending `x 0 → -∞` makes the pairing tend to `⊤`. If `y 0 = 0` and
-- `y 1 ≠ 0`, evaluating on boundary points gives arbitrarily large values. At `y = 0`, every
-- pairing is `0`, so the support function is `0`.
/-- Proposition 2.5: for the set `C = {(x₁, x₂) | x₁ + x₂^2 / 2 ≤ 0}` in `ℝ²`, the support
function, viewed through the Euclidean-dual identification, equals `y₂^2 / (2 y₁)` when
`y₁ > 0`, equals `0` at the origin, and equals `⊤` otherwise. -/
theorem support_function_parabolic_region (y : EuclideanSpace ℝ (Fin 2)) :
    support_function {x : EuclideanSpace ℝ (Fin 2) | x 0 + x 1 ^ 2 / 2 ≤ 0}
        (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin 2)) y) =
      if 0 < y 0 then ((((y 1 : ℝ) ^ 2) / (2 * y 0) : ℝ) : EReal)
      else if y = 0 then (0 : EReal)
      else ⊤ := sorry

end

/-! ### Theorem_2_5 (from Chap02) -/
universe u

open Set Filter

variable {E : Type u} [NormedAddCommGroup E] [ProperSpace E]

section

-- Proof sketch: choose `x₀ ∈ S ∩ effective_domain f`. The chapter owner abstraction
-- `IsCoerciveExtendedRealFunction f` supplies `Tendsto f (cocompact E) (𝓝 (⊤ : EReal))`; applying
-- `EReal.tendsto_nhds_top_iff_real` at the finite value `f x₀` gives
-- `∀ᶠ x in cocompact E ⊓ 𝓟 S, f x₀ ≤ f x`. Apply `LowerSemicontinuousOn.exists_isMinOn` to the
-- compact closed subset obtained by adjoining `x₀` to that compact part of `S`, then compare with
-- points outside the compact set using the eventual lower bound.
/-- Theorem 2.5: a proper closed coercive extended-real-valued function, equivalently here a lower
semicontinuous coercive function, attains its minimum on every closed set `S` meeting its
effective domain. -/
theorem attains_min_on_closed_set_of_coercive (f : E → EReal) {S : Set E}
    (hf : LowerSemicontinuous f) (hcoercive : IsCoerciveExtendedRealFunction f)
    (hS_closed : IsClosed S) (hS_dom : (S ∩ effective_domain f).Nonempty) :
    ∃ x ∈ S, IsMinOn f S x := by
  obtain ⟨x₀, hx₀S, hx₀dom⟩ := hS_dom
  have hx₀_top : f x₀ ≠ ⊤ := hx₀dom.ne
  have hx₀_bot : f x₀ ≠ ⊥ := hcoercive.ne_bot x₀
  have hx₀_eq : (((f x₀).toReal : ℝ) : EReal) = f x₀ := EReal.coe_toReal hx₀_top hx₀_bot
  have htop :
      ∀ᶠ x in cocompact E, (((f x₀).toReal : ℝ) : EReal) < f x :=
    (EReal.tendsto_nhds_top_iff_real.mp hcoercive.tendsto_top_cocompact) (f x₀).toReal
  have hbound : ∀ᶠ x in cocompact E ⊓ 𝓟 S, f x₀ ≤ f x := by
    filter_upwards [htop.filter_mono inf_le_left] with x hx
    exact (by simpa [hx₀_eq] using hx : f x₀ < f x).le
  rcases (hasBasis_cocompact.inf_principal S).eventually_iff.1 hbound with ⟨K, hK, hKf⟩
  let T : Set E := insert x₀ (K ∩ S)
  have hTS : T ⊆ S := insert_subset_iff.2 ⟨hx₀S, inter_subset_right⟩
  have hT_compact : IsCompact T := (hK.inter_right hS_closed).insert x₀
  obtain ⟨x, hxT, hxmin⟩ := (hf.lowerSemicontinuousOn T).exists_isMinOn (insert_nonempty x₀ _) hT_compact
  refine ⟨x, hTS hxT, ?_⟩
  intro y hyS
  by_cases hyK : y ∈ K
  · exact isMinOn_iff.mp hxmin y (Or.inr ⟨hyK, hyS⟩)
  · exact (isMinOn_iff.mp hxmin x₀ (Or.inl rfl)).trans (hKf ⟨hyK, hyS⟩)

end
