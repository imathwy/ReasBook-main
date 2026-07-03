import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_3_33 (from Chap03) -/
section

variable {n : ℕ}

local notation "Δ" => stdSimplex ℝ (Fin n)

/- Corollary 3.33 is a `source-facing` simplex specialization of the owner constrained-optimality
criterion `isMinOn_iff_exists_subgradient_neg_mem_normal_cone` from Theorem 3.31, together with
the simplex normal-cone bridge
`neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_exists_multiplier` from Proposition 3.34.
This file therefore keeps only the simplex-specific statement and reuses the upstream
convex-analysis API directly. -/
recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall subdifferential
recall normal_cone
recall isMinOn_iff_exists_subgradient_neg_mem_normal_cone
recall neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_exists_multiplier

-- Proof sketch: apply the constrained convex optimality criterion under the qualification
-- `ri(Δ_n) ∩ ri(dom f) ≠ ∅` to obtain a subgradient whose negation lies in the owner normal cone
-- of the simplex at `xStar`. Transport that dual vector to coordinates by `dotProductEquiv`, and
-- then use Proposition 3.34 to identify the resulting normal-cone condition with the existence of
-- a scalar multiplier that is constant on the positive support of `xStar` and bounded above by the
-- remaining coordinates.
/-- Corollary 3.33: under the relative-interior qualification
`ri(Δ_n) ∩ ri(dom f) ≠ ∅`, a point `xStar ∈ Δ_n = stdSimplex ℝ (Fin n)` minimizes `f` on the unit
simplex if and only if there exist a subgradient vector `g` at `xStar`, identified with the dual
space by `dotProductEquiv`, and a scalar `μ` such that `g i = μ` whenever `xStar i > 0` and
`μ ≤ g i` whenever `xStar i = 0`. -/
theorem isMinOn_stdSimplex_iff_exists_subgradient_vector_and_multiplier
    {f : (Fin n → ℝ) → EReal} (hf : IsProperExtendedRealFunction f)
    (hconv : is_convex_function f)
    (hri : (intrinsicInterior ℝ Δ ∩ intrinsicInterior ℝ (effective_domain f)).Nonempty)
    {xStar : Fin n → ℝ} (hxStar : xStar ∈ Δ) :
    IsMinOn f Δ xStar ↔
      ∃ g : Fin n → ℝ,
        dotProductEquiv ℝ (Fin n) g ∈ subdifferential f xStar ∧
          ∃ μ : ℝ, IsStdSimplexMultiplier xStar g μ := by
  have hΔ : Convex ℝ Δ := convex_stdSimplex ℝ (Fin n)
  have howner :
      IsMinOn f Δ xStar ↔
        ∃ g' : Module.Dual ℝ (Fin n → ℝ),
          g' ∈ subdifferential f xStar ∧ -g' ∈ normal_cone Δ xStar :=
    isMinOn_iff_exists_subgradient_neg_mem_normal_cone (f := f) hf.ne_bot hconv hΔ
      (by simpa [Set.inter_comm] using hri) hxStar
  constructor
  · intro hxmin
    rcases howner.mp hxmin with ⟨g', hg', hg'normal⟩
    let g : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm g'
    refine ⟨g, ?_, ?_⟩
    · simpa [g] using hg'
    · have hg'normal' :
          -dotProductEquiv ℝ (Fin n) g ∈ normal_cone Δ xStar := by
        simpa [g] using hg'normal
      have hmult :
          -dotProductEquiv ℝ (Fin n) g ∈ normal_cone Δ xStar ↔
            ∃ μ : ℝ, IsStdSimplexMultiplier xStar g μ :=
        neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_exists_multiplier hxStar
      exact hmult.mp hg'normal'
  · rintro ⟨g, hg, μ, hμ⟩
    have hmult :
        -dotProductEquiv ℝ (Fin n) g ∈ normal_cone Δ xStar ↔
          ∃ μ : ℝ, IsStdSimplexMultiplier xStar g μ :=
      neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_exists_multiplier hxStar
    exact howner.mpr ⟨dotProductEquiv ℝ (Fin n) g, hg, by
      exact hmult.mpr ⟨μ, hμ⟩⟩

end

/-! ### Proposition_3_33 (from Chap03) -/
open scoped BigOperators

section

variable {m d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/- Proposition 3.33 is a `source-facing` optimality criterion for the owner objective
`fermatWeberObjective`. The relevant owner/bridge API already lives upstream in
`isMinOn_univ_iff_zero_mem_subdifferentialAt`, `euclideanSubdifferentialAt`,
`mem_euclideanSubdifferentialAt_iff`, and
`euclidean_subdifferentialAt_fermatWeberObjective_eq_finset_sum_piecewise`, so this file keeps
only the textbook minimizer criterion instead of introducing extra public wrapper predicates for
its two cases. -/
recall isMinOn_univ_iff_zero_mem_subdifferentialAt
recall euclideanSubdifferentialAt
recall mem_euclideanSubdifferentialAt_iff
recall fermatWeberObjective
recall euclidean_subdifferentialAt_fermatWeberObjective_eq_finset_sum_piecewise

-- Proof sketch: apply the real-valued Fermat criterion
-- `isMinOn_univ_iff_zero_mem_subdifferentialAt`, then rewrite zero subgradient membership through
-- the Euclidean bridge `euclideanSubdifferentialAt`. Away from the sites `Set.range a`, each
-- summand is differentiable, so the zero-subgradient condition becomes the vanishing of the
-- weighted sum of normalized displacement vectors. At a site `a j`, split off the nonsmooth term
-- indexed by `j`, use the Euclidean-norm subdifferential at the origin for that term, and rewrite
-- membership of the zero vector in the resulting translated closed ball as the residual norm bound.
/-- Proposition 3.33: for pairwise distinct sites and nonnegative weights, a point globally
minimizes the Fermat--Weber objective if and only if either it is not one of the sites and the
weighted normalized displacement vectors sum to zero, or it equals a site `a_j` and the norm of
the corresponding residual sum over the remaining sites is at most `ω_j`. -/
theorem isMinOn_fermatWeberObjective_iff_balance_or_site_bound
    (ω : Fin m → ℝ) (a : Fin m → E) (ha : Function.Injective a) (hω : ∀ i, 0 ≤ ω i) (x : E) :
    IsMinOn (fermatWeberObjective ω a) Set.univ x ↔
      let balance : Fin m → E := fun i ↦ ω i • ((‖x - a i‖)⁻¹ • (x - a i))
      (x ∉ Set.range a ∧ ∑ i, balance i = 0) ∨
        ∃ j : Fin m, x = a j ∧ ‖(Finset.univ.erase j).sum balance‖ ≤ ω j := sorry

end
