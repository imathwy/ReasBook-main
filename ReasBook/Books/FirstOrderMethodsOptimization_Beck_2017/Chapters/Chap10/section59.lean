import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_59 (from Chap10) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 10.59 is `source-facing`: it fixes the standing assumptions for the constrained
problem `min {h(x) | x ∈ C}` used in the S-FISTA subsection. The relevant mathlib owners are the
standard predicates `C.Nonempty`, `IsClosed C`, `Convex ℝ C`, `ConvexOn ℝ Set.univ h`, and
`LipschitzWith ℓh h`. Following the project pattern for problem data in Chapter 10, the clean
public interface is therefore a small `Prop`-valued class on the objective, the feasible set, and
the given Lipschitz constant, rather than a new packaged optimization object. -/

/-- Definition 10.59: the constrained problem `min {h(x) | x ∈ C}` has a nonempty closed convex
feasible set `C`, and its objective `h : E → ℝ` is globally convex and `ℓ_h`-Lipschitz. -/
class IsConvexLipschitzConstrainedMinimizationProblem
    (h : E → ℝ) (C : Set E) (ℓh : NNReal) : Prop where
  constraint_nonempty : C.Nonempty
  constraint_closed : IsClosed C
  constraint_convex : Convex ℝ C
  objective_convex : ConvexOn ℝ Set.univ h
  objective_lipschitz : LipschitzWith ℓh h

/-- A constrained convex Lipschitz minimization problem exposes nonemptiness of the feasible set
to typeclass search. -/
instance instFactConstraintNonemptyOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    Fact C.Nonempty :=
  ⟨hproblem.constraint_nonempty⟩

/-- A constrained convex Lipschitz minimization problem exposes closedness of the feasible set to
typeclass search. -/
instance instFactIsClosedOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    Fact (IsClosed C) :=
  ⟨hproblem.constraint_closed⟩

/-- A constrained convex Lipschitz minimization problem exposes convexity of the feasible set to
typeclass search. -/
instance instFactConvexOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    Fact (Convex ℝ C) :=
  ⟨hproblem.constraint_convex⟩

/-- A constrained convex Lipschitz minimization problem exposes convexity of the objective to
typeclass search. -/
instance instFactConvexOnOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    Fact (ConvexOn ℝ Set.univ h) :=
  ⟨hproblem.objective_convex⟩

/-- A constrained convex Lipschitz minimization problem exposes the global Lipschitz bound of the
objective to typeclass search. -/
instance instFactLipschitzWithOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    Fact (LipschitzWith ℓh h) :=
  ⟨hproblem.objective_lipschitz⟩

/-- A constrained convex Lipschitz minimization problem canonically makes the real-valued
objective proper after coercion to `EReal`. -/
theorem IsConvexLipschitzConstrainedMinimizationProblem.objective_toEReal_proper
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    IsProperExtendedRealFunction h.toEReal := by
  rcases hproblem.constraint_nonempty with ⟨x, hx⟩
  let _ : Nonempty E := ⟨x⟩
  simpa using Function.toEReal_isProper h

/-- A constrained convex Lipschitz minimization problem makes the real-valued objective
lower semicontinuous after coercion to `EReal`. -/
theorem IsConvexLipschitzConstrainedMinimizationProblem.objective_toEReal_lowerSemicontinuous
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    LowerSemicontinuous h.toEReal :=
  Function.toEReal_lowerSemicontinuous_of_lipschitz hproblem.objective_lipschitz

/-- A constrained convex Lipschitz minimization problem makes the real-valued objective convex
after coercion to `EReal`. -/
theorem IsConvexLipschitzConstrainedMinimizationProblem.objective_toEReal_convex
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    is_convex_function h.toEReal :=
  Function.toEReal_isConvexFunction hproblem.objective_convex

/-- The real-valued objective of a constrained convex Lipschitz minimization problem is proper
after coercion to `EReal`. -/
instance instIsProperExtendedRealFunctionToERealOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    IsProperExtendedRealFunction h.toEReal :=
  hproblem.objective_toEReal_proper

/-- The real-valued objective of a constrained convex Lipschitz minimization problem is lower
semicontinuous after coercion to `EReal`. -/
instance instLowerSemicontinuousToERealOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    LowerSemicontinuous h.toEReal :=
  hproblem.objective_toEReal_lowerSemicontinuous

/-- A constrained convex Lipschitz minimization problem exposes lower semicontinuity of the
real-valued objective after coercion to `EReal` through `Fact`. -/
instance instFactLowerSemicontinuousToERealOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    Fact (LowerSemicontinuous h.toEReal) :=
  ⟨hproblem.objective_toEReal_lowerSemicontinuous⟩

/-- The real-valued objective of a constrained convex Lipschitz minimization problem is convex
after coercion to `EReal`. -/
instance instIsConvexFunctionToERealOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    is_convex_function h.toEReal :=
  hproblem.objective_toEReal_convex

/-- A constrained convex Lipschitz minimization problem exposes convexity of the real-valued
objective after coercion to `EReal` through `Fact`. -/
instance instFactIsConvexFunctionToERealOfIsConvexLipschitzConstrainedMinimizationProblem
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    Fact (is_convex_function h.toEReal) :=
  ⟨hproblem.objective_toEReal_convex⟩

end

/-! ### Proposition_10_59 (from Chap10) -/
universe u

open InnerProductSpace (toDualMap)

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 10.59 is `source-facing` in the Chapter 10 dual-norm-attainment API.

Domain sampling:
- source-facing owner: `Λ[·] = primalCounterparts` from Lemma 10.61;
- source-facing characterization: `mem_primalCounterparts_iff` from Definition 10.63;
- derived owner API: `norm_eq_one_of_mem_primalCounterparts` and
  `apply_eq_norm_of_mem_primalCounterparts` from Lemma 10.61;
- ambient canonical map: `toDualMap` from the Riesz representation API.

The primitive data are only the vector `a : E`. The source proposition is therefore best stated
directly on the existing Chapter 10 owner `Λ[toDualMap ℝ E a]`, with the normalized vector formula
proved from the owner lemmas and the equality case in Cauchy-Schwarz, rather than by introducing a
separate Euclidean-subdifferential bridge theorem as a second public layer. -/

-- Proof sketch: membership of `x` in `Λ[toDualMap ℝ E a]` gives `‖x‖ = 1` and
-- `⟪a, x⟫ = ‖a‖` via the owner lemmas `norm_eq_one_of_mem_primalCounterparts` and
-- `apply_eq_norm_of_mem_primalCounterparts`. This is the equality case of Cauchy-Schwarz, so
-- `x` must be the positive normalized multiple `‖a‖⁻¹ • a`. The converse is immediate from
-- `‖toDualMap ℝ E a‖ = ‖a‖` and the defining inequalities of `Λ[·]`.
/-- Helper for Proposition 10.59: the normalized nonzero vector has Euclidean norm `1`. -/
lemma normalized_norm_eq_one
    {a : E} (ha : a ≠ 0) :
    ‖‖a‖⁻¹ • a‖ = 1 := by
  have hnorma : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  -- Compute the norm of the normalized vector directly from `norm_smul`.
  calc
    ‖‖a‖⁻¹ • a‖ = ‖‖a‖⁻¹‖ * ‖a‖ := norm_smul _ _
    _ = ‖a‖⁻¹ * ‖a‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      positivity
    _ = 1 := by rw [inv_mul_cancel₀ hnorma]

/-- Helper for Proposition 10.59: the normalized vector belongs to the primal-counterpart set of
`toDualMap ℝ E a`. -/
lemma normalized_toDualMap_mem_primalCounterparts
    {a : E} (ha : a ≠ 0) :
    (‖a‖⁻¹ • a) ∈ Λ[toDualMap ℝ E a] := by
  have hnorma : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hnorm_normalized : ‖‖a‖⁻¹ • a‖ = 1 := normalized_norm_eq_one ha
  have htoDual_norm : ‖toDualMap ℝ E a‖ = ‖a‖ := (toDualMap ℝ E).norm_map a
  -- Unfold the owner and verify the unit-ball and norm-attainment clauses separately.
  unfold primalCounterparts
  constructor
  · exact hnorm_normalized.le
  · calc
      (toDualMap ℝ E a) (‖a‖⁻¹ • a) = inner ℝ a (‖a‖⁻¹ • a) := by
        rw [InnerProductSpace.toDualMap_apply_apply]
      _ = ‖a‖⁻¹ * inner ℝ a a := by
        rw [real_inner_smul_right]
      _ = ‖a‖⁻¹ * ‖a‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]
      _ = ‖a‖ := by
        rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hnorma, one_mul]
      _ = ‖toDualMap ℝ E a‖ := by
        rw [htoDual_norm]

/-- Helper for Proposition 10.59: every primal counterpart of `toDualMap ℝ E a` has inner product
`1` with the normalized vector. -/
lemma normalized_inner_eq_one_of_mem_primalCounterparts
    {a x : E} (ha : a ≠ 0) (hx : x ∈ Λ[toDualMap ℝ E a]) :
    inner ℝ (‖a‖⁻¹ • a) x = 1 := by
  have hnorma : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have happly : (toDualMap ℝ E a) x = ‖toDualMap ℝ E a‖ :=
    apply_eq_norm_of_mem_primalCounterparts hx
  have htoDual_norm : ‖toDualMap ℝ E a‖ = ‖a‖ := (toDualMap ℝ E).norm_map a
  have hinner_ax : inner ℝ a x = ‖a‖ := by
    -- Rewrite the owner equality into the ambient inner-product form.
    calc
      inner ℝ a x = (toDualMap ℝ E a) x := by
        rw [InnerProductSpace.toDualMap_apply_apply]
      _ = ‖toDualMap ℝ E a‖ := happly
      _ = ‖a‖ := htoDual_norm
  -- Normalize the attained pairing by scaling the first inner-product argument.
  calc
    inner ℝ (‖a‖⁻¹ • a) x = ‖a‖⁻¹ * inner ℝ a x := by
      rw [real_inner_smul_left]
    _ = ‖a‖⁻¹ * ‖a‖ := by
      rw [hinner_ax]
    _ = 1 := by
      rw [inv_mul_cancel₀ hnorma]

/-- Helper for Proposition 10.59: every primal counterpart of `toDualMap ℝ E a` equals the
normalized vector `‖a‖⁻¹ • a`. -/
lemma eq_normalized_of_mem_primalCounterparts_toDualMap
    {a x : E} (ha : a ≠ 0) (hx : x ∈ Λ[toDualMap ℝ E a]) :
    x = ‖a‖⁻¹ • a := by
  have hnorm_normalized : ‖‖a‖⁻¹ • a‖ = 1 := normalized_norm_eq_one ha
  have hnorm_x : ‖x‖ = 1 := by
    have htoDual_ne : toDualMap ℝ E a ≠ 0 := by
      intro hzero
      apply ha
      exact (toDualMap ℝ E).injective (by simpa using hzero)
    exact norm_eq_one_of_mem_primalCounterparts htoDual_ne hx
  have hinner : inner ℝ (‖a‖⁻¹ • a) x = 1 :=
    normalized_inner_eq_one_of_mem_primalCounterparts ha hx
  -- Apply the equality case of Cauchy-Schwarz to the two unit vectors.
  have h_eq : ‖a‖⁻¹ • a = x :=
    (inner_eq_one_iff_of_norm_eq_one hnorm_normalized hnorm_x).mp hinner
  exact h_eq.symm

/-- Proposition 10.59: for every nonzero vector `a` in a real inner-product space, the Chapter 10
norming-vector set `Λ[toDualMap ℝ E a]` is the singleton containing the normalized vector
`‖a‖⁻¹ • a`. -/
theorem primalCounterparts_toDualMap_eq_singleton_normalized
    {a : E} (ha : a ≠ 0) :
    Λ[toDualMap ℝ E a] = ({‖a‖⁻¹ • a} : Set E) := by
  ext x
  constructor
  · intro hx
    -- The source owner lemmas reduce any member to the normalized vector.
    have hx_eq : x = ‖a‖⁻¹ • a :=
      eq_normalized_of_mem_primalCounterparts_toDualMap ha hx
    simpa [Set.mem_singleton_iff] using hx_eq
  · intro hx
    -- The normalized vector satisfies the defining primal-counterpart equalities.
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact normalized_toDualMap_mem_primalCounterparts ha

end
