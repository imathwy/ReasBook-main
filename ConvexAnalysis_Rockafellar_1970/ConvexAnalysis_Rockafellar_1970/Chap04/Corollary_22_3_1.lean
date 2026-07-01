import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_22_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators RealInnerProductSpace Rockafellar

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {I : Type*} [Fintype I]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 22.3.1 is the homogeneous zero-right-hand-side form of Farkas' lemma
  for a finite family of weak linear inequalities in a real inner-product space.
- `core/canonical`: the chapter owner theorem
  `linear_inequality_consequence_iff_exists_nonnegative_multiplier`, stated on the intrinsic
  pairing owner layer and whose left-hand side is owner inclusion of the weak feasible set into
  the target half-space.
- `bridge/view`: this item applies that owner theorem to the canonical functional pairing obtained
  from `InnerProductSpace.toDualMap`, then uses injectivity of `toDualMap` to rewrite the
  pointwise weighted-pairing identity certificate as the textbook vector conic-combination
  identity. Consistency is automatic because `x = 0` satisfies every homogeneous weak inequality,
  and the scalar inequality in the multiplier certificate becomes vacuous.

Domain-style sampling used here:
- the project theorem `linear_inequality_consequence_iff_exists_nonnegative_multiplier`;
- `InnerProductSpace.toDualMap` from the chapter inner-product bridge material;
- finite sums over an arbitrary finite index type `[Fintype I]`.

Primitive data vs derived API:
- primitive inputs: the target vector `a0` and the finite family `a`;
- owner abstraction: `linear_inequality_consequence_iff_exists_nonnegative_multiplier` applied to
  the homogeneous scalar family `fun _ ↦ 0` after converting vectors to functionals with
  `InnerProductSpace.toDualMap`;
- derived API: the nonnegative conic-combination characterization, after discarding the vacuous
  scalar inequality.

Layer target: `source-facing`. The corollary remains in the textbook homogeneous form, but its
implementation and supporting API now come directly from the chapter owner theorem.
-/

-- Proof sketch: apply
-- `is_linear_inequality_consequence_iff_exists_nonnegative_multiplier` to the functional family
-- `fun i ↦ ((InnerProductSpace.toDualMap ℝ E) (a i)).toLinearMap` with all right-hand sides equal
-- to `0`. The consistency hypothesis is witnessed by `x = 0`,
-- `InnerProductSpace.toDualMap_apply_apply` rewrites the resulting pointwise inequalities back
-- to the textbook inner-product form, and the scalar inequality `∑ i, λ i * 0 ≤ 0` is automatic.
/-- Corollary 22.3.1: (Farkas' Lemma). The homogeneous inequality `⟪a₀, x⟫ ≤ 0` is a consequence
of the system `⟪aᵢ, x⟫ ≤ 0` for `i ∈ I` if and only if there are nonnegative real numbers `λᵢ`
such that `∑ i, λᵢ • aᵢ = a₀`. -/
theorem homogeneous_farkas_lemma
    (a0 : E) (a : I → E) :
    (∀ x : E, (∀ i : I, ⟪a i, x⟫ ≤ 0) → ⟪a0, x⟫ ≤ 0) ↔
      ∃ weights : I → ℝ,
        (∀ i : I, 0 ≤ weights i) ∧
          (∑ i, weights i • a i) = a0 := by
  let toDualMap := InnerProductSpace.toDualMap ℝ E
  let a0' : E →ₗ[ℝ] ℝ := (toDualMap a0).toLinearMap
  let a' : I → E →ₗ[ℝ] ℝ := fun i ↦ (toDualMap (a i)).toLinearMap
  have hcertificate :
      (∃ weights : I → ℝ,
        (∀ i : I, 0 ≤ weights i) ∧
          (∀ x : E, ∑ i, weights i * (⟪x, a' i⟫ₚ : ℝ) = (⟪x, a0'⟫ₚ : ℝ))) ↔
        ∃ weights : I → ℝ,
          (∀ i : I, 0 ≤ weights i) ∧
            (∑ i, weights i • a i) = a0 := by
    constructor
    · rintro ⟨weights, hnonneg, hsum⟩
      refine ⟨weights, hnonneg, ?_⟩
      have hsum_cont : ∑ i, weights i • toDualMap (a i) = toDualMap a0 := by
        ext x
        simpa [a0', a', smul_eq_mul] using hsum x
      apply toDualMap.injective
      simpa using hsum_cont
    · rintro ⟨weights, hnonneg, hsum⟩
      refine ⟨weights, hnonneg, ?_⟩
      have hsum_cont : ∑ i, weights i • toDualMap (a i) = toDualMap a0 := by
        simpa using congrArg toDualMap hsum
      intro x
      have hsum_cont_x :
          (∑ i, weights i • toDualMap (a i)) x = toDualMap a0 x := by
        simpa using congrArg (fun b : E →L[ℝ] ℝ => b x) hsum_cont
      simpa [a0', a', smul_eq_mul] using hsum_cont_x
  have hmain :
      (∀ x : E, (∀ i : I, ⟪a i, x⟫ ≤ 0) → ⟪a0, x⟫ ≤ 0) ↔
        (∃ weights : I → ℝ,
          (∀ i : I, 0 ≤ weights i) ∧
            (∀ x : E, ∑ i, weights i * (⟪x, a' i⟫ₚ : ℝ) = (⟪x, a0'⟫ₚ : ℝ))) := by
    simpa [a0', a', InnerProductSpace.toDualMap_apply_apply] using
      (is_linear_inequality_consequence_iff_exists_nonnegative_multiplier
        a0' 0 a' (fun _ ↦ (0 : ℝ))
        (by
          refine ⟨(0 : E), ?_⟩
          intro i
          simp [a']))
  exact hmain.trans hcertificate

end
