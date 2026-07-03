import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_31 (from Chap03) -/
open scoped BigOperators

universe u

section

/- Definition 3.31 is a recall-only item in the chapter's weighted primal-dual certificate
domain.

Primary domain:
- finite weighted inner-product certificates attached to sampled primal points.

Sampled owner-style declarations:
- mathlib `dotProduct`, the canonical finite weighted-sum owner behind the certificate formula
- `gapFunctionCertificate` in `Chap03/Lemma_3_24`, the chapter owner for the sampled certificate
- `gapFunctionCertificate_apply` in `Chap03/Lemma_3_24`, the defining finite-sum expansion

Best owner abstraction:
- source-facing: the certificate `δ_N`
- core/canonical: `gapFunctionCertificate y α g`
- bridge/view: `gapFunctionCertificate_apply`

Primitive data:
- the horizon `N`
- the sample points `y : Fin (N + 1) → E`
- the coefficients `α : Fin (N + 1) → ℝ`
- the field `g : E → E`

Derived API:
- the certificate function `gapFunctionCertificate y α g`
- its pointwise weighted-sum expansion

Source/core/bridge triage:
- source-facing: the textbook gap certificate
- core/canonical: the owner in `Lemma_3_24`
- bridge/view: this recall surface

The owner already lives in `Lemma_3_24`, so this file remains a pure recall layer and introduces
no parallel local wrapper or alias. -/

/- Definition 3.31: the gap function certificate attached to test points `y_k`, scaling
coefficients `α_k`, and a map `g` is the function
`δ_N(x) = ∑_{k=0}^N α_k ⟪g(y_k), y_k - x⟫`. -/
recall gapFunctionCertificate
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ}
    (y : Fin (N + 1) → E) (α : Fin (N + 1) → ℝ) (g : E → E) :
    E → ℝ

/- Evaluating the gap function certificate expands to its defining weighted inner-product sum. -/
recall gapFunctionCertificate_apply
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ}
    (y : Fin (N + 1) → E) (α : Fin (N + 1) → ℝ) (g : E → E) (x : E) :
    gapFunctionCertificate y α g x =
      ∑ k, α k * inner ℝ (g (y k)) (y k - x)

end

/-! ### Lemma_3_31 (from Chap03) -/
noncomputable section

open MeasureTheory

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩

/- Primary domain: measure-theoretic convex geometry of centroid halfspace cuts in a finite-
dimensional real inner-product space.

Sampled owner-style declarations:
- `cuttingHalfspace` in `Definition_3_49`, the chapter owner for affine retained cuts;
- `setAverage` in `Definition_3_54`, the canonical centroid owner recalled there;
- `centerOfGravityCut_volumeRatio_le_one_sub_inv_e` in `Lemma_3_2_6`, the chapter owner theorem
  for the centroid-cut volume estimate under the canonical finite/positive-volume hypotheses;
- `Bornology.IsBounded.measure_lt_top` and `measure_pos_of_nonempty_interior`, the mathlib bridges
  from boundedness and nonempty interior to those owner hypotheses.

Best owner abstraction:
- source-facing: this lemma's textbook hypothesis package of boundedness, convexity, and nonempty
  interior;
- core/canonical: the centroid cut `S ∩ cuttingHalfspace (⨍ x in S, x) g` together with the
  intrinsic owner theorem `centerOfGravityCut_volumeRatio_le_one_sub_inv_e`;
- bridge/view: the derived hypotheses `volume S ≠ ⊤` and `volume S ≠ 0`.

Primitive data:
- the set `S` and the direction `g`;
- boundedness, convexity, nonempty interior, and `g ≠ 0`.

Derived API:
- finite volume from boundedness;
- positive volume from nonempty interior;
- the final ratio estimate by direct reuse of the owner theorem.

This file stays source-facing: the textbook packages the geometric assumptions more concretely than
the owner theorem does, so the refinement is a thin bridge rather than a parallel owner API.
The earlier `EuclideanSpace ℝ (Fin n)` surface was only a display model, so the owner bridge now
lives at the same intrinsic finite-dimensional layer as the chapter's localization-radius API. -/

/-- Lemma 3.31 at the intrinsic owner level: if `S ⊆ E` is bounded and convex with nonempty
interior in a finite-dimensional real inner-product space, then for any nonzero `g : E` the
centroid cut
`S₊ = S ∩ cuttingHalfspace (⨍ x in S, x) g = {x ∈ S | ⟪g, (⨍ x in S, x) - x⟫_ℝ ≥ 0}`
has relative volume at most `1 - 1 / e`. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` statement. -/
-- Proof sketch: this is Grünbaum's centroid halfspace inequality. Use boundedness and nonempty
-- interior to obtain finite positive volume for `S`, then apply the owner centroid halfspace
-- estimate to `S` with those derived measure hypotheses.
theorem centerOfGravityCut_volumeRatio_le_one_sub_inv_e_of_bounded_convex_nonemptyInterior
    (S : Set E) (g : E) (hS_bounded : Bornology.IsBounded S) (hS_convex : Convex ℝ S)
    (hS_int : (interior S).Nonempty) (hg : g ≠ 0) :
    (volume (S ∩ cuttingHalfspace (⨍ x in S, x) g)).toReal / (volume S).toReal ≤
      1 - 1 / Real.exp 1 := by
  have hS_finite : volume S ≠ ⊤ := hS_bounded.measure_lt_top.ne
  have hS_pos : volume S ≠ 0 := (Measure.measure_pos_of_nonempty_interior volume hS_int).ne'
  simpa using centerOfGravityCut_volumeRatio_le_one_sub_inv_e S g hS_convex hS_finite hS_pos hg

end

/-! ### Proposition_3_31 (from Chap03) -/
noncomputable section

open scoped CoordinateSubspace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Primary domain: span-based first-order black-box iterates in `ℝⁿ`, viewed through the chapter's
coordinate-subspace owner `ℝ^{k,n}`.

Sampled owner-style declarations:
* `SatisfiesLinearSpanCondition` from `Chap03/Theorem_3_2_1`, the chapter owner for span-method
  iterate sequences;
* `SatisfiesLinearSpanCondition.zero_eq`, the canonical extraction of the starting-point datum from
  that owner;
* `coordinateSubspace k n` with notation `ℝ^{k,n}` and its view lemma
  `mem_coordinateSubspace_iff`, the chapter owner for prefix-supported vectors;
* `prefix_span_le_coordinateSubspace` from `Chap02/Lemma_2_5`, the exact bridge from span data to
  coordinate-subspace membership.

Best owner abstraction:
* core/canonical: `SatisfiesLinearSpanCondition (0 : E) g xSeq k` for the iterate process and the
  coordinate-submodule owner `ℝ^{k,n}`;
* source-facing: the resisting-oracle support-growth rule
  `xSeq i ∈ ℝ^{i,n} → g (xSeq i) ∈ ℝ^{i + 1,n}`;
* bridge/view: `prefix_span_le_coordinateSubspace`.

Primitive data:
* the iterate sequence `xSeq`,
* the queried-vector map `g`,
* the owner span-condition datum `SatisfiesLinearSpanCondition (0 : E) g xSeq k`,
* the resisting-oracle support-growth rule sending `xSeq i ∈ ℝ^{i,n}` to
  `g (xSeq i) ∈ ℝ^{i + 1,n}`.

Derived API:
* the coordinate-support conclusion for every iterate `xSeq i` with `i ≤ k`.

Source/core/bridge triage:
* source-facing: the resisting-oracle support-growth hypothesis;
* core/canonical: `SatisfiesLinearSpanCondition`;
* bridge/view: the proposition below converting the owner span condition plus support growth into
  coordinate-support control.

This file therefore deletes the parallel local span-method interface and states the proposition
directly on the chapter owner `SatisfiesLinearSpanCondition`, with the coordinate-subspace theorem
used only as the geometric bridge. -/

/-- Proposition 3.31: coordinate-support growth under the resisting oracle. If a deterministic
first-order method on `ℝⁿ` starts at `0` and the resisting oracle returns, at each stage `i < k`,
a vector in `ℝ^{i+1,n}` whenever the current iterate lies in `ℝ^{i,n}`, then every iterate `xᵢ`
with `i ≤ k` lies in `ℝ^{i,n}`. The iterate process itself is expressed through the chapter's
canonical span-condition owner `SatisfiesLinearSpanCondition`. -/
-- Proof sketch: argue inductively on the iterate index. The base case is `x₀ = 0`. For the step,
-- the resisting-oracle hypothesis gives `g j ∈ ℝ^{j.1 + 1,n}` for each earlier index
-- `j : Fin (i + 1)`, so `prefix_span_le_coordinateSubspace` puts the span of the revealed vectors
-- inside `ℝ^{i+1,n}`; the span condition for the deterministic method then yields
-- `x (i + 1) ∈ ℝ^{i+1,n}`.
theorem iterates_mem_coordinateSubspace_under_resistingOracle
    {k : ℕ} {g : E → E} {xSeq : ℕ → E}
    (hxSeq : SatisfiesLinearSpanCondition (0 : E) g xSeq k)
    (hresist : ∀ i < k, xSeq i ∈ ℝ^{i,n} → g (xSeq i) ∈ ℝ^{i + 1,n})
    (i : ℕ) (hi : i ≤ k) :
    xSeq i ∈ ℝ^{i,n} := by
  have hx0 : xSeq 0 = 0 := hxSeq.zero_eq
  refine Nat.strong_induction_on i ?_ hi
  intro i ih hik
  cases i with
  | zero =>
      simp [hx0]
  | succ i =>
      have hstep :
          xSeq (i + 1) ∈ Submodule.span ℝ (Set.range fun t : Fin (i + 1) ↦ g (xSeq t)) := by
        have hxSeq_step :
            xSeq (i + 1) ∈
              AffineSubspace.mk' (0 : E)
                (Submodule.span ℝ (Set.range fun t : Fin (i + 1) ↦ g (xSeq t))) :=
          hxSeq (i + 1) hik
        rw [AffineSubspace.mem_mk'] at hxSeq_step
        simpa using hxSeq_step
      exact
        (prefix_span_le_coordinateSubspace (fun t ↦ g (xSeq t)) fun j ↦
          hresist j (lt_of_lt_of_le j.is_lt hik)
            (ih j j.is_lt (Nat.le_of_lt (lt_of_lt_of_le j.is_lt hik))))
          hstep

end

/-! ### Theorem_3_31 (from Chap03) -/
/- Theorem 3.31 is recall-only in the chapter's partial-infimal-projection /
subdifferential-transfer domain.

Primary domain:
- partial infimal projection and subdifferential transfer for convex extended-real objectives.

Sampled owner-style declarations:
- `partialInfProjection_convexOn_of_convexWithTop` in `Theorem_3_8`, the upstream convexity
  owner for the canonical `partialInfProjection`;
- `partialInfProjection_realPart_convexOn_of_convexWithTop` in `Theorem_3_1_25`, the
  canonical convexity theorem on the owner partial infimal projection;
- `mem_subdifferentialWithin_partialInfProjection_realPart_of_mem_argmin_of_subgradient` in
  `Theorem_3_1_25`, the source-faithful subgradient-transfer theorem.

Best owner abstraction:
- the two chapter owner-level recall targets in `Theorem_3_1_25`.

Primitive data:
- none in this file.

Derived API:
- this numbered recall surface.

Source/core/bridge triage:
- source-facing: Theorem 3.31's convexity and subgradient-transfer statements for partial
  infimal projection;
- core/canonical: the owner declarations in `Theorem_3_1_25`;
- bridge/view: this recall surface.

The previous file kept parallel theorem wrappers around declarations that now already live on the
correct owner abstractions in `Theorem_3_1_25`. The redundant wrappers are deleted here in favor
of direct recall/use. -/

recall partialInfProjection_realPart_convexOn_of_convexWithTop

recall mem_subdifferentialWithin_partialInfProjection_realPart_of_mem_argmin_of_subgradient
