import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_5 (from Chap02) -/
universe u

noncomputable section

open scoped BigOperators

/-
Definition 2.5 lies in the duality domain for dual norms of separated seminorms on real
inner-product spaces, with the source-facing specialization to Euclidean spaces `ℝⁿ`.

Sampled owner-style declarations:
* mathlib `Seminorm.closedBall_zero_eq`
* mathlib `normSeminorm`
* mathlib `closedBall_normSeminorm`
* project `unit_closed_ball_support_function_eq_norm` in `Lemma_2_3`
* project `Seminorm.inner_le_dualNorm_mul` in `Definition_2_5`
* project `supportFunction` in `Chap03/Definition_3_9`

Source/core/bridge triage:
* source-facing: the textbook dual norm of a norm on `ℝⁿ`
* core/canonical: the same owner `p.dualNorm` on a finite-dimensional real inner-product
  space
* bridge/view: `Seminorm.dualNorm_apply`

Primitive data:
* a seminorm `p : Seminorm ℝ E`
* a finite-dimensional real inner-product-space structure on `E`
* the separation hypothesis `[Seminorm.IsNorm p]`

Derived API:
* the support-function formula `Seminorm.dualNorm_apply`
* duality consequences such as `Seminorm.inner_le_dualNorm_mul`
* the Euclidean specialization `Seminorm.dualNorm_normSeminorm_eq_norm` in `Lemma_2_3`
* the operator-norm owner `Seminorm.primalDualOperatorNorm` in `Definition_2_32`

The later Chapter 3 `EReal`-valued `supportFunction` is the more general support-function owner.
Definition 2.5 keeps the source-facing `ℝ`-valued dual norm, with `ℝⁿ` as the textbook ambient
model and finite-dimensional real inner-product spaces as the canonical owner layer.
-/

namespace Seminorm

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- A real seminorm is a norm when only the zero vector has seminorm zero. -/
class IsNorm (p : Seminorm ℝ E) : Prop where
  /-- The only vector with seminorm zero is the zero vector. -/
  eq_zero_of_map_eq_zero {x : E} : p x = 0 → x = 0

/-- A separated seminorm is strictly positive on every nonzero vector. -/
theorem map_pos_of_ne_zero (p : Seminorm ℝ E) [p.IsNorm] {x : E} (hx : x ≠ 0) :
    0 < p x := by
  have hpx_ne : p x ≠ 0 := fun hpx ↦ hx (IsNorm.eq_zero_of_map_eq_zero hpx)
  exact lt_of_le_of_ne (apply_nonneg p x) (Ne.symm hpx_ne)

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ambient norm on a real normed vector space is a norm in the bundled seminorm sense. -/
instance : IsNorm (normSeminorm ℝ E) where
  eq_zero_of_map_eq_zero {x} hx := by
    exact norm_eq_zero.mp (by simpa using hx : ‖x‖ = 0)

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem le_coordinate_constant_mul_norm (p : Seminorm ℝ E) [FiniteDimensional ℝ E]
    (x : E) :
    p x ≤
      (∑ i, ‖((Module.finBasis ℝ E).coord i).toContinuousLinearMap‖ *
        p ((Module.finBasis ℝ E) i)) * ‖x‖ := by
  let b := Module.finBasis ℝ E
  change p x ≤ (∑ i, ‖(b.coord i).toContinuousLinearMap‖ * p (b i)) * ‖x‖
  have hx : x = ∑ i, (b.repr x i) • b i := by
    exact (b.sum_repr x).symm
  have hsum :
      p (∑ i, (b.repr x i) • b i) ≤
        ∑ i, p ((b.repr x i) • b i) := by
    exact
      Finset.le_sum_of_subadditive p (by simp) (map_add_le_add p) Finset.univ
        (fun i ↦ (b.repr x i) • b i)
  calc
    p x = p (∑ i, (b.repr x i) • b i) := congrArg p hx
    _ ≤ ∑ i, p ((b.repr x i) • b i) := by
      simpa using hsum
    _ = ∑ i, |b.repr x i| * p (b i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      simpa [Real.norm_eq_abs] using
        (map_smul_eq_mul p (b.repr x i) (b i))
    _ ≤ ∑ i, (‖(b.coord i).toContinuousLinearMap‖ * p (b i)) * ‖x‖ := by
      exact Finset.sum_le_sum fun i _ ↦ by
        have hcoeff :
            |b.repr x i| ≤
              ‖(b.coord i).toContinuousLinearMap‖ * ‖x‖ := by
          simpa [Real.norm_eq_abs] using
            (b.coord i).toContinuousLinearMap.le_opNorm x
        have hpi_nonneg : 0 ≤ p (b i) := apply_nonneg p (b i)
        calc
          |b.repr x i| * p (b i) ≤
              (‖(b.coord i).toContinuousLinearMap‖ * ‖x‖) * p (b i) := by
            exact mul_le_mul_of_nonneg_right hcoeff hpi_nonneg
          _ = (‖(b.coord i).toContinuousLinearMap‖ * p (b i)) * ‖x‖ := by
            ring
    _ = (∑ i, ‖(b.coord i).toContinuousLinearMap‖ * p (b i)) * ‖x‖ := by
      rw [← Finset.sum_mul]

/-- On a finite-dimensional real normed space, a separated seminorm controls the ambient
norm up to a positive constant. -/
theorem exists_norm_le_mul (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm] :
    ∃ C > 0, ∀ x : E, ‖x‖ ≤ C * p x := by
  by_cases h0 : Module.finrank ℝ E = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x
    letI : Subsingleton E := (Module.finrank_zero_iff (R := ℝ) (M := E)).mp h0
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  · let b := Module.finBasis ℝ E
    let C : ℝ := (∑ i, ‖(b.coord i).toContinuousLinearMap‖ * p (b i)) + 1
    have hC_pos : 0 < C := by
      dsimp [C]
      positivity
    have hp_ball : p.ball 0 1 ∈ nhds (0 : E) := by
      refine Filter.mem_of_superset
        (Metric.ball_mem_nhds (0 : E) (by positivity : 0 < C⁻¹)) ?_
      intro y hy
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
      rw [Seminorm.mem_ball_zero]
      calc
        p y ≤ (∑ i, ‖(b.coord i).toContinuousLinearMap‖ * p (b i)) * ‖y‖ := by
          simpa [b] using le_coordinate_constant_mul_norm p y
        _ ≤ C * ‖y‖ := by
          dsimp [C]
          have hsum_le :
              ∑ i, ‖(b.coord i).toContinuousLinearMap‖ * p (b i) ≤ C := by
            linarith
          exact mul_le_mul_of_nonneg_right hsum_le (norm_nonneg _)
        _ < C * C⁻¹ := mul_lt_mul_of_pos_left hy hC_pos
        _ = 1 := by
          rw [mul_inv_cancel₀ hC_pos.ne']
    have hp_cont : Continuous p := Seminorm.continuous hp_ball
    let i0 : Fin (Module.finrank ℝ E) := ⟨0, Nat.pos_of_ne_zero h0⟩
    let u0 : E := ‖b i0‖⁻¹ • b i0
    have hu0 : u0 ∈ Metric.sphere (0 : E) 1 := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      have hbi0_ne : b i0 ≠ 0 := b.ne_zero i0
      have hbi0_norm_pos : 0 < ‖b i0‖ := norm_pos_iff.mpr hbi0_ne
      dsimp [u0]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hbi0_norm_pos.le),
        inv_mul_cancel₀ hbi0_norm_pos.ne']
    have hsphere : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere (0 : E) 1
    obtain ⟨u, hu, hu_min⟩ :=
      hsphere.exists_isMinOn ⟨u0, hu0⟩ hp_cont.continuousOn
    have hu_norm : ‖u‖ = 1 := by
      rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hu
    have hu_ne : u ≠ 0 := by
      exact norm_ne_zero_iff.mp (by simp [hu_norm])
    have hpu_pos : 0 < p u := map_pos_of_ne_zero p hu_ne
    refine ⟨(p u)⁻¹, inv_pos.mpr hpu_pos, ?_⟩
    intro y
    by_cases hy0 : y = 0
    · simp [hy0]
    · have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      let y' : E := ‖y‖⁻¹ • y
      have hy'_sphere : y' ∈ Metric.sphere (0 : E) 1 := by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
        dsimp [y']
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hy_norm_pos.le),
          inv_mul_cancel₀ hy_norm_pos.ne']
      have hu_le : p u ≤ p y' := (isMinOn_iff.mp hu_min) y' hy'_sphere
      have hy'_eq : p y' = ‖y‖⁻¹ * p y := by
        dsimp [y']
        rw [map_smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.mpr hy_norm_pos.le)]
      have htmp : p u ≤ ‖y‖⁻¹ * p y := by
        simpa [hy'_eq] using hu_le
      have hmul : p u * ‖y‖ ≤ p y := by
        simpa [mul_comm] using (le_inv_mul_iff₀ hy_norm_pos).mp htmp
      exact (le_inv_mul_iff₀ hpu_pos).2 hmul

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The pairing image of the closed `p`-unit ball is bounded above, so `p.dualNorm g` is a
genuine real supremum. -/
private theorem bddAbove_innerImage_closedBall
    (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm] (g : E) :
    BddAbove ((fun x : E ↦ inner ℝ g x) '' p.closedBall 0 1) := by
  obtain ⟨C, hC_pos, hnorm_le⟩ := p.exists_norm_le_mul
  refine ⟨‖g‖ * C, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  have hy_norm : ‖y‖ ≤ C := by
    have hpy : p y ≤ 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hy
    calc
      ‖y‖ ≤ C * p y := hnorm_le y
      _ ≤ C * 1 := by
        gcongr
      _ = C := by
        ring
  calc
    inner ℝ g y ≤ ‖g‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ ‖g‖ * C := by
      gcongr


/-- Definition 2.5 in owner form: on a real inner-product space, `p.dualNorm` is the support
function of the closed `p`-unit ball for a separated seminorm `p`, i.e. the textbook dual norm.
The finite-dimensional hypothesis is the canonical owner layer guaranteeing this support value is
an honest real supremum. -/
def dualNorm (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm] (g : E) : ℝ :=
  sSup ((fun x : E ↦ inner ℝ g x) '' p.closedBall 0 1)

end

end Seminorm

namespace SeminormDualNorm

/- Source-facing Lean notation for the dual norm induced by a separated seminorm `p`. -/
scoped notation:max "‖" g "‖[" p ",*]" => Seminorm.dualNorm p g

end SeminormDualNorm

open scoped SeminormDualNorm

namespace Seminorm

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Expanding the source-facing owner `‖g‖[p,*]` gives the support-function formula over the
closed `p`-unit ball. -/
theorem dualNorm_apply (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm] (g : E) :
    ‖g‖[p,*] = sSup ((fun x : E ↦ inner ℝ g x) '' {x | p x ≤ 1}) := by
  rw [dualNorm, p.closedBall_zero_eq]

/-- On a finite-dimensional real inner-product space, the dual norm of a separated seminorm is
bounded by a positive constant multiple of the ambient norm. -/
theorem exists_dualNorm_le_mul_norm (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm] :
    ∃ C > 0, ∀ g : E, ‖g‖[p,*] ≤ C * ‖g‖ := by
  obtain ⟨C, hC_pos, hnorm_le⟩ := p.exists_norm_le_mul
  refine ⟨C, hC_pos, ?_⟩
  intro g
  rw [dualNorm_apply]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⟨0, by simp, by simp⟩⟩
  · rintro y ⟨u, hu, rfl⟩
    have hpu : p u ≤ 1 := hu
    have hu_norm : ‖u‖ ≤ C := by
      calc
        ‖u‖ ≤ C * p u := hnorm_le u
        _ ≤ C * 1 := by
          gcongr
        _ = C := by
          ring
    calc
      inner ℝ g u ≤ ‖g‖ * ‖u‖ := real_inner_le_norm _ _
      _ ≤ ‖g‖ * C := by
        gcongr
      _ = C * ‖g‖ := by
        ring

/-- The dual pairing is bounded by the product of a separated seminorm and its dual norm. -/
theorem inner_le_dualNorm_mul (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm]
    (x g : E) :
    inner ℝ g x ≤ ‖g‖[p,*] * p x := by
  by_cases hx : x = 0
  · simp [hx, map_zero p]
  · have hpx_pos : 0 < p x := map_pos_of_ne_zero p hx
    let y : E := (p x)⁻¹ • x
    have hy_norm : p y = 1 := by
      simpa [y, Real.norm_of_nonneg (inv_nonneg.mpr hpx_pos.le),
        inv_mul_cancel₀ hpx_pos.ne'] using
        (map_smul_eq_mul p (p x)⁻¹ x)
    have hy_ball : y ∈ p.closedBall 0 1 := by
      rw [Seminorm.mem_closedBall_zero]
      exact hy_norm.le
    have hy_le : inner ℝ g y ≤ ‖g‖[p,*] := by
      rw [dualNorm]
      exact le_csSup (p.bddAbove_innerImage_closedBall g) ⟨y, hy_ball, rfl⟩
    have hx_eq : p x • y = x := by
      simp [y, smul_smul, hpx_pos.ne']
    calc
      inner ℝ g x = inner ℝ g (p x • y) := by rw [hx_eq]
      _ = p x * inner ℝ g y := by rw [real_inner_smul_right]
      _ ≤ p x * ‖g‖[p,*] := mul_le_mul_of_nonneg_left hy_le hpx_pos.le
      _ = ‖g‖[p,*] * p x := by ring

end

end Seminorm

end

/-! ### Lemma_2_5 (from Chap02) -/
open scoped CoordinateSubspace

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Primary domain: linear-algebraic coordinate subspaces in `ℝⁿ`.

Sampled owner-style declarations in this domain:
- `coordinateSubspace k n`, the chapter’s canonical `Submodule` owner for `ℝ^{k,n}`;
- `mem_coordinateSubspace_iff`, the canonical coordinatewise membership criterion;
- `Submodule.span`, the owner construction for the linear span of the first `k` vectors in a
  sequence;
- `Submodule.span_le`, the canonical way to prove a span lies in a target submodule.

Best owner abstraction:
- source-facing/core: a sequence `g : ℕ → E` together with the coordinate-subspace hypothesis
  `g j ∈ ℝ^{j.1 + 1,n}` on the relevant prefix `j : Fin k`;
- bridge/view: any later specialization `g j = ∇ f (x j)`.

Primitive data:
- the ambient Euclidean space `E`,
- the sequence `g`,
- the hypothesis that each prefix term `g j` for `j : Fin k` already belongs to the appropriate
  owner `coordinateSubspace (j.1 + 1) n`.

Derived API:
- `mem_coordinateSubspace_iff`, which upgrades membership from `ℝ^{j.1 + 1,n}` to `ℝ^{k,n}` by
  comparing the coordinate-vanishing ranges when `j.1 + 1 ≤ k`;
- the resulting prefix span lies in the owner coordinate subspace
  `coordinateSubspace k n`.

Source/core/bridge triage:
- source-facing: the textbook fact that the first `k` search directions lie in `ℝ^{k,n}`;
- core/canonical: the sequence-level span theorem below;
- bridge/view: applying it to a gradient sequence when a later argument truly needs gradient
  notation.
-/

/-- Lemma 2.5: if each of the first `k` terms of a sequence `g` lies in its natural owner
coordinate subspace `ℝ^{j.1+1,n}`, then the span of that prefix lies in `ℝ^{k,n}`. Applying this
with `g j = ∇ f (x j)` recovers the gradient-prefix span statement used later in the chapter. -/
-- Proof sketch: use `Submodule.span_le`. For a generator `g j` with `j : Fin k`, the hypothesis
-- gives membership in `ℝ^{j.1 + 1,n}`. Rewriting by `mem_coordinateSubspace_iff`, every
-- coordinate with index at least `k` also lies in the vanishing range for `ℝ^{j.1 + 1,n}`, since
-- `j.1 + 1 ≤ k`.
theorem prefix_span_le_coordinateSubspace {k : ℕ}
    (g : ℕ → E)
    (hg : ∀ j : Fin k, g j ∈ ℝ^{j.1 + 1,n}) :
    Submodule.span ℝ (Set.range fun j : Fin k ↦ g j) ≤ ℝ^{k,n} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  have hj : g j ∈ ℝ^{j.1 + 1,n} := hg j
  change g j ∈ ℝ^{k,n}
  rw [mem_coordinateSubspace_iff] at hj ⊢
  intro i hik
  exact hj i (le_trans (Nat.succ_le_of_lt j.is_lt) hik)

end

/-! ### Proposition_2_5 (from Chap02) -/
noncomputable section

open scoped BigOperators

variable (n : ℕ)

local notation "F" => Fin n → ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 2.5 lies in the finite-dimensional strong-convexity domain for entropy on the
standard simplex.

Sampled owner-style declarations before refining this file:
* project `StrongConvexOnWith` in `Definition_2_14`
* mathlib `stdSimplex`
* mathlib `convex_stdSimplex`
* mathlib `WithLp.linearEquiv`
* mathlib `PiLp.norm_eq_sum`

Best owner abstraction for the main theorem:
* `StrongConvexOnWith p μ Q f` on the canonical function-space simplex owner
  `Q = stdSimplex ℝ (Fin n)`

Primitive data:
* the canonical simplex owner `stdSimplex ℝ (Fin n)`
* the source-facing entropy function `entropyFunction n : (Fin n → ℝ) → ℝ`

Derived API:
* the owner `ℓ₁` seminorm `simplexL1Seminorm n` on `Fin n → ℝ`, obtained by pulling back the
  owner `L¹` norm on `WithLp 1 (Fin n → ℝ)`
* its coordinate formula `simplexL1Seminorm_apply`
* the Euclidean bridge `EuclideanSpace.l1Seminorm n`, obtained by pulling back
  `simplexL1Seminorm n` along `EuclideanSpace.equiv`
* the coordinate-pullback bridge theorem obtained from Proposition 2.5 via `EuclideanSpace.equiv`

Source/core/bridge triage:
* source-facing: `entropyFunction n` and its strong-convexity statement on `stdSimplex ℝ (Fin n)`
* core/canonical: the owner predicate `StrongConvexOnWith`
* bridge/view: the Euclidean coordinate pullback
  `(EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' stdSimplex ℝ (Fin n)` and `EuclideanSpace.l1Seminorm n`
  as the coordinate pullback of the owner `simplexL1Seminorm n`
-/

/-- The canonical `ℓ₁` seminorm on `Fin n → ℝ`, obtained by pulling back the owner `L¹` norm on
`WithLp 1 (Fin n → ℝ)` along `WithLp.toLp`. -/
private abbrev functionL1Equiv : F ≃ₗ[ℝ] WithLp 1 F :=
  (WithLp.linearEquiv 1 ℝ F).symm

/-- The canonical `ℓ₁` seminorm on `Fin n → ℝ`. -/
abbrev simplexL1Seminorm : Seminorm ℝ F :=
  Seminorm.comp (normSeminorm ℝ (WithLp 1 F)) (functionL1Equiv n).toLinearMap

private theorem simplexL1Seminorm_toLp (x : F) :
    simplexL1Seminorm n x = ‖WithLp.toLp (1 : ENNReal) x‖ := by
  change ‖functionL1Equiv n x‖ = ‖WithLp.toLp (1 : ENNReal) x‖
  rfl

/-- Applying the canonical `ℓ₁` seminorm to a function sums the absolute values of its
coordinates. -/
theorem simplexL1Seminorm_apply (x : F) :
    simplexL1Seminorm n x = ∑ i, ‖x i‖ := by
  rw [simplexL1Seminorm_toLp]
  simpa [Real.norm_eq_abs] using
    PiLp.norm_eq_sum (by simp : 0 < (1 : ENNReal).toReal) (WithLp.toLp (1 : ENNReal) x)

/-- The canonical `ℓ₁` seminorm on `Fin n → ℝ` is a norm. -/
instance simplexL1Seminorm_isNorm : Seminorm.IsNorm (simplexL1Seminorm n : Seminorm ℝ F) where
  eq_zero_of_map_eq_zero := by
    intro x hx
    exact (functionL1Equiv n).map_eq_zero_iff.mp <|
      norm_eq_zero.mp <| by
        simpa [simplexL1Seminorm, functionL1Equiv] using hx

/-- The entropy function `x ↦ ∑ᵢ xᵢ log xᵢ` on the canonical simplex ambient space
`Fin n → ℝ`. -/
def entropyFunction : F → ℝ :=
  fun x ↦ ∑ i, x i * Real.log (x i)

/-- Evaluating `entropyFunction` expands to the coordinatewise entropy sum. -/
theorem entropyFunction_apply (x : F) :
    entropyFunction n x = ∑ i, x i * Real.log (x i) :=
  rfl

/-- Helper for Proposition 2.5: the Euclidean-coordinate realization of the entropy function. -/
private def entropyCoordinateFunction : E → ℝ :=
  fun x ↦ entropyFunction n ((EuclideanSpace.equiv (Fin n) ℝ) x)

/-- Helper for Proposition 2.5: the coordinate `ℓ₁` seminorm used for the Hessian argument on
`ℝⁿ`. -/
private abbrev coordinateL1Seminorm : Seminorm ℝ E :=
  Seminorm.comp (simplexL1Seminorm n) (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap

/-- Helper for Proposition 2.5: the derivative of the explicit Euclidean entropy gradient at a
strictly positive point. -/
private abbrev entropyCoordinateGradientFDeriv (x : E) : E →L[ℝ] E :=
  (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin n ↦
      (x i)⁻¹ • (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ))

/-- Helper for Proposition 2.5: the strict subprobability simplex
`{x : ℝⁿ | x_i > 0, ∑ i, x_i < 1}` is the open owner domain used for the Hessian argument. -/
private def openSubprobabilitySimplex : Set E :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}

/-- Helper for Proposition 2.5: the fixed interior anchor used to approach boundary simplex
points from the strict subprobability simplex. -/
private def subprobabilityInteriorAnchor : E :=
  WithLp.toLp 2 fun _ ↦ ((2 : ℝ) * (n + 1))⁻¹

/-- Helper for Proposition 2.5: the Euclidean coordinate `ℓ₁` seminorm sums the absolute values
of the coordinates. -/
private theorem coordinateL1Seminorm_apply (x : E) :
    coordinateL1Seminorm n x = ∑ i, ‖x i‖ := by
  simpa [coordinateL1Seminorm] using
    simplexL1Seminorm_apply n ((EuclideanSpace.equiv (Fin n) ℝ) x)

/-- Helper for Proposition 2.5: membership in the Euclidean preimage of the standard simplex is
the coordinatewise nonnegativity-plus-sum-one condition. -/
private theorem mem_preimage_stdSimplex_iff {x : E} :
    x ∈ ((EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' stdSimplex ℝ (Fin n)) ↔
      (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 := by
  simp [stdSimplex]

/-- Helper for Proposition 2.5: the strict subprobability simplex is open. -/
private theorem isOpen_openSubprobabilitySimplex :
    IsOpen (openSubprobabilitySimplex n) := by
  -- Each coordinate positivity constraint is open, and the strict sum bound is open as well.
  have hpos : IsOpen {x : E | ∀ i, 0 < x i} := by
    simpa [Set.setOf_forall] using
      isOpen_iInter_of_finite fun i : Fin n ↦
        isOpen_lt continuous_const
          (PiLp.continuous_apply (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i)
  have hsum : IsOpen {x : E | ∑ i, x i < 1} := by
    have hcont : Continuous fun x : E ↦ ∑ i, x i := by
      exact continuous_finset_sum _ fun i _ ↦
        PiLp.continuous_apply (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i
    exact isOpen_lt hcont continuous_const
  simpa [openSubprobabilitySimplex, Set.setOf_and] using hpos.inter hsum

/-- Helper for Proposition 2.5: the strict subprobability simplex is convex. -/
private theorem convex_openSubprobabilitySimplex :
    Convex ℝ (openSubprobabilitySimplex n) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro i
    -- Positivity is preserved because at least one endpoint weight is positive.
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      subst ha0
      subst hb1
      simpa [openSubprobabilitySimplex] using hy.1 i
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hax_pos : 0 < a * x i := mul_pos ha_pos (hx.1 i)
      have hyb_nonneg : 0 ≤ b * y i := mul_nonneg hb (hy.1 i).le
      calc
        0 < a * x i + 0 := by linarith
        _ ≤ a * x i + b * y i := by linarith
        _ = (a • x + b • y) i := by simp [smul_eq_mul]
  · -- The sum constraint is affine, so the strict upper bound is preserved by convexity.
    have hxsum : ∑ i, x i < 1 := hx.2
    have hysum : ∑ i, y i < 1 := hy.2
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      subst ha0
      subst hb1
      simpa [smul_eq_mul] using hy.2
    · by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        subst hb0
        subst ha1
        simpa [smul_eq_mul] using hx.2
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        calc
          ∑ i, (a • x + b • y) i = a * ∑ i, x i + b * ∑ i, y i := by
            simp [smul_eq_mul, Finset.mul_sum, Finset.sum_add_distrib]
          _ < a * 1 + b * 1 := by
                have hax : a * ∑ i, x i < a := by nlinarith
                have hby : b * ∑ i, y i < b := by nlinarith
                linarith
          _ = 1 := by linarith

/-- Helper for Proposition 2.5: the anchor point has strictly positive coordinates. -/
private theorem subprobabilityInteriorAnchor_pos (i : Fin n) :
    0 < subprobabilityInteriorAnchor n i := by
  -- The anchor is the constant vector with value `1 / (2 (n + 1))`.
  simp [subprobabilityInteriorAnchor]
  positivity

/-- Helper for Proposition 2.5: the anchor point lies strictly below the simplex hyperplane. -/
private theorem subprobabilityInteriorAnchor_sum_lt_one :
    ∑ i, subprobabilityInteriorAnchor n i < 1 := by
  -- The anchor sum is `n / (2 (n + 1))`, hence strictly smaller than `1`.
  have hsum :
      ∑ i, subprobabilityInteriorAnchor n i = (n : ℝ) / ((2 : ℝ) * (n + 1)) := by
    simp [subprobabilityInteriorAnchor, div_eq_mul_inv]
  rw [hsum]
  have hden : ((2 : ℝ) * (n + 1)) ≠ 0 := by positivity
  field_simp [hden]
  nlinarith

/-- Helper for Proposition 2.5: the Euclidean Riesz functional is the sum of the coordinate
projections weighted by the coordinates of the representing vector. -/
private theorem toDual_eq_sum_pi_proj (v : E) :
    (InnerProductSpace.toDual ℝ E) v =
      ∑ i : Fin n,
        v i • (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ) := by
  ext h
  -- Identify both linear forms by evaluating them on an arbitrary vector.
  change inner ℝ v h = _
  rw [PiLp.inner_apply]
  -- On Euclidean coordinates, both sides are the same finite sum `∑ i, hᵢ vᵢ`.
  change (∑ i : Fin n, h i * v i) = _
  simp [mul_comm]

/-- Helper for Proposition 2.5: the Euclidean-coordinate entropy function is continuous. -/
private theorem entropyCoordinateFunction_continuous :
    Continuous (entropyCoordinateFunction n) := by
  -- Continuity follows termwise from the continuous extension of `x ↦ x log x`.
  -- Each coordinate term is continuous after composing with the corresponding projection.
  have hterms :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Continuous fun x : E ↦ x i * Real.log (x i) := by
    intro i hi
    exact Real.continuous_mul_log.comp
      (PiLp.continuous_apply (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i)
  -- Summing the coordinate terms recovers the entropy function.
  simpa [entropyCoordinateFunction, entropyFunction] using continuous_finset_sum _ hterms

/-- Helper for Proposition 2.5: on the strict subprobability simplex, each boundary simplex point
can be joined to the fixed anchor while staying inside the open owner domain. -/
private theorem preimage_stdSimplex_segment_anchor_mem_openSubprobabilitySimplex
    {x : E} (hx : x ∈ ((EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' stdSimplex ℝ (Fin n)))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    (1 - t) • x + t • subprobabilityInteriorAnchor n ∈ openSubprobabilitySimplex n := by
  have hx' : (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 := by
    simpa using (mem_preimage_stdSimplex_iff (n := n) (x := x)).mp hx
  refine ⟨?_, ?_⟩
  · intro i
    -- The positive anchor makes every positive-time perturbation land in the strict interior.
    have hanchor : 0 < subprobabilityInteriorAnchor n i :=
      subprobabilityInteriorAnchor_pos (n := n) i
    have hright : 0 < t * subprobabilityInteriorAnchor n i := mul_pos ht.1 hanchor
    have hleft : 0 ≤ (1 - t) * x i := mul_nonneg (sub_nonneg.mpr ht.2) (hx'.1 i)
    calc
      0 < 0 + t * subprobabilityInteriorAnchor n i := by simpa using hright
      _ ≤ (1 - t) * x i + t * subprobabilityInteriorAnchor n i := by linarith
      _ = ((1 - t) • x + t • subprobabilityInteriorAnchor n) i := by
            simp [smul_eq_mul]
  · -- The sum interpolates between `1` and the anchor sum, so it becomes strict for `t > 0`.
    have hanchor : ∑ i, subprobabilityInteriorAnchor n i < 1 :=
      subprobabilityInteriorAnchor_sum_lt_one (n := n)
    calc
      ∑ i, ((1 - t) • x + t • subprobabilityInteriorAnchor n) i
          = (1 - t) * ∑ i, x i + t * ∑ i, subprobabilityInteriorAnchor n i := by
              simp [smul_eq_mul, Finset.mul_sum, Finset.sum_add_distrib]
      _ < 1 := by
            nlinarith [hx'.2, hanchor, ht.1, ht.2]

/-- Helper for Proposition 2.5: on the positive orthant, the Euclidean-coordinate entropy
gradient is the coordinate vector `log x + 1`. -/
private theorem entropyCoordinateFunction_hasGradientAt_of_pos
    {x : E} (hx : ∀ i, 0 < x i) :
    HasGradientAt
      (entropyCoordinateFunction n)
      (WithLp.toLp 2 fun i ↦ Real.log (x i) + 1)
      x := by
  -- Route correction: work with the Fréchet derivative first, then identify it with the Riesz
  -- representative of the Euclidean gradient via `toDual_eq_sum_pi_proj`.
  have hsum :
      HasFDerivAt
        (entropyCoordinateFunction n)
        (∑ i : Fin n,
          (Real.log (x i) + 1) •
            (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ))
        x := by
    have hterms :
        ∀ i ∈ (Finset.univ : Finset (Fin n)),
          HasFDerivAt
            (fun y : E ↦ y i * Real.log (y i))
            (((Real.log (x i) + 1) : ℝ) •
              (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ))
            x := by
      intro i hi
      -- Differentiate the one-variable entropy term after the coordinate projection.
      have happly :
          HasFDerivAt
            (fun y : E ↦ y i)
            (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ)
            x := by
        simpa using PiLp.hasFDerivAt_apply (2 : ENNReal) x i
      have hscalar :
          HasDerivAt
            (fun t : ℝ ↦ t * Real.log t)
            (Real.log (x i) + 1)
            (x i) := by
        exact Real.hasDerivAt_mul_log (hx i).ne'
      simpa [Function.comp] using hscalar.comp_hasFDerivAt x happly
    -- Summing the coordinate derivatives gives the Fréchet derivative of the whole entropy sum.
    convert HasFDerivAt.sum hterms using 1
    funext y
    simp [entropyCoordinateFunction, entropyFunction]
  have hfrechet :
      HasFDerivAt
        (entropyCoordinateFunction n)
        ((InnerProductSpace.toDual ℝ E) (WithLp.toLp 2 fun i ↦ Real.log (x i) + 1))
        x := by
    -- The summed coordinate functional is exactly the Riesz functional of `log x + 1`.
    simpa [toDual_eq_sum_pi_proj (n := n) (WithLp.toLp 2 fun i ↦ Real.log (x i) + 1)] using hsum
  -- Convert the Fréchet derivative into the Euclidean gradient witness.
  simpa using hfrechet.hasGradientAt

/-- Helper for Proposition 2.5: the Euclidean-coordinate entropy function is `C²` on the strict
subprobability simplex. -/
private theorem entropy_contDiffOn_open_subprobability_simplex :
    ContDiffOn ℝ 2 (entropyCoordinateFunction n) (openSubprobabilitySimplex n) := by
  intro x hx
  have hterms :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        ContDiffWithinAt
          ℝ 2
          (fun y : E ↦ y i * Real.log (y i))
          (openSubprobabilitySimplex n)
          x := by
    intro i hi
    -- Each coordinate projection is smooth, and positivity on the open simplex allows `log`.
    have happly :
        ContDiffWithinAt
          ℝ 2
          (fun y : E ↦ y i)
          (openSubprobabilitySimplex n)
          x := by
      have hcont : ContDiffAt ℝ 2 (fun y : E ↦ y i) x := by
        simpa [Function.comp] using
          (contDiff_apply ℝ ℝ (n := (2 : WithTop ℕ∞)) i).contDiffAt.comp x
            (((EuclideanSpace.equiv (Fin n) ℝ).contDiff (n := (2 : WithTop ℕ∞))).contDiffAt)
      exact hcont.contDiffWithinAt
    have hlog :
        ContDiffWithinAt
          ℝ 2
          (fun y : E ↦ Real.log (y i))
          (openSubprobabilitySimplex n)
          x := by
      exact happly.log (hx.1 i).ne'
    exact happly.mul hlog
  -- Summing the coordinate `C²` terms gives `C²` regularity of the entropy sum.
  simpa [entropyCoordinateFunction, entropyFunction] using ContDiffWithinAt.sum hterms

/-- Helper for Proposition 2.5: near a strict subprobability point, the Euclidean entropy
gradient has the coordinate formula `x ↦ log x + 1`. -/
private theorem entropyCoordinateFunction_hasFDerivAt_gradient_of_mem_openSubprobabilitySimplex
    {x : E} (hx : x ∈ openSubprobabilitySimplex n) :
    HasFDerivAt
      (gradient (entropyCoordinateFunction n))
      (entropyCoordinateGradientFDeriv (n := n) x)
      x := by
  -- Route correction: differentiate the explicit positive-orthant gradient field, then replace
  -- the totalized gradient by this field on a neighborhood of the positive point.
  let G : E → E := fun y ↦ WithLp.toLp 2 fun i ↦ Real.log (y i) + 1
  let H : E → Fin n → ℝ := fun y i ↦ Real.log (y i) + 1
  let H' : E →L[ℝ] Fin n → ℝ :=
    ContinuousLinearMap.pi fun i : Fin n ↦
      ((x i)⁻¹ : ℝ) •
        (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ)
  have hEq : gradient (entropyCoordinateFunction n) =ᶠ[nhds x] G := by
    have hpos : {y : E | ∀ i : Fin n, 0 < y i} ∈ nhds x := by
      have hopen : IsOpen {y : E | ∀ i : Fin n, 0 < y i} := by
        simpa [Set.setOf_forall] using
          isOpen_iInter_of_finite fun i : Fin n ↦
            isOpen_lt continuous_const
              (PiLp.continuous_apply (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i)
      exact hopen.mem_nhds hx.1
    filter_upwards [hpos] with y hy
    exact (entropyCoordinateFunction_hasGradientAt_of_pos (n := n) hy).gradient
  have hH : HasFDerivAt H H' x := by
    rw [hasFDerivAt_pi]
    intro i
    have happly :
        HasFDerivAt
          (fun y : E ↦ y i)
          (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ)
          x := by
      simpa using PiLp.hasFDerivAt_apply (2 : ENNReal) x i
    have hlog :
        HasFDerivAt
          (fun y : E ↦ Real.log (y i))
          (((x i)⁻¹ : ℝ) •
            (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ))
          x := by
      simpa [Function.comp] using (Real.hasDerivAt_log (hx.1 i).ne').comp_hasFDerivAt x happly
    -- The added constant `1` does not change the derivative.
    simpa [H, H'] using hlog.add_const (1 : ℝ)
  have hToLp :
      HasFDerivAt
        (WithLp.toLp 2 : (Fin n → ℝ) → E)
        (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap
        (H x) := by
    simpa using PiLp.hasFDerivAt_toLp (2 : ENNReal) (H x)
  let T : (Fin n → ℝ) →L[ℝ] E :=
    (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap
  have hG :
      HasFDerivAt
        G
        (T.comp H')
        x := by
    -- First differentiate the coordinate function `H`, then package the coordinates with `toLp`.
    simpa [G, H, T] using hToLp.comp x hH
  -- Replace the abstract gradient by its explicit coordinate formula near the positive point.
  simpa [entropyCoordinateGradientFDeriv, H'] using hG.congr_of_eventuallyEq hEq

/-- Helper for Proposition 2.5: on the strict subprobability simplex, the Euclidean entropy
Hessian acts diagonally with entries `x_i⁻¹`. -/
private theorem entropy_hessian_apply_on_open_subprobability_simplex
    {x : E} (hx : x ∈ openSubprobabilitySimplex n) (h : E) :
    hessian (entropyCoordinateFunction n) x h = WithLp.toLp 2 fun i ↦ h i / x i := by
  have hderiv :=
    entropyCoordinateFunction_hasFDerivAt_gradient_of_mem_openSubprobabilitySimplex (n := n) hx
  -- The Hessian is the derivative of the gradient, now identified with the explicit diagonal map.
  change fderiv ℝ (gradient (entropyCoordinateFunction n)) x h = _
  rw [hderiv.fderiv]
  ext i
  simp [entropyCoordinateGradientFDeriv, div_eq_mul_inv, mul_comm]

/-- Helper for Proposition 2.5: the Euclidean entropy Hessian quadratic form is
`∑ i, h_i^2 / x_i` on the strict subprobability simplex. -/
private theorem entropy_hessian_quadratic_form_on_open_subprobability_simplex
    {x : E} (hx : x ∈ openSubprobabilitySimplex n) (h : E) :
    inner ℝ (hessian (entropyCoordinateFunction n) x h) h =
      ∑ i, (h i) ^ (2 : ℕ) / x i := by
  -- Rewrite the Hessian by the explicit diagonal formula, then expand the Euclidean inner product.
  rw [entropy_hessian_apply_on_open_subprobability_simplex (n := n) hx h]
  simpa [pow_two, dotProduct, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (EuclideanSpace.inner_eq_star_dotProduct (WithLp.toLp 2 fun i ↦ h i / x i) h)

/-- Helper for Proposition 2.5: the Euclidean entropy Hessian dominates the square of the
coordinate `ℓ₁` seminorm on the strict subprobability simplex. -/
private theorem entropy_hessian_lower_bound_l1_on_open_subprobability_simplex
    {x : E} (hx : x ∈ openSubprobabilitySimplex n) (h : E) :
    (coordinateL1Seminorm n h) ^ (2 : ℕ) ≤
      inner ℝ (hessian (entropyCoordinateFunction n) x h) h := by
  rw [entropy_hessian_quadratic_form_on_open_subprobability_simplex (n := n) hx h]
  rw [coordinateL1Seminorm_apply]
  by_cases hn : n = 0
  · subst hn
    simp
  · let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    let s : ℝ := ∑ i : Fin n, x i
    let A : ℝ := ∑ i : Fin n, ‖h i‖
    let B : ℝ := ∑ i : Fin n, ‖h i‖ ^ (2 : ℕ) / x i
    have hs_pos : 0 < s := by
      dsimp [s]
      have hi0 : 0 < x i0 := hx.1 i0
      exact lt_of_lt_of_le hi0 <|
        Finset.single_le_sum (fun i hi => (hx.1 i).le) (Finset.mem_univ i0)
    have hs_le_one : s ≤ 1 := le_of_lt hx.2
    have hB_nonneg : 0 ≤ B := by
      refine Finset.sum_nonneg fun i hi ↦ ?_
      have hxi : 0 ≤ x i := (hx.1 i).le
      positivity
    have hTitu :
        A ^ (2 : ℕ) / s ≤ B := by
      dsimp [A, B, s]
      simpa [Real.norm_eq_abs, sq_abs] using
        (Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin n)) (fun i ↦ ‖h i‖)
          (fun i hi ↦ hx.1 i))
    have hmain : A ^ (2 : ℕ) ≤ s * B := by
      have hdiv := (div_le_iff₀ hs_pos).mp hTitu
      simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv
    have hsB : s * B ≤ B := by
      nlinarith
    simpa [A, B, Real.norm_eq_abs, sq_abs] using hmain.trans hsB

/-- Helper for Proposition 2.5: the Euclidean-coordinate entropy function is `1`-strongly convex
on the coordinate realization of the simplex. -/
private theorem entropyCoordinateFunction_strongConvexOnWith_l1_preimage_stdSimplex :
    StrongConvexOnWith
      (coordinateL1Seminorm n) 1
      ((EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' stdSimplex ℝ (Fin n))
      (entropyCoordinateFunction n) := by
  let S : Set E := ((EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' stdSimplex ℝ (Fin n))
  have hS_conv : Convex ℝ S := by
    simpa [S] using
      (convex_stdSimplex ℝ (Fin n)).linear_preimage
        (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap
  have hopenStrong :
      StrongConvexOnWith
        (coordinateL1Seminorm n) 1
        (openSubprobabilitySimplex n)
        (entropyCoordinateFunction n) := by
    rw [StrongConvexOnWith.iff_hessian_quadratic_form_lower_bound
      (p := coordinateL1Seminorm n) (μ := (1 : ℝ))
      (U := openSubprobabilitySimplex n) (f := entropyCoordinateFunction n)]
    · intro x hx h
      simpa using entropy_hessian_lower_bound_l1_on_open_subprobability_simplex (n := n) hx h
    · norm_num
    · exact isOpen_openSubprobabilitySimplex (n := n)
    · exact convex_openSubprobabilitySimplex (n := n)
    · exact entropy_contDiffOn_open_subprobability_simplex (n := n)
  refine ⟨hS_conv, zero_lt_one, ?_⟩
  intro x hx y hy a b ha hb hab
  let z : E := a • x + b • y
  let xt : ℝ → E := fun t ↦ (1 - t) • x + t • subprobabilityInteriorAnchor n
  let yt : ℝ → E := fun t ↦ (1 - t) • y + t • subprobabilityInteriorAnchor n
  let zt : ℝ → E := fun t ↦ (1 - t) • z + t • subprobabilityInteriorAnchor n
  have hz : z ∈ S := hS_conv hx hy ha hb hab
  have hIoc : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioc (0 : ℝ) 1 := by
    have hlt_one : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [self_mem_nhdsWithin, hlt_one] with t ht0 ht1
    exact ⟨ht0, ht1.le⟩
  have hineq :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        entropyCoordinateFunction n (zt t) ≤
          a * entropyCoordinateFunction n (xt t) +
            b * entropyCoordinateFunction n (yt t) -
              a * b * ((1 / 2 : ℝ) * ((1 - t) ^ (2 : ℕ) * (coordinateL1Seminorm n (x - y)) ^ (2 : ℕ))) := by
    filter_upwards [hIoc] with t ht
    have hxt : xt t ∈ openSubprobabilitySimplex n :=
      preimage_stdSimplex_segment_anchor_mem_openSubprobabilitySimplex (n := n) hx ht
    have hyt : yt t ∈ openSubprobabilitySimplex n :=
      preimage_stdSimplex_segment_anchor_mem_openSubprobabilitySimplex (n := n) hy ht
    have hstrong := hopenStrong.2.2 hxt hyt ha hb hab
    have hsegment : a • xt t + b • yt t = zt t := by
      ext i
      dsimp [xt, yt, zt, z]
      calc
        a * ((1 - t) * x i + t * subprobabilityInteriorAnchor n i) +
            b * ((1 - t) * y i + t * subprobabilityInteriorAnchor n i)
            = (1 - t) * (a * x i + b * y i) +
                (a + b) * (t * subprobabilityInteriorAnchor n i) := by ring
        _ = (1 - t) * (a * x i + b * y i) + t * subprobabilityInteriorAnchor n i := by
              rw [hab]
              ring
        _ = (1 - t) * (a * x i + b * y i) + t * subprobabilityInteriorAnchor n i := by rfl
    have hdiff :
        xt t - yt t = (1 - t) • (x - y) := by
      ext i
      dsimp [xt, yt]
      ring
    have hnorm :
        coordinateL1Seminorm n (xt t - yt t) =
          (1 - t) * coordinateL1Seminorm n (x - y) := by
      rw [hdiff, map_smul_eq_mul]
      simp [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    have hnorm_sq :
        (coordinateL1Seminorm n (xt t - yt t)) ^ (2 : ℕ) =
          (1 - t) ^ (2 : ℕ) * (coordinateL1Seminorm n (x - y)) ^ (2 : ℕ) := by
      rw [hnorm]
      ring
    -- Rewrite the open-domain strong-convexity inequality in terms of the boundary-approximation
    -- path and the rescaled `ℓ₁` correction.
    have hstrong' := hstrong
    rw [hsegment, hnorm_sq] at hstrong'
    simpa [xt, yt, zt, z, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hstrong'
  have hxt_tendsto : Filter.Tendsto xt (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds x) := by
    have hcont : Continuous xt := by
      dsimp [xt]
      fun_prop
    convert (hcont.tendsto 0).mono_left nhdsWithin_le_nhds using 1
    simp [xt]
  have hyt_tendsto : Filter.Tendsto yt (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds y) := by
    have hcont : Continuous yt := by
      dsimp [yt]
      fun_prop
    convert (hcont.tendsto 0).mono_left nhdsWithin_le_nhds using 1
    simp [yt]
  have hzt_tendsto : Filter.Tendsto zt (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds z) := by
    have hcont : Continuous zt := by
      dsimp [zt]
      fun_prop
    convert (hcont.tendsto 0).mono_left nhdsWithin_le_nhds using 1
    simp [zt]
  have hlhs :
      Filter.Tendsto
        (fun t : ℝ ↦ entropyCoordinateFunction n (zt t))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (entropyCoordinateFunction n z)) := by
    exact (entropyCoordinateFunction_continuous (n := n)).tendsto z |>.comp hzt_tendsto
  have hrhs :
      Filter.Tendsto
        (fun t : ℝ ↦
          a * entropyCoordinateFunction n (xt t) +
            b * entropyCoordinateFunction n (yt t) -
              a * b * ((1 / 2 : ℝ) * ((1 - t) ^ (2 : ℕ) * (coordinateL1Seminorm n (x - y)) ^ (2 : ℕ))))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          (a * entropyCoordinateFunction n x +
            b * entropyCoordinateFunction n y -
              a * b * ((1 / 2 : ℝ) * (coordinateL1Seminorm n (x - y)) ^ (2 : ℕ)))) := by
    have hxtf :
        Filter.Tendsto
          (fun t : ℝ ↦ entropyCoordinateFunction n (xt t))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (entropyCoordinateFunction n x)) := by
      exact (entropyCoordinateFunction_continuous (n := n)).tendsto x |>.comp hxt_tendsto
    have hytf :
        Filter.Tendsto
          (fun t : ℝ ↦ entropyCoordinateFunction n (yt t))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (entropyCoordinateFunction n y)) := by
      exact (entropyCoordinateFunction_continuous (n := n)).tendsto y |>.comp hyt_tendsto
    have hcorr :
        Filter.Tendsto
          (fun t : ℝ ↦ a * b *
            ((1 / 2 : ℝ) * ((1 - t) ^ (2 : ℕ) * (coordinateL1Seminorm n (x - y)) ^ (2 : ℕ))))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (a * b * ((1 / 2 : ℝ) * (coordinateL1Seminorm n (x - y)) ^ (2 : ℕ)))) := by
      have hcont :
          Continuous fun t : ℝ ↦
            a * b *
              ((1 / 2 : ℝ) * ((1 - t) ^ (2 : ℕ) * (coordinateL1Seminorm n (x - y)) ^ (2 : ℕ))) := by
        fun_prop
      convert (hcont.tendsto 0).mono_left nhdsWithin_le_nhds using 1
      simp
    exact (hxtf.const_mul a).add (hytf.const_mul b) |>.sub hcorr
  letI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hlimit := le_of_tendsto_of_tendsto hlhs hrhs hineq
  simpa [z, S, smul_eq_mul] using hlimit

/-- Helper for Proposition 2.5: strong convexity pulls back along a linear equivalence by
precomposition. -/
private theorem strongConvexOnWith_precompose_linear_equiv
    {G H : Type*} [NormedAddCommGroup G] [NormedAddCommGroup H]
    [NormedSpace ℝ G] [NormedSpace ℝ H]
    (e : G ≃L[ℝ] H) {p : Seminorm ℝ H} {μ : ℝ} {Q : Set H} {f : H → ℝ}
    (hf : StrongConvexOnWith p μ Q f) :
    StrongConvexOnWith (Seminorm.comp p e.toLinearMap) μ (e ⁻¹' Q) (fun x : G ↦ f (e x)) := by
  refine ⟨hf.1.linear_preimage e.toLinearMap, hf.2.1, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Rewrite the pulled-back segment inequality through the linear equivalence.
  simpa [Seminorm.comp_apply, map_add, map_smulₛₗ, smul_eq_mul] using
    hf.2.2 hx hy ha hb hab

/-- Proposition 2.5: the entropy function `x ↦ ∑ᵢ xᵢ log xᵢ` is `1`-strongly convex on the
standard simplex `Δ_n = stdSimplex ℝ (Fin n)` with respect to the canonical `ℓ₁` norm on the
function-space owner `Fin n → ℝ`. -/
-- Proof sketch: prove the source-faithful statement first on the Euclidean realization of the
-- simplex, where the Hessian criterion applies on the strict subprobability simplex, and then
-- transport the result back along `EuclideanSpace.equiv`.
theorem entropyFunction_strongConvexOnWith_l1_stdSimplex :
    StrongConvexOnWith (simplexL1Seminorm n) 1 (stdSimplex ℝ (Fin n)) (entropyFunction n) := by
  -- Transport the Euclidean-coordinate theorem back to the function-space owner.
  simpa [entropyCoordinateFunction, coordinateL1Seminorm, simplexL1Seminorm] using
    (strongConvexOnWith_precompose_linear_equiv (EuclideanSpace.equiv (Fin n) ℝ).symm
      (entropyCoordinateFunction_strongConvexOnWith_l1_preimage_stdSimplex (n := n)))

namespace EuclideanSpace

/-- The canonical coordinate `ℓ₁` seminorm on `ℝⁿ`, obtained by pulling back the owner
`simplexL1Seminorm n` along the coordinate linear equivalence. -/
abbrev l1Seminorm : Seminorm ℝ E :=
  Seminorm.comp (simplexL1Seminorm n) (equiv (Fin n) ℝ).toLinearMap

/-- Applying the canonical coordinate `ℓ₁` seminorm to a vector sums the absolute values of its
coordinates. -/
-- Proof sketch: `l1Seminorm n` is the coordinate pullback of the owner `simplexL1Seminorm n`, so
-- apply `simplexL1Seminorm_apply` to the coordinate function `equiv (Fin n) ℝ x`.
theorem l1Seminorm_apply (x : E) :
    l1Seminorm n x = ∑ i, ‖x i‖ := by
  simpa [l1Seminorm] using simplexL1Seminorm_apply n ((equiv (Fin n) ℝ) x)

/-- The canonical coordinate `ℓ₁` seminorm is a norm on `ℝⁿ`. -/
-- Proof sketch: `l1Seminorm n` is the pullback of the owner norm `simplexL1Seminorm n` along the
-- coordinate linear equivalence `equiv (Fin n) ℝ`, so vanishing reduces to
-- `simplexL1Seminorm_isNorm` on the coordinate function.
instance l1Seminorm_isNorm : Seminorm.IsNorm (l1Seminorm n : Seminorm ℝ E) where
  eq_zero_of_map_eq_zero := by
    intro x hx
    let hSimplex : Seminorm.IsNorm (simplexL1Seminorm n : Seminorm ℝ F) := inferInstance
    exact (equiv (Fin n) ℝ).injective <|
      hSimplex.eq_zero_of_map_eq_zero <| by
        simpa [l1Seminorm] using hx

/-- Proposition 2.5 transported to Euclidean coordinates: precomposing the canonical owner
`entropyFunction n` with `equiv (Fin n) ℝ` yields a `1`-strongly convex function on the
preimage of `stdSimplex ℝ (Fin n)` with respect to the coordinate `ℓ₁` norm. -/
-- Proof sketch: compute the Hessian of the entropy on the relative interior of the coordinate
-- realization of `stdSimplex` as the diagonal form `∑ᵢ hᵢ² / xᵢ`, then use the simplex
-- normalization `∑ᵢ xᵢ = 1` to bound this quadratic form below by `‖h‖₁²`. This yields the
-- second-order criterion for `1`-strong convexity with respect to the canonical coordinate `ℓ₁`
-- seminorm.
theorem entropyFunction_strongConvexOnWith_l1_preimage_stdSimplex :
    StrongConvexOnWith
      (l1Seminorm n) 1
      ((equiv (Fin n) ℝ) ⁻¹' stdSimplex ℝ (Fin n))
      (fun x : E ↦ _root_.entropyFunction n ((equiv (Fin n) ℝ) x)) :=
  by
    -- The public Euclidean statement is definitionally the private coordinate theorem above.
    simpa [l1Seminorm, entropyCoordinateFunction, coordinateL1Seminorm] using
      (entropyCoordinateFunction_strongConvexOnWith_l1_preimage_stdSimplex (n := n))

end EuclideanSpace

end
