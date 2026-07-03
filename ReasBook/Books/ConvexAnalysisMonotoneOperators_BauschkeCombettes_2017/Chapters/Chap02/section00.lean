import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_2_0_1 (from Chap02) -/
universe u

open scoped InnerProductSpace

/- Text 2.0.1: in a real Hilbert space, the norm induced by the inner product is the canonical
norm satisfying `‖x‖ = Real.sqrt ⟪x, x⟫_ℝ`. -/
recall norm_eq_sqrt_real_inner {F : Type u} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x : F) : ‖x‖ = Real.sqrt ⟪x, x⟫_ℝ

/- In the induced metric on a real inner product space, the distance between `x` and `y` is the
norm of their difference. -/
recall dist_eq_norm_sub {E : Type u} [SeminormedAddCommGroup E] (x y : E) :
    dist x y = ‖x - y‖

/-! ### Text_2_0_2 (from Chap02) -/
universe u

/- Text 2.0.2: for a Hilbert space `𝓗`, the identity operator is the canonical identity map
`id : 𝓗 → 𝓗`. -/
recall id

/-- The identity operator sends every element to itself. -/
theorem identity_operator_apply {𝓗 : Type u} (x : 𝓗) :
    id x = x := rfl

/-! ### Text_2_0_3 (from Chap02) -/
universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Text 2.0.3: a vector is orthogonal to a subset of a real inner product space if and only if it
is orthogonal to the linear span of that subset. -/
theorem mem_orthogonalComplement_iff {C : Set H} {u : H} :
    u ∈ (Submodule.span ℝ C)ᗮ ↔ ∀ x ∈ C, inner ℝ x u = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro hu x hx
    exact hu x (Submodule.subset_span hx)
  · intro hu x hx
    refine Submodule.span_induction
      (fun x hx ↦ hu x hx)
      (by simp)
      (fun x y _ _ hx hy ↦ by simp [inner_add_left, hx, hy])
      (fun a x _ hx ↦ by simp [inner_smul_left, hx])
      hx

/-! ### Text_2_0_4 (from Chap02) -/
open TopologicalSpace

open scoped Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Proof sketch: use `HilbertBasis.mk` for the converse direction and, conversely, identify the
-- range of a `HilbertBasis C ℝ E` with the given set `C`.
/-- Text 2.0.4: for a real Hilbert space, a subset is an orthonormal basis exactly when the
inclusion `C ↪ E` underlies a `HilbertBasis C ℝ E`, equivalently when the subset is orthonormal
and its algebraic span is dense. -/
theorem isOrthonormalBasis_iff [CompleteSpace E] (C : Set E) :
    (∃ b : HilbertBasis C ℝ E, ⇑b = ((↑) : C → E)) ↔
      Orthonormal ℝ ((↑) : C → E) ∧
        (Submodule.span ℝ C).topologicalClosure = ⊤ := sorry

-- Proof sketch: A countable orthonormal basis gives a countable dense subset, and conversely a
-- separable Hilbert space admits a countable orthonormal basis.
/-- `SeparableSpace` is the canonical mathlib formulation of admitting a countable orthonormal
basis, expressed via a countable subtype carrying a `HilbertBasis`. -/
theorem separableSpace_iff_exists_countable_orthonormal_basis [CompleteSpace E] :
    SeparableSpace E ↔
      ∃ C : Set E, C.Countable ∧ ∃ b : HilbertBasis C ℝ E, ⇑b = ((↑) : C → E) := sorry

/-! ### Text_2_0_5 (from Chap02) -/
universe u

/- Text 2.0.5: a family in a real Hilbert space is summable exactly when its finite partial sums
converge to some limit in the canonical mathlib sense; this is the definition of `Summable` via
the existence of a `HasSum` limit along the unconditional summation filter. -/
recall Summable

/- For a family of extended nonnegative reals, the infinite sum is the supremum of the sums over
finite subsets. -/
recall ENNReal.tsum_eq_iSup_sum {α : Type u} {f : α → ENNReal} :
    ∑' (a : α), f a = ⨆ s, ∑ a ∈ s, f a

/-! ### Text_2_0_6 (from Chap02) -/
/- Text 2.0.6: for real normed vector spaces `X` and `Y`, the textbook space
`\mathcal{B}(\mathcal{X},\mathcal{Y})` of bounded linear maps is formalized by the canonical
mathlib type `ContinuousLinearMap`, written `X →L[ℝ] Y`; in particular,
`\mathcal{B}(\mathcal{X})` is `X →L[ℝ] X`, and its operator norm is the ambient norm on this
space. -/
recall ContinuousLinearMap

/- The operator norm is exactly the supremum of `‖T x‖` over the closed unit ball, matching the
textbook definition. -/
recall ContinuousLinearMap.sSup_unitClosedBall_eq_norm

/-! ### Text_2_0_7 (from Chap02) -/
universe u v

open scoped InnerProductSpace

variable {𝓗 : Type u} {𝓚 : Type v}
variable [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable [NormedAddCommGroup 𝓚] [InnerProductSpace ℝ 𝓚] [CompleteSpace 𝓚]

/- Text 2.0.7: for real Hilbert spaces `𝓗` and `𝓚` and a bounded linear operator
`T ∈ 𝓑(𝓗, 𝓚)`, the textbook adjoint operator `T*` is the canonical mathlib operator
`ContinuousLinearMap.adjoint T`, written `T†` in inner-product notation. -/
recall ContinuousLinearMap.adjoint

/- The defining identity of the adjoint is the standard inner-product identity
`⟪T x, y⟫ = ⟪x, T† y⟫`. -/
recall ContinuousLinearMap.adjoint_inner_right

/- The adjoint is uniquely characterized by the defining inner-product identity. -/
recall ContinuousLinearMap.eq_adjoint_iff

/-! ### Text_2_0_8 (from Chap02) -/
universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The level set of a real linear functional at the scalar `η`. -/
def hyperplane (f : H →ₗ[ℝ] ℝ) (η : ℝ) : Set H :=
  {x | f x = η}

/-- Text 2.0.8: a hyperplane in a real Hilbert space is a level set of a nonzero real linear
functional. -/
def is_hyperplane (s : Set H) : Prop :=
  ∃ f : H →ₗ[ℝ] ℝ, f ≠ 0 ∧ ∃ η : ℝ, s = hyperplane f η

-- Proof sketch: unfold `hyperplane`; membership is definitionally the equation `f x = η`.
/-- Membership in `hyperplane f η` is the defining linear-functional equation. -/
theorem mem_hyperplane_iff {f : H →ₗ[ℝ] ℝ} {η : ℝ} {x : H} :
    x ∈ hyperplane f η ↔ f x = η :=
  Iff.rfl

-- Proof sketch: use `f` and `η` as the witnesses in the defining existential statement for
-- `is_hyperplane`.
/-- The level set of a nonzero real linear functional is a hyperplane. -/
theorem hyperplane_is_hyperplane (f : H →ₗ[ℝ] ℝ) (hf : f ≠ 0) (η : ℝ) :
    is_hyperplane (hyperplane f η) :=
  ⟨f, hf, η, rfl⟩

-- Proof sketch: use `f` and `η` as the witnesses in the defining existential statement for
-- `is_hyperplane`.
/-- The level set of a nonzero real linear functional is a hyperplane. -/
theorem is_hyperplane_setOf_eq (f : H →ₗ[ℝ] ℝ) (hf : f ≠ 0) (η : ℝ) :
    is_hyperplane {x | f x = η} := by
  simpa [hyperplane] using hyperplane_is_hyperplane f hf η

/-! ### Text_2_0_9 (from Chap02) -/
universe u

open scoped InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The level set of the real inner-product functional `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
def innerProductLevelSet (u : H) (η : ℝ) : Set H :=
  hyperplane (innerSLFlip ℝ u).toLinearMap η

/-- The closed sublevel set of the real inner-product functional `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
def innerProductClosedSublevelSet (u : H) (η : ℝ) : Set H :=
  (innerSLFlip ℝ u) ⁻¹' Set.Iic η

/-- The open strict sublevel set of the real inner-product functional `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
def innerProductOpenSublevelSet (u : H) (η : ℝ) : Set H :=
  (innerSLFlip ℝ u) ⁻¹' Set.Iio η

/-- The inner-product level set is the hyperplane cut out by the real linear functional
`x ↦ ⟪x, u⟫_ℝ`. -/
theorem innerProductLevelSet_eq_hyperplane (u : H) (η : ℝ) :
    innerProductLevelSet u η = hyperplane (innerSLFlip ℝ u).toLinearMap η :=
  rfl

-- Proof sketch: unfold `innerProductLevelSet`; membership is definitionally the equality
-- `inner ℝ x u = η`.
/-- Membership in the inner-product level set is the defining inner-product equation. -/
theorem mem_innerProductLevelSet_iff {u x : H} {η : ℝ} :
    x ∈ innerProductLevelSet u η ↔ ⟪x, u⟫_ℝ = η := by
  rw [innerProductLevelSet, mem_hyperplane_iff]
  change (innerSLFlip ℝ u) x = η ↔ _
  rw [innerSLFlip_apply_apply]

-- Proof sketch: unfold `innerProductClosedSublevelSet`; membership is definitionally the
-- inequality `inner ℝ x u ≤ η`.
/-- Membership in the closed inner-product sublevel set is the defining inequality. -/
theorem mem_innerProductClosedSublevelSet_iff {u x : H} {η : ℝ} :
    x ∈ innerProductClosedSublevelSet u η ↔ ⟪x, u⟫_ℝ ≤ η := by
  rw [innerProductClosedSublevelSet]
  change (innerSLFlip ℝ u) x ≤ η ↔ _
  rw [innerSLFlip_apply_apply]

-- Proof sketch: unfold `innerProductOpenSublevelSet`; membership is definitionally the strict
-- inequality `inner ℝ x u < η`.
/-- Membership in the open inner-product strict sublevel set is the defining inequality. -/
theorem mem_innerProductOpenSublevelSet_iff {u x : H} {η : ℝ} :
    x ∈ innerProductOpenSublevelSet u η ↔ ⟪x, u⟫_ℝ < η := by
  rw [innerProductOpenSublevelSet]
  change (innerSLFlip ℝ u) x < η ↔ _
  rw [innerSLFlip_apply_apply]

/-- Text 2.0.9: if `u ≠ 0`, the closed hyperplane with normal `u` and offset `η` is the level set
of `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
theorem closedHyperplane_eq_setOf (u : H) (η : ℝ) (_hu : u ≠ 0) :
    innerProductLevelSet u η = {x | ⟪x, u⟫_ℝ = η} := by
  ext x
  simp [mem_innerProductLevelSet_iff]

/-- Text 2.0.9: if `u ≠ 0`, the closed half-space with outer normal `u` and offset `η` is the
sublevel set of `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
theorem closedHalfSpace_eq_setOf (u : H) (η : ℝ) (_hu : u ≠ 0) :
    innerProductClosedSublevelSet u η = {x | ⟪x, u⟫_ℝ ≤ η} := by
  ext x
  simp [mem_innerProductClosedSublevelSet_iff]

/-- Text 2.0.9: if `u ≠ 0`, the open half-space with outer normal `u` and offset `η` is the
strict sublevel set of `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
theorem openHalfSpace_eq_setOf (u : H) (η : ℝ) (_hu : u ≠ 0) :
    innerProductOpenSublevelSet u η = {x | ⟪x, u⟫_ℝ < η} := by
  ext x
  simp [mem_innerProductOpenSublevelSet_iff]

/-! ### Text_2_0_10 (from Chap02) -/
universe u

open scoped InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Text 2.0.10: subtracting the normal correction sends `x` onto the closed
hyperplane with normal `u` and offset `η`. -/
private lemma orthogonal_foot_mem_closedHyperplane (x u : H) (η : ℝ) (hu : u ≠ 0) :
    x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u ∈ innerProductLevelSet u η := by
  have hu_norm : ‖u‖ ≠ 0 := by
    simpa using hu
  have hu_sq : ‖u‖ ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hu_norm hu_norm
  -- Rewrite membership as the defining inner-product equation of the hyperplane.
  rw [mem_innerProductLevelSet_iff]
  -- Compute the inner product of the corrected point with the normal vector.
  calc
    ⟪x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u, u⟫_ℝ
        = ⟪x, u⟫_ℝ - (((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) * ⟪u, u⟫_ℝ) := by
            rw [inner_sub_left, real_inner_smul_left]
    _ = ⟪x, u⟫_ℝ - (((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) * (‖u‖ ^ 2)) := by
            rw [real_inner_self_eq_norm_sq]
    _ = ⟪x, u⟫_ℝ - (⟪x, u⟫_ℝ - η) := by
            field_simp [hu_sq]
    _ = η := by
            ring

/-- Helper for Text 2.0.10: the distance from `x` to its orthogonal foot on
`innerProductLevelSet u η` is the normalized absolute inner-product defect. -/
private lemma dist_to_orthogonal_foot_eq_abs_inner_sub_div_norm (x u : H) (η : ℝ) (hu : u ≠ 0) :
    dist x (x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u) = |⟪x, u⟫_ℝ - η| / ‖u‖ := by
  have hu_norm : ‖u‖ ≠ 0 := by
    simpa using hu
  -- Collapse the distance to the norm of the normal correction vector.
  calc
    dist x (x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u)
        = ‖((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u‖ := by
            rw [dist_eq_norm]
            simp
    _ = |(⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2| * ‖u‖ := by
            rw [norm_smul, Real.norm_eq_abs]
    _ = (|⟪x, u⟫_ℝ - η| / (‖u‖ ^ 2)) * ‖u‖ := by
            rw [abs_div, abs_of_nonneg (sq_nonneg ‖u‖)]
    _ = |⟪x, u⟫_ℝ - η| / ‖u‖ := by
            field_simp [pow_two, hu_norm]

/-- Helper for Text 2.0.10: every point of `innerProductLevelSet u η` is at least the normalized
inner-product defect away from `x`. -/
private lemma abs_inner_sub_div_norm_le_dist_of_mem_closedHyperplane
    (x y u : H) (η : ℝ) (hu : u ≠ 0) (hy : y ∈ innerProductLevelSet u η) :
    |⟪x, u⟫_ℝ - η| / ‖u‖ ≤ dist x y := by
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hy_eq : ⟪y, u⟫_ℝ = η := mem_innerProductLevelSet_iff.mp hy
  have hinner : ⟪x, u⟫_ℝ - η = ⟪x - y, u⟫_ℝ := by
    calc
      ⟪x, u⟫_ℝ - η = ⟪x, u⟫_ℝ - ⟪y, u⟫_ℝ := by
        rw [hy_eq]
      _ = ⟪x - y, u⟫_ℝ := by
        rw [inner_sub_left]
  have hcs : |⟪x - y, u⟫_ℝ| ≤ ‖x - y‖ * ‖u‖ := abs_real_inner_le_norm (x - y) u
  have hdiv : |⟪x - y, u⟫_ℝ| / ‖u‖ ≤ ‖x - y‖ := by
    exact (div_le_iff₀ hu_pos).2 (by simpa [mul_comm] using hcs)
  -- Replace the inner-product defect by the hyperplane equation and identify distance with a norm.
  simpa [hinner, dist_eq_norm] using hdiv

/-- Text 2.0.10: the distance from a point to the closed hyperplane `innerProductLevelSet u η` is
the absolute value of the inner-product defect `⟪x, u⟫_ℝ - η`, normalized by `‖u‖`. -/
-- Proof sketch: project `x` onto the hyperplane along the normal direction `u`, namely at
-- `x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u`, to get the upper bound, and use Cauchy-Schwarz on
-- `⟪x - y, u⟫_ℝ = ⟪x, u⟫_ℝ - η` for arbitrary `y ∈ innerProductLevelSet u η` to get the lower
-- bound.
theorem infDist_hyperplane_eq_abs_inner_sub_div_norm (x u : H) (η : ℝ) (hu : u ≠ 0) :
    Metric.infDist x (innerProductLevelSet u η) = |⟪x, u⟫_ℝ - η| / ‖u‖ := by
  let p := x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u
  have hp : p ∈ innerProductLevelSet u η := by
    -- The textbook witness is exactly the orthogonal foot onto the affine hyperplane.
    simpa [p] using orthogonal_foot_mem_closedHyperplane x u η hu
  have hs : (innerProductLevelSet u η).Nonempty := ⟨p, hp⟩
  have hupper : Metric.infDist x (innerProductLevelSet u η) ≤ |⟪x, u⟫_ℝ - η| / ‖u‖ := by
    -- The explicit projection witness gives the required upper bound.
    calc
      Metric.infDist x (innerProductLevelSet u η) ≤ dist x p := Metric.infDist_le_dist_of_mem hp
      _ = |⟪x, u⟫_ℝ - η| / ‖u‖ := by
        simpa [p] using dist_to_orthogonal_foot_eq_abs_inner_sub_div_norm x u η hu
  have hlower : |⟪x, u⟫_ℝ - η| / ‖u‖ ≤ Metric.infDist x (innerProductLevelSet u η) := by
    -- Every point of the hyperplane satisfies the Cauchy-Schwarz lower bound.
    rw [Metric.le_infDist hs]
    intro y hy
    exact abs_inner_sub_div_norm_le_dist_of_mem_closedHyperplane x y u η hu hy
  exact le_antisymm hupper hlower

/-! ### Text_2_0_11 (from Chap02) -/
universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗]

/- In a normed additive commutative group, the canonical metric is given by the norm of the
difference. -/
recall dist_eq_norm

/-- Text 2.0.11: the strong (norm) topology on a normed space is the topology induced by the
canonical metric `d x y = ‖x - y‖`. -/
theorem strong_topology_eq_metric_topology :
    (inferInstance : TopologicalSpace 𝓗) =
      (inferInstance : MetricSpace 𝓗).toUniformSpace.toTopologicalSpace := rfl

/-! ### Text_2_0_12 (from Chap02) -/
universe u v

open Filter
open scoped Topology

variable {A : Type v} [Preorder A] [IsDirected A fun a b ↦ a ≤ b] [Nonempty A]
variable {𝓗 : Type u} [SeminormedAddCommGroup 𝓗]

/- Text 2.0.12: strong convergence of a net in a normed space is exactly the canonical
metric/net criterion recalled below; mathlib states it in the slightly more general setting of a
seminormed additive commutative group. -/
recall NormedAddCommGroup.tendsto_atTop

/-! ### Text_2_0_13 (from Chap02) -/
universe u v

open Filter
open TopologicalSpace
open scoped InnerProductSpace Topology

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem real_Ioo_isTopologicalBasis :
    IsTopologicalBasis {s : Set ℝ | ∃ a b, s = Set.Ioo a b} := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro s ⟨a, b, rfl⟩
    exact isOpen_Ioo
  · intro x s hx hs
    rcases mem_nhds_iff_exists_Ioo_subset.mp (IsOpen.mem_nhds hs hx) with
      ⟨a, b, hxIoo, hsubset⟩
    exact ⟨Set.Ioo a b, ⟨a, b, rfl⟩, hxIoo, hsubset⟩

/-- The weakly open half-space cut out by the scalar inequality `⟪x, u⟫ < η` in the weak
topology. -/
private def weakOpenHalfSpace [CompleteSpace H] (u : H) (η : ℝ) : Set (WeakSpace ℝ H) :=
  {x | ⟪(toWeakSpace ℝ H).symm x, u⟫_ℝ < η}

private def IsFiniteWeakOpenHalfSpaceIntersection [CompleteSpace H]
    (s : Set (WeakSpace ℝ H)) : Prop :=
  ∃ ι : Type u, ∃ F : Finset ι, ∃ u : ι → H, ∃ η : ι → ℝ,
    s = ⋂ i ∈ F, weakOpenHalfSpace (u i) (η i)

private theorem isOpen_weakOpenHalfSpace [CompleteSpace H] (u : H) (η : ℝ) :
    IsOpen (weakOpenHalfSpace u η) := by
  simpa [weakOpenHalfSpace] using
    IsOpen.preimage (weakSpace_continuous_inner_right u) isOpen_Iio

private theorem basisElem_isFiniteWeakOpenHalfSpaceIntersection [CompleteSpace H]
    {U : StrongDual ℝ H → Set ℝ} {F : Finset (StrongDual ℝ H)}
    (hU : ∀ l, l ∈ F → U l ∈ ({s : Set ℝ | ∃ a b, s = Set.Ioo a b} : Set (Set ℝ))) :
    IsFiniteWeakOpenHalfSpaceIntersection
      (((fun x : WeakSpace ℝ H ↦ fun l ↦ l ((toWeakSpace ℝ H).symm x)) ⁻¹'
        ((F : Set (StrongDual ℝ H)).pi U) : Set (WeakSpace ℝ H))) := by
  classical
  let J := {l // l ∈ F} × Bool
  have hIoo : ∀ l : {l // l ∈ F}, ∃ a b, U l.1 = Set.Ioo a b := by
    intro l
    exact hU l.1 l.2
  choose a b hab using hIoo
  refine ⟨J, Finset.univ, ?_, ?_, ?_⟩
  · intro j
    exact
      if j.2 then
        (InnerProductSpace.toDual ℝ H).symm j.1.1
      else
        -((InnerProductSpace.toDual ℝ H).symm j.1.1)
  · intro j
    exact if j.2 then b j.1 else -(a j.1)
  · ext x
    simp [weakOpenHalfSpace, Set.pi_def]
    constructor
    · intro hx j
      rcases j with ⟨⟨l, hl⟩, jflag⟩
      have hUl : U l = Set.Ioo (a ⟨l, hl⟩) (b ⟨l, hl⟩) := hab ⟨l, hl⟩
      have hxIoo : l ((toWeakSpace ℝ H).symm x) ∈ Set.Ioo (a ⟨l, hl⟩) (b ⟨l, hl⟩) := by
        rw [← hUl]
        exact hx l hl
      have hxl :
          a ⟨l, hl⟩ < ⟪(toWeakSpace ℝ H).symm x, (InnerProductSpace.toDual ℝ H).symm l⟫_ℝ ∧
            ⟪(toWeakSpace ℝ H).symm x, (InnerProductSpace.toDual ℝ H).symm l⟫_ℝ <
              b ⟨l, hl⟩ := by
        simpa [← InnerProductSpace.toDual_symm_apply, real_inner_comm] using hxIoo
      by_cases hflag : jflag = true
      · simp [hflag, hxl.2]
      · have :
            -⟪(toWeakSpace ℝ H).symm x, (InnerProductSpace.toDual ℝ H).symm l⟫_ℝ <
              -a ⟨l, hl⟩ := by
          linarith
        simp [hflag, inner_neg_right, this]
    · intro hx l hl
      have hupper := hx ⟨⟨l, hl⟩, true⟩
      have hlower := hx ⟨⟨l, hl⟩, false⟩
      have hlower' :
          a ⟨l, hl⟩ < ⟪(toWeakSpace ℝ H).symm x, (InnerProductSpace.toDual ℝ H).symm l⟫_ℝ := by
        have :
            -⟪(toWeakSpace ℝ H).symm x, (InnerProductSpace.toDual ℝ H).symm l⟫_ℝ <
              -a ⟨l, hl⟩ := by
          simpa [inner_neg_right] using hlower
        linarith
      have hUl : U l = Set.Ioo (a ⟨l, hl⟩) (b ⟨l, hl⟩) := hab ⟨l, hl⟩
      have hxIoo :
          l ((toWeakSpace ℝ H).symm x) ∈ Set.Ioo (a ⟨l, hl⟩) (b ⟨l, hl⟩) := by
        simpa [← InnerProductSpace.toDual_symm_apply, real_inner_comm] using ⟨hlower', hupper⟩
      rw [hUl]
      exact hxIoo

private theorem isOpen_iff_exists_sUnion_of_finiteWeakOpenHalfSpaceIntersections
    [CompleteSpace H] {s : Set (WeakSpace ℝ H)} :
    IsOpen s ↔
      ∃ T : Set (Set (WeakSpace ℝ H)),
        s = ⋃₀ T ∧ ∀ t ∈ T, IsFiniteWeakOpenHalfSpaceIntersection t := by
  classical
  let e : WeakSpace ℝ H → StrongDual ℝ H → ℝ :=
    fun x l ↦ l ((toWeakSpace ℝ H).symm x)
  let B : Set (Set (StrongDual ℝ H → ℝ)) :=
    {S | ∃ U : StrongDual ℝ H → Set ℝ, ∃ F : Finset (StrongDual ℝ H),
      (∀ l, l ∈ F → U l ∈ ({s : Set ℝ | ∃ a b, s = Set.Ioo a b} : Set (Set ℝ))) ∧
        S = (F : Set (StrongDual ℝ H)).pi U}
  have hB :
      IsTopologicalBasis (t := inferInstance) ((fun a ↦ e ⁻¹' a) '' B) := by
    exact (isTopologicalBasis_pi fun _ : StrongDual ℝ H ↦ real_Ioo_isTopologicalBasis).induced e
  constructor
  · intro hs
    rcases hB.open_eq_sUnion hs with ⟨T, hTB, hTs⟩
    refine ⟨T, hTs, ?_⟩
    intro t ht
    rcases hTB ht with ⟨S, hS, rfl⟩
    rcases hS with ⟨U, F, hU, rfl⟩
    exact basisElem_isFiniteWeakOpenHalfSpaceIntersection hU
  · rintro ⟨T, rfl, hT⟩
    refine isOpen_sUnion fun t ht ↦ ?_
    rcases hT t ht with ⟨ι, F, u, η, rfl⟩
    exact isOpen_biInter_finset fun i hi ↦ isOpen_weakOpenHalfSpace (u i) (η i)

/-- Text 2.0.13 (1): a subset of a real Hilbert space is weakly open iff it is a union of finite
intersections of weakly open half-spaces, and canonically this means that its image in
`WeakSpace ℝ H` is open. -/
theorem isOpen_image_toWeakSpace_iff_exists_sUnion_eq_biInter_inner_halfSpace
    [CompleteSpace H] {C : Set H} :
    IsOpen ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) ↔
      ∃ S : Set (Set H), C = ⋃₀ S ∧
        ∀ s ∈ S, ∃ ι : Type u, ∃ F : Finset ι, ∃ u : ι → H, ∃ η : ι → ℝ,
          s = ⋂ i ∈ F, {x : H | ⟪x, u i⟫_ℝ < η i} := by
  classical
  constructor
  · intro hC
    rcases
      isOpen_iff_exists_sUnion_of_finiteWeakOpenHalfSpaceIntersections.mp hC with
      ⟨T, hTunion, hT⟩
    refine ⟨{s : Set H | ∃ t ∈ T, s = (toWeakSpace ℝ H).symm '' t}, ?_, ?_⟩
    · ext x
      constructor
      · intro hx
        have hxImage : toWeakSpace ℝ H x ∈ ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) :=
          ⟨x, hx, rfl⟩
        rw [hTunion] at hxImage
        rcases Set.mem_sUnion.mp hxImage with ⟨t, htT, hxt⟩
        exact
          Set.mem_sUnion.mpr
            ⟨(toWeakSpace ℝ H).symm '' t, ⟨t, htT, rfl⟩, ⟨toWeakSpace ℝ H x, hxt, by simp⟩⟩
      · rintro ⟨s, ⟨t, htT, rfl⟩, hx⟩
        rcases hx with ⟨y, hy, rfl⟩
        have hyImage : y ∈ ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) := by
          rw [hTunion]
          exact Set.mem_sUnion.mpr ⟨t, htT, hy⟩
        rcases hyImage with ⟨z, hz, rfl⟩
        simpa using hz
    · intro s hs
      rcases hs with ⟨t, htT, rfl⟩
      rcases hT t htT with ⟨ι, F, u, η, rfl⟩
      refine ⟨ι, F, u, η, ?_⟩
      ext x
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = toWeakSpace ℝ H x := by
          simpa using congrArg (toWeakSpace ℝ H) hyx
        simpa [weakOpenHalfSpace, this] using hy
      · intro hx
        refine ⟨toWeakSpace ℝ H x, ?_, by simp⟩
        simpa [weakOpenHalfSpace] using hx
  · rintro ⟨S, hSunion, hS⟩
    let T : Set (Set (WeakSpace ℝ H)) :=
      {t | ∃ s ∈ S, t = (toWeakSpace ℝ H) '' s}
    have hTunion : ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) = ⋃₀ T := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [hSunion] at hx
        rcases Set.mem_sUnion.mp hx with ⟨s, hsS, hxs⟩
        exact Set.mem_sUnion.mpr ⟨(toWeakSpace ℝ H) '' s, ⟨s, hsS, rfl⟩, ⟨x, hxs, rfl⟩⟩
      · rintro ⟨t, ⟨s, hsS, rfl⟩, hy⟩
        rcases hy with ⟨x, hx, rfl⟩
        refine ⟨x, ?_, rfl⟩
        rw [hSunion]
        exact Set.mem_sUnion.mpr ⟨s, hsS, hx⟩
    have hT : ∀ t ∈ T, IsFiniteWeakOpenHalfSpaceIntersection t := by
      intro t ht
      rcases ht with ⟨s, hsS, rfl⟩
      rcases hS s hsS with ⟨ι, F, u, η, rfl⟩
      refine ⟨ι, F, u, η, ?_⟩
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [weakOpenHalfSpace] using hx
      · intro hy
        refine ⟨(toWeakSpace ℝ H).symm y, ?_, by simp⟩
        simpa [weakOpenHalfSpace] using hy
    exact
      isOpen_iff_exists_sUnion_of_finiteWeakOpenHalfSpaceIntersections.mpr ⟨T, hTunion, hT⟩

/- Text 2.0.13: for a real Hilbert space, weak convergence is convergence in `WeakSpace ℝ H`,
equivalently coordinatewise convergence of inner products against fixed vectors. -/
recall weakConvergence_iff_forall_tendsto_inner_right

/-- Text 2.0.13 (3), weak-closedness clause: a subset of a real Hilbert space is weakly closed iff
it contains the weak limit of every directed net in the set. -/
theorem isClosed_image_toWeakSpace_iff_forall_net_tendsto
    {C : Set H} :
    IsClosed ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) ↔
      ∀ ⦃A : Type u⦄ [Nonempty A] [Preorder A] [IsDirectedOrder A] (ξ : A → H) (x : H),
        (∀ a, ξ a ∈ C) →
          Tendsto (fun a ↦ toWeakSpace ℝ H (ξ a)) atTop (𝓝 (toWeakSpace ℝ H x)) →
            x ∈ C := by
  constructor
  · intro hC A _ _ _ ξ x hξ hlim
    have hxImage :
        ∀ a, toWeakSpace ℝ H (ξ a) ∈ ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) := by
      intro a
      exact ⟨ξ a, hξ a, rfl⟩
    have hxClosed :
        toWeakSpace ℝ H x ∈ ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) :=
      hC.mem_of_tendsto hlim (Eventually.of_forall hxImage)
    rcases hxClosed with ⟨y, hy, hyx⟩
    simpa using (toWeakSpace ℝ H).injective hyx ▸ hy
  · intro hC
    rw [← closure_subset_iff_isClosed]
    intro y hy
    rcases (toWeakSpace ℝ H).surjective y with ⟨x, rfl⟩
    rcases (mem_closure_iff_exists_net_tendsto).1 hy with ⟨A, _, _, _, ξ, hξ⟩
    let ζ : A → H := fun a ↦ (toWeakSpace ℝ H).symm (ξ a)
    have hζ : ∀ a, ζ a ∈ C := by
      intro a
      rcases hmem : ξ a with ⟨y, hy⟩
      rcases hy with ⟨z, hz, rfl⟩
      have hEq : ζ a = z := by simp [ζ, hmem]
      exact hEq ▸ hz
    have hlim :
        Tendsto (fun a ↦ toWeakSpace ℝ H (ζ a)) atTop (𝓝 (toWeakSpace ℝ H x)) := by
      simpa [ζ] using hξ
    exact ⟨x, hC ζ x hζ hlim, rfl⟩

/-- Text 2.0.13 (3), weak-compactness clause: a subset of a real Hilbert space is weakly compact
iff every directed net in the set admits a weakly convergent subnet whose limit still belongs to
the set. -/
theorem isCompact_image_toWeakSpace_iff_forall_net_exists_subnet_tendsto
    {C : Set H} :
    IsCompact ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) ↔
      ∀ ⦃A : Type u⦄ [Nonempty A] [Preorder A] [IsDirectedOrder A] (ξ : A → H),
        (∀ a, ξ a ∈ C) →
          ∃ x ∈ C, ∃ (B : Type*) (_ : Nonempty B) (_ : Preorder B) (_ : IsDirectedOrder B)
            (φ : B → A),
            Monotone φ ∧ Tendsto φ atTop atTop ∧
              Tendsto (fun b ↦ toWeakSpace ℝ H (ξ (φ b))) atTop (𝓝 (toWeakSpace ℝ H x)) := by
  constructor
  · intro hC A _ _ _ ξ hξ
    have hcompact :
        EveryNetHasConvergentSubnetIn ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) :=
      (isCompact_iff_everyNetHasConvergentSubnetIn
        ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H))).1 hC
    rcases hcompact (fun a ↦ toWeakSpace ℝ H (ξ a)) (fun a ↦ ⟨ξ a, hξ a, rfl⟩) with
      ⟨y, hyC, B, _, _, _, φ, hφmono, hφtop, hφtend⟩
    rcases hyC with ⟨x, hx, rfl⟩
    exact ⟨x, hx, B, inferInstance, inferInstance, inferInstance, φ, hφmono, hφtop, hφtend⟩
  · intro hC
    refine
      (isCompact_iff_everyNetHasConvergentSubnetIn
        ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H))).2 ?_
    intro A _ _ _ ξ hξ
    let ζ : A → H := fun a ↦ (toWeakSpace ℝ H).symm (ξ a)
    have hζ : ∀ a, ζ a ∈ C := by
      intro a
      rcases hξ a with ⟨x, hx, hxEq⟩
      have hEq : ζ a = x := by
        simpa [ζ] using (congrArg (toWeakSpace ℝ H).symm hxEq).symm
      exact hEq ▸ hx
    rcases hC ζ hζ with ⟨x, hx, B, _, _, _, φ, hφmono, hφtop, hφtend⟩
    refine ⟨toWeakSpace ℝ H x, ⟨x, hx, rfl⟩, B, inferInstance, inferInstance, inferInstance,
      φ, hφmono, hφtop, ?_⟩
    simpa [ζ, Function.comp] using hφtend

/-! ### Text_2_0_14 (from Chap02) -/
universe u v w

open Filter
open scoped Topology

variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Text 2.0.14 (1): a map on a subset of a real Hilbert space is weakly continuous when it is
continuous from the weak subspace topology on the domain to the weak topology on the codomain. -/
def WeaklyContinuous {D : Set H} (T : D → K) : Prop :=
  letI : TopologicalSpace D :=
    TopologicalSpace.induced (fun x : D ↦ toWeakSpace ℝ H x) inferInstance
  Continuous fun x : D ↦ toWeakSpace ℝ K (T x)

-- Proof sketch: unfold `WeaklyContinuous`; continuity for the subtype of `WeakSpace ℝ H` is
-- equivalent to preservation of `atTop`-convergent directed nets in that weak subspace topology.
/-- Weak continuity on a subset is equivalent to preservation of weak convergence along every
directed net in that subset. -/
theorem weaklyContinuous_iff_forall_net_tendsto {D : Set H} {T : D → K} :
    WeaklyContinuous T ↔
      ∀ {A : Type w} [Preorder A] [IsDirectedOrder A] (ξ : A → D) (x : D),
        Tendsto
            (fun a ↦ toWeakSpace ℝ H (ξ a : H))
            atTop
            (𝓝 (toWeakSpace ℝ H (x : H))) →
          Tendsto
            (fun a ↦ toWeakSpace ℝ K (T (ξ a)))
            atTop
            (𝓝 (toWeakSpace ℝ K (T x))) := sorry

/-- Text 2.0.14 (2): an extended-real-valued function is weakly lower semicontinuous at `x` when
it is lower semicontinuous at `x` for the weak topology on the Hilbert space. -/
def WeaklyLowerSemicontinuousAt (f : H → EReal) (x : H) : Prop :=
  LowerSemicontinuousAt (f ∘ (toWeakSpace ℝ H).symm) (toWeakSpace ℝ H x)

-- Proof sketch: rewrite weak lower semicontinuity at `x` as lower semicontinuity at the point
-- `toWeakSpace ℝ H x`, then apply the canonical liminf characterization in the weak topology.
/-- Weak lower semicontinuity at a point is equivalent to the liminf inequality along every weakly
convergent directed net. -/
theorem weaklyLowerSemicontinuousAt_iff_forall_net_le_liminf
    (f : H → EReal) (x : H) :
    WeaklyLowerSemicontinuousAt f x ↔
      ∀ {A : Type w} [Preorder A] [IsDirectedOrder A] (ξ : A → H),
        Tendsto
            (fun a ↦ toWeakSpace ℝ H (ξ a))
            atTop
            (𝓝 (toWeakSpace ℝ H x)) →
          f x ≤ Filter.liminf (fun a ↦ f (ξ a)) atTop := sorry

/-- Text 2.0.14 (3): an extended-real-valued function is weakly lower semicontinuous when it is
lower semicontinuous for the weak topology on the Hilbert space. -/
def WeaklyLowerSemicontinuous (f : H → EReal) : Prop :=
  LowerSemicontinuous (f ∘ (toWeakSpace ℝ H).symm)

-- Proof sketch: this is the canonical theorem `lowerSemicontinuous_iff`, applied to the function
-- on `WeakSpace ℝ H` induced by `f`.
/-- Global weak lower semicontinuity is equivalent to pointwise weak lower semicontinuity. -/
theorem weaklyLowerSemicontinuous_iff_forall_weaklyLowerSemicontinuousAt
    (f : H → EReal) :
    WeaklyLowerSemicontinuous f ↔ ∀ x, WeaklyLowerSemicontinuousAt f x := by
  simpa [WeaklyLowerSemicontinuous, WeaklyLowerSemicontinuousAt] using
    (lowerSemicontinuous_iff :
      LowerSemicontinuous (f ∘ (toWeakSpace ℝ H).symm) ↔
        ∀ x : WeakSpace ℝ H,
          LowerSemicontinuousAt (f ∘ (toWeakSpace ℝ H).symm) x)
