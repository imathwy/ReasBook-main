

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_4 (from Chap03) -/
noncomputable section

universe u

/- Definition 3.4 is `source-facing` in the inequality-constrained duality API. Its primitive data
are the Lagrangian and the resulting dual objective. Chapter 2's `effective_domain` remains the
owner abstraction for finite-valued loci, but the multiplier nonnegativity condition belongs to
the separate source-facing dual-domain layer rather than being folded into the dual objective
itself. Accordingly, `q` is the raw Lagrangian infimum, while the admissible dual multipliers are
described by coordinatewise nonnegativity together with lower-finiteness of `q`. -/

section

variable {E : Type u} {m : ℕ}
variable (X : Set E) (f : E → ℝ) (g : E → EuclideanSpace ℝ (Fin m))

local notation "MultiplierSpace" => EuclideanSpace ℝ (Fin m)

/-- The Lagrangian associated to `f`, the inequality-constraint map `g`, and a multiplier vector. -/
def lagrangian (multiplier : MultiplierSpace) : E → ℝ :=
  fun x ↦ f x + dotProduct multiplier (g x)

-- Proof sketch: unfold `lagrangian`; the statement is exactly its defining formula.
/-- The Lagrangian is the objective value plus the Euclidean pairing of the multiplier with the
constraint vector. -/
@[simp] theorem lagrangian_apply (multiplier : MultiplierSpace) (x : E) :
    lagrangian f g multiplier x = f x + dotProduct multiplier (g x) :=
  rfl

/-- Definition 3.4: the Lagrangian dual objective function of the constrained problem
`min {f x : g x ≤ 0, x ∈ X}`. It is the infimum of the Lagrangian over `X`; the coordinatewise
nonnegativity restriction on multipliers is imposed separately in the dual-domain layer. -/
def lagrangian_dual_objective (multiplier : MultiplierSpace) : EReal :=
  sInf ((fun x : E ↦ (lagrangian f g multiplier x : EReal)) '' X)

-- Proof sketch: unfold `lagrangian_dual_objective`; the statement is exactly its defining
-- infimum formula.
/-- Evaluating the dual objective at a multiplier gives the infimum of the `EReal`-valued
Lagrangian over `X`. -/
theorem lagrangian_dual_objective_eq_sInf
    (multiplier : MultiplierSpace) :
    lagrangian_dual_objective X f g multiplier =
      sInf ((fun x : E ↦ (lagrangian f g multiplier x : EReal)) '' X) :=
  rfl

/-- The source-facing dual domain consists of the coordinatewise nonnegative multipliers at which
the negated dual objective belongs to the Chapter 2 owner `effective_domain`. -/
def lagrangian_dual_effective_domain : Set MultiplierSpace :=
  {multiplier | ∀ i : Fin m, 0 ≤ multiplier i} ∩
    effective_domain (fun μ ↦ -lagrangian_dual_objective X f g μ)

-- Proof sketch: unfold `lagrangian_dual_effective_domain` to `effective_domain (-q)` and use the
-- `EReal` identity `-q(λ) < ⊤ ↔ q(λ) ≠ ⊥ ↔ ⊥ < q(λ)`.
/-- A multiplier lies in `dom (-q)` exactly when it is coordinatewise nonnegative and the dual
objective is greater than `-∞` there. -/
@[simp] theorem mem_lagrangian_dual_effective_domain
    (multiplier : MultiplierSpace) :
    multiplier ∈ lagrangian_dual_effective_domain X f g ↔
      (∀ i : Fin m, 0 ≤ multiplier i) ∧ ⊥ < lagrangian_dual_objective X f g multiplier := by
  simp [lagrangian_dual_effective_domain, effective_domain, lt_top_iff_ne_top,
    EReal.neg_eq_top_iff, bot_lt_iff_ne_bot]

end

/-! ### Lemma_3_4 (from Chap03) -/
noncomputable section

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]
variable {m p : ℕ}

local notation "InequalitySpace" => EuclideanSpace ℝ (Fin m)
local notation "EqualitySpace" => EuclideanSpace ℝ (Fin p)
local notation "PerturbationSpace" =>
  InequalitySpace × EqualitySpace

/- Lemma 3.4 is `source-facing` in the perturbation-value-function API. Its
`core/canonical` owner declarations are the Chapter 2 convexity predicate
`is_convex_function` and the partial-minimization theorem
`partial_infimum_is_convex_function`. This file keeps only the source-facing
feasible-set and value-function constructions, with the membership/evaluation
facts exposed as derived simp lemmas. -/
recall is_convex_function
recall partial_infimum_is_convex_function

/-- The feasible set for the perturbation parameter `(u, t)` consists of the points of `X`
satisfying the coordinatewise inequality constraints `g i x ≤ u i` and the affine equality
constraint `A x + b = t`. -/
def value_function_feasible_set (X : Set E) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] EqualitySpace) (b : EqualitySpace)
    (u : InequalitySpace) (t : EqualitySpace) : Set E :=
  {x | x ∈ X ∧ (∀ i : Fin m, g i x ≤ (u i : EReal)) ∧ A x + b = t}

-- Proof sketch: unfold `value_function_feasible_set`; membership is exactly the conjunction of
-- belonging to `X`, satisfying each scalar inequality constraint, and solving the affine equality
-- constraint.
/-- A point lies in the perturbation feasible set exactly when it belongs to `X`, satisfies every
inequality constraint, and meets the affine equality constraint. -/
@[simp] theorem mem_value_function_feasible_set (X : Set E) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] EqualitySpace) (b : EqualitySpace)
    (u : InequalitySpace) (t : EqualitySpace) (x : E) :
    x ∈ value_function_feasible_set X g A b u t ↔
      x ∈ X ∧ (∀ i : Fin m, g i x ≤ (u i : EReal)) ∧ A x + b = t :=
  Iff.rfl

/-- The perturbation value function assigns to `(u, t)` the infimum of `f` over the feasible set
cut out by the perturbation constraints. -/
def value_function (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] EqualitySpace) (b : EqualitySpace) :
    PerturbationSpace → EReal :=
  Function.uncurry fun u t ↦ sInf (f '' value_function_feasible_set X g A b u t)

-- Proof sketch: unfold `value_function`; evaluation at `(u, t)` is definitionally the infimum of
-- the image of `f` on `value_function_feasible_set X g A b u t`.
/-- Evaluating the perturbation value function at `(u, t)` gives the infimum of `f` over the
corresponding feasible set. -/
@[simp] theorem value_function_apply (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] EqualitySpace) (b : EqualitySpace)
    (u : InequalitySpace) (t : EqualitySpace) :
    value_function X f g A b (u, t) =
      sInf (f '' value_function_feasible_set X g A b u t) :=
  rfl

-- Proof sketch: if `∀ i, u i ≤ w i`, every point feasible for `u` is also feasible for `w`,
-- because the only changing conditions are the coordinatewise bounds `g i x ≤ u i`. Membership in
-- `X` and the affine equality constraint are unchanged.
/-- Relaxing the inequality perturbation coordinates enlarges the perturbation feasible set. -/
theorem value_function_feasible_set_mono_u (X : Set E) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] EqualitySpace) (b : EqualitySpace)
    {u w : InequalitySpace} {t : EqualitySpace} (huw : ∀ i : Fin m, u i ≤ w i) :
    value_function_feasible_set X g A b u t ⊆ value_function_feasible_set X g A b w t := sorry

-- Proof sketch: `value_function_feasible_set_mono_u` shows the feasible set for `u` sits inside
-- the feasible set for `w` whenever `∀ i, u i ≤ w i`. Taking infima of `f` over these nested
-- feasible sets yields antitonicity in the inequality perturbation parameter.
/-- For fixed equality perturbation `t`, the perturbation value function is antitone in the
inequality perturbation parameter. -/
theorem value_function_antitone_u (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] EqualitySpace) (b : EqualitySpace)
    {u w : InequalitySpace} {t : EqualitySpace} (huw : ∀ i : Fin m, u i ≤ w i) :
    value_function X f g A b (u, t) ≥ value_function X f g A b (w, t) := sorry

-- Proof sketch: view `value_function X f g A b` as the partial infimum in the `E`-variable of the
-- jointly convex constrained objective on `E × (ℝ^m × ℝ^p)` that equals `f x` on the convex set of
-- triples `(x, u, t)` with `x ∈ X`, `g i x ≤ u i`, and `A x + b = t`, and equals `⊤` outside that
-- set. Convexity of `X`, of `f`, and of each `g i`, together with linearity of `A`, gives
-- convexity of that owner objective, so `partial_infimum_is_convex_function` yields convexity of
-- the value function directly, with no properness hypothesis.
/-- Lemma 3.4: if `f` and all constraint functions `g i` are convex and `X` is convex, then the
perturbation value function is convex on `ℝ^m × ℝ^p`. -/
theorem value_function_is_convex (X : Set E) (f : E → EReal) (g : Fin m → E → EReal)
    (A : E →ₗ[ℝ] EqualitySpace) (b : EqualitySpace)
    (hf_convex : is_convex_function f) (hg_convex : ∀ i : Fin m, is_convex_function (g i))
    (hX_convex : Convex ℝ X) :
    is_convex_function (value_function X f g A b) := sorry

end

/-! ### Proposition_3_4 (from Chap03) -/
open scoped Matrix

noncomputable section

section SymmetricMatrices

open Matrix

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "𝕊" => symmetricMatrices n

/- Proposition 3.4 is `source-facing` in the chapter spectral-subdifferential API. The ambient
owner object for the matrix variable is the canonical submodule `symmetricMatrices n = 𝕊^n` from
Definition 1.30, while the spectral owner data comes from mathlib's
`Matrix.IsHermitian.eigenvalues`. The public declarations below keep the book's
maximum-eigenvalue function and rank-one symmetric matrix as the source-facing views derived from
those owners. -/

recall euclideanSubdifferentialAt

-- Proof sketch: the project owner criterion `mem_symmetricMatrices_iff` identifies membership in
-- `𝕊^n` with symmetry. The transpose of `vvᵀ` is again `vvᵀ` by `transpose_vecMulVec`.
/-- The real rank-one matrix `vvᵀ` belongs to the symmetric-matrix space `𝕊^n`. -/
private theorem rankOneMatrix_mem_symmetricMatrices (v : E) :
    vecMulVec v v ∈ symmetricMatrices n := by
  rw [mem_symmetricMatrices_iff, transpose_vecMulVec]

variable [NeZero n]

/-- `symmetricMaxEigenvalue X` is the largest eigenvalue of the symmetric matrix `X`, using the
canonical descending ordering of the Hermitian spectrum. -/
noncomputable def symmetricMaxEigenvalue (X : 𝕊) : ℝ :=
  let hX := X.property.isHermitian
  hX.eigenvalues 0

/-- `symmetricRankOne v` is the symmetric rank-one matrix `vvᵀ`, regarded as an element of
`𝕊^n`. -/
def symmetricRankOne (v : E) : 𝕊 :=
  ⟨vecMulVec v v, rankOneMatrix_mem_symmetricMatrices v⟩

-- Proof sketch: use the Rayleigh quotient characterization
-- `λ_max Y = max_{‖u‖ = 1} uᵀYu`, evaluate it at the given eigenvector `v`, and rewrite
-- `vᵀ(Y - X)v` as the Frobenius inner product with `vvᵀ`, then apply the Riesz identification
-- between `𝕊^n` and its continuous dual, as packaged by `euclideanSubdifferentialAt`.
/-- Proposition 3.4: if `v` is a unit eigenvector of the symmetric matrix `X` for the largest
eigenvalue, then the rank-one matrix `vvᵀ` belongs to the Euclidean subdifferential of the
maximum-eigenvalue function at `X`; equivalently, via the Frobenius trace-pairing Riesz
identification, it represents a dual subgradient at `X`. -/
theorem symmetricRankOne_mem_euclideanSubdifferentialAt_symmetricMaxEigenvalue
    (X : 𝕊) (v : E) (hv_norm : ‖v‖ = 1)
    (hv_eigen : (X : Matrix (Fin n) (Fin n) ℝ) *ᵥ v = symmetricMaxEigenvalue X • v) :
    symmetricRankOne v ∈ euclideanSubdifferentialAt symmetricMaxEigenvalue X := sorry

end SymmetricMatrices

/-! ### Theorem_3_4 (from Chap03) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 3.4 is `source-facing` in the chapter real-valued convex-analysis API. The
`core/canonical` owner notions are Chapter 3's `subdifferential` and `strongDualSubdifferential`;
the declaration `subdifferentialAt` below is the stable real-valued specialization used
throughout the chapter, not a second owner abstraction. -/
/-- The real-valued subdifferential at `x`, viewed through the chapter's strong-dual bridge for
the extended-real-valued coercion of `f`. -/
abbrev subdifferentialAt (f : E → ℝ) (x : E) : Set (StrongDual ℝ E) :=
  strongDualSubdifferential (fun y ↦ (f y : EReal)) x

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: view `f` as the everywhere-finite extended-real-valued function
-- `y ↦ (f y : EReal)`. Its effective domain is all of `E`, so every `x` is an interior point.
-- The owner theorem `subdifferential_nonempty_at_interior_point` yields an algebraic dual
-- subgradient, and finite dimensionality upgrades that linear functional canonically to a
-- continuous one via `LinearMap.toContinuousLinearMap`; this is exactly a point of
-- `subdifferentialAt f x`.
/-- Theorem 3.4 in owner-set form: every real-valued convex function on `E` is subdifferentiable
at each point. -/
theorem subdifferentialAt_nonempty_of_convexOn {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x : E) :
    (subdifferentialAt f x).Nonempty := by
  have hconvex : is_convex_function (fun y ↦ (f y : EReal)) := by
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro y hy
      simp
    · simpa [effective_domain] using hf
  have hx : x ∈ interior (effective_domain (fun y ↦ (f y : EReal))) := by
    simp [effective_domain]
  rcases
      subdifferential_nonempty_at_interior_point
        (fun y ↦ (f y : EReal)) x hconvex hx with
    ⟨g, hg⟩
  exact ⟨LinearMap.toContinuousLinearMap g, by simpa [subdifferentialAt] using hg⟩

end

section

open InnerProductSpace (toDualMap)

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Euclidean/vector-side subdifferential at `x`, obtained by transporting the owner
`subdifferentialAt f x : Set (StrongDual ℝ E)` back to vectors using the Riesz map `toDualMap`.
This is a derived `bridge/view` API obtained by specializing `euclideanSubdifferential` to the
everywhere-finite coercion of `f`; `subdifferentialAt` remains the owner abstraction. -/
abbrev euclideanSubdifferentialAt (f : E → ℝ) (x : E) : Set E :=
  euclideanSubdifferential (fun y ↦ (f y : EReal)) x

/-- Membership in `euclideanSubdifferentialAt f x` is definitionally membership of the
corresponding functional `toDualMap ℝ E z` in `subdifferentialAt f x`. -/
@[simp] theorem mem_euclideanSubdifferentialAt_iff
    {f : E → ℝ} {x z : E} :
    z ∈ euclideanSubdifferentialAt f x ↔
      toDualMap ℝ E z ∈ subdifferentialAt f x :=
  mem_euclideanSubdifferential_iff

end
