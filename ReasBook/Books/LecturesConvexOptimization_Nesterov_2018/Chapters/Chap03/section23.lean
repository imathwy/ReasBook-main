import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_23 (from Chap03) -/
open ProperCone
open scoped Pointwise Topology
open scoped NormalCone

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Source-facing Lean notation for the textbook tangent-cone family `T_Q`. -/
namespace TangentCone

scoped notation:max "𝒯[" Q "]" => posTangentConeAt Q

end TangentCone

open scoped TangentCone

/- Definition 3.23 belongs to the chapter's canonical tangent-cone API around the owner
abstraction `posTangentConeAt`.

Primary domain:
- tangent and normal cones in real inner-product-space convex analysis.

Relevant declarations sampled before refinement:
- `posTangentConeAt`
- `posTangentConeAt_eq_closure_pointedConeHull_vsub_singleton`
- `normalCone`
- `ProperCone.innerDual_innerDual`

Owner abstraction:
- `posTangentConeAt`

Primitive data:
- the set `Q`
- the base point `xBar`

Derived API:
- the textbook polarization criterion
  `∀ g ∈ N[Q] xBar, 0 ≤ inner ℝ g p`

Source/core/bridge triage:
- source-facing: the textbook tangent-cone criterion at `xBar`
- core/canonical: `posTangentConeAt`
- bridge/view: `mem_tangentCone_iff`

This file therefore recalls the owner declaration directly instead of maintaining a parallel local
`tangentCone` definition. The public bridge theorem now uses the source-facing notation
`𝒯[Q] xBar` for the tangent cone together with Definition 3.22's normal-cone notation `N[Q] xBar`,
so the theorem surface matches the textbook polarity criterion directly. The textbook `ℝⁿ`
statement is a specialization of this owner-level inner-product-space bridge, and the closedness
hypothesis from the prose is omitted because the polarity criterion itself only depends on
convexity and the base-point condition `xBar ∈ Q`. -/

/-- Definition 3.23: for a convex set `Q` in a complete real inner-product space and `xBar ∈ Q`,
membership in the textbook tangent cone `𝒯[Q] xBar` is exactly the polarity condition against
every normal vector `g ∈ N[Q] xBar`. The notation `𝒯[Q] xBar` is the source-facing surface for the
canonical owner `posTangentConeAt Q xBar`, and the textbook `ℝⁿ` statement is the corresponding
specialization. -/
theorem mem_tangentCone_iff {Q : Set E} {xBar p : E}
    (hQ_convex : Convex ℝ Q) (hxBar : xBar ∈ Q) :
    p ∈ 𝒯[Q] xBar ↔
      ∀ g ∈ N[Q] xBar, 0 ≤ inner ℝ g p :=
by
  let S : Set E := Q -ᵥ ({xBar} : Set E)
  have hposTangentConeAt :
      posTangentConeAt Q xBar = closure ((PointedCone.hull ℝ S : Set E)) := by
    simpa [S] using
      posTangentConeAt_eq_closure_pointedConeHull_vsub_singleton Q hQ_convex xBar hxBar
  have hnormal :
      innerDual (closure ((PointedCone.hull ℝ S : Set E))) = N[Q] xBar := by
    ext g
    change g ∈ innerDual (closure ((PointedCone.hull ℝ S : Set E))) ↔ g ∈ innerDual S
    constructor
    · intro hg
      exact fun x hx ↦ hg <| subset_closure <| PointedCone.subset_hull hx
    · intro hg
      rw [mem_innerDual] at hg ⊢
      intro x hx
      let G : ProperCone ℝ E := innerDual ({g} : Set E)
      have hS : S ⊆ (G : Set E) := by
        intro y hy
        simpa [G, mem_innerDual, real_inner_comm] using hg hy
      have hhull : (PointedCone.hull ℝ S : Set E) ⊆ G := Submodule.span_le.mpr hS
      simpa [G, mem_innerDual, real_inner_comm] using
        (G.isClosed.closure_subset_iff.2 hhull) hx
  change p ∈ posTangentConeAt Q xBar ↔ p ∈ innerDual (N[Q] xBar : Set E)
  rw [hposTangentConeAt, ← hnormal]
  let C : ProperCone ℝ E := ⟨(PointedCone.hull ℝ S).closure, isClosed_closure⟩
  change p ∈ C ↔ p ∈ innerDual (((innerDual (C : Set E) : ProperCone ℝ E) : Set E))
  rw [innerDual_innerDual C]

/-! ### Lemma_3_23 (from Chap03) -/
noncomputable section

open Finset
open scoped BigOperators WithTopConvexAnalysis

universe uX uU

variable {N : ℕ}

/-
Lemma 3.23 lies in the chapter's primal-dual residual / lower-value domain.

Sampled owner-style declarations:
- `IsLeast`, the canonical order owner for attained lower values;
- mathlib `Finset.centerMass`, the canonical owner for the sampled dual average;
- `gapFunctionCertificate` in `Chap03/Lemma_3_24`, the chapter owner for the sampled certificate;
- `sampledAffineMinorant` in `Chap03/Proposition_3_26`, the chapter owner for one sampled affine
  lower model;
- the affine-map sum `∑ k, α k • ℓ k : X →ᵃ[ℝ] ℝ` in `Chap03/Proposition_3_27`, the canonical
  owner for weighted sums of sampled affine minorants;
- `primal_dual_decomposition_mem_Icc_of_gap_le` in `Chap03/Lemma_3_1_23`, the project's generic
  interval owner for the source-facing chain
  `0 ≤ (f(x_N) - f^*) + (φ^* - φ(\hat u_N)) ≤ f(x_N) - φ(\hat u_N) ≤ r_N`;
- `compact_convex_concave_minimax` in `Chap03/Theorem_3_37`, whose lower slice-value side uses the
  same canonical lower-value construction `u ↦ sInf ((fun x ↦ Ψ x u) '' P)`;
- `∂[P] f(x)` together with the bridge `subdifferentialWithin` in `Chap03/Theorem_3_44`, the
  source-facing owner surface for the relative subgradients used to build the affine lower model.

Best owner abstraction:
- source-facing: the textbook affine model `l_N` built from the sampled selections `u(y_k)` and
  `g(y_k)`, together with the resulting raw gap and interval estimate at the averaged dual point
- core/canonical: the lower slice-value owner
  `u ↦ sInf ((fun x ↦ Ψ x u) '' P)`
- bridge/view: the auxiliary sampled-family specialization of the canonical affine-map sum owner

Primitive data:
- the feasible primal and dual sets `P`, `S`
- the kernel `Ψ`
- the weights `α`, sample points `y`, the sampled-selection maps `u`, `g`
- the iterate `xN`, the attained affine-model minimum `modelMin`, and the residual bound `rN`

Derived API:
- the averaged sampled dual point `(Finset.univ).centerMass α (u ∘ y)`
- the textbook affine model
  `l_N = ∑ k, α k • sampledAffineMinorant (y k) (g (y k)) (Ψ (y k) (u (y k)))`
- the canonical lower slice value `u ↦ sInf ((fun x ↦ Ψ x u) '' P)`
- the auxiliary sampled-family bridge theorem obtained by replacing `u(y_k)` and `g(y_k)` by
  arbitrary sampled families
- the affine-model minimum witness `h_modelMin`

The previous version stated the public residual bound only for a normalized auxiliary sampled model
with arbitrary sampled dual and subgradient families, and it exposed a stronger global attainment
bridge `φ`. This refinement keeps the auxiliary sampled-family bridge, but restores the main
theorem to the textbook source-facing affine model `l_N` built from the sampled selections
`u(y_k)` and `g(y_k)` while placing the chapter's canonical lower-value owner
`u ↦ sInf ((fun x ↦ Ψ x u) '' P)` directly on the public theorem surface.
-/

section AveragedAffineLowerModel

variable {X : Type uX} [SeminormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {U : Type uU} [AddCommGroup U] [Module ℝ U]

variable {P : Set X} {S : Set U}
variable {f : X → ℝ}
variable {Ψ : X → U → ℝ}
variable {α : Fin (N + 1) → ℝ} {y : Fin (N + 1) → X}
variable {xN : X}
variable {modelMin rN fStar φStar : ℝ}

local notation "lowerValue" => fun u' : U ↦ sInf ((fun x ↦ Ψ x u') '' P)

section SampledAffineLowerModel

variable {g : Fin (N + 1) → X} {u : Fin (N + 1) → U}

local notation "uHat" => Finset.univ.centerMass α u
local notation "samplePoint[" k "]" => y k
local notation "sampledSlice[" k "]" => (((fun x ↦ Ψ x (u k)) : X → ℝ))
local notation "sampledModel" =>
  (∑ k, α k • sampledAffineMinorant (y k) (g k) (Ψ (y k) (u k)) : X →ᵃ[ℝ] ℝ)

/-- Helper for Lemma 3.23: evaluating the sampled affine model recovers the textbook weighted sum
of sampled affine minorants. -/
theorem sampled_model_apply (x : X) :
    sampledModel x =
      ∑ k, α k * (Ψ (y k) (u k) + inner ℝ (g k) (x - y k)) := by
  classical
  -- Expand the affine-map sum into the scalar textbook model.
  let s : Finset (Fin (N + 1)) := Finset.univ
  change (s.sum fun k ↦ α k • sampledAffineMinorant (y k) (g k) (Ψ (y k) (u k))) x =
      s.sum fun k ↦ α k * (Ψ (y k) (u k) + inner ℝ (g k) (x - y k))
  clear_value s
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s his ih =>
      simp [his, ih, sampledAffineMinorant_apply]

/-- Helper for Lemma 3.23: each sampled affine lower model lies below its corresponding sampled
slice on the feasible set `P`, and summing preserves that lower bound. -/
theorem sampled_model_le_sampled_slice_sum
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (h_subgrad : ∀ k : Fin (N + 1), g k ∈ ∂[P] (sampledSlice[k]) (samplePoint[k]))
    {x : X} (hx : x ∈ P) :
    sampledModel x ≤ ∑ k, α k * Ψ x (u k) := by
  have hsupport :
      ∀ k : Fin (N + 1),
        Ψ (y k) (u k) + inner ℝ (g k) (x - y k) ≤ Ψ x (u k) := by
    intro k
    rcases mem_subdifferentialWithin_iff.mp (h_subgrad k) with ⟨_, hminorant⟩
    exact hminorant hx
  -- Compare termwise after rewriting the affine-map sum in textbook scalar form.
  calc
    sampledModel x = ∑ k, α k * (Ψ (y k) (u k) + inner ℝ (g k) (x - y k)) := by
      rw [sampled_model_apply]
    _ ≤ ∑ k, α k * Ψ x (u k) := by
      refine Finset.sum_le_sum fun k _ ↦ ?_
      exact mul_le_mul_of_nonneg_left (hsupport k) (hα_nonneg k)

/-- Helper for Lemma 3.23: concavity in the dual variable turns the weighted sampled slice values
into the slice value at the averaged sampled dual point. -/
theorem sampled_slice_sum_le_center_mass_slice
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum_one : ∑ k, α k = 1)
    (hu_mem : ∀ k, u k ∈ S)
    (h_concave_u : ∀ x ∈ P, ConcaveOn ℝ S (fun v ↦ Ψ x v))
    {x : X} (hx : x ∈ P) :
    ∑ k, α k * Ψ x (u k) ≤ Ψ x uHat := by
  have h_center_mass :
      Finset.univ.centerMass α (((fun v ↦ Ψ x v) : U → ℝ) ∘ u) ≤ Ψ x uHat := by
    -- Apply Jensen's inequality to the concave slice `v ↦ Ψ x v`.
    exact (h_concave_u x hx).le_map_centerMass
      (t := Finset.univ)
      (fun k _ ↦ hα_nonneg k)
      (by simp [hα_sum_one])
      (fun k _ ↦ hu_mem k)
  -- Rewrite the center of mass of real slice values as the normalized weighted sum.
  rw [Finset.centerMass_eq_of_sum_1 (t := Finset.univ)
      (w := α) (((fun v ↦ Ψ x v) : U → ℝ) ∘ u) hα_sum_one] at h_center_mass
  simpa [Function.comp] using h_center_mass

/-- Helper for Lemma 3.23: the attained minimum of the sampled affine model is a lower bound for
the canonical lower slice value at the averaged sampled dual point. -/
theorem modelMin_le_lowerValue_uHat
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum_one : ∑ k, α k = 1)
    (hu_mem : ∀ k, u k ∈ S)
    (h_subgrad : ∀ k : Fin (N + 1), g k ∈ ∂[P] (sampledSlice[k]) (samplePoint[k]))
    (h_concave_u : ∀ x ∈ P, ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (h_modelMin : IsLeast (sampledModel '' P) modelMin) :
    modelMin ≤ lowerValue uHat := by
  rcases h_modelMin.1 with ⟨x0, hx0, _⟩
  refine le_csInf ?_ ?_
  · exact ⟨Ψ x0 uHat, ⟨x0, hx0, rfl⟩⟩
  · rintro b ⟨x, hx, rfl⟩
    have h_lower_model : modelMin ≤ sampledModel x := by
      exact h_modelMin.2 ⟨x, hx, rfl⟩
    -- Chain the affine-model lower bound with Jensen's inequality at the averaged dual point.
    exact h_lower_model.trans <|
      (sampled_model_le_sampled_slice_sum hα_nonneg h_subgrad hx).trans <|
        sampled_slice_sum_le_center_mass_slice hα_nonneg hα_sum_one hu_mem h_concave_u hx

/-- Auxiliary sampled-family bridge: if a convex combination of sampled affine minorants has least
feasible value `modelMin` and `f xN - modelMin ≤ r_N`, then the raw primal-dual gap against the
canonical lower value at the weighted sampled dual average is bounded by `r_N`. -/
-- Proof sketch: each relative subgradient inequality shows that the affine minorant
-- `x ↦ Ψ (y k) (u k) + ⟪g k, x - y k⟫` is bounded above on `P` by the corresponding slice
-- `x ↦ Ψ x (u k)`. Summing these affine minorants through the canonical affine-map owner
-- `sampledModel` yields a pointwise lower model on `P`. Concavity of `Ψ(x, ·)` on `S` and
-- `ConcaveOn.le_map_centerMass` then give
-- `(Finset.univ).centerMass α (fun k ↦ Ψ x (u k)) ≤ Ψ x uHat` for every `x ∈ P`. The resulting
-- pointwise domination on `P` makes `modelMin` a lower bound for `((fun x ↦ Ψ x uHat) '' P)`,
-- hence `modelMin ≤ lowerValue uHat`. Combining this with the residual bound yields the claim.
theorem duality_gap_le_residual_of_sampled_affine_lower_model
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum_one : ∑ k, α k = 1)
    (hu_mem : ∀ k, u k ∈ S)
    (h_subgrad : ∀ k : Fin (N + 1), g k ∈ ∂[P] (sampledSlice[k]) (samplePoint[k]))
    (h_concave_u : ∀ x ∈ P, ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (h_modelMin : IsLeast (sampledModel '' P) modelMin)
    (h_residual : f xN - modelMin ≤ rN) :
    f xN - lowerValue uHat ≤ rN := by
  have h_modelMin_le_lowerValue :
      modelMin ≤ lowerValue uHat :=
    modelMin_le_lowerValue_uHat
      hα_nonneg hα_sum_one hu_mem h_subgrad h_concave_u h_modelMin
  -- Replace the canonical lower value by the smaller affine-model minimum, then use the residual
  -- estimate against that minimum.
  exact (sub_le_sub_left h_modelMin_le_lowerValue (f xN)).trans h_residual

end SampledAffineLowerModel

section TextbookAffineLowerModel

variable {u : X → U} {g : X → X}

local notation "uHatN" => Finset.univ.centerMass α (u ∘ y)
local notation "samplePoint[" k "]" => y k
local notation "sampledSlice[" k "]" => (((fun x ↦ Ψ x (u (y k))) : X → ℝ))
local notation "lN" =>
  (∑ k, α k • sampledAffineMinorant (y k) (g (y k)) (Ψ (y k) (u (y k))) : X →ᵃ[ℝ] ℝ)

/- The textbook source-facing affine model is the sampled affine-map owner specialized to the dual
and subgradient selections `u(y_k)` and `g(y_k)`. -/

/-- Lemma 3.23: if `x_N` satisfies the residual estimate against the textbook affine model
`l_N = ∑_{k=0}^N α_k [Ψ(y_k, u(y_k)) + ⟪g(y_k), · - y_k⟫]`
built from the sampled selections `u(y_k)` and
`g(y_k) ∈ ∂[P] (fun x ↦ Ψ x (u(y_k))) (y_k)`, then the raw primal-dual gap against the canonical
lower value at the averaged sampled dual point
`\hat u_N = (Finset.univ).centerMass α (u ∘ y)` is bounded above by `r_N`. -/
-- Proof sketch: specialize the auxiliary sampled-family bridge to the concrete sampled families
-- `u ∘ y` and `g ∘ y`. This turns the generic sampled affine-map sum into the textbook model
-- `l_N` and the generic center of mass into the textbook averaged sampled dual point `uHatN`.
theorem duality_gap_le_residual_of_averaged_affine_lower_model
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum_one : ∑ k, α k = 1)
    (hu_mem : ∀ k, u (y k) ∈ S)
    (h_subgrad :
      ∀ k : Fin (N + 1), g (y k) ∈ ∂[P] (sampledSlice[k]) (samplePoint[k]))
    (h_concave_u : ∀ x ∈ P, ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (h_modelMin : IsLeast (lN '' P) modelMin)
    (h_residual : f xN - modelMin ≤ rN) :
    f xN - lowerValue uHatN ≤ rN := by
  let uSample : Fin (N + 1) → U := u ∘ y
  let gSample : Fin (N + 1) → X := g ∘ y
  have hu_mem_sample : ∀ k, uSample k ∈ S := by
    simpa [uSample] using hu_mem
  have h_subgrad_sample :
      ∀ k : Fin (N + 1),
        gSample k ∈ subdifferentialWithin P ((fun x ↦ Ψ x (uSample k)) : X → ℝ) (y k) := by
    simpa [uSample, gSample] using h_subgrad
  simpa [uSample, gSample] using
    duality_gap_le_residual_of_sampled_affine_lower_model
      hα_nonneg hα_sum_one hu_mem_sample h_subgrad_sample h_concave_u h_modelMin h_residual

/-- Interval companion of Lemma 3.23: once `fStar` and `φStar` are known to bound the sampled
primal and dual values at `xN` and `uHatN`, the textbook affine-model residual bound yields the
full decomposition interval estimate. -/
-- Proof sketch: first apply the raw-gap theorem above to obtain
-- `f xN - lowerValue uHatN ≤ rN`. The generic Chapter 3 interval owner
-- `primal_dual_decomposition_mem_Icc_of_gap_le` then applies directly from the local comparison
-- bounds `fStar ≤ f xN` and `lowerValue uHatN ≤ φStar` together with weak duality.
theorem primal_dual_decomposition_mem_Icc_and_gap_le_of_averaged_affine_lower_model
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum_one : ∑ k, α k = 1)
    (hu_mem : ∀ k, u (y k) ∈ S)
    (h_subgrad :
      ∀ k : Fin (N + 1), g (y k) ∈ ∂[P] (sampledSlice[k]) (samplePoint[k]))
    (h_concave_u : ∀ x ∈ P, ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (h_modelMin : IsLeast (lN '' P) modelMin)
    (h_residual : f xN - modelMin ≤ rN)
    (h_primal : fStar ≤ f xN)
    (h_dual : lowerValue uHatN ≤ φStar)
    (h_weak_duality : φStar ≤ fStar) :
    (f xN - fStar) + (φStar - lowerValue uHatN) ∈
        Set.Icc 0 (f xN - lowerValue uHatN) ∧
      f xN - lowerValue uHatN ≤ rN := by
  have h_gap :
      f xN - lowerValue uHatN ≤ rN :=
    duality_gap_le_residual_of_averaged_affine_lower_model
      hα_nonneg hα_sum_one hu_mem h_subgrad h_concave_u h_modelMin h_residual
  simpa using
    (primal_dual_decomposition_mem_Icc_of_gap_le
      h_primal
      h_dual
      h_weak_duality
      h_gap)

end TextbookAffineLowerModel

end AveragedAffineLowerModel

end

/-! ### Proposition_3_23 (from Chap03) -/
noncomputable section

open Matrix
open scoped ConstrainedArgmin
open scoped NormalCone
open scoped WithTopConvexAnalysis

/-
Proposition 3.23 lies in the chapter's equality-constrained convex-optimality / normal-cone
domain.

Relevant owner declarations sampled before refinement:
* `mem_constrainedArgmin_iff_exists_subgradient_mem_normalCone` in `Theorem_3_1_24`, the chapter
  owner theorem for constrained convex optimality in normal-cone form
* `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical owner
  for feasible minimizers on a set
* `normalCone_linearLevelSet` in `Proposition_3_22`, the affine-level-set normal-cone formula
  `(N[{x | L x = b}] xStar : Set E) = L.adjoint.range`
* `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`, the matrix/linear-map bridge identifying
  `Aᵀ` with the adjoint of `A.toEuclideanLin`

Best owner abstraction:
* the affine level set `{x | L x = b}` together with the constrained-optimality owner theorem
  `mem_constrainedArgmin_iff_exists_subgradient_mem_normalCone`

Primitive data:
* a convex objective `f : E → ℝ`
* a linear equality constraint `L x = b`
* a feasible base point `xStar`

Derived API:
* the affine-level-set specialization of the normal-cone optimality criterion
* the adjoint-range reformulation on finite-dimensional inner-product spaces
* the Euclidean matrix/transpose specialization `Aᵀ yStar ∈ ∂ f(xStar)`

Source/core/bridge triage:
* source-facing: Proposition 3.23's equality-constrained optimality criteria in normal-cone and
  transpose form
* core/canonical: `argmin[Q] f`, `mem_constrainedArgmin_iff_exists_subgradient_mem_normalCone`,
  `N[Q] xStar`, and `normalCone_linearLevelSet`
* bridge/view: `mem_constrainedArgmin_iff`, `L.adjoint.range`, and the transpose/adjoint
  identification for matrices

The previous file exposed a conditional decomposition hypothesis for the constrained
subdifferential. That weakened the source-facing proposition into a bridge lemma. This refinement
instead specializes the existing chapter owner theorem for constrained convex optimality directly
to the affine set `{x | L x = b}`, and only then rewrites the resulting normal-cone certificate
through the canonical affine normal-cone formula and the matrix transpose/adjoint bridge.
-/

section

variable {E Λ : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]

/-- Proposition 3.23, affine normal-cone form: for a convex objective on a real inner-product
space, a feasible point minimizes `f` on the affine level set `{x | L x = b}` exactly when some
subgradient at that point lies in the normal cone of the level set. -/
theorem isMinOn_linearLevelSet_iff_exists_subgradient_mem_normalCone
    [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    (L : E →ₗ[ℝ] Λ) (b : Λ) {xStar : E}
    (hxStar : L xStar = b) :
    IsMinOn f {x | L x = b} xStar ↔
      ∃ gStar : E,
        gStar ∈ ∂ (fun x : E ↦ (f x : WithTop ℝ))(xStar) ∧
          gStar ∈ N[{x | L x = b}] xStar := by
  let Q : Set E := {x | L x = b}
  have hxQ : xStar ∈ Q := by
    simpa [Q] using hxStar
  have hQ_convex : Convex ℝ Q := by
    simpa [Q] using (convex_singleton b).linear_preimage L
  have howner :
      xStar ∈ argmin[Q] f ↔
        ∃ gStar : E,
          gStar ∈ ∂ (fun x : E ↦ (f x : WithTop ℝ))(xStar) ∧
            gStar ∈ N[Q] xStar :=
    mem_constrainedArgmin_iff_exists_subgradient_mem_normalCone
      hQ_convex hf_conv hxQ
  rw [mem_constrainedArgmin_iff] at howner
  constructor
  · intro hxMin
    exact howner.mp ⟨hxQ, hxMin⟩
  · intro hcert
    exact (howner.mpr hcert).2

end

section

variable {E Λ : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]

/-- Proposition 3.23, affine adjoint-range form: on a finite-dimensional affine level set
`{x | L x = b}`, optimality is equivalent to the existence of a subgradient in the adjoint range
`range Lᵀ`. -/
theorem isMinOn_linearLevelSet_iff_exists_adjoint_subgradient
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ Λ]
    {f : E → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    (L : E →ₗ[ℝ] Λ) (b : Λ) {xStar : E}
    (hxStar : L xStar = b) :
    IsMinOn f {x | L x = b} xStar ↔
      ∃ yStar : Λ, L.adjoint yStar ∈ ∂ (fun x : E ↦ (f x : WithTop ℝ))(xStar) := by
  have hnormal :
      (N[{x : E | L x = b}] xStar : Set E) = L.adjoint.range :=
    normalCone_linearLevelSet L b hxStar
  rw [isMinOn_linearLevelSet_iff_exists_subgradient_mem_normalCone
      hf_conv L b hxStar]
  constructor
  · rintro ⟨gStar, hgStar, hgNormal⟩
    have hgRange : gStar ∈ L.adjoint.range := by
      change gStar ∈ ((N[{x : E | L x = b}] xStar : Set E)) at hgNormal
      rw [hnormal] at hgNormal
      exact hgNormal
    rcases Set.mem_range.mp hgRange with ⟨yStar, hyStar⟩
    exact ⟨yStar, hyStar.symm ▸ hgStar⟩
  · rintro ⟨yStar, hyStar⟩
    have hyNormal : L.adjoint yStar ∈ N[{x : E | L x = b}] xStar := by
      have hyRange : L.adjoint yStar ∈ L.adjoint.range := ⟨yStar, rfl⟩
      change L.adjoint yStar ∈ (N[{x : E | L x = b}] xStar : Set E)
      rw [hnormal]
      exact hyRange
    exact ⟨L.adjoint yStar, hyStar, hyNormal⟩

end

section

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/-- Proposition 3.23, textbook matrix form: on the affine level set `{x | A x = b}`, a feasible
point minimizes `f` exactly when some transpose image `Aᵀ yStar` belongs to `∂ f(xStar)`. -/
theorem isMinOn_matrix_linearLevelSet_iff_exists_transpose_subgradient
    {f : Eₙ → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) {xStar : Eₙ}
    (hxStar : A.toEuclideanLin xStar = b) :
    IsMinOn f {x | A.toEuclideanLin x = b} xStar ↔
      ∃ yStar : Eₘ,
        Aᵀ.toEuclideanLin yStar ∈ ∂ (fun x : Eₙ ↦ (f x : WithTop ℝ))(xStar) := by
  have hAdj : A.toEuclideanLin.adjoint = Aᵀ.toEuclideanLin := by
    simpa using (toEuclideanLin_conjTranspose_eq_adjoint A).symm
  simpa [hAdj] using
    isMinOn_linearLevelSet_iff_exists_adjoint_subgradient
      hf_conv A.toEuclideanLin b hxStar

end

end

/-! ### Theorem_3_23 (from Chap03) -/
/- Theorem 3.23 lies in the chapter's extended-valued convex-analysis / subdifferential domain.

Relevant owner-style declarations sampled before refinement:
- `IsSubgradientAt`
- `subdifferential`
- `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`
- `subgradient_inner_sub_nonneg_of_isMinOn`

Best owner abstraction:
- the intrinsic subdifferential owner `subdifferential` together with the minimizer theorem
  `subgradient_inner_sub_nonneg_of_isMinOn`

Primitive data:
- a feasible set `Q`, an extended-real objective `f`, points `x0`, `xStar`, `g`
- the feasibility hypothesis `hx0 : x0 ∈ Q`
- the minimizing hypothesis `hxStar : IsMinOn f Q xStar`
- the owner-membership hypothesis `hg : g ∈ subdifferential f x0`

Derived API:
- the nonnegative pairing inequality `0 ≤ inner ℝ g (x0 - xStar)`

Source/core/bridge triage:
- source-facing: this textbook minimizer-pairing theorem
- core/canonical: `subdifferential`, `IsSubgradientAt`, `IsMinOn`, and the theorem
  `subgradient_inner_sub_nonneg_of_isMinOn`
- bridge/view: the former Euclidean/closed/convex wrapper, now deleted because its extra
  hypotheses were redundant and created a duplicate theorem surface

The earlier version of this file reintroduced a second public theorem with the same name and
mathematical content, but on an over-concrete Euclidean wrapper API carrying unused convexity,
closedness, nonemptiness, and domain hypotheses. The intrinsic owner theorem already exists in
`Theorem_3_1_5_6` with the exact source-facing conclusion, so this item is now a direct recall
instead of a parallel duplicate. -/

recall subgradient_inner_sub_nonneg_of_isMinOn
