import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_35_8_1 (from Chap07) -/
noncomputable section

open scoped Rockafellar Topology
open Function

universe u v

namespace Bifunction

section

variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace ℝ U]
variable [SeminormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]

/-!
Source/core/bridge triage:

- `source-facing`: this corollary characterizes differentiability of the finite real branch of a
  concave-convex saddle-function at an interior point of the saddle effective domain by linearity
  of the mixed directional derivative, and then gives the corresponding basis-line criterion and
  its product-coordinate-line specialization under that same interior-domain hypothesis.
- `core/canonical`: the surrounding chapter already owns the relevant notions as
  `DifferentiableAt ℝ (uncurry K).realBranch (u, v)`,
  `directionalDerivativeAt (uncurry K) (u, v)`, the Chapter 25 owner
  `(uncurry K).HasLinearDirectionalDerivativeAt (u, v)`, the product-space basis owner
  `Module.Basis ι ℝ (U × V)`, and the Chapter 34/35 domain owner `dom K`.
- `bridge/view`: the source wording “finite on a neighborhood of `(u, v)`” is canonically rendered
  by the owner condition `(u, v) ∈ interior (dom K)`, while the source wording “the directional
  derivative function is linear” is rendered directly by the canonical Chapter 25 owner on the
  product directional derivative. The coordinate-line version is a specialization through the
  canonical product basis `bU.prod bV`.

Domain-style sampling used here:

- `Module.Basis.prod` from mathlib for the owner-level product basis on `U × V`;
- `Function.differentiableAt_iff_hasLinearDirectionalDerivativeAt` from
  `Chap05.Theorem_25_2`;
- `Bifunction.differentiableAt_uncurry_iff_existsUnique_mem_subdifferentialAt` and
  `Bifunction.subdifferentialAt_eq_prod_singleton_fderiv_of_differentiableAt`
  from `Chap07.Theorem_35_8`;
- `Function.directionalDerivativeAt` from `Chap05.Lemma_23_0_1`;
- `SaddleFunction.dom` and `SaddleFunction.mem_interior_dom` from
  `Chap07.Defn_34_3` / `Chap07.Text_35_5_5`;
- `SaddleFunction.bot_lt_and_lt_top_of_mem_dom` from `Chap07.Text_34_1_6`.

Primitive data vs derived API:

- primitive source data: the concave-convex saddle-function `K`, the point `(u, v)`, and the
  local-finiteness owner hypothesis `(u, v) ∈ interior (dom K)`;
- primitive ambient assumptions: finite-dimensionality of each factor space `U` and `V`;
- primitive bridge data for the sufficient criterion: a basis `b : Module.Basis ι ℝ (U × V)` and
  line differentiability of `(uncurry K).realBranch` at `(u, v)` along each `b i`;
- derived API: the interior-point differentiability criterion and the coordinate-line sufficient
  condition obtained from `Module.Basis.prod`.

Layer target: `source-facing`, stated directly on the canonical Chapter 25/35 owners.
-/

-- Proof sketch: the interior-domain hypothesis is the chapter owner for Rockafellar's local
-- finiteness hypothesis, so it replaces the incorrect attempt to infer interiority from
-- differentiability of the totalized branch `realBranch`. Use interiority to recover the finite
-- point data needed for Theorem 35.8, then combine Theorem 35.8 with the Chapter 25 criterion on
-- the product real branch.
/-- Corollary 35.8.1: at an interior point of the effective domain of a concave-convex
saddle-function `K`, the finite real branch `(uncurry K).realBranch` is differentiable if and
only if the mixed directional-derivative owner
`d ↦ directionalDerivativeAt (uncurry K) (u, v) d` is linear in Rockafellar's Chapter 25 sense,
i.e. `(uncurry K).HasLinearDirectionalDerivativeAt (u, v)`. -/
theorem differentiableAt_realBranch_uncurry_iff_hasLinearDirectionalDerivativeAt_of_mem_interior_dom
    {K : U → V → WithBotTop ℝ} (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    {u : U} {v : V} (huv : (u, v) ∈ interior (dom K)) :
    DifferentiableAt ℝ (uncurry K).realBranch (u, v) ↔
      (uncurry K).HasLinearDirectionalDerivativeAt (u, v) := sorry

end

section

variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace ℝ U]
variable [SeminormedAddCommGroup V] [NormedSpace ℝ V]

-- Proof sketch: keep the local-finiteness owner `(u, v) ∈ interior (dom K)` explicit, since
-- line differentiability of the totalized branch `realBranch` does not force interiority of
-- `dom K`. A finite basis of `U × V` supplies the coordinate data and the needed
-- finite-dimensionality locally for linearity of the mixed directional-derivative owner.
/-- Basis-line criterion: at an interior point `(u, v)` of `dom K`, if the finite real branch is
line-differentiable along every vector of a finite basis of the product space `U × V`, then the
mixed directional derivative is linear at `(u, v)`. -/
theorem hasLinearDirectionalDerivativeAt_of_mem_interior_dom_of_lineDifferentiableAt_basis
    {ι : Type*} [Finite ι]
    {K : U → V → WithBotTop ℝ}
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    {u : U} {v : V} (huv : (u, v) ∈ interior (dom K))
    (b : Module.Basis ι ℝ (U × V))
    (hline : ∀ i : ι, LineDifferentiableAt ℝ (uncurry K).realBranch (u, v) (b i)) :
    (uncurry K).HasLinearDirectionalDerivativeAt (u, v) :=
  sorry

-- Proof sketch: apply the basis-line theorem to the canonical product basis `bU.prod bV`; the
-- first-variable and second-variable coordinate hypotheses are exactly the `Sum.inl` and
-- `Sum.inr` cases.
/-- Product-coordinate-line criterion: at an interior point `(u, v)` of `dom K`, if the finite
real branch is line-differentiable along all directions `(bU i, 0)` and `(0, bV j)` from finite
bases `bU`, `bV`, then the mixed directional derivative is linear at `(u, v)`. -/
theorem hasLinearDirectionalDerivativeAt_of_mem_interior_dom_of_coordLineDifferentiableAt
    {ιU : Type*} [Finite ιU] {ιV : Type*} [Finite ιV]
    {K : U → V → WithBotTop ℝ}
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    {u : U} {v : V} (huv : (u, v) ∈ interior (dom K))
    (bU : Module.Basis ιU ℝ U) (bV : Module.Basis ιV ℝ V)
    (hpartial₁ :
      ∀ i : ιU, LineDifferentiableAt ℝ (uncurry K).realBranch (u, v) (bU i, 0))
    (hpartial₂ :
      ∀ j : ιV, LineDifferentiableAt ℝ (uncurry K).realBranch (u, v) (0, bV j)) :
    (uncurry K).HasLinearDirectionalDerivativeAt (u, v) :=
  hasLinearDirectionalDerivativeAt_of_mem_interior_dom_of_lineDifferentiableAt_basis
    hK_shape huv (bU.prod bV)
      (fun ij ↦ by
        cases ij
        · rename_i i
          simpa [Module.Basis.prod_apply, Function.comp] using hpartial₁ i
        · rename_i j
          simpa [Module.Basis.prod_apply, Function.comp] using hpartial₂ j)

end

end Bifunction

/-! ### Theorem_35_8 (from Chap07) -/
noncomputable section

universe u v

namespace Bifunction

open scoped Rockafellar

section

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 35.8 identifies differentiability of a concave-convex saddle-function at
  a point with uniqueness of its saddle subgradient there.
- `core/canonical`: the theorem surface is stated on the canonical strong-dual bridge owner
  `Bifunction.subdifferentialAtDual`; theorem surfaces use the notation
  `∂ₛ K(u, v)`, with no explicit carrier arguments.
- `bridge/view`: the codomain lift from a finite-valued `K : U → V → 𝕜` to
  `toWithBotTop K : U → V → WithBotTop 𝕜` is the only bridge used for the
  subdifferential owner.

Domain-style sampling used here:

- `Function.differentiableAt_iff_existsUnique_mem_subdifferentialAt` and
  `Function.hasLinearDirectionalDerivativeAt_iff_existsUnique_mem_subdifferentialAt` from
  `Theorem_25_2`;
- `Bifunction.subdifferentialAt` from `Text_35_6_3`
  (with `Text_35_6_4` as the strong-dual bridge);
- `Bifunction.subdifferential1At` and `Bifunction.subdifferential2At` from
  `Text_35_5_1` and `Text_35_5_2`.

Primitive data vs derived API:
- primitive source data: a finite-valued concave-convex saddle-function `K : U → V → 𝕜`;
- primitive owner bridge data: the canonical codomain lift `toWithBotTop K`;
- derived API: product-singleton identification of the lifted saddle subdifferential
  by the canonical
  first and second Fréchet derivatives, and the converse differentiability criterion from
  uniqueness of that owner.
-/

-- Proof sketch: apply the Chapter 25 singleton-subdifferential criterion to the two slices of the
-- finite-valued `K`, then read the saddle subdifferential as the pairing-level product owner
-- specialized to strong duals via `∂ₛ (toWithBotTop K)(u, v)`.
/-- Theorem 35.8 (1): for a concave-convex finite-valued saddle-function `K : U → V → 𝕜`, if
`Function.uncurry K` is differentiable at `(u, v)`, then the saddle subdifferential of its
canonical codomain lift `toWithBotTop K` is the product of
the singleton first and second partial subdifferentials determined by the Fréchet derivatives of
the two slices at `(u, v)`. -/
theorem subdifferentialAt_eq_prod_singleton_fderiv_of_differentiableAt
    {K : U → V → 𝕜} (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 (toWithBotTop K))
    {u : U} {v : V}
    (hdiff : DifferentiableAt 𝕜 (Function.uncurry K) (u, v)) :
    ∂ₛ (toWithBotTop K)(u, v) =
      {fderiv 𝕜 (fun u' ↦ K u' v) u} ×ˢ {fderiv 𝕜 (K u) v} := sorry

variable [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 V]

-- Proof sketch: uniqueness of `∂ₛ (toWithBotTop K)(u, v)` means
-- uniqueness of the first and second partial dual subgradients at `(u, v)` for the lifted owner
-- `toWithBotTop K`. Any interior/slice bridge data needed by one-variable Chapter 25 converses are
-- derived internally from the concave-convex hypotheses, and separate differentiability is then
-- upgraded to differentiability on the product.
/-- Theorem 35.8 (2): conversely, if a concave-convex saddle-function has a unique saddle
subgradient at `(u, v)` for the lifted owner `toWithBotTop K`, then `Function.uncurry K` is
differentiable at `(u, v)`. -/
theorem differentiableAt_uncurry_of_existsUnique_mem_subdifferentialAt
    {K : U → V → 𝕜} (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 (toWithBotTop K))
    {u : U} {v : V}
    (hsub : ∃! p, p ∈ ∂ₛ (toWithBotTop K)(u, v)) :
    DifferentiableAt 𝕜 (Function.uncurry K) (u, v) := sorry

-- Proof sketch: combine the forward singleton-product identification with the converse
-- uniqueness-to-differentiability implication to expose the source theorem directly as an iff
-- on the pairing-level owner specialized to strong duals.
/-- Canonical iff form of Theorem 35.8: for a finite-valued concave-convex saddle-function
`K : U → V → 𝕜`, differentiability of `Function.uncurry K` at `(u, v)` is equivalent to
uniqueness of the lifted saddle subgradient owner
`∂ₛ (toWithBotTop K)(u, v)`. -/
theorem differentiableAt_uncurry_iff_existsUnique_mem_subdifferentialAt
    {K : U → V → 𝕜} (hK_shape : SaddleFunction.IsConcaveConvex 𝕜 (toWithBotTop K))
    {u : U} {v : V} :
    DifferentiableAt 𝕜 (Function.uncurry K) (u, v) ↔
      ∃! p, p ∈ ∂ₛ (toWithBotTop K)(u, v) := by
  constructor
  · intro hdiff
    refine ⟨(fderiv 𝕜 (fun u' ↦ K u' v) u, fderiv 𝕜 (K u) v), ?_, ?_⟩
    · have hs :
        ∂ₛ (toWithBotTop K)(u, v) =
          {fderiv 𝕜 (fun u' ↦ K u' v) u} ×ˢ {fderiv 𝕜 (K u) v} :=
        subdifferentialAt_eq_prod_singleton_fderiv_of_differentiableAt
          (K := K) hK_shape hdiff
      rw [hs]
      simp
    · intro p hp
      have hs :
          ∂ₛ (toWithBotTop K)(u, v) =
            {fderiv 𝕜 (fun u' ↦ K u' v) u} ×ˢ {fderiv 𝕜 (K u) v} :=
          subdifferentialAt_eq_prod_singleton_fderiv_of_differentiableAt
            (K := K) hK_shape hdiff
      rw [hs] at hp
      rcases hp with ⟨hp₁, hp₂⟩
      exact Prod.ext (by simpa using hp₁) (by simpa using hp₂)
  · intro hsub
    exact differentiableAt_uncurry_of_existsUnique_mem_subdifferentialAt hK_shape hsub

end

end Bifunction
