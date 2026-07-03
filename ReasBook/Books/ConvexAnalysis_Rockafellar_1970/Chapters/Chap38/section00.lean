import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_38_0_1 (from Chap08) -/
noncomputable section

universe u v

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v} {𝕜 : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: the opening definition of §38 introduces the addition-like operation
  `F₁ D F₂` on bifunctions, obtained by taking infimal convolution in the second variable while
  the first variable is held fixed.
- `core/canonical`: the chapter owner is `infimal_convolution` / `□` on one-variable functions;
  the bifunction operation is the direct slice expression `fun u ↦ F₁ u □ F₂ u`.
- `bridge/view`: Section 38 keeps a source-facing notation `D`, but its implementation layer is
  exactly this slice-level canonical owner expression.

Domain-style sampling used here:
- `infimal_convolution` / `□` from `Chap01.Text_5_4_0`;
- `infimal_convolution_apply` from the same owner layer;
- `Bifunction.perturbationFunction` from `Chap06.Definition_6_29_1` as the existing project
  pattern for a source-facing bifunction owner built directly from an indexed-infimum function
  construction.

Primitive data vs derived API:
- primitive source data: the bifunctions `F₁` and `F₂`;
- primitive source-facing owner: `infimalConvolution`, written `F₁ D F₂`;
- derived API: the pointwise evaluation formula and the uncurried identity companion.

Layer target: `source-facing`.
-/

section Owner

variable [ConditionallyCompleteLinearOrder 𝕜] [Add 𝕜]
variable [Add X]

/-- Definition 38.0.1: the infimal convolution of two bifunctions is obtained by taking, for each
`u`, the infimal convolution of the functions `F₁ u` and `F₂ u` in the second variable. The
textbook proper-convex hypotheses belong to later theorems, not to the primitive definition of
this source-facing owner. -/
abbrev infimalConvolution (F₁ F₂ : U → X → WithBotTop 𝕜) : U → X → WithBotTop 𝕜 :=
  fun u ↦ F₁ u □ F₂ u

scoped[Rockafellar] infixl:70 " D " => Bifunction.infimalConvolution

/-- The Section 38 bifunction operation is exactly the uncurried graph function built from the
slice-level owner expression `fun u ↦ F₁ u □ F₂ u`. -/
@[simp] theorem uncurry_infimalConvolution
    (F₁ F₂ : U → X → WithBotTop 𝕜) :
    Function.uncurry (F₁ D F₂) =
      Function.uncurry (fun u ↦ F₁ u □ F₂ u) := by
  rfl

end Owner

section SubtractionFormula

variable [ConditionallyCompleteLinearOrder 𝕜] [Add 𝕜]
variable [AddCommGroup X]

/-- Evaluating `F₁ D F₂` at `(u, x)` gives the infimum of `F₁ u y + F₂ u (x - y)` over all
`y`. -/
@[simp] theorem infimalConvolution_apply
    (F₁ F₂ : U → X → WithBotTop 𝕜) (u : U) (x : X) :
    (F₁ D F₂) u x = ⨅ y : X, F₁ u y + F₂ u (x - y) := by
  change ((F₁ u) □ (F₂ u)) x = ⨅ y : X, F₁ u y + F₂ u (x - y)
  exact infimal_convolution_apply (F₁ u) (F₂ u) x

end SubtractionFormula

end

end Bifunction

/-! ### Proposition_38_0_2 (from Chap08) -/
noncomputable section

universe u v r

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.0.2 identifies the adjoint bifunction of the singleton-graph
  indicator equation with the singleton-graph concave-indicator equation attached to a dual
  companion map.
- `core/canonical`: this equation is already owned by the Chapter 33 theorem
  `pairingEquation_graphIndicator_of_isPairingCompanion`.
- `bridge/view`: map compatibility is represented by the Chapter 33 owner
  `IsPairingCompanion`.

Primary mathematical domain:
- bifunction adjoints and singleton-graph indicator kernels of maps.

Domain-style sampling used here:
- `graphIndicator` and `graphConcaveIndicator` from `Chap06.Definition_6_29_9`;
- `IsPairingCompanion` and
  `pairingEquation_graphIndicator_of_isPairingCompanion` from `Chap07.Lemma33_0_30`;
- the pairing notations `⟪·, ·⟫ᶠ`, `⟪·, ·⟫ᶜ`, and `⟪·, ·⟫ₚ`.

Primitive data vs derived API:
- primitive source data: a map `A` and a dual companion map `Astar`;
- primitive owner expression:
  `pairingEquation_graphIndicator_of_isPairingCompanion`;
- derived API: the source-labeled proposition theorem below.

Layer target:
- `source-facing` as a thin source-label bridge over the canonical Chapter 33 owner theorem.
-/

section PairingEquation

variable {𝕜 : Type r} {U : Type u} {X : Type v} {UStar : Type u} {XStar : Type v}
variable [AddGroup 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

local instance : HasPairing UStar U 𝕜 := HasPairing.swap

-- Proof sketch: Proposition 38.0.2 is exactly the Chapter 33 singleton-graph pairing equation
-- under the global companion hypothesis, so this file keeps only a source-labeled bridge.
/-- Proposition 38.0.2: if `Astar` is a pairing companion of `A`, then the singleton-graph
pairing equation holds at every point. -/
theorem proposition_38_0_2
    (A : U → X) (Astar : XStar → UStar)
    (hA : IsPairingCompanion A Astar)
    (u : U) (xStar : XStar) :
    ⟪graphIndicator 𝕜 A u, xStar⟫ᶠ = ⟪u, graphConcaveIndicator 𝕜 Astar xStar⟫ᶜ := by
  exact pairingEquation_graphIndicator_of_isPairingCompanion A Astar hA u xStar

end PairingEquation

end Bifunction

/-! ### Proposition_38_0_3 (from Chap08) -/
noncomputable section

open LinearMap
open scoped Rockafellar

universe u v

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.0.3 identifies the inverse and inverse-adjoint of the convex
  indicator bifunction attached to a nonsingular linear transformation.
- `core/canonical`: the existing owners are `graphIndicator`, `graphConcaveIndicator`,
  inverse notation `F _*`, and `concaveAdjoint`; the linear-algebra owner for the adjoint map
  is `LinearMap.adjoint`.
- `bridge/view`: the source phrase "nonsingular linear transformation" is rendered by the
  canonical Lean owner `LinearEquiv`, and the source expression `(A⁻¹)^* = (A^*)⁻¹` is recorded
  on the indicator side through the map `adjoint (A.symm : F →ₗ[ℝ] E)`.

Domain-style sampling used here:
- inverse notation `F _*` from `Chap07.Definition_36_4_1`;
- `graphIndicator`, `graphConcaveIndicator`, and the pointwise pairing equation for those owners
  from `Chap07.Lemma33_0_30`;
- `concaveAdjoint` from the Chapter 6 concave-bifunction-adjoint owner layer;
- `LinearMap.adjoint` as the canonical inner-product-space adjoint.

Primitive data vs derived API:
- primitive input data: an invertible linear map `A`;
- primitive owner expressions: `graphIndicator ℝ A`, `(graphIndicator ℝ A) _*`, and the
  concave-adjoint owner applied to that inverse;
- derived API: the identification of the inverse with the concave indicator of `A.symm`, and the
  identification of the concave adjoint of that inverse with the convex indicator of
  `adjoint (A.symm : F →ₗ[ℝ] E)`.

Layer target:
- `source-facing` for the two indicator-bifunction equalities;
- `bridge/view` only in the passage from the source's Euclidean adjoint notation to
  `LinearMap.adjoint`.
-/

section InverseClause

variable {𝕜 : Type*} {E : Type u} {F : Type v}
variable [Ring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]

-- Proof sketch: unfold the inverse notation `F _*`, `graphIndicator`, and
-- `graphConcaveIndicator`. The singleton condition `x = A u` is equivalent to `u = A.symm x`
-- because `A` is a `LinearEquiv`, so both sides reduce to the same pointwise indicator formula.
/-- Proposition 38.0.3 (1): the inverse of the convex indicator bifunction of a nonsingular linear
transformation `A` is the concave indicator bifunction of `A⁻¹`. -/
theorem inverse_graphIndicator_eq_graphConcaveIndicator_symm
    (A : E ≃ₗ[𝕜] F) :
    (graphIndicator 𝕜 A) _* = graphConcaveIndicator 𝕜 A.symm := by
  funext x u
  have hA : x = A u ↔ u = A.symm x := by
    simpa [eq_comm] using
      (A.toEquiv.apply_eq_iff_eq_symm_apply : A u = x ↔ u = A.symm x)
  by_cases h : x = A u
  · have hu : u = A.symm x := hA.mp h
    have hxmem : x ∈ ({A u} : Set F) := by
      simpa [Set.mem_singleton_iff] using h
    have humem : u ∈ ({A.symm x} : Set E) := by
      simpa [Set.mem_singleton_iff] using hu
    rw [inverse_apply]
    simp [graphIndicator, graphConcaveIndicator, hxmem, humem]
  · have hu : u ≠ A.symm x := by
      intro hu
      exact h (hA.mpr hu)
    have hxnot : x ∉ ({A u} : Set F) := by
      simpa [Set.mem_singleton_iff] using h
    have hunot : u ∉ ({A.symm x} : Set E) := by
      simpa [Set.mem_singleton_iff] using hu
    rw [inverse_apply]
    simp [graphIndicator, graphConcaveIndicator, hxnot, hunot]

end InverseClause

section AdjointClause

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

local instance : Neg (WithBotTop ℝ) := WithBotTop.instNeg
local instance : InvolutiveNeg (WithBotTop ℝ) := WithBotTop.instInvolutiveNeg

-- Proof sketch: first rewrite `inverse (graphIndicator ℝ A)` using the preceding inverse-indicator
-- identification, then rewrite the adjoint branch via the hypothesis `hAdj`. In the inner-product
-- self-dual setting this yields the convex indicator bifunction of `(A⁻¹)^*`, which is the
-- canonical Lean rendering of the source map `(A^*)⁻¹`.
/-- Proposition 38.0.3 (2), conditional bridge form: assuming the adjoint-side singleton-graph
identification `hAdj`, the concave adjoint of the inverse indicator bifunction is the convex
indicator bifunction of `(A⁻¹)^*`, equivalently of `(A^*)⁻¹`. -/
theorem concaveAdjoint_inverse_graphIndicator_eq_graphIndicator_adjoint_symm
    (A : E ≃ₗ[ℝ] F)
    (hAdj :
      Bifunction.adjoint (XStar := F) (UStar := E) (graphIndicator ℝ A) =
        graphConcaveIndicator ℝ (LinearMap.adjoint (A : E →ₗ[ℝ] F))) :
    concaveAdjoint E F ((graphIndicator ℝ A) _*) =
      graphIndicator ℝ (LinearMap.adjoint (A.symm : F →ₗ[ℝ] E)) := by
  let Aadj : E ≃ₗ[ℝ] F :=
    { toLinearMap := LinearMap.adjoint (A.symm : F →ₗ[ℝ] E)
      invFun := LinearMap.adjoint (A : E →ₗ[ℝ] F)
      left_inv := by
        intro x
        have hcomp :
            (LinearMap.adjoint (A : E →ₗ[ℝ] F)) ∘ₗ
              LinearMap.adjoint (A.symm : F →ₗ[ℝ] E) = LinearMap.id := by
          simpa using
            (LinearMap.adjoint_comp (A.symm : F →ₗ[ℝ] E) (A : E →ₗ[ℝ] F)).symm
        simpa using congrArg (fun T : E →ₗ[ℝ] E ↦ T x) hcomp
      right_inv := by
        intro y
        have hcomp :
            (LinearMap.adjoint (A.symm : F →ₗ[ℝ] E)) ∘ₗ
              LinearMap.adjoint (A : E →ₗ[ℝ] F) = LinearMap.id := by
          simpa using
            (LinearMap.adjoint_comp (A : E →ₗ[ℝ] F) (A.symm : F →ₗ[ℝ] E)).symm
        simpa using congrArg (fun T : F →ₗ[ℝ] F ↦ T y) hcomp }
  have hAadj :
      (graphIndicator ℝ Aadj) _* = graphConcaveIndicator ℝ Aadj.symm :=
    inverse_graphIndicator_eq_graphConcaveIndicator_symm Aadj
  have hInv :
      (graphConcaveIndicator ℝ (LinearMap.adjoint (A : E →ₗ[ℝ] F))) _* =
        graphIndicator ℝ (LinearMap.adjoint (A.symm : F →ₗ[ℝ] E)) := by
    have hInv' :
        graphIndicator ℝ (LinearMap.adjoint (A.symm : F →ₗ[ℝ] E)) =
          (graphConcaveIndicator ℝ (LinearMap.adjoint (A : E →ₗ[ℝ] F))) _* := by
      have hInv'' :
          (graphIndicator ℝ Aadj) _* _* =
            (graphConcaveIndicator ℝ Aadj.symm) _* :=
        congrArg (fun H => H _*) hAadj
      have hInv''' : (graphIndicator ℝ Aadj) _* _* = graphIndicator ℝ Aadj :=
        inverse_inverse (graphIndicator ℝ Aadj)
      calc
        graphIndicator ℝ (LinearMap.adjoint (A.symm : F →ₗ[ℝ] E)) = graphIndicator ℝ Aadj := by
          simp [Aadj]
        _ = (graphIndicator ℝ Aadj) _* _* := by
          exact hInv'''.symm
        _ = (graphConcaveIndicator ℝ Aadj.symm) _* := hInv''
        _ = (graphConcaveIndicator ℝ (LinearMap.adjoint (A : E →ₗ[ℝ] F))) _* := by
          simp [Aadj]
    exact hInv'.symm
  have hComm :
      concaveAdjoint E F ((graphIndicator ℝ A) _*) =
        ((adjoint (XStar := F) (UStar := E) (graphIndicator ℝ A)) _*) :=
    concaveAdjoint_inverse_eq_inverse_adjoint (graphIndicator ℝ A)
  calc
    concaveAdjoint E F ((graphIndicator ℝ A) _*) =
        ((adjoint (XStar := F) (UStar := E) (graphIndicator ℝ A)) _*) := hComm
    _ = (graphConcaveIndicator ℝ (LinearMap.adjoint (A : E →ₗ[ℝ] F))) _* := by rw [hAdj]
    _ = graphIndicator ℝ (LinearMap.adjoint (A.symm : F →ₗ[ℝ] E)) := hInv

end AdjointClause

end Bifunction

/-! ### Definition_38_0_4 (from Chap08) -/
noncomputable section

universe u v

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: the unnumbered definition before Theorem 38.4 introduces the image `Ff` of a
  function `f` under a bifunction `F`, namely `x ↦ inf_u (f u + F u x)`.
- `core/canonical`: the existing Chapter 6 owner for pointwise infima in the second variable is
  `Bifunction.perturbationFunction`.
- `bridge/view`: the new Chapter 38 source object is exactly the perturbation function of the
  bifunction `(x, u) ↦ f u + F u x`.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` and its pointwise formulas
  `perturbationFunction_apply_eq_sInf_range` / `perturbationFunction_apply` from
  `Chap06.Definition_6_29_1`;
- `Bifunction.lagrangian` from `Chap07.Theorem_36_5`, another source-facing owner defined as a
  thin bridge to an existing one-variable conjugation owner;
- `Function.linearImage` from `Chap01.Theorem_5_7`, the more specific image-of-a-function owner
  for linear transformations that this Chapter 38 object generalizes.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → WithBotTop α` and a function
  `f : U → WithBotTop α`, at the codomain-generic additive/lattice layer;
- primitive source-facing owner introduced here: `Bifunction.image F f`;
- derived API: the bridge to `perturbationFunction`, the `sInf`-of-range formula, and the indexed
  `iInf` formula.

Layer target: `source-facing`. The Chapter 38 image operation is a genuine new source object, but
its implementation reuses the existing perturbation-function owner instead of duplicating another
pointwise-infimum definition.

Notation decision: no new notation is introduced. The raw owner name `image` is short and stable,
while the textbook juxtaposition `Ff` does not translate into an inference-stable Lean notation.
-/

section

variable {U : Type u} {X : Type v} {α : Type*}
variable [ConditionallyCompleteLattice α] [Add α]

/-- Definition 38.0.4: the image of a function `f` under a bifunction `F`, defined by
`x ↦ inf_u (f u + F u x)`. -/
abbrev image (F : U → X → WithBotTop α) (f : U → WithBotTop α) : X → WithBotTop α :=
  perturbationFunction (fun x u ↦ f u + F u x)

/-- Evaluating `image F f` at `x` gives the infimum of the range of the kernel
`u ↦ f u + F u x`. -/
@[simp] theorem image_apply_eq_sInf_range
    (F : U → X → WithBotTop α) (f : U → WithBotTop α) (x : X) :
    image F f x = sInf (Set.range fun u ↦ f u + F u x) := by
  rfl

/-- Evaluating `image F f` at `x` is the indexed infimum `inf_u (f u + F u x)`. -/
@[simp] theorem image_apply
    (F : U → X → WithBotTop α) (f : U → WithBotTop α) (x : X) :
    image F f x = ⨅ u, (f u + F u x) := by
  simpa [image] using perturbationFunction_apply (fun x u ↦ f u + F u x) x

end

end Bifunction
