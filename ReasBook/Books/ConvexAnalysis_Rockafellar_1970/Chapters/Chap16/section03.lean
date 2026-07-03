import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_16_3_1_1 (from Chap03) -/
noncomputable section

universe u v w z s

section

open scoped Rockafellar

variable {α : Type s} [ConditionallyCompleteLattice α]
variable {E : Type u} {F : Type v} {EStar : Type w} {FStar : Type z}
variable [HasPairing FStar F α] [HasPairing EStar E α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.3.1.1 identifies the support function of the image `AC`
  with the support function of `C` precomposed with the transpose/dual map `A*`.
- `core/canonical`: the owner abstractions are the chapter support function `δᵛ(· | C)` and an
  explicit dual-side map `Astar` related to `A` by a pairing-compatibility identity.
- `bridge/view`: the source's transpose `A*` is represented abstractly by `Astar` at the pairing
  layer.

Domain-style sampling used here:
- `supportFunction` and `supportFunction_def`;
- `iSup_le` and `le_iSup` on the support-function supremum;
- a dual-map pairing compatibility hypothesis.

Primitive data vs derived API:
- primitive inputs: `A`, `Astar`, the pairing compatibility relation, and the set `C`;
- derived API: the support-function identity, obtained by rewriting the defining supremum along
  the set image and then replacing the pairing term using compatibility.

Layer target: `source-facing`, stated at the pairing owner layer.

Semantic note: the displayed identity already holds for arbitrary subsets `C`; the textbook's
convexity hypothesis is redundant and is therefore omitted.

Codomain note: the support-function statement is exposed at the codomain-general
`WithBotTop α` layer rather than hard-wiring `EReal` in the primary owner theorem.
-/

-- Proof sketch: unfold both support functions. For fixed `yStar`, reindex the supremum over
-- `A '' C` through `Set.image`; then rewrite each pairing value `⟪yStar, A x⟫` as
-- `⟪Astar yStar, x⟫` by the compatibility hypothesis.
/-- Corollary 16.3.1.1 at the pairing owner layer: if `A` and `Astar` satisfy
`⟪yStar, A x⟫ = ⟪Astar yStar, x⟫`, then the support function of `A '' C` equals the support
function of `C` precomposed with `Astar`. -/
theorem supportFunction_image_eq_supportFunction_comp
    (A : E → F) (Astar : FStar → EStar)
    (hA : ∀ x : E, ∀ yStar : FStar, (⟪yStar, A x⟫ₚ : α) = ⟪Astar yStar, x⟫ₚ)
    (C : Set E) :
    (δᵛ[WithBotTop α](· | A '' C)) = (δᵛ[WithBotTop α](· | C)) ∘ Astar := by
  ext yStar
  rw [Function.comp_apply, supportFunction_def, supportFunction_def]
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, hxC, rfl⟩
    calc
      (⟪yStar, A x⟫ₚ : WithBotTop α) = ⟪Astar yStar, x⟫ₚ := by
        exact congrArg (fun r : α ↦ (r : WithBotTop α)) (hA x yStar)
      _ ≤ ⨆ z : C, (⟪Astar yStar, (z : E)⟫ₚ : WithBotTop α) :=
        le_iSup (fun z : C ↦ (⟪Astar yStar, (z : E)⟫ₚ : WithBotTop α)) ⟨x, hxC⟩
  · refine iSup_le ?_
    intro x
    calc
      (⟪Astar yStar, (x : E)⟫ₚ : WithBotTop α) = ⟪yStar, A (x : E)⟫ₚ := by
        exact congrArg (fun r : α ↦ (r : WithBotTop α)) (hA (x : E) yStar).symm
      _ ≤ ⨆ y : A '' C, (⟪yStar, (y : F)⟫ₚ : WithBotTop α) :=
        le_iSup (fun y : A '' C ↦ (⟪yStar, (y : F)⟫ₚ : WithBotTop α))
          ⟨A (x : E), ⟨(x : E), x.2, rfl⟩⟩

end

/-! ### Corollary_16_3_1_2 (from Chap03) -/
noncomputable section

universe u v

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜] [IsOrderedAddMonoid 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [ClosedIciTopology 𝕜]
variable {E : Type u} {F : Type v}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 F]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable [HasLinearPairing F F 𝕜] [HasContinuousPairing F F 𝕜]
variable [HasPairingSwap E E 𝕜] [HasPairingSwap F F 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.3.1.2 identifies the support function of the inverse image
  `A⁻¹ (closure D)` with the closure of the dual-side image `A* δ*(· | closure D)`.
- `core/canonical`: the owner abstractions are the project support function `supportFunction`, the
  lower-semicontinuous closure `lowerSemicontinuousHull`, the function image operator
  `Function.linearImage`, the set closure `closure`, and an explicit dual map `Astar`.
- `bridge/view`: Rockafellar's `δ*(· | D)` is rendered by `supportFunction D`, and the source's
  `cl (A* δ*(· | closure D))` is rendered by
  `lowerSemicontinuousHull (Astar ◁ supportFunction D)`, using closure-invariance of support.

Domain-style sampling used here:
- `supportFunction` and the pairing-symmetric indicator/support bridge from Text 13.1.4;
- `indicatorFunction_isConvex_iff` from `Chap01.Remark_4_8_1`;
- `lowerSemicontinuousHull_indicator_eq_indicator_closure` from Text 7.0.14;
- `convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_of_convex`
  from Theorem 16.3.2;
- `intrinsicClosure_eq_closure` for the intrinsic-closure pairing bridge.

Primitive data vs derived API:
- primitive inputs: a primal map `A : E → F`, a dual map `Astar : F → E`, a pairing
  compatibility identity, a set `D ⊆ F`, and the convexity hypothesis on `D`;
- derived API: the support-function identity itself, stated directly at the pairing owner layer.

Layer target: `source-facing`, expressed through the canonical project owners.

Ambient note: the upstream owner theorem `Theorem_16_3_2` already has a pairing-layer primary
statement with an explicit dual map. This file keeps that pairing-level owner surface.

Topology note: this first section keeps ambient `closure` as primary because the available pairing
assumptions here are only topological-module assumptions; replacing `closure` by
`intrinsicClosure 𝕜` requires stronger normed/metric hypotheses to use
`intrinsicClosure_eq_closure`. A scalar-generic intrinsic-closure bridge is added below at the
same pairing owner layer.
-/

-- Theorem 16.3.2 is applied to `indicatorFunction D`.
-- Convexity of that indicator comes from `indicatorFunction_isConvex_iff`.
-- Text 13.1.5 identifies `cl(δ(· | D))` with `δ(· | closure D)`, and the
-- pairing-symmetric indicator/support bridges rewrite both conjugate terms.
/-- Corollary 16.3.1.2 at the pairing owner layer: for primal/dual maps `A` and `Astar` with
`⟪Astar y, x⟫ = ⟪y, A x⟫`, and a convex set `D ⊆ F`, the support function of
`A ⁻¹' closure D` equals the lower-semicontinuous closure of the `Astar`-image of the support
function of `D`. -/
theorem supportFunction_preimage_closure_eq_lowerSemicontinuousHull_linearImage_of_pairing
    (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E)
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : 𝕜) = ⟪y, A x⟫ₚ)
    (D : Set F) (hD : Convex 𝕜 D) :
    (δᵛ(· | A ⁻¹' closure D) : E → WithBotTop 𝕜) =
      cl(Astar ◁ (δᵛ(· | D) : F → WithBotTop 𝕜)) := by
  have hcore :
      ((cl((δ[𝕜](· | D))) ∘ A)⋆ : E → WithBotTop 𝕜) =
        cl(Astar ◁ (((δ[𝕜](· | D))⋆ : F → WithBotTop 𝕜))) := by
    exact
      convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_of_convex
        (A := A) (Astar := Astar) (hAstar := hAstar) (g := (δ[𝕜](· | D)))
        ((indicator_isConvex_iff (𝕜 := 𝕜) (α := 𝕜) D).2 hD)
  have hleft :
      ((cl((δ[𝕜](· | D))) ∘ A)⋆ : E → WithBotTop 𝕜) =
        (δᵛ[WithBotTop 𝕜](· | A ⁻¹' closure D) : E → WithBotTop 𝕜) := by
    have hcl_ind :
        (cl((δ[𝕜](· | D))) : F → WithBotTop 𝕜) =
          (δ[𝕜](· | closure D) : F → WithBotTop 𝕜) := by
      simpa using
        (lowerSemicontinuousHull_indicator_eq_indicator_closure
          (X := F) (𝕜 := 𝕜) D)
    have hcl_comp :
        (cl((δ[𝕜](· | D))) ∘ A) = (δ[𝕜](· | A ⁻¹' closure D)) := by
      funext x
      exact congrFun hcl_ind (A x)
    calc
      ((cl((δ[𝕜](· | D))) ∘ A)⋆ : E → WithBotTop 𝕜) =
          ((δ[𝕜](· | A ⁻¹' closure D))⋆ : E → WithBotTop 𝕜) := by
            exact
              congrArg (fun f : E → WithBotTop 𝕜 ↦ (f⋆ : E → WithBotTop 𝕜)) hcl_comp
      _ = (δᵛ[WithBotTop 𝕜](· | A ⁻¹' closure D) : E → WithBotTop 𝕜) := by
            simpa using
              (convexConjugate_indicatorFunction_eq_supportFunction
                (E := E) (EStar := E) (α := 𝕜) (C := A ⁻¹' closure D))
  have hright :
      cl(Astar ◁ (((δ[𝕜](· | D))⋆ : F → WithBotTop 𝕜))) =
        cl(Astar ◁ (δᵛ[WithBotTop 𝕜](· | D))) := by
    simpa using
      congrArg (fun f : F → WithBotTop 𝕜 ↦ cl(Astar ◁ f))
        (convexConjugate_indicatorFunction_eq_supportFunction
          (E := F) (EStar := F) (α := 𝕜) (C := D))
  exact hleft.symm.trans (hcore.trans hright)

end

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [ClosedIciTopology 𝕜]
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable [HasLinearPairing F F 𝕜] [HasContinuousPairing F F 𝕜]
variable [HasPairingSwap E E 𝕜] [HasPairingSwap F F 𝕜]

/-- Intrinsic-closure bridge of Corollary 16.3.1.2 at the pairing owner layer: under the
finite-dimensional normed hypotheses needed for `intrinsicClosure_eq_closure`, the same support
formula can be read with `intrinsicClosure 𝕜 D` on the preimage side. -/
theorem supportFunction_preimage_intrinsicClosure_eq_lowerSemicontinuousHull_linearImage_of_pairing
    (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E)
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : 𝕜) = ⟪y, A x⟫ₚ)
    (D : Set F) (hD : Convex 𝕜 D) :
    (δᵛ(· | A ⁻¹' intrinsicClosure 𝕜 D) : E → WithBotTop 𝕜) =
      cl(Astar ◁ (δᵛ(· | D) : F → WithBotTop 𝕜)) := by
  calc
    (δᵛ(· | A ⁻¹' intrinsicClosure 𝕜 D) : E → WithBotTop 𝕜) =
        (δᵛ(· | A ⁻¹' closure D) : E → WithBotTop 𝕜) := by
          simp
    _ = cl(Astar ◁ (δᵛ(· | D) : F → WithBotTop 𝕜)) := by
      simpa using
        (supportFunction_preimage_closure_eq_lowerSemicontinuousHull_linearImage_of_pairing
          A Astar hAstar D hD)

end

/-! ### Corollary_16_3_1_3 (from Chap03) -/
noncomputable section

universe u v

section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem exists_mem_riDom_indicator_of_exists_mem_intrinsicInterior
    (A : E →ₗ[ℝ] F) {D : Set F}
    (hri : ∃ x : E, A x ∈ intrinsicInterior ℝ D) :
    ∃ x : E, A x ∈ intrinsicInterior ℝ dom(indicatorFunction D) := by
  simpa [effectiveDomain_indicatorFunction] using hri

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.3.1.3 removes the closure from Corollary 16.3.1.2 for inverse
  images of a convex set `D` under a linear map `A`, assuming some point of the range of `A`
  meets `ri D`, and then records the fiberwise infimum formula together with attainment.
- `core/canonical`: the owner declarations are the chapter support-function notation `δᵛ(· | D)`,
  the linear-image notation `◁`, `LinearMap.adjoint`, and the relative-interior notation
  `riDom(·)`.
- `bridge/view`: Rockafellar's `δ*(· | D)` is rendered by `δᵛ(· | D)`, the inverse image `A⁻¹ D`
  by the set preimage `A ⁻¹' D`, and the adjoint-side fiber infimum by
  `Function.linearImage_eq_sInf_image`.

Domain-style sampling used here:
- `supportFunction_preimage_closure_eq_lowerSemicontinuousHull_linearImage_adjoint`
  from Corollary 16.3.1.2;
- `convexConjugate_comp_linearMap_eq_linearImage_adjoint_of_exists_mem_intrinsicInterior_dom`,
  `convexConjugate_comp_linearMap_apply_eq_sInf_image_conjugate_of_exists_mem_intrinsicInterior_dom`,
  and
  `convexConjugate_comp_linearMap_apply_eq_top_or_exists_adjoint_eq_and_eq_conjugate_of_exists_mem_intrinsicInterior_dom`
  from Theorem 16.3.3;
- the support-function/indicator bridge
  `convexConjugate_indicatorFunction_eq_supportFunction`.

Primitive data vs derived API:
- primitive inputs: a linear map `A : E → F`, a convex set `D ⊆ F`, and a witness
  `∃ x, A x ∈ ri D`;
- derived API: the closure-free support-function identity, its pointwise infimum formula, and the
  attained-or-vacuous alternative.

Layer target: `source-facing`, stated directly in the canonical chapter notation.

Ambient note: the owner theorems sampled above already live on arbitrary finite-dimensional real
inner-product spaces, so this corollary is refined to that same canonical ambient level instead of
reintroducing the coordinate model `EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)`.
-/

-- Proof sketch: specialize Theorem 16.3.3 to the indicator function `indicatorFunction D`.
-- Convexity of `D` gives the needed convexity of that indicator, and the effective domain of the
-- indicator is exactly `D`, so the hypothesis is already the relative-interior condition required
-- there. The support-function/indicator bridge then rewrites the conjugate identities into the
-- displayed support-function identity, which is exactly Corollary 16.3.1.2 with the closure
-- operation removed.
/-- Corollary 16.3.1.3, in canonical ambient form: for a real linear map `A : E → F` between
finite-dimensional inner-product spaces and a convex set `D ⊆ F`, if some `A x` lies in `ri D`,
then the closure in Corollary 16.3.1.2 is unnecessary, so
`δ*(· | A⁻¹ D) = A* δ*(· | D)`, rendered here as `(δᵛ(· | A ⁻¹' D)) = A.adjoint ◁ (δᵛ(· | D))`.
The textbook Euclidean statement is recovered by specializing `E = R^n` and `F = R^m`. -/
theorem supportFunction_preimage_eq_linearImage_adjoint_supportFunction_of_exists_mem_intrinsicInterior
    (A : E →ₗ[ℝ] F) (D : Set F) (hD : Convex ℝ D)
    (hri : ∃ x : E, A x ∈ intrinsicInterior ℝ D) :
    (δᵛ(· | A ⁻¹' D)) = A.adjoint ◁ (δᵛ(· | D)) := by
  simpa [show indicatorFunction D ∘ A = indicatorFunction (A ⁻¹' D) by rfl,
    convexConjugate_indicatorFunction_eq_supportFunction] using
    (convexConjugate_comp_linearMap_eq_linearImage_adjoint_of_exists_mem_intrinsicInterior_dom
      A (indicatorFunction D) ((indicatorFunction_isConvex_iff D).2 hD)
      (exists_mem_riDom_indicator_of_exists_mem_intrinsicInterior A hri))

-- Proof sketch: evaluate the closure-free support-function identity at `xStar`, then rewrite the
-- value of `Function.linearImage A.adjoint (supportFunction D)` by the owner formula
-- `Function.linearImage_eq_sInf_image`.
/-- Evaluating the closure-free support-function identity at `xStar` gives the infimum of
`δ*(· | D)` over the adjoint fiber `A* y* = xStar`. -/
theorem supportFunction_preimage_apply_eq_sInf_image_of_exists_mem_intrinsicInterior
    (A : E →ₗ[ℝ] F) (D : Set F) (hD : Convex ℝ D)
    (hri : ∃ x : E, A x ∈ intrinsicInterior ℝ D) (xStar : E) :
    δᵛ(xStar | A ⁻¹' D) =
      sInf ((δᵛ(· | D)) '' {yStar : F | A.adjoint yStar = xStar}) := by
  simpa [show indicatorFunction D ∘ A = indicatorFunction (A ⁻¹' D) by rfl,
    convexConjugate_indicatorFunction_eq_supportFunction] using
    (convexConjugate_comp_linearMap_apply_eq_sInf_image_conjugate_of_exists_mem_intrinsicInterior_dom
      A (indicatorFunction D) ((indicatorFunction_isConvex_iff D).2 hD)
      (exists_mem_riDom_indicator_of_exists_mem_intrinsicInterior A hri) xStar)

-- Proof sketch: specialize the attained-or-vacuous clause of Theorem 16.3.3 to the indicator
-- function of `D`, then translate the resulting conjugate terms back into support functions. If
-- the adjoint fiber is empty, the infimum is vacuous and the value is `⊤`; otherwise a minimizing
-- `yStar` exists.
/-- Under the same relative-interior hypothesis, the fiberwise infimum formula for
`δ*(· | A⁻¹ D)` is either vacuous, giving `⊤`, or is attained at some `yStar` with
`A.adjoint yStar = xStar`. -/
theorem supportFunction_preimage_apply_eq_top_or_exists_adjoint_eq_and_eq_supportFunction_of_exists_mem_intrinsicInterior
    (A : E →ₗ[ℝ] F) (D : Set F) (hD : Convex ℝ D)
    (hri : ∃ x : E, A x ∈ intrinsicInterior ℝ D) (xStar : E) :
    δᵛ(xStar | A ⁻¹' D) = ⊤ ∨
      ∃ yStar : F, A.adjoint yStar = xStar ∧
        δᵛ(xStar | A ⁻¹' D) = δᵛ(yStar | D) := by
  simpa [show indicatorFunction D ∘ A = indicatorFunction (A ⁻¹' D) by rfl,
    convexConjugate_indicatorFunction_eq_supportFunction] using
    (convexConjugate_comp_linearMap_apply_eq_top_or_exists_adjoint_eq_and_eq_conjugate_of_exists_mem_intrinsicInterior_dom
      A (indicatorFunction D) ((indicatorFunction_isConvex_iff D).2 hD)
      (exists_mem_riDom_indicator_of_exists_mem_intrinsicInterior A hri) xStar)

end

/-! ### Theorem_16_3_1 (from Chap03) -/
noncomputable section

universe u v w z

section

open Function
open scoped Rockafellar

variable {E : Type u} {F : Type v} {EStar : Type w} {FStar : Type z}
variable {α : Type*}
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable [DenselyOrdered α] [NoBotOrder α] [NoTopOrder α] [Nonempty α]
variable [HasPairing E EStar α] [HasPairing F FStar α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.3.1 states that the conjugate of the image `Af` of a function `f`
  under a linear transformation is obtained by composing the conjugate `f*` with the dual-side map
  `A*`.
- `core/canonical`: the chapter owners are the image operation `A ◁ f` from Theorem 5.7 and the
  Fenchel conjugate `f⋆` from Defn 12.2.
- `bridge/view`: the duality relation is exposed directly as a pairing-side compatibility identity
  between `A` and an explicit dual map `Astar`.

Domain-style sampling used here:
- `Function.linearImage` and its scoped notation `◁` from Theorem 5.7;
- `convexConjugate` and its scoped postfix notation `⋆` from Defn 12.2;
- `HasPairing` from Chapter 1 for primal/dual evaluation;
- an explicit pairing compatibility hypothesis
  `∀ x y⋆, ⟪A x, y⋆⟫ = ⟪x, Astar y⋆⟫`.

Primitive data vs derived API:
- primitive inputs: the primal map `A`, the dual map `Astar`, the duality compatibility relation,
  and the function `f`;
- derived API: the conjugate identity itself, expressed directly as an equality of functions.

Layer target: `source-facing`, stated through the canonical chapter owners rather than by
introducing any parallel local wrapper.

Semantic note: the source presents this identity in the convex-analysis setting, but the owner-side
formula itself already makes sense for arbitrary `WithTopBot α`-valued `f`, so no extra wrapper or
auxiliary packaging is needed around the canonical statement.

Ambient note: the core owner statement only needs paired spaces and an explicit dual map satisfying
the pairing identity.
-/

-- Proof sketch: unfold `(A ◁ f)⋆` and the fiberwise definition of `A ◁ f`. For fixed `y⋆`,
-- rewrite the outer supremum over `y` and the inner infimum over the fiber `A x = y` as a single
-- supremum over `x`. Then use pairing compatibility to replace `⟪A x, y⋆⟫` by
-- `⟪x, Astar y⋆⟫`, which is exactly the defining supremum for `f⋆ (Astar y⋆)`.
/-- Theorem 16.3.1 in canonical owner form: if a primal map `A` and a dual map `Astar` satisfy
`⟪A x, y⋆⟫ = ⟪x, Astar y⋆⟫`, then the Fenchel conjugate of `A ◁ f` is `f⋆ ∘ Astar`. -/
theorem convexConjugate_linearImage_eq_comp
    (A : E → F) (Astar : FStar → EStar)
    (hA : ∀ x yStar, ⟪A x, yStar⟫ₚ = ⟪x, Astar yStar⟫ₚ)
    (f : E → WithTopBot α) :
    (A ◁ f)⋆ = f⋆ ∘ Astar := by
  ext yStar
  simp only [Function.comp_apply]
  rw [convexConjugate_eq_iSup_pairing_sub, convexConjugate_eq_iSup_pairing_sub]
  apply le_antisymm
  · refine iSup_le fun y ↦ ?_
    let s : Set (WithTopBot α) := f '' {x : E | A x = y}
    let c : WithTopBot α := ⟪y, yStar⟫ₚ
    rw [linearImage_eq_sInf_image]
    change c - sInf s ≤ ⨆ x : E, ((⟪x, Astar yStar⟫ₚ : α) : WithTopBot α) - f x
    refine (WithBotTop.le_of_forall_lt_iff_le (α := α)).2 ?_
    intro z hz
    have hz_sum : (z : WithTopBot α) + sInf s < c := by
      exact
        (WithBotTop.lt_sub_iff_add_lt
          (.inr (show (z : WithTopBot α) ≠ ⊤ by simp))
          (.inr (show (z : WithTopBot α) ≠ ⊥ by simp))).1 hz
    have hzs : sInf s < c - (z : WithTopBot α) := by
      refine
        (WithBotTop.lt_sub_iff_add_lt
          (.inl (show (z : WithTopBot α) ≠ ⊥ by simp))
          (.inl (show (z : WithTopBot α) ≠ ⊤ by simp))).2 ?_
      simpa [add_comm] using hz_sum
    rcases sInf_lt_iff.1 hzs with ⟨w, hw, hw_lt⟩
    rcases hw with ⟨x, hAx, rfl⟩
    have hw_sum : f x + (z : WithTopBot α) < c := by
      exact
        (WithBotTop.lt_sub_iff_add_lt
          (.inl (show (z : WithTopBot α) ≠ ⊥ by simp))
          (.inl (show (z : WithTopBot α) ≠ ⊤ by simp))).1 hw_lt
    have hz_term : (z : WithTopBot α) < ⟪y, yStar⟫ₚ - f x := by
      refine
        (WithBotTop.lt_sub_iff_add_lt
          (.inr (show (z : WithTopBot α) ≠ ⊤ by simp))
          (.inr (show (z : WithTopBot α) ≠ ⊥ by simp))).2 ?_
      simpa [c, add_comm] using hw_sum
    have hdual : (⟪y, yStar⟫ₚ : WithTopBot α) = ⟪x, Astar yStar⟫ₚ := by
      rw [← hAx]
      exact congrArg (fun r : α ↦ (r : WithTopBot α)) (hA x yStar)
    rw [hdual] at hz_term
    exact lt_of_lt_of_le hz_term <| le_iSup (fun x : E ↦ ⟪x, Astar yStar⟫ₚ - f x) x
  · refine iSup_le fun x ↦ ?_
    have hsInf : (A ◁ f) (A x) ≤ f x := by
      rw [linearImage_eq_sInf_image]
      exact sInf_le ⟨x, rfl, rfl⟩
    calc
      ⟪x, Astar yStar⟫ₚ - f x
          = ⟪A x, yStar⟫ₚ - f x := by
            simpa using
              congrArg (fun t : WithTopBot α ↦ t - f x)
                (congrArg (fun r : α ↦ (r : WithTopBot α)) (hA x yStar).symm)
      _ ≤ ⟪A x, yStar⟫ₚ - (A ◁ f) (A x) := by
            exact WithBotTop.sub_le_sub le_rfl hsInf
      _ ≤ ⨆ y : F, ⟪y, yStar⟫ₚ - (A ◁ f) y := by
            exact le_iSup (fun y : F ↦ ⟪y, yStar⟫ₚ - (A ◁ f) y) (A x)

end

/-! ### Corollary_16_3_2_1 (from Chap03) -/
noncomputable section

universe u v

section

open scoped Rockafellar

variable {α : Type*} [ConditionallyCompleteLattice α] [One α]
variable {E : Type u} {F : Type v} {EStar : Type*} {FStar : Type*}
variable [HasPairing FStar F α] [HasPairing EStar E α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.3.2.1 states that the polar of the image `AC` is the inverse image
  of the polar `C*` under a dual map `A*`.
- `core/canonical`: the owner layer is pairing-based: set image `A '' C`, chapter polar owner
  `Set.polar` (notation `ᵒ[α]`), and an explicit dual-side map `Astar` constrained by
  pairing compatibility.
- `bridge/view`: the inner-product adjoint form is provided at the canonical continuous-operator
  layer, where `Astar` is instantiated by `A.adjoint`.

Domain-style sampling used here:
- `Set.polar` and the parameterized notation `ᵒ[α]` from `Text_14_0_5`;
- `supportFunction_image_eq_supportFunction_comp` from `Corollary_16_3_1_1`.

Primitive data vs derived API:
- primitive inputs: `A`, `Astar`, pairing compatibility, and the set `C`;
- derived API: the polar-image identity.

Layer target: `source-facing`, stated first at the pairing owner layer; the adjoint theorem is the
continuous-operator bridge specialization.

Semantic note: because `Set.polar C` is defined as the `1`-sublevel set of `supportFunction C`,
Corollary 16.3.1.1 already yields the displayed identity for arbitrary sets `C`; the source's
convexity hypothesis is therefore redundant and omitted.

Codomain note: the main theorem is stated at the extended-codomain layer `WithBotTop α`, matching
the support-function and polar owners.
-/

namespace Set

-- Proof sketch: `Cᵒ[α]` is the `1`-sublevel set of `supportFunction C` by definition. Apply the
-- pairing-level support-function image theorem and take preimages of `Set.Iic 1`.
/-- Corollary 16.3.2.1 at the pairing owner layer: if `A` and `Astar` satisfy
`⟪yStar, A x⟫ = ⟪Astar yStar, x⟫`, then the polar of `A '' C` is the preimage of `Cᵒ[α]` under
`Astar`. -/
theorem polar_image_eq_preimage
    (A : E → F) (Astar : FStar → EStar)
    (hA : ∀ x : E, ∀ yStar : FStar, (⟪yStar, A x⟫ₚ : α) = ⟪Astar yStar, x⟫ₚ)
    (C : Set E) :
    (A '' C)ᵒ[α] = Astar ⁻¹' Cᵒ[α] := by
  simpa [Set.polar] using
    congrArg (fun f ↦ f ⁻¹' Set.Iic (1 : WithBotTop α))
      (supportFunction_image_eq_supportFunction_comp (A := A) (Astar := Astar)
        (hA := hA) (C := C))

end Set

end

section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

namespace ContinuousLinearMap

/-- Corollary 16.3.2.1, inner-product bridge form: the polar of `A '' C` is the inverse image of
`Cᵒ` under `A.adjoint`. -/
theorem polar_image_eq_preimage_adjoint_polar
    (A : E →L[ℝ] F) (C : Set E) :
    (A '' C)ᵒ[ℝ] = A.adjoint ⁻¹' Cᵒ[ℝ] := by
  simpa using
    (Set.polar_image_eq_preimage (A := A) (Astar := A.adjoint)
      (hA := fun x yStar => by
        simpa using (ContinuousLinearMap.adjoint_inner_left A x yStar).symm)
      (C := C))

end ContinuousLinearMap

end

/-! ### Corollary_16_3_2_2 (from Chap03) -/
noncomputable section

universe u v w z

section

open scoped Rockafellar

variable {α : Type*} [ConditionallyCompleteLattice α] [One α]
variable {E : Type u} {F : Type v} {EStar : Type w} {FStar : Type z}
variable [HasPairing FStar F α] [HasPairing F FStar α]
variable [HasPairing EStar E α] [HasPairing E EStar α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.3.2.2 states that the polar of the inverse image
  `A⁻¹ (closure D)` is the closure of the dual-side image `A^*(D^*)`.
- `core/canonical`: the owner form is pairing-level and scalar-generic: for primal/dual maps
  `A`, `Astar` and compatibility `⟪y, Astar x*⟫ = ⟪A y, x*⟫`, if `C` satisfies bipolarity
  `((Cᵒ)ᵒ = C)`, then `(A⁻¹ C)ᵒ = ((A*(Cᵒ))ᵒ)ᵒ`.
- `bridge/view`: the closure identity is exposed from the core theorem using explicit bipolar
  hypotheses for `C` and for `Astar '' Cᵒ`.

Domain-style sampling used here:
- `Set.polar_image_eq_preimage` from `Corollary_16_3_2_1`;
- `Set.polar_closure` from `Text_14_0_5`;
- `LinearMap.adjoint` only for the inner-product bridge theorem.

Primitive data vs derived API:
- primitive owner data: primal/dual maps `A`, `Astar`, pairing compatibility, and bipolarity
  inputs for `C` and `Astar '' Cᵒ`;
- derived bridge data: `Astar = A.adjoint` yields the adjoint bridge, and `C = closure D`
  yields the closure specialization.

Layer target: the main theorem is the pairing owner theorem; Euclidean/adjoint/closure forms are
retained as bridge corollaries.

Semantic note: the origin-closure hypothesis is mathematically necessary for this polar identity.
Without it, the displayed equation already fails for the zero map and a convex set whose closure
does not meet `0`.
-/

-- Proof sketch: apply Corollary 16.3.2.1 to `Astar` with dual map `A` to identify
-- `(Astar '' Cᵒ[α])ᵒ[α]` as `A ⁻¹' ((Cᵒ[α])ᵒ[α])`,
-- then rewrite by bipolarity of `C`.
/-- Pairing owner form of Corollary 16.3.2.2: if `C` is bipolar and `A`, `Astar` satisfy
`⟪y, Astar x*⟫ = ⟪A y, x*⟫`, then the polar of `A ⁻¹' C` is
the double polar of `Astar '' Cᵒ[α]`.
-/
theorem polar_preimage_eq_double_polar_image_polar
    (A : E → F) (Astar : FStar → EStar)
    (hAstar : ∀ xStar : FStar, ∀ y : E, (⟪y, Astar xStar⟫ₚ : α) = ⟪A y, xStar⟫ₚ)
    (C : Set F) (hC_bipolar : Set.polar α (Set.polar α C : Set FStar) = C) :
    ((A ⁻¹' C)ᵒ[α] : Set EStar) =
      (((Astar '' (Cᵒ[α] : Set FStar))ᵒ[α] : Set E)ᵒ[α]) := by
  have himage_polar :
      ((Astar '' (Cᵒ[α] : Set FStar))ᵒ[α] : Set E) = A ⁻¹' C := by
    calc
      (Astar '' (Cᵒ[α] : Set FStar))ᵒ[α] =
          A ⁻¹' Set.polar α (Set.polar α C : Set FStar) := by
        simpa using
          Set.polar_image_eq_preimage (A := Astar) (Astar := A) (hA := hAstar)
            (C := (Set.polar α C : Set FStar))
      _ = A ⁻¹' C := by simp [hC_bipolar]
  rw [himage_polar]

end

section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

-- Proof sketch: apply the pairing-level double-polar owner theorem and rewrite both double-polars
-- by the supplied primitive bipolar hypotheses.
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Bipolar bridge form of Corollary 16.3.2.2: for primal/dual linear maps
`A : E → F`, `Astar : F → E` satisfying `⟪y, Astar x*⟫ = ⟪A y, x*⟫`, if `C` is bipolar and
`Astar '' Cᵒ[ℝ]` has closure as its bipolar, then
`(A ⁻¹' C)ᵒ[ℝ] = closure (Astar '' Cᵒ[ℝ])`. -/
theorem polar_preimage_eq_closure_image_polar
    (A : E →ₗ[ℝ] F) (Astar : F →ₗ[ℝ] E)
    (hA : ∀ xStar : F, ∀ y : E, (⟪y, Astar xStar⟫ₚ : ℝ) = ⟪A y, xStar⟫ₚ)
    (C : Set F)
    (hC_bipolar : Set.polar ℝ (Set.polar ℝ C : Set F) = C)
    (himage_bipolar :
      Set.polar ℝ (Set.polar ℝ (Astar '' (Set.polar ℝ C : Set F)) : Set E) =
        closure (Astar '' (Set.polar ℝ C : Set F))) :
    (A ⁻¹' C)ᵒ[ℝ] = closure (Astar '' Cᵒ[ℝ]) := by
  calc
    (A ⁻¹' C)ᵒ[ℝ] = Set.polar ℝ (Set.polar ℝ (Astar '' (Set.polar ℝ C : Set F)) : Set E) := by
      simpa using
        polar_preimage_eq_double_polar_image_polar
          (A := A) (Astar := Astar) (hAstar := hA) (C := C) (hC_bipolar := hC_bipolar)
    _ = closure (Astar '' (Set.polar ℝ C : Set F)) := himage_bipolar
    _ = closure (Astar '' Cᵒ[ℝ]) := by rfl

-- Proof sketch: specialize the owner theorem with `Astar = A.adjoint`; the pairing
-- compatibility witness is `LinearMap.adjoint_inner_right`.
/-- Inner-product bridge form: specialize the owner theorem with `Astar = A.adjoint`. -/
theorem polar_preimage_eq_closure_image_adjoint_polar
    (A : E →ₗ[ℝ] F) (C : Set F)
    (hC_bipolar : Set.polar ℝ (Set.polar ℝ C : Set F) = C)
    (himage_bipolar :
      Set.polar ℝ (Set.polar ℝ (A.adjoint '' (Set.polar ℝ C : Set F)) : Set E) =
        closure (A.adjoint '' (Set.polar ℝ C : Set F))) :
    (A ⁻¹' C)ᵒ[ℝ] = closure (A.adjoint '' Cᵒ[ℝ]) := by
  simpa using
    polar_preimage_eq_closure_image_polar (A := A) (Astar := A.adjoint)
      (hA := fun xStar y => by
        simpa using (A.adjoint_inner_right y xStar))
      (C := C) hC_bipolar himage_bipolar

-- Proof sketch: specialize the adjoint bridge theorem to `C = closure D` and simplify the polar
-- by `Set.polar_closure`.
/-- Source-facing closure specialization under explicit bipolar hypotheses for `closure D` and for
`A.adjoint '' (closure D)ᵒ[ℝ]`. -/
theorem polar_preimage_closure_eq_closure_image_adjoint_polar
    (A : E →ₗ[ℝ] F) (D : Set F)
    (hclosureD_bipolar : Set.polar ℝ (Set.polar ℝ (closure D) : Set F) = closure D)
    (himage_bipolar :
      Set.polar ℝ (Set.polar ℝ (A.adjoint '' (Set.polar ℝ (closure D) : Set F)) : Set E) =
        closure (A.adjoint '' (Set.polar ℝ (closure D) : Set F))) :
    (A ⁻¹' closure D)ᵒ[ℝ] = closure (A.adjoint '' Dᵒ[ℝ]) := by
  simpa [Set.polar_closure] using
    polar_preimage_eq_closure_image_adjoint_polar
      A (closure D) hclosureD_bipolar himage_bipolar

end

/-! ### Theorem_16_3_2 (from Chap03) -/
noncomputable section

universe u v

section

open scoped Rockafellar

variable {α : Type*}
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable [DenselyOrdered α] [NoBotOrder α] [NoTopOrder α] [Nonempty α]
variable {E : Type u} {F : Type v}
variable [HasPairing E E α] [HasPairing F F α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.3.2 identifies the conjugate of the precomposition
  `((cl g) A)^*` with the closure of the dual-side image `cl (A^* g^*)`.
- `core/canonical`: the owner layer is pairing-based. The primitive data are a primal map `A`,
  a dual map `Astar`, and the compatibility identity
  `⟪Astar y, x⟫ = ⟪y, A x⟫`.
- `bridge/view`: the inner-product adjoint form is a specialization with `Astar := A.adjoint`.

Domain-style sampling used here:
- `convexConjugate` from Defn 12.2;
- `lowerSemicontinuousHull` from Text 7.0.4;
- `Function.linearImage` and
  `convexConjugate_linearImage_eq_comp` from Theorem 16.3.1;
- the inner-product bridge `LinearMap.adjoint`.

Primitive data vs derived API:
- primitive inputs: maps `A : E → F` and `Astar : F → E`, the duality compatibility
  witness, and a function `g : F → WithTopBot α`;
- primitive owner identity: the biconjugate-layer equality
  `((g⋆⋆ ∘ A)⋆) = (Astar ◁ g⋆)⋆⋆`;
- derived API: the lower-semicontinuous-hull form and the convex-source form, recovered by
  supplying biconjugacy identities from Theorem 12.2.

Layer target: `source-facing`, expressed through the canonical owner declarations.
-/

-- Proof sketch: apply Theorem 16.3.1 to `Astar` and `g⋆`, using `A` as the dual-side map.
-- This identifies `(Astar ◁ g⋆)⋆` with `g⋆⋆ ∘ A`; conjugating both sides gives the displayed
-- biconjugate-layer identity.
theorem convexConjugate_comp_linearMap_eq_biconjugate_linearImage
    (A : E → F) (Astar : F → E)
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : α) = ⟪y, A x⟫ₚ)
    (g : F → WithTopBot α) :
    ((g⋆⋆ ∘ A)⋆ : E → WithTopBot α) =
      ((Astar ◁ g⋆)⋆ : E → WithTopBot α)⋆ := by
  have himage :
      (Astar ◁ g⋆)⋆ = g⋆⋆ ∘ A := by
    simpa using
      (convexConjugate_linearImage_eq_comp
        (A := Astar) (Astar := A) (hA := hAstar)
        (f := g⋆))
  exact congrArg (fun f : E → WithTopBot α ↦ (f⋆ : E → WithTopBot α)) himage.symm

section

variable [TopologicalSpace α] [TopologicalSpace E] [TopologicalSpace F]

-- Proof sketch: rewrite the primitive biconjugate identity above using the two supplied
-- biconjugacy equalities `g⋆⋆ = cl(g)` and `(Astar ◁ g⋆)⋆⋆ = cl(Astar ◁ g⋆)`.
/-- Lower-semicontinuous-hull form of Theorem 16.3.2: if the biconjugates of `g` and
`Astar ◁ g⋆` identify with their lower-semicontinuous hulls, then `((cl(g) ∘ A)⋆) =
cl(Astar ◁ g⋆)`. -/
theorem convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_of_biconjugate
    (A : E → F) (Astar : F → E)
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : α) = ⟪y, A x⟫ₚ)
    (g : F → WithTopBot α)
    (hg_biconj : g⋆⋆ = cl(g))
    (hAg_biconj :
      ((Astar ◁ g⋆)⋆ : E → WithTopBot α)⋆ =
        cl(Astar ◁ g⋆)) :
    ((cl(g) ∘ A)⋆ : E → WithTopBot α) = cl(Astar ◁ g⋆) := by
  calc
    ((cl(g) ∘ A)⋆ : E → WithTopBot α) = ((g⋆⋆ ∘ A)⋆ : E → WithTopBot α) := by
      simp [hg_biconj]
    _ = ((Astar ◁ g⋆)⋆ : E → WithTopBot α)⋆ := by
      simpa using
        convexConjugate_comp_linearMap_eq_biconjugate_linearImage
          (A := A) (Astar := Astar) (hAstar := hAstar) (g := g)
    _ = cl(Astar ◁ g⋆) := hAg_biconj

end

end

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜] [IsOrderedAddMonoid 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜] [NoBotOrder 𝕜] [NoTopOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} {F : Type v}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 F]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable [HasLinearPairing F F 𝕜] [HasContinuousPairing F F 𝕜]

-- Bridge note: the convex-source form relies on the Chapter 12 biconjugacy theorem
-- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`.
-- The primitive theorem above is the canonical owner layer; this theorem supplies the
-- convex-source hypotheses that produce those biconjugacy identities.
-- Theorem 16.3.2 is recovered from the primitive biconjugacy-layer theorem by using
-- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull` for `g` and `Astar ◁ g⋆`.
/-- Pairing-layer convex-source form of Theorem 16.3.2: for a primal map `A`, a dual map `Astar`,
and compatibility identity `⟪Astar y, x⟫ = ⟪y, A x⟫`, the conjugate of `cl(g) ∘ A` equals
`cl(Astar ◁ g⋆)` whenever `g` is convex. -/
theorem convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_of_convex
    (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E)
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : 𝕜) = ⟪y, A x⟫ₚ)
    (g : F → WithTopBot 𝕜) (hg : g.IsConvex 𝕜) :
    ((cl(g) ∘ A)⋆ : E → WithTopBot 𝕜) = cl(Astar ◁ g⋆) := by
  have hgstar_conv : ((g⋆ : F → WithTopBot 𝕜)).IsConvex 𝕜 :=
    Function.isConvex_convexConjugate g
  have hconv : (Astar ◁ (g⋆ : F → WithTopBot 𝕜)).IsConvex 𝕜 := by
    simpa using
      Function.isConvex_linearImage (A := Astar) (h := (g⋆ : F → WithTopBot 𝕜)) hgstar_conv
  exact
    convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_of_biconjugate
      (A := A) (Astar := Astar) (hAstar := hAstar) (g := g)
      (hg_biconj := hg.biconjugate_eq_lowerSemicontinuousHull)
      (hAg_biconj := hconv.biconjugate_eq_lowerSemicontinuousHull)

end

section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Inner-product-space bridge form of Theorem 16.3.2. -/
theorem convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_adjoint_of_convex
    (A : E →ₗ[ℝ] F) (g : F → WithTopBot ℝ) (hg : g.IsConvex ℝ) :
    ((cl(g) ∘ A)⋆ : E → WithTopBot ℝ) = cl(A.adjoint ◁ g⋆) := by
  simpa using
    (convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_of_convex
      (A := A) (Astar := A.adjoint)
      (hAstar := fun y x => A.adjoint_inner_left x y) (g := g) hg)

end

/-! ### Theorem_16_3_3 (from Chap03) -/
noncomputable section

universe u v

section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.3.3 removes the closure from Theorem 16.3.2 under a relative-
  interior hypothesis, then records the pointwise infimum formula and the attainment-or-vacuity
  alternative.
- `core/canonical`: the owner layer is pairing-based and scalar-parameterized:
  `convexConjugate`, `Function.linearImage`, and `riDom[𝕜](g)`.
- `bridge/view`: the Euclidean/adjoint statement is a specialization via `Astar := A.adjoint`.

Domain-style sampling used here:
- `convexConjugate_comp_linearMap_eq_lowerSemicontinuousHull_linearImage_adjoint_of_convex`
  and its pairing-level owner from Theorem 16.3.2;
- `Function.linearImage_eq_sInf_image` from Theorem 5.7;
- `convexConjugate_comp_map_apply_eq_linearImage_apply_of_closureFreeDualFormula`
  from Text 16.0.5;
- the relative-interior owner `riDom[𝕜](·)`.

Primitive data vs derived API:
- primitive inputs: linear maps `A : E → F`, `Astar : F → E`, compatibility
  `⟪Astar y, x⟫ = ⟪y, A x⟫`, a convex `g : F → WithBotTop 𝕜`, and
  `∃ x, A x ∈ riDom[𝕜](g)`;
- derived API: closure-free dual identity, pointwise infimum formula, and attainment-or-vacuity.

Layer target: `source-facing`, expressed directly through the established owner declarations.
-/

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [DenselyOrdered 𝕜] [NoBotOrder 𝕜] [NoTopOrder 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable [HasLinearPairing F F 𝕜] [HasContinuousPairing F F 𝕜]
variable (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (g : F → WithBotTop 𝕜)

-- Proof sketch: combine Theorem 9.5 (`cl(g ∘ A) = cl(g) ∘ A`) with Theorem 16.3.2 on the
-- pairing owner layer, then remove the remaining closure on the linear image under the same
-- relative-interior hypothesis.
/-- Pairing-layer closure-free form of Theorem 16.3.3. -/
theorem convexConjugate_comp_linearMap_eq_linearImage_of_exists_mem_riDom
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : 𝕜) = ⟪y, A x⟫ₚ)
    (hg : g.IsConvex 𝕜) (hri : ∃ x : E, A x ∈ riDom[𝕜](g))
    :
    (g ∘ A)⋆ = Astar ◁ g⋆ := by
  have hcl_comp : cl(g ∘ A) = cl(g) ∘ A := by
    exact hg.lowerSemicontinuousHull_comp_linearMap_eq (A := A) (by
      simpa [Set.Nonempty] using hri)
  have hdual :
      ((g ∘ A)⋆ : E → WithBotTop 𝕜) =
        cl(Astar ◁ (g⋆ : F → WithBotTop 𝕜)) := by
    sorry
  -- The remaining step is exactly the closure-removal claim for the linear-image side.
  sorry

-- Proof sketch: apply the owner-level pointwise theorem from Text 16.0.5 to the closure-free
-- equality established just above, then expand the right-hand side by
-- `Function.linearImage_eq_sInf_image`.
/-- Evaluating the closure-free dual formula at `xStar` gives the infimum of `g⋆` on the dual
fiber `Astar yStar = xStar`. -/
theorem convexConjugate_comp_linearMap_apply_eq_sInf_image_conjugate_of_exists_mem_riDom
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : 𝕜) = ⟪y, A x⟫ₚ)
    (hg : g.IsConvex 𝕜) (hri : ∃ x : E, A x ∈ riDom[𝕜](g))
    (xStar : E) :
    (g ∘ A)⋆ xStar =
      sInf (g⋆ '' {yStar : F | Astar yStar = xStar}) := by
  have hdual : (g ∘ A)⋆ = Astar ◁ g⋆ :=
    convexConjugate_comp_linearMap_eq_linearImage_of_exists_mem_riDom
      A Astar g hAstar hg hri
  simpa [Function.linearImage_eq_sInf_image] using
    convexConjugate_comp_map_apply_eq_linearImage_apply_of_closureFreeDualFormula
      A Astar g hdual xStar

-- Proof sketch: under the same relative-interior hypothesis, the source theorem states that the
-- infimum over the dual fiber is attained whenever the fiber is nonempty. If the fiber is empty,
-- the displayed infimum is vacuous and equals `⊤`.
/-- Under the same hypothesis, the infimum over the dual fiber is either vacuous (`⊤`) or attained
at some `yStar` with `Astar yStar = xStar`. -/
theorem convexConjugate_comp_linearMap_apply_eq_top_or_exists_eq_and_eq_conjugate_of_exists_mem_riDom
    (hAstar : ∀ y : F, ∀ x : E, (⟪Astar y, x⟫ₚ : 𝕜) = ⟪y, A x⟫ₚ)
    (hg : g.IsConvex 𝕜) (hri : ∃ x : E, A x ∈ riDom[𝕜](g))
    (xStar : E) :
    (g ∘ A)⋆ xStar = ⊤ ∨
      ∃ yStar : F, Astar yStar = xStar ∧
        (g ∘ A)⋆ xStar = g⋆ yStar := sorry

end

section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable (A : E →ₗ[ℝ] F) (g : F → WithBotTop ℝ)

/-- Theorem 16.3.3, adjoint bridge form. -/
theorem convexConjugate_comp_linearMap_eq_linearImage_adjoint_of_exists_mem_intrinsicInterior_dom
    (hg : g.IsConvex ℝ) (hri : ∃ x : E, A x ∈ riDom[ℝ](g))
    :
    (g ∘ A)⋆ = A.adjoint ◁ g⋆ := by
  simpa using
    (convexConjugate_comp_linearMap_eq_linearImage_of_exists_mem_riDom
      (A := A) (Astar := A.adjoint) (g := g)
      (hAstar := fun y x => A.adjoint_inner_left x y) hg hri)

/-- Pointwise infimum formula in the adjoint bridge form. -/
theorem convexConjugate_comp_linearMap_apply_eq_sInf_image_conjugate_of_exists_mem_intrinsicInterior_dom
    (hg : g.IsConvex ℝ) (hri : ∃ x : E, A x ∈ riDom[ℝ](g))
    (xStar : E) :
    (g ∘ A)⋆ xStar =
      sInf (g⋆ '' {yStar : F | A.adjoint yStar = xStar}) := by
  simpa using
    (convexConjugate_comp_linearMap_apply_eq_sInf_image_conjugate_of_exists_mem_riDom
      (A := A) (Astar := A.adjoint) (g := g)
      (hAstar := fun y x => A.adjoint_inner_left x y) hg hri xStar)

/-- Attainment-or-vacuity formula in the adjoint bridge form. -/
theorem convexConjugate_comp_linearMap_apply_eq_top_or_exists_adjoint_eq_and_eq_conjugate_of_exists_mem_intrinsicInterior_dom
    (hg : g.IsConvex ℝ) (hri : ∃ x : E, A x ∈ riDom[ℝ](g))
    (xStar : E) :
    (g ∘ A)⋆ xStar = ⊤ ∨
      ∃ yStar : F, A.adjoint yStar = xStar ∧
        (g ∘ A)⋆ xStar = g⋆ yStar := by
  simpa using
    (convexConjugate_comp_linearMap_apply_eq_top_or_exists_eq_and_eq_conjugate_of_exists_mem_riDom
      (A := A) (Astar := A.adjoint) (g := g)
      (hAstar := fun y x => A.adjoint_inner_left x y) hg hri xStar)

end
