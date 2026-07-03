import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_23_9 (from Chap05) -/
noncomputable section

open scoped Rockafellar

universe u v w

section

variable {𝕜 : Type w} [NormedField 𝕜] [LinearOrder 𝕜]
variable {E : Type u} {F : Type v}
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-!
Source/core/bridge triage for clause (1).

- `source-facing`: Theorem 23.9 (1) is the adjoint pullback inclusion for subdifferentials of a
  composite.
- `core/canonical`: the intrinsic owner is `∂ f at x`, and the natural pullback
  map on dual subgradients is precomposition `yStar ↦ yStar.comp A` for
  `A : E →L[𝕜] F`.
- `bridge/view`: `∂ᵥf(x)` is only the inner-product specialization of that
  owner, so the adjoint-image statement belongs below as the inner-product bridge form of the
  intrinsic pullback theorem.
-/

-- Proof sketch: if `yStar ∈ ∂ h at (A x)`, then the supporting inequality for `h` at
-- `A x` applied to `A z` gives
-- `h (A z) ≥ h (A x) + yStar (A z - A x)`. Rewrite the evaluation term by precomposition as
-- `(yStar.comp A) (z - x)`, which is exactly the defining inequality for
-- `yStar.comp A ∈ ∂ (h ∘ A) at x`.
/-- Theorem 23.9 (1), canonical owner form: for any continuous linear map `A`, every intrinsic
subgradient of `h` at `A x` pulls back by precomposition with `A` to an intrinsic subgradient of
the composite `h ∘ A` at `x`. -/
theorem precomp_image_subdifferentialAt_subset_subdifferentialAt_comp
    (A : E →L[𝕜] F) (h : F → WithBotTop 𝕜) (x : E) :
    (fun yStar : StrongDual 𝕜 F ↦ yStar.comp A) '' (∂ h at (A x)) ⊆
      (∂ (h ∘ A) at x) := by
  intro xStar hxStar
  rcases hxStar with ⟨yStar, hyStar, rfl⟩
  rw [mem_subdifferentialAt] at hyStar ⊢
  intro z
  simpa [ContinuousLinearMap.coe_comp', Function.comp_apply, map_sub] using hyStar (A z)

end

section

variable {𝕜 : Type w} [RCLike 𝕜] [LinearOrder 𝕜]
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

namespace Function

-- Proof sketch: transport the canonical owner theorem above through the Fréchet-Riesz
-- identifications `InnerProductSpace.toDual 𝕜 E` and `InnerProductSpace.toDual 𝕜 F`. Under those
-- identifications, precomposition `yStar ↦ yStar.comp A` becomes the Hilbert adjoint
-- `A.adjoint`.
/-- Theorem 23.9 (1), inner-product bridge form: for any continuous linear map `A`, every vector
subgradient of `h` at `A x` pulls back by the adjoint map to a vector subgradient of the
composite `h ∘ A` at `x`. Equivalently, `A.adjoint '' ∂h(Ax) ⊆ ∂(h ∘ A)(x)`. -/
theorem adjoint_image_subdifferentialAt_subset_subdifferentialAt_comp_linearMap
    (A : E →L[𝕜] F) (h : F → WithBotTop 𝕜) (x : E) :
    A.adjoint '' (∂ᵥh(A x)) ⊆ (∂ᵥ(h ∘ A)(x)) := by
  let eE := InnerProductSpace.toDual 𝕜 E
  let eF := InnerProductSpace.toDual 𝕜 F
  intro xStar hxStar
  rcases hxStar with ⟨yStar, hyStar, rfl⟩
  change eF yStar ∈ (∂ h at (A x)) at hyStar
  change eE (A.adjoint yStar) ∈ (∂ (h ∘ A) at x)
  have hroot :
      (eF yStar).comp A ∈ (∂ (h ∘ A) at x) :=
    _root_.precomp_image_subdifferentialAt_subset_subdifferentialAt_comp A h x
      (Set.mem_image_of_mem (fun zStar : StrongDual 𝕜 F ↦ zStar.comp A) hyStar)
  have hcomp : eE (A.adjoint yStar) = (eF yStar).comp A := by
    ext z
    exact ContinuousLinearMap.adjoint_inner_left A z yStar
  exact hcomp ▸ hroot

end Function

section

variable {𝕜 : Type w} [RCLike 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] [CompleteSpace F]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 23.9 is the linear-precomposition rule for subdifferentials:
  `∂(h ∘ A)(x)` always contains the adjoint image `A* ∂h(Ax)`, and this inclusion is an equality
  under the standard range-relative-interior qualification or, in the polyhedral branch, under
  the weaker range-domain qualification.
- `core/canonical`: the primitive owner for subgradients is `∂ f at x` from
  `Chap05/Definition_23_0_6`, together with the effective-domain owners `dom(·)` and
  `riDom[𝕜](·)`,
  the polyhedral-function owner `Function.HasPolyhedralEpigraph`, and the adjoint-side
  conjugacy
  theorem
  `convexConjugate_comp_linearMap_eq_linearImage_adjoint_of_exists_mem_intrinsicInterior_dom`.
- `bridge/view`: the chapter-facing inner-product surface `∂ᵥf(x)` transports the
  primitive dual owner along the Hilbert-space duality bridge, so the source notation `A* ∂h(Ax)`
  is rendered directly as the set image `A.adjoint '' ∂ᵥh(A x)`, with no auxiliary
  “subgradient package”.

Domain-style sampling used here:
- `_root_.precomp_image_subdifferentialAt_subset_subdifferentialAt_comp` from this file;
- `∂ f at x` and `∂ᵥf(x)` from `Chap05/Definition_23_0_6`;
- `Function.IsClosedProperConvex.mem_subdifferentialAt_convexConjugate_iff` from
  `Chap05/Corollary_23_5_1`;
- `convexConjugate_comp_linearMap_eq_linearImage_adjoint_of_exists_mem_intrinsicInterior_dom`
  from `Chap03/Theorem_16_3_3`;
- the owner predicate `Function.HasPolyhedralEpigraph` from `Chap04/Text_19_0_8`, together
  with the owner-side linear-preimage theorem
  `Function.HasPolyhedralEpigraph.comp_linearMap` from `Chap04/Corollary_19_3_1`.

Primitive data vs derived API:
- primitive inputs: a linear map `A : E →ₗ[𝕜] F`, a function `h : F → WithBotTop 𝕜`,
  and a base point `x : E`;
- source qualifications: properness of `h`, together with either convexity of `h` plus a point
  of `riDom[𝕜](h)` in the range of `A`, or a polyhedral-epigraph hypothesis plus a point of
  `dom(h)` in the range of `A`;
- derived bridge API: the adjoint-image inclusion from clause (1), the two atomic equality clauses
  corresponding to the two source qualifications, and the original source-facing disjunctive
  theorem as a thin wrapper.

Layer target for this namespace: `bridge/view`. The intrinsic owner theorem for clause (1) now
lives above on `∂ f at x`; the declarations below are the inner-product
specializations that keep the source's adjoint notation on the theorem surface.
-/

-- Proof sketch: the inclusion from clause (1) is always available. For the reverse inclusion,
-- start with `xStar ∈ ∂ᵥ(h ∘ A)(x)` and apply the Fenchel-Young criterion from
-- Theorem 23.5 to the composite `h ∘ A`. Under either qualification branch, the Chapter 16 dual
-- formula identifies `(h ∘ A)⋆` with `A.adjoint ◁ h⋆`, and in the polyhedral branch the Chapter
-- 19 image theorem upgrades the same formula from polyhedrality. The attained linear-image value
-- then produces some `yStar` with `A.adjoint yStar = xStar` and
-- `yStar ∈ ∂ᵥh(A x)` via Corollary 23.5.1, giving the reverse inclusion.
/-- Theorem 23.9 (2), relative-interior branch: if the range of `A` contains a point of
`ri (dom h)`, then the composite subdifferential is exactly the adjoint image of the
subdifferential at the image point:
`∂(h ∘ A)(x) = A.adjoint '' ∂h(Ax)`. -/
theorem subdifferentialAt_comp_linearMap_eq_adjoint_image_of_exists_mem_riDom
    (A : E →ₗ[𝕜] F) (h : F → WithBotTop 𝕜) (hh_convex : h.IsConvex 𝕜)
    (hh_proper : h.IsProper) (x : E) (hri : ∃ x0 : E, A x0 ∈ riDom[𝕜](h)) :
    (∂ᵥ(h ∘ A)(x)) = A.adjoint '' (∂ᵥh(A x)) := sorry

/-- Theorem 23.9 (2), polyhedral branch: if `h` has polyhedral epigraph and the range of
`A` contains a point of `dom h`, then the same subdifferential equality holds. The convexity
assumption is absorbed by `h.HasPolyhedralEpigraph`, so only properness remains as separate
primitive data. -/
theorem subdifferentialAt_comp_linearMap_eq_adjoint_image_of_polyhedral_of_exists_mem_dom
    (A : E →ₗ[𝕜] F) (h : F → WithBotTop 𝕜) (hh_proper : h.IsProper)
    (hh_poly : h.HasPolyhedralEpigraph) (x : E) (hdom : ∃ x0 : E, A x0 ∈ dom(h)) :
    (∂ᵥ(h ∘ A)(x)) = A.adjoint '' (∂ᵥh(A x)) := sorry

/-- Theorem 23.9 (2): if the range of `A` contains a point of `ri (dom h)`, or if `h` has
polyhedral epigraph and the range of `A` contains a point of `dom h`, then the composite
subdifferential is exactly the adjoint image of the subdifferential at the image point:
`∂(h ∘ A)(x) = A.adjoint '' ∂h(Ax)`. This is the source-facing wrapper combining the two atomic
qualification branches above. -/
theorem subdifferentialAt_comp_linearMap_eq_adjoint_image_of_riDom_or_polyhedral
    (A : E →ₗ[𝕜] F) (h : F → WithBotTop 𝕜) (hh_proper : h.IsProper) (x : E)
    (hqual : (h.IsConvex 𝕜 ∧ ∃ x0 : E, A x0 ∈ riDom[𝕜](h)) ∨
      h.HasPolyhedralEpigraph ∧ ∃ x0 : E, A x0 ∈ dom(h)) :
    (∂ᵥ(h ∘ A)(x)) = A.adjoint '' (∂ᵥh(A x)) := by
  rcases hqual with ⟨hh_convex, hri⟩ | ⟨hh_poly, hdom⟩
  · exact subdifferentialAt_comp_linearMap_eq_adjoint_image_of_exists_mem_riDom
      A h hh_convex hh_proper x hri
  · exact subdifferentialAt_comp_linearMap_eq_adjoint_image_of_polyhedral_of_exists_mem_dom
      A h hh_proper hh_poly x hdom

end Function

end
