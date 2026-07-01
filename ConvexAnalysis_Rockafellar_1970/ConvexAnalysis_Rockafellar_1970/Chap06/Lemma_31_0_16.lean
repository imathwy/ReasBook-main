import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Example_23_0_7
import ConvexAnalysis_Rockafellar_1970.Chap05.Text_26_0_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_5

noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} {U : Type v}
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]

local instance instHasPairingSwapPrimalStrongDual :
    HasPairingSwap E (StrongDual 𝕜 E) 𝕜 where
  pairing_swap _ _ := rfl

/-!
Source/core/bridge triage for Lemma 31.0.16.

- `source-facing`: the homogeneous-program Kuhn-Tucker conditions for the support/indicator
  specialization are the two owner memberships on support and concave-indicator sides.
- `core/canonical`: the chapter/project owners are `normalCone`, `subdifferentialAt`,
  and `concaveSubdifferentialAt` on the intrinsic dual carrier `StrongDual`; this pass exposes
  the pointwise canonical theorem first, then a homogeneous-program specialization as a thin
  bridge.
- `bridge/view`: this file specializes the existing Chapter 23/6 owner bridges to the Chapter 31
  support/indicator data, without using the Euclidean `∂ᵥ` bridge or `A.adjoint`.

Domain-style sampling used here:
- `supportFunction` (`δᵛ(· | C)`) from `Chap01.Defintion_4_8_2`;
- `subdifferentialAt` (`∂[Y]`) from `Chap05.Definition_23_0_6`;
- `indicatorFunction_isClosedProperConvex_of_nonempty` from `Chap03.Text_12_3_6`;
- `convexConjugate_indicatorFunction_eq_supportFunction` from `Chap03.Text_13_1_4`;
- `_root_.subdifferentialGraph_convexConjugate_eq_inv` from `Chap05.Text_26_0_1`;
- `_root_.subdifferentialAt_indicatorFunction_eq_normalCone` from
  `Chap05.Example_23_0_7`;
- `_root_.mem_concaveSubdifferentialAt_iff_neg_mem_subdifferentialAt_neg` from
  `Chap06.Definition_6_30_5`.

Primitive data vs derived API:
- primitive core data: sets `C`, `D` and points `x`, `xStar`, `u`, `uStar`;
- derived source-facing bridge data: a map `A` and companion dual-side map `Astar` yielding
  `xStar = Astar uStar` and `u = A x`.

Layer target: `core/canonical`.

Scalar/ambient check:
- this declaration is expressed at the generic ordered-normed scalar layer required by the
  graph-inversion owner `_root_.subdifferentialGraph_convexConjugate_eq_inv` and the indicator/
  normal-cone bridges used below.
-/

/-- Pointwise canonical owner form behind Lemma 31.0.16: support/indicator Kuhn-Tucker
subgradient conditions are exactly paired normal-cone memberships, on intrinsic dual carriers. -/
theorem supportIndicator_kuhnTuckerConditions_iff_normalCone
    {C : Set E} {D : Set U}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    {x : E} {xStar : StrongDual 𝕜 E} {u : U} {uStar : StrongDual 𝕜 U} :
    x ∈ (∂[E] (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot 𝕜)(xStar)) ∧
      uStar ∈ (∂⁺ (fun z : U ↦ -(δ[𝕜](z | D))) at u) ↔
      xStar ∈ N[𝕜](x | C) ∧
        -uStar ∈ N[𝕜](u | D) := by
  change x ∈ subdifferentialAt (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot 𝕜) xStar E ∧
      uStar ∈ (∂⁺ (fun z : U ↦ -(δ[𝕜](z | D))) at u) ↔
      xStar ∈ N[𝕜](x | C) ∧
        -uStar ∈ N[𝕜](u | D)
  have hSupport :
      x ∈ subdifferentialAt (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot 𝕜) xStar E ↔
        xStar ∈ N[𝕜](x | C) := by
    have hIndicatorClosed :
        Function.IsClosedProperConvex (𝕜 := 𝕜) (δ[𝕜](· | C) : E → WithTopBot 𝕜) :=
      indicatorFunction_isClosedProperConvex_of_nonempty hC_nonempty hC_closed hC_convex
    have hConjSupport :
        (((δ[𝕜](· | C) : E → WithTopBot 𝕜)⋆ : StrongDual 𝕜 E → WithTopBot 𝕜)) =
          (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot 𝕜) := by
      simpa using
        (convexConjugate_indicatorFunction_eq_supportFunction
          (E := E) (EStar := StrongDual 𝕜 E) (α := 𝕜) (C := C))
    have hGraph :
        _root_.subdifferentialGraph
            (((δ[𝕜](· | C) : E → WithTopBot 𝕜)⋆ : StrongDual 𝕜 E → WithTopBot 𝕜)) E =
          (_root_.subdifferentialGraph (δ[𝕜](· | C) : E → WithTopBot 𝕜)).inv :=
      _root_.subdifferentialGraph_convexConjugate_eq_inv
        (f := (δ[𝕜](· | C) : E → WithTopBot 𝕜)) hIndicatorClosed
    have hConjSub :
        x ∈ subdifferentialAt
          (((δ[𝕜](· | C) : E → WithTopBot 𝕜)⋆ : StrongDual 𝕜 E → WithTopBot 𝕜))
          xStar E ↔
          xStar ∈ (∂ (δ[𝕜](· | C) : E → WithTopBot 𝕜) at x) := by
      change
        (xStar, x) ∈ _root_.subdifferentialGraph
            (((δ[𝕜](· | C) : E → WithTopBot 𝕜)⋆ : StrongDual 𝕜 E → WithTopBot 𝕜)) E ↔
          (x, xStar) ∈ _root_.subdifferentialGraph
            (δ[𝕜](· | C) : E → WithTopBot 𝕜)
      rw [hGraph]
      exact
        (SetRel.mem_inv
          (R := _root_.subdifferentialGraph (δ[𝕜](· | C) : E → WithTopBot 𝕜))
          (a := x) (b := xStar))
    calc
      x ∈ subdifferentialAt (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot 𝕜) xStar E
          ↔ x ∈
            subdifferentialAt
              (((δ[𝕜](· | C) : E → WithTopBot 𝕜)⋆ : StrongDual 𝕜 E → WithTopBot 𝕜))
              xStar E := by
              rw [← hConjSupport]
      _ ↔ xStar ∈ (∂ (δ[𝕜](· | C) : E → WithTopBot 𝕜) at x) := hConjSub
      _ ↔ xStar ∈ N[𝕜](x | C) := by
            rw [_root_.subdifferentialAt_indicatorFunction_eq_normalCone]
  have hIndicator :
      uStar ∈ (∂⁺ (fun z : U ↦ -(δ[𝕜](z | D))) at u) ↔
        -uStar ∈ N[𝕜](u | D) := by
    rw [_root_.mem_concaveSubdifferentialAt_iff_neg_mem_subdifferentialAt_neg]
    have hneg_indicator :
        (-(fun z : U ↦ -(δ[𝕜](z | D)))) = (δ[𝕜](· | D) : U → WithTopBot 𝕜) := by
      funext z
      by_cases hz : z ∈ D <;> simp [indicator_def, hz]
    rw [hneg_indicator]
    rw [_root_.subdifferentialAt_indicatorFunction_eq_normalCone]
  exact hSupport.and hIndicator

/-- Lemma 31.0.16, homogeneous-program specialization: instantiate the pointwise canonical
owner theorem with `xStar = Astar uStar` and `u = A x`. -/
theorem homogeneousProgram_supportIndicator_kuhnTuckerConditions_iff_normalCone
    {A : E →L[𝕜] U} {Astar : StrongDual 𝕜 U → StrongDual 𝕜 E}
    {C : Set E} {D : Set U}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    {x : E} {uStar : StrongDual 𝕜 U} :
    x ∈ (∂[E] (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot 𝕜)(Astar uStar)) ∧
      uStar ∈ (∂⁺ (fun z : U ↦ -(δ[𝕜](z | D))) at A x) ↔
      Astar uStar ∈ N[𝕜](x | C) ∧
        -uStar ∈ N[𝕜](A x | D) := by
  change x ∈ subdifferentialAt (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot 𝕜) (Astar uStar) E ∧
      uStar ∈ (∂⁺ (fun z : U ↦ -(δ[𝕜](z | D))) at A x) ↔
      Astar uStar ∈ N[𝕜](x | C) ∧
        -uStar ∈ N[𝕜](A x | D)
  exact
    (supportIndicator_kuhnTuckerConditions_iff_normalCone
      (C := C) (D := D) hC_nonempty hC_closed hC_convex
      (x := x) (xStar := Astar uStar) (u := A x) (uStar := uStar))

end
