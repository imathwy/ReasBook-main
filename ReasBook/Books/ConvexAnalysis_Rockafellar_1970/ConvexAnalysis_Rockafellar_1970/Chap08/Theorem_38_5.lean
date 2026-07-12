import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_8
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_0_4
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_1

noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

section Owner

variable {U : Type u} {X : Type v} {Y : Type w}
variable {α : Type*}
variable [ConditionallyCompleteLattice α] [Add α]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 38.5 studies the product `GF` of two convex bifunctions, defined by
  `((GF) u) y = inf_x (F u x + G x y)`.
- `core/canonical`: the owner abstractions already present upstream are `Bifunction.image` for the
  one-step elimination of an intermediate variable, `Bifunction.adjoint`, and the
  slice-domain owner `Bifunction.dom`.
- `bridge/view`: the Chapter 38 product is therefore the thin source-facing bridge
  `fun u ↦ image G (F u)` rather than a second pointwise-infimum wheel.

Primary mathematical domain:
- composition of proper convex bifunctions and the adjoint-duality formula `(GF)* = F*G*`.

Domain-style sampling used here:
- `Bifunction.image` and `Bifunction.image_apply` from `Definition_38_0_4`;
- `Bifunction.adjoint` from `Chap06.Lemma_31_0_8`;
- `Bifunction.dom` and `Bifunction.IsProper` from `Chap08.Theorem_38_1`.

Primitive data vs derived API:
- primitive source data: bifunctions `F : U → X → WithBotTop α` and
  `G : X → Y → WithBotTop α`;
- primitive source-facing owner introduced here: `Bifunction.comp`, used in the raw owner form
  `comp G F` because dot notation would collide with ordinary `Function.comp`;
- derived API: the pointwise image formula, the indexed-infimum formula, graph convexity of
  `Function.uncurry`, the adjoint identity, and the attainment clause for the dual-side product.

Layer target: `source-facing`. The product `GF` is genuine source-facing content for §38.5, but it
should be owned by a thin bridge over the existing image operator.

Notation decision:
- no new notation is introduced. The source juxtaposition `GF` is not a stable Lean surface form,
  and a symbolic surrogate would be decorative rather than canonical. The short owner name `comp`
  keeps the mathematical meaning explicit without introducing parser noise.
-/

/-- Theorem 38.5 owner: the product of bifunctions, obtained by taking for each `u` the image of
the slice `F u` under `G`. -/
abbrev comp
    (G : X → Y → WithBotTop α) (F : U → X → WithBotTop α) :
    U → Y → WithBotTop α :=
  fun u ↦ image G (F u)

/-- Evaluating the product `comp G F` at `(u, y)` is the image formula for the slice `F u`
under `G`. -/
@[simp] theorem comp_apply
    (G : X → Y → WithBotTop α) (F : U → X → WithBotTop α) (u : U) (y : Y) :
    comp G F u y = image G (F u) y :=
  rfl

/-- Evaluating `comp G F` at `(u, y)` gives the indexed infimum
`inf_x (F u x + G x y)`. -/
@[simp] theorem comp_apply_eq_iInf
    (G : X → Y → WithBotTop α) (F : U → X → WithBotTop α) (u : U) (y : Y) :
    comp G F u y = ⨅ x : X, F u x + G x y := by
  simpa [comp] using image_apply G (F u) y

end Owner

section Theorem

variable {U : Type u} {X : Type v} {Y : Type w}

local notation "ri(" C ")" => intrinsicInterior ℝ C

section Convexity

variable {𝕜 : Type*} {α : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid Y] [SMul 𝕜 Y]
variable [AddCommMonoid α] [SMul 𝕜 α] [LE α]
variable [ConditionallyCompleteLattice α] [Add α]

/-- Theorem 38.5, convexity clause: the product `comp G F` of convex bifunctions is again convex,
expressed canonically as convexity of the uncurried graph function. -/
theorem uncurry_comp_isConvex
    {F : U → X → WithBotTop α} {G : X → Y → WithBotTop α}
    (hF : Function.IsConvex 𝕜 (Function.uncurry F))
    (hG : Function.IsConvex 𝕜 (Function.uncurry G)) :
    Function.IsConvex 𝕜 (Function.uncurry (comp G F)) := by
  sorry

end Convexity

section Adjoint

variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]
variable [HasLinearPairing Y Y ℝ] [HasContinuousPairing Y Y ℝ]
variable {F : U → X → EReal} {G : X → Y → EReal}

/-- Theorem 38.5, adjoint clause: if the relative interiors of `dom F*` and `dom G` meet, then
the adjoint of the product is the product of the adjoints, rendered by the owners
`adjoint`, `dom`, and `comp`. -/
theorem adjointFunction_comp_eq_comp_adjointFunction_of_common_riDom
    (hF_convex : Function.IsConvex ℝ (Function.uncurry F)) (hF_proper : IsProper F)
    (hG_convex : Function.IsConvex ℝ (Function.uncurry G)) (hG_proper : IsProper G)
    (hri :
      (ri(dom (adjoint X U F)) ∩ ri(dom G)).Nonempty)
    :
    adjoint Y U (comp G F) =
      comp (adjoint X U F) (adjoint Y X G) := by
  sorry

/-- Pointwise form of the adjoint identity in Theorem 38.5. -/
@[simp] theorem adjointFunction_comp_apply_of_common_riDom
    (hF_convex : Function.IsConvex ℝ (Function.uncurry F)) (hF_proper : IsProper F)
    (hG_convex : Function.IsConvex ℝ (Function.uncurry G)) (hG_proper : IsProper G)
    (hri :
      (ri(dom (adjoint X U F)) ∩ ri(dom G)).Nonempty)
    (yStar : Y) (uStar : U) :
    adjoint Y U (comp G F) yStar uStar =
      comp (adjoint X U F) (adjoint Y X G) yStar uStar := by
  simpa using
    congrFun
      (congrFun
        (adjointFunction_comp_eq_comp_adjointFunction_of_common_riDom
          hF_convex hF_proper hG_convex hG_proper hri)
        yStar)
      uStar

/-- Theorem 38.5, attainment clause in owner form: under the same common-relative-interior
hypothesis, the dual-side product `F*G*` is attained at every pair `(u*, y*)`. Because the
chapter owner `comp` is defined by an infimum, this is stated as existence of an intermediate
`x*` realizing the value of `comp (adjoint F) (adjoint G) y* u*`. -/
theorem exists_eq_comp_adjointFunction_of_common_riDom
    (hF_convex : Function.IsConvex ℝ (Function.uncurry F)) (hF_proper : IsProper F)
    (hG_convex : Function.IsConvex ℝ (Function.uncurry G)) (hG_proper : IsProper G)
    (hri :
      (ri(dom (adjoint X U F)) ∩ ri(dom G)).Nonempty)
    (yStar : Y) (uStar : U) :
    ∃ xStar : X,
      comp (adjoint X U F) (adjoint Y X G) yStar uStar =
        adjoint Y X G yStar xStar + adjoint X U F xStar uStar := by
  sorry

end Adjoint

end Theorem

end Bifunction
