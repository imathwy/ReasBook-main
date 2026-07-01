import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_2_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2

noncomputable section

universe u v

open scoped Pointwise Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 38.3 scales a convex bifunction `F` by a positive scalar `λ`, asserts
  that the scaled bifunction stays convex and preserves the closed/proper status of `F`, and
  identifies both the slice pairing `⟨(F λ)u, x⋆⟩` and the adjoint `(F λ)⋆`.
- `core/canonical`: the owner layer already present upstream is the function-side scaling owner
  `rightScalarMul`, the function conjugacy theorem `convexConjugate_rightScalarMul_eq_left_smul`
  from `Theorem_16_1`, the chapter bifunction properness owner `Bifunction.IsProper` from
  `Theorem_38_1`, the bifunction adjoint owner `adjoint`, and the Chapter 34 bifunction
  owners `lowerPairing` and `IsClosedConvex`.
- `bridge/view`: the only new owner needed here is the slice-wise bifunction scaling operation
  `Bifunction.rightScalarMul` from `Definition_38_2_2`; every other clause of Theorem 38.3 should
  be stated directly in the existing owner language instead of introducing duplicate convexity or
  properness wrappers.

Primary mathematical domain:
- convex bifunctions, their slice-wise positive rescaling, and the interaction of that rescaling
  with the canonical pairing and adjoint operations.

Domain-style sampling used here:
- `Bifunction.rightScalarMul` and `Bifunction.rightScalarMul_apply`
  from `Definition_38_2_2`;
- `Bifunction.dom` and `Bifunction.IsProper` from `Chap08.Theorem_38_1`;
- `convexConjugate_rightScalarMul_eq_left_smul` from `Chap03.Theorem_16_1`;
- `adjoint` from `Chap06.Lemma_31_0_8`;
- `lowerPairing` and `IsClosedConvex` from `Chap07.Defn_34_2`.

Primitive data vs derived API:
- primitive input data: a positive scalar `lam` and a bifunction
  `F : U → X → WithBotTop 𝕜`;
- primitive source-facing owners reused here: `Bifunction.rightScalarMul F lam` and the existing
  chapter properness owner `Bifunction.IsProper`;
- derived API: convexity preservation for `Function.uncurry`, closedness preservation for
  `IsClosedConvex`, properness preservation for `Bifunction.IsProper`, the source pairing formula,
  and the adjoint scaling identity.

Layer target: `source-facing`.
-/

section Convexity

variable {𝕜 : Type*}
variable {U : Type u} {X : Type v}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

/-- Theorem 38.3, convexity clause: the positive-slice scaling `F λ` of a convex bifunction is
again convex. -/
theorem isConvex_rightScalarMul
    {F : U → X → WithBotTop 𝕜} (hF : (Function.uncurry F).IsConvex 𝕜)
    (lam : Set.Ioi (0 : 𝕜)) :
    (Function.uncurry (rightScalarMul F lam)).IsConvex 𝕜 := by
  let A : U × X →ₗ[𝕜] U × X :=
    { toFun := fun p ↦ (p.1, (lam : 𝕜)⁻¹ • p.2)
      map_add' := by
        intro p q
        ext <;> simp [smul_add]
      map_smul' := by
        intro a p
        ext
        · rfl
        · change (((lam : 𝕜)⁻¹) • (a • p.2)) = a • (((lam : 𝕜)⁻¹) • p.2)
          simp [smul_smul, mul_comm] }
  have hpre : ((Function.uncurry F) ∘ A).IsConvex 𝕜 :=
    hF.comp_linearMap A
  have hscaled :
      (fun p : U × X ↦ (lam : WithBotTop 𝕜) * F p.1 ((lam : 𝕜)⁻¹ • p.2)).IsConvex 𝕜 := by
    simpa [A, Function.comp, Function.uncurry] using
      (hpre.smul_nonneg lam.2.le)
  have hEq :
      (fun p : U × X ↦ (lam : WithBotTop 𝕜) * F p.1 ((lam : 𝕜)⁻¹ • p.2)) =
        Function.uncurry (rightScalarMul F lam) := by
    funext p
    simpa [Function.uncurry] using (rightScalarMul_apply F lam p.1 p.2).symm
  simpa [hEq] using hscaled

end Convexity

section Closedness

variable {𝕜 : Type*}
variable {U : Type u} {X : Type v}
variable [TopologicalSpace U] [TopologicalSpace X]
variable [TopologicalSpace 𝕜]
variable [CommSemiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [ContinuousSMul 𝕜 X]

/-- Theorem 38.3, closedness clause: positive slice scaling preserves the Chapter 34 owner
`IsClosedConvex`. -/
theorem isClosedConvex_rightScalarMul
    {F : U → X → WithBotTop 𝕜} (hF : IsClosedConvex F) (lam : Set.Ioi (0 : 𝕜)) :
    IsClosedConvex (rightScalarMul F lam) := by
  sorry

end Closedness

section Properness

variable {𝕜 : Type*}
variable {U : Type u} {X : Type v}
variable [CommSemiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [MulAction 𝕜 X]

/-- Theorem 38.3, properness clause: positive slice scaling preserves the Chapter 38 properness
owner `Bifunction.IsProper`. -/
theorem isProper_rightScalarMul_iff
    (F : U → X → WithBotTop 𝕜) (lam : Set.Ioi (0 : 𝕜)) :
    IsProper (rightScalarMul F lam) ↔ IsProper F := by
  sorry

end Properness

section LowerPairing

variable {𝕜 : Type*}
variable {U : Type u} {X : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [HasLinearPairing X X 𝕜]

/-- Theorem 38.3, pairing clause in owner form: the lower pairing of the scaled bifunction is the
pointwise left scalar multiple of the lower pairing of `F`. -/
theorem lowerPairing_rightScalarMul
    (F : U → X → WithBotTop 𝕜) (lam : Set.Ioi (0 : 𝕜)) :
    lowerPairing X (rightScalarMul F lam) =
      (lam : WithBotTop 𝕜) • lowerPairing X F := by
  sorry

/-- Theorem 38.3, displayed source formula:
`⟨(F λ)u, x⋆⟩ = λ ⟨Fu, x⋆⟩`. Here `⟨Fu, x⋆⟩` is the existing owner `lowerPairing F u x⋆`. -/
theorem lowerPairing_rightScalarMul_apply
    (F : U → X → WithBotTop 𝕜) (lam : Set.Ioi (0 : 𝕜)) (u : U) (xStar : X) :
    lowerPairing X (rightScalarMul F lam) u xStar =
      (lam : WithBotTop 𝕜) * lowerPairing X F u xStar := by
  simpa [Pi.smul_apply] using
    congrFun (congrFun (lowerPairing_rightScalarMul F lam) u) xStar

end LowerPairing

section Adjoint

variable {𝕜 : Type*}
variable {U : Type u} {X : Type v} {UStar : Type u} {XStar : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommGroup UStar] [Module 𝕜 UStar]
variable [AddCommMonoid XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasLinearPairing X XStar 𝕜]

/-- Theorem 38.3, adjoint clause in owner form: the adjoint of the scaled bifunction is the same
positive slice scaling of the adjoint. -/
theorem adjointFunction_rightScalarMul
    (F : U → X → WithBotTop 𝕜) (lam : Set.Ioi (0 : 𝕜)) :
    adjoint XStar UStar (rightScalarMul F lam) =
      rightScalarMul (adjoint XStar UStar F) lam := by
  sorry

/-- Pointwise form of the adjoint-scaling clause `(F λ)⋆ = F⋆ λ`. -/
@[simp] theorem adjointFunction_rightScalarMul_apply
    (F : U → X → WithBotTop 𝕜) (lam : Set.Ioi (0 : 𝕜)) (xStar : XStar) (uStar : UStar) :
    adjoint XStar UStar (rightScalarMul F lam) xStar uStar =
      rightScalarMul (adjoint XStar UStar F) lam xStar uStar := by
  simpa using congrFun (congrFun (adjointFunction_rightScalarMul F lam) xStar) uStar

end Adjoint

end Bifunction
