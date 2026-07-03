import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_38_3_1 (from Chap08) -/
noncomputable section

universe u v w

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: the Chapter 8 owner for the image `Ff` of a function `f` under a bifunction `F`
  is already `Bifunction.image`, introduced in `Definition_38_0_4` with the source formula
  `x ↦ inf_u (f u + F u x)`.
- `core/canonical`: the underlying owner abstraction remains Chapter 6's
  `Bifunction.perturbationFunction`, together with Chapter 7's inverse notation `F _*`.
- `bridge/view`: this file records the equivalent inverse-slice presentation from Definition
  38.3.1, `inf_u (f u - (F_* x) u)`, and the corresponding Chapter 1 linear-image bridge in that
  inverse-slice form.

Domain-style sampling used here:
- `Bifunction.image` and `Bifunction.image_apply` from `Chap08.Definition_38_0_4`;
- inverse notation `F _*` and theorem `Bifunction.inverse_apply` from
  `Chap07.Definition_36_4_1`;
- `Bifunction.perturbationFunction_apply` and
  `Bifunction.perturbationFunction_eq_linearImage_fst` from
  `Chap06.Definition_6_29_1`.

Primitive data vs derived API:
- primitive source data: the bifunction `F : U → X → WithBotTop α` and the function
  `f : U → WithBotTop α`;
- primitive owner: the existing chapter declaration `Bifunction.image F f`;
- derived API here: the inverse-slice evaluation formula and its linear-image restatement.

Layer target: `bridge/view`. The file therefore recalls the existing owner instead of introducing
a second public `def image`.
-/

/- Definition 38.3.1 reuses the Chapter 8 owner `Bifunction.image`; this file only adds the
inverse-slice companion formulas. -/
recall Bifunction.image

/- The additive pointwise formula `x ↦ inf_u (f u + F u x)` is already the canonical companion
theorem for the owner. -/
recall Bifunction.image_apply

section

variable {U : Type u} {X : Type v} {α : Type*}
variable [ConditionallyCompleteLattice α] [Add α] [InvolutiveNeg α]

/-- Definition 38.3.1: evaluating `image F f` at `x` also gives the inverse-slice formula
`inf_u (f u - (F_* x) u)`. -/
@[simp] theorem image_apply_eq_iInf_sub_inverse
    (F : U → X → WithBotTop α) (f : U → WithBotTop α) (x : X) :
    image F f x = ⨅ u : U, f u - F _* x u := by
  simpa [WithBotTop.sub_eq_add_neg] using image_apply F f x

end

section

variable {𝕜 : Type w} {U : Type u} {X : Type v} {α : Type*}
variable [Semiring 𝕜]
variable [ConditionallyCompleteLattice α] [Add α] [InvolutiveNeg α]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

/-- Under the Chapter 1 module owner layer over `𝕜`, `image F f` is the linear image of the
inverse-slice kernel under projection to the `x`-coordinate. -/
theorem image_eq_linearImage_fst
    (F : U → X → WithBotTop α) (f : U → WithBotTop α) :
    image F f =
      (LinearMap.fst 𝕜 X U) ◁ Function.uncurry (fun x u ↦ f u - F _* x u) := by
  calc
    image F f = perturbationFunction (fun x u ↦ f u - F _* x u) := by
      funext x
      rw [perturbationFunction_apply]
      exact image_apply_eq_iInf_sub_inverse F f x
    _ = (LinearMap.fst 𝕜 X U) ◁ Function.uncurry (fun x u ↦ f u - F _* x u) := by
      simpa [LinearMap.fst_apply] using
        (perturbationFunction_eq_linearImage_fst
          (U := X) (X := U)
          (fun x u ↦ f u - F _* x u))

end

end Bifunction

/-! ### Proposition_38_3_2 (from Chap08) -/
noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.3.2 identifies the image of a function under the convex
  indicator bifunction of a linear map `A` with the ordinary Chapter 1 image of that function
  under `A`.
- `core/canonical`: the two existing owners are `Bifunction.image` for bifunction images and
  `Function.linearImage` for fiberwise infima along a linear map; the singleton-indicator
  bifunction attached to `A` is the graph owner `graphIndicator 𝕜 A`.
- `bridge/view`: this item is therefore a direct equality between existing owner-level
  constructions, not a place to introduce a new wrapper for “image under an indicator bifunction”.

Domain-style sampling used here:
- `Bifunction.image` from `Chap08.Definition_38_0_4`;
- `Bifunction.graphIndicator` from `Chap06.Definition_6_29_9`;
- `Function.linearImage` and `Function.linearImage_eq_sInf_image` from `Chap01.Theorem_5_7`.

Primitive data vs derived API:
- primitive source data: a linear map `A : U →ₗ[𝕜] X` and a function `f : U → WithBotTop 𝕜`;
- primitive owners reused directly: `image`, `graphIndicator`, and `Function.linearImage`;
- derived API here: only the bridge equality between the two source-facing image constructions.

Source-faithful assumption note: Rockafellar states the result for a function that does not take
the value `-∞`. In the project's `WithBotTop 𝕜` owner layer, that hypothesis is the non-bottom
condition `∀ u, f u ≠ ⊥`; convexity is unused in this identity.

Layer target: `bridge/view`.
-/

section

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

-- Proof sketch: expand `image (graphIndicator 𝕜 A) f` pointwise using `image_apply`. For a
-- fixed `x`, the singleton-indicator term is `0` exactly on the fiber `A u = x` and `⊤`
-- otherwise, so the infimum reduces to the fiberwise infimum of `f`. That is exactly the Chapter
-- 1 owner `Function.linearImage A f`.
/-- Proposition 38.3.2: for the singleton-indicator bifunction of a linear map `A`, the Chapter 8
image of `f` agrees with the Chapter 1 linear image `A ◁ f`; equivalently, the infimum defining
`image (graphIndicator 𝕜 A) f` is taken over the fiber `A u = x` provided `f` never takes the
value `-∞`. -/
theorem image_graphIndicator_eq_linearImage
    (A : U →ₗ[𝕜] X) (f : U → WithBotTop 𝕜) (hf : ∀ u, f u ≠ ⊥) :
    image (graphIndicator 𝕜 A) f = A ◁ f := by
  classical
  funext x
  let fiber : Set U := {u : U | A u = x}
  calc
    image (graphIndicator 𝕜 A) f x
        = ⨅ u : U, if u ∈ fiber then f u else ⊤ := by
            rw [image_apply]
            apply iInf_congr
            intro u
            by_cases hu : u ∈ fiber
            · have hux : A u = x := by
                simpa [fiber] using hu
              have hxu : x = A u := hux.symm
              calc
                f u + graphIndicator 𝕜 A u x
                    = f u + (if x = A u then (0 : WithBotTop 𝕜) else ⊤) := by
                        rw [graphIndicator_cases]
                _ = f u := by simp [hxu]
                _ = if u ∈ fiber then f u else ⊤ := by simp [hu]
            · have hux : A u ≠ x := by
                simpa [fiber] using hu
              have hxu : x ≠ A u := by
                simpa [eq_comm] using hux
              calc
                f u + graphIndicator 𝕜 A u x
                    = f u + (if x = A u then (0 : WithBotTop 𝕜) else ⊤) := by
                        rw [graphIndicator_cases]
                _ = ⊤ := by
                      rw [if_neg hxu]
                      exact (WithBotTop.add_top_iff_ne_bot).2 (hf u)
                _ = if u ∈ fiber then f u else ⊤ := by simp [hu]
    _ = ⨅ u ∈ fiber, f u := by
          rw [iInf_ite]
          simp
    _ = (A ◁ f) x := by
          by_cases hfiber : fiber.Nonempty
          · letI : Nonempty U := ⟨hfiber.some⟩
            have hbelow : BddBelow (Set.range fun u : fiber ↦ f u) := by
              refine ⟨⊥, ?_⟩
              rintro _ ⟨u, rfl⟩
              exact bot_le
            have htop : ⨅ u : fiber, f u ≤ sInf (∅ : Set (WithBotTop 𝕜)) := by
              simp
            rw [Function.linearImage_eq_sInf_image]
            simpa [fiber] using (csInf_image hfiber hbelow htop).symm
          · rw [Function.linearImage_eq_sInf_image]
            have hempty : fiber = ∅ := Set.not_nonempty_iff_eq_empty.mp hfiber
            simp [fiber, hempty]

end

end Bifunction

/-! ### Theorem_38_3 (from Chap08) -/
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
