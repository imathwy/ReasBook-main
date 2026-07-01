import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_4_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_0_4

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
