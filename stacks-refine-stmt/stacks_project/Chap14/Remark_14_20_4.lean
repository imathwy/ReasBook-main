import Mathlib
import stacks_project.Chap14.Lemma_14_20_2
import stacks_project.Chap14.Lemma_14_20_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X : C} {V : SimplicialObject C}

/- Domain-style sampling for Remark 14.20.4:
- primary domain: augmented simplicial objects, the augmented Čech nerve adjunction, and the
  degree-`0` description of morphisms into a Čech nerve;
- sampled owner declarations:
  `SimplicialObject.cechNerveEquiv`,
  `cechNerveHomEquivZero`,
  `cechNerveHomEquivZero_symm_apply_zero_pi`,
  `augmentation_zero_simplex_face_condition`;
- best owner abstraction:
  mathlib’s owner-level abstraction is `SimplicialObject.cechNerveEquiv`, but it requires the
  global functorial wide-pullback hypothesis. Since this remark only assumes wide pullbacks for the
  single arrow `ε.app (op ⦋0⦌)`, the correct local owner in the source-faithful hypothesis profile
  is the chapter bridge `cechNerveHomEquivZero`;
- primitive data vs. derived API:
  the primitive source-facing datum is the augmentation `ε : V ⟶ const X`, while the induced
  simplicial map `augmentationToCechNerve ε : V ⟶ cechNerve (ε.app (op ⦋0⦌))` is derived from the
  identity map of `V₀` under `cechNerveHomEquivZero`;
- source/core/bridge triage:
  `source-facing`: the canonical simplicial morphism induced by an augmentation;
  `core/canonical`: `SimplicialObject.cechNerveEquiv`;
  `bridge/view`: the chapter-level degree-`0` characterization via `cechNerveHomEquivZero`.
-/

section

variable (ε : V ⟶ (SimplicialObject.const C).obj X)
variable [∀ n : ℕ, HasWidePullback (Arrow.mk (ε.app (op ⦋0⦌))).right
  (fun _ : Fin (n + 1) ↦ (Arrow.mk (ε.app (op ⦋0⦌))).left)
  (fun _ ↦ (Arrow.mk (ε.app (op ⦋0⦌))).hom)]

private def augmentationToCechNerveZeroSimplex :
    { g0 : V _⦋0⦌ ⟶ V _⦋0⦌ // V.δ 0 ≫ g0 ≫ ε.app (op ⦋0⦌) = V.δ 1 ≫ g0 ≫ ε.app (op ⦋0⦌) } :=
  ⟨𝟙 (V _⦋0⦌), by simpa using augmentation_zero_simplex_face_condition ε⟩

/-- Remark 14.20.4: an augmentation `ε : V ⟶ X` induces the canonical simplicial morphism from
`V` to the Čech nerve of its degree-`0` component `ε.app (op ⦋0⦌) : V₀ ⟶ X`. This source-facing
map is the inverse image of the identity on `V₀` under the chapter bridge
`cechNerveHomEquivZero`. -/
noncomputable def augmentationToCechNerve :
    V ⟶ ((Arrow.mk (ε.app (op ⦋0⦌))).cechNerve) :=
  (cechNerveHomEquivZero (ε.app (op ⦋0⦌)) V).symm (augmentationToCechNerveZeroSimplex ε)

@[simp] theorem augmentationToCechNerve_app_zero_pi :
    (augmentationToCechNerve ε).app (op ⦋0⦌) ≫
        WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk (ε.app (op ⦋0⦌))).hom) 0 =
      𝟙 (V _⦋0⦌) := by
  simpa [augmentationToCechNerve] using
    cechNerveHomEquivZero_symm_apply_zero_pi (ε.app (op ⦋0⦌)) V
      (augmentationToCechNerveZeroSimplex ε)

/-- The induced simplicial morphism recovers the original augmentation after composing with the
augmentation of the Čech nerve. -/
@[simp] theorem augmentationToCechNerve_comp_augmentedCechNerve_hom :
    augmentationToCechNerve ε ≫ (Arrow.mk (ε.app (op ⦋0⦌))).augmentedCechNerve.hom = ε := by
  apply (augmentHomEquivZeroSimplex V X).injective
  apply Subtype.ext
  simpa [Category.assoc, WidePullback.π_arrow] using
    congrArg (fun g0 ↦ g0 ≫ ε.app (op ⦋0⦌)) (augmentationToCechNerve_app_zero_pi ε)

end

end CategoryTheory
