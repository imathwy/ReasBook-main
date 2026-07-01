import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_12_2_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_0_4
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_1

noncomputable section

open scoped Rockafellar

universe u v

namespace Bifunction

section

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 38.4.1 upgrades Theorem 38.4 under closedness of the bifunction `F`
  and the function `f`, concluding that `image F f` is closed, that its defining infimum is
  attained pointwise, and that its conjugate is the closure of the adjoint-side image `F⋆ f⋆`.
- `core/canonical`: the owner declarations already present in the chapter are `Bifunction.image`,
  `Bifunction.adjoint`, `Bifunction.dom`, `Function.IsClosedProperConvex`, `riDom(·)`, and
  `lowerSemicontinuousHull`, written `cl(·)`.
- `bridge/view`: the source expressions `F⋆ f⋆` and `ri (dom F⋆)` use the same adjoint owner
  after the canonical operational view `Function.swap (F⋆)`, which matches the input order
  expected by `image` and `dom`.

Domain-style sampling used here:
- `Bifunction.image` and `Bifunction.image_apply` from `Definition_38_0_4`;
- `Bifunction.adjoint` from `Lemma_31_0_8`;
- `Bifunction.dom` and `Bifunction.IsProper` from `Theorem_38_1`;
- `Bifunction.IsClosedConvex` from `Chap07.Defn_34_2`;
- `Function.IsClosedProperConvex.biconjugate_eq`, together with the chapter notations `riDom(·)`
  and `cl(·)`.

Primitive data vs derived API:
- primitive inputs: a bifunction `F : U → X → EReal` and a function `f : U → EReal`;
- primitive owner hypotheses: `IsClosedConvex F`, the Chapter 38 properness owner `IsProper F`,
  closed proper convexity of `f`, and the common-relative-interior hypothesis on `f⋆` and
  `Function.swap (F⋆)`;
- derived API: lower semicontinuity of `image F f`, the pointwise attainment formula, and the
  conjugacy identity with `cl(image (Function.swap (F⋆)) (f⋆))`.

Layer target: `source-facing`, stated directly in the established owner language with no extra
wrapper for “closed image data” or “attainment data”.
-/

variable (F : U → X → EReal) (f : U → EReal)
variable (hF : IsClosedConvex F) (hF_proper : IsProper F)
variable (hf : f.IsClosedProperConvex)

local notation "ri(" C ")" => intrinsicInterior ℝ C

variable
    (hri :
      (riDom(f⋆) ∩ ri(dom (Function.swap (F⋆ : X → U → EReal)))).Nonempty)

-- Proof sketch: apply the closed-case upgrade of Theorem 38.4 to the source-facing owner
-- `image F f`. Closedness is recorded canonically as lower semicontinuity of the resulting
-- function, not by introducing a second owner for “closed images”.
/-- Corollary 38.4.1, closedness clause: if `F` is a closed proper convex bifunction, `f` is
closed proper convex, and `riDom(f⋆)` meets `ri (dom (Function.swap (F⋆)))`, then the image
`image F f` is closed. -/
theorem lowerSemicontinuous_image_of_common_riDom
    :
    LowerSemicontinuous (image F f) := by
  sorry

-- Proof sketch: the same closed-case regularity hypothesis yields attainment of the source
-- infimum `inf_u (f u + F u x)` for every `x`. The theorem keeps that source-facing equality
-- surface instead of repackaging attainment in an auxiliary structure.
/-- Corollary 38.4.1, attainment clause: under the same hypotheses, the infimum in the definition
of `image F f` is attained at every `x`. -/
theorem exists_eq_image_of_common_riDom
    (x : X) :
    ∃ u : U, image F f x = f u + F u x := by
  sorry

-- Proof sketch: the dual identity from Theorem 38.4 is applied on the conjugate side and then
-- converted back to the original side with closed proper convex biconjugacy. The resulting outer
-- closure is the chapter owner `cl(·)`.
/-- Corollary 38.4.1, conjugacy clause:
`(image F f)⋆ = cl(image (Function.swap (F⋆)) (f⋆))`. -/
theorem
    convexConjugate_image_eq_cl_image_adjoint_conjugate_of_common_riDom
    :
    (image F f)⋆ = cl(image (Function.swap (F⋆ : X → U → EReal)) (f⋆)) := by
  sorry

end

end Bifunction
