import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_4_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Lemma_38_6
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_4

noncomputable section

open scoped Rockafellar

universe u v u' v'

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup UStar] [Module ℝ UStar]
variable [AddCommGroup XStar] [Module ℝ XStar]
variable [HasLinearPairing U UStar ℝ] [HasContinuousPairing U UStar ℝ]
variable [HasLinearPairing X XStar ℝ] [HasContinuousPairing X XStar ℝ]
variable {F : U → X → EReal} {f : U → EReal} {g : X → EReal}

local notation "ri(" C ")" => intrinsicInterior ℝ C
local instance : HasPairing UStar U ℝ := HasPairing.swap
local instance : HasPairing XStar X ℝ := HasPairing.swap

local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → EReal)
local notation "f⋆" => (convexConjugate f : UStar → EReal)
local notation "g∗" => (concaveConjugate g : XStar → EReal)
local notation "adjointUpperImage" =>
  upperPerturbationFunction (fun uStar xStar ↦ g∗ xStar - F⋆ xStar uStar)
local notation "inverseUpperImage" =>
  upperPerturbationFunction (fun u x ↦ g x - F _* x u)
local notation "adjointImage" =>
  image (Function.swap F⋆) f⋆

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 38.7 is the four-term Chapter 38 duality chain
  `⟨Ff, g^*⟩ = ⟨f, F^* g^*⟩ = -⟨f^*, F_* g⟩ = -⟨F^*_* f^*, g⟩`.
- `core/canonical`: the owner layer is already present in the project as `Bifunction.image`,
  `Bifunction.adjoint`, `Bifunction.inverse`, `Bifunction.upperPerturbationFunction`,
  `Function.innerProduct`, and the conjugate owners `f⋆` and `g∗`.
- `bridge/view`: no new owner is introduced here; the source term `F^* g^*` is written directly
  with the canonical owner `upperPerturbationFunction`, while `F_* g` and `F^*_* f^*` are kept as
  local notation for repeated canonical expressions.

Primary mathematical domain:
- convex bifunction duality and Chapter 38 inner products under a relative-interior qualification.

Domain-style sampling used here:
- `Bifunction.image` from `Definition_38_0_4`;
- `Bifunction.adjoint` from `Definition_6_30_14`;
- `Bifunction.inverse` from `Definition_36_4_1`;
- `Bifunction.upperPerturbationFunction` from `Definition_6_30_11`;
- `Bifunction.convexConjugate_image_eq_image_adjoint_conjugate_of_common_riDom` from
  `Theorem_38_4`;
- `Function.hasInnerProduct_convexConjugate_concaveConjugate`,
  `Function.innerProduct_convexConjugate_concaveConjugate_eq_neg`,
  `Function.hasInnerProduct_lowerSemicontinuousHull_concaveClosure`, and
  `Function.innerProduct_lowerSemicontinuousHull_concaveClosure_eq` from `Lemma_38_6`.

Primitive data vs derived API:
- primitive inputs: a convex bifunction `F`, a proper convex function `f`, and a proper concave
  function `g`;
- primitive owner layer already upstream: `image F f`, `F⋆`, `F _*`, `upperPerturbationFunction`,
  `Function.innerProduct`, and `Function.HasInnerProduct`;
- derived API here: existence of the four Chapter 38 inner products under the source slicewise
  relative-interior qualification, together with the three atomic equalities making up the
  displayed chain in Theorem 38.7.

Layer target: `source-facing`, stated directly in the existing owner language on the paired spaces
`U/UStar` and `X/XStar` rather than on an unnecessary self-dual specialization.
-/

variable (hF_convex : (Function.uncurry F).IsConvex ℝ)
variable (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
variable (hg_concave : g.IsConcave ℝ) (hg_proper : (-g).IsProper)
variable
  (hqual :
    ∃ u : U,
      u ∈ riDom(f) ∩ ri(dom F) ∧
        (riDom(F u) ∩ riDom(-g)).Nonempty)

-- Proof sketch: use the source qualification to derive the relative-interior hypothesis needed
-- for the pair `(image F f, g∗)`, then combine the image/adjoint conjugacy theorem of
-- Theorem 38.4 with the Chapter 38.5 existence criterion for function inner products.
/-- The first two Chapter 38 inner products in Theorem 38.7 exist under the source slicewise
relative-interior qualification. -/
theorem hasInnerProduct_image_concaveConjugate_and_adjointUpperImage_of_qualification :
    Function.HasInnerProduct (image F f) g∗ ∧
      Function.HasInnerProduct f adjointUpperImage := sorry

-- Proof sketch: first apply the preceding existence theorem to the qualified pair
-- `(image F f, g∗)`. Then rewrite the conjugate of `image F f` by Theorem 38.4 as the adjoint-side
-- image of `f⋆`, and use the Theorem 38.7 duality argument to identify the common inner-product
-- value with the adjoint-side upper image of `g∗`.
/-- Theorem 38.7: under the source slicewise relative-interior qualification,
`⟨Ff, g^*⟩ = ⟨f, F^* g^*⟩`, rendered in the chapter owner language as the equality between the
inner product of `image F f` with `g∗` and the inner product of `f` with the adjoint-side upper
image of `g∗`. This is the first equality in the displayed chain
`⟨Ff, g^*⟩ = ⟨f, F^* g^*⟩ = -⟨f^*, F_* g⟩ = -⟨F^*_* f^*, g⟩`. -/
theorem innerProduct_image_concaveConjugate_eq_innerProduct_adjointUpperImage_of_qualification :
    Function.innerProduct (image F f) g∗ =
      Function.innerProduct f adjointUpperImage := sorry

-- Proof sketch: reinterpret the source theorem for the inverse bifunction `F _*`, using the same
-- slicewise relative-interior hypothesis in the swapped orientation. This yields existence of the
-- Chapter 38 inner products for `(f⋆, inverseUpperImage)` and `(adjointImage, g)`.
/-- The last two Chapter 38 inner products in Theorem 38.7 exist under the same source
qualification. Here `inverseUpperImage` is the source term `F_* g`, and `adjointImage` is the
source term `F^*_* f^*`. -/
theorem hasInnerProduct_convexConjugate_inverseUpperImage_and_adjointImage_of_qualification :
    Function.HasInnerProduct f⋆ inverseUpperImage ∧
      Function.HasInnerProduct adjointImage g := sorry

-- Proof sketch: apply the inverse-bifunction form of the same strong-duality argument used for
-- the main theorem. The resulting equality is exactly the middle equality in the source chain,
-- written with the canonical owner `upperPerturbationFunction` for `F_* g`.
/-- The middle equality in Theorem 38.7: the inner product of `f` with the adjoint-side upper
image of `g∗` equals the negative of the inner product of `f⋆` with the inverse-side upper image
of `g`. -/
theorem innerProduct_adjointUpperImage_eq_neg_innerProduct_inverseUpperImage_of_qualification :
    Function.innerProduct f adjointUpperImage =
      -Function.innerProduct f⋆ inverseUpperImage := sorry

-- Proof sketch: rewrite `adjointImage` by Theorem 38.4 as the conjugate of `image F f`, then
-- apply Lemma 38.6 to the qualified pair `(image F f, g∗)` and simplify the double sign change.
/-- The final equality in Theorem 38.7 after cancelling the common minus sign:
the inner product of `f⋆` with the inverse-side upper image of `g` equals the inner product of
the adjoint image `image (Function.swap F⋆) (f⋆)` with `g`. -/
theorem innerProduct_inverseUpperImage_eq_innerProduct_adjointImage_of_qualification :
    Function.innerProduct f⋆ inverseUpperImage =
      Function.innerProduct adjointImage g := sorry

end

end Bifunction
