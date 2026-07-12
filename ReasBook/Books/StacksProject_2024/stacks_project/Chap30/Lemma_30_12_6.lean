import StacksProject_2024.Chap30.Lemma_30_12_4
import StacksProject_2024.Chap30.Lemma_30_12_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced `ObjectProperty.IsSerreClass` for global
-- short-exact two-out-of-three behavior. Local Lemmas 30.12.4 and 30.12.5 instead keep the
-- devissage input as a predicate `P : X.Modules → Prop` with explicit coherence hypotheses, so
-- this file follows that Chapter 30 layer.

/-- A property of coherent module sheaves satisfies the source two-out-of-three condition for
short exact sequences. -/
structure DevissageTwoOutOfThree.{u} {X : Scheme.{u}} (P : X.Modules → Prop) : Prop where
  /-- If the left and middle terms satisfy `P`, then so does the right term. -/
  right_of_left_middle {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    (h₁ : S.X₁.IsCoherent) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent)
    (hP₁ : P S.X₁) (hP₂ : P S.X₂) : P S.X₃
  /-- If the left and right terms satisfy `P`, then so does the middle term. -/
  middle_of_left_right {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    (h₁ : S.X₁.IsCoherent) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent)
    (hP₁ : P S.X₁) (hP₃ : P S.X₃) : P S.X₂
  /-- If the middle and right terms satisfy `P`, then so does the left term. -/
  left_of_middle_right {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    (h₁ : S.X₁.IsCoherent) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent)
    (hP₂ : P S.X₂) (hP₃ : P S.X₃) : P S.X₁

universe u

/-- A global two-out-of-three condition restricts to sheaves supported on any fixed closed
subscheme. -/
theorem DevissageTwoOutOfThree.onSupport
    {X : Scheme.{u}} {P : X.Modules → Prop} (hP : DevissageTwoOutOfThree P)
    (Z₀ : X.IdealSheafData) :
    DevissageTwoOutOfThreeOnSupport Z₀ P := sorry

variable {X : Scheme.{u}} [IsNoetherian X]

/-- Lemma 30.12.6: let `X` be a Noetherian scheme and let `P` be a property of coherent
`\mathcal O_X`-modules. Suppose `P` satisfies two-out-of-three for short exact sequences of
coherent modules. If for every integral closed subscheme `Z ⊆ X` with generic point `ξ` there
exists a coherent sheaf `𝒢` with support `Z`, whose generic stalk is annihilated by
`\mathfrak m_ξ`, whose residue-field fiber has dimension one, and which satisfies `P`, then
`P` holds for every coherent module on `X`. -/
@[stacks 01YI]
theorem devissagePropertyHoldsOfGenericRankOneSheaves
    (P : X.Modules → Prop)
    (h_shortExact : DevissageTwoOutOfThree P)
    (h_generic :
      ∀ (Z : X.IdealSheafData) (h_integral : IsIntegral Z.subscheme)
        (ξ : X), IsGenericPoint ξ (Z.support : Set X) →
          ∃ 𝒢 : X.Modules, DevissageGenericRankOneSheaf Z ξ P 𝒢)
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    P ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
