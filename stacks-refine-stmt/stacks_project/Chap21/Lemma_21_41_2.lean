import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v w w'

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {DA : Type w} [Category.{w} DA]
variable {DC : Type w'} [Category.{w'} DC]

variable
  (sourceUnit : SimplicialObject (Sheaf J CommRingCat.{max u v}) → DA)
variable
  (targetAsSourceModule :
    {A B : SimplicialObject (Sheaf J CommRingCat.{max u v})} → (A ⟶ B) → DA)
variable
  (structureMap :
    {A B : SimplicialObject (Sheaf J CommRingCat.{max u v})} → (α : A ⟶ B) →
      sourceUnit A ⟶ targetAsSourceModule α)
variable
  (derivedLowerShriek :
    SimplicialObject (Sheaf J CommRingCat.{max u v}) → DA ⥤ DC)
variable
  (derivedTensorWithTarget :
    {A B : SimplicialObject (Sheaf J CommRingCat.{max u v})} → (α : A ⟶ B) → DA ⥤ DA)

-- Proof sketch: resolve `K` by a bounded-above complex of termwise flat simplicial
-- `\mathcal A_\bullet`-modules so that derived tensoring with `\mathcal B_\bullet` becomes the
-- ordinary tensor product. Compute the cohomology sheaves of both sides fiberwise using
-- Lemmas `21.40.1` and `21.40.2`, and then apply the category-over-a-point comparison of
-- Lemma `21.39.12` on each fiber.
/-- Lemma 21.41.2: let `\mathcal C` be a site and let
`\alpha : \mathcal A_\bullet \to \mathcal B_\bullet` be a morphism of simplicial sheaves of
commutative rings on `\mathcal C`. In the abstract interface used here, `sourceUnit A` is a chosen
model of `\mathcal A_\bullet` in `D(\mathcal A_\bullet)`, `targetAsSourceModule α` is a chosen
model of `\mathcal B_\bullet` viewed as an `\mathcal A_\bullet`-module, `structureMap α` realizes
the map induced by `\alpha`, `derivedLowerShriek A` is a chosen model of `L\pi_! :
D(\mathcal A_\bullet) \to D(\mathcal C)`, and `derivedTensorWithTarget α` is the endofunctor
`K \mapsto K \otimes_{\mathcal A_\bullet}^{\mathbf L} \mathcal B_\bullet`. If
`L\pi_!(\mathcal A_\bullet) \to L\pi_!(\mathcal B_\bullet)` is an isomorphism, then for every
`K ∈ D(\mathcal A_\bullet)` the objects `L\pi_!(K)` and
`L\pi_!(K \otimes_{\mathcal A_\bullet}^{\mathbf L} \mathcal B_\bullet)` are canonically
isomorphic in `D(\mathcal C)`. -/
theorem derivedLowerShriek_isomorphic_after_tensor_simplicialSheafChange
    {A B : SimplicialObject (Sheaf J CommRingCat.{max u v})} (α : A ⟶ B)
    (hα : IsIso ((derivedLowerShriek A).map (structureMap α))) (K : DA) :
    IsIsomorphic
      ((derivedLowerShriek A).obj K)
      ((derivedLowerShriek A).obj ((derivedTensorWithTarget α).obj K)) := sorry

end

end CategoryTheory
