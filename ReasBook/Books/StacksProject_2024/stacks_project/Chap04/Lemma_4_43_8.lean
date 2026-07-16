import StacksProject_2024.stacks_project.Chap04.Remark_4_43_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.MonoidalCategory

noncomputable section

namespace CategoryTheory

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/- Domain sampling:
- Primary domain: rigid monoidal category theory.
- Core/canonical declarations inspected:
  - `CategoryTheory.ExactPairing`
  - `CategoryTheory.tensorRightAdjunction`
  - `CategoryTheory.tensorRightTensor`
  - `CategoryTheory.Adjunction.toExactPairing`
- Owner abstraction: `ExactPairing Y X`.
- Layer triage:
  - `source-facing`: the fixed-pair statement that if `Y₁` is a left dual of `A` and `Y₂` is a
    left dual of `B`, then `Y₂ ⊗ Y₁` is a left dual of `A ⊗ B`;
  - `core/canonical`: `ExactPairing Y X`;
  - `bridge/view`: the tensor-right adjunctions `tensorRightAdjunction`, their tensor-product
    comparison isomorphisms `tensorRightTensor`, and the canonical reconstruction
    `Adjunction.toExactPairing`.
- Primitive vs. derived:
  - primitive data: the exact pairings `ExactPairing Y₁ A` and `ExactPairing Y₂ B`;
  - derived API: the composite tensor-right adjunction on `tensorRight (Y₂ ⊗ Y₁)` and the
    resulting exact pairing on `(Y₂ ⊗ Y₁, A ⊗ B)`, together with the induced
    `HasLeftDual (A ⊗ B)` instance for chosen duals.
-/

section

variable {A B Y₁ Y₂ : C} [ExactPairing Y₁ A] [ExactPairing Y₂ B]

namespace ExactPairing

private def tensorAdjunction :
    tensorRight (Y₂ ⊗ Y₁) ⊣ tensorRight (A ⊗ B) :=
  let adjComp : tensorRight Y₂ ⋙ tensorRight Y₁ ⊣ tensorRight A ⋙ tensorRight B :=
    (tensorRightAdjunction Y₂ B).comp (tensorRightAdjunction Y₁ A)
  let adjLeft : tensorRight (Y₂ ⊗ Y₁) ⊣ tensorRight A ⋙ tensorRight B :=
    adjComp.ofNatIsoLeft (tensorRightTensor Y₂ Y₁).symm
  adjLeft.ofNatIsoRight (tensorRightTensor A B).symm

private theorem tensorAdjunction_compatible :
    (tensorAdjunction : tensorRight (Y₂ ⊗ Y₁) ⊣ tensorRight (A ⊗ B)).CompatibleWithLeftTensoring := by
  -- Proof sketch: unfold the composite adjunction built from the two tensor-right adjunctions,
  -- rewrite its hom-set equivalence through `Adjunction.comp`, `ofNatIsoLeft`, and
  -- `ofNatIsoRight`, then combine the compatibility theorem
  -- `tensorRightAdjunction_compatibleWithLeftTensoring` for each input exact pairing with
  -- monoidal coherence for the comparison associators.
  sorry

/-- Lemma 4.43.8: if `Y₁` is a left dual of `A` and `Y₂` is a left dual of `B`, then
`Y₂ ⊗ Y₁` is a left dual of `A ⊗ B`. This exact pairing is canonically reconstructed from the
tensor-right adjunction of the two input pairings. -/
instance tensor : ExactPairing (Y₂ ⊗ Y₁) (A ⊗ B) :=
  tensorAdjunction.toExactPairing tensorAdjunction_compatible

end ExactPairing

end

section

variable {A B : C} [HasLeftDual A] [HasLeftDual B]

namespace HasLeftDual

/-- If two objects admit chosen left duals, then their tensor product admits the tensor product of
those duals, in reverse order, as a chosen left dual. -/
instance tensor : HasLeftDual (A ⊗ B) where
  leftDual := (ᘁB : C) ⊗ (ᘁA : C)
  exact := inferInstance

end HasLeftDual

end

end CategoryTheory
