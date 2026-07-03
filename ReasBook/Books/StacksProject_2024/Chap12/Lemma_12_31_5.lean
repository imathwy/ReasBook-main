import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap12.Lemma_12_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory.Limits

universe u v

namespace CategoryTheory

namespace SequentialInverseSystem

variable {A : Type u} [Category.{v} A] [Preadditive A]

/- Domain-style sampling for Lemma 12.31.5 in the sequential inverse-system / split-limit domain:
- sampled owner-level declarations:
  * `SequentialInverseSystem` in `Definition_12_31_2`
  * `SequentialInverseSystem.transitionMap` in `Definition_12_31_2`
  * `SequentialInverseSystem.shift` in `Definition_12_31_2`
  * `HasEventuallySplitLimit` in `Lemma_12_30_1`
  * `essentiallyConstantCofilteredDiagram_iff_hasEventuallySplitLimit` in `Lemma_12_30_1`
  * `BinaryBiproductData` in mathlib's binary-biproduct API
- best owner abstractions:
  * primitive tail owners: `SequentialInverseSystem.shift` for the shifted tail of `F`, and
    `SequentialInverseSystem` for the complementary system
  * chapter bridge owner: `HasEventuallySplitLimit`

Primitive-vs-derived split:
- primitive source-facing data: an actual limit cone `c : LimitCone F`, a tail index `N`, the
  shifted tail owner `F.shift N`, and for each shifted stage `j` a direct-sum decomposition of
  `(F.shift N).obj (op j)` into the limit object `c.cone.pt` and the `j`-th object of a
  complementary sequential inverse system `Z`, together with the induced tail comparison maps read
  directly from `(F.shift N).transitionMap` and `Z.transitionMap`.
- derived API: the owner-level criterion `HasEventuallySplitLimit F`, and hence the canonical
  essential-constancy predicate on the cofiltered diagram `F`.

Source/core/bridge triage:
- `source-facing`: `HasLimitTailDecomposition`, which is the sequential tail decomposition stated
  in the Stacks lemma.
- `core/canonical`: `HasEventuallySplitLimit F` and `IsEssentiallyConstantCofilteredDiagram F`.
- `bridge/view`: `hasEventuallySplitLimit_iff` and
  `essentiallyConstant_iff_hasLimitTailDecomposition`, which identify the source-facing sequential
  criterion with the chapter owner abstractions. -/

private def tailDecompositionMap
    {X Y Z : A} (bY : BinaryBiproductData X Y) (bZ : BinaryBiproductData X Z) (f : Y ⟶ Z) :
    bY.bicone.pt ⟶ bZ.bicone.pt :=
  let hZ : IsLimit bZ.bicone.toCone := bZ.isBilimit.isLimit
  hZ.lift (BinaryFan.mk bY.bicone.fst (bY.bicone.snd ≫ f))

/-- Lemma 12.31.5: a sequential inverse system admits a split limit tail when, after shifting by
some index `N`, the shifted system `F.shift N` is identified stagewise with the direct sum of the
actual inverse limit `c.cone.pt` and a complementary sequential inverse system `Z`, the transition
maps preserve the limit summand, and the complementary transition maps are eventually zero. -/
def HasLimitTailDecomposition (F : SequentialInverseSystem A) : Prop :=
  ∃ c : LimitCone F,
    ∃ N : ℕ,
      ∃ Z : SequentialInverseSystem A,
        ∃ B : ∀ j, BinaryBiproductData c.cone.pt (Z.obj (op j)),
          ∃ e : ∀ j, (F.shift N).obj (op j) ≅ (B j).bicone.pt,
            (∀ j, c.cone.π.app (op (N + j)) = (B j).bicone.inl ≫ (e j).inv) ∧
              (∀ {i j : ℕ} (hij : i ≤ j),
                (F.shift N).transitionMap hij =
                  (e j).hom ≫ tailDecompositionMap (B j) (B i) (Z.transitionMap hij) ≫
                    (e i).inv) ∧
                ∀ i : ℕ, ∃ j : ℕ, ∃ hij : i ≤ j, Z.transitionMap hij = 0

-- Proof sketch: pass from the owner-level criterion `HasEventuallySplitLimit F` to a cofinal tail
-- of `ℕᵒᵖ`, identify an initial full subcategory with another sequential inverse system, and
-- rewrite the splitting data from Lemma 12.30.1 as explicit biproduct decompositions of the tail
-- stages. The eventual-vanishing clause is the translated form of the condition that the
-- complementary summand is killed by some earlier transition map.
/-- Bridge theorem for Lemma 12.31.5: the chapter owner `HasEventuallySplitLimit F` is equivalent
to the explicit sequential tail decomposition with actual limit object and eventually vanishing
complementary transition maps. -/
theorem hasEventuallySplitLimit_iff [IsIdempotentComplete A] (F : SequentialInverseSystem A) :
    HasEventuallySplitLimit F ↔ HasLimitTailDecomposition F := sorry

/-- A sequential inverse system is essentially constant if and only if it admits the source-facing
tail decomposition from Lemma 12.31.5. -/
theorem essentiallyConstant_iff_hasLimitTailDecomposition [IsIdempotentComplete A]
    (F : SequentialInverseSystem A) :
    IsEssentiallyConstantCofilteredDiagram F ↔ HasLimitTailDecomposition F := by
  rw [essentiallyConstantCofilteredDiagram_iff_hasEventuallySplitLimit, hasEventuallySplitLimit_iff]

end SequentialInverseSystem

end CategoryTheory
