import Mathlib
import stacks_project.Chap04.Lemma_4_31_13
import stacks_project.Chap04.Lemma_4_34_1
import stacks_project.Chap04.Lemma_4_35_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

universe v u

namespace CategoryTheory

/- Internal categorical bridge: a functor is fully faithful exactly when its canonical diagonal
into the categorical self-pullback is an equivalence. -/
private theorem fullyFaithful_iff_diagonal_to_self_pullback_isEquivalence
    {A : Type (max u v)} {B : Type (max u v)}
    [Category.{v} A] [Category.{v} B]
    (F : A ⥤ B) :
    Nonempty F.FullyFaithful ↔
      (Δₚ F).IsEquivalence := sorry

section

variable {C : Type (max u v)} {S : Type (max u v)} {S' : Type (max u v)}
  [Category.{v} C] [Category.{v} S] [Category.{v} S']
variable {p : S ⥤ C} {p' : S' ⥤ C} [IsFibredInGroupoids p] [IsFibredInGroupoids p']
variable (F : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p')

local instance : IsFibredInGroupoids (BasedCategory.ofFunctor p).p := by
  simpa using (inferInstance : IsFibredInGroupoids p)

local instance : IsFibredInGroupoids (BasedCategory.ofFunctor p').p := by
  simpa using (inferInstance : IsFibredInGroupoids p')

/- Domain-style sampling for the auxiliary bridge layer of Lemma 4.35.10:
- primary domain: based functors between categories fibred in groupoids over a fixed base and the
  canonical diagonal functor over that base;
- sampled owner-level declarations:
  `FibredInGroupoidsMor`,
  `FibredInGroupoidsOver.twoFibreProduct`,
  `FibredInGroupoidsMor.diagonalMor`,
  `relativeDiagonalOver`,
  `FibredInGroupoidsMor.fullyFaithful_iff_fiberwise`;
- best owner abstraction for the final source-facing statement: `FibredInGroupoidsMor`; the raw
  `BasedFunctor` theorem here is the bridge/view used to prove that owner-level statement;
- primitive data at this bridge layer: only the based functor `F`;
- derived API: the diagonal equivalence-over-base criterion and its fiberwise restatement.

Source/core/bridge triage:
- `source-facing`: the bundled `FibredInGroupoidsMor` theorem stated below;
- `core/canonical`: `Nonempty F.FullyFaithful`,
  `F.relativeDiagonalOver.IsEquivalenceOverBase`;
- `bridge/view`: the comparison between the raw diagonal-over-base criterion and the diagonal of
  each fiber functor. -/

-- Proof sketch: apply Lemma `4.35.9` to the diagonal based functor over `C`, so the global
-- diagonal equivalence criterion reduces to equivalence on each fiber. On the fiber over `U`, the
-- owner-level relative diagonal `BasedFunctor.relativeDiagonalOver F` specializes to the
-- explicit self-`2`-fibre-product model from Lemma `4.35.7`. On each fiber over `U`, its induced
-- functor is the canonical diagonal `Δₚ (F.fiberFunctor U)`.
private theorem basedFunctor_diagonal_isEquivalenceOverBase_iff_fiberwise :
    F.relativeDiagonalOver.IsEquivalenceOverBase ↔
      ∀ U : C, (Δₚ (F.fiberFunctor U)).IsEquivalence := sorry

-- Proof sketch: the textbook statement is the global diagonal criterion in `Cat/C`, realized by
-- the explicit fibred `2`-fibre-product model from Lemma `4.35.7`.
end

namespace FibredInGroupoidsMor

section

open FibredInGroupoidsOver

variable {C : Type (max u v)} [Category.{v} C]
variable {X Y : FibredInGroupoidsOver.{v, max u v, max u v, v} C}
variable (F : X ⟶ Y)

/- Domain-style sampling for Lemma 4.35.10:
- primary domain: morphisms of categories fibred in groupoids over a fixed base together with
  their canonical diagonal into the fibred self-`2`-fibre product;
- sampled owner-level declarations:
  `FibredInGroupoidsMor`,
  `FibredInGroupoidsOver.twoFibreProduct`,
  `FibredInGroupoidsMor.diagonalMor`,
  `FibredInGroupoidsMor.fiberFunctor`,
  `FibredInGroupoidsMor.IsEquivalenceOverBase`;
- best owner abstraction: the morphism `F : FibredInGroupoidsMor X Y`, with the target owner
  `FibredInGroupoidsOver.twoFibreProduct F F` and the bundled canonical diagonal `F.diagonalMor`;
- primitive data: only the owner morphism `F`;
- derived API: the fully-faithful criterion expressed directly in terms of the canonical diagonal
  over-base equivalence predicate.

Source/core/bridge triage:
- `source-facing`: Lemma 4.35.10 on `FibredInGroupoidsMor`;
- `core/canonical`: `Nonempty F.FullyFaithful` and the owner predicate
  `F.diagonalMor.IsEquivalenceOverBase`;
- `bridge/view`: the raw `BasedFunctor` diagonal criterion above. -/

/-- Companion bridge: the owner-level diagonal of `F` is an equivalence over the base exactly
when the induced diagonal on every fiber is an equivalence. -/
theorem diagonal_isEquivalenceOverBase_iff_fiberwise :
    IsEquivalenceOverBase (diagonalMor F) ↔
      ∀ U : C, (Δₚ (fiberFunctor F U)).IsEquivalence := by
  simpa [FibredInGroupoidsMor.diagonalMor] using
    basedFunctor_diagonal_isEquivalenceOverBase_iff_fiberwise (toBasedFunctor F)

/-- Lemma 4.35.10: a morphism of categories fibred in groupoids over `C` is fully faithful if and
only if its canonical diagonal into the fibred self-`2`-fibre product is an equivalence over
`C`. The target is the chapter owner `FibredInGroupoidsOver.twoFibreProduct F F`, and the
diagonal is the bundled owner morphism `F.diagonalMor`.
-/
theorem fullyFaithful_iff_diagonal_isEquivalenceOverBase :
    Nonempty (toBasedFunctor F).FullyFaithful ↔ IsEquivalenceOverBase (diagonalMor F) := by
  rw [diagonal_isEquivalenceOverBase_iff_fiberwise, fullyFaithful_iff_fiberwise]
  constructor
  · intro hF U
    exact
      (fullyFaithful_iff_diagonal_to_self_pullback_isEquivalence (fiberFunctor F U)).mp (hF U)
  · intro hΔ U
    exact
      (fullyFaithful_iff_diagonal_to_self_pullback_isEquivalence (fiberFunctor F U)).mpr (hΔ U)

end

end FibredInGroupoidsMor

end CategoryTheory
