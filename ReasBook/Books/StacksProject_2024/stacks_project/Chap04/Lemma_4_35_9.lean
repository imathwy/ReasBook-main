import Mathlib
import StacksProject_2024.Chap04.Definition_4_35_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FibredCategoryMor

section

variable {X Y : FibredCategoryOver C}
variable (F : X ⟶ Y)

/- Domain-style sampling for Lemma 4.35.9:
- primary domain: morphisms of fibred categories over `C` and, in the source-facing textbook
  specialization, morphisms of categories fibred in groupoids;
- sampled owner-level declarations:
  `FibredCategoryMor.fiberFunctor`,
  `FibredInGroupoidsMor.fiberFunctor`,
  `FibredInGroupoidsMor.G`,
  `Functor.IsEquivalence`,
  `BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase`,
  `FibredInGroupoidsMor.IsEquivalenceOverBase`;
- best owner abstraction: the source-facing owner is `FibredInGroupoidsMor`; the faithful,
  fully faithful, and ordinary-equivalence clauses admit a canonical bridge/view generalization on
  the ambient owner `FibredCategoryMor`, while `F.IsEquivalenceOverBase` remains a derived
  upgrade over the base rather than the primary textbook owner here;
- primitive data: the owner morphism `F : FibredCategoryMor X Y`;
- derived API: the induced fiber functors `F.fiberFunctor U`, together with the source-facing
  specialization to `FibredInGroupoidsMor` and the derived over-base equivalence upgrade.

Source/core/bridge triage:
- `source-facing`: the `FibredInGroupoidsMor` faithful, fully faithful, and ordinary-equivalence
  statements below;
- `core/canonical`: `(toBasedFunctor F).Faithful`,
  `Nonempty (toBasedFunctor F).FullyFaithful`, and `(G F).IsEquivalence`;
- `bridge/view`: the ambient `FibredCategoryMor` faithful and fully faithful criteria and the
  induced fiber functors `fiberFunctor F U`; `IsEquivalenceOverBase F` is a companion upgrade
  over the base. -/

-- Proof sketch: if `F` is faithful, then its restriction to each fibre is faithful. Conversely,
-- a morphism over an arbitrary base arrow is determined by the corresponding vertical morphism
-- into a chosen pullback, so fibrewise faithfulness implies global faithfulness.
/-- Bridge/view form of Lemma 4.35.9: a morphism of fibred categories over `C` is faithful
exactly when each induced functor on the fiber over `U` is faithful. -/
theorem faithful_iff_fiberwise :
    (toBasedFunctor F).Faithful ↔ ∀ U : C, (fiberFunctor F U).Faithful := sorry

-- Proof sketch: the fully-faithful statement is proved fibrewise exactly as in the faithful case,
-- using pullbacks to reduce arbitrary morphisms over `f : U ⟶ V` to vertical morphisms in the
-- fibre over `U`.
/-- Bridge/view form of Lemma 4.35.9: a morphism of fibred categories over `C` is fully faithful
exactly when each induced functor on the fiber over `U` is fully faithful. -/
theorem fullyFaithful_iff_fiberwise :
    Nonempty (toBasedFunctor F).FullyFaithful ↔
      ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful :=
  sorry

end

end FibredCategoryMor

namespace FibredInGroupoidsMor

section

variable {X Y : FibredInGroupoidsOver C}
variable (F : X ⟶ Y)

/-- Lemma 4.35.9, faithful clause, on the source-facing owner `FibredInGroupoidsMor`. -/
theorem faithful_iff_fiberwise :
    (toBasedFunctor F).Faithful ↔ ∀ U : C, (fiberFunctor F U).Faithful := by
  simpa using FibredCategoryMor.faithful_iff_fiberwise F.toHom

/-- Lemma 4.35.9, fully faithful clause, on the source-facing owner `FibredInGroupoidsMor`. -/
theorem fullyFaithful_iff_fiberwise :
    Nonempty (toBasedFunctor F).FullyFaithful ↔
      ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful := by
  simpa using FibredCategoryMor.fullyFaithful_iff_fiberwise F.toHom

-- Proof sketch: one direction restricts a quasi-inverse of `F` to each fibre. For the converse,
-- fibrewise equivalences imply fibrewise full faithfulness and essential surjectivity; the first
-- gives global full faithfulness by the previous theorem, and the second gives global essential
-- surjectivity because every target object already lies in a fixed fibre.
/-- Lemma 4.35.9: the underlying functor of a morphism of categories fibred in groupoids over
`C` is an equivalence exactly when each induced functor on the fiber over `U` is an equivalence.
-/
theorem isEquivalence_iff_fiberwise :
    (G F).IsEquivalence ↔ ∀ U : C, (fiberFunctor F U).IsEquivalence :=
  sorry

/-- Companion to Lemma 4.35.9: under the equivalent source-facing conditions, `F` is in
particular an equivalence over the base. -/
theorem isEquivalenceOverBase_of_isEquivalence
    (hF : (G F).IsEquivalence) : IsEquivalenceOverBase F :=
  sorry

end

end FibredInGroupoidsMor

end CategoryTheory
