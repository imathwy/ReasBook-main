import Mathlib
import StacksProject_2024.Chap14.Definition_14_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open SSet.modelCategoryQuillen

universe u

section

variable {X Y : SSet.{u}} {f : X ⟶ Y}

/- Domain-style sampling for Lemma 14.30.2:
- primary domain: simplicial-set lifting properties and monomorphisms in the Quillen model
  structure;
- sampled owner declarations:
  `SSet.modelCategoryQuillen.I.rlp`,
  `CategoryTheory.MorphismProperty.monomorphisms`,
  `CategoryTheory.MorphismProperty.rlp`,
  `CategoryTheory.HasLiftingProperty`;
- best owner abstraction: `(monomorphisms SSet).rlp`;
- primitive data: the morphism `f` together with the owner property `I.rlp f` from
  Definition 14.30.1;
- derived API: the pointwise lifting statement `HasLiftingProperty i f` for a chosen monomorphism
  `i`.

Source/core/bridge triage:
- `source-facing`: a trivial Kan fibration lifts against every monomorphism of simplicial sets;
- `core/canonical`: `(monomorphisms SSet).rlp f`;
- `bridge/view`: evaluation of that owner property on a particular monomorphism `i`. -/

-- Proof sketch: reinterpret a trivial Kan fibration via
-- `I.rlp`, identify termwise injective maps of
-- simplicial sets with monomorphisms, and then use the standard closure argument to upgrade the
-- owner property from the generating boundary inclusions to all monomorphisms.
/-- Lemma 14.30.2: a trivial Kan fibration of simplicial sets has the right lifting property with
respect to any monomorphism of simplicial sets, i.e. canonically with respect to any termwise
injective map. -/
theorem boundaryInclusions_rlp_monomorphisms (hf : I.rlp f) :
    (monomorphisms SSet).rlp f := sorry

/-- Companion owner-level reformulation of Lemma 14.30.2: for simplicial sets, lifting against the
boundary inclusions is equivalent to lifting against all monomorphisms. The forward implication is
the source-facing content of the lemma; the reverse implication is the generic monotonicity of
`MorphismProperty.rlp` applied to `I_le_monomorphisms`. -/
theorem boundaryInclusions_rlp_iff_monomorphisms_rlp :
    I.rlp f ↔ (monomorphisms SSet).rlp f :=
  ⟨boundaryInclusions_rlp_monomorphisms,
    fun hmono ↦
      (show (monomorphisms SSet).rlp ≤ I.rlp from antitone_rlp I_le_monomorphisms) f hmono⟩

end
