import Mathlib
import StacksProject_2024.Chap15.Definition_15_37_3
import StacksProject_2024.Chap15.Definition_15_112_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsExtensionOfDiscreteValuationRings
open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]

/- Domain-style sampling for Lemma 15.112.5:
- primary domain: extensions of discrete valuation rings, formal smoothness for the maximal-ideal
  adic topology, and weak ramification on maximal ideals and residue fields;
- sampled owner declarations:
  `RingHom.formally_smooth_for_adic`,
  `IsExtensionOfDiscreteValuationRings.WeaklyUnramified`,
  `IsExtensionOfDiscreteValuationRings.weaklyUnramified_iff_map_maximalIdeal`,
  `flat_geometricallyRegularSpecialFiber_formallySmooth_tfae`;
- best owner abstraction: the formal smoothness side is owned by
  `RingHom.formally_smooth_for_adic`, while weak ramification is owned by `WeaklyUnramified`; the
  maximal-ideal equality is only a bridge view of the latter, not primitive public data;
- primitive-vs-derived split: the primitive data are the DVR extension structure
  `[IsExtensionOfDiscreteValuationRings A B]`, while the maximal-ideal equality and the formal
  smoothness criterion are derived API.

Source/core/bridge triage:
- `source-facing`: the equivalence in Lemma 15.112.5;
- `core/canonical`: `(algebraMap A B).formally_smooth_for_adic (maximalIdeal B)` and
  `WeaklyUnramified A B`;
- `bridge/view`: `weaklyUnramified_iff_map_maximalIdeal`.
-/

-- Proof sketch: apply Proposition `15.40.5` to the local map `A → B`. For extensions of
-- discrete valuation rings, flatness is automatic from torsion-freeness, while the special fiber
-- over `ResidueField A` is a field. Then use Proposition `10.158.9` and the field-extension
-- criterion for geometric regularity versus formal smoothness to identify geometric regularity of
-- the special fiber with separability of `ResidueField B / ResidueField A`; in this DVR setting,
-- weakly unramified is the canonical owner `WeaklyUnramified A B`, with
-- `weaklyUnramified_iff_map_maximalIdeal` as the maximal-ideal bridge.
/-- Lemma 15.112.5: for an extension `A ⊆ B` of discrete valuation rings, the map `A → B` is
formally smooth for the `maximalIdeal B`-adic topology if and only if `A ⊆ B` is weakly
unramified and the residue field extension `ResidueField B / ResidueField A` is separable. -/
@[stacks 09E7]
theorem formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField :
    (algebraMap A B).formally_smooth_for_adic (maximalIdeal B) ↔
      WeaklyUnramified A B ∧
        Algebra.IsSeparable (ResidueField A) (ResidueField B) := sorry

end
