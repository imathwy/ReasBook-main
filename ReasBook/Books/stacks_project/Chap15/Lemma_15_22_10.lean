import Mathlib.RingTheory.Flat.TorsionFree

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: flatness and torsion theory for modules over valuation rings;
- sampled owner API:
  `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`,
  `Submodule.isTorsionFree_iff_torsion_eq_bot`,
  the instance `ValuationRing A → IsBezout A`;
- best owner abstraction: the canonical owners are `Module.Flat` and `Module.IsTorsionFree`;
- primitive data: the ring `A`, the module `M`, and the valuation-ring structure on `A`;
- derived API: the induced `IsBezout A` instance and the torsion-vanishing bridge
  `Submodule.isTorsionFree_iff_torsion_eq_bot`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma specialized to valuation rings;
  `core/canonical`: the Bezout-domain flatness criterion and the torsion-free owner predicate;
  `bridge/view`: this theorem, which specializes the canonical Bezout criterion to valuation
  rings.

No extra primitive data should be introduced here: valuation rings already carry the needed
`IsBezout` instance upstream, so the file should reuse the owner theorem directly rather than keep
any parallel local flatness-versus-torsion wrapper.
-/

section

open Module

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]

-- Proof sketch: specialize the canonical Bezout-domain criterion
-- `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout` along the valuation-ring instance
-- `IsBezout A`, then rewrite the source-facing torsion-free owner with
-- `Submodule.isTorsionFree_iff_torsion_eq_bot`.
/-- Lemma 15.22.10: for a valuation ring `A`, an `A`-module `M` is flat if and only if `M` is torsion free. -/
theorem flat_iff_isTorsionFree_of_valuationRing :
    Flat A M ↔ IsTorsionFree A M := by
  rw [Submodule.isTorsionFree_iff_torsion_eq_bot, Flat.flat_iff_torsion_eq_bot_of_isBezout]

end
