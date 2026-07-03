import Mathlib
import stacks_project.Chap10.Definition_10_32_1
import stacks_project.Chap10.Definition_10_69_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open RingTheory

namespace RingTheory.Sequence

section

variable {A' : Type u} [CommRing A']
variable {B' : Type u} [CommRing B'] [Algebra A' B']
variable [Module.Flat A' B'] [Algebra.FinitePresentation A' B']

variable {I : Ideal A'} {r : ℕ} (f' : Fin r → B')

local notation "IB" => Ideal.map (algebraMap A' B') I
local notation "FiberRing" => B' ⧸ IB
local notation "fbar" => fun i : Fin r ↦ Ideal.Quotient.mk IB (f' i)
local notation "FiberQuot" => FiberRing ⧸ Ideal.span (Set.range fbar)
local notation "Quot" => B' ⧸ Ideal.span (Set.range f')

/- Domain-style sampling for Lemma 15.31.5:
* primary domain: flatness of quotients by finite quasi-regular sequences across a locally
  nilpotent thickening in commutative algebra;
* sampled owner declarations:
  `Ideal.IsLocallyNilpotent`,
  `RingTheory.Sequence.IsQuasiRegularSequence`,
  `RingTheory.Sequence.isQuasiRegularSequence_baseChange_of_flat_quotient`,
  `flat_over_middleRing_of_locallyNilpotent_of_flat_over_base_and_flat_mod_extended_ideal`;
* best owner abstraction: the theorem itself is `source-facing` and should stay a direct flatness
  statement for the quotient ring `B' ⧸ (f'_1, ..., f'_r)`, but the ambient flatness and finite
  presentation of `A' → B'` belong to the canonical algebra owners `[Module.Flat A' B']` and
  `[Algebra.FinitePresentation A' B']`;
* primitive data vs derived API: the primitive data are the algebra `A' → B'`, the locally
  nilpotent ideal `I`, and the tuple `f'`; the quotient presentations `FiberRing`, `FiberQuot`,
  and `Quot` are only bridge views, and the quasi-regularity hypothesis serves only to supply the
  closed-fiber flatness input.

Source/core/bridge triage:
* `source-facing`: the flatness of `Quot` over `A'`;
* `core/canonical`: `Module.Flat`, `Algebra.FinitePresentation`, `Ideal.IsLocallyNilpotent`, and
  `IsQuasiRegularSequence`;
* `bridge/view`: the quotient models `FiberRing = B' / IB` and
  `FiberQuot = FiberRing / (fbar_1, ..., fbar_r)`.
-/

-- Proof sketch: localize at a prime of `Quot` and use the local criterion for flatness. The
-- ambient owners `[Module.Flat A' B']` and `[Algebra.FinitePresentation A' B']` provide the
-- finitely presented flat map needed to invoke the fiberwise criterion on the localized diagram,
-- reducing to regularity in the fiber. Lemma `15.31.4` gives quasi-regularity after passage to
-- the fiber, and Lemma `15.30.7` upgrades quasi-regularity to regularity in the Noetherian local
-- fiber ring, yielding flatness of `Quot` over `A'`.
/-- Lemma 15.31.5: let `A' → B'` be a flat finitely presented ring map, let `I ⊆ A'` be a locally
nilpotent ideal, and let `f'_1, \ldots, f'_r ∈ B'`. If the images of `f'_1, \ldots, f'_r` in
`B' / I B'` form a quasi-regular sequence and the quotient `(B' / I B') / (f'_1, \ldots, f'_r)`
is flat over `A' / I`, then `B' / (f'_1, \ldots, f'_r)` is flat over `A'`. -/
theorem flat_quotient_of_quasiRegularSequence_mod_locallyNilpotent
    (hI : I.IsLocallyNilpotent)
    (hqr : IsQuasiRegularSequence (List.ofFn fbar))
    (hquot : Module.Flat (A' ⧸ I) FiberQuot) :
    Module.Flat A' Quot := sorry

end

end RingTheory.Sequence
