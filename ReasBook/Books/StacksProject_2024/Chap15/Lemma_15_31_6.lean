import Mathlib
import StacksProject_2024.Chap10.Definition_10_32_1
import StacksProject_2024.Chap10.Definition_10_69_1

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

/- Domain-style sampling for Lemma 15.31.6:
* primary domain: smooth quotients by finite quasi-regular sequences across a locally nilpotent
  thickening in commutative algebra;
* sampled owner declarations:
  `Ideal.IsLocallyNilpotent`,
  `RingTheory.Sequence.IsQuasiRegularSequence`,
  `RingTheory.Sequence.flat_quotient_of_quasiRegularSequence_mod_locallyNilpotent`,
  `Algebra.smooth_iff_forall_smoothAtPrime`;
* best owner abstraction: this theorem is `source-facing` and should remain a direct smoothness
  statement for the quotient ring, while the ambient flatness and finite presentation of
  `A' → B'` belong to the canonical algebra owners `[Module.Flat A' B']` and
  `[Algebra.FinitePresentation A' B']`;
* primitive data vs derived API: the primitive inputs are the algebra `A' → B'`, the locally
  nilpotent ideal `I`, the tuple `f'`, and the smooth closed fiber `FiberQuot`; the quotient
  presentations `FiberRing`, `FiberQuot`, and `Quot` are only bridge views.

Source/core/bridge triage:
* `source-facing`: the smoothness of `Quot` over `A'`;
* `core/canonical`: `Algebra.Smooth`, `Module.Flat`, `Algebra.FinitePresentation`,
  `Ideal.IsLocallyNilpotent`, and `IsQuasiRegularSequence`;
* `bridge/view`: the quotient models `FiberRing = B' / IB` and
  `FiberQuot = FiberRing / (fbar_1, ..., fbar_r)`.
-/

-- Proof sketch: Lemma `15.31.5` gives flatness of `Quot` over `A'`. Smoothness of the closed
-- fiber `FiberQuot` over `A' ⧸ I` implies finite presentation of `FiberQuot`, hence finite
-- presentation of `Quot` over `A'` across the locally nilpotent thickening. For every prime of
-- `Quot`, reduction modulo `I` leaves the fiber over the corresponding prime of `A'` unchanged,
-- so the fiber is smooth by
-- the hypothesis on `FiberQuot`. The flat finitely presented smooth-fiber criterion then yields
-- smoothness of `Quot` over `A'`.
/-- Lemma 15.31.6: let `A' → B'` be a flat finitely presented ring map, let `I ⊆ A'` be a locally
nilpotent ideal, and let `f'_1, \ldots, f'_r ∈ B'`. If the images of `f'_1, \ldots, f'_r` in
`B' / I B'` form a quasi-regular sequence and the quotient
`(B' / I B') / (f'_1, \ldots, f'_r)` is smooth over `A' / I`, then `B' / (f'_1, \ldots, f'_r)`
is smooth over `A'`. -/
theorem smooth_quotient_of_quasiRegularSequence_mod_locallyNilpotent
    (hI : I.IsLocallyNilpotent)
    (hqr : IsQuasiRegularSequence (List.ofFn fbar))
    (hsmooth : Algebra.Smooth (A' ⧸ I) FiberQuot) :
    Algebra.Smooth A' Quot := sorry

end

end RingTheory.Sequence
