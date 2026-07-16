import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import StacksProject_2024.stacks_project.Chap10.Definition_10_69_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-
Domain triage:
* primary domain: quasi-regular sequences in commutative algebra and their behavior under
  localization;
* sampled owner API:
  `RingTheory.Sequence.IsQuasiRegular`,
  `RingTheory.Sequence.IsQuasiRegular.of_flat_of_isBaseChange`,
  `RingTheory.Sequence.IsRegular.exists_away_of_atPrime`,
  `LocalizedModule.AtPrime`;
* source-facing layer: `RingTheory.Sequence.IsQuasiRegular M xs`;
* core/canonical owner abstractions used by this item: the source-facing predicate
  `IsQuasiRegular` together with the canonical localization owners `Localization.AtPrime`,
  `Localization.Away`, `LocalizedModule.AtPrime`, and `LocalizedModule.Away`;
* primitive vs derived split: the localized rings and modules are primitive owner data, while the
  existence of an element `g ∉ p` spreading quasi-regularity from `M_𝔭` to `M_g` is derived bridge
  API;
* layer: `bridge/view`, since the theorem transports the source-facing quasi-regularity predicate
  along the canonical localization owners without introducing any new owner-level structure.
-/

namespace RingTheory.Sequence

-- Proof sketch: let `K` be the kernel of the quasi-regular associated-graded map for `xs`.
-- Finite generation of `K` over the polynomial ring lets us choose finitely many homogeneous
-- generators. The hypothesis after localizing at `p` makes each generator vanish after inverting
-- some element outside `p`; multiplying those denominators gives `g ∉ p` killing all generators,
-- so the kernel vanishes after localizing away from `g`, which is exactly quasi-regularity there.
/-- Lemma 10.69.4: if the image of a sequence `xs` in `R_𝔭` is quasi-regular on the localized
module `M_𝔭`, then after inverting one element outside `p` the image of `xs` is already
quasi-regular on `M_g`. -/
theorem IsQuasiRegular.exists_away_of_atPrime (p : Ideal R) [p.IsPrime] {xs : List R}
    (hxs : IsQuasiRegular (LocalizedModule.AtPrime p M)
      (xs.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ g : R, g ∉ p ∧
      IsQuasiRegular (LocalizedModule.Away g M)
        (xs.map (algebraMap R (Localization.Away g))) := sorry

end RingTheory.Sequence

end
