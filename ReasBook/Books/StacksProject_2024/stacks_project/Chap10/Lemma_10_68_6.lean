import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Regular.RegularSequence

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingTheory.Sequence

/-
Domain triage:
* primary domain: regular sequences on localized modules over commutative rings;
* sampled owner API: `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.IsRegular.isQuasiRegular`,
  `RingTheory.Sequence.IsQuasiRegular.exists_away_of_atPrime`,
  `Module.mem_support_iff`;
* core/canonical owner: `RingTheory.Sequence.IsRegular M rs`;
* layer split: regularity of the successive quotients is primitive owner data, while spreading
  regularity from `M_𝔭` to some principal neighborhood `M_g` is derived bridge API.
-/

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Proof sketch: for each stage of the sequence, take the kernel of multiplication by the next
-- element on the corresponding quotient of `M`. These kernels are finite `R`-modules because `R`
-- is Noetherian and `M` is finite, and the hypothesis says their localizations at `p` vanish.
-- Clear denominators for finitely many generators of all these kernels at once to obtain
-- `g ∉ p` such that every localized kernel over `R_g` is zero, which is exactly regularity over
-- `R_g`.
/-- Lemma 10.68.6: if `R` is Noetherian, `M` is a finite `R`-module, and the image of a sequence
`xs` in `R_𝔭` is regular on `M_𝔭`, then after inverting one element outside `p` the image of `xs`
is already regular on `M_g`. -/
theorem IsRegular.exists_away_of_atPrime (p : Ideal R) [p.IsPrime] {xs : List R}
    (hxs : IsRegular (LocalizedModule.AtPrime p M)
      (xs.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ g : R, g ∉ p ∧
      IsRegular (LocalizedModule.Away g M)
        (xs.map (algebraMap R (Localization.Away g))) := sorry

end

end RingTheory.Sequence
