import Mathlib
import stacks_project.Chap10.Definition_10_125_1
import stacks_project.Chap10.Definition_10_135_5
import stacks_project.Chap10.Definition_10_136_1
import stacks_project.Chap10.Definition_10_136_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace Algebra

open scoped TensorProduct
open Algebra.TensorProduct

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/-- The condition that some basic open neighbourhood of `q` is syntomic over `R`. -/
def SyntomicAtPrime (R : Type u) [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ (algebraMap R (Localization.Away g)).Syntomic

/-- The condition that some basic open neighbourhood of `q` is a relative global complete
intersection over `R`. -/
def RelativeGlobalCompleteIntersectionAtPrime (R : Type u) [CommRing R] {S : Type v} [CommRing S]
    [Algebra R S] (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ IsRelativeGlobalCompleteIntersection R (Localization.Away g)

/-- The local fiber ring at `q` is a complete intersection over the residue field of the
contracted prime `q ∩ R`. -/
def FiberCompleteIntersectionAtPrime (R : Type u) [CommRing R] {S : Type v} [CommRing S]
    [Algebra R S] (q : PrimeSpectrum S) : Prop :=
  @IsCompleteIntersectionOver.{u, max u v, max u v}
    (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q) inferInstance inferInstance
    (fiberLocalRingAtResidueFieldAlgebra R S q)

/-- Some basic open neighbourhood of `q` is of finite presentation over `R`, the local map
`R_(q ∩ R) → S_q` is flat, and the local fiber ring at `q` is a complete intersection over
`κ(q ∩ R)`. -/
def FinitePresentationFlatAndFiberCompleteIntersectionAtPrime (R : Type u) [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S] (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧
    FinitePresentation R (Localization.Away g) ∧
    (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl).Flat ∧
    FiberCompleteIntersectionAtPrime R q

-- Proof sketch: `(1) → (3)` is the local fiber criterion for syntomic morphisms, while
-- `(2) → (1)` is the earlier result that relative global complete intersections are syntomic.
-- For `(3) → (2)`, shrink around `q` so that a finite presentation of `S` is available, then use
-- the complete-intersection condition on the local fiber ring together with the standard
-- presentation-theoretic argument to obtain a relative global complete intersection after another
-- localization away from `q`.
/-- Lemma 10.136.15: for a prime `q` of `S` with contracted prime `q ∩ R`, the following are
equivalent: some basic open neighbourhood of `q` is syntomic over `R`; some basic open
neighbourhood of `q` is a relative global complete intersection over `R`; and some basic open
neighbourhood of `q` is of finite presentation over `R`, the local map
`R_(q ∩ R) → S_q` is flat, and the local fiber ring at `q` is a complete intersection over
`κ(q ∩ R)`. -/
theorem syntomicAtPrime_tfae
    (q : PrimeSpectrum S) :
    List.TFAE
      [ SyntomicAtPrime R q
      , RelativeGlobalCompleteIntersectionAtPrime R q
      , FinitePresentationFlatAndFiberCompleteIntersectionAtPrime R q
      ] := sorry

end

end Algebra
