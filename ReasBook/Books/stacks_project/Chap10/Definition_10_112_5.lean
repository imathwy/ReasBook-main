import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open PrimeSpectrum
open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

/-- The prime of the fiber ring `κ(q ∩ R) ⊗[R] S` corresponding to `q : Spec S`. -/
abbrev fiberPrimeAt (q : PrimeSpectrum S) : PrimeSpectrum ((q.asIdeal.under R).Fiber S) :=
  preimageEquivFiber R S (comap (algebraMap R S) q) ⟨q, rfl⟩

/-- Definition 10.112.5: for a prime `q : Spec S`, the local ring of the fiber at `q` is the
local ring of the fiber ring `κ(q ∩ R) ⊗[R] S` at the corresponding prime. -/
def fiberLocalRingAt (q : PrimeSpectrum S) : Type _ :=
  Localization.AtPrime (fiberPrimeAt R S q).asIdeal

/-- The local ring of the fiber at `q` is canonically a commutative ring. -/
instance fiberLocalRingAtCommRing (q : PrimeSpectrum S) : CommRing (fiberLocalRingAt R S q) := by
  change CommRing (Localization.AtPrime (fiberPrimeAt R S q).asIdeal)
  infer_instance

/-- The local ring of the fiber at `q` is canonically a local ring. -/
instance fiberLocalRingAtIsLocalRing (q : PrimeSpectrum S) : IsLocalRing (fiberLocalRingAt R S q) := by
  change IsLocalRing (Localization.AtPrime (fiberPrimeAt R S q).asIdeal)
  infer_instance

/-- The local ring of the fiber at `q` is canonically a module over itself. -/
instance fiberLocalRingAtModule (q : PrimeSpectrum S) :
    Module (fiberLocalRingAt R S q) (fiberLocalRingAt R S q) :=
  Semiring.toModule

/-- The local ring of the fiber at `q` is canonically an algebra over the fiber ring. -/
instance fiberLocalRingAtFiberAlgebra (q : PrimeSpectrum S) :
    Algebra ((q.asIdeal.under R).Fiber S) (fiberLocalRingAt R S q) := by
  change Algebra ((q.asIdeal.under R).Fiber S)
    (Localization.AtPrime (fiberPrimeAt R S q).asIdeal)
  infer_instance

/-- The local ring of the fiber at `q` is canonically an algebra over the residue field
`κ(q ∩ R)`. -/
noncomputable instance fiberLocalRingAtResidueFieldAlgebra (q : PrimeSpectrum S) :
    Algebra (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q) := by
  change Algebra (q.asIdeal.under R).ResidueField
    (Localization.AtPrime (fiberPrimeAt R S q).asIdeal)
  infer_instance

/-- The canonical ring map `S → (κ(q ∩ R) ⊗[R] S)_(\bar q)` to the local fiber ring at `q`. -/
abbrev toFiberLocalRingAt (q : PrimeSpectrum S) : S →+* fiberLocalRingAt R S q :=
  (algebraMap ((q.asIdeal.under R).Fiber S) (fiberLocalRingAt R S q)).comp
    (includeRight : S →ₐ[R] ((q.asIdeal.under R).Fiber S)).toRingHom

/-- The local ring of the fiber at `q` is canonically an `S`-algebra. -/
noncomputable instance fiberLocalRingAtAlgebra (q : PrimeSpectrum S) :
    Algebra S (fiberLocalRingAt R S q) :=
  RingHom.toAlgebra (toFiberLocalRingAt R S q)

/-- The local ring of the fiber at `q` is the localization of the fiber ring at the prime
corresponding to `q`. -/
-- Proof sketch: unfold `fiberLocalRingAt`; it is defined to be `Localization.AtPrime` of the
-- corresponding prime `fiberPrimeAt q`, so the standard localization instance applies.
instance fiberLocalRingAtIsLocalization (q : PrimeSpectrum S) :
    IsLocalization.AtPrime (fiberLocalRingAt R S q) (fiberPrimeAt R S q).asIdeal := by
  change IsLocalization.AtPrime (Localization.AtPrime (fiberPrimeAt R S q).asIdeal)
    (fiberPrimeAt R S q).asIdeal
  infer_instance

theorem fiberLocalRingAt_isLocalization (q : PrimeSpectrum S) :
    IsLocalization.AtPrime (fiberLocalRingAt R S q) (fiberPrimeAt R S q).asIdeal :=
  fiberLocalRingAtIsLocalization R S q

end

namespace PrimeSpectrum

section

variable {S : Type v} [CommRing S]

/-- The images of `fs : List S` in the local fiber ring at `q` form a regular sequence. This is
the thin pointwise bridge from the owner fiber local ring `fiberLocalRingAt R S q` to the
canonical predicate `RingTheory.Sequence.IsRegular`. -/
def IsRegularInFiberLocalRing (q : PrimeSpectrum S) (R : Type u) [CommRing R] [Algebra R S]
    (fs : List S) : Prop := by
  exact
    @RingTheory.Sequence.IsRegular (fiberLocalRingAt R S q) (fiberLocalRingAt R S q)
      _ _ (fiberLocalRingAtModule R S q) (fs.map (toFiberLocalRingAt R S q))

end

end PrimeSpectrum
