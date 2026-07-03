import Mathlib
import StacksProject_2024.Chap10.Definition_10_104_6
import StacksProject_2024.Chap10.Definition_10_125_1
import StacksProject_2024.Chap10.Proposition_10_102_9
import StacksProject_2024.Chap10.Situation_10_102_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open CategoryTheory ChainComplex HomologicalComplex
open scoped TensorProduct

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {e : ℕ}

namespace FiniteFreeComplex

/- Domain triage:
* primary domain: exactness of bounded finite free complexes after passage to the fiber local ring;
* sampled owner declarations in this domain:
  `FiniteFreeComplex.ExactInPositiveDegrees`,
  `FiniteFreeComplex.toChainComplex`,
  `toFiberLocalRingAt`,
  `fiberLocalRingAt`, and
  `ModuleCat.extendScalars`;
* best owner abstraction: `FiniteFreeComplex.ExactInPositiveDegrees` is the chapter owner for
  fiberwise exactness in positive degrees; the scalar extension of `C` to
  `fiberLocalRingAt R S q` is the canonical `bridge/view` object connecting the source-facing
  fiberwise predicate to that owner abstraction;
* primitive versus derived API: the primitive data here are `C`, the owner fiber local ring, and
  the scalar-extended finite free complex `C.fiberComplexAt R q`; the pointwise predicate
  `C.ExactInPositiveDegreesAtFiber R q` is the source-facing owner on primes, and the exact locus
  is the derived set-valued API built from that pointwise predicate.
-/

/-- The finite free complex over the fiber local ring at `q` obtained from `C` by scalar
extension along `S → fiberLocalRingAt R S q`. -/
noncomputable def fiberComplexAt (C : FiniteFreeComplex S e) (R : Type u) [CommRing R]
    [Algebra R S] (q : PrimeSpectrum S) : FiniteFreeComplex (fiberLocalRingAt R S q) e where
  toChainComplex :=
    { X := fun i ↦ ModuleCat.of (fiberLocalRingAt R S q)
          ((fiberLocalRingAt R S q) ⊗[S] ↑(C.toChainComplex.X i))
      d := fun i j ↦ ModuleCat.ofHom
          (LinearMap.baseChange (fiberLocalRingAt R S q) (C.toChainComplex.d i j).hom)
      shape := fun i j hij ↦ by
        sorry
      d_comp_d' := fun i j k _ _ ↦ by
        sorry }
  isZero_toChainComplex_X i hi := by
    sorry
  rank := C.rank
  termIso i := by
    change ModuleCat.of (fiberLocalRingAt R S q)
        ((fiberLocalRingAt R S q) ⊗[S] ↑(C.toChainComplex.X i)) ≅
      ModuleCat.of (fiberLocalRingAt R S q) (Fin (C.rank i) → fiberLocalRingAt R S q)
    let hbase :
        ModuleCat.of (fiberLocalRingAt R S q)
            ((fiberLocalRingAt R S q) ⊗[S] ↑(C.toChainComplex.X i)) ≅
          ModuleCat.of (fiberLocalRingAt R S q)
            ((fiberLocalRingAt R S q) ⊗[S] (Fin (C.rank i) → S)) :=
      (LinearEquiv.baseChange S (fiberLocalRingAt R S q) (C.toChainComplex.X i)
        (Fin (C.rank i) → S) (C.termIso i).toLinearEquiv).toModuleIso
    let hpi :
        ModuleCat.of (fiberLocalRingAt R S q)
            ((fiberLocalRingAt R S q) ⊗[S] (Fin (C.rank i) → S)) ≅
          ModuleCat.of (fiberLocalRingAt R S q) (Fin (C.rank i) → fiberLocalRingAt R S q) := by
      simpa using
        (TensorProduct.piScalarRight S (fiberLocalRingAt R S q) (fiberLocalRingAt R S q)
          (Fin (C.rank i))).toModuleIso
    exact hbase ≪≫ hpi

/-- The fiber complex of `C` at `q` is exact in the positive degrees. -/
def ExactInPositiveDegreesAtFiber (C : FiniteFreeComplex S e) (R : Type u) [CommRing R]
    [Algebra R S] (q : PrimeSpectrum S) : Prop :=
  (C.fiberComplexAt R q).ExactInPositiveDegrees

/-- A prime `q` lies in the fiberwise exactness predicate exactly when the scalar-extended fiber
complex at `q` is exact in positive degrees. -/
theorem exactInPositiveDegreesAtFiber_iff (C : FiniteFreeComplex S e) (R : Type u) [CommRing R]
    [Algebra R S] (q : PrimeSpectrum S) :
    C.ExactInPositiveDegreesAtFiber R q ↔ (C.fiberComplexAt R q).ExactInPositiveDegrees := by
  rfl

/-- The primes `q : Spec(S)` where the localized fiber complex
`F_{•,q} ⊗[R] κ(q ∩ R)` attached to `C` is exact in positive degrees. -/
def fiberExactLocus (C : FiniteFreeComplex S e) (R : Type u) [CommRing R] [Algebra R S] :
    Set (PrimeSpectrum S) :=
  { q | C.ExactInPositiveDegreesAtFiber R q }

/-- A prime lies in `fiberExactLocus` exactly when the corresponding fiber complex is exact in
positive degrees. -/
theorem mem_fiberExactLocus_iff (C : FiniteFreeComplex S e) (R : Type u) [CommRing R]
    [Algebra R S] (q : PrimeSpectrum S) :
    q ∈ C.fiberExactLocus R ↔ C.ExactInPositiveDegreesAtFiber R q := by
  rfl

end FiniteFreeComplex

variable [IsNoetherianRing R] [Algebra.FiniteType R S] [Module.Flat R S]

-- Proof sketch: apply the Buchsbaum--Eisenbud exactness criterion on each local fiber ring to
-- translate exactness of the fiber complex into determinantal-ideal conditions. Flatness lets one
-- compare the localized complex with the residue-fiber complex, and Lemma `10.129.2` makes the
-- required regular-sequence conditions open under the assumption that all fibers are
-- Cohen--Macaulay of constant Krull dimension.
/-- Lemma 10.129.3: let `R → S` be a finite type flat ring map with `R` Noetherian, and let
`C : FiniteFreeComplex S e` encode a finite complex `0 → S^{n_e} → ⋯ → S^{n_0}`. If there is a
constant such that every fiber ring `κ(𝔭) ⊗[R] S` is Cohen--Macaulay of that Krull dimension,
then the set of primes `q : Spec(S)` for which the fiber complex
`F_{•,q} ⊗[R] κ(q ∩ R)` is exact is an open subset of `Spec(S)`. -/
theorem isOpen_setOf_exactInPositiveDegreesAtFiber (C : FiniteFreeComplex S e)
    (hCM : ∀ p : PrimeSpectrum R, CohenMacaulayRing (p.asIdeal.Fiber S))
    (hConstDim : ∀ p p' : PrimeSpectrum R,
      ringKrullDim (p.asIdeal.Fiber S) = ringKrullDim (p'.asIdeal.Fiber S)) :
    IsOpen { q : PrimeSpectrum S | C.ExactInPositiveDegreesAtFiber R q } := sorry

/-- The fiber exactness locus is open under the fiberwise Cohen--Macaulay and constant-dimension
hypotheses of Lemma `10.129.3`. -/
theorem isOpen_fiberExactLocus (C : FiniteFreeComplex S e)
    (hCM : ∀ p : PrimeSpectrum R, CohenMacaulayRing (p.asIdeal.Fiber S))
    (hConstDim : ∀ p p' : PrimeSpectrum R,
      ringKrullDim (p.asIdeal.Fiber S) = ringKrullDim (p'.asIdeal.Fiber S)) :
    IsOpen (C.fiberExactLocus R) := by
  simpa [FiniteFreeComplex.fiberExactLocus] using
    isOpen_setOf_exactInPositiveDegreesAtFiber C hCM hConstDim

end
