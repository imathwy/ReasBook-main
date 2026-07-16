import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_47_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open AlgebraicGeometry CommRingCat

universe u

section

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]

-- Proof sketch: `(1) → (2)` is immediate. For `(2) → (3)`, write `SeparableClosure k` as the
-- union of its finite separable subextensions and use flat going-down to compare minimal primes.
-- For `(3) → (4)`, the extension from the separable closure to the algebraic closure is purely
-- inseparable, so the induced map on spectra is a homeomorphism. For `(4) → (1)`, embed an
-- arbitrary field extension and `AlgebraicClosure k` into a common overfield and use flat
-- injective base change plus the unique-minimal-prime criterion from Lemma `10.47.2`.
/-- Lemma 10.47.3: for a `k`-algebra `R`, the following are equivalent: every base change to a
field extension of `k` has irreducible prime spectrum, every base change to a finite separable
field extension of `k` has irreducible prime spectrum, the base change to `SeparableClosure k` has
irreducible prime spectrum, and the base change to `AlgebraicClosure k` has irreducible prime
spectrum. -/
theorem irreducibleSpace_primeSpectrum_baseChange_tfae :
    List.TFAE
      [ (∀ (K : Type u) [Field K] [Algebra k K],
            IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
        (∀ (K : Type u) [Field K] [Algebra k K]
            [FiniteDimensional k K] [Algebra.IsSeparable k K],
            IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)),
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k)) ] := sorry

private theorem geometricallyIrreducible_tfae :
    List.TFAE
      [ GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))),
        (∀ (K : Type u) [Field K] [Algebra k K]
            [FiniteDimensional k K] [Algebra.IsSeparable k K],
            IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)),
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k)) ] := by
  have htfae :
      List.TFAE
        [ (∀ (K : Type u) [Field K] [Algebra k K],
              IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
          (∀ (K : Type u) [Field K] [Algebra k K]
              [FiniteDimensional k K] [Algebra.IsSeparable k K],
              IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k)) ] :=
    irreducibleSpace_primeSpectrum_baseChange_tfae
  let hgeom :
      GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
        ∀ (K : Type u) [Field K] [Algebra k K],
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] K)) :=
    geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange
  tfae_have 1 ↔ 2 := by
    exact hgeom.trans <| htfae.out 0 1 (by simp) (by simp)
  tfae_have 1 ↔ 3 := by
    exact hgeom.trans <| htfae.out 0 2 (by simp) (by simp)
  tfae_have 1 ↔ 4 := by
    exact hgeom.trans <| htfae.out 0 3 (by simp) (by simp)
  tfae_finish

/-- Canonical geometric-irreducibility form of Lemma 10.47.3, clauses `(1) ↔ (2)`: it is enough
to test irreducibility of `PrimeSpectrum (R ⊗[k] K)` on finite separable extensions of `k`. -/
theorem geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_finiteSeparable_baseChange :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsSeparable k K],
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] K)) := by
  have htfae :
      List.TFAE
        [ GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))),
          (∀ (K : Type u) [Field K] [Algebra k K]
              [FiniteDimensional k K] [Algebra.IsSeparable k K],
              IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k)) ] :=
    geometricallyIrreducible_tfae
  simpa using htfae.out 0 1 (by simp) (by simp)

/-- Canonical geometric-irreducibility form of Lemma 10.47.3, clauses `(1) ↔ (3)`: a `k`-algebra
is geometrically irreducible iff its base change to `SeparableClosure k` has irreducible prime
spectrum. -/
theorem geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_separableClosure :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
      IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)) := by
  have htfae :
      List.TFAE
        [ GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))),
          (∀ (K : Type u) [Field K] [Algebra k K]
              [FiniteDimensional k K] [Algebra.IsSeparable k K],
              IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k)) ] :=
    geometricallyIrreducible_tfae
  simpa using htfae.out 0 2 (by simp) (by simp)

/-- Canonical geometric-irreducibility form of Lemma 10.47.3, clauses `(1) ↔ (4)`: a `k`-algebra
is geometrically irreducible iff its base change to `AlgebraicClosure k` has irreducible prime
spectrum. -/
theorem geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_algebraicClosure :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
      IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k)) := by
  have htfae :
      List.TFAE
        [ GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))),
          (∀ (K : Type u) [Field K] [Algebra k K]
              [FiniteDimensional k K] [Algebra.IsSeparable k K],
              IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k)) ] :=
    geometricallyIrreducible_tfae
  simpa using htfae.out 0 3 (by simp) (by simp)

end
