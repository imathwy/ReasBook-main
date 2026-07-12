import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Lemma_10_61_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open PrimeSpectrum
open Algebra.TensorProduct

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

private noncomputable abbrev fiberPrime (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    PrimeSpectrum (p.asIdeal.Fiber S) :=
  PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩

omit [Algebra.FiniteType R S] in
private theorem fiberPrime_asIdeal_comap (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    Ideal.comap includeRight.toRingHom (fiberPrime p q hq).asIdeal = q.asIdeal := by
  change
    ((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrime p q hq)).1.asIdeal =
      q.asIdeal
  exact congrArg
    (fun x : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} ↦ x.1.asIdeal)
    ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply ⟨q, hq⟩)

private theorem isOpen_singleton_of_quasiFiniteAt (K : Type*) {A : Type*} [Field K] [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (Q : PrimeSpectrum A)
    [Algebra.QuasiFiniteAt K Q.asIdeal] :
    IsOpen ({Q} : Set (PrimeSpectrum A)) := by
  exact
    (@Algebra.QuasiFiniteAt.isClopen_singleton K A _ _ _ Q inferInstance inferInstance
      inferInstance).isOpen

private theorem quasiFiniteAt_iff_quasiFiniteAt_fiberPrime (p : PrimeSpectrum R)
    (q : PrimeSpectrum S) (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    Algebra.QuasiFiniteAt R q.asIdeal ↔
      Algebra.QuasiFiniteAt p.asIdeal.ResidueField (fiberPrime p q hq).asIdeal := by
  constructor
  · intro h
    letI : Algebra.QuasiFiniteAt R q.asIdeal := h
    have hfiber : Ideal.comap includeRight.toRingHom (fiberPrime p q hq).asIdeal = q.asIdeal :=
      fiberPrime_asIdeal_comap p q hq
    exact
      Algebra.QuasiFiniteAt.baseChange q.asIdeal (fiberPrime p q hq).asIdeal (by
          simpa using hfiber.symm)
  · intro h
    letI : q.asIdeal.LiesOver p.asIdeal := ⟨(congrArg PrimeSpectrum.asIdeal hq).symm⟩
    letI : Algebra.QuasiFiniteAt p.asIdeal.ResidueField (fiberPrime p q hq).asIdeal := h
    have hfiber : Ideal.comap includeRight.toRingHom (fiberPrime p q hq).asIdeal = q.asIdeal :=
      fiberPrime_asIdeal_comap p q hq
    exact
      Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField
        p.asIdeal q.asIdeal (fiberPrime p q hq).asIdeal (by
          simpa using hfiber)

-- Proof sketch: identify the primes of the fiber `p.asIdeal.Fiber S` with the primes of `S`
-- lying over `p` via `PrimeSpectrum.preimageHomeomorphFiber`. Under this identification, clause
-- (1) says every point of `Spec (p.asIdeal.Fiber S)` is open, so the spectrum is discrete.
-- Since `p.asIdeal.Fiber S` is a finite type algebra over the field `p.asIdeal.ResidueField`,
-- apply Lemma `10.61.3` to obtain the equivalence with module-finiteness over the residue field
-- and with finiteness of the prime spectrum.
/-- Lemma 10.122.4: for a finite type ring map `R → S` and a prime `p` of `R`, the following are
equivalent: `R → S` is quasi-finite at every prime of `S` lying over `p`; the fiber algebra
`p.asIdeal.Fiber S = S ⊗[R] κ(p)` is finite over `κ(p)`; and `Spec (p.asIdeal.Fiber S)` is a
finite set. -/
@[stacks 0H8X]
theorem quasiFiniteAt_primesOver_tfae_fiberFinite (p : PrimeSpectrum R) :
    List.TFAE
      [ (∀ q : PrimeSpectrum S,
            PrimeSpectrum.comap (algebraMap R S) q = p → Algebra.QuasiFiniteAt R q.asIdeal)
      , Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S)
      , Finite (PrimeSpectrum (p.asIdeal.Fiber S))
      ] := by
  let K := p.asIdeal.ResidueField
  let A := p.asIdeal.Fiber S
  have hA :
      List.TFAE
        [ Ring.KrullDimLE 0 A
        , Finite (PrimeSpectrum A)
        , Finite (MaximalSpectrum A)
        , T2Space (PrimeSpectrum A)
        , FiniteDimensional K A
        , IsArtinianRing A
        , DiscreteTopology (PrimeSpectrum A)
        ] :=
      (finiteTypeAlgebra_over_field_zeroDimensional_tfae :
        List.TFAE
          [ Ring.KrullDimLE 0 A
          , Finite (PrimeSpectrum A)
          , Finite (MaximalSpectrum A)
          , T2Space (PrimeSpectrum A)
          , FiniteDimensional K A
          , IsArtinianRing A
          , DiscreteTopology (PrimeSpectrum A)
          ])
  tfae_have 1 → 3 := by
    intro hqf
    have hFiber : ∀ Q : PrimeSpectrum A, Algebra.QuasiFiniteAt K Q.asIdeal := by
      intro Q
      let q := (PrimeSpectrum.preimageEquivFiber R S p).symm Q
      have hQ : fiberPrime p q.1 q.2 = Q := by
        change
          (PrimeSpectrum.preimageEquivFiber R S p)
              ((PrimeSpectrum.preimageEquivFiber R S p).symm Q) = Q
        exact (PrimeSpectrum.preimageEquivFiber R S p).apply_symm_apply Q
      simpa [hQ] using
        (quasiFiniteAt_iff_quasiFiniteAt_fiberPrime p q.1 q.2).mp
          (hqf q.1 q.2)
    letI : DiscreteTopology (PrimeSpectrum A) :=
      discreteTopology_iff_isOpen_singleton.mpr fun Q ↦ by
        letI : Algebra.QuasiFiniteAt K Q.asIdeal := hFiber Q
        simpa using isOpen_singleton_of_quasiFiniteAt K Q
    simpa [A] using (finite_of_compact_of_discrete : Finite (PrimeSpectrum A))
  tfae_have 3 → 2 := by
    intro hfinite
    have hfd : FiniteDimensional K A := (hA.out 1 4 rfl rfl).mp hfinite
    letI : FiniteDimensional K A := hfd
    simpa [A, K] using (inferInstance : Module.Finite K A)
  tfae_have 2 → 1 := by
    intro hfinite
    letI : Module.Finite K A := hfinite
    have hFiber : ∀ Q : PrimeSpectrum A, Algebra.QuasiFiniteAt K Q.asIdeal := by
      intro Q
      dsimp [Algebra.QuasiFiniteAt]
      infer_instance
    intro q hq
    exact
      (quasiFiniteAt_iff_quasiFiniteAt_fiberPrime p q hq).mpr <|
        hFiber (fiberPrime p q hq)
  tfae_finish

end
