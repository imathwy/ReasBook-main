import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
variable [Algebra.FiniteType k S]

-- Proof sketch: finite type over a field makes `S` Noetherian and Jacobson. The owner-side
-- equivalence `Module.finite_iff_krullDimLE_zero` identifies the zero-dimensional clause with
-- `FiniteDimensional k S`, and `Module.finite_iff_isArtinianRing` identifies that clause with
-- `IsArtinianRing S`. The Artinian-to-finite-maximal-spectrum step is then delegated to the owner
-- instance `IsArtinianRing.instFiniteMaximalSpectrum`, and the Jacobson/discrete-spectrum clauses
-- are recovered from the canonical prime-spectrum API.
/-- Lemma 10.61.3: for a finite type `k`-algebra `S`, the canonical zero-dimensional, finite-
spectrum, Hausdorff-spectrum, finite-dimensional, Artinian, and discrete-spectrum clauses are
equivalent.

Canonical Lean form: clause `(1)` uses the owner predicate `Ring.KrullDimLE 0 S`. Under the extra
hypothesis `[Nontrivial S]`, this recovers the source wording `ringKrullDim S = 0` via
`ringKrullDimZero_iff_ringKrullDim_eq_zero`. The theorem itself does not need `[Nontrivial S]`,
since all seven canonical clauses still agree in the zero-ring edge case. -/
@[stacks 0ALW]
theorem finiteTypeAlgebra_over_field_zeroDimensional_tfae :
    List.TFAE
      [ Ring.KrullDimLE 0 S
      , Finite (PrimeSpectrum S)
      , Finite (MaximalSpectrum S)
      , T2Space (PrimeSpectrum S)
      , FiniteDimensional k S
      , IsArtinianRing S
      , DiscreteTopology (PrimeSpectrum S)
      ] := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have hFiniteType : (algebraMap k S).FiniteType := by
    rwa [RingHom.finiteType_algebraMap]
  letI : IsJacobsonRing S := hFiniteType.isJacobsonRing
  have hclosedPoints_of_finiteMax [Finite (MaximalSpectrum S)] :
      (closedPoints (PrimeSpectrum S)).Finite := by
    let f : MaximalSpectrum S → closedPoints (PrimeSpectrum S) := fun x ↦
      ⟨x.toPrimeSpectrum, (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr x.isMaximal⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      exact
        ⟨⟨x.asIdeal, (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx⟩, rfl⟩
    exact Finite.of_surjective f hf
  tfae_have 1 ↔ 5 := by
    simpa using (Module.finite_iff_krullDimLE_zero k S).symm
  tfae_have 5 ↔ 6 := by
    simpa using Module.finite_iff_isArtinianRing k S
  tfae_have 6 → 3 := by
    intro hArt
    letI : IsArtinianRing S := hArt
    infer_instance
  tfae_have 3 → 7 := by
    intro hfin
    letI : Finite (MaximalSpectrum S) := hfin
    exact JacobsonSpace.discreteTopology hclosedPoints_of_finiteMax
  tfae_have 6 ↔ 7 := by
    constructor
    · intro hArt
      letI : IsArtinianRing S := hArt
      letI : Finite (MaximalSpectrum S) := inferInstance
      exact JacobsonSpace.discreteTopology hclosedPoints_of_finiteMax
    · intro hdisc
      exact
        (Module.finite_iff_isArtinianRing k S).mp <|
          (Module.finite_iff_krullDimLE_zero k S).mpr <|
            (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp hdisc).2
  tfae_have 7 → 2 := by
    intro hdisc
    exact (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp hdisc).1
  tfae_have 2 → 4 := by
    intro hfin
    letI : Finite (PrimeSpectrum S) := hfin
    let hclosed : (closedPoints (PrimeSpectrum S)).Finite := Set.toFinite _
    letI : DiscreteTopology (PrimeSpectrum S) := JacobsonSpace.discreteTopology hclosed
    infer_instance
  tfae_have 4 → 1 := by
    intro hT2
    letI : T2Space (PrimeSpectrum S) := hT2
    letI : T1Space (PrimeSpectrum S) := T2Space.t1Space
    refine Ring.KrullDimLE.mk₀ fun I hI ↦ ?_
    exact
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal ⟨I, hI⟩).mp
        isClosed_singleton
  tfae_finish

end
