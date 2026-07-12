import Mathlib
import StacksProject_2024.Chap10.Lemma_10_88_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M]

/- Source/core/bridge triage:
* source-facing: the quotient-ring comparison statement from Lemma `10.88.12`.
* core/canonical: the chapter owner `Module.MittagLeffler` from `Definition_10_88_7`.
* bridge/view: specialize the finite/finitely-presented restriction-of-scalars owner theorem to the
  quotient algebra `R → R ⧸ I`; the reverse implication remains the source-facing quotient bridge.
-/
-- Proof sketch: one direction is Lemma `10.88.11` applied to the quotient map `R → R ⧸ I`. For
-- the converse, choose a directed colimit presentation of `M` by finitely presented `R ⧸ I`-modules;
-- since `I` is finitely generated, the quotient algebra `R ⧸ I` is finite and finitely presented
-- over `R`, so the same stages are finitely presented over `R`, and the Hom inverse systems over
-- `R` and `R ⧸ I` agree because the quotient map is surjective.
/-- Lemma 10.88.12: if `S = R ⧸ I` for a finitely generated ideal `I`, then an `S`-module `M` is
Mittag-Leffler over `R` if and only if it is Mittag-Leffler over `S`. -/
theorem mittagLeffler_iff_over_ring_and_quotient (I : Ideal R) (hI : I.FG)
    [Module (R ⧸ I) M] [Module R M] [IsScalarTower R (R ⧸ I) M] :
    MittagLeffler R M ↔ MittagLeffler (R ⧸ I) M := by
  constructor
  · intro hM
    sorry
  · intro hM
    letI : Algebra.FinitePresentation R (R ⧸ I) := Algebra.FinitePresentation.quotient hI
    letI : Module.Finite R (R ⧸ I) := by infer_instance
    have hrestrict :
        ∀ (S : Type _) [CommRing S] [Algebra R S] [Module S M] [Module R M]
          [IsScalarTower R S M] [Module.Finite R S] [Algebra.FinitePresentation R S],
          MittagLeffler S M → MittagLeffler R M := by
      intro S _ _ _ _ _ _ _ hS
      letI : MittagLeffler S M := hS
      exact @mittagLeffler_restrictScalars_of_finite_finitePresentation R S M
        _ _ _ _ _ _ _ _ _ _
    exact hrestrict (R ⧸ I) hM

end

end Module
