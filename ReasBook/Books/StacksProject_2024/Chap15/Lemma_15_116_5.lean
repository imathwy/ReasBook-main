import Mathlib
import StacksProject_2024.Chap10.Lemma_10_155_2
import StacksProject_2024.Chap15.Lemma_15_116_4

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v w x uA vA wA xA

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

/- Domain-style sampling for Lemma 15.116.5:
- primary domain: ramification-eliminating base change for extensions of discrete valuation
  rings, expressed through the chapter solution predicates and strict-henselization existence;
- sampled owner declarations:
  `IsWeakSolutionFor`,
  `IsSolutionFor`,
  `IsSeparableSolutionFor`,
  `IsStrictHenselizationOf`;
- best owner abstraction: the solution notions already belong to the chapter owners from
  `Definition_15_116_1`, so this lemma should remain a source-facing existence theorem relating
  those owners rather than introduce a second bundled square owner;
- primitive-vs-derived split: the primitive witness data are the DVR extensions `A → A'`,
  `B → B'`, `A' → B'`, the compatible fraction fields `K'`, `L'`, and the residue-field
  comparison algebras; the three descent clauses are derived API and should therefore be phrased
  directly with `IsWeakSolutionFor`, `IsSolutionFor`, and `IsSeparableSolutionFor`.

Source/core/bridge triage:
- `source-facing`: the existence theorem for a ramification-eliminating square;
- `core/canonical`: `IsWeakSolutionFor`, `IsSolutionFor`, `IsSeparableSolutionFor`, and the
  strict-henselization owner `IsStrictHenselizationOf` used in the proof sketch;
- `bridge/view`: the explicit existential witness rings and fields together with their algebraic
  and residue-field comparison properties.
-/

-- Proof sketch: choose `A'` as a directed colimit of finite étale local extensions of `A` whose
-- residue field is a separable closure of `ResidueField A`, choose `B'` as a strict henselization
-- of `B`, and use the strict-henselian lifting lemma to produce the commutative square. The
-- fraction-field and residue-field conditions come from the chosen constructions together with the
-- canonical tower compatibilities for the induced comparison maps, while descent of weak
-- solutions, solutions, and separable solutions follows by approximating a solution over
-- `A' → B'` at a finite étale stage and then applying Lemma `15.116.4`.
/-- Lemma 15.116.5: for an extension `A → B` of discrete valuation rings with fraction fields
`K ⊂ L`, there exist extensions of discrete valuation rings `A → A'`, `B → B'`, and
`A' → B'` with compatible induced maps on fraction fields and residue fields such that `K' / K`
and `L' / L` are separable algebraic, the residue fields of `A'` and `B'` are separable closures
of those of `A` and `B`, and the existence of a weak solution, a solution, or a separable
solution for `A' → B'` implies the corresponding existence statement for `A → B`. -/
theorem exists_ramificationEliminationSquare :
    ∃ (Aprime : Type uA) (_ : CommRing Aprime) (_ : IsDomain Aprime)
      (_ : IsDiscreteValuationRing Aprime) (_ : Algebra A Aprime)
      (_ : IsExtensionOfDiscreteValuationRings A Aprime)
      (Bprime : Type vA) (_ : CommRing Bprime) (_ : IsDomain Bprime)
      (_ : IsDiscreteValuationRing Bprime) (_ : Algebra B Bprime) (_ : Algebra Aprime Bprime)
      (_ : Algebra A Bprime) (_ : IsScalarTower A Aprime Bprime) (_ : IsScalarTower A B Bprime)
      (_ : IsExtensionOfDiscreteValuationRings B Bprime)
      (_ : IsExtensionOfDiscreteValuationRings Aprime Bprime)
      (Kprime : Type wA) (_ : Field Kprime) (_ : Algebra Aprime Kprime)
      (_ : IsFractionRing Aprime Kprime) (_ : Algebra K Kprime) (_ : Algebra A Kprime)
      (_ : IsScalarTower A Aprime Kprime) (_ : IsScalarTower A K Kprime)
      (Lprime : Type xA) (_ : Field Lprime) (_ : Algebra Bprime Lprime)
      (_ : IsFractionRing Bprime Lprime) (_ : Algebra L Lprime) (_ : Algebra B Lprime)
      (_ : IsScalarTower B Bprime Lprime) (_ : IsScalarTower B L Lprime)
      (_ : Algebra Kprime Lprime) (_ : Algebra Aprime Lprime)
      (_ : IsScalarTower Aprime Bprime Lprime) (_ : IsScalarTower Aprime Kprime Lprime)
      (_ : Algebra (ResidueField A) (ResidueField Aprime))
      (_ : Algebra (ResidueField B) (ResidueField Bprime))
      (_ : Algebra (ResidueField Aprime) (ResidueField Bprime))
      (_ : Algebra (ResidueField A) (ResidueField Bprime))
      (_ : IsScalarTower (ResidueField A) (ResidueField Aprime) (ResidueField Bprime))
      (_ : IsScalarTower (ResidueField A) (ResidueField B) (ResidueField Bprime)),
      Algebra.IsAlgebraic K Kprime ∧
        Algebra.IsSeparable K Kprime ∧
        Algebra.IsAlgebraic L Lprime ∧
        Algebra.IsSeparable L Lprime ∧
        IsSepClosure (ResidueField A) (ResidueField Aprime) ∧
        IsSepClosure (ResidueField B) (ResidueField Bprime) ∧
        ((∃ (K1prime : Type (max uA vA wA xA)) (_ : Field K1prime)
            (_ : Algebra Aprime K1prime) (_ : Algebra Kprime K1prime)
            (_ : IsScalarTower Aprime Kprime K1prime)
            (_ : FiniteDimensional Kprime K1prime),
            IsWeakSolutionFor Aprime Bprime Kprime Lprime K1prime) →
          ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
            (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
            IsWeakSolutionFor A B K L K1) ∧
        ((∃ (K1prime : Type (max uA vA wA xA)) (_ : Field K1prime)
            (_ : Algebra Aprime K1prime) (_ : Algebra Kprime K1prime)
            (_ : IsScalarTower Aprime Kprime K1prime)
            (_ : FiniteDimensional Kprime K1prime),
            IsSolutionFor Aprime Bprime Kprime Lprime K1prime) →
          ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
            (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
            IsSolutionFor A B K L K1) ∧
        ((∃ (K1prime : Type (max uA vA wA xA)) (_ : Field K1prime)
            (_ : Algebra Aprime K1prime) (_ : Algebra Kprime K1prime)
            (_ : IsScalarTower Aprime Kprime K1prime)
            (_ : FiniteDimensional Kprime K1prime),
            IsSeparableSolutionFor Aprime Bprime Kprime Lprime K1prime) →
          ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
            (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
            IsSeparableSolutionFor A B K L K1) := sorry

end
