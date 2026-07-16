import Mathlib
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_5
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_5_3.ResidueFieldLiftDecomposition
-- `Serre.Chap16.Proposition_16_16_3_3` is intentionally not imported: it transitively re-exports
-- `Proposition_16_16_3_3.PositiveBasics`, which declares the scoped notation `R⁺[_](_)` (and a
-- `SatisfiesConditionR`) already provided here by `Remark_16_16_3_5.ReverseDirection`/`Core`.
-- Importing both yields an "environment already contains 'Representation.«termR⁺[_](_)»'"
-- collision.  All owner predicates used below (`SatisfiesConditionR`, `SatisfiesConditionRPrime`,
-- `FDRep.HasRPrimeLift`, `satisfiesConditionRPrime_imp_satisfiesConditionR`, and the `R⁺` notation)
-- come from the `Remark_16_16_3_5` cluster.
import LinearRepresentations_Serre_1977.Serre.Chap16.Remark_16_16_3_5.ReverseDirection
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open scoped Representation

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

/- Domain-style sampling for Theorem 16-16.3-6:
* primary domain: modular representation-theoretic lifting criteria for finite `p`-solvable
  groups, expressed through the Chapter `16` owner predicates `SatisfiesConditionR` and
  `SatisfiesConditionRPrime`;
* relevant owner declarations inspected in this domain:
  `IsPSolvableOfHeight`,
  `SatisfiesConditionR`,
  `FDRep.HasRPrimeLift`,
  `SatisfiesConditionRPrime`,
  `IsPSolvable`;
* best owner abstraction: the source-facing conjunction asserting that the fixed
  fraction-field/local-ring setting `K/A` satisfies Serre's conditions `(R)` and `(R')` under the
  canonical group-theoretic owner predicate `IsPSolvable p G`;
* primitive data: the owner predicates `IsPSolvable p G`, `SatisfiesConditionR (R⁺[K](G)) A`, and
  `SatisfiesConditionRPrime A K G`;
* derived API: the two projection theorems below extracting `(R)` and `(R')` separately from the
  source-facing Fong-Swan conjunction.

Source/core/bridge triage:
* source-facing: `fong_swan_of_isPSolvable`;
* core/canonical: `IsPSolvable`, `SatisfiesConditionR`, and `SatisfiesConditionRPrime`;
* bridge/view: the two projection lemmas, which do not introduce any new owner data.
-/

/-- Helper for Theorem 16-16.3-6: a source-facing residue-field lift packages as Serre's
condition `(R')` per-object lift witness. -/
private theorem hasRPrimeLift_of_isResidueFieldLift
    [IsDomain A] [IsDiscreteValuationRing A]
    (S : FDRep k G) [Simple S]
    {P : Type u} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    (ρA : Representation A G P) (red : P →ₗ[A] S)
    (hred : IsResidueFieldLift S.ρ ρA red) :
    FDRep.HasRPrimeLift S K := by
  -- Turn the free `A[G]`-lift into the canonical scalar-extension owner and its stable lattice.
  obtain ⟨L, hLiso⟩ :=
    residueFieldLift_scalarExtension_reduction_iso
      (A := A) (K := K) (G := G) S.ρ ρA red hred
  let X : FDRep K G := residueFieldLiftScalarExtensionOwner (A := A) (K := K) (G := G) ρA
  have eS : S ≅ FDRep.of S.ρ := fdRepIsoOfRho S
  refine ⟨X, ?_, L, ?_⟩
  · -- Simplicity ascends from the simple reduced lattice by the standard DVR criterion.
    rcases hLiso with ⟨eL⟩
    letI : Simple (FDRep.of S.ρ) := Simple.of_iso eS.symm
    letI : Simple (FDRep.of L.reductionRepresentation) := Simple.of_iso eL
    have hredIrr : Representation.IsIrreducible L.reductionRepresentation :=
      FDRep.isIrreducible_of_simple (FDRep.of L.reductionRepresentation)
    letI : Representation.IsIrreducible X.ρ := by
      simpa [X] using simple_reduction_implies_isIrreducible _ L hredIrr
    exact FDRep.simple_of_isIrreducible X
  · -- Compose the reduction isomorphism with the tautological `S ≅ FDRep.of S.ρ` comparison.
    rcases hLiso with ⟨eL⟩
    exact ⟨eL.trans eS.symm⟩

/-- Helper for Theorem 16-16.3-6: Serre's 17.6 lift statement for every simple residue-field
module is exactly condition `(R')` after packaging the scalar-extension stable lattice. -/
private theorem satisfiesConditionRPrime_of_residueField_lifts
    [IsDomain A] [IsDiscreteValuationRing A]
    (hLift :
      ∀ S : FDRep k G, Simple S →
        ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module A P)
          (_ : Module.Free A P) (_ : Module.Finite A P)
          (ρA : Representation A G P) (red : P →ₗ[A] S),
            IsResidueFieldLift S.ρ ρA red) :
    SatisfiesConditionRPrime A K G := by
  intro S hS
  -- Apply the source lift theorem to the chosen simple object, then repackage it as `(R')`.
  rcases hLift S hS with ⟨P, hAdd, hMod, hFree, hFinite, ρA, red, hred⟩
  letI : AddCommGroup P := hAdd
  letI : Module A P := hMod
  letI : Module.Free A P := hFree
  letI : Module.Finite A P := hFinite
  letI : Simple S := hS
  exact hasRPrimeLift_of_isResidueFieldLift (A := A) (K := K) (G := G) S ρA red hred

/-- Helper for Theorem 16-16.3-6: in the split Henselian setting formalized in Chapter `17`,
Serre's Fong-Swan induction supplies the exact residue-field lift family needed for `(R')`. -/
private theorem residueField_lifts_of_isPSolvable_henselian_split
    [HenselianLocalRing A] [IsAlgClosed k]
    (hp : Nat.Prime p) (hG : IsPSolvable p G) :
    ∀ S : FDRep k G, Simple S →
      ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module A P)
        (_ : Module.Free A P) (_ : Module.Finite A P)
        (ρA : Representation A G P) (red : P →ₗ[A] S),
          IsResidueFieldLift S.ρ ρA red := by
  intro S hS
  -- Chapter `17` proves the source induction once the residue field is split enough for Schur's
  -- lemma and the base ring is Henselian for the lifting steps.
  letI : Simple S := hS
  letI : Representation.IsIrreducible S.ρ := FDRep.isIrreducible_of_simple S
  exact exists_residueFieldLift_of_isIrreducible_of_isPSolvable (A := A) hp hG S.ρ

/-- Helper for Theorem 16-16.3-6: condition `(R')` formally yields the source-facing conjunction,
via the proved `(R') → (R)` direction of Remark `16-16.3-5` (which uses the trivial DVR witness
`A' = A`, `K' = K`).  We invoke that direction directly through the split support module. -/
private theorem fong_swan_conjunction_of_satisfiesConditionRPrime
    [IsDomain A] [IsDiscreteValuationRing A]
    (hR' : SatisfiesConditionRPrime A K G) :
    SatisfiesConditionR (R⁺[K](G)) A ∧
      SatisfiesConditionRPrime A K G :=
  ⟨satisfiesConditionRPrime_imp_satisfiesConditionR (A := A) (K := K) (G := G) hR', hR'⟩

/-- Theorem 16-16.3-6 (Theorem 38, Fong–Swan).  In Serre's `p`-modular system `(A, K, k)` —
`A` a *complete* discrete valuation ring with fraction field `K` of characteristic `0` and residue
field `k = A/𝔪` of characteristic `p`, *sufficiently large* — if the finite group `G` is
`p`-solvable, then it satisfies Serre's conditions `(R)` and `(R')`: the actual positive cone
`R_K^+(G)` satisfies condition `(R)`, and every simple finite-dimensional `k[G]`-module is the
reduction modulo `𝔪` of a stable lattice in a (necessarily simple) finite-dimensional
`K[G]`-representation.

Faithful framing of Serre's hypotheses (Serre, Part III, opening of §14: "`K` complete with respect
to a discrete valuation", and §16.3 "`K` sufficiently large"):
* `[IsDiscreteValuationRing A]` + `[HenselianLocalRing A]` — Serre's `(A, K, k)` is a modular system
  with `A` a *complete* DVR; completeness (here recorded as the operative Henselian property used by
  the lifting steps of Serre's 17.6 induction) is **essential**: without a DVR, `A = K` a field
  makes `(R)` vacuously **false** (`SatisfiesConditionR` needs a finite DVR extension of `A`).
* `[IsAlgClosed k]` — Serre's "`K` sufficiently large", recorded on the residue field for the
  Schur-lemma step of the Fong–Swan induction (the same largeness rendering used throughout
  Chapter 17).  It is **essential**: over a non-large field the `(R')` conjunct is **false** even
  for `p`-solvable `G` — e.g. `A = ℤ_(2)`, `K = ℚ`, `p = 2`, `G = C₇` (which is `2`-solvable) has a
  `3`-dimensional simple `𝔽₂[C₇]`-module, while every simple `ℚ[C₇]`-representation has dimension
  `1` or `6`, so it does not lift; over a sufficiently large residue field the lift exists. -/
theorem fong_swan_of_isPSolvable
    [IsDomain A] [IsDiscreteValuationRing A] [HenselianLocalRing A] [IsAlgClosed k]
    (hp : Nat.Prime p) (hG : IsPSolvable p G) :
    SatisfiesConditionR (R⁺[K](G)) A ∧
      SatisfiesConditionRPrime A K G :=
  -- `(R')` is Serre's 17.6 Fong–Swan induction (Chapter 17 lift of every simple `k[G]`-module to a
  -- free `A[G]`-lattice, packaged here as `(R')`); the `(R)` half is then formal via the trivial
  -- witness in Remark `16-16.3-5`.
  fong_swan_conjunction_of_satisfiesConditionRPrime (A := A) (K := K) (G := G)
    (satisfiesConditionRPrime_of_residueField_lifts (A := A) (K := K) (G := G)
      (residueField_lifts_of_isPSolvable_henselian_split (A := A) hp hG))

/-- The `(R')` half of Theorem `16-16.3-6`, obtained by projecting the Fong-Swan conjunction. -/
theorem satisfiesConditionRPrime_of_isPSolvable
    [IsDomain A] [IsDiscreteValuationRing A] [HenselianLocalRing A] [IsAlgClosed k]
    (hp : Nat.Prime p) (hG : IsPSolvable p G) :
    SatisfiesConditionRPrime A K G :=
  (fong_swan_of_isPSolvable hp hG).2

/-- The `(R)` half of Theorem `16-16.3-6`, obtained by projecting the Fong-Swan conjunction: a
`p`-solvable finite group satisfies Serre's condition `(R)` for actual `K[G]`-representation
classes. -/
theorem satisfiesConditionR_of_isPSolvable
    [IsDomain A] [IsDiscreteValuationRing A] [HenselianLocalRing A] [IsAlgClosed k]
    (hp : Nat.Prime p) (hG : IsPSolvable p G) :
    SatisfiesConditionR (R⁺[K](G)) A :=
  (fong_swan_of_isPSolvable hp hG).1

end

end Representation
