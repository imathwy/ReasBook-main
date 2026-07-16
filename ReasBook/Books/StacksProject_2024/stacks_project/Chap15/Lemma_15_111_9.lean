import Mathlib
import StacksProject_2024.stacks_project.Chap09.Lemma_9_15_6
import StacksProject_2024.stacks_project.Chap15.Lemma_15_111_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u v

section

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]

local notation "RFix" => FixedPoints.subring R G

/- Domain-style sampling for Lemma 15.111.9:
- primary domain: invariant-theoretic actions of decomposition/stabilizer groups on quotient and
  residue fields
- sampled owner declarations:
  `Algebra.IsInvariant`,
  `Ideal.IsFractionRing.normal`,
  `Ideal.Quotient.normal`,
  `Ideal.Quotient.stabilizerHom`,
  `IsFractionRing.stabilizerHom`,
  `IsFractionRing.stabilizerHom_surjective`
- best owner abstractions: the fraction-field normality theorem `Ideal.IsFractionRing.normal` for
  clause `(1)`, and the stabilizer owner `IsFractionRing.stabilizerHom` with its canonical
  surjectivity theorem `IsFractionRing.stabilizerHom_surjective` for clause `(2)`
- primitive data: the invariant fixed-subring extension `RFix ⊆ R` together with primes
  `p ⊆ RFix`, `q ⊆ R` and the lying-over hypothesis `q.LiesOver p`
- derived API: normality of the residue-field extension and surjectivity of the decomposition-group
  action on `Aut(κ(q) / κ(p))`

Layer triage:
- `source-facing`: the textbook residue-field statement for the decomposition group over `p` and
  `q`
- `core/canonical`: `Ideal.IsFractionRing.normal`, `IsFractionRing.stabilizerHom`, and
  `IsFractionRing.stabilizerHom_surjective`
- `bridge/view`: the fixed-subring/residue-field instances in this file realizing the source
  situation as an instance of the canonical owner theorem

The surjectivity clause is derived API from the owner theorem, so it should be expressed by direct
canonical reuse rather than by a parallel local wrapper theorem.
-/

/-- Helper for Lemma 15.111.9: fixed scalars from `R^G` commute with the given `G`-action on
`R`. -/
private instance fixedPointsSubring_smulCommClass :
    SMulCommClass G RFix R where
  smul_comm g x r := by
    -- Rewrite the scalar from `R^G` to `R` and use that it is fixed by every group element.
    change (MulSemiringAction.toRingHom G R g) ((x : R) * r) = (x : R) * (g • r)
    rw [map_mul]
    simpa using congrArg (fun t : R => t * (g • r)) (x.2 g)

variable (p : Ideal (FixedPoints.subring R G)) [p.IsPrime]
variable (q : Ideal R) [q.IsPrime] [q.LiesOver p]

local notation "κp" => p.ResidueField
local notation "κq" => q.ResidueField

private noncomputable instance fixedPointsResidueFieldAlgebra :
    Algebra (RFix ⧸ p) κq :=
  ((Ideal.ResidueField.map p q (algebraMap RFix R) (Ideal.over_def q p)).comp
    (algebraMap (RFix ⧸ p) κp)).toAlgebra

-- Proof sketch: both ring homomorphisms are induced by the same inclusion `R^G ↪ R`; compare them
-- on quotient classes represented by elements of `R^G`.
omit [Finite G] in
private theorem fixedPointsResidueField_comp_quotient :
    algebraMap (RFix ⧸ p) κq =
      (algebraMap (R ⧸ q) κq).comp (algebraMap (RFix ⧸ p) (R ⧸ q)) := by
  -- Compare the two quotient-to-residue-field maps on representatives coming from `R^G`.
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- After reducing to `a : R^G`, the defining residue-field map formula is exactly the needed
  -- compatibility with the quotient algebra map.
  change
    Ideal.ResidueField.map p q (algebraMap RFix R) (Ideal.over_def q p)
        ((algebraMap RFix κp) a) =
      (algebraMap (R ⧸ q) κq) ((algebraMap RFix (R ⧸ q)) a)
  rw [Ideal.ResidueField.map_algebraMap p q (algebraMap RFix R) (Ideal.over_def q p) a]
  rfl

private noncomputable instance fixedPointsResidueFieldTower :
    IsScalarTower (RFix ⧸ p) κp κq :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable instance fixedPointsQuotientResidueFieldTower :
    IsScalarTower (RFix ⧸ p) (R ⧸ q) κq :=
  IsScalarTower.of_algebraMap_eq' (fixedPointsResidueField_comp_quotient p q)

-- Proof sketch: the invariant extension `R^G ⊆ R` is integral, so the induced residue field
-- extension is algebraic; normality follows from the orbit polynomial over `R^G` whose roots are
-- the conjugates `σ(a)` and whose reduction mod `q` splits in `κ(q)`.
/-- Lemma 15.111.9 (1): if `q` is a prime of `R` lying over a prime `p` of the fixed subring
`R^G`, then the residue field extension `κ(q) / κ(p)` is algebraic and normal. -/
theorem residueField_normal_of_liesOver_fixedPoints :
    Normal κp κq := by
  classical
  letI := Fintype.ofFinite G
  letI : Nontrivial (R ⧸ q) := Ideal.Quotient.nontrivial_iff.2 q.isPrime.ne_top
  letI : Nontrivial R := Function.Surjective.nontrivial (Ideal.Quotient.mk_surjective (I := q))
  have hTower : IsScalarTower RFix κp κq := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    -- Compare the two maps `R^G → κ(q)` through the canonical residue-field map.
    simp [Ideal.ResidueField.map_algebraMap]
  let S : Set κq := Set.range (algebraMap (R ⧸ q) κq)
  have hsplit :
      ∀ y ∈ S, IsIntegral κp y ∧ ((minpoly κp y).map (algebraMap κp κq)).Splits := by
    intro y hy
    obtain ⟨xq, rfl⟩ := hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xq
    rw [Ideal.algebraMap_quotient_residueField_mk]
    change IsIntegral κp (algebraMap R κq x) ∧
      ((minpoly κp (algebraMap R κq x)).map (algebraMap κp κq)).Splits
    obtain ⟨P, hPmap, -, hPmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic
      (Algebra.IsInvariant.charpoly_mem_lifts RFix R G x)
      (MulSemiringAction.monic_charpoly G x)
    have hroot : Polynomial.aeval x P = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hPmap, MulSemiringAction.eval_charpoly]
    have hy_aeval :
        Polynomial.aeval (algebraMap R κq x) (P.map (algebraMap RFix κp)) = 0 := by
      letI := hTower
      rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algebraMap_apply, hroot, map_zero]
    have hy_integral : IsIntegral κp (algebraMap R κq x) := by
      exact ⟨P.map (algebraMap RFix κp), hPmonic.map _, hy_aeval⟩
    have hPmapκq :
        P.map (algebraMap RFix κq) = (MulSemiringAction.charpoly G x).map (algebraMap R κq) := by
      simpa [Polynomial.map_map, IsScalarTower.algebraMap_eq RFix R κq] using
        congrArg (Polynomial.map (algebraMap R κq)) hPmap
    refine ⟨hy_integral, Polynomial.Splits.of_dvd ?_ ?_ (minpoly.dvd κp _ hy_aeval)⟩
    · letI := hTower
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq RFix κp κq, hPmapκq,
        MulSemiringAction.charpoly_eq, Polynomial.map_prod]
      exact Polynomial.Splits.prod fun _ _ ↦ (Polynomial.Splits.X_sub_C _).map _
    · exact (hPmonic.map _).ne_zero
  have hS_top : IntermediateField.adjoin κp S = ⊤ := by
    apply eq_top_iff.mpr
    intro z _
    rw [IntermediateField.mem_adjoin_range_iff κp (algebraMap (R ⧸ q) κq)]
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (R ⧸ q) z
    exact ⟨x, y, hy, hxy.symm⟩
  exact normal_of_adjoin_range_minpoly_splits
    (F := κp) (E := κq) (α := algebraMap (R ⧸ q) κq) hS_top
    (fun x ↦ (hsplit _ ⟨x, rfl⟩).1)
    (fun x ↦ (hsplit _ ⟨x, rfl⟩).2)

-- Proof sketch: the stabilizer of `q` acts on `R / q` over `(R^G) / p`, hence on
-- `Frac(R / q) = κ(q)` over `Frac((R^G) / p) = κ(p)`. The invariant-theory surjectivity theorem for
-- stabilizers then gives every automorphism of `κ(q) / κ(p)`.
/- Lemma 15.111.9 (2): the decomposition group
`D = {σ ∈ G | σ(q) = q}` surjects onto `Aut(κ(q) / κ(p))`. In this fixed-subring setting, this is
exactly the canonical invariant-theory owner theorem
`IsFractionRing.stabilizerHom_surjective`, specialized to `A = R^G`, `B = R`, `P = p`, and
`Q = q`. -/
/-- Lemma 15.111.9 (2): the decomposition group of `q` surjects onto the automorphism group of the
residue-field extension `κ(q) / κ(p)`. -/
theorem stabilizerHom_surjective_of_liesOver_fixedPoints :
    Function.Surjective (IsFractionRing.stabilizerHom G p q κp κq) := by
  -- This is exactly the fixed-subring specialization of the canonical stabilizer-owner theorem.
  exact IsFractionRing.stabilizerHom_surjective
    (A := RFix) (B := R) (G := G) (P := p) (Q := q) κp κq

end
