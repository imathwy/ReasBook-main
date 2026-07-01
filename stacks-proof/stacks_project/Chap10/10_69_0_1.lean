import Mathlib
import stacks_project.Chap10.Definition_10_70_1

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open scoped BigOperators TensorProduct Pointwise

universe u v

noncomputable section

/-- The quotient-Rees model of the associated graded ring `⊕_{n ≥ 0} I^n / I^(n + 1)` of an
ideal `I`. -/
abbrev idealAssociatedGradedRing {R : Type u} [CommRing R] (I : Ideal R) : Type u :=
  (reesAlgebra I) ⧸ Ideal.map (algebraMap R (reesAlgebra I)) I

/-- The degree-one monomial attached to an element of `I` lies in the Rees algebra of `I`. -/
theorem idealAssociatedGradedDegreeOne_mem {R : Type u} [CommRing R] {I : Ideal R} (x : I) :
    monomial 1 (x : R) ∈ reesAlgebra I := by
  refine (reesAlgebra.monomial_mem (I := I) (i := 1) (r := (x : R))).2 ?_
  simpa [pow_one] using x.2

/-- The degree-one class in the associated graded ring determined by an element of `I`. -/
def idealAssociatedGradedDegreeOne {R : Type u} [CommRing R] {I : Ideal R} (x : I) :
    idealAssociatedGradedRing I :=
  Ideal.Quotient.mk _ ⟨monomial 1 (x : R), idealAssociatedGradedDegreeOne_mem x⟩

private theorem idealAssociatedGradedIdeal_le_comap
    {R : Type u} [CommRing R] {I : Ideal R}
    {S : Type v} [CommRing S] {J : Ideal S}
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) :
    Ideal.map (algebraMap R (reesAlgebra I)) I ≤
      Ideal.comap (reesAlgebraMap f hIJ)
        (Ideal.map (algebraMap S (reesAlgebra J)) J) := by
  -- Check the defining Rees-ideal containment on the degree-zero generators coming from `I`.
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  have hfr : f r ∈ J := Ideal.mem_comap.mp (hIJ hr)
  have hmem :
      algebraMap S (reesAlgebra J) (f r) ∈ Ideal.map (algebraMap S (reesAlgebra J)) J := by
    -- The image of `f r` is one of the target generators.
    exact Ideal.mem_map_of_mem (algebraMap S (reesAlgebra J)) hfr
  have hmap :
      reesAlgebraMap f hIJ (algebraMap R (reesAlgebra I) r) =
        algebraMap S (reesAlgebra J) (f r) := by
    -- On constants, `reesAlgebraMap` acts coefficientwise by `f`.
    apply Subtype.ext
    simp [reesAlgebraMap]
  -- Rewriting the source generator image lands it in the target mapped ideal.
  simpa [Ideal.mem_comap, hmap] using hmem

/-- The canonical map on quotient-Rees models of associated graded rings induced by a ring map
sending `I` into `J`. -/
def idealAssociatedGradedMap
    {R : Type u} [CommRing R] {I : Ideal R}
    {S : Type v} [CommRing S] {J : Ideal S}
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) :
    idealAssociatedGradedRing I →+* idealAssociatedGradedRing J :=
  Ideal.quotientMap
    (Ideal.map (algebraMap S (reesAlgebra J)) J)
    (reesAlgebraMap f hIJ)
    (idealAssociatedGradedIdeal_le_comap f hIJ)

section

variable {R : Type u} [CommRing R]

/-- The quotient-Rees model of `gr_I(R)` is naturally an algebra over `R / I`. -/
instance idealAssociatedGradedRing.algebraQuotient (I : Ideal R) :
    Algebra (R ⧸ I) (idealAssociatedGradedRing I) :=
  Ideal.Quotient.algebraQuotientMapQuotient

section

variable [IsLocalRing R]

/-- For the maximal ideal of a local ring, the associated graded ring is naturally an algebra over
the residue field. -/
instance idealAssociatedGradedRing.algebraResidueField :
    Algebra (IsLocalRing.ResidueField R)
      (idealAssociatedGradedRing (IsLocalRing.maximalIdeal R)) := by
  simpa [IsLocalRing.ResidueField] using
    (idealAssociatedGradedRing.algebraQuotient (I := IsLocalRing.maximalIdeal R))

end

private abbrev idealAssociatedGradedRingQuotientMap (I : Ideal R) :
    reesAlgebra I →ₐ[R] idealAssociatedGradedRing I :=
  Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R (reesAlgebra I)) I)

/-- The degree-`n` homogeneous piece of the quotient-Rees model of the associated graded ring. -/
def idealAssociatedGradedRingGrade (I : Ideal R) (n : ℕ) :
    Submodule R (idealAssociatedGradedRing I) :=
  (reesAlgebraGrade I n).map (idealAssociatedGradedRingQuotientMap I).toLinearMap

/-- The class of an element of `I` in degree one is homogeneous of degree one. -/
theorem idealAssociatedGradedDegreeOne_mem_grade {I : Ideal R} (x : I) :
    idealAssociatedGradedDegreeOne x ∈ idealAssociatedGradedRingGrade I 1 := by
  refine ⟨reesAlgebraDegreeOne I x, reesAlgebraDegreeOne_mem I x, rfl⟩

/-- The canonical map on associated graded rings induced by `f` preserves the degree-`n`
homogeneous pieces. -/
theorem idealAssociatedGradedMap_mem_grade
    {S : Type v} [CommRing S] (I : Ideal R) (J : Ideal S)
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) (n : ℕ)
    {x : idealAssociatedGradedRing I}
    (hx : x ∈ idealAssociatedGradedRingGrade I n) :
    idealAssociatedGradedMap f hIJ x ∈ idealAssociatedGradedRingGrade J n := by
  -- Unpack the source homogeneous class to a homogeneous Rees representative.
  rcases hx with ⟨y, hy, rfl⟩
  refine ⟨reesAlgebraMap f hIJ y, ?_, rfl⟩
  -- Mapping the degree-`n` Rees representative preserves its homogeneous degree.
  rcases hy with ⟨z, rfl⟩
  refine ⟨⟨f z.1, ?_⟩, ?_⟩
  · have hmap : f z.1 ∈ Ideal.map f (I ^ n) := Ideal.mem_map_of_mem f z.2
    have hpow : Ideal.map f (I ^ n) ≤ J ^ n := by
      simpa [Ideal.map_pow] using
        (Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hIJ) n :
          Ideal.map f I ^ n ≤ J ^ n)
    exact hpow hmap
  · -- The Rees-algebra map keeps the unique degree-`n` monomial shape unchanged.
    apply Subtype.ext
    exact (Polynomial.map_monomial (f := f) (n := n) (a := z.1)).symm

/-- The degree-`n` component of the canonical map on associated graded rings induced by `f`. -/
def idealAssociatedGradedGradeMap
    {S : Type v} [CommRing S] (I : Ideal R) (J : Ideal S)
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) (n : ℕ) :
    idealAssociatedGradedRingGrade I n → idealAssociatedGradedRingGrade J n :=
  fun x ↦
    ⟨idealAssociatedGradedMap f hIJ x,
      idealAssociatedGradedMap_mem_grade I J f hIJ n x.2⟩

end

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The `n`-th stage `I^n M` of the `I`-adic filtration. -/
abbrev idealAssociatedGradedStage (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : Submodule R M :=
  ((I ^ n) • ⊤ : Submodule R M)

/-- The degree-`n` graded piece `I^n M / I^(n + 1) M`, written as the quotient of the subtype
`I^n M` by its next filtration step. -/
abbrev idealAssociatedGradedPiece (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : Type v :=
  idealAssociatedGradedStage I M n ⧸
    (idealAssociatedGradedStage I M (n + 1)).submoduleOf
      (idealAssociatedGradedStage I M n)

/-- The associated graded module `⊕_{n ≥ 0} I^n M / I^(n + 1) M` of the `I`-adic filtration. -/
abbrev idealAssociatedGradedModule (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    Type v :=
  DirectSum ℕ (idealAssociatedGradedPiece I M)

private noncomputable def idealAssociatedGradedInternalPieceEquiv
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    (idealAssociatedGradedStage I M n ⧸
        ((I) • ⊤ : Submodule R (idealAssociatedGradedStage I M n))) ≃ₗ[R]
      idealAssociatedGradedPiece I M n :=
  Submodule.quotEquivOfEq _ _ (by
    ext x
    rw [Submodule.mem_smul_top_iff]
    change ((x : M) ∈ I • idealAssociatedGradedStage I M n) ↔
      ((x : M) ∈ idealAssociatedGradedStage I M (n + 1))
    rw [← mul_smul]
    rw [show I * I ^ n = I ^ (n + 1) by
      rw [Ideal.mul_comm, ← pow_succ]])

noncomputable instance (I : Ideal R) (n : ℕ) :
    Module (R ⧸ I) (idealAssociatedGradedPiece I M n) :=
  (idealAssociatedGradedInternalPieceEquiv I M n).symm.toAddEquiv.module _

private abbrev quasiRegularIdeal (rs : List R) : Ideal R :=
  Ideal.ofList rs

/-- The internal quotient model `J^n M / J (J^n M)` used to build the polynomial action before
identifying it with the textbook quotient. -/
private abbrev quasiRegularAssociatedGradedInternalPiece
    (rs : List R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) : Type v :=
  idealAssociatedGradedStage (quasiRegularIdeal rs) M n ⧸
    ((quasiRegularIdeal rs) • ⊤ :
      Submodule R (idealAssociatedGradedStage (quasiRegularIdeal rs) M n))

/-- The internal direct-sum model built from `J^n M / J (J^n M)`. -/
private abbrev quasiRegularAssociatedGradedInternal
    (rs : List R) (M : Type v) [AddCommGroup M] [Module R M] : Type v :=
  DirectSum ℕ (quasiRegularAssociatedGradedInternalPiece rs M)

private abbrev quasiRegularTotalDegree {rs : List R} (e : Fin rs.length →₀ ℕ) : ℕ :=
  e.degree

private abbrev quasiRegularStage (rs : List R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : Submodule R M :=
  idealAssociatedGradedStage (quasiRegularIdeal rs) M n

private abbrev quasiRegularDenominator (rs : List R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : Submodule R (quasiRegularStage rs M n) :=
  ((quasiRegularIdeal rs) • ⊤ : Submodule R (quasiRegularStage rs M n))

/-- Helper for 10.69.0.1: every module element lies in the zeroth filtration stage. -/
private theorem quasiRegularStage_zero_mem
    (rs : List R) (m : M) :
    m ∈ quasiRegularStage rs M 0 := by
  -- The stage `J^0 M` is just the whole module.
  simpa [quasiRegularStage, idealAssociatedGradedStage]

/-- Helper for 10.69.0.1: multiplying the stage `I^n M` by `I^d` shifts the filtration index by
`d`. -/
private theorem idealAssociatedGradedStage_pow_smul_eq
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (d n : ℕ) :
    ((I ^ d) • idealAssociatedGradedStage I M n : Submodule R M) =
      idealAssociatedGradedStage I M (n + d) := by
  -- Rewrite `I^d • (I^n M)` as `I^(d + n) M`, then commute the nat addition in the stage index.
  calc
    ((I ^ d) • idealAssociatedGradedStage I M n : Submodule R M)
        = ((I ^ d) • ((I ^ n) • (⊤ : Submodule R M)) : Submodule R M) := rfl
    _ = (((I ^ d) * (I ^ n)) • (⊤ : Submodule R M) : Submodule R M) := by
      rw [← mul_smul]
    _ = ((I ^ (d + n)) • (⊤ : Submodule R M) : Submodule R M) := by
      rw [← pow_add]
    _ = idealAssociatedGradedStage I M (n + d) := by
      simp [idealAssociatedGradedStage, Nat.add_comm]

/-- Helper for 10.69.0.1: multiplying the denominator `I(I^n M)` by `I^d` gives the denominator
inside the shifted stage `I^(n + d) M`. -/
private theorem idealAssociatedGradedDenominator_pow_smul_eq
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (d n : ℕ) :
    ((I ^ d) • (I • idealAssociatedGradedStage I M n) : Submodule R M) =
      I • idealAssociatedGradedStage I M (n + d) := by
  -- Commute the extra `I`-factor to the front and then reuse the stage-shift lemma.
  calc
    ((I ^ d) • (I • idealAssociatedGradedStage I M n) : Submodule R M)
        = (((I ^ d) * I) • idealAssociatedGradedStage I M n : Submodule R M) := by
            rw [← mul_smul]
    _ = ((I * I ^ d) • idealAssociatedGradedStage I M n : Submodule R M) := by
      rw [Ideal.mul_comm]
    _ = (I • ((I ^ d) • idealAssociatedGradedStage I M n) : Submodule R M) := by
      rw [mul_smul]
    _ = I • idealAssociatedGradedStage I M (n + d) := by
      rw [idealAssociatedGradedStage_pow_smul_eq]

/-- The internal quotient model of the degree-`n` piece is canonically identified with the
textbook quotient `J^n M / J^(n + 1) M`. -/
private noncomputable def quasiRegularAssociatedGradedInternalPieceEquiv
    (rs : List R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    quasiRegularAssociatedGradedInternalPiece rs M n ≃ₗ[R]
      idealAssociatedGradedPiece (quasiRegularIdeal rs) M n :=
  idealAssociatedGradedInternalPieceEquiv (quasiRegularIdeal rs) M n

private noncomputable def quasiRegularAssociatedGradedAddEquiv
    (rs : List R) (M : Type v) [AddCommGroup M] [Module R M] :
    idealAssociatedGradedModule (quasiRegularIdeal rs) M ≃+
      quasiRegularAssociatedGradedInternal rs M :=
  DirectSum.congrAddEquiv fun n ↦
    (quasiRegularAssociatedGradedInternalPieceEquiv rs M n).symm.toAddEquiv

/-- The product `∏ f_i^{e_i}` attached to a monomial exponent `e`. -/
private def quasiRegularAssociatedGradedMonomialWeight
    (rs : List R) (e : Fin rs.length →₀ ℕ) : R :=
  ∏ i : Fin rs.length, rs.get i ^ e i

omit [CommRing R] in
/-- Helper for 10.69.0.1: total degree is additive on monomial exponents. -/
private theorem quasiRegularTotalDegree_add {rs : List R}
    (e f : Fin rs.length →₀ ℕ) :
    quasiRegularTotalDegree (e + f) =
      quasiRegularTotalDegree e + quasiRegularTotalDegree f := by
  -- Use that `Finsupp.degree` is an additive monoid homomorphism.
  simpa [quasiRegularTotalDegree] using
    (Finsupp.degree : (Fin rs.length →₀ ℕ) →+ ℕ).map_add e f

/-- Helper for 10.69.0.1: monomial weights multiply by adding the exponent vectors. -/
private theorem quasiRegularAssociatedGradedMonomialWeight_add (rs : List R)
    (e f : Fin rs.length →₀ ℕ) :
    quasiRegularAssociatedGradedMonomialWeight rs e *
      quasiRegularAssociatedGradedMonomialWeight rs f =
    quasiRegularAssociatedGradedMonomialWeight rs (e + f) := by
  -- Rewrite the product of monomial weights as a pointwise product and simplify each exponent.
  unfold quasiRegularAssociatedGradedMonomialWeight
  rw [← Finset.prod_mul_distrib]
  congr with i
  rw [Finsupp.add_apply, pow_add]

-- Proof sketch: each factor `rs.get i ^ e i` lies in the corresponding power of the ideal
-- generated by `rs`; multiplying these contributions places the whole product in the power whose
-- exponent is the total degree of `e`.
/-- The monomial weight attached to `e` lies in the corresponding power of the ideal generated by
the sequence `rs`. -/
private theorem quasiRegularAssociatedGradedMonomialWeight_mem_pow (rs : List R)
    (e : Fin rs.length →₀ ℕ) :
    quasiRegularAssociatedGradedMonomialWeight rs e ∈
      (quasiRegularIdeal rs) ^ quasiRegularTotalDegree e := by
  -- Each factor `rs.get i ^ e i` lies in `J ^ e i`, so their product lies in the product of
  -- those powers, which simplifies to `J ^ (∑ i, e i)`.
  have hprod :
      quasiRegularAssociatedGradedMonomialWeight rs e ∈
        ∏ i : Fin rs.length, (quasiRegularIdeal rs) ^ e i := by
    refine Ideal.prod_mem_prod ?_
    intro i hi
    have hmem : rs.get i ∈ quasiRegularIdeal rs := by
      exact Ideal.subset_span (by simpa using List.getElem_mem rs i)
    exact Ideal.pow_mem_pow hmem (e i)
  simpa [quasiRegularAssociatedGradedMonomialWeight, quasiRegularTotalDegree,
    Finsupp.degree_eq_sum, Finset.prod_pow_eq_pow_sum] using hprod

-- Proof sketch: combine membership of the monomial weight in `J^|e|` with the description of
-- `J^|e| M` as `(J^|e|) • ⊤`.
/-- Multiplying an element of `M` by the monomial weight lands in the appropriate graded piece
submodule `J^|e| M`. -/
private theorem quasiRegularAssociatedGradedMonomialWeight_smul_mem
    (rs : List R) (e : Fin rs.length →₀ ℕ)
    (m : M) :
    quasiRegularAssociatedGradedMonomialWeight rs e • m ∈
      quasiRegularStage rs M (quasiRegularTotalDegree e) := by
  -- View the graded stage as `(J ^ |e|) • ⊤` and use the ideal-power membership just proved.
  simpa [quasiRegularStage, idealAssociatedGradedStage] using
    (Submodule.smul_mem_smul
      (quasiRegularAssociatedGradedMonomialWeight_mem_pow rs e)
      (by simp : m ∈ (⊤ : Submodule R M)))

/-- Multiplication by the monomial weight on the `n`-th stage `J^n M`. -/
private theorem quasiRegularAssociatedGradedMonomialWeight_smul_mem_stage
    (rs : List R) (n : ℕ) (e : Fin rs.length →₀ ℕ)
    (m : quasiRegularStage rs M n) :
    ((quasiRegularAssociatedGradedMonomialWeight rs e) •
        (quasiRegularStage rs M n).subtype) m ∈
      quasiRegularStage rs M (n + quasiRegularTotalDegree e) := by
  -- Move the target stage back to the explicit submodule `(J^|e|) • (J^n M)`.
  rw [quasiRegularStage,
    ← idealAssociatedGradedStage_pow_smul_eq
      (I := quasiRegularIdeal rs) (M := M) (d := quasiRegularTotalDegree e) (n := n)]
  exact Submodule.smul_mem_smul
    (quasiRegularAssociatedGradedMonomialWeight_mem_pow rs e) m.2

/-- Multiplication by the monomial weight, followed by passage to the quotient
`J^|e| M / J^(|e| + 1) M`. -/
private def quasiRegularAssociatedGradedMonomialMapToPiece (rs : List R) (e : Fin rs.length →₀ ℕ) :
    M →ₗ[R]
      quasiRegularAssociatedGradedInternalPiece rs M (quasiRegularTotalDegree e) :=
  (Submodule.mkQ (quasiRegularDenominator rs M (quasiRegularTotalDegree e))).comp
    (LinearMap.codRestrict
      (quasiRegularStage rs M (quasiRegularTotalDegree e))
      ((quasiRegularAssociatedGradedMonomialWeight rs e) • (LinearMap.id : M →ₗ[R] M))
      (quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e))

-- Proof sketch: if `m ∈ J M`, then multiplying by a degree-`|e|` monomial weight moves it into
-- `J^(|e| + 1) M`, which is zero in the quotient defining the graded piece.
/-- The monomial map to the graded piece vanishes on `J M`, so it factors through `M / J M`. -/
private theorem quasiRegularAssociatedGradedMonomialMapToPiece_ker_le (rs : List R)
    (e : Fin rs.length →₀ ℕ) :
    ((quasiRegularIdeal rs) • ⊤ : Submodule R M) ≤
      LinearMap.ker
        (quasiRegularAssociatedGradedMonomialMapToPiece rs e) := by
  intro x hx
  -- Rewrite the quotient-zero test as denominator membership in the target graded piece.
  rw [LinearMap.mem_ker]
  change
    Submodule.Quotient.mk
      (⟨quasiRegularAssociatedGradedMonomialWeight rs e • x,
        quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e x⟩ :
        quasiRegularStage rs M (quasiRegularTotalDegree e)) = 0
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff]
  change quasiRegularAssociatedGradedMonomialWeight rs e • x ∈
    (quasiRegularIdeal rs) • quasiRegularStage rs M (quasiRegularTotalDegree e)
  -- Transport the target denominator back to `(J^|e|) • (J M)`.
  have hdenom :
      (((quasiRegularIdeal rs) ^ quasiRegularTotalDegree e) •
          ((quasiRegularIdeal rs) • idealAssociatedGradedStage (quasiRegularIdeal rs) M 0) :
            Submodule R M) =
        (quasiRegularIdeal rs) • quasiRegularStage rs M (quasiRegularTotalDegree e) := by
    simpa [quasiRegularStage] using
      (idealAssociatedGradedDenominator_pow_smul_eq
        (I := quasiRegularIdeal rs) (M := M) (d := quasiRegularTotalDegree e) (n := 0))
  rw [← hdenom]
  have hx_zero :
      x ∈ (quasiRegularIdeal rs) • idealAssociatedGradedStage (quasiRegularIdeal rs) M 0 := by
    simpa [idealAssociatedGradedStage] using hx
  simpa [idealAssociatedGradedStage] using
    (Submodule.smul_mem_smul
      (quasiRegularAssociatedGradedMonomialWeight_mem_pow rs e)
      hx_zero :
      quasiRegularAssociatedGradedMonomialWeight rs e • x ∈
        (((quasiRegularIdeal rs) ^ quasiRegularTotalDegree e) •
          ((quasiRegularIdeal rs) • idealAssociatedGradedStage (quasiRegularIdeal rs) M 0) :
            Submodule R M))

/-- The map `M / J M → J^|e| M / J^(|e| + 1) M` determined by the monomial exponent `e`. -/
private def quasiRegularAssociatedGradedMonomialMap (rs : List R) (e : Fin rs.length →₀ ℕ) :
    M ⧸ ((quasiRegularIdeal rs) • ⊤ : Submodule R M) →ₗ[R]
      quasiRegularAssociatedGradedInternalPiece rs M (quasiRegularTotalDegree e) :=
  Submodule.liftQ
    ((quasiRegularIdeal rs) • ⊤ : Submodule R M)
    (quasiRegularAssociatedGradedMonomialMapToPiece rs e)
    (quasiRegularAssociatedGradedMonomialMapToPiece_ker_le rs e)

/-- The class of `(\prod_i f_i^{e_i}) • m` in the degree-`|e|` graded piece. -/
private def quasiRegularAssociatedGradedInternalMonomialClass (rs : List R) (m : M)
    (e : Fin rs.length →₀ ℕ) :
    quasiRegularAssociatedGradedInternalPiece rs M (quasiRegularTotalDegree e) :=
  Submodule.Quotient.mk
    ⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
      quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩

-- Proof sketch: unfold the quotient lift defining
-- `quasiRegularAssociatedGradedMonomialMap`; on a representative `m : M` it is defined by the
-- class of `(\prod_i f_i^{e_i}) • m` in `J^|e| M / J^(|e| + 1) M`.
/-- On a representative `m : M`, the monomial map sends the class of `m` to the class of
`(\prod_i f_i^{e_i}) • m` in the degree-`|e|` graded piece. -/
private theorem quasiRegularAssociatedGradedMonomialMap_mk (rs : List R) (m : M)
    (e : Fin rs.length →₀ ℕ) :
    quasiRegularAssociatedGradedMonomialMap rs e
        (Submodule.Quotient.mk m) =
      quasiRegularAssociatedGradedInternalMonomialClass rs m e := by
  -- Unfold the quotient lift: on representatives the map is defined by the corresponding class.
  rw [quasiRegularAssociatedGradedMonomialMap, Submodule.liftQ_apply]
  rfl

/-- Multiplication by the monomial weight on the stage `J^n M`. -/
private def quasiRegularAssociatedGradedMonomialMapOnStage
    (rs : List R) (n : ℕ) (e : Fin rs.length →₀ ℕ) :
    quasiRegularStage rs M n →ₗ[R]
      quasiRegularStage rs M (n + quasiRegularTotalDegree e) :=
  LinearMap.codRestrict
    (quasiRegularStage rs M (n + quasiRegularTotalDegree e))
    ((quasiRegularAssociatedGradedMonomialWeight rs e) • (quasiRegularStage rs M n).subtype)
    (quasiRegularAssociatedGradedMonomialWeight_smul_mem_stage rs n e)

/-- Multiplication by the monomial weight sends the denominator `J (J^n M)` into the denominator
of `J^(n + |e|) M / J^(n + |e| + 1) M`. -/
private theorem quasiRegularAssociatedGradedMonomialMapOnStage_denominator_le
    (rs : List R) (n : ℕ) (e : Fin rs.length →₀ ℕ) :
    quasiRegularDenominator rs M n ≤
      (quasiRegularDenominator rs M (n + quasiRegularTotalDegree e)).comap
        (quasiRegularAssociatedGradedMonomialMapOnStage rs n e) := by
  intro x hx
  rw [Submodule.mem_smul_top_iff] at hx
  -- Unpack denominator membership in the codomain quotient as membership in `J (J^(n + |e|) M)`.
  rw [Submodule.mem_comap, Submodule.mem_smul_top_iff]
  change
    quasiRegularAssociatedGradedMonomialWeight rs e •
        ((quasiRegularStage rs M n).subtype x) ∈
      (quasiRegularIdeal rs) • quasiRegularStage rs M (n + quasiRegularTotalDegree e)
  -- Rewrite the target denominator as `(J^|e|) • (J (J^n M))` and use `x ∈ J (J^n M)`.
  rw [quasiRegularStage,
    ← idealAssociatedGradedDenominator_pow_smul_eq
      (I := quasiRegularIdeal rs) (M := M) (d := quasiRegularTotalDegree e) (n := n)]
  exact Submodule.smul_mem_smul
    (quasiRegularAssociatedGradedMonomialWeight_mem_pow rs e) hx

/-- The monomial map on the `n`-th graded piece of the associated graded module. -/
private def quasiRegularAssociatedGradedMonomialMapOnPiece
    (rs : List R) (n : ℕ) (e : Fin rs.length →₀ ℕ) :
    quasiRegularAssociatedGradedInternalPiece rs M n →ₗ[R]
      quasiRegularAssociatedGradedInternalPiece rs M (n + quasiRegularTotalDegree e) :=
  Submodule.mapQ
    (quasiRegularDenominator rs M n)
    (quasiRegularDenominator rs M (n + quasiRegularTotalDegree e))
    (quasiRegularAssociatedGradedMonomialMapOnStage rs n e)
    (quasiRegularAssociatedGradedMonomialMapOnStage_denominator_le rs n e)

-- Route correction: compute the quotient-piece monomial operators on representatives first, then
-- lift those formulas to homogeneous generators of the direct sum.

/-- Helper for 10.69.0.1: on a quotient representative, `mapQ` is the expected monomial-weight
action on the underlying stage element. -/
private theorem quasiRegularAssociatedGradedMonomialMapOnPiece_mk
    (rs : List R) (n : ℕ) (e : Fin rs.length →₀ ℕ)
    (m : quasiRegularStage rs M n) :
    quasiRegularAssociatedGradedMonomialMapOnPiece rs n e (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk
        ⟨quasiRegularAssociatedGradedMonomialWeight rs e • (m : M),
          quasiRegularAssociatedGradedMonomialWeight_smul_mem_stage rs n e m⟩ := by
  -- Unfold only the quotient map and evaluate it on the chosen representative.
  rw [quasiRegularAssociatedGradedMonomialMapOnPiece, Submodule.mapQ_apply]
  rfl

/-- Helper for 10.69.0.1: the zero exponent acts trivially on each quotient piece. -/
-- TODO(10.69.0.1): reduce this quotient-level identity to representative computations using the
-- `Submodule.mapQ` API without relying on the currently failing eliminator elaboration.
private theorem quasiRegularAssociatedGradedMonomialMapOnPiece_zero
    (rs : List R) (n : ℕ)
    (z : quasiRegularAssociatedGradedInternalPiece rs M n) :
    quasiRegularAssociatedGradedMonomialMapOnPiece rs n (0 : Fin rs.length →₀ ℕ) z = z := by
  -- Compute the quotient-piece map on one representative and simplify the zero monomial weight.
  refine Quotient.inductionOn z ?_
  intro m
  simpa [quasiRegularAssociatedGradedMonomialWeight, quasiRegularTotalDegree] using
    (quasiRegularAssociatedGradedMonomialMapOnPiece_mk
      (M := M) rs n (0 : Fin rs.length →₀ ℕ) m)

/-- The action of a monomial on the associated graded module. -/
private def quasiRegularAssociatedGradedMonomialAction
    (rs : List R) (e : Fin rs.length →₀ ℕ) :
    quasiRegularAssociatedGradedInternal rs M →ₗ[R]
      quasiRegularAssociatedGradedInternal rs M :=
  DirectSum.toModule R ℕ (quasiRegularAssociatedGradedInternal rs M) fun n ↦
    ((DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M)
        (n + quasiRegularTotalDegree e)).restrictScalars R).comp
      (quasiRegularAssociatedGradedMonomialMapOnPiece rs n e)

/-- Helper for 10.69.0.1: the monomial action sends a homogeneous generator in degree `n` to the
corresponding homogeneous generator in degree `n + |e|`. -/
private theorem quasiRegularAssociatedGradedMonomialAction_lof
    (rs : List R) (n : ℕ) (e : Fin rs.length →₀ ℕ)
    (z : quasiRegularAssociatedGradedInternalPiece rs M n) :
    quasiRegularAssociatedGradedMonomialAction rs e
        (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          (quasiRegularAssociatedGradedInternalPiece rs M) n z) =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M)
        (n + quasiRegularTotalDegree e)
        (quasiRegularAssociatedGradedMonomialMapOnPiece rs n e z) := by
  -- `DirectSum.toModule` evaluates on a single homogeneous generator by the defining branch.
  change
    (DirectSum.toModule R ℕ (quasiRegularAssociatedGradedInternal rs M) fun n ↦
        ((DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
            (quasiRegularAssociatedGradedInternalPiece rs M)
            (n + quasiRegularTotalDegree e)).restrictScalars R).comp
          (quasiRegularAssociatedGradedMonomialMapOnPiece rs n e))
      ((DirectSum.lof R ℕ (quasiRegularAssociatedGradedInternalPiece rs M) n) z) =
    (((DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          (quasiRegularAssociatedGradedInternalPiece rs M)
          (n + quasiRegularTotalDegree e)).restrictScalars R).comp
        (quasiRegularAssociatedGradedMonomialMapOnPiece rs n e)) z
  exact DirectSum.toModule_lof
    (R := R)
    (ι := ℕ)
    (M := quasiRegularAssociatedGradedInternalPiece rs M)
    (N := quasiRegularAssociatedGradedInternal rs M)
    (φ := fun n ↦
      ((DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          (quasiRegularAssociatedGradedInternalPiece rs M)
          (n + quasiRegularTotalDegree e)).restrictScalars R).comp
        (quasiRegularAssociatedGradedMonomialMapOnPiece rs n e))
    n z

/-- Helper for 10.69.0.1: transporting a stage element along an equality of degrees does not
change its underlying module element. -/
private theorem quasiRegularStage_cast_coe_eq
    (rs : List R) {n n' : ℕ} (h : n = n')
    (x : quasiRegularStage rs M n) :
    (((cast (congrArg (fun k ↦ ↥(quasiRegularStage rs M k)) h) x :
      quasiRegularStage rs M n') : M)) = x := by
  cases h
  rfl

/-- Helper for 10.69.0.1: quotienting commutes with transport between equal-degree internal
pieces. -/
private theorem quasiRegularAssociatedGradedInternalPiece_cast_mk_eq
    (rs : List R) {n n' : ℕ} (h : n = n')
    (x : quasiRegularStage rs M n) :
    (Submodule.Quotient.mk
      (cast (congrArg (fun k ↦ ↥(quasiRegularStage rs M k)) h) x) :
      quasiRegularAssociatedGradedInternalPiece rs M n') =
      cast (congrArg (quasiRegularAssociatedGradedInternalPiece rs M) h)
        (Submodule.Quotient.mk x : quasiRegularAssociatedGradedInternalPiece rs M n) := by
  cases h
  rfl

/-- Helper for 10.69.0.1: `DirectSum.lof` is unchanged by transporting the homogeneous piece along
an equality of degrees. -/
private theorem quasiRegularAssociatedGraded_lof_cast_eq
    (rs : List R) {n n' : ℕ} (h : n = n')
    (z : quasiRegularAssociatedGradedInternalPiece rs M n) :
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (quasiRegularAssociatedGradedInternalPiece rs M) n'
      (cast (congrArg (quasiRegularAssociatedGradedInternalPiece rs M) h) z) =
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (quasiRegularAssociatedGradedInternalPiece rs M) n z := by
  cases h
  rfl

/-- Helper for 10.69.0.1: composing the quotient-piece monomial maps corresponds to adding
exponents, after the canonical graded-index cast. -/
private theorem quasiRegularAssociatedGradedMonomialMapOnPiece_add
    (rs : List R) (n : ℕ) (e f : Fin rs.length →₀ ℕ)
    (z : quasiRegularAssociatedGradedInternalPiece rs M n) :
    cast (by rw [quasiRegularTotalDegree_add, Nat.add_assoc])
      (quasiRegularAssociatedGradedMonomialMapOnPiece rs (n + quasiRegularTotalDegree e) f
        (quasiRegularAssociatedGradedMonomialMapOnPiece rs n e z)) =
      quasiRegularAssociatedGradedMonomialMapOnPiece rs n (e + f) z := by
  refine Quotient.inductionOn z ?_
  intro m
  let x :
      quasiRegularStage rs M
        ((n + quasiRegularTotalDegree e) + quasiRegularTotalDegree f) :=
    ⟨quasiRegularAssociatedGradedMonomialWeight rs f •
        (quasiRegularAssociatedGradedMonomialWeight rs e • (m : M)),
      quasiRegularAssociatedGradedMonomialWeight_smul_mem_stage rs
        (n + quasiRegularTotalDegree e) f
        ⟨quasiRegularAssociatedGradedMonomialWeight rs e • (m : M),
          quasiRegularAssociatedGradedMonomialWeight_smul_mem_stage rs n e m⟩⟩
  let y :
      quasiRegularStage rs M (n + quasiRegularTotalDegree (e + f)) :=
    ⟨quasiRegularAssociatedGradedMonomialWeight rs (e + f) • (m : M),
      quasiRegularAssociatedGradedMonomialWeight_smul_mem_stage rs n (e + f) m⟩
  have h :
      (n + quasiRegularTotalDegree e) + quasiRegularTotalDegree f =
        n + quasiRegularTotalDegree (e + f) := by
    rw [quasiRegularTotalDegree_add, Nat.add_assoc]
  have hxy :
      cast (congrArg (fun k ↦ ↥(quasiRegularStage rs M k)) h) x = y := by
    apply Subtype.ext
    calc
      (((cast (congrArg (fun k ↦ ↥(quasiRegularStage rs M k)) h) x :
          quasiRegularStage rs M (n + quasiRegularTotalDegree (e + f))) : M)) = x := by
            exact quasiRegularStage_cast_coe_eq (M := M) rs h x
      _ = y := by
            simp [x, y, quasiRegularAssociatedGradedMonomialWeight_add, smul_smul, mul_comm]
  have hmk :
      cast (congrArg (quasiRegularAssociatedGradedInternalPiece rs M) h)
        (Submodule.Quotient.mk x :
          quasiRegularAssociatedGradedInternalPiece rs M
            ((n + quasiRegularTotalDegree e) + quasiRegularTotalDegree f)) =
      (Submodule.Quotient.mk y :
        quasiRegularAssociatedGradedInternalPiece rs M
          (n + quasiRegularTotalDegree (e + f))) := by
    calc
      cast (congrArg (quasiRegularAssociatedGradedInternalPiece rs M) h)
          (Submodule.Quotient.mk x :
            quasiRegularAssociatedGradedInternalPiece rs M
              ((n + quasiRegularTotalDegree e) + quasiRegularTotalDegree f)) =
        (Submodule.Quotient.mk
          (cast (congrArg (fun k ↦ ↥(quasiRegularStage rs M k)) h) x) :
            quasiRegularAssociatedGradedInternalPiece rs M
              (n + quasiRegularTotalDegree (e + f))) := by
              symm
              exact quasiRegularAssociatedGradedInternalPiece_cast_mk_eq
                (M := M) rs h x
      _ = Submodule.Quotient.mk y := by rw [hxy]
  simpa [x, y, h, quasiRegularAssociatedGradedMonomialMapOnPiece_mk] using hmk

/-- Helper for 10.69.0.1: successive monomial actions on a homogeneous generator correspond to
adding the exponent vectors. -/
private theorem quasiRegularAssociatedGradedMonomialAction_comp_lof
    (rs : List R) (n : ℕ) (e f : Fin rs.length →₀ ℕ)
    (z : quasiRegularAssociatedGradedInternalPiece rs M n) :
    quasiRegularAssociatedGradedMonomialAction rs f
        (quasiRegularAssociatedGradedMonomialAction rs e
          (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          (quasiRegularAssociatedGradedInternalPiece rs M) n z)) =
      quasiRegularAssociatedGradedMonomialAction rs (e + f)
        (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          (quasiRegularAssociatedGradedInternalPiece rs M) n z) := by
  let h :
      (n + quasiRegularTotalDegree e) + quasiRegularTotalDegree f =
        n + quasiRegularTotalDegree (e + f) := by
    rw [quasiRegularTotalDegree_add, Nat.add_assoc]
  calc
    quasiRegularAssociatedGradedMonomialAction rs f
        (quasiRegularAssociatedGradedMonomialAction rs e
          (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
            (quasiRegularAssociatedGradedInternalPiece rs M) n z)) =
      quasiRegularAssociatedGradedMonomialAction rs f
        (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          (quasiRegularAssociatedGradedInternalPiece rs M)
          (n + quasiRegularTotalDegree e)
          (quasiRegularAssociatedGradedMonomialMapOnPiece rs n e z)) := by
            rw [quasiRegularAssociatedGradedMonomialAction_lof]
    _ =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M)
        ((n + quasiRegularTotalDegree e) + quasiRegularTotalDegree f)
        (quasiRegularAssociatedGradedMonomialMapOnPiece rs (n + quasiRegularTotalDegree e) f
          (quasiRegularAssociatedGradedMonomialMapOnPiece rs n e z)) := by
            simpa using quasiRegularAssociatedGradedMonomialAction_lof
              (M := M) rs (n + quasiRegularTotalDegree e) f
              (quasiRegularAssociatedGradedMonomialMapOnPiece rs n e z)
    _ =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M)
        (n + quasiRegularTotalDegree (e + f))
        (cast (congrArg (quasiRegularAssociatedGradedInternalPiece rs M) h)
          (quasiRegularAssociatedGradedMonomialMapOnPiece rs (n + quasiRegularTotalDegree e) f
            (quasiRegularAssociatedGradedMonomialMapOnPiece rs n e z))) := by
              simpa using
                (quasiRegularAssociatedGraded_lof_cast_eq (M := M) rs h
                  (quasiRegularAssociatedGradedMonomialMapOnPiece rs
                    (n + quasiRegularTotalDegree e) f
                    (quasiRegularAssociatedGradedMonomialMapOnPiece rs n e z))).symm
    _ =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M)
        (n + quasiRegularTotalDegree (e + f))
        (quasiRegularAssociatedGradedMonomialMapOnPiece rs n (e + f) z) := by
              rw [quasiRegularAssociatedGradedMonomialMapOnPiece_add (M := M) rs n e f z]
    _ =
      quasiRegularAssociatedGradedMonomialAction rs (e + f)
        (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          (quasiRegularAssociatedGradedInternalPiece rs M) n z) := by
            simpa using (quasiRegularAssociatedGradedMonomialAction_lof
              (M := M) rs n (e + f) z
              ).symm

/-- Helper for 10.69.0.1: the zero exponent acts trivially on the whole internal direct sum. -/
-- TODO(10.69.0.1): prove this by `DirectSum.induction_on` after the zero-action formula on each
-- quotient piece has been repaired.
private theorem quasiRegularAssociatedGradedMonomialAction_zero
    (rs : List R) (x : quasiRegularAssociatedGradedInternal rs M) :
    quasiRegularAssociatedGradedMonomialAction rs (0 : Fin rs.length →₀ ℕ) x = x := by
  induction x using DirectSum.induction_on with
  | zero =>
      -- The zero direct-sum element is fixed by any linear endomorphism.
      simp
  | of n z =>
      -- On a homogeneous generator, reduce to the degreewise zero-exponent computation.
      simpa [quasiRegularTotalDegree, quasiRegularAssociatedGradedMonomialMapOnPiece_zero
        (M := M) rs n z] using
        (quasiRegularAssociatedGradedMonomialAction_lof
          (M := M) rs n (0 : Fin rs.length →₀ ℕ) z)
  | add x y hx hy =>
      -- Extend from generators to arbitrary direct-sum elements by additivity.
      simp [map_add, hx, hy]

/-- Helper for 10.69.0.1: composing monomial actions on the whole internal direct sum corresponds
to adding exponent vectors. -/
private theorem quasiRegularAssociatedGradedMonomialAction_add
    (rs : List R) (e f : Fin rs.length →₀ ℕ)
    (x : quasiRegularAssociatedGradedInternal rs M) :
    quasiRegularAssociatedGradedMonomialAction rs f
        (quasiRegularAssociatedGradedMonomialAction rs e x) =
      quasiRegularAssociatedGradedMonomialAction rs (e + f) x := by
  induction x using DirectSum.induction_on with
  | zero =>
      -- The linear monomial actions both send `0` to `0`.
      simp
  | of n z =>
      -- Reduce to the generator computation proved just above.
      exact quasiRegularAssociatedGradedMonomialAction_comp_lof
        (rs := rs) (n := n) (e := e) (f := f) z
  | add x y hx hy =>
      -- Extend from generators to arbitrary direct-sum elements by additivity.
      simp [map_add, hx, hy]

/-- The polynomial action on the associated graded module defined by the monomial operators above.
-/
private def quasiRegularAssociatedGradedPolynomialSmul (rs : List R)
    (p : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) :
    quasiRegularAssociatedGradedInternal rs M →
      quasiRegularAssociatedGradedInternal rs M :=
  fun x ↦ Finsupp.sum p fun e a ↦ a • quasiRegularAssociatedGradedMonomialAction rs e x

private instance quasiRegularAssociatedGradedInternalSMul (rs : List R) :
    SMul (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
      (quasiRegularAssociatedGradedInternal rs M) where
  smul p x := quasiRegularAssociatedGradedPolynomialSmul rs p x

/-- Helper for 10.69.0.1: a single monomial polynomial acts by its coefficient times the matching
monomial action. -/
private theorem quasiRegularAssociatedGradedPolynomialSmul_monomial
    (rs : List R) (a : R ⧸ Ideal.ofList rs) (e : Fin rs.length →₀ ℕ)
    (x : quasiRegularAssociatedGradedInternal rs M) :
    (MvPolynomial.monomial e a) • x =
      a • quasiRegularAssociatedGradedMonomialAction rs e x := by
  -- Collapse the defining polynomial sum to its unique nonzero monomial term.
  change quasiRegularAssociatedGradedPolynomialSmul rs (MvPolynomial.monomial e a) x =
    a • quasiRegularAssociatedGradedMonomialAction rs e x
  simpa [quasiRegularAssociatedGradedPolynomialSmul] using
    (MvPolynomial.sum_monomial_eq
      (u := e) (r := a)
      (b := fun d b ↦ b • quasiRegularAssociatedGradedMonomialAction rs d x))

private theorem quasiRegularAssociatedGradedInternal_one_smul
    (rs : List R) (x : quasiRegularAssociatedGradedInternal rs M) :
    (1 : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) • x = x := by
  -- Rewrite `1` as the zero monomial and use the zero-exponent action computation.
  rw [MvPolynomial.one_def, quasiRegularAssociatedGradedPolynomialSmul_monomial]
  simpa using quasiRegularAssociatedGradedMonomialAction_zero (rs := rs) (x := x)

-- TODO(10.69.0.1): split the finite-support polynomial sum in a way compatible with the current
-- `Finsupp.sum` elaboration, then recover additivity of the polynomial action.
/-- Helper for 10.69.0.1: the custom polynomial action is additive in the polynomial argument. -/
private theorem quasiRegularAssociatedGradedPolynomialSmul_add_split
    (rs : List R) (p q : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
    (x : quasiRegularAssociatedGradedInternal rs M) :
    quasiRegularAssociatedGradedPolynomialSmul rs (p + q) x =
      quasiRegularAssociatedGradedPolynomialSmul rs p x +
        quasiRegularAssociatedGradedPolynomialSmul rs q x := by
  unfold quasiRegularAssociatedGradedPolynomialSmul
  exact Finsupp.sum_add_index'
    (fun _ => zero_smul _ _)
    (fun _ _ _ => add_smul _ _ _)

private theorem quasiRegularAssociatedGradedInternal_add_smul
    (rs : List R) (p q : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
    (x : quasiRegularAssociatedGradedInternal rs M) :
    (p + q) • x = p • x + q • x := by
  -- Route correction: once the defining finite-support sum is split, scalar additivity is exact.
  exact quasiRegularAssociatedGradedPolynomialSmul_add_split (M := M) rs p q x

-- TODO(10.69.0.1): evaluate the defining finite-support sum of the zero polynomial directly.
private theorem quasiRegularAssociatedGradedInternal_zero_smul
    (rs : List R) (x : quasiRegularAssociatedGradedInternal rs M) :
    (0 : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) • x = 0 := by
  -- Unfold the custom scalar action and evaluate the empty finite-support sum for `0`.
  change quasiRegularAssociatedGradedPolynomialSmul rs 0 x = 0
  rfl

-- TODO(10.69.0.1): recover right-additivity of the polynomial action once the scalar-additivity
-- lemma above is repaired.
private theorem quasiRegularAssociatedGradedInternal_smul_zero
    (rs : List R) (p : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) :
    p • (0 : quasiRegularAssociatedGradedInternal rs M) = 0 := by
  -- Each monomial operator is linear, so every summand in the defining polynomial action vanishes.
  change quasiRegularAssociatedGradedPolynomialSmul rs p 0 = 0
  simp [quasiRegularAssociatedGradedPolynomialSmul]

-- TODO(10.69.0.1): prove distributivity over the direct-sum argument by induction on the
-- polynomial once `add_smul` is stabilized.
private theorem quasiRegularAssociatedGradedInternal_smul_add
    (rs : List R) (p : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
    (x y : quasiRegularAssociatedGradedInternal rs M) :
    p • (x + y) = p • x + p • y := by
  induction p using MvPolynomial.induction_on' with
  | monomial e a =>
      rw [quasiRegularAssociatedGradedPolynomialSmul_monomial,
        quasiRegularAssociatedGradedPolynomialSmul_monomial,
        quasiRegularAssociatedGradedPolynomialSmul_monomial]
      rw [LinearMap.map_add, smul_add]
  | add p q hp hq =>
      simp [quasiRegularAssociatedGradedInternal_add_smul, hp, hq, add_assoc,
        add_left_comm]

/-- Helper for 10.69.0.1: each quotient-piece monomial operator commutes with the ambient
`R / J`-scalar action. -/
private theorem quasiRegularAssociatedGradedMonomialMapOnPiece_map_smul
    (rs : List R) (n : ℕ) (a : R ⧸ Ideal.ofList rs) (e : Fin rs.length →₀ ℕ)
    (z : quasiRegularAssociatedGradedInternalPiece rs M n) :
    quasiRegularAssociatedGradedMonomialMapOnPiece rs n e (a • z) =
      a • quasiRegularAssociatedGradedMonomialMapOnPiece rs n e z := by
  refine Quotient.inductionOn₂ a z ?_
  intro r m
  change quasiRegularAssociatedGradedMonomialMapOnPiece rs n e
      (r • (Submodule.Quotient.mk m : quasiRegularAssociatedGradedInternalPiece rs M n)) =
    r • quasiRegularAssociatedGradedMonomialMapOnPiece rs n e (Submodule.Quotient.mk m)
  rw [← Submodule.Quotient.mk_smul, quasiRegularAssociatedGradedMonomialMapOnPiece_mk,
    quasiRegularAssociatedGradedMonomialMapOnPiece_mk, ← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  simp [smul_smul, mul_comm]

/-- Helper for 10.69.0.1: each monomial action commutes with the ambient `R / J`-scalar action.
-/
private theorem quasiRegularAssociatedGradedMonomialAction_map_smul
    (rs : List R) (a : R ⧸ Ideal.ofList rs) (e : Fin rs.length →₀ ℕ)
    (x : quasiRegularAssociatedGradedInternal rs M) :
    quasiRegularAssociatedGradedMonomialAction rs e (a • x) =
      a • quasiRegularAssociatedGradedMonomialAction rs e x := by
  induction x using DirectSum.induction_on with
  | zero =>
      simp
  | of n z =>
      change (quasiRegularAssociatedGradedMonomialAction rs e)
          (a • DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
            (quasiRegularAssociatedGradedInternalPiece rs M) n z) =
        a •
          (quasiRegularAssociatedGradedMonomialAction rs e)
            (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
              (quasiRegularAssociatedGradedInternalPiece rs M) n z)
      rw [← (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M) n).map_smul,
        quasiRegularAssociatedGradedMonomialAction_lof,
        quasiRegularAssociatedGradedMonomialAction_lof,
        ← (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          (quasiRegularAssociatedGradedInternalPiece rs M)
          (n + quasiRegularTotalDegree e)).map_smul]
      congr 1
      exact quasiRegularAssociatedGradedMonomialMapOnPiece_map_smul
        (M := M) rs n a e z
  | add x y hx hy =>
      simp [map_add, hx, hy]

/-- Helper for 10.69.0.1: multiplying on the right by a monomial polynomial acts by the
corresponding scalar followed by the matching monomial operator. -/
private theorem quasiRegularAssociatedGradedInternal_mul_smul_monomial
    (rs : List R) (p : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
    (e : Fin rs.length →₀ ℕ) (a : R ⧸ Ideal.ofList rs)
    (x : quasiRegularAssociatedGradedInternal rs M) :
    (p * MvPolynomial.monomial e a) • x =
      p • (a • quasiRegularAssociatedGradedMonomialAction rs e x) := by
  induction p using MvPolynomial.induction_on' with
  | monomial f b =>
      rw [MvPolynomial.monomial_mul, quasiRegularAssociatedGradedPolynomialSmul_monomial,
        quasiRegularAssociatedGradedPolynomialSmul_monomial,
        quasiRegularAssociatedGradedMonomialAction_map_smul,
        quasiRegularAssociatedGradedMonomialAction_add (M := M) (rs := rs) (e := e) (f := f)]
      simp [smul_smul, add_comm, mul_comm]
  | add p q hp hq =>
      rw [add_mul, quasiRegularAssociatedGradedInternal_add_smul, hp, hq,
        quasiRegularAssociatedGradedInternal_add_smul]

-- TODO(10.69.0.1): after restoring the polynomial-module distributivity lemmas, prove the
-- monomial-monomial case and extend bilinearly to all polynomials.
private theorem quasiRegularAssociatedGradedInternal_mul_smul
    (rs : List R) (p q : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
    (x : quasiRegularAssociatedGradedInternal rs M) :
    (p * q) • x = p • q • x := by
  induction q using MvPolynomial.induction_on' with
  | monomial e a =>
      simpa [quasiRegularAssociatedGradedPolynomialSmul_monomial] using
        quasiRegularAssociatedGradedInternal_mul_smul_monomial (M := M) rs p e a x
  | add q₁ q₂ hq₁ hq₂ =>
      simp [mul_add, quasiRegularAssociatedGradedInternal_add_smul,
        quasiRegularAssociatedGradedInternal_smul_add, hq₁, hq₂]

private instance quasiRegularAssociatedGradedInternalModule (rs : List R) :
    Module (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
      (quasiRegularAssociatedGradedInternal rs M) where
  smul := (· • ·)
  one_smul := quasiRegularAssociatedGradedInternal_one_smul rs
  mul_smul := quasiRegularAssociatedGradedInternal_mul_smul rs
  smul_add := quasiRegularAssociatedGradedInternal_smul_add rs
  smul_zero := quasiRegularAssociatedGradedInternal_smul_zero rs
  add_smul := quasiRegularAssociatedGradedInternal_add_smul rs
  zero_smul := quasiRegularAssociatedGradedInternal_zero_smul rs

private theorem quasiRegularAssociatedGradedDegreeZeroInclusion_map_add
    (rs : List R)
    (x y : M ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R M)) :
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ) (x + y)) =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ) x) +
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ) y) := by
  -- Compose additivity of the degree-zero monomial map with additivity of `DirectSum.lof`.
  rw [(quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)).map_add]
  exact (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
    (quasiRegularAssociatedGradedInternalPiece rs M) 0).map_add _ _

-- TODO(10.69.0.1): show the degree-zero inclusion is quotient-linear over `R / J`; the current
-- failure is a scalar-compatibility elaboration issue for `map_smul_of_tower`.
private theorem quasiRegularAssociatedGradedDegreeZeroInclusion_map_smul
    (rs : List R) (a : R ⧸ Ideal.ofList rs)
    (x : M ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R M)) :
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ) (a • x)) =
      a • DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ) x) := by
  refine Quotient.inductionOn₂ a x ?_
  intro r m
  change DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (quasiRegularAssociatedGradedInternalPiece rs M) 0
      (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)
        (r • (Submodule.Quotient.mk m : M ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R M)))) =
    r • DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (quasiRegularAssociatedGradedInternalPiece rs M) 0
      (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)
        (Submodule.Quotient.mk m))
  have hclass :
      quasiRegularAssociatedGradedInternalMonomialClass rs (r • m)
          (0 : Fin rs.length →₀ ℕ) =
        r • quasiRegularAssociatedGradedInternalMonomialClass rs m
          (0 : Fin rs.length →₀ ℕ) := by
    simpa [quasiRegularAssociatedGradedInternalMonomialClass,
      quasiRegularAssociatedGradedMonomialWeight] using
      (Submodule.Quotient.mk_smul
        (p := quasiRegularDenominator rs M 0) r
        (⟨m, quasiRegularStage_zero_mem (M := M) rs m⟩ :
          quasiRegularStage rs M 0))
  have hmap :
      quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)
          (r • (Submodule.Quotient.mk m : M ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R M))) =
        r • quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)
          (Submodule.Quotient.mk m) := by
    rw [← Submodule.Quotient.mk_smul, quasiRegularAssociatedGradedMonomialMap_mk,
      quasiRegularAssociatedGradedMonomialMap_mk]
    exact hclass
  calc
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)
          (r • (Submodule.Quotient.mk m : M ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R M)))) =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M) 0
        (r • quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)
          (Submodule.Quotient.mk m)) := by
          exact congrArg
            (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
              (quasiRegularAssociatedGradedInternalPiece rs M) 0) hmap
    _ = r • DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)
          (Submodule.Quotient.mk m)) := by
          exact
            (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
              (quasiRegularAssociatedGradedInternalPiece rs M) 0).map_smul r
              (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)
                (Submodule.Quotient.mk m))

/-- The degree-zero inclusion `M / J M → ⊕_{n ≥ 0} J^n M / J^(n + 1) M`. -/
private def quasiRegularAssociatedGradedDegreeZeroInclusion (rs : List R) :
    M ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R M) →ₗ[R ⧸ Ideal.ofList rs]
      quasiRegularAssociatedGradedInternal rs M :=
  { toFun := fun x ↦
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ) x)
    map_add' := quasiRegularAssociatedGradedDegreeZeroInclusion_map_add rs
    map_smul' := quasiRegularAssociatedGradedDegreeZeroInclusion_map_smul rs }

-- TODO(10.69.0.1): after the polynomial-action distributivity lemmas are restored, repackage the
-- tower law by induction on the polynomial argument.
private theorem quasiRegularAssociatedGradedInternal_isScalarTower (rs : List R) :
    IsScalarTower (R ⧸ quasiRegularIdeal rs)
      (MvPolynomial (Fin rs.length) (R ⧸ quasiRegularIdeal rs))
      (quasiRegularAssociatedGradedInternal rs M) := by
  constructor
  intro a p x
  induction p using MvPolynomial.induction_on' with
  | monomial e b =>
      rw [MvPolynomial.smul_monomial, quasiRegularAssociatedGradedPolynomialSmul_monomial,
        quasiRegularAssociatedGradedPolynomialSmul_monomial]
      simp [smul_smul]
  | add p q hp hq =>
      simp [quasiRegularAssociatedGradedInternal_add_smul, hp, hq]

private instance quasiRegularAssociatedGradedInternalIsScalarTower (rs : List R) :
    IsScalarTower (R ⧸ quasiRegularIdeal rs)
      (MvPolynomial (Fin rs.length) (R ⧸ quasiRegularIdeal rs))
      (quasiRegularAssociatedGradedInternal rs M) :=
  quasiRegularAssociatedGradedInternal_isScalarTower rs

noncomputable instance (rs : List R) :
    Module (MvPolynomial (Fin rs.length) (R ⧸ quasiRegularIdeal rs))
      (idealAssociatedGradedModule (quasiRegularIdeal rs) M) := by
  let _ :
      IsScalarTower (R ⧸ quasiRegularIdeal rs)
        (MvPolynomial (Fin rs.length) (R ⧸ quasiRegularIdeal rs))
        (quasiRegularAssociatedGradedInternal rs M) :=
    quasiRegularAssociatedGradedInternal_isScalarTower rs
  exact (quasiRegularAssociatedGradedAddEquiv rs M).module _

/-- Helper for 10.69.0.1: the zero-exponent monomial class is represented by the obvious stage-zero
quotient class. -/
private theorem quasiRegularAssociatedGradedInternalMonomialClass_zero_eq_mk
    (rs : List R) (m : M) :
    quasiRegularAssociatedGradedInternalMonomialClass rs m (0 : Fin rs.length →₀ ℕ) =
      Submodule.Quotient.mk
        ((⟨m, quasiRegularStage_zero_mem (M := M) rs m⟩ : quasiRegularStage rs M 0)) := by
  -- Rewrite the zero monomial weight to `1`, so the two stage-zero representatives agree.
  rw [quasiRegularAssociatedGradedInternalMonomialClass]
  change
    (Submodule.Quotient.mk
      ((⟨quasiRegularAssociatedGradedMonomialWeight rs (0 : Fin rs.length →₀ ℕ) • m,
        quasiRegularAssociatedGradedMonomialWeight_smul_mem rs
          (0 : Fin rs.length →₀ ℕ) m⟩ :
        quasiRegularStage rs M 0)) :
      quasiRegularAssociatedGradedInternalPiece rs M 0) =
      Submodule.Quotient.mk
        ((⟨m, quasiRegularStage_zero_mem (M := M) rs m⟩ : quasiRegularStage rs M 0))
  simp [quasiRegularAssociatedGradedMonomialWeight]

/-- Helper for 10.69.0.1: transporting a stage element along an equality of degrees does not
change its underlying module element. -/
private theorem quasiRegularStage_cast_coe
    (rs : List R) {n n' : ℕ} (h : n = n')
    (x : quasiRegularStage rs M n) :
    (((cast (congrArg (fun k ↦ ↥(quasiRegularStage rs M k)) h) x :
      quasiRegularStage rs M n') : M)) = x := by
  cases h
  rfl

/-- Helper for 10.69.0.1: quotienting commutes with transport between equal-degree internal
pieces. -/
private theorem quasiRegularAssociatedGradedInternalPiece_cast_mk
    (rs : List R) {n n' : ℕ} (h : n = n')
    (x : quasiRegularStage rs M n) :
    (Submodule.Quotient.mk
      (cast (congrArg (fun k ↦ ↥(quasiRegularStage rs M k)) h) x) :
      quasiRegularAssociatedGradedInternalPiece rs M n') =
      cast (congrArg (quasiRegularAssociatedGradedInternalPiece rs M) h)
        (Submodule.Quotient.mk x : quasiRegularAssociatedGradedInternalPiece rs M n) := by
  cases h
  rfl

/-- Helper for 10.69.0.1: `DirectSum.lof` is unchanged by transporting the homogeneous piece along
an equality of degrees. -/
private theorem quasiRegularAssociatedGraded_lof_cast
    (rs : List R) {n n' : ℕ} (h : n = n')
    (z : quasiRegularAssociatedGradedInternalPiece rs M n) :
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (quasiRegularAssociatedGradedInternalPiece rs M) n'
      (cast (congrArg (quasiRegularAssociatedGradedInternalPiece rs M) h) z) =
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (quasiRegularAssociatedGradedInternalPiece rs M) n z := by
  cases h
  rfl

/-- Helper for 10.69.0.1: the explicit stage-zero monomial representative transports along
`|e| = 0 + |e|` to the usual representative in degree `|e|`. -/
private theorem quasiRegularAssociatedGradedMonomialRepresentative_cast_zero_add
    (rs : List R) (m : M) (e : Fin rs.length →₀ ℕ) :
    (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
      quasiRegularAssociatedGradedMonomialWeight_smul_mem_stage rs 0 e
        ⟨m, quasiRegularStage_zero_mem (M := M) rs m⟩⟩ :
      quasiRegularStage rs M (0 + quasiRegularTotalDegree e)) =
      cast (congrArg (fun n ↦ ↥(quasiRegularStage rs M n))
        (by simpa using (Nat.zero_add (quasiRegularTotalDegree e))))
        (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
          quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ :
          quasiRegularStage rs M (quasiRegularTotalDegree e)) := by
  -- Normalize the index transport at the stage-representative level before quotienting.
  let h : quasiRegularTotalDegree e = 0 + quasiRegularTotalDegree e := by
    simpa using (Nat.zero_add (quasiRegularTotalDegree e))
  apply Subtype.ext
  change
    quasiRegularAssociatedGradedMonomialWeight rs e • m =
      ↑(cast (congrArg (fun n ↦ ↥(quasiRegularStage rs M n)) h)
        (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
          quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ :
          quasiRegularStage rs M (quasiRegularTotalDegree e)))
  exact
    (quasiRegularStage_cast_coe (M := M) rs h
      (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
        quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ :
          quasiRegularStage rs M (quasiRegularTotalDegree e))).symm

/-- Helper for 10.69.0.1: the quotient class coming from the stage-zero computation is the usual
monomial class after transporting the target degree from `|e|` to `0 + |e|`. -/
private theorem quasiRegularAssociatedGradedInternalMonomialClass_cast_zero_add
    (rs : List R) (m : M) (e : Fin rs.length →₀ ℕ) :
    (Submodule.Quotient.mk
      (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
        quasiRegularAssociatedGradedMonomialWeight_smul_mem_stage rs 0 e
          ⟨m, quasiRegularStage_zero_mem (M := M) rs m⟩⟩ :
        quasiRegularStage rs M (0 + quasiRegularTotalDegree e)) :
      quasiRegularAssociatedGradedInternalPiece rs M (0 + quasiRegularTotalDegree e)) =
      (cast (congrArg (quasiRegularAssociatedGradedInternalPiece rs M)
        (by simpa using (Nat.zero_add (quasiRegularTotalDegree e))))
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e)) := by
  -- Lift the representative-level transport through the quotient constructor.
  let h : quasiRegularTotalDegree e = 0 + quasiRegularTotalDegree e := by
    simpa using (Nat.zero_add (quasiRegularTotalDegree e))
  calc
    (Submodule.Quotient.mk
      (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
        quasiRegularAssociatedGradedMonomialWeight_smul_mem_stage rs 0 e
          ⟨m, quasiRegularStage_zero_mem (M := M) rs m⟩⟩ :
        quasiRegularStage rs M (0 + quasiRegularTotalDegree e)) :
      quasiRegularAssociatedGradedInternalPiece rs M (0 + quasiRegularTotalDegree e)) =
      (Submodule.Quotient.mk
        (cast (congrArg (fun n ↦ ↥(quasiRegularStage rs M n))
          h
          )
          (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
            quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ :
            quasiRegularStage rs M (quasiRegularTotalDegree e))) :
        quasiRegularAssociatedGradedInternalPiece rs M (0 + quasiRegularTotalDegree e)) := by
          simpa using congrArg
            (fun x : quasiRegularStage rs M (0 + quasiRegularTotalDegree e) ↦
              (Submodule.Quotient.mk x :
                quasiRegularAssociatedGradedInternalPiece rs M
                  (0 + quasiRegularTotalDegree e)))
            (quasiRegularAssociatedGradedMonomialRepresentative_cast_zero_add
              (M := M) rs m e)
    _ =
      cast (congrArg (quasiRegularAssociatedGradedInternalPiece rs M)
        h)
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e) := by
          change
            (Submodule.Quotient.mk
              (cast (congrArg (fun n ↦ ↥(quasiRegularStage rs M n)) h)
                (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
                  quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ :
                  quasiRegularStage rs M (quasiRegularTotalDegree e))) :
              quasiRegularAssociatedGradedInternalPiece rs M (0 + quasiRegularTotalDegree e)) =
            cast (congrArg (quasiRegularAssociatedGradedInternalPiece rs M) h)
              (Submodule.Quotient.mk
                (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
                  quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ :
                  quasiRegularStage rs M (quasiRegularTotalDegree e)) :
                quasiRegularAssociatedGradedInternalPiece rs M (quasiRegularTotalDegree e))
          exact
            quasiRegularAssociatedGradedInternalPiece_cast_mk (M := M) rs h
              (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
                quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ :
                  quasiRegularStage rs M (quasiRegularTotalDegree e))

/-- Helper for 10.69.0.1: the homogeneous generator `DirectSum.lof` ignores the normalization
transport from `|e|` to `0 + |e|`. -/
private theorem quasiRegularAssociatedGraded_lof_cast_zero_add
    (rs : List R) (e : Fin rs.length →₀ ℕ)
    (z : quasiRegularAssociatedGradedInternalPiece rs M (quasiRegularTotalDegree e)) :
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (quasiRegularAssociatedGradedInternalPiece rs M)
      (0 + quasiRegularTotalDegree e)
      ((cast (congrArg (quasiRegularAssociatedGradedInternalPiece rs M)
        (by simpa using (Nat.zero_add (quasiRegularTotalDegree e)))) z)) =
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (quasiRegularAssociatedGradedInternalPiece rs M)
      (quasiRegularTotalDegree e) z := by
  -- The direct-sum generator transport is definitionally trivial after normalizing the index.
  let h : quasiRegularTotalDegree e = 0 + quasiRegularTotalDegree e := by
    simpa using (Nat.zero_add (quasiRegularTotalDegree e))
  change
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (quasiRegularAssociatedGradedInternalPiece rs M)
      (0 + quasiRegularTotalDegree e)
      (cast (congrArg (quasiRegularAssociatedGradedInternalPiece rs M) h) z) =
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (quasiRegularAssociatedGradedInternalPiece rs M)
      (quasiRegularTotalDegree e) z
  exact quasiRegularAssociatedGraded_lof_cast (M := M) rs h z

/-- Helper for 10.69.0.1: acting on the degree-zero monomial class computes the expected
representative-level monomial class, with the target index normalized from `0 + |e|` to `|e|`.
-/
private theorem quasiRegularAssociatedGradedMonomialMapOnPiece_zero_class_aux
    (rs : List R) (m : M) (e : Fin rs.length →₀ ℕ) :
    quasiRegularAssociatedGradedMonomialMapOnPiece rs 0 e
        (quasiRegularAssociatedGradedInternalMonomialClass rs m (0 : Fin rs.length →₀ ℕ)) =
      (cast (congrArg (quasiRegularAssociatedGradedInternalPiece rs M)
        (by simpa using (Nat.zero_add (quasiRegularTotalDegree e))))
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e)) := by
  -- Route correction: compute on the explicit stage-zero representative first, then use the
  -- dedicated quotient-level transport lemma instead of rewriting under `cast`.
  rw [quasiRegularAssociatedGradedInternalMonomialClass_zero_eq_mk]
  let m0 : quasiRegularStage rs M 0 := ⟨m, quasiRegularStage_zero_mem (M := M) rs m⟩
  simpa [m0] using
    (quasiRegularAssociatedGradedMonomialMapOnPiece_mk (M := M) rs 0 e m0).trans
      (quasiRegularAssociatedGradedInternalMonomialClass_cast_zero_add (M := M) rs m e)

-- Proof sketch: a monomial acts on the degree-zero piece by multiplication with the corresponding
-- monomial weight, landing in the graded piece indexed by its total degree.
/-- The action of a monomial on a degree-zero class is the expected class of the monomial-weighted
representative in the corresponding graded piece. -/
private theorem quasiRegularAssociatedGradedMonomialAction_degreeZero_mk
    (rs : List R) (m : M) (e : Fin rs.length →₀ ℕ) :
    quasiRegularAssociatedGradedMonomialAction rs e
        (quasiRegularAssociatedGradedDegreeZeroInclusion rs (Submodule.Quotient.mk m)) =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M)
        (quasiRegularTotalDegree e)
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e) := by
  -- Route correction: unfold the degree-zero inclusion to a homogeneous generator, compute the
  -- monomial action there, and only then normalize the final `DirectSum.lof` transport.
  calc
    quasiRegularAssociatedGradedMonomialAction rs e
        (quasiRegularAssociatedGradedDegreeZeroInclusion rs (Submodule.Quotient.mk m)) =
      quasiRegularAssociatedGradedMonomialAction rs e
        (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          (quasiRegularAssociatedGradedInternalPiece rs M) 0
          (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)
            (Submodule.Quotient.mk m))) := by
          rfl
    _ =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M)
        (0 + quasiRegularTotalDegree e)
        (quasiRegularAssociatedGradedMonomialMapOnPiece rs 0 e
          (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)
            (Submodule.Quotient.mk m))) := by
          -- Evaluate the monomial action on the degree-zero homogeneous generator.
          exact quasiRegularAssociatedGradedMonomialAction_lof
            (M := M) rs 0 e
            (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)
              (Submodule.Quotient.mk m))
    _ =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M)
        (0 + quasiRegularTotalDegree e)
        (cast (congrArg (quasiRegularAssociatedGradedInternalPiece rs M)
          (by simpa using (Nat.zero_add (quasiRegularTotalDegree e))))
          (quasiRegularAssociatedGradedInternalMonomialClass rs m e)) := by
          -- Rewrite the inner degree-zero class using the stabilized quotient-level cast API.
          rw [quasiRegularAssociatedGradedMonomialMap_mk]
          rw [quasiRegularAssociatedGradedMonomialMapOnPiece_zero_class_aux (M := M)]
    _ =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M)
        (quasiRegularTotalDegree e)
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e) := by
          -- Normalize the target index from `0 + |e|` back to `|e|`.
          exact quasiRegularAssociatedGraded_lof_cast_zero_add (M := M) rs e
            (quasiRegularAssociatedGradedInternalMonomialClass rs m e)

private instance quasiRegularSequenceAssociatedGradedSourceModule
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R) :
    Module (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
      (TensorProduct (R ⧸ Ideal.ofList rs)
        (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
        (N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N))) :=
  TensorProduct.leftModule

private instance quasiRegularSequenceAssociatedGradedTextbookSourceModule
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R) :
    Module (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
      ((N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N)) ⊗[R ⧸ Ideal.ofList rs]
        MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) :=
  (TensorProduct.comm (R ⧸ Ideal.ofList rs)
    (N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N))
    (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))).toAddEquiv.module _

/-- Auxiliary base-change model for the canonical associated-graded map: it is the polynomial-linear
extension of the degree-zero inclusion. -/
private noncomputable def quasiRegularSequenceAssociatedGradedMapAux
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R) :
    TensorProduct (R ⧸ Ideal.ofList rs)
      (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
      (N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N)) →ₗ[
        MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)]
      quasiRegularAssociatedGradedInternal rs N :=
  (quasiRegularAssociatedGradedDegreeZeroInclusion rs).liftBaseChange
    (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))

/-- Helper for 10.69.0.1: on a monomial tensor in the base-change model, the auxiliary map is the
expected monomial action on the degree-zero class. -/
private theorem quasiRegularSequenceAssociatedGradedMapAux_tmul_monomial
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R)
    (m : N) (e : Fin rs.length →₀ ℕ) :
    quasiRegularSequenceAssociatedGradedMapAux N rs
        ((MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs)) ⊗ₜ[R ⧸ Ideal.ofList rs]
          Submodule.Quotient.mk m) =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs N)
        (quasiRegularTotalDegree e)
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e) := by
  -- Evaluate the base-change lift on a simple tensor, then collapse the monomial polynomial action.
  rw [quasiRegularSequenceAssociatedGradedMapAux, LinearMap.liftBaseChange_tmul,
    quasiRegularAssociatedGradedPolynomialSmul_monomial]
  simpa using quasiRegularAssociatedGradedMonomialAction_degreeZero_mk
    (rs := rs) (m := m) (e := e)

/-- The tensor-commutation map from the textbook source
`M / J M ⊗_{R / J} (R / J)[X₁, ..., X_c]` to the base-change source
`(R / J)[X₁, ..., X_c] ⊗_{R / J} M / J M`. -/
private noncomputable def quasiRegularSequenceAssociatedGradedSourceComm
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R) :
    ((N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N)) ⊗[R ⧸ Ideal.ofList rs]
      MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) →ₗ[
        MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)]
      TensorProduct (R ⧸ Ideal.ofList rs)
        (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
        (N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N)) :=
  let _ :
      Module (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
        ((N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N)) ⊗[R ⧸ Ideal.ofList rs]
          MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) :=
    quasiRegularSequenceAssociatedGradedTextbookSourceModule N rs
  let _ :
      Module (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
        (TensorProduct (R ⧸ Ideal.ofList rs)
          (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
          (N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N))) :=
    quasiRegularSequenceAssociatedGradedSourceModule N rs
  (((TensorProduct.comm (R ⧸ Ideal.ofList rs)
      (N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N))
      (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))).toAddEquiv).linearEquiv _).toLinearMap

/-- Helper for 10.69.0.1: the source commutation map swaps a quotient representative and a
monomial simple tensor in the textbook tensor-product source. -/
private theorem quasiRegularSequenceAssociatedGradedSourceComm_tmul
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R)
    (m : N) (e : Fin rs.length →₀ ℕ) :
    quasiRegularSequenceAssociatedGradedSourceComm N rs
        (Submodule.Quotient.mk m ⊗ₜ[R ⧸ Ideal.ofList rs]
          MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs)) =
      (MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs)) ⊗ₜ[R ⧸ Ideal.ofList rs]
        Submodule.Quotient.mk m := by
  -- Unfold the commutation linear map and evaluate it on the simple tensor generator.
  simp [quasiRegularSequenceAssociatedGradedSourceComm, TensorProduct.comm_tmul]

/-- Helper for 10.69.0.1: the internal-model piece equivalence sends the monomial class to the
textbook quotient class represented by the same weighted element. -/
private theorem quasiRegularAssociatedGradedInternalPieceEquiv_monomialClass
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R)
    (m : N) (e : Fin rs.length →₀ ℕ) :
    quasiRegularAssociatedGradedInternalPieceEquiv rs N (quasiRegularTotalDegree e)
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e) =
      Submodule.Quotient.mk
        ⟨(∏ i : Fin rs.length, rs.get i ^ e i) • m, by
          simpa [quasiRegularAssociatedGradedMonomialWeight] using
            quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ := by
  -- The piece equivalence is `quotEquivOfEq`, so it preserves quotient representatives verbatim.
  rw [quasiRegularAssociatedGradedInternalPieceEquiv,
    quasiRegularAssociatedGradedInternalMonomialClass]
  exact Submodule.quotEquivOfEq_mk
    (((quasiRegularIdeal rs) • ⊤ :
      Submodule R (idealAssociatedGradedStage (quasiRegularIdeal rs) N (quasiRegularTotalDegree e))))
    (((idealAssociatedGradedStage (quasiRegularIdeal rs) N (quasiRegularTotalDegree e + 1)).submoduleOf
      (idealAssociatedGradedStage (quasiRegularIdeal rs) N (quasiRegularTotalDegree e)))) _ _

/-- Helper for 10.69.0.1: the inverse direct-sum equivalence sends a homogeneous generator to the
same homogeneous generator with the componentwise piece equivalence applied. -/
private theorem quasiRegularAssociatedGradedAddEquiv_symm_lof
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R)
    (n : ℕ) (z : quasiRegularAssociatedGradedInternalPiece rs N n) :
    (quasiRegularAssociatedGradedAddEquiv rs N).symm
        (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          (quasiRegularAssociatedGradedInternalPiece rs N) n z) =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (idealAssociatedGradedPiece (Ideal.ofList rs) N) n
        (quasiRegularAssociatedGradedInternalPieceEquiv rs N n z) := by
  -- This is the single-support case of the direct-sum congruence attached to the piecewise
  -- quotient equivalences.
  change DirectSum.map
      (fun k ↦ (quasiRegularAssociatedGradedInternalPieceEquiv rs N k).toAddMonoidHom)
      (DirectSum.of (quasiRegularAssociatedGradedInternalPiece rs N) n z) =
    DirectSum.of (idealAssociatedGradedPiece (Ideal.ofList rs) N) n
      (quasiRegularAssociatedGradedInternalPieceEquiv rs N n z)
  -- Now this is exactly the `DirectSum.map` formula on a single homogeneous generator.
  simpa using DirectSum.map_of
    (f := fun k ↦ (quasiRegularAssociatedGradedInternalPieceEquiv rs N k).toAddMonoidHom)
    n z

/-- Helper for 10.69.0.1: acting on the degree-zero monomial class computes the expected
representative-level monomial class. -/
private theorem quasiRegularAssociatedGradedMonomialMapOnPiece_zero_class
    (rs : List R) (m : M) (e : Fin rs.length →₀ ℕ) :
    quasiRegularAssociatedGradedMonomialMapOnPiece rs 0 e
        (quasiRegularAssociatedGradedInternalMonomialClass rs m (0 : Fin rs.length →₀ ℕ)) =
      cast
        (congrArg (quasiRegularAssociatedGradedInternalPiece rs M)
          (by simpa using (Nat.zero_add (quasiRegularTotalDegree e))))
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e) := by
  -- Reuse the earlier normalized representative computation for the degree-zero source class.
  exact quasiRegularAssociatedGradedMonomialMapOnPiece_zero_class_aux
    (M := M) rs m e

/-- Helper for 10.69.0.1: transporting one homogeneous generator through the direct-sum
identification from the internal quotient model to the textbook graded piece only applies the
piecewise equivalence. -/
private theorem quasiRegularAssociatedGradedAddEquiv_lof
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R)
    (n : ℕ) (z : quasiRegularAssociatedGradedInternalPiece rs N n) :
    ((quasiRegularAssociatedGradedAddEquiv rs N).linearEquiv
      (R ⧸ Ideal.ofList rs)).symm
        (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          (quasiRegularAssociatedGradedInternalPiece rs N) n z) =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (idealAssociatedGradedPiece (Ideal.ofList rs) N) n
        (quasiRegularAssociatedGradedInternalPieceEquiv rs N n z) := by
  -- The transferred linear equivalence has the same underlying function as the additive one.
  simpa using quasiRegularAssociatedGradedAddEquiv_symm_lof
    (N := N) rs n z

-- Semantic recall note: no dedicated `lean_leansearch` tool was available in this environment;
-- local project precedent checked in `Definition_10_69_1`.

/-- 10.69.0.1: for an `R`-module `M` and a sequence `rs = [f₁, ..., f_c]`, the canonical
map of graded `((R / J)[X₁, ..., X_c])`-modules from
`M / J M ⊗_{R / J} (R / J)[X₁, ..., X_c]` to `⊕_{n ≥ 0} J^n M / J^(n + 1) M`
is the polynomial-linear extension of the degree-zero inclusion. -/
noncomputable def quasiRegularSequenceAssociatedGradedMap
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R) :
    ((N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N)) ⊗[R ⧸ Ideal.ofList rs]
      MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) →ₗ[
        MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)]
      idealAssociatedGradedModule (Ideal.ofList rs) N :=
  ((quasiRegularAssociatedGradedAddEquiv rs N).linearEquiv _).symm.toLinearMap.comp <|
    (quasiRegularSequenceAssociatedGradedMapAux N rs).comp <|
      (quasiRegularSequenceAssociatedGradedSourceComm N rs)

end RingTheory.Sequence

end
