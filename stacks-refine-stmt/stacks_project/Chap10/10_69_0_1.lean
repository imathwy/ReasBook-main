import Mathlib
import stacks_project.Chap10.Definition_10_70_1

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open scoped BigOperators TensorProduct

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
        (Ideal.map (algebraMap S (reesAlgebra J)) J) := sorry

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
    idealAssociatedGradedMap f hIJ x ∈ idealAssociatedGradedRingGrade J n := sorry

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

-- Proof sketch: each factor `rs.get i ^ e i` lies in the corresponding power of the ideal
-- generated by `rs`; multiplying these contributions places the whole product in the power whose
-- exponent is the total degree of `e`.
/-- The monomial weight attached to `e` lies in the corresponding power of the ideal generated by
the sequence `rs`. -/
private theorem quasiRegularAssociatedGradedMonomialWeight_mem_pow (rs : List R)
    (e : Fin rs.length →₀ ℕ) :
    quasiRegularAssociatedGradedMonomialWeight rs e ∈
      (quasiRegularIdeal rs) ^ quasiRegularTotalDegree e := sorry

-- Proof sketch: combine membership of the monomial weight in `J^|e|` with the description of
-- `J^|e| M` as `(J^|e|) • ⊤`.
/-- Multiplying an element of `M` by the monomial weight lands in the appropriate graded piece
submodule `J^|e| M`. -/
private theorem quasiRegularAssociatedGradedMonomialWeight_smul_mem
    (rs : List R) (e : Fin rs.length →₀ ℕ)
    (m : M) :
    quasiRegularAssociatedGradedMonomialWeight rs e • m ∈
      quasiRegularStage rs M (quasiRegularTotalDegree e) := sorry

/-- Multiplication by the monomial weight on the `n`-th stage `J^n M`. -/
private theorem quasiRegularAssociatedGradedMonomialWeight_smul_mem_stage
    (rs : List R) (n : ℕ) (e : Fin rs.length →₀ ℕ)
    (m : quasiRegularStage rs M n) :
    ((quasiRegularAssociatedGradedMonomialWeight rs e) •
        (quasiRegularStage rs M n).subtype) m ∈
      quasiRegularStage rs M (n + quasiRegularTotalDegree e) := sorry

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
        (quasiRegularAssociatedGradedMonomialMapToPiece rs e) := sorry

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
      quasiRegularAssociatedGradedInternalMonomialClass rs m e := sorry

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
  sorry

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

private theorem quasiRegularAssociatedGradedInternal_one_smul
    (rs : List R) (x : quasiRegularAssociatedGradedInternal rs M) :
    (1 : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) • x = x := by
  sorry

private theorem quasiRegularAssociatedGradedInternal_mul_smul
    (rs : List R) (p q : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
    (x : quasiRegularAssociatedGradedInternal rs M) :
    (p * q) • x = p • q • x := by
  sorry

private theorem quasiRegularAssociatedGradedInternal_smul_add
    (rs : List R) (p : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
    (x y : quasiRegularAssociatedGradedInternal rs M) :
    p • (x + y) = p • x + p • y := by
  sorry

private theorem quasiRegularAssociatedGradedInternal_smul_zero
    (rs : List R) (p : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) :
    p • (0 : quasiRegularAssociatedGradedInternal rs M) = 0 := by
  sorry

private theorem quasiRegularAssociatedGradedInternal_add_smul
    (rs : List R) (p q : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
    (x : quasiRegularAssociatedGradedInternal rs M) :
    (p + q) • x = p • x + q • x := by
  sorry

private theorem quasiRegularAssociatedGradedInternal_zero_smul
    (rs : List R) (x : quasiRegularAssociatedGradedInternal rs M) :
    (0 : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) • x = 0 := by
  sorry

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
  sorry

private theorem quasiRegularAssociatedGradedDegreeZeroInclusion_map_smul
    (rs : List R) (a : R ⧸ Ideal.ofList rs)
    (x : M ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R M)) :
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ) (a • x)) =
      a • DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (quasiRegularAssociatedGradedInternalPiece rs M) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ) x) := by
  sorry

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

private theorem quasiRegularAssociatedGradedInternal_isScalarTower (rs : List R) :
    IsScalarTower (R ⧸ quasiRegularIdeal rs)
      (MvPolynomial (Fin rs.length) (R ⧸ quasiRegularIdeal rs))
      (quasiRegularAssociatedGradedInternal rs M) := by
  sorry

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
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e) := sorry

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

/-- Equation 10.69.0.1: for an `R`-module `M` and a sequence `rs = [f₁, ..., f_c]`, the canonical
map of
graded `((R / J)[X₁, ..., X_c])`-modules from the polynomial extension of `M / J M` to
`⊕_{n ≥ 0} J^n M / J^(n + 1) M` is the polynomial-linear extension of the degree-zero inclusion. -/
private noncomputable def quasiRegularSequenceAssociatedGradedMapAux
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R) :
    TensorProduct (R ⧸ Ideal.ofList rs)
      (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
      (N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N)) →ₗ[
        MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)]
      quasiRegularAssociatedGradedInternal rs N :=
  (quasiRegularAssociatedGradedDegreeZeroInclusion rs).liftBaseChange
    (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))

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

/-- Equation 10.69.0.1: for an `R`-module `M` and a sequence `rs = [f₁, ..., f_c]`, the canonical
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

-- Proof sketch: use the base-change description of Equation `10.69.0.1` on simple tensors and
-- then compute the action of the
-- monomial `X^e` on the degree-zero class of `m`.
/-- Equation 10.69.0.1 on a monomial simple tensor sends `X^e ⊗ m̄` to the class of
`(\prod_i f_i^{e_i}) • m` in the degree-`|e|` summand of the associated graded module. -/
theorem quasiRegularSequenceAssociatedGradedMap_tmul_monomial
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R)
    (m : N) (e : Fin rs.length →₀ ℕ) :
    quasiRegularSequenceAssociatedGradedMap N rs
        (Submodule.Quotient.mk m ⊗ₜ[R ⧸ Ideal.ofList rs]
          MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs)) =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (idealAssociatedGradedPiece (Ideal.ofList rs) N)
        e.degree
        (Submodule.Quotient.mk
          ⟨(∏ i : Fin rs.length, rs.get i ^ e i) • m, by
            simpa [quasiRegularAssociatedGradedMonomialWeight] using
              quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩) := sorry

-- Proof sketch: every homogeneous class in `J^n M / J^(n + 1) M` is represented by a finite sum of
-- monomials `(\prod_i f_i^{e_i}) • m_e` of total degree `n`, so it lies in the image of the sum of
-- the corresponding simple tensors `X^e ⊗ m̄_e`.
/-- Equation 10.69.0.1 (surjectivity): the canonical associated-graded map attached to a finite
sequence is
surjective. -/
theorem quasiRegularSequenceAssociatedGradedMap_surjective
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R) :
    Function.Surjective (quasiRegularSequenceAssociatedGradedMap N rs) := sorry

end RingTheory.Sequence

end
