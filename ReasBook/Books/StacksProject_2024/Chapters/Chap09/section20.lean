import Mathlib
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_20_1 (from Chap09) -/
universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/- Domain-style sampling for Definition 9.20.1:
- primary domain: trace and norm for finite field extensions;
- sampled owner declarations: `Algebra.trace`, `Algebra.trace_apply`, `Algebra.norm`,
  `Algebra.norm_apply`;
- `source-facing`: the textbook trace and norm of a finite extension `L/K`;
- `core/canonical`: the mathlib owners `Algebra.trace K L` and `Algebra.norm K`;
- `bridge/view`: the companion formulas expressing them as the trace and determinant of
  left-multiplication by an element.

Primitive data are only the canonical owner maps `Algebra.trace K L` and `Algebra.norm K`; the
left-multiplication formulas are derived API, so this file should stay at direct recall/use rather
than introducing parallel local definitions.
-/

/- Definition 9.20.1 (1): for a finite field extension `L/K`, the trace `Trace_{L/K}` is the
canonical linear map `Algebra.trace K L`, sending `α : L` to the trace over `K` of multiplication
by `α` on `L`. -/
recall Algebra.trace

/- Companion recall: the defining formula for the trace is the existing theorem
`Algebra.trace_apply`, identifying `Algebra.trace K L α` with the trace of the left-multiplication
linear endomorphism by `α`. -/
recall Algebra.trace_apply

/- Definition 9.20.1 (2): for a finite field extension `L/K`, the norm `Norm_{L/K}` is the
canonical multiplicative map `Algebra.norm K`, sending `α : L` to the determinant over `K` of
multiplication by `α` on `L`. -/
recall Algebra.norm

/- Companion recall: the defining formula for the norm is the existing theorem
`Algebra.norm_apply`, identifying `Algebra.norm K α` with the determinant of the
left-multiplication linear endomorphism by `α`. -/
recall Algebra.norm_apply

/-! ### Lemma_9_20_2 (from Chap09) -/
open IntermediateField
open Module

universe u v

namespace Algebra

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/- Domain-style sampling for Lemma 9.20.2:
- `source-facing`: the characteristic polynomial of multiplication by `α` on a finite extension
  `L/K`
- `core/canonical`: `Algebra.lmul K L α` is the primitive endomorphism, and
  `IntermediateField.adjoin.finrank` owns the simple-extension degree
- `bridge/view`: `Matrix.charpoly_leftMulMatrix` computes the simple-extension `charpoly`, while
  `Module.finrank_mul_finrank` supplies the textbook exponent

Primitive data is the pair `(Algebra.lmul K L α, minpoly K α)`. The degree formula below is
derived API, so the displayed exponent should be proved directly from the existing owner theorems
instead of being treated as an independent local wheel.
-/

/-- Helper for Lemma 9.20.2: the characteristic polynomial of a block diagonal matrix with a
constant square block `A` repeated `e` times is `A.charpoly ^ e`. -/
lemma charpoly_blockDiagonal_const {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (e : ℕ) :
    (Matrix.blockDiagonal (fun _ : Fin e => A)).charpoly = A.charpoly ^ e := by
  -- Rewrite the characteristic matrix blockwise so that the determinant factors over the blocks.
  rw [Matrix.charpoly]
  have hcharmatrix :
      (Matrix.blockDiagonal (fun _ : Fin e => A)).charmatrix =
        Matrix.blockDiagonal (fun _ : Fin e => A.charmatrix) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    by_cases h : k = k'
    · subst h
      by_cases hij : i = j
      · subst hij
        simp [Matrix.charmatrix_apply_eq, Matrix.blockDiagonal_apply_eq]
      · simp [Matrix.charmatrix_apply_ne, Matrix.blockDiagonal_apply_eq, hij]
    · simp [Matrix.charmatrix, Matrix.blockDiagonal_apply_ne, h]
  rw [hcharmatrix, Matrix.det_blockDiagonal]
  simp [Matrix.charpoly]

/-- Helper for Lemma 9.20.2: the simple-extension left-multiplication block attached to the
canonical power basis of `K⟮α⟯/K` has characteristic polynomial `minpoly K α`. -/
lemma charpoly_leftMulMatrix_adjoin_gen (α : L) (hα : IsIntegral K α) :
    let pb : PowerBasis K K⟮α⟯ := IntermediateField.adjoin.powerBasis hα
    (Algebra.leftMulMatrix pb.basis pb.gen).charpoly = minpoly K α := by
  -- This is exactly the owner theorem for a power basis, specialized to the adjoin power basis.
  simpa [IntermediateField.minpoly_gen] using
    (charpoly_leftMulMatrix (R := K) (IntermediateField.adjoin.powerBasis hα))

/-- Lemma 9.20.2: for a finite field extension `L/K`, the characteristic polynomial of the
`K`-linear endomorphism of `L` given by multiplication by `α` is the minimal polynomial of `α`
over `K` raised to the power `[L : K(α)]`. This is the canonical Lean form of the textbook
statement that the characteristic polynomial is `P ^ e` with
`e * deg(P) = [L : K]`. -/
-- Proof sketch: choose a `K(α)`-basis of `L`, use the induced `K`-basis from `Basis.smulTower`,
-- identify the resulting matrix of `Algebra.lmul K L α` with a block diagonal matrix whose blocks
-- are the simple-extension left-multiplication matrix, and then combine
-- `charpoly_leftMulMatrix` with the tower-law exponent
-- `finrank K⟮α⟯ L * (minpoly K α).natDegree = finrank K L`.

theorem charpoly_lmul_eq_minpoly_pow_finrank_adjoin (α : L) :
    (lmul K L α).charpoly = (minpoly K α) ^ finrank K⟮α⟯ L := by
  let hα : IsIntegral K α := .of_finite K α
  let pb : PowerBasis K K⟮α⟯ := IntermediateField.adjoin.powerBasis hα
  let b : Basis (Fin (finrank K⟮α⟯ L)) K⟮α⟯ L := Module.finBasis K⟮α⟯ L
  -- Pass to the scalar-tower basis so the `K(α)`-linear structure becomes visible over `K`.
  rw [← LinearMap.charpoly_toMatrix (lmul K L α) (pb.basis.smulTower b)]
  have hmatrix :
      LinearMap.toMatrix (pb.basis.smulTower b) (pb.basis.smulTower b) (lmul K L α) =
        Matrix.blockDiagonal
          (fun _ : Fin (finrank K⟮α⟯ L) => Algebra.leftMulMatrix pb.basis pb.gen) := by
    -- Rewrite `α` as the image of the simple-extension generator and apply the tower basis lemma.
    calc
      LinearMap.toMatrix (pb.basis.smulTower b) (pb.basis.smulTower b) (lmul K L α)
          = Algebra.leftMulMatrix (pb.basis.smulTower b) α := by
              simpa using
                (Algebra.leftMulMatrix_apply (b := pb.basis.smulTower b) (R := K) (S := L)
                  α).symm
      _ = Algebra.leftMulMatrix (pb.basis.smulTower b)
            (algebraMap K⟮α⟯ L (AdjoinSimple.gen K α)) := by
            rw [IntermediateField.AdjoinSimple.algebraMap_gen]
      _ = Matrix.blockDiagonal
            (fun _ : Fin (finrank K⟮α⟯ L) =>
              Algebra.leftMulMatrix pb.basis (AdjoinSimple.gen K α)) := by
            simpa [pb, b] using
              Algebra.smulTower_leftMulMatrix_algebraMap pb.basis b (AdjoinSimple.gen K α)
      _ = Matrix.blockDiagonal
            (fun _ : Fin (finrank K⟮α⟯ L) => Algebra.leftMulMatrix pb.basis pb.gen) := by
            simp [pb]
  rw [hmatrix, charpoly_blockDiagonal_const]
  -- Each block is the simple-extension companion block, whose charpoly is the minimal polynomial.
  rw [charpoly_leftMulMatrix_adjoin_gen (K := K) (L := L) α hα]

end Algebra

/-! ### Lemma_9_20_3 (from Chap09) -/
open Module
open IntermediateField
open scoped IntermediateField

universe u v

namespace Algebra

variable (K : Type u) {L : Type v}
variable [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/- Domain-style sampling for Lemma 9.20.3:
- `source-facing`: norm and trace formulas for an element of a finite field extension in terms of
  the coefficients of its minimal polynomial.
- sampled owner declarations:
  `Algebra.norm`,
  `Algebra.norm_eq_norm_adjoin`,
  `PowerBasis.norm_gen_eq_coeff_zero_minpoly`,
  `trace_eq_finrank_mul_minpoly_nextCoeff`.
- best owner abstraction: `Algebra.norm` and `Algebra.trace` are the primitive owners; the
  textbook formulas are bridge statements obtained by reducing to the canonical simple-extension
  norm/trace owners and then reading the minimal-polynomial coefficients there.

Primitive data is the owner triple `(norm K α, trace K L α, minpoly K α)`. The displayed constant
and next coefficients are derived API, so this file should reuse the existing mathlib owner
theorems for norm transitivity, simple-extension norm, and trace rather than routing through a
parallel local characteristic-polynomial bridge.

Source/core/bridge triage:
- `source-facing`: the textbook coefficient formulas for `norm K α` and `trace K L α`;
- `core/canonical`: the owner operations `norm`, `trace`, `minpoly`, and the canonical simple
  extension `K⟮α⟯`;
- `bridge/view`: `norm_eq_norm_adjoin`, `PowerBasis.norm_gen_eq_coeff_zero_minpoly`,
  `trace_eq_finrank_mul_minpoly_nextCoeff`, and the tower-law degree identity
  `finrank_mul_finrank`.
-/

/-- Lemma 9.20.3 (1): for a finite field extension `L/K`, the norm of `α` is `(-1)^[L:K]`
times the constant coefficient of the minimal polynomial of `α` over `K`, raised to the power
`[L : K(α)]`. In the textbook notation `P = x^d + a₁ x^(d - 1) + ... + a_d`, this constant
coefficient is `a_d`. -/
-- Proof sketch: reduce `norm K α` to the norm of the generator of the simple extension `K(α)/K`
-- via `norm_eq_norm_adjoin`, evaluate that simple-extension norm with
-- `PowerBasis.norm_gen_eq_coeff_zero_minpoly`, and then rewrite the exponent by the tower law.
theorem norm_eq_sign_mul_minpoly_coeff_zero_pow_finrank_adjoin
    (α : L) : norm K α = (-1 : K) ^ finrank K L * (minpoly K α).coeff 0 ^ finrank K⟮α⟯ L := by
  have hα : IsIntegral K α := .of_finite K α
  rw [norm_eq_norm_adjoin K α]
  have hgen : norm K (AdjoinSimple.gen K α) =
      (-1 : K) ^ finrank K K⟮α⟯ * (minpoly K α).coeff 0 := by
    simpa [IntermediateField.adjoin.powerBasis_gen hα, minpoly_gen K α,
      IntermediateField.adjoin.finrank hα] using
      (PowerBasis.norm_gen_eq_coeff_zero_minpoly
        (IntermediateField.adjoin.powerBasis hα : PowerBasis K K⟮α⟯))
  rw [hgen, mul_pow, ← pow_mul]
  congr 1
  rw [finrank_mul_finrank K K⟮α⟯ L]

end Algebra

/- Lemma 9.20.3 (2): for a finite field extension `L/K`, the trace of `α` is minus
`[L : K(α)]` times the next coefficient of the minimal polynomial of `α` over `K`. In the
textbook notation `P = x^d + a₁ x^(d - 1) + ... + a_d`, this next coefficient is `a₁`. The
canonical Lean statement is the existing theorem `trace_eq_finrank_mul_minpoly_nextCoeff`.
-/
recall trace_eq_finrank_mul_minpoly_nextCoeff

/-! ### Lemma_9_20_4 (from Chap09) -/
universe u v w

open scoped Matrix
open Module

namespace LinearMap

variable (R : Type u) {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling for Lemma 9.20.4:
- primary domain: trace and determinant transitivity for linear endomorphisms over a free scalar
  tower.
- sampled owner declarations:
  `LinearMap.trace_eq_matrix_trace`,
  `LinearMap.restrictScalars_toMatrix`,
  `Algebra.trace_eq_matrix_trace`,
  `Algebra.trace_trace`.
- best owner abstraction:
  - `source-facing`: the trace/determinant formulas for an `S`-linear endomorphism viewed over the
    base extension `S/R`, interpreted with the zero-by-default trace/determinant conventions;
  - `core/canonical`: `LinearMap.trace`, `Algebra.trace`, and `LinearMap.det_restrictScalars`;
  - `bridge/view`: restriction of scalars `f.restrictScalars R`, together with the scalar-tower
    bases `Free.chooseBasis R S` and `Free.chooseBasis S A`.

Primitive data is only the endomorphism `f : A →ₗ[S] A`; the matrix expressions are derived API
used to connect the source-facing trace statement to the canonical owners, while the infinite-basis
branches are governed by the zero-by-default trace owners `LinearMap.trace` and `Algebra.trace`.
Clause `(1)` remains the minimal bridge theorem because mathlib has the algebra-side analogue
`Algebra.trace_trace` but no endomorphism-level `LinearMap.trace_restrictScalars`, while clause
`(2)` should be a direct recall of the existing owner theorem rather than a parallel local wrapper.

Source/core/bridge triage:
- `(1)` is a `source-facing` bridge statement relating the module-theoretic trace owner
  `LinearMap.trace` to the scalar-extension owner `Algebra.trace`.
- `(2)` is `core/canonical`, so it should stay a direct recall of
  `LinearMap.det_restrictScalars`.
-/

section TraceRestrictScalars

variable [AddCommMonoid A] [Module R A] [Module S A] [IsScalarTower R S A]
variable [Module.Free R S] [Module.Free S A]

/- Lemma 9.20.4 (1): for a free `S`-module `A` over a free extension `S/R`, the zero-by-default
trace of an `S`-linear endomorphism viewed over `R` is the algebra trace from `S` to `R` of its
`S`-linear trace. This is the source-facing bridge theorem; with `R` as an explicit ambient
input, it has the ordinary call shape `LinearMap.trace_restrictScalars R f`. -/
theorem trace_restrictScalars (f : A →ₗ[S] A) :
    trace R A (f.restrictScalars R) = Algebra.trace R S (trace S A f) := by
  classical
  by_cases hR : Subsingleton R
  · exact Subsingleton.elim _ _
  letI := not_subsingleton_iff_nontrivial.mp hR
  by_cases hA : Subsingleton A
  · letI := hA
    have hf : f = 0 := by ext a; exact Subsingleton.elim _ _
    subst hf
    simp
  letI := not_subsingleton_iff_nontrivial.mp hA
  let bS := Free.chooseBasis R S
  let bA := Free.chooseBasis S A
  have := Module.nontrivial S A
  cases fintypeOrInfinite (Free.ChooseBasisIndex R S)
  · cases fintypeOrInfinite (Free.ChooseBasisIndex S A)
    · let M := toMatrix bA bA f
      rw [trace_eq_matrix_trace R (bS.smulTower' bA), restrictScalars_toMatrix,
        trace_eq_matrix_trace S bA]
      calc
        Matrix.trace ((M.map (Algebra.leftMulMatrix bS)).comp _ _ _ _ _)
            = ∑ y, Matrix.trace (Algebra.leftMulMatrix bS (M y y)) := by
                simp [Matrix.trace, Matrix.diag, Matrix.comp_apply, Fintype.sum_prod_type]
        _ = ∑ y, Algebra.trace R S (M y y) := by
                simp [Algebra.trace_eq_matrix_trace bS]
        _ = Algebra.trace R S (∑ y, M y y) := by
                rw [map_sum]
        _ = Algebra.trace R S (Matrix.trace M) := by
                simp [Matrix.trace]
    ·
      have hA_noBasis : ¬∃ s : Finset A, Nonempty (Basis s S A) := by
        rintro ⟨s, ⟨b⟩⟩
        exact Module.not_finite_of_infinite_basis bA (Module.Finite.of_basis b)
      have hRA_noBasis : ¬∃ s : Finset A, Nonempty (Basis s R A) := by
        rintro ⟨s, ⟨b⟩⟩
        exact Module.not_finite_of_infinite_basis (bS.smulTower bA) (Module.Finite.of_basis b)
      simp [LinearMap.trace, hA_noBasis, hRA_noBasis]
  ·
      have hS_noBasis : ¬∃ s : Finset S, Nonempty (Basis s R S) := by
        rintro ⟨s, ⟨b⟩⟩
        exact Module.not_finite_of_infinite_basis bS (Module.Finite.of_basis b)
      have hRA_noBasis : ¬∃ s : Finset A, Nonempty (Basis s R A) := by
        rintro ⟨s, ⟨b⟩⟩
        exact Module.not_finite_of_infinite_basis (bS.smulTower bA) (Module.Finite.of_basis b)
      rw [Algebra.trace_eq_zero_of_not_exists_basis R hS_noBasis,
        LinearMap.zero_apply]
      simp [LinearMap.trace, hRA_noBasis]

end TraceRestrictScalars

section DetRestrictScalars

variable [AddCommGroup A] [Module R A] [Module S A] [IsScalarTower R S A]
variable [Module.Free R S] [Module.Free S A]

/- Lemma 9.20.4 (2): the determinant formula is the canonical theorem
`LinearMap.det_restrictScalars`. -/
recall det_restrictScalars

end DetRestrictScalars

end LinearMap

/-! ### Lemma_9_20_5 (from Chap09) -/
universe u v w

variable {K : Type u} {L : Type v} {M : Type w}
variable [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
variable [FiniteDimensional K L] [FiniteDimensional L M]

/- Lemma 9.20.5 (1): in a tower of finite field extensions `M/L/K`, the trace from `M` to `K`
is the composite of the trace from `M` to `L` with the trace from `L` to `K`. This is the
canonical theorem `Algebra.trace_comp_trace`. -/
recall Algebra.trace_comp_trace

/- Lemma 9.20.5 (2): in a tower of finite field extensions `M/L/K`, the norm from `M` to `K` is
the composite of the norm from `M` to `L` with the norm from `L` to `K`. This is the canonical
theorem `Algebra.norm_norm`. -/
recall Algebra.norm_norm

/-! ### Definition_9_20_6 (from Chap09) -/
universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/- Domain-style sampling for Definition 9.20.6:
- primary domain: trace pairings for finite field extensions;
- sampled owner declarations: `Algebra.traceForm`, `Algebra.traceForm_apply`,
  `Algebra.traceForm_isSymm`, `Algebra.traceForm_toMatrix`;
- best owner abstraction:
  - `source-facing`: the trace pairing `Q_{L/K}` of the finite field extension `L / K`;
  - `core/canonical`: the bilinear form `Algebra.traceForm K L`;
  - `bridge/view`: the evaluation formula `Algebra.traceForm_apply`, symmetry
    `Algebra.traceForm_isSymm`, and basis-matrix presentation `Algebra.traceForm_toMatrix`;
- primitive data: only the canonical owner bilinear form `Algebra.traceForm K L`;
- derived API: its pointwise trace formula, symmetry, and matrix expressions in a basis.

This item is therefore already at the correct `core/canonical` owner layer, so refinement should
stay as direct recall/use rather than introducing any local trace-pairing wrapper.
-/

/- Definition 9.20.6: for a finite field extension `L/K`, the trace pairing is the symmetric
`K`-bilinear form `Algebra.traceForm K L`, i.e. the form sending `(α, β)` to
`Trace_{L/K}(α * β)`. -/
recall Algebra.traceForm

/- Companion recall: the defining formula for the trace pairing is the existing theorem
`Algebra.traceForm_apply`, identifying `Algebra.traceForm K L α β` with `Algebra.trace K L (α * β)`.
-/
recall Algebra.traceForm_apply

/- Companion recall: the trace pairing is symmetric by the existing theorem
`Algebra.traceForm_isSymm`. -/
recall Algebra.traceForm_isSymm

/-! ### Lemma_9_20_7 (from Chap09) -/
universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/- Domain-style sampling for Lemma 9.20.7:
- primary domain: separability criteria for finite field extensions via the trace map and trace
  pairing;
- sampled owner declarations:
  `Algebra.trace`,
  `Algebra.traceForm`,
  `Algebra.traceForm_nondegenerate`,
  `traceForm_nondegenerate_tfae`;
- best owner abstraction:
  - `source-facing`: the equivalence between separability of `L/K`, nonvanishing of the trace, and
    nondegeneracy of the trace pairing;
  - `core/canonical`: the mathlib theorem `traceForm_nondegenerate_tfae`;
  - `bridge/view`: the forward implications `Algebra.traceForm_nondegenerate` and
    `Algebra.trace_ne_zero`, derived from the same owner theorem;
- primitive data: the finite extension `L/K` together with the canonical owners
  `Algebra.trace K L` and `Algebra.traceForm K L`;
- derived API: the TFAE packaging of the three equivalent criteria.

This item is therefore already at the correct `core/canonical` layer, so refinement should remain
direct recall of `traceForm_nondegenerate_tfae` rather than introducing a parallel local
separability criterion.
-/

/- Lemma 9.20.7: for a finite field extension `L/K`, the following are equivalent: the extension
`L/K` is separable, the trace map `Algebra.trace K L` is not identically zero, and the trace
pairing `Algebra.traceForm K L` is nondegenerate. This is the canonical theorem
`traceForm_nondegenerate_tfae`. -/
recall traceForm_nondegenerate_tfae

/-! ### Definition_9_20_8 (from Chap09) -/
universe u v w

open Module

/- Domain-style sampling for Definition 9.20.8:
- primary domain: discriminants of finite field extensions, represented by basis discriminants of
  the trace pairing and then reduced modulo squares;
- sampled owner declarations:
  `Algebra.discr`,
  `Algebra.discr_reindex`,
  `Algebra.discr_of_matrix_vecMul`,
  `Algebra.traceForm`,
  `MulAction.orbitRel.Quotient`;
- best owner abstraction:
  - `source-facing`: the discriminant class of the finite extension `L/K` in `K / (Kˣ)^2`;
  - `core/canonical`: `Algebra.discr K b` as the basis discriminant of the extension, together
    with the quotient `MulAction.orbitRel.Quotient (Subgroup.square Kˣ) K`;
  - `bridge/view`: the basis-independence theorem for the square class of `Algebra.discr K b`,
    yielding `fieldExtensionDiscriminant_eq`;
- primitive data: the canonical square-class quotient and the basis discriminant
  `Algebra.discr K b`;
- derived API: the basis-independence theorem `fieldExtensionDiscriminant_eq`.

Source/core/bridge triage:
- `source-facing`: `fieldExtensionDiscriminant`, the discriminant class of the finite extension
  `L/K`;
- `core/canonical`: `Algebra.discr` for basis representatives and
  `MulAction.orbitRel.Quotient (Subgroup.square Kˣ) K` for square classes;
- `bridge/view`: `fieldExtensionDiscriminant_eq`, identifying the source-facing class with any
  basis representative `Algebra.discr K b`.
-/

variable (K : Type u) [Field K]

/-- Field elements modulo multiplication by a square of a unit. -/
abbrev SquareClass := MulAction.orbitRel.Quotient (Subgroup.square Kˣ) K

namespace SquareClass

/-- The square class of a field element. -/
abbrev mk (a : K) : SquareClass K := Quotient.mk'' a

theorem mk_eq_mk_iff {a b : K} :
    mk K a = mk K b ↔ ∃ u : Kˣ, a = ↑(u ^ (2 : ℕ)) * b :=
    by
  change (Quotient.mk'' a : Quotient (MulAction.orbitRel (Subgroup.square Kˣ) K)) =
      Quotient.mk'' b ↔ _
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨u, hu⟩
    rcases (Subgroup.mem_square.mp u.2) with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    calc
      a = u • b := hu.symm
      _ = ((u : Subgroup.square Kˣ) : Kˣ) • b := by rw [MulAction.subgroup_smul_def]
      _ = (((u : Subgroup.square Kˣ) : Kˣ) : K) * b := by simp [Units.smul_def]
      _ = ↑(v ^ (2 : ℕ)) * b := by rw [hv, pow_two]
  · rintro ⟨u, hu⟩
    refine ⟨⟨u ^ (2 : ℕ), Subgroup.mem_square.mpr ⟨u, by simp [pow_two]⟩⟩, ?_⟩
    simpa [MulAction.subgroup_smul_def, Units.smul_def] using hu.symm

end SquareClass

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

private theorem squareClass_eq_of_basis_discr {ι : Type w} [Fintype ι] [DecidableEq ι]
    {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (b : Basis ι K L) (b' : Basis ι' K L) :
    SquareClass.mk K (Algebra.discr K b) = SquareClass.mk K (Algebra.discr K b') := by
  let e : ι ≃ ι' := b.indexEquiv b'
  let b₀ : Basis ι K L := b'.reindex e.symm
  have hdet : IsUnit (b₀.toMatrix b).det := by
    letI := Basis.invertibleToMatrix b₀ b
    exact Matrix.isUnit_det_of_invertible (b₀.toMatrix b)
  rw [SquareClass.mk_eq_mk_iff]
  refine ⟨hdet.unit, ?_⟩
  calc
    Algebra.discr K b = (b₀.toMatrix b).det ^ 2 * Algebra.discr K b₀ := by
      calc
        Algebra.discr K b =
            Algebra.discr K (Matrix.vecMul b₀ ((b₀.toMatrix b).map (algebraMap K L))) := by
              rw [b₀.toMatrix_map_vecMul b]
        _ = (b₀.toMatrix b).det ^ 2 * Algebra.discr K b₀ := by
              simpa using Algebra.discr_of_matrix_vecMul b₀ (b₀.toMatrix b)
    _ = ↑(hdet.unit ^ (2 : ℕ)) * Algebra.discr K b₀ := by simp
    _ = ↑(hdet.unit ^ (2 : ℕ)) * Algebra.discr K b' := by
      congr 1
      simpa [b₀, Basis.coe_reindex] using
        (@Algebra.discr_reindex K L ι' _ _ _ _ ι _ _ _ b' e.symm)

section FiniteDimensional

variable [FiniteDimensional K L]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- Definition 9.20.8: the discriminant of the finite field extension `L/K` is the square class of
the discriminant of the trace pairing `Q_{L/K}`, i.e. the class of any basis representative
`Algebra.discr K b` in `K / (Kˣ)^2`. -/
noncomputable def fieldExtensionDiscriminant (K : Type u) [Field K] (L : Type v) [Field L]
    [Algebra K L] [FiniteDimensional K L] : SquareClass K :=
  SquareClass.mk K (Algebra.discr K (Module.finBasis K L))

/-- Any basis representative computes the discriminant class of `L/K`. -/
theorem fieldExtensionDiscriminant_eq (b : Basis ι K L) :
    fieldExtensionDiscriminant K L = SquareClass.mk K (Algebra.discr K b) := by
  simpa [fieldExtensionDiscriminant] using
    squareClass_eq_of_basis_discr (Module.finBasis K L) b

end FiniteDimensional

/-! ### Exercise_9_20_9 (from Chap09) -/
/- Domain-style sampling for Exercise 9.20.9:
- primary domain: quadratic field extensions, discriminant classes, and the separable / purely
  inseparable dichotomy;
- sampled owner declarations:
  `fieldExtensionDiscriminant`,
  `fieldExtensionDiscriminant_eq`,
  `Algebra.IsSeparable`,
  `IsPurelyInseparable`,
  `IntermediateField.adjoin`,
  `IntermediateField.mem_bot`,
  `Algebra.IsQuadraticExtension.finrank_eq_two`,
  `IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable`,
  `IntermediateField.bot_eq_top_iff_finrank_eq_one`;
- sampled chapter/project recall surface:
  `Definition_9_20_8`,
  `Definition_9_12_2`,
  `Definition_9_14_1`;
- owner abstraction: the source-facing discriminant owner is
  `fieldExtensionDiscriminant K L : SquareClass K`; `fieldExtensionDiscriminant_eq` is the bridge
  back to basis representatives `Algebra.discr K b` from Definition 9.20.8; `Algebra.IsSeparable
  K L` and `IsPurelyInseparable K L` canonically own the extension-theoretic predicates appearing
  in the source, `K⟮x⟯` is the canonical owner for the simple-generator condition, and
  `IntermediateField.mem_bot` is the canonical bridge from base-field membership in
  `(⊥ : IntermediateField K L)` back to the underlying `algebraMap` image;
- primitive data: the discriminant class and the separable / purely inseparable predicates that
  distinguish the quadratic cases;
- derived API: the basis-level discriminant representatives obtained through
  `fieldExtensionDiscriminant_eq`, together with `IntermediateField.mem_bot` for unpacking the
  base-field membership owner, and the source-facing generator consequences recorded below as
  companion theorems.

Source/core/bridge triage:
- `source-facing`: the three explicit Stacks cases for a quadratic extension;
- `core/canonical`: `fieldExtensionDiscriminant`, `Algebra.IsSeparable`, and
  `IsPurelyInseparable`;
- `bridge/view`: `fieldExtensionDiscriminant_eq`, relating the owner discriminant class to the
  basis discriminants `Algebra.discr K b`, and `IntermediateField.mem_bot`, relating base-field
  membership in `(⊥ : IntermediateField K L)` to the underlying `algebraMap` image; the main
  exercise theorem should state the full source-facing three-way trichotomy directly, while the
  shorter owner-level discriminant and separability projections remain companion consequences.
-/

open scoped IntermediateField
open Polynomial

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

variable {K L}

section Quadratic

variable [Algebra.IsQuadraticExtension K L]

local notation "Δ" => fieldExtensionDiscriminant K L
local notation "purelyInseparableCase" =>
  Δ = (⟦(0 : K)⟧ : SquareClass K) ∧ ringChar K = 2 ∧ IsPurelyInseparable K L ∧
    ∃ x : L, x ^ 2 ∈ (⊥ : IntermediateField K L) ∧ K⟮x⟯ = ⊤
local notation "separableCase" =>
  Δ = (⟦(1 : K)⟧ : SquareClass K) ∧ ringChar K = 2 ∧ Algebra.IsSeparable K L
local notation "nonsquareCase" =>
  Δ ≠ (⟦(1 : K)⟧ : SquareClass K) ∧ ringChar K ≠ 2 ∧
    ∃ y : L, ∃ a : K, Δ = (⟦a⟧ : SquareClass K) ∧
      y ^ 2 = algebraMap K L a ∧ K⟮y⟯ = ⊤

/-- Helper for Exercise 9.20.9: a nonseparable quadratic extension is purely inseparable, and its
base field has characteristic `2`. -/
lemma quadratic_extension_isPurelyInseparable_and_char_two_of_not_separable
    (hsep : ¬ Algebra.IsSeparable K L) :
    IsPurelyInseparable K L ∧ ringChar K = 2 := by
  -- The inseparable degree must divide the quadratic degree, and nonseparability rules out degree `1`.
  have hmul : Field.finSepDegree K L * Field.finInsepDegree K L = Module.finrank K L :=
    Field.finSepDegree_mul_finInsepDegree (F := K) (E := L)
  have hfinInsep_ne_one : Field.finInsepDegree K L ≠ 1 := by
    simpa [isSeparable_iff_finInsepDegree_eq_one] using hsep
  have hfinInsep_dvd_two : Field.finInsepDegree K L ∣ 2 := by
    refine ⟨Field.finSepDegree K L, ?_⟩
    calc
      2 = Module.finrank K L := by
        symm
        simpa using (Algebra.IsQuadraticExtension.finrank_eq_two K L)
      _ = Field.finSepDegree K L * Field.finInsepDegree K L := hmul.symm
      _ = Field.finInsepDegree K L * Field.finSepDegree K L := by rw [Nat.mul_comm]
  have hfinInsep_eq_two : Field.finInsepDegree K L = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hfinInsep_dvd_two with hdeg | hdeg
    · exact (hfinInsep_ne_one hdeg).elim
    · exact hdeg
  have hfinSep_eq_one : Field.finSepDegree K L = 1 := by
    rw [hfinInsep_eq_two] at hmul
    have hfinrank_two : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
    omega
  have hpure : IsPurelyInseparable K L :=
    isPurelyInseparable_of_finSepDegree_eq_one (F := K) (E := L) hfinSep_eq_one
  refine ⟨hpure, ?_⟩
  -- The inseparable degree of a finite extension is a power of the exponential characteristic.
  obtain ⟨n, hnpow⟩ := finInsepDegree_eq_pow (F := K) (E := L) (q := ringExpChar K)
  have hpow : 2 = ringExpChar K ^ n := by rw [hfinInsep_eq_two] at hnpow; exact hnpow
  rcases expChar_is_prime_or_one K (ringExpChar K) with hprime | hone
  · have hq_dvd_two : ringExpChar K ∣ 2 := by
      cases n with
      | zero =>
          simp at hpow
      | succ m =>
          exact ⟨(ringExpChar K) ^ m, by simpa [pow_succ, Nat.mul_comm] using hpow⟩
    have hq_eq_two : ringExpChar K = 2 :=
      (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).1 hq_dvd_two
    have hExp : ExpChar K 2 := ringExpChar.of_eq (R := K) hq_eq_two
    have htwo_zero : (2 : K) = 0 := by
      cases hExp with
      | prime _ =>
          exact CharP.cast_eq_zero K 2
    exact CharP.ringChar_of_prime_eq_zero (R := K) Nat.prime_two htwo_zero
  · simp [hone] at hpow

/-- Helper for Exercise 9.20.9: a nonseparable quadratic extension has discriminant class `0`
because its trace pairing is identically zero. -/
lemma quadratic_extension_discriminant_eq_zero_of_not_separable
    (hsep : ¬ Algebra.IsSeparable K L) :
    Δ = (⟦(0 : K)⟧ : SquareClass K) := by
  -- Every entry of the trace matrix vanishes in the inseparable case, so its determinant does too.
  have hdiscr_zero : Algebra.discr K (Module.finBasis K L) = 0 := by
    haveI : Nonempty (Fin (Module.finrank K L)) := by
      rw [Algebra.IsQuadraticExtension.finrank_eq_two K L]
      infer_instance
    rw [Algebra.discr_def]
    have hmatrix_zero : Algebra.traceMatrix K (Module.finBasis K L) = 0 := by
      ext i j
      simp [Algebra.traceMatrix_apply, Algebra.trace_eq_zero_of_not_isSeparable hsep]
    simpa [hmatrix_zero] using
      (Matrix.det_zero (n := Fin (Module.finrank K L)) (R := K))
  calc
    Δ = SquareClass.mk K (Algebra.discr K (Module.finBasis K L)) := by
      simpa using (fieldExtensionDiscriminant_eq (K := K) (L := L) (Module.finBasis K L))
    _ = (⟦(0 : K)⟧ : SquareClass K) := by simp [hdiscr_zero]

/-- Owner-level projection of the exact trichotomy: a purely inseparable quadratic field extension
cannot also be separable. The discriminant equalities appearing in the source-facing branches are
derived consequences, so the companion theorem is stated directly in the canonical owner
vocabulary. -/
theorem quadratic_extension_not_separable_of_isPurelyInseparable
    (hpure : IsPurelyInseparable K L) :
    ¬ Algebra.IsSeparable K L :=
  by
    letI : IsPurelyInseparable K L := hpure
    intro hsep
    -- If every element comes from the base field, the quadratic extension would collapse to degree `1`.
    have htop : (⊥ : IntermediateField K L) = ⊤ := by
      apply top_unique
      intro x hx
      obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable K L x
      rw [← hy]
      exact IntermediateField.mem_bot.mpr ⟨y, rfl⟩
    have hfinrank_one : Module.finrank K L = 1 :=
      (IntermediateField.bot_eq_top_iff_finrank_eq_one (F := K) (E := L)).1 htop
    have hfinrank_two : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
    omega

/-- Owner-level projection of the exact trichotomy: a quadratic field extension in characteristic
different from `2` cannot be purely inseparable. The zero-discriminant clause is therefore kept
only in the main source-facing trichotomy. -/
theorem quadratic_extension_not_purelyInseparable_of_char_ne_two
    (hchar : ringChar K ≠ 2) :
    ¬ IsPurelyInseparable K L :=
  by
    intro hpure
    have hnotsep : ¬ Algebra.IsSeparable K L :=
      quadratic_extension_not_separable_of_isPurelyInseparable (K := K) (L := L) hpure
    exact hchar <|
      (quadratic_extension_isPurelyInseparable_and_char_two_of_not_separable
        (K := K) (L := L) hnotsep).2

/-- Source-facing branch extracted from the exact trichotomy: in characteristic `2`, a purely
inseparable quadratic extension is generated by an element whose square lies in the base field.
The base-field membership is expressed canonically as membership in `(⊥ : IntermediateField K L)`,
with `IntermediateField.mem_bot` available as the bridge back to an explicit `algebraMap`
witness when needed. -/
theorem exists_square_generator_of_purelyInseparable_quadratic_extension
    (hpure : IsPurelyInseparable K L) :
    ∃ x : L, x ^ 2 ∈ (⊥ : IntermediateField K L) ∧ K⟮x⟯ = ⊤ := by
  letI : IsPurelyInseparable K L := hpure
  have hnotsep : ¬ Algebra.IsSeparable K L :=
    quadratic_extension_not_separable_of_isPurelyInseparable (K := K) (L := L) hpure
  have hchar : ringChar K = 2 :=
    (quadratic_extension_isPurelyInseparable_and_char_two_of_not_separable
      (K := K) (L := L) hnotsep).2
  haveI : CharP K 2 := ringChar.of_eq hchar
  have hbot_ne_top : (⊥ : IntermediateField K L) ≠ ⊤ := by
    intro hbot_top
    have hfinrank_one : Module.finrank K L = 1 :=
      (IntermediateField.bot_eq_top_iff_finrank_eq_one (F := K) (E := L)).1 hbot_top
    have hfinrank_two : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
    omega
  have hx_exists : ∃ x : L, x ∉ (⊥ : IntermediateField K L) := by
    by_contra hx_exists
    -- Negation normalization turns the contradiction hypothesis into base-field membership.
    push_neg at hx_exists
    apply hbot_ne_top
    apply top_unique
    intro x hx
    exact hx_exists x
  obtain ⟨x, hx_not_bot⟩ := hx_exists
  have hprime : Nat.Prime (Module.finrank K L) := by
    simpa [Algebra.IsQuadraticExtension.finrank_eq_two K L] using Nat.prime_two
  have hsimple : IsSimpleOrder (IntermediateField K L) :=
    IntermediateField.isSimpleOrder_of_finrank_prime (F := K) (E := L) hprime
  have hx_adjoin_top : K⟮x⟯ = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top K⟮x⟯ with hx_bot | hx_top
    · exact (hx_not_bot <| by simpa [hx_bot] using (IntermediateField.mem_adjoin_simple_self K x)).elim
    · exact hx_top
  have hx_minpoly_degree : (minpoly K x).natDegree = 2 := by
    have hfinrank_simple : Module.finrank K K⟮x⟯ = 2 := by
      calc
        Module.finrank K K⟮x⟯ = Module.finrank K (⊤ : IntermediateField K L) := by
          rw [hx_adjoin_top]
        _ = Module.finrank K L := by simp
        _ = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x)] at hfinrank_simple
    exact hfinrank_simple
  have hx_elemExponent_one : IsPurelyInseparable.elemExponent K x = 1 := by
    have hpow :
        2 ^ IsPurelyInseparable.elemExponent K x = 2 ^ 1 := by
      simpa [hx_minpoly_degree] using
        (IsPurelyInseparable.minpoly_natDegree_eq' (K := K) (L := L) 2 x).symm
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hpow
  have hx_square_range : x ^ 2 ∈ (algebraMap K L).range := by
    refine ⟨IsPurelyInseparable.elemReduct K x, ?_⟩
    simpa [hx_elemExponent_one] using
      (IsPurelyInseparable.algebraMap_elemReduct_eq' (K := K) (L := L) 2 x)
  have hx_square : x ^ 2 ∈ (⊥ : IntermediateField K L) := by
    simpa [IntermediateField.mem_bot] using hx_square_range
  have hx_top : K⟮x⟯ = ⊤ := by
    exact hx_adjoin_top
  exact ⟨x, hx_square, hx_top⟩

/-- Helper for Exercise 9.20.9: in a quadratic extension, any element outside the base field
already generates the whole extension. -/
lemma adjoin_eq_top_of_not_mem_bot {x : L} (hx : x ∉ (⊥ : IntermediateField K L)) :
    K⟮x⟯ = ⊤ := by
  -- Prime degree leaves no room for a proper nontrivial intermediate field.
  have hprime : Nat.Prime (Module.finrank K L) := by
    simpa [Algebra.IsQuadraticExtension.finrank_eq_two K L] using Nat.prime_two
  have hsimple : IsSimpleOrder (IntermediateField K L) :=
    IntermediateField.isSimpleOrder_of_finrank_prime (F := K) (E := L) hprime
  rcases hsimple.eq_bot_or_eq_top K⟮x⟯ with hx_bot | hx_top
  · exact (hx <| (IntermediateField.adjoin_simple_eq_bot_iff).1 hx_bot).elim
  · exact hx_top

/-- Helper for Exercise 9.20.9: every quadratic extension admits a primitive generator outside the
base field. -/
lemma exists_primitive_generator :
    ∃ x : L, x ∉ (⊥ : IntermediateField K L) ∧ K⟮x⟯ = ⊤ := by
  -- The base field cannot already be the whole quadratic extension.
  have hbot_ne_top : (⊥ : IntermediateField K L) ≠ ⊤ := by
    intro hbot_top
    have hfinrank_one : Module.finrank K L = 1 :=
      (IntermediateField.bot_eq_top_iff_finrank_eq_one (F := K) (E := L)).1 hbot_top
    have hfinrank_two : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
    omega
  obtain ⟨x, hx_not_bot⟩ :
      ∃ x : L, x ∉ (⊥ : IntermediateField K L) := by
    by_contra hx_exists
    push_neg at hx_exists
    apply hbot_ne_top
    apply top_unique
    intro x hx
    exact hx_exists x
  -- Any such element is automatically primitive by the simple-order argument above.
  exact ⟨x, hx_not_bot, adjoin_eq_top_of_not_mem_bot (K := K) (L := L) hx_not_bot⟩

/-- Helper for Exercise 9.20.9: a primitive element of a quadratic extension has quadratic minimal
polynomial. -/
lemma minpoly_natDegree_eq_two_of_adjoin_top {x : L} (hx_top : K⟮x⟯ = ⊤) :
    (minpoly K x).natDegree = 2 := by
  -- The simple extension has the same dimension as the whole quadratic extension.
  have hx_int : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hfinrank_simple : Module.finrank K K⟮x⟯ = 2 := by
    calc
      Module.finrank K K⟮x⟯ = Module.finrank K (⊤ : IntermediateField K L) := by
        rw [hx_top]
      _ = Module.finrank K L := by
        simp
      _ = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  rw [IntermediateField.adjoin.finrank hx_int] at hfinrank_simple
  exact hfinrank_simple

/-- Helper for Exercise 9.20.9: a monic quadratic polynomial is determined by its next and
constant coefficients. -/
lemma quadratic_monic_eq_X_sq_add_C_mul_X_add_C {p : K[X]} (hp : p.Monic)
    (hdeg : p.natDegree = 2) :
    p = X ^ 2 + C p.nextCoeff * X + C (p.coeff 0) := by
  -- The general quadratic normal form specializes to the monic case after rewriting the top two
  -- coefficients.
  have hquad :
      p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
    apply Polynomial.eq_quadratic_of_degree_le_two
    exact degree_le_of_natDegree_le (le_of_eq hdeg)
  have hcoeff2 : p.coeff 2 = 1 := by
    simpa [hdeg] using hp.coeff_natDegree
  have hnext : p.nextCoeff = p.coeff 1 := by
    have hpos : 0 < p.natDegree := by
      simpa [hdeg]
    simpa [hdeg] using (Polynomial.nextCoeff_of_natDegree_pos (p := p) hpos)
  calc
    p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := hquad
    _ = X ^ 2 + C p.nextCoeff * X + C (p.coeff 0) := by
      rw [hcoeff2, ← hnext]
      simp

/-- Helper for Exercise 9.20.9: in characteristic `2`, the scalar `-1` is equal to `1`. -/
lemma neg_one_eq_one_of_ringChar_two (hchar : ringChar K = 2) : (-(1 : K)) = 1 := by
  letI : CharP K 2 := ringChar.of_eq hchar
  -- Cancelling a final `1` reduces the claim to `1 + 1 = 0`.
  have htwo_zero : (2 : K) = 0 := CharP.cast_eq_zero K 2
  apply add_right_cancel (b := (1 : K))
  simp [one_add_one_eq_two, htwo_zero]

/-- Helper for Exercise 9.20.9: in characteristic `2`, a quadratic primitive generator with trace
`1` has minimal polynomial next coefficient `1`. -/
lemma minpoly_nextCoeff_eq_one_of_trace_one_generator_char_two
    (hsep : Algebra.IsSeparable K L) {z : L} (hz_trace : Algebra.trace K L z = 1)
    (hz_top : K⟮z⟯ = ⊤) (hchar : ringChar K = 2) :
    (minpoly K z).nextCoeff = 1 := by
  letI : Algebra.IsSeparable K L := hsep
  -- The quadratic trace formula determines the next coefficient up to a sign.
  have hfinrank_z : Module.finrank K⟮z⟯ L = 1 := by
    rw [hz_top]
    simp
  have htrace_formula : Algebra.trace K L z = -(minpoly K z).nextCoeff := by
    simpa [hfinrank_z] using
      (trace_eq_finrank_mul_minpoly_nextCoeff (K := K) (L := L) z)
  have hnext_neg : -(minpoly K z).nextCoeff = 1 := by
    simpa [hz_trace] using htrace_formula.symm
  have hnext_neg_one : (minpoly K z).nextCoeff = -(1 : K) := by
    simpa using congrArg Neg.neg hnext_neg
  -- In characteristic `2`, negation fixes `1`.
  simpa [neg_one_eq_one_of_ringChar_two (K := K) hchar] using hnext_neg_one

/-- Helper for Exercise 9.20.9: a quadratic primitive generator with trace `0` has minimal
polynomial next coefficient `0`. -/
lemma minpoly_nextCoeff_eq_zero_of_trace_zero_generator
    {y : L} (hy_trace : Algebra.trace K L y = 0) (hy_top : K⟮y⟯ = ⊤) :
    (minpoly K y).nextCoeff = 0 := by
  -- The same trace formula shows the next coefficient vanishes.
  have hfinrank_y : Module.finrank K⟮y⟯ L = 1 := by
    rw [hy_top]
    simp
  have htrace_formula : Algebra.trace K L y = -(minpoly K y).nextCoeff := by
    simpa [hfinrank_y] using
      (trace_eq_finrank_mul_minpoly_nextCoeff (K := K) (L := L) y)
  have hneg_next : -(minpoly K y).nextCoeff = 0 := by
    simpa [hy_trace] using htrace_formula.symm
  exact neg_eq_zero.mp hneg_next

/-- Helper for Exercise 9.20.9: in characteristic `2`, a separable quadratic extension admits a
primitive generator of trace `1` and Artin-Schreier form. -/
lemma exists_artin_schreier_generator_of_separable_quadratic_char_two
    (hsep : Algebra.IsSeparable K L) (hchar : ringChar K = 2) :
    ∃ z : L, Algebra.trace K L z = 1 ∧ z ^ 2 - z ∈ (⊥ : IntermediateField K L) ∧
      K⟮z⟯ = ⊤ := by
  letI : CharP K 2 := ringChar.of_eq hchar
  letI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  -- Normalize an element with nonzero trace so that its trace becomes exactly `1`.
  have htrace_ne_zero : Algebra.trace K L ≠ 0 := Algebra.trace_ne_zero K L
  obtain ⟨x, hx_trace⟩ : ∃ x : L, Algebra.trace K L x ≠ 0 := by
    by_contra hx
    apply htrace_ne_zero
    ext x
    by_cases hx_zero : Algebra.trace K L x = 0
    · exact hx_zero
    · exact False.elim (hx ⟨x, hx_zero⟩)
  let z : L := (algebraMap K L ((Algebra.trace K L x)⁻¹)) * x
  have hz_trace : Algebra.trace K L z = 1 := by
    -- Scaling by the inverse trace forces the trace to be one.
    calc
      Algebra.trace K L z = Algebra.trace K L (((Algebra.trace K L x)⁻¹ : K) • x) := by
        simp [z, Algebra.smul_def]
      _ = (Algebra.trace K L x)⁻¹ * Algebra.trace K L x := by
        simpa [Algebra.smul_def] using
          (LinearMap.map_smul_of_tower (Algebra.trace K L) ((Algebra.trace K L x)⁻¹) x)
      _ = 1 := by
        exact inv_mul_cancel₀ hx_trace
  have hz_not_bot : z ∉ (⊥ : IntermediateField K L) := by
    -- Elements of the base field have zero trace in characteristic `2`.
    intro hz_bot
    rcases IntermediateField.mem_bot.mp hz_bot with ⟨a, ha⟩
    have htwo_zero : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have htrace_bot : Algebra.trace K L z = 0 := by
      calc
        Algebra.trace K L z = (2 : K) * a := by
          rw [ha.symm, Algebra.trace_algebraMap]
          simp [Algebra.IsQuadraticExtension.finrank_eq_two K L]
        _ = 0 := by
          simp [htwo_zero]
    have hzero_one : (0 : K) = 1 := htrace_bot.symm.trans hz_trace
    exact zero_ne_one hzero_one
  have hz_top : K⟮z⟯ = ⊤ :=
    adjoin_eq_top_of_not_mem_bot (K := K) (L := L) hz_not_bot
  have hz_top_subalg : Algebra.adjoin K ({z} : Set L) = ⊤ := by
    -- Convert the intermediate-field generator statement to the subalgebra statement expected by
    -- `PowerBasis.ofAdjoinEqTop`.
    simpa [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (F := K) (E := L)
      (hα := (isAlgebraic_iff_isIntegral.2 (Algebra.IsIntegral.isIntegral z)))] using
      congrArg IntermediateField.toSubalgebra hz_top
  have hz_int : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  have hdeg : (minpoly K z).natDegree = 2 :=
    minpoly_natDegree_eq_two_of_adjoin_top (K := K) (L := L) hz_top
  have hnext_one : (minpoly K z).nextCoeff = 1 :=
    minpoly_nextCoeff_eq_one_of_trace_one_generator_char_two
      (K := K) (L := L) hsep hz_trace hz_top hchar
  have hpoly :
      minpoly K z =
        X ^ 2 + C (minpoly K z).nextCoeff * X + C ((minpoly K z).coeff 0) :=
    quadratic_monic_eq_X_sq_add_C_mul_X_add_C (K := K)
      (p := minpoly K z) (minpoly.monic hz_int) hdeg
  have hz_root :
      z ^ 2 + z + algebraMap K L ((minpoly K z).coeff 0) = 0 := by
    -- Evaluating the quadratic minimal polynomial at `z` expresses `z² - z` over the base field.
    have hroot := minpoly.aeval K z
    rw [hpoly] at hroot
    simpa [hnext_one] using hroot
  have hneg_z : -z = z := by
    have htwo_zero : (2 : L) = 0 := CharP.cast_eq_zero L 2
    -- In characteristic `2`, every element is its own negative.
    apply neg_eq_iff_add_eq_zero.mpr
    calc
      z + z = (2 : L) * z := by ring
      _ = 0 := by simp [htwo_zero]
  have hz_as : z ^ 2 - z = algebraMap K L (-(minpoly K z).coeff 0) := by
    -- Move the constant term to the other side and use `-z = z`.
    calc
      z ^ 2 - z = z ^ 2 + z := by
        simp [sub_eq_add_neg, hneg_z]
      _ = algebraMap K L (-(minpoly K z).coeff 0) := by
        calc
          z ^ 2 + z = z ^ 2 + z + algebraMap K L ((minpoly K z).coeff 0) -
              algebraMap K L ((minpoly K z).coeff 0) := by
                ring
          _ = algebraMap K L (-(minpoly K z).coeff 0) := by
                rw [hz_root]
                simp
  have hz_as_bot : z ^ 2 - z ∈ (⊥ : IntermediateField K L) := by
    exact IntermediateField.mem_bot.mpr ⟨-(minpoly K z).coeff 0, hz_as.symm⟩
  exact ⟨z, hz_trace, hz_as_bot, hz_top⟩

/-- Helper for Exercise 9.20.9: an Artin-Schreier primitive generator in characteristic `2` has
discriminant class `1`. -/
lemma quadratic_extension_discriminant_eq_one_of_artin_schreier_generator
    (hsep : Algebra.IsSeparable K L) {z : L} (hz_trace : Algebra.trace K L z = 1)
    (hz : z ^ 2 - z ∈ (⊥ : IntermediateField K L)) (hz_top : K⟮z⟯ = ⊤)
    (hchar : ringChar K = 2) :
    Δ = (⟦(1 : K)⟧ : SquareClass K) := by
  letI : Algebra.IsSeparable K L := hsep
  letI : CharP K 2 := ringChar.of_eq hchar
  letI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  -- The trace formula fixes the next coefficient, so the derivative becomes the constant `1`.
  have hz_int : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  have hdeg : (minpoly K z).natDegree = 2 :=
    minpoly_natDegree_eq_two_of_adjoin_top (K := K) (L := L) hz_top
  have hnext_one : (minpoly K z).nextCoeff = 1 :=
    minpoly_nextCoeff_eq_one_of_trace_one_generator_char_two
      (K := K) (L := L) hsep hz_trace hz_top hchar
  have hpoly :
      minpoly K z =
        X ^ 2 + C (minpoly K z).nextCoeff * X + C ((minpoly K z).coeff 0) :=
    quadratic_monic_eq_X_sq_add_C_mul_X_add_C (K := K)
      (p := minpoly K z) (minpoly.monic hz_int) hdeg
  have hz_deriv : Polynomial.aeval z (minpoly K z).derivative = 1 := by
    have htwo_zero : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hone_add : (1 : K) + 1 = 0 := by
      simpa [one_add_one_eq_two] using htwo_zero
    have hderiv : (minpoly K z).derivative = (1 : K[X]) := by
      rw [hpoly]
      simp [hnext_one, hone_add]
    rw [hderiv]
    simp
  have hz_top_subalg : Algebra.adjoin K ({z} : Set L) = ⊤ := by
    -- Convert the intermediate-field generator statement to the subalgebra statement expected by
    -- `PowerBasis.ofAdjoinEqTop`.
    simpa [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (F := K) (E := L)
      (hα := (isAlgebraic_iff_isIntegral.2 hz_int))] using
      congrArg IntermediateField.toSubalgebra hz_top
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hz_int hz_top_subalg
  have hpb_gen : pb.gen = z := by
    simpa [pb] using (PowerBasis.ofAdjoinEqTop_gen (K := K) (S := L) hz_int hz_top_subalg)
  have hpb_dim : pb.dim = 2 := by
    simpa [pb, hdeg] using (PowerBasis.ofAdjoinEqTop_dim (K := K) (S := L) hz_int hz_top_subalg)
  have hdiscr : Algebra.discr K pb.basis = 1 := by
    -- The quadratic power-basis discriminant is the norm of the constant derivative.
    calc
      Algebra.discr K pb.basis =
          (-1) ^ (Module.finrank K L * (Module.finrank K L - 1) / 2) *
            Algebra.norm K (Polynomial.aeval pb.gen (minpoly K pb.gen).derivative) := by
              simpa using (Algebra.discr_powerBasis_eq_norm (K := K) (L := L) (pb := pb))
      _ = (-1 : K) ^ 1 * Algebra.norm K (1 : L) := by
            simp [Algebra.IsQuadraticExtension.finrank_eq_two K L, hpb_gen, hz_deriv]
      _ = 1 := by
            simp [neg_one_eq_one_of_ringChar_two (K := K) hchar]
  -- Conclude by reading the discriminant class on this power basis.
  calc
    Δ = SquareClass.mk K (Algebra.discr K pb.basis) := by
      simpa using (fieldExtensionDiscriminant_eq (K := K) (L := L) pb.basis)
    _ = SquareClass.mk K (1 : K) := by
      rw [hdiscr]
    _ = (⟦(1 : K)⟧ : SquareClass K) := rfl

/-- Helper for Exercise 9.20.9: in characteristic different from `2`, a quadratic extension admits
a primitive generator of trace `0` whose square lies in the base field. -/
lemma exists_trace_zero_square_generator_of_char_ne_two
    (hchar : ringChar K ≠ 2) :
    ∃ y : L, Algebra.trace K L y = 0 ∧ y ^ 2 ∈ (⊥ : IntermediateField K L) ∧
      K⟮y⟯ = ⊤ := by
  have htwo_ne_zero : (2 : K) ≠ 0 := by
    intro htwo_zero
    exact hchar (CharP.ringChar_of_prime_eq_zero (R := K) Nat.prime_two htwo_zero)
  have hsep : Algebra.IsSeparable K L := by
    by_contra hnot
    exact hchar
      ((quadratic_extension_isPurelyInseparable_and_char_two_of_not_separable
        (K := K) (L := L) hnot).2)
  obtain ⟨x, hx_not_bot, hx_top⟩ := exists_primitive_generator (K := K) (L := L)
  let t : K := (2 : K)⁻¹ * Algebra.trace K L x
  let y : L := x - algebraMap K L t
  have hy_trace : Algebra.trace K L y = 0 := by
    -- Subtracting half the trace kills the linear coefficient.
    calc
      Algebra.trace K L y = Algebra.trace K L x - Algebra.trace K L (algebraMap K L t) := by
        simp [y]
      _ = Algebra.trace K L x - (2 : K) * t := by
        rw [Algebra.trace_algebraMap]
        simp [Algebra.IsQuadraticExtension.finrank_eq_two K L]
      _ = Algebra.trace K L x - (2 : K) * ((2 : K)⁻¹ * Algebra.trace K L x) := by
        simp [t]
      _ = 0 := by
        rw [show (2 : K) * ((2 : K)⁻¹ * Algebra.trace K L x) =
            ((2 : K) * (2 : K)⁻¹) * Algebra.trace K L x by ring]
        rw [mul_inv_cancel₀ htwo_ne_zero, one_mul, sub_self]
  have hy_not_bot : y ∉ (⊥ : IntermediateField K L) := by
    -- Translating by a base-field element preserves non-membership in the base field.
    intro hy_bot
    have ht_mem : algebraMap K L t ∈ (⊥ : IntermediateField K L) :=
      IntermediateField.mem_bot.mpr ⟨t, rfl⟩
    have hx_mem : x ∈ (⊥ : IntermediateField K L) := by
      have hx_eq : x = y + algebraMap K L t := by
        simp [y]
      rw [hx_eq]
      exact (⊥ : IntermediateField K L).add_mem hy_bot ht_mem
    exact hx_not_bot hx_mem
  have hy_top : K⟮y⟯ = ⊤ :=
    adjoin_eq_top_of_not_mem_bot (K := K) (L := L) hy_not_bot
  have hy_int : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  have hdeg : (minpoly K y).natDegree = 2 :=
    minpoly_natDegree_eq_two_of_adjoin_top (K := K) (L := L) hy_top
  have hnext_zero : (minpoly K y).nextCoeff = 0 :=
    minpoly_nextCoeff_eq_zero_of_trace_zero_generator
      (K := K) (L := L) hy_trace hy_top
  have hpoly :
      minpoly K y =
        X ^ 2 + C (minpoly K y).nextCoeff * X + C ((minpoly K y).coeff 0) :=
    quadratic_monic_eq_X_sq_add_C_mul_X_add_C (K := K)
      (p := minpoly K y) (minpoly.monic hy_int) hdeg
  have hy_root : y ^ 2 + algebraMap K L ((minpoly K y).coeff 0) = 0 := by
    -- With zero trace, the minimal polynomial has no linear term.
    have hroot := minpoly.aeval K y
    rw [hpoly] at hroot
    simpa [hnext_zero] using hroot
  have hy_square_eq : y ^ 2 = algebraMap K L (-(minpoly K y).coeff 0) := by
    calc
      y ^ 2 = y ^ 2 + algebraMap K L ((minpoly K y).coeff 0) -
          algebraMap K L ((minpoly K y).coeff 0) := by
            ring
      _ = algebraMap K L (-(minpoly K y).coeff 0) := by
            rw [hy_root]
            simp
  have hy_square_bot : y ^ 2 ∈ (⊥ : IntermediateField K L) := by
    exact IntermediateField.mem_bot.mpr ⟨-(minpoly K y).coeff 0, hy_square_eq.symm⟩
  exact ⟨y, hy_trace, hy_square_bot, hy_top⟩

/-- Helper for Exercise 9.20.9: in characteristic different from `2`, a primitive trace-zero
square-root generator represents the discriminant square class. -/
lemma quadratic_extension_discriminant_eq_squareclass_of_square_generator
    {y : L} (hy_trace : Algebra.trace K L y = 0) {a : K}
    (hy : y ^ 2 = algebraMap K L a) (hy_top : K⟮y⟯ = ⊤) (hchar : ringChar K ≠ 2) :
    Δ = (⟦a⟧ : SquareClass K) := by
  have hsep : Algebra.IsSeparable K L := by
    by_contra hnot
    exact hchar
      ((quadratic_extension_isPurelyInseparable_and_char_two_of_not_separable
        (K := K) (L := L) hnot).2)
  letI : Algebra.IsSeparable K L := hsep
  have htwo_ne_zero : (2 : K) ≠ 0 := by
    intro htwo_zero
    exact hchar (CharP.ringChar_of_prime_eq_zero (R := K) Nat.prime_two htwo_zero)
  have hy_int : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  have hdeg : (minpoly K y).natDegree = 2 :=
    minpoly_natDegree_eq_two_of_adjoin_top (K := K) (L := L) hy_top
  have hnext_zero : (minpoly K y).nextCoeff = 0 :=
    minpoly_nextCoeff_eq_zero_of_trace_zero_generator
      (K := K) (L := L) hy_trace hy_top
  have hpoly :
      minpoly K y =
        X ^ 2 + C (minpoly K y).nextCoeff * X + C ((minpoly K y).coeff 0) :=
    quadratic_monic_eq_X_sq_add_C_mul_X_add_C (K := K)
      (p := minpoly K y) (minpoly.monic hy_int) hdeg
  have hy_root : y ^ 2 + algebraMap K L ((minpoly K y).coeff 0) = 0 := by
    -- Zero trace removes the linear term from the quadratic minimal polynomial.
    have hroot := minpoly.aeval K y
    rw [hpoly] at hroot
    simpa [hnext_zero] using hroot
  have hy_square_eq : y ^ 2 = algebraMap K L (-(minpoly K y).coeff 0) := by
    calc
      y ^ 2 = y ^ 2 + algebraMap K L ((minpoly K y).coeff 0) -
          algebraMap K L ((minpoly K y).coeff 0) := by
            ring
      _ = algebraMap K L (-(minpoly K y).coeff 0) := by
            rw [hy_root]
            simp
  have hcoeff0_neg : -(minpoly K y).coeff 0 = a := by
    exact (algebraMap K L).injective (hy_square_eq.symm.trans hy)
  have hcoeff0 : (minpoly K y).coeff 0 = -a := by
    simpa using congrArg Neg.neg hcoeff0_neg
  have hy_top_subalg : Algebra.adjoin K ({y} : Set L) = ⊤ := by
    -- Convert the intermediate-field generator statement to the subalgebra statement expected by
    -- `PowerBasis.ofAdjoinEqTop`.
    simpa [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (F := K) (E := L)
      (hα := (isAlgebraic_iff_isIntegral.2 (Algebra.IsIntegral.isIntegral y)))] using
      congrArg IntermediateField.toSubalgebra hy_top
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hy_int hy_top_subalg
  have hpb_gen : pb.gen = y := by
    simpa [pb] using (PowerBasis.ofAdjoinEqTop_gen (K := K) (S := L) hy_int hy_top_subalg)
  have hpb_dim : pb.dim = 2 := by
    simpa [pb, hdeg] using (PowerBasis.ofAdjoinEqTop_dim (K := K) (S := L) hy_int hy_top_subalg)
  have hy_deriv : Polynomial.aeval y (minpoly K y).derivative = (2 : L) * y := by
    -- The derivative of `X² + c` is `2X`.
    have hderiv : (minpoly K y).derivative = C (2 : K) * X := by
      rw [hpoly]
      simpa [hnext_zero, one_add_one_eq_two, C_eq_natCast]
    rw [hderiv]
    calc
      Polynomial.aeval y (C (2 : K) * X) = algebraMap K L (2 : K) * y := by
        simp
      _ = (2 : L) * y := by
        rw [show algebraMap K L (2 : K) = (2 : L) from map_natCast (algebraMap K L) 2]
  have hnorm_y : Algebra.norm K y = -a := by
    -- The constant coefficient of the minimal polynomial computes the norm of the generator.
    calc
      Algebra.norm K y = Algebra.norm K pb.gen := by
        simp [hpb_gen]
      _ = (-1 : K) ^ pb.dim * (minpoly K pb.gen).coeff 0 := by
        simpa using (Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb)
      _ = -a := by
        simp [hpb_dim, hpb_gen, hcoeff0]
  have hy_deriv_norm :
      Algebra.norm K (Polynomial.aeval y (minpoly K y).derivative) = -4 * a := by
    -- Multiplicativity of the norm reduces the derivative norm to the generator norm.
    calc
      Algebra.norm K (Polynomial.aeval y (minpoly K y).derivative)
          = Algebra.norm K ((2 : L) * y) := by
              rw [hy_deriv]
      _ = Algebra.norm K (algebraMap K L (2 : K) * y) := by
              rw [show (2 : L) = algebraMap K L (2 : K) from (map_natCast (algebraMap K L) 2).symm]
      _ = Algebra.norm K (algebraMap K L (2 : K)) * Algebra.norm K y := by
              rw [map_mul]
      _ = (2 : K) ^ 2 * (-a) := by
              rw [hnorm_y, Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two K L]
      _ = -4 * a := by
              ring
  have hdiscr : Algebra.discr K pb.basis = 4 * a := by
    -- The power-basis discriminant is `- norm(2y) = 4a`.
    calc
      Algebra.discr K pb.basis =
          (-1) ^ (Module.finrank K L * (Module.finrank K L - 1) / 2) *
            Algebra.norm K (Polynomial.aeval pb.gen (minpoly K pb.gen).derivative) := by
              simpa using (Algebra.discr_powerBasis_eq_norm (K := K) (L := L) (pb := pb))
      _ = (-1 : K) * (-4 * a) := by
            simp [Algebra.IsQuadraticExtension.finrank_eq_two K L, hpb_gen, hy_deriv_norm]
      _ = 4 * a := by
            ring
  have hsquare :
      SquareClass.mk K (4 * a) = (⟦a⟧ : SquareClass K) := by
    -- The factor `4 = 2²` is a square in the base field.
    rw [SquareClass.mk_eq_mk_iff]
    refine ⟨Units.mk0 2 htwo_ne_zero, ?_⟩
    simp [pow_two]
    left
    norm_num
  calc
    Δ = SquareClass.mk K (Algebra.discr K pb.basis) := by
      simpa using (fieldExtensionDiscriminant_eq (K := K) (L := L) pb.basis)
    _ = SquareClass.mk K (4 * a) := by
      rw [hdiscr]
    _ = (⟦a⟧ : SquareClass K) := hsquare

/-- Source-facing branch extracted from the exact trichotomy: in characteristic not `2`, a
quadratic extension is generated by a square root representing its discriminant class. Together
with `quadratic_extension_discriminant_ne_one_of_char_ne_two`, this recovers the third textbook
branch. -/
theorem exists_discriminant_square_root_generator_of_char_ne_two
    (hchar : ringChar K ≠ 2) :
    ∃ y : L, ∃ a : K, Δ = (⟦a⟧ : SquareClass K) ∧
      y ^ 2 = algebraMap K L a ∧ K⟮y⟯ = ⊤ := by
  -- Use the trace-zero normal form and then identify the discriminant class on that generator.
  obtain ⟨y, hy_trace, hy_square_bot, hy_top⟩ :=
    exists_trace_zero_square_generator_of_char_ne_two (K := K) (L := L) hchar
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hy_square_bot
  have hy : y ^ 2 = algebraMap K L a := by
    simpa using ha.symm
  have hdisc :
      Δ = (⟦a⟧ : SquareClass K) :=
    quadratic_extension_discriminant_eq_squareclass_of_square_generator
      (K := K) (L := L) hy_trace hy hy_top hchar
  exact ⟨y, a, hdisc, hy, hy_top⟩

/-- Owner-level projection of the exact trichotomy: in characteristic not `2`, the discriminant of
a quadratic field extension is not a square in the base field, expressed as the discriminant
square class not being `1`. -/
theorem quadratic_extension_discriminant_ne_one_of_char_ne_two
    (hchar : ringChar K ≠ 2) : Δ ≠ (⟦(1 : K)⟧ : SquareClass K) :=
  by
    -- A square representative would force the primitive square-root generator back into the base.
    intro hΔ_one
    obtain ⟨y, a, hdisc, hy, hy_top⟩ :=
      exists_discriminant_square_root_generator_of_char_ne_two (K := K) (L := L) hchar
    have hsq : (⟦a⟧ : SquareClass K) = (⟦(1 : K)⟧ : SquareClass K) := by
      calc
        (⟦a⟧ : SquareClass K) = Δ := hdisc.symm
        _ = (⟦(1 : K)⟧ : SquareClass K) := hΔ_one
    rcases (SquareClass.mk_eq_mk_iff (K := K) (a := a) (b := (1 : K))).1 hsq with ⟨u, hu⟩
    have hu_sq : a = (↑u : K) ^ 2 := by
      simpa [pow_two] using hu
    have hfactor :
        (y - algebraMap K L (↑u : K)) * (y + algebraMap K L (↑u : K)) = 0 := by
      calc
        (y - algebraMap K L (↑u : K)) * (y + algebraMap K L (↑u : K))
            = y ^ 2 - (algebraMap K L (↑u : K)) ^ 2 := by
                ring
        _ = algebraMap K L a - algebraMap K L ((↑u : K) ^ 2) := by
              rw [hy, map_pow]
        _ = 0 := by
              rw [hu_sq]
              ring
    have hy_bot : y ∈ (⊥ : IntermediateField K L) := by
      rcases mul_eq_zero.mp hfactor with hy_minus | hy_plus
      · exact IntermediateField.mem_bot.mpr ⟨(↑u : K), (sub_eq_zero.mp hy_minus).symm⟩
      · have hy_eq : y = algebraMap K L (-(↑u : K)) := by
          calc
            y = y + algebraMap K L (↑u : K) - algebraMap K L (↑u : K) := by
                  ring
            _ = algebraMap K L (-(↑u : K)) := by
                  rw [hy_plus]
                  simp
        exact IntermediateField.mem_bot.mpr ⟨-(↑u : K), hy_eq.symm⟩
    have hy_adjoin_bot : K⟮y⟯ = (⊥ : IntermediateField K L) :=
      (IntermediateField.adjoin_simple_eq_bot_iff).2 hy_bot
    have hbot_top : (⊥ : IntermediateField K L) = ⊤ := hy_adjoin_bot.symm.trans hy_top
    have hfinrank_one : Module.finrank K L = 1 :=
      (IntermediateField.bot_eq_top_iff_finrank_eq_one (F := K) (E := L)).1 hbot_top
    have hfinrank_two : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
    omega

/-- Exercise 9.20.9 (1): for a quadratic field extension `L/K`, exactly one of the three textbook
cases occurs: the discriminant is `0`, the characteristic is `2`, and `L/K` is purely
inseparable generated by a square root from the base field; the discriminant is `1`, the
characteristic is `2`, and `L/K` is separable; or the discriminant is not a square, the
characteristic is not `2`, and `L` is generated by a square root of a representative of its
discriminant class. The shorter owner-level projections are recorded separately as companion
theorems. -/
-- Proof sketch: split according to whether `L/K` is separable. In characteristic `2`, a
-- degree-two inseparable extension is purely inseparable and forces discriminant `0`, while the
-- separable branch has discriminant `1`. If `ringChar K ≠ 2`, the discriminant class is not the
-- square class of `1`, and the quadratic extension is generated by a square root representing the
-- discriminant class.
theorem quadratic_extension_discriminant_trichotomy :
    (purelyInseparableCase ∨ separableCase ∨ nonsquareCase) ∧
      ¬ (purelyInseparableCase ∧ separableCase) ∧
      ¬ (purelyInseparableCase ∧ nonsquareCase) ∧
      ¬ (separableCase ∧ nonsquareCase) :=
  by
    have hpure_sep :
        ¬ (purelyInseparableCase ∧ separableCase) := by
      -- The purely inseparable branch contradicts the separability assertion in the second branch.
      rintro ⟨hpure, hsep⟩
      exact (quadratic_extension_not_separable_of_isPurelyInseparable
        (K := K) (L := L) hpure.2.2.1) hsep.2.2
    have hpure_nonsquare :
        ¬ (purelyInseparableCase ∧ nonsquareCase) := by
      -- The first branch forces characteristic `2`, while the third excludes it.
      rintro ⟨hpure, hnonsquare⟩
      exact hnonsquare.2.1 hpure.2.1
    have hsep_nonsquare :
        ¬ (separableCase ∧ nonsquareCase) := by
      -- The second and third branches have incompatible characteristic assumptions.
      rintro ⟨hsep, hnonsquare⟩
      exact hnonsquare.2.1 hsep.2.1
    have hexists : purelyInseparableCase ∨ separableCase ∨ nonsquareCase := by
      by_cases hsep : Algebra.IsSeparable K L
      · by_cases hchar : ringChar K = 2
        · -- The separable characteristic-`2` branch is the Artin-Schreier normal form.
          obtain ⟨z, hz_trace, hz_as, hz_top⟩ :=
            exists_artin_schreier_generator_of_separable_quadratic_char_two
              (K := K) (L := L) hsep hchar
          have hdisc :
              Δ = (⟦(1 : K)⟧ : SquareClass K) :=
            quadratic_extension_discriminant_eq_one_of_artin_schreier_generator
              (K := K) (L := L) hsep hz_trace hz_as hz_top hchar
          exact Or.inr <| Or.inl ⟨hdisc, hchar, hsep⟩
        · -- In odd characteristic, complete the square and use the resulting square-root generator.
          have hdisc_ne :
              Δ ≠ (⟦(1 : K)⟧ : SquareClass K) :=
            quadratic_extension_discriminant_ne_one_of_char_ne_two (K := K) (L := L) hchar
          obtain ⟨y, a, hdisc, hy, hy_top⟩ :=
            exists_discriminant_square_root_generator_of_char_ne_two (K := K) (L := L) hchar
          exact Or.inr <| Or.inr ⟨hdisc_ne, hchar, ⟨y, a, hdisc, hy, hy_top⟩⟩
      · obtain ⟨hpure, hchar⟩ :=
          quadratic_extension_isPurelyInseparable_and_char_two_of_not_separable
            (K := K) (L := L) hsep
        have hdisc :
            Δ = (⟦(0 : K)⟧ : SquareClass K) :=
          quadratic_extension_discriminant_eq_zero_of_not_separable (K := K) (L := L) hsep
        obtain ⟨x, hx_square, hx_top⟩ :=
          exists_square_generator_of_purelyInseparable_quadratic_extension (K := K) (L := L) hpure
        exact Or.inl ⟨hdisc, hchar, hpure, ⟨x, hx_square, hx_top⟩⟩
    exact ⟨hexists, hpure_sep, hpure_nonsquare, hsep_nonsquare⟩

end Quadratic
