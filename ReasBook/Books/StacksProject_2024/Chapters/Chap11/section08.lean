import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_11_8_1 (from Chap11) -/
/- Domain-style sampling for Definition 11.8.1:
- primary domain: splitting fields of finite central simple algebras via scalar extension;
- sampled owner declarations:
  `CSA`,
  `CSA.baseChange`,
  `CSA.mk`,
  `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`;
- best owner abstraction: this item is `source-facing`, but its core/canonical owner object is the
  base-changed algebra `A.baseChange K : CSA K`; the splitting predicate should be defined by a
  matrix-algebra presentation of that owner, not by a separate wrapper carrying extra data.
- primitive data: existence of a `K`-algebra equivalence from `A.baseChange K` to a full matrix
  algebra over `K`.
- derived API: the positive-size reformulation is better exposed via the canonical positive natural
  numbers `ℕ+`, rather than by storing a separate `n ≠ 0` proof.

Source/core/bridge triage:
- `source-facing`: `CSA.IsSplitBy`, expressing that the field extension `K/k` splits `A`;
- `core/canonical`: the owner object `A.baseChange K : CSA K`;
- `bridge/view`: the companion positive-index reformulation below, which repackages the same matrix
  presentation using `ℕ+`. -/

universe u v w

variable {k : Type u} [Field k]

namespace CSA

variable (A : CSA.{u, v} k) (K : Type w) [Field K] [Algebra k K]

/-- Definition 11.8.1: a field extension `K/k` splits the finite central simple `k`-algebra `A`
if the scalar extension, viewed as the canonical base-changed central simple `K`-algebra
`A.baseChange K`, is `K`-algebra isomorphic to a full matrix algebra over `K`. -/
def IsSplitBy : Prop :=
  ∃ n : ℕ, Nonempty ((A.baseChange K) ≃ₐ[K] Matrix (Fin n) (Fin n) K)

/-- Textbook-positive reformulation of `IsSplitBy`: the matrix size may be indexed by a positive
natural number. -/
theorem isSplitBy_iff_exists_pnat_algEquiv_matrix :
    A.IsSplitBy K ↔
      ∃ n : ℕ+, Nonempty ((A.baseChange K) ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  constructor
  · rintro ⟨n, h⟩
    by_cases hn : n = 0
    · exfalso
      subst hn
      rcases h with ⟨e⟩
      exact zero_ne_one <| e.injective <| Subsingleton.elim _ _
    · exact ⟨⟨n, Nat.pos_of_ne_zero hn⟩, by simpa using h⟩
  · rintro ⟨n, h⟩
    exact ⟨(n : ℕ), by simpa using h⟩

end CSA

/-! ### Theorem_11_8_2 (from Chap11) -/
/- Domain-style sampling for Theorem 11.8.2:
- primary domain: splitting fields of finite central simple algebras, organized on the owner
  `CSA k` and its scalar-extension predicate `CSA.IsSplitBy`;
- sampled owner declarations:
  `CSA`,
  `CSA.baseChange`,
  `CSA.IsSplitBy`,
  `IsBrauerEquivalent`;
- best owner abstraction: this theorem is `source-facing`; its core/canonical owner remains the
  base-changed algebra `A.baseChange K`, while Brauer equivalence on representatives is the right
  bridge language for the criterion and its invariance consequences;
- primitive data: a representative `B : CSA k`, the canonical relation `IsBrauerEquivalent A B`,
  a `k`-algebra embedding `K →ₐ[k] B`, and the square-dimension condition
  `Module.finrank k B = Module.finrank k K ^ 2`;
- derived API: Brauer-invariance of `CSA.IsSplitBy`, which should be exposed once at the owner
  level rather than re-derived in downstream files.

Source/core/bridge triage:
- `source-facing`: the splitting criterion itself for `A.IsSplitBy K`;
- `core/canonical`: the base-changed owner `A.baseChange K : CSA K`;
- `bridge/view`: Brauer-equivalence invariance of `IsSplitBy`, derived from the main criterion. -/

universe u v w

namespace CSA

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)
variable (K : Type w) [Field K] [Algebra k K] [FiniteDimensional k K]

-- Proof sketch: for the forward implication, realize the split algebra as `End_K(V)`, take the
-- commutant of `A` in `End_k(V)`, and use the double-centralizer dimension formula to obtain a
-- Brauer-equivalent algebra containing `K` with `k`-dimension `[K : k]^2`. For the reverse
-- implication, use the embedded copy of `K` in `B`, identify `B ⊗[k] K` with the corresponding
-- centralizer in `End_k(B)`, and apply the centralizer criterion from the previous subsection.
/-- Theorem 11.8.2: a finite extension `K/k` splits the finite central simple `k`-algebra `A` if
and only if there exists a finite central simple `k`-algebra `B` Brauer equivalent to `A` that
contains `K` as a `k`-subalgebra and has `k`-dimension `[K : k]^2`. -/
theorem isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq :
    A.IsSplitBy K ↔
      ∃ B : CSA.{u, v} k,
        IsBrauerEquivalent A B ∧
          Nonempty (K →ₐ[k] B) ∧
          Module.finrank k B = Module.finrank k K ^ 2 := sorry

/-- Brauer-equivalent finite central simple algebras have the same finite splitting fields. -/
theorem isSplitBy_iff_of_isBrauerEquivalent {B : CSA.{u, v} k}
    (hAB : IsBrauerEquivalent A B) :
    A.IsSplitBy K ↔ B.IsSplitBy K := by
  constructor
  · intro hA
    rcases (A.isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq K).1 hA with
      ⟨C, hAC, hK, hdim⟩
    refine (B.isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq K).2 ?_
    exact ⟨C, IsBrauerEquivalent.trans (IsBrauerEquivalent.symm hAB) hAC, hK, hdim⟩
  · intro hB
    rcases (B.isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq K).1 hB with
      ⟨C, hBC, hK, hdim⟩
    refine (A.isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq K).2 ?_
    exact ⟨C, IsBrauerEquivalent.trans hAB hBC, hK, hdim⟩

end CSA

/-! ### Lemma_11_8_3 (from Chap11) -/
universe u v

/- Domain-style sampling for Lemma 11.8.3:
- primary domain: maximal subfields as splitting fields of finite central simple algebras;
- sampled owner declarations:
  `CSA.IsSplitBy`,
  `CSA.isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq`,
  `IsMaximalSubfield`,
  `IsMaximalSubfield.finrank_sq`;
- best owner abstraction: `CSA.IsSplitBy` is the core/canonical owner, while `IsMaximalSubfield`
  is the source-facing maximal-subfield hypothesis and this lemma is the bridge from the latter to
  the former;
- primitive data: the maximal subfield `K₀ : Subalgebra k A`, its inclusion `K₀ →ₐ[k] A`, and
  the square-dimension formula from `IsMaximalSubfield.finrank_sq`;
- derived API: the splitting statement for the canonical representative `CSA.mk (AlgCat.of k A)`.

Source/core/bridge triage:
- `source-facing`: this lemma for maximal subfields of a finite central skew field;
- `core/canonical`: `CSA.IsSplitBy`;
- `bridge/view`: the application of Theorem 11.8.2 with the canonical inclusion `K₀ →ₐ[k] A`. -/

section

variable {k : Type u} [Field k]
variable {A : Type v} [DivisionRing A] [Algebra k A] [FiniteDimensional k A]
  [Algebra.IsCentral k A]

-- Proof sketch: apply Theorem 11.8.2 to the central simple algebra underlying `A`, taking
-- `B := A` and the canonical inclusion `K₀ →ₐ[k] A` of the maximal subfield `K₀`. Lemma 11.7.4
-- identifies the finrank hypothesis required by Theorem 11.8.2.
/-- Lemma 11.8.3: if `K₀` is a maximal `k`-subfield of a finite central skew field `A`, then
`K₀` splits the associated finite central simple `k`-algebra. -/
theorem maximal_subfield_splits
    (K₀ : Subalgebra k A) [IsMaximalSubfield K₀] :
    (CSA.mk (AlgCat.of k A)).IsSplitBy K₀ := by
  refine
    ((CSA.mk (AlgCat.of k A)).isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq
      K₀).2 ?_
  refine ⟨CSA.mk (AlgCat.of k A), IsBrauerEquivalent.refl _, ⟨K₀.val⟩, ?_⟩
  simpa using IsMaximalSubfield.finrank_sq K₀

end

/-! ### Lemma_11_8_4 (from Chap11) -/
universe u v w

section

open Matrix

variable {k : Type u} [Field k]
variable {K : Type v} [DivisionRing K] [Algebra k K] [FiniteDimensional k K]
variable [Algebra.IsCentral k K]
variable {k' : Type w} [Field k'] [Algebra k k'] [FiniteDimensional k k']

/- Layer note: this is `source-facing`. The owner abstraction `CSA` remains the right language for
splitness, but Lemma 11.8.4 is about the division-algebra representative itself, not arbitrary
finite central simple algebras. The proof must therefore pass through a Wedderburn decomposition of
the auxiliary `CSA` from Theorem 11.8.2 and the uniqueness of division representatives from
Lemma 11.5.1, rather than treating `CSA.degree` as a Brauer-class invariant. -/
-- Proof sketch: apply Theorem 11.8.2 to `CSA.mk (AlgCat.of k K)` to obtain a Brauer-equivalent
-- finite central simple algebra `B` containing `k'` with `k`-dimension `[k' : k]^2`. Write `B`
-- as a matrix algebra over a finite central division algebra `D` using Wedderburn. Since `B` is
-- Brauer equivalent to `CSA.mk (AlgCat.of k K)`, Lemma 11.5.1 identifies `D` with `K`; comparing
-- dimensions then shows `[k' : k] = n * (CSA.mk (AlgCat.of k K)).degree` for the matrix size `n`,
-- hence the stated divisibility.
/-- Lemma 11.8.4: the degree of the central simple algebra attached to a finite central skew field
`K/k` divides the degree of every finite splitting field. -/
lemma csa_degree_dvd_finrank_of_splitting_field
    (hk' : (CSA.mk (AlgCat.of k K)).IsSplitBy k') :
    (CSA.mk (AlgCat.of k K)).degree ∣ Module.finrank k k' :=
  by
    let A : CSA.{u, v} k := CSA.mk (AlgCat.of k K)
    rcases (A.isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq k').1 hk' with
      ⟨B, hAB, _, hdim⟩
    letI : IsArtinianRing B := IsArtinianRing.of_finite k B
    obtain ⟨n, hn, D, hDdiv, hDalg, hDfin, ⟨e⟩⟩ :=
      IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k B
    letI : DivisionRing D := hDdiv
    letI : Algebra k D := hDalg
    letI : Module.Finite k D := hDfin
    letI : FiniteDimensional k D := inferInstance
    letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) D) := Algebra.IsCentral.of_algEquiv k B _ e
    letI : Algebra.IsCentral k D := by
      refine ⟨fun x hx ↦ ?_⟩
      have hxM : scalar (Fin n) x ∈ (Subalgebra.center k D).map (scalarAlgHom (Fin n) k) := by
        exact ⟨x, hx, rfl⟩
      rw [← subalgebraCenter_eq_scalarAlgHom_map] at hxM
      obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hxM
      rw [Algebra.mem_bot]
      refine ⟨a, ?_⟩
      let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
      simpa [i] using (congrArg (fun M : Matrix (Fin n) (Fin n) D ↦ M i i) ha).symm
    have hBD : IsBrauerEquivalent B (CSA.mk (AlgCat.of k D)) := by
      refine ⟨1, n, one_ne_zero, NeZero.ne n, ?_⟩
      exact ⟨((reindexAlgEquiv k B finOneEquiv).trans uniqueAlgEquiv).trans e⟩
    have hKD : Nonempty (K ≃ₐ[k] D) :=
      (division_algebras_are_similar_iff k K D).1 (IsBrauerEquivalent.trans hAB hBD)
    have hfinD : Module.finrank k D = Module.finrank k K := by
      rcases hKD with ⟨eKD⟩
      simpa using (LinearEquiv.finrank_eq eKD.toLinearEquiv).symm
    have hsq : Module.finrank k k' ^ 2 = (n * A.degree) ^ 2 := by
      calc
        Module.finrank k k' ^ 2 = Module.finrank k B := hdim.symm
        _ = Module.finrank k (Matrix (Fin n) (Fin n) D) := LinearEquiv.finrank_eq e.toLinearEquiv
        _ = n * n * Module.finrank k D := by
          simpa using (Module.finrank_matrix k D (Fin n) (Fin n))
        _ = n * n * A.degree ^ 2 := by rw [hfinD, A.degree_sq_eq_finrank]
        _ = (n * A.degree) ^ 2 := by
          simp [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    refine ⟨n, ?_⟩
    calc
      Module.finrank k k' = Nat.sqrt (Module.finrank k k' ^ 2) := by
        simp [pow_two]
      _ = Nat.sqrt ((n * A.degree) ^ 2) := by rw [hsq]
      _ = n * A.degree := by simp [pow_two]
      _ = A.degree * n := by rw [Nat.mul_comm]

end

/-! ### Proposition_11_8_5 (from Chap11) -/
open scoped TensorProduct

universe u v w

/- Domain-style sampling for Proposition 11.8.5:
- primary domain: separable maximal subfields and finite separable splitting fields for finite
  central simple algebras and their Brauer classes;
- sampled owner declarations:
  `Br`,
  `IsMaximalSubfield`,
  `CSA.IsSplitBy`,
  `CSA.isSplitBy_iff_of_isBrauerEquivalent`,
  `BrauerGroup.IsSplitBy`;
- best owner abstraction: the representative-level splitting notion is canonically owned by
  `CSA.IsSplitBy`, while the source-facing Brauer-class surface in this chapter is `Br(k)`;
  the Brauer-group statement should therefore be a quotient-level bridge on `Br(k)` built from
  the representative owner, rather than a parallel wrapper vocabulary;
- primitive data: a maximal subfield `K : Subalgebra k D` in the division-algebra case, and the
  owner predicate `A.IsSplitBy L` for scalar extensions of a representative `A : CSA k`;
- derived API: the quotient-level bridge `BrauerGroup.IsSplitBy` and the induced existence theorem
  for classes `A : Br(k)`.

Source/core/bridge triage:
- `source-facing`: existence of a separable maximal subfield and existence of a finite separable
  splitting field;
- `core/canonical`: `CSA.IsSplitBy`;
- `bridge/view`: the quotient-level predicate `BrauerGroup.IsSplitBy` and the descent from
  representatives to Brauer classes. -/

section

variable {k : Type u} [Field k]
variable {D : Type v} [DivisionRing D] [Algebra k D] [FiniteDimensional k D]
  [Algebra.IsCentral k D]

-- Proof sketch: among the separable `k`-subfields of `D`, choose one maximal by inclusion. If it
-- were not maximal among commutative `k`-subalgebras, enlarging it would produce an element of `D`
-- separable over `k`, contradicting maximality of the separable subfield.
/-- Proposition 11.8.5 (1): a finite central skew field over `k` contains a maximal subfield that
is separable over `k`. -/
theorem exists_separable_maximal_subfield :
    ∃ K : Subalgebra k D, Algebra.IsSeparable k K ∧ IsMaximalSubfield K := sorry

namespace CSA

variable (A : CSA.{u, v} k)

-- Proof sketch: choose a Brauer-equivalent finite central skew field representing `A`, apply the
-- first part to obtain a separable maximal subfield, and then use Lemma 11.8.3 to see that this
-- maximal subfield splits the division algebra. Brauer equivalence preserves the splitting-field
-- condition, so the same finite separable extension splits `A`.
/-- Proposition 11.8.5 (2), representative form: every finite central simple `k`-algebra is split
by some finite separable extension of `k`. -/
theorem exists_finite_separable_splitting_field :
    ∃ (L : Type w) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L),
      A.IsSplitBy L := sorry

end CSA

namespace BrauerGroup

variable (A : Br(k))
variable (L : Type w) [Field L] [Algebra k L]

/-- A Brauer class is split by `L` if it admits a finite central simple representative split by
`L`. -/
def IsSplitBy : Prop :=
  ∃ B : CSA.{u, max u v} k, (Quotient.mk _ B : Br(k)) = A ∧ B.IsSplitBy L

@[simp] theorem isSplitBy_mk [FiniteDimensional k L] (A : CSA.{u, max u v} k) :
    BrauerGroup.IsSplitBy (Quotient.mk _ A : Br(k)) L ↔ A.IsSplitBy L := by
  constructor
  · rintro ⟨B, hBA, hB⟩
    have hiff : A.IsSplitBy L ↔ B.IsSplitBy L := by
      exact A.isSplitBy_iff_of_isBrauerEquivalent L <| Quotient.exact hBA.symm
    exact hiff.2 hB
  · intro hA
    exact ⟨A, rfl, hA⟩

/- Layer note: Proposition 11.8.5 (2) is `source-facing`, but its owner abstraction is
`BrauerGroup k`; the representative-level `CSA` statement is retained only as a bridge. -/
/-- Proposition 11.8.5 (2): every Brauer class over `k` admits a finite separable splitting
field. -/
theorem exists_finite_separable_splitting_field :
    ∃ (L : Type w) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L), A.IsSplitBy L := by
  refine Quotient.inductionOn A fun B ↦ ?_
  rcases B.exists_finite_separable_splitting_field with ⟨L, _, _, _, _, hL⟩
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨B, rfl, hL⟩⟩

end BrauerGroup

end

/-! ### Lemma_11_8_6 (from Chap11) -/
open scoped TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- Domain-style sampling for Lemma 11.8.6:
- primary domain: finite-dimensional central simple algebras and their splitting criteria;
- sampled owner declarations:
  `CSA.IsSplitBy`,
  `CSA.baseChange`,
  `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`,
  `CSA.finrank_isSquare`;
- best owner abstraction: the numbered TFAE statement is `source-facing` on an arbitrary
  `k`-algebra `A`, while the canonical owner for the splitting clauses is `CSA k`;
- primitive data: for the main TFAE, only the ambient `k`-algebra structure on `A`; for the
  companion statements below, only a representative `A : CSA k`;
- derived API: the algebraic-closure, separable-closure, and finite-Galois splitting statements on
  `CSA`; the degree API belongs upstream with `CSA.finrank_isSquare` rather than in this later
  TFAE file.

Source/core/bridge triage:
- `source-facing`: `finite_central_simple_tfae`;
- `core/canonical`: `CSA k` together with `CSA.IsSplitBy`;
- `bridge/view`: the owner-level companion splitness theorems below, which package the explicit
  matrix-algebra clauses of the TFAE in the canonical `IsSplitBy` language. -/

/-- Lemma 11.8.6: for a `k`-algebra `A`, the following are equivalent: `A` is finite-dimensional,
central, and simple; it has center exactly `k` and only trivial two-sided ideals; it becomes a
matrix algebra after scalar extension to the algebraic closure or to the separable closure; it is
split by a finite Galois extension of `k`; and it is a full matrix algebra over a finite central
division `k`-algebra. -/
theorem finite_central_simple_tfae :
    List.TFAE
      [ FiniteDimensional k A ∧ Algebra.IsCentral k A ∧ IsSimpleRing A,
        FiniteDimensional k A ∧ Subalgebra.center k A = ⊥ ∧
          Nontrivial A ∧ ∀ I : Ideal A, I.IsTwoSided → I = ⊥ ∨ I = ⊤,
        ∃ n : ℕ, n ≠ 0 ∧ Nonempty
          ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
            Matrix (Fin n) (Fin n) (AlgebraicClosure k)),
        ∃ n : ℕ, n ≠ 0 ∧ Nonempty
          ((A ⊗[k] SeparableClosure k) ≃ₐ[SeparableClosure k]
            Matrix (Fin n) (Fin n) (SeparableClosure k)),
        ∃ (k' : Type w) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k')
          (_ : IsGalois k k') (n : ℕ),
          n ≠ 0 ∧ Nonempty ((A ⊗[k] k') ≃ₐ[k'] Matrix (Fin n) (Fin n) k'),
        ∃ (n : ℕ), n ≠ 0 ∧ ∃ (D : Type w) (_ : DivisionRing D) (_ : Algebra k D)
          (_ : FiniteDimensional k D) (_ : Algebra.IsCentral k D),
          Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) D) ] := sorry

end

namespace CSA

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)

/- Layer note: `finite_central_simple_tfae` is the `source-facing` statement for an arbitrary
`k`-algebra. The declarations below move to the `core/canonical` owner abstraction `CSA k` for
representative-level splitness and degree data, rather than keeping parallel ad hoc wrappers. -/

-- Proof sketch: a finite central simple algebra becomes a matrix algebra after scalar extension to
-- an algebraic closure by the splitting criterion.
/-- Companion statement: every finite central simple `k`-algebra splits over `AlgebraicClosure k`.
-/
theorem isSplitBy_algebraicClosure : A.IsSplitBy (AlgebraicClosure k) := sorry

-- Proof sketch: a finite central simple algebra splits over the separable closure because the
-- algebraic-closure splitting descends along Lemma 11.4.5.
/-- Companion statement: every finite central simple `k`-algebra splits over `SeparableClosure k`.
-/
theorem isSplitBy_separableClosure : A.IsSplitBy (SeparableClosure k) := sorry

-- Proof sketch: Proposition 11.8.5 gives a finite separable splitting field, and a finite Galois
-- closure of that field yields the Galois form.
/-- Companion statement: every finite central simple `k`-algebra admits a finite Galois splitting
field. -/
theorem exists_finite_galois_splitting_field :
    ∃ (k' : Type w) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k')
      (_ : IsGalois k k'),
      A.IsSplitBy k' := sorry

end CSA
