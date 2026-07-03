import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_11_5_1 (from Chap11) -/
/- Domain-style sampling for Lemma 11.5.1:
- primary domain: Brauer equivalence classes of finite-dimensional central simple algebras, with
  source-facing specialization to finite-dimensional central division `k`-algebras;
- sampled owner declarations:
  `IsBrauerEquivalent`,
  `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`,
  `matrix_simple_module`,
  `matrix_endomorphism_alg_equiv_op`;
- best owner abstraction: the core owner remains `IsBrauerEquivalent` on `CSA k`; this lemma should
  stay a source-facing bridge for division-algebra representatives rather than introducing a new
  wrapper or a second owner;
- primitive data: a division-algebra representative enters only through the canonical owner object
  `CSA.mk (AlgCat.of k K)`, and Wedderburn contributes only the matrix-algebra presentation needed
  to construct such a representative, while the uniqueness bridge is derived from the canonical
  simple-module and endomorphism-algebra owners for matrix algebras;
- derived API: the present file should expose the existence of a division representative and the
  uniqueness criterion identifying equality of Brauer classes for such representatives with
  existence of a `k`-algebra isomorphism.

Source/core/bridge triage:
- `source-facing`: division-algebra representatives of a Brauer class;
- `core/canonical`: `IsBrauerEquivalent` on `CSA k`;
- `bridge/view`: the existence and uniqueness bridges below between arbitrary `CSA` objects and
  their finite central division representatives. -/

/- Companion recall: the owner abstraction for similarity classes of finite-dimensional central
simple `k`-algebras is `CSA k` equipped with the canonical Brauer equivalence relation
`IsBrauerEquivalent`; this relation is an equivalence by `IsBrauerEquivalent.is_eqv`. -/
recall IsBrauerEquivalent.is_eqv

open Matrix
open scoped Matrix.Module

universe u v

section

variable (k : Type u) [Field k]
variable (A : CSA.{u, v} k)
variable (K K' : Type v) [DivisionRing K] [DivisionRing K']
variable [Algebra k K] [Algebra k K']
variable [Algebra.IsCentral k K] [Algebra.IsCentral k K']
variable [FiniteDimensional k K] [FiniteDimensional k K']

private theorem isCentral_of_matrix (n : ℕ) [NeZero n] (D : Type v) [DivisionRing D] [Algebra k D]
    [Algebra.IsCentral k (Matrix (Fin n) (Fin n) D)] : Algebra.IsCentral k D where
  out x hx := by
    have hxM : scalar (Fin n) x ∈ (Subalgebra.center k D).map (scalarAlgHom (Fin n) k) := by
      exact ⟨x, hx, rfl⟩
    rw [← subalgebraCenter_eq_scalarAlgHom_map] at hxM
    obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hxM
    rw [Algebra.mem_bot]
    refine ⟨a, ?_⟩
    let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    simpa [i] using (congrArg (fun M : Matrix (Fin n) (Fin n) D ↦ M i i) ha).symm

/- Layer note: this is a `source-facing` existence bridge. The core/canonical owner notions are
`CSA k` and `IsBrauerEquivalent`; Theorem 11.3.3 supplies the matrix-over-division presentation,
and the matrix-center owner theorem recovers the centrality needed to repackage the division
algebra canonically as an object of `CSA k`. -/
/-- Lemma 11.5.1 (existence): every finite-dimensional central simple `k`-algebra is Brauer
equivalent to one attached to a finite-dimensional central division `k`-algebra. -/
lemma exists_division_algebra_representative :
    ∃ (K : Type v) (_ : DivisionRing K) (_ : Algebra k K) (_ : Algebra.IsCentral k K)
      (_ : FiniteDimensional k K),
      IsBrauerEquivalent A (CSA.mk (AlgCat.of k K)) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn, K, hKdiv, hKalg, hKfin, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  letI : NeZero n := hn
  letI : DivisionRing K := hKdiv
  letI : Algebra k K := hKalg
  letI : Module.Finite k K := hKfin
  letI : FiniteDimensional k K := inferInstance
  letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) K) := Algebra.IsCentral.of_algEquiv k A _ e
  letI : Algebra.IsCentral k K := isCentral_of_matrix k n K
  refine ⟨K, hKdiv, hKalg, inferInstance, inferInstance, ?_⟩
  refine ⟨1, n, one_ne_zero, NeZero.ne n, ?_⟩
  refine ⟨((reindexAlgEquiv k A finOneEquiv).trans uniqueAlgEquiv).trans e⟩

/- Layer note: this is a source-facing bridge. The core/canonical owner notion is
`IsBrauerEquivalent` on `CSA k`, while the source statement is about division-algebra
representatives of a Brauer class. -/
-- Proof sketch: `IsBrauerEquivalent` already records similarity by matrix stabilization, so the
-- owner-level input is an algebra equivalence between matrix algebras over `K` and `K'`. Compare
-- the endomorphism algebras of the transported standard simple modules using
-- `matrix_endomorphism_alg_equiv_op` and the uniqueness of simple modules over a simple Artinian
-- ring from `simple_modules_unique_up_to_linear_equiv`; this recovers `Kᵐᵒᵖ ≃ₐ[k] K'ᵐᵒᵖ`, hence
-- `K ≃ₐ[k] K'`. The converse is the `n = m = 1` case of Brauer equivalence.
/-- Lemma 11.5.1: finite-dimensional central division `k`-algebras determine their Brauer classes
uniquely; equivalently, matrix algebras over them are similar exactly when the underlying
division `k`-algebras are `k`-algebra isomorphic. -/
lemma division_algebras_are_similar_iff :
    IsBrauerEquivalent
      (CSA.mk (AlgCat.of k K))
      (CSA.mk (AlgCat.of k K')) ↔
      Nonempty (K ≃ₐ[k] K') := by
  constructor
  · rintro ⟨n, m, hn0, hm0, h⟩
    change Nonempty (Matrix (Fin n) (Fin n) K ≃ₐ[k] Matrix (Fin m) (Fin m) K') at h
    rcases h with ⟨e⟩
    letI : NeZero n := ⟨hn0⟩
    letI : NeZero m := ⟨hm0⟩
    let hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    let hm : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)
    letI : IsArtinianRing (Matrix (Fin n) (Fin n) K) :=
      IsArtinianRing.of_finite k (Matrix (Fin n) (Fin n) K)
    letI : Module (Matrix (Fin n) (Fin n) K) (Fin m → K') :=
      Module.compHom (Fin m → K') e.toRingHom
    letI : Module k (Fin m → K') := inferInstance
    letI : IsScalarTower k (Matrix (Fin n) (Fin n) K) (Fin m → K') := by
      refine ⟨?_⟩
      intro c a x
      calc
        e (c • a) • x = (c • e a) • x := by
          congr 1
          simpa [Algebra.smul_def] using
            (show e (((algebraMap k (Matrix (Fin n) (Fin n) K)) c) * a) =
                ((algebraMap k (Matrix (Fin m) (Fin m) K')) c) * e a from
              e.map_mul ((algebraMap k (Matrix (Fin n) (Fin n) K)) c) a)
        _ = c • (e a • x) := smul_assoc c (e a) x
    letI : IsSimpleModule (Matrix (Fin n) (Fin n) K) (Fin n → K) := matrix_simple_module hn
    letI : IsSimpleModule (Matrix (Fin m) (Fin m) K') (Fin m → K') := matrix_simple_module hm
    letI : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
    let compLinearMap : (Fin m → K') →ₛₗ[e.toRingHom] (Fin m → K') :=
      { toFun := id
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    letI : IsSimpleModule (Matrix (Fin n) (Fin n) K) (Fin m → K') :=
      (LinearMap.isSimpleModule_iff_of_bijective compLinearMap (Function.bijective_id)).2 inferInstance
    let l : (Fin n → K) ≃ₗ[Matrix (Fin n) (Fin n) K] (Fin m → K') :=
      simple_modules_unique_up_to_linear_equiv.some
    let eK : Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) ≃ₐ[k] Kᵐᵒᵖ :=
      matrix_endomorphism_alg_equiv_op hn
    let eComp :
        Module.End (Matrix (Fin n) (Fin n) K) (Fin m → K') ≃ₐ[k]
          Module.End (Matrix (Fin m) (Fin m) K') (Fin m → K') := by
      letI : Module (Matrix (Fin n) (Fin n) K) (Fin m → K') := Module.compHom (Fin m → K') e.toRingHom
      refine
        { toFun := fun f ↦
            { toFun := f
              map_add' := f.map_add
              map_smul' := by
                intro b x
                obtain ⟨a, rfl⟩ := e.surjective b
                exact f.map_smul a x }
          invFun := fun f ↦
            { toFun := f
              map_add' := f.map_add
              map_smul' := by
                intro a x
                exact f.map_smul (e a) x }
          left_inv := by intro f; rfl
          right_inv := by intro f; rfl
          map_mul' := by intro f g; rfl
          map_add' := by intro f g; rfl
          commutes' := by
            intro c
            ext x
            simp [Algebra.algebraMap_eq_smul_one] }
    let eK' : Module.End (Matrix (Fin n) (Fin n) K) (Fin m → K') ≃ₐ[k] K'ᵐᵒᵖ :=
      eComp.trans (matrix_endomorphism_alg_equiv_op hm)
    let hop : Kᵐᵒᵖ ≃ₐ[k] K'ᵐᵒᵖ := eK.symm.trans ((l.conjAlgEquiv k).trans eK')
    exact ⟨AlgEquiv.unop hop⟩
  · rintro ⟨e⟩
    refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
    change Nonempty (Matrix (Fin 1) (Fin 1) K ≃ₐ[k] Matrix (Fin 1) (Fin 1) K')
    exact ⟨(((reindexAlgEquiv k K finOneEquiv).trans uniqueAlgEquiv).trans e).trans
      ((reindexAlgEquiv k K' finOneEquiv).trans uniqueAlgEquiv).symm⟩

end

/-! ### Definition_11_5_2 (from Chap11) -/
noncomputable section

universe u v

/- Domain-style sampling for Definition 11.5.2:
- primary domain: Brauer equivalence classes of finite-dimensional central simple algebras over a
  field, with tensor product and opposite algebra as the source-facing group operations;
- sampled owner declarations:
  `CSA`,
  `IsBrauerEquivalent`,
  `BrauerGroup`,
  `Br`,
  `CSA.tensorProduct`,
  `Aᵐᵒᵖ`;
- best owner abstraction: the core/canonical owner remains the quotient `BrauerGroup k`, and the
  source-facing owner notation is `Br(k) := BrauerGroup.{u, max u v} k`, which removes the
  auxiliary size hypothesis from the public group interface while keeping the same quotient owner;
- primitive data: the quotient owner `BrauerGroup k`, the representative-level tensor product
  `CSA.tensorProduct`, the opposite-algebra representative `Aᵐᵒᵖ`, and the canonical `ULift`
  representative of the neutral Brauer class;
- derived API: the quotient-level `1`, `*`, and `⁻¹` on `Br(k)`, together with the resulting
  `CommGroup` structure and the quotient computation lemmas below.

Source/core/bridge triage:
- `source-facing`: the Brauer group `Br(k)` with multiplication induced by tensor product and
  inverse induced by the opposite algebra;
- `core/canonical`: the quotient owner `BrauerGroup k`;
- `bridge/view`: the representative-level `CSA` constructions below (`unit`, `opposite`) and
  the Brauer-equivalence compatibility theorems that descend them to the quotient. -/

/-- Textbook surface notation for the Brauer group of `k`, realized on the canonical quotient
universe `max u v` so the base field itself has a size-independent neutral representative. -/
abbrev Br (k : Type u) [Field k] := BrauerGroup.{u, max u v} k

notation "Br(" k ")" => Br k

namespace CSA

variable {k : Type u} [Field k]

/-- The opposite algebra of a finite-dimensional central simple `k`-algebra, repackaged as the
canonical corresponding object of `CSA k`. -/
def opposite (A : CSA.{u, v} k) : CSA.{u, v} k where
  toAlgCat := AlgCat.of k Aᵐᵒᵖ

variable (k : Type u) [Field k]

/-- The canonical `ULift` representative of the neutral Brauer class in carrier universe
`max u v`. -/
def unit : CSA.{u, max u v} k where
  toAlgCat := AlgCat.of k (ULift.{v, u} k)
  isCentral := by
    refine ⟨fun x _ ↦ ?_⟩
    exact ⟨x.down, rfl⟩
  isSimple := inferInstance
  fin_dim := by
    simpa using
      (ULift.algEquiv : ULift.{v, u} k ≃ₐ[k] k).symm.toLinearEquiv.finiteDimensional

variable {k}

/-- Brauer equivalence is compatible with passage to opposite algebras. -/
theorem brauerEquivalent_opposite {A B : CSA.{u, v} k} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent A.opposite B.opposite := by
  sorry

/-- Brauer equivalence is compatible with tensor product on representatives. -/
theorem brauerEquivalent_tensorProduct {A A' B B' : CSA.{u, v} k}
    (hAA' : IsBrauerEquivalent A A') (hBB' : IsBrauerEquivalent B B') :
    IsBrauerEquivalent (A.tensorProduct B) (A'.tensorProduct B') := by
  sorry

/-- Tensor product on representatives induces the associative law in the Brauer group. -/
theorem brauerEquivalent_tensorProduct_assoc (A B C : CSA.{u, v} k) :
    IsBrauerEquivalent ((A.tensorProduct B).tensorProduct C) (A.tensorProduct (B.tensorProduct C)) :=
  by
  sorry

/-- Tensor product on representatives induces the commutative law in the Brauer group. -/
theorem brauerEquivalent_tensorProduct_comm (A B : CSA.{u, v} k) :
    IsBrauerEquivalent (A.tensorProduct B) (B.tensorProduct A) := by
  sorry

/-- Tensoring with the canonical neutral representative leaves a Brauer class unchanged. -/
theorem brauerEquivalent_tensorProduct_unit (A : CSA.{u, max u v} k) :
    IsBrauerEquivalent (A.tensorProduct (unit k)) A := by
  sorry

/-- The canonical neutral representative is a left unit for tensor product on Brauer classes. -/
theorem brauerEquivalent_unit_tensorProduct (A : CSA.{u, max u v} k) :
    IsBrauerEquivalent ((unit k).tensorProduct A) A := by
  sorry

/-- The opposite algebra represents the inverse Brauer class. -/
theorem brauerEquivalent_tensorProduct_opposite (A : CSA.{u, max u v} k) :
    IsBrauerEquivalent (A.tensorProduct A.opposite) (unit k) := by
  sorry

end CSA

namespace BrauerGroup

variable {k : Type u} [Field k]

/-- Definition 11.5.2: the Brauer group `Br(k)` of `k` is the quotient `BrauerGroup k` of finite
central simple `k`-algebras by Brauer equivalence, endowed with multiplication induced by tensor
product and inverse induced by the opposite algebra. -/
noncomputable instance : One (Br(k)) :=
  ⟨Quotient.mk _ (CSA.unit k)⟩

/-- Multiplication in the Brauer group is induced by tensor product of representatives. -/
noncomputable instance : Mul (Br(k)) :=
  ⟨Quotient.map₂ CSA.tensorProduct
      fun {_ _} h₁ {_ _} h₂ ↦ CSA.brauerEquivalent_tensorProduct h₁ h₂⟩

/-- Inversion in the Brauer group is induced by passage to the opposite algebra. -/
noncomputable instance : Inv (Br(k)) :=
  ⟨Quotient.map CSA.opposite fun _ _ h ↦ CSA.brauerEquivalent_opposite h⟩

/-- The source-facing owner `Br(k)` carries the canonical commutative-group structure described in
Definition 11.5.2. -/
noncomputable instance : CommGroup (Br(k)) where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  mul_assoc a b c := by
    refine Quotient.inductionOn₃ a b c fun A B C ↦ ?_
    exact Quotient.sound (CSA.brauerEquivalent_tensorProduct_assoc A B C)
  one_mul a := by
    refine Quotient.inductionOn a fun A ↦ ?_
    exact Quotient.sound (CSA.brauerEquivalent_unit_tensorProduct A)
  mul_one a := by
    refine Quotient.inductionOn a fun A ↦ ?_
    exact Quotient.sound (CSA.brauerEquivalent_tensorProduct_unit A)
  inv_mul_cancel a := by
    refine Quotient.inductionOn a fun A ↦ ?_
    exact Quotient.sound <|
      IsBrauerEquivalent.trans (CSA.brauerEquivalent_tensorProduct_comm A.opposite A)
        (CSA.brauerEquivalent_tensorProduct_opposite A)
  mul_comm a b := by
    refine Quotient.inductionOn₂ a b fun A B ↦ ?_
    exact Quotient.sound (CSA.brauerEquivalent_tensorProduct_comm A B)

@[simp] theorem one_def :
    (1 : Br(k)) = Quotient.mk _ (CSA.unit k) :=
  rfl

@[simp] theorem mk_mul_mk (A B : CSA.{u, max u v} k) :
    (Quotient.mk _ A : Br(k)) * Quotient.mk _ B =
      Quotient.mk _ (A.tensorProduct B) :=
  rfl

@[simp] theorem mk_inv (A : CSA.{u, max u v} k) :
    (Quotient.mk _ A : Br(k))⁻¹ = Quotient.mk _ A.opposite :=
  rfl

end BrauerGroup

/-! ### Lemma_11_5_3 (from Chap11) -/
noncomputable section

universe u v

/- Domain-style sampling for Lemma 11.5.3:
- primary domain: Brauer equivalence classes of finite-dimensional central simple algebras over an
  algebraically closed field;
- sampled owner declarations:
  `CSA.brauerEquivalent_baseField`,
  `CSA.unit`,
  `BrauerGroup.one_def`,
  `Br`,
  `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`,
  `ULift.algEquiv`;
- best owner abstraction: the source-facing quotient-level statement belongs on the public owner
  `Br(k)`, using the canonical neutral class from `Definition_11_5_2`; the representative-level
  bridge is `CSA.brauerEquivalent_unit`;
- primitive data: a representative `A : CSA k`, the owner relation `IsBrauerEquivalent`, and the
  canonical neutral representative `CSA.unit`;
- derived API: the explicit quotient theorem `BrauerGroup.eq_one_of_isAlgClosed`, together with
  the quotient-level subsingleton instance obtained from that theorem.

Source/core/bridge triage:
- `source-facing`: every Brauer class over an algebraically closed field equals the unit class;
- `core/canonical`: `BrauerGroup k`, presented on the public surface as `Br(k)`;
- `bridge/view`: `CSA.brauerEquivalent_unit`, obtained from the source-facing base-field bridge
  plus the canonical comparison from `k` to `CSA.unit k`. -/

open Matrix

namespace CSA

section

variable (k : Type u) [Field k] [IsAlgClosed k]

private theorem brauerEquivalent_baseField_small (A : CSA.{u, u} k) :
    IsBrauerEquivalent A (CSA.mk (AlgCat.of k k)) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed k A
  refine ⟨1, n, one_ne_zero, hn.ne, ?_⟩
  exact ⟨((reindexAlgEquiv k A finOneEquiv).trans uniqueAlgEquiv).trans e⟩

omit [IsAlgClosed k] in
private theorem smallCarrierOfCSA (A : CSA.{u, v} k) : Small.{u} (↑A.toAlgCat) :=
  Small.mk' (Module.finBasis k A).equivFun.toEquiv

omit [IsAlgClosed k] in
private def shrinkCSA (A : CSA.{u, v} k) : CSA.{u, u} k :=
  letI := smallCarrierOfCSA k A
  { toAlgCat := AlgCat.of k (Shrink.{u} (↑A.toAlgCat))
    isCentral := by
      let e : Shrink.{u} (↑A.toAlgCat) ≃ₐ[k] ↑A.toAlgCat := Shrink.algEquiv k (↑A.toAlgCat)
      refine ⟨fun x hx ↦ ?_⟩
      have hx' : e x ∈ Subalgebra.center k (↑A.toAlgCat) := by
        rw [Subalgebra.mem_center_iff] at hx ⊢
        intro b
        have hcomm : e.symm b * x = x * e.symm b := hx (e.symm b)
        exact by simpa using congrArg e hcomm
      obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hx'
      rw [Algebra.mem_bot]
      refine ⟨a, ?_⟩
      have hxe : e x = e (algebraMap k (Shrink.{u} (↑A.toAlgCat)) a) := by
        simpa using ha
      exact e.injective hxe.symm
    isSimple := IsSimpleRing.of_ringEquiv (Shrink.ringEquiv (↑A.toAlgCat)).symm inferInstance
    fin_dim := (Shrink.algEquiv k (↑A.toAlgCat)).symm.toLinearEquiv.finiteDimensional }

omit [IsAlgClosed k] in
private def shrinkAlgEquiv (A : CSA.{u, v} k) : shrinkCSA k A ≃ₐ[k] A :=
  letI := smallCarrierOfCSA k A
  Shrink.algEquiv k (↑A.toAlgCat)

omit [IsAlgClosed k] in
private theorem brauerEquivalent_shrink (A : CSA.{u, v} k) :
    IsBrauerEquivalent A (shrinkCSA k A) := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  exact ⟨((reindexAlgEquiv k A finOneEquiv).trans uniqueAlgEquiv).trans <|
    (shrinkAlgEquiv k A).symm.trans <|
      ((reindexAlgEquiv k (shrinkCSA k A) finOneEquiv).trans uniqueAlgEquiv).symm⟩

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Lemma 11.5.3, representative-level bridge: over an algebraically closed field, every
finite-dimensional central simple `k`-algebra is Brauer equivalent to the base field. -/
theorem brauerEquivalent_baseField (A : CSA.{u, v} k) :
    IsBrauerEquivalent A (CSA.mk (AlgCat.of k k)) := by
  exact IsBrauerEquivalent.trans (brauerEquivalent_shrink k A)
    (brauerEquivalent_baseField_small k (shrinkCSA k A))

private theorem brauerEquivalent_baseField_unit (k : Type u) [Field k] :
    IsBrauerEquivalent (CSA.mk (AlgCat.of k k)) (CSA.unit k) := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  exact ⟨((reindexAlgEquiv k (CSA.mk (AlgCat.of k k)) finOneEquiv).trans uniqueAlgEquiv).trans <|
    (ULift.algEquiv : ↑(CSA.unit k).toAlgCat ≃ₐ[k] k).symm.trans <|
      ((reindexAlgEquiv k (CSA.unit k) finOneEquiv).trans uniqueAlgEquiv).symm⟩

/-- Companion bridge: over an algebraically closed field, every finite-dimensional central simple
`k`-algebra is Brauer equivalent to the canonical neutral representative `CSA.unit k`. -/
theorem brauerEquivalent_unit (A : CSA.{u, max u v} k) :
    IsBrauerEquivalent A (CSA.unit k) := by
  exact IsBrauerEquivalent.trans A.brauerEquivalent_baseField (brauerEquivalent_baseField_unit k)

end

end CSA

namespace BrauerGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Lemma 11.5.3: if `k` is algebraically closed, then every Brauer class over `k` is the unit
class. -/
theorem eq_one_of_isAlgClosed (A : Br(k)) : A = 1 := by
  refine Quotient.inductionOn A fun A ↦ ?_
  rw [one_def]
  exact Quotient.sound A.brauerEquivalent_unit

instance subsingleton_of_isAlgClosed : Subsingleton (Br(k)) := by
  refine ⟨fun A B ↦ ?_⟩
  rw [A.eq_one_of_isAlgClosed, B.eq_one_of_isAlgClosed]

end BrauerGroup

/-! ### Lemma_11_5_4 (from Chap11) -/
open scoped TensorProduct

universe u v

namespace CSA

section

variable {k : Type u} [Field k]

/- Domain-style sampling for Lemma 11.5.4:
- primary domain: finite-dimensional central simple algebras and their matrix-algebra
  presentations after scalar extension to an algebraically closed field;
- sampled owner declarations:
  `CSA`,
  `CSA.baseChange`,
  `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`,
  `Module.finrank_baseChange`;
- best owner abstraction: the relevant owner object is the base-changed central simple algebra
  `A.baseChange K : CSA K`; the square-dimension statement is derived API on the source-facing owner
  `A : CSA k`, not new primitive data;
- primitive data: a finite central simple algebra `A : CSA k`;
- derived API: the scalar-extension matrix presentation over `AlgebraicClosure k`, the resulting
  square formula for `Module.finrank k A`, and the canonical degree `A.degree` defined as the
  square root of that dimension.

Source/core/bridge triage:
- `source-facing`: the textbook statement that the degree `[A : k]` is a square for a finite
  central simple `k`-algebra;
- `core/canonical`: the owner objects `A : CSA k` and `A.baseChange K : CSA K`;
- `bridge/view`: the passage to `AlgebraicClosure k` and the matrix-algebra presentation given by
  `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`. -/

/-- Lemma 11.5.4: the `k`-dimension of a finite central simple algebra is a square natural number.
-/
-- Proof sketch: after extending scalars to an algebraic closure of `k`, apply Lemma 11.5.3 to
-- identify the algebra with a matrix algebra and compute its dimension as `n ^ 2`.
theorem finrank_isSquare (A : CSA.{u, v} k) : IsSquare (Module.finrank k A) := by
  let K := AlgebraicClosure k
  obtain ⟨n, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K (A.baseChange K)
  have hbase : Module.finrank K (A.baseChange K) = Module.finrank k A := by
    change Module.finrank K (K ⊗[k] A) = Module.finrank k A
    exact Module.finrank_baseChange
  refine ⟨n, ?_⟩
  calc
    Module.finrank k A = Module.finrank K (A.baseChange K) := hbase.symm
    _ = Module.finrank K (Matrix (Fin n) (Fin n) K) := e.toLinearEquiv.finrank_eq
    _ = n * n := by
      simpa using (Module.finrank_matrix K K (Fin n) (Fin n))

/-- The degree of a finite central simple algebra is the square root of its dimension over the
base field. -/
noncomputable def degree (A : CSA.{u, v} k) : ℕ :=
  Nat.sqrt (Module.finrank k A)

-- Proof sketch: by Lemma 11.5.4 the dimension of `A` is a square, so `Nat.sqrt` recovers the
-- unique positive integer whose square is `Module.finrank k A`.
/-- The square of the degree of a finite central simple algebra is its dimension over the base
field. -/
theorem degree_sq_eq_finrank (A : CSA.{u, v} k) :
    A.degree ^ 2 = Module.finrank k A := by
  rcases A.finrank_isSquare with ⟨n, hn⟩
  rw [degree, hn, Nat.sqrt_eq, pow_two]

end

end CSA
