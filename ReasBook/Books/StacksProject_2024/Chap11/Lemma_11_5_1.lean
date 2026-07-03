import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Tactic.Recall
import stacks_project.Chap11.Lemma_11_4_6

-- Declarations for this item will be appended below by the statement pipeline.

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
