import Mathlib
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.LinearAlgebra.Matrix.ToLin
import stacks_proof.stacks_project.Chap11.Definition_11_8_1
import stacks_proof.stacks_project.Chap11.Lemma_11_4_8
import stacks_proof.stacks_project.Chap11.Lemma_11_4_10
import stacks_proof.stacks_project.Chap11.Lemma_11_5_1
import stacks_proof.stacks_project.Chap11.Lemma_11_7_2
import stacks_proof.stacks_project.Chap11.Lemma_11_7_3
import stacks_proof.stacks_project.Chap11.Definition_11_5_2
import stacks_proof.stacks_project.Chap11.Theorem_11_8_2.BaseChangeMatrix
import stacks_proof.stacks_project.Chap11.Theorem_11_8_2.SplitByBrauer

-- Declarations for this item will be appended below by the statement pipeline.

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

universe u v w z

namespace CSA

open scoped TensorProduct
open Algebra.TensorProduct
open Matrix

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)
variable (K : Type w) [Field K] [Algebra k K] [FiniteDimensional k K]

/-- Helper for Theorem 11.8.2: centrality of a matrix algebra forces centrality of its division
coefficients. -/
private theorem matrix_central_implies_division_central (k : Type u) [Field k] (n : ℕ)
    [NeZero n] (D : Type v) [DivisionRing D] [Algebra k D]
    [Algebra.IsCentral k (Matrix (Fin n) (Fin n) D)] :
    Algebra.IsCentral k D := by
  -- Move a central scalar matrix back to one of its diagonal entries in the coefficient ring.
  refine ⟨fun x hx ↦ ?_⟩
  have hxM : scalar (Fin n) x ∈ (Subalgebra.center k D).map (scalarAlgHom (Fin n) k) := by
    exact ⟨x, hx, rfl⟩
  rw [← subalgebraCenter_eq_scalarAlgHom_map] at hxM
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hxM
  rw [Algebra.mem_bot]
  refine ⟨a, ?_⟩
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  simpa [i] using (congrArg (fun M : Matrix (Fin n) (Fin n) D ↦ M i i) ha).symm

/-- Helper for Theorem 11.8.2: a matrix model over a central division algebra packages the
corresponding Brauer-equivalence witness. -/
private theorem matrix_model_isBrauerEquivalent_division
    {B : CSA.{u, v} k} {n : ℕ} [NeZero n] {D : Type v}
    [DivisionRing D] [Algebra k D] [FiniteDimensional k D] [Algebra.IsCentral k D]
    (e : B ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    IsBrauerEquivalent B (CSA.mk (AlgCat.of k D)) := by
  -- Package the direct matrix presentation as the `1 × 1` stabilization witness.
  refine ⟨1, n, one_ne_zero, NeZero.ne n, ?_⟩
  exact ⟨((Matrix.reindexAlgEquiv k B finOneEquiv).trans uniqueAlgEquiv).trans e⟩

/-- Helper for Theorem 11.8.2: a coefficient algebra equivalence induces the corresponding matrix
algebra equivalence by entrywise transport. -/
private noncomputable def matrix_coeffAlgEquiv
    {k : Type u} [Field k] (n : ℕ) {R : Type v} {S : Type z} [Semiring R] [Semiring S]
    [Algebra k R] [Algebra k S] (e : R ≃ₐ[k] S) :
    Matrix (Fin n) (Fin n) R ≃ₐ[k] Matrix (Fin n) (Fin n) S := by
  -- The entrywise matrix map is an algebra hom, and the inverse coefficient map gives
  -- bijectivity.
  refine AlgEquiv.ofBijective (e.toAlgHom.mapMatrix) ?_
  constructor
  · intro M N hMN
    ext i j
    exact e.injective <| by simpa using congrArg (fun X ↦ X i j) hMN
  · intro M
    refine ⟨e.symm.toAlgHom.mapMatrix M, ?_⟩
    ext i j
    simp

/-- Helper for Theorem 11.8.2: restriction of scalars turns `K`-linear endomorphisms of the
standard split module into `k`-linear endomorphisms without changing the underlying maps. -/
private noncomputable def moduleEndRestrictScalarsAlgHom {n : Type*} [Fintype n] [DecidableEq n] :
    Module.End K (n → K) →ₐ[k] Module.End k (n → K) where
  toFun f := f.restrictScalars k
  map_zero' := rfl
  map_one' := by
    -- The identity endomorphism is unchanged by restriction of scalars.
    ext x
    rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' c := by
    -- Scalar endomorphisms still act pointwise after forgetting from `K`-linearity to `k`-linearity.
    ext x i
    rfl

omit [FiniteDimensional k K] in
/-- Helper for Theorem 11.8.2: the restriction-of-scalars map on endomorphism algebras is
injective on the standard split module. -/
private theorem restrictEndInjective {n : Type*} [Fintype n] [DecidableEq n] :
    Function.Injective (moduleEndRestrictScalarsAlgHom (k := k) (K := K) :
      Module.End K (n → K) →ₐ[k] Module.End k (n → K)) := by
  intro f g hfg
  -- Two `K`-linear endomorphisms are equal once their underlying `k`-linear maps agree on every
  -- vector.
  apply LinearMap.ext
  intro v
  exact congrArg (fun h : Module.End k (n → K) ↦ h v) hfg

omit [FiniteDimensional k K] in
/-- Helper for Theorem 11.8.2: the restriction of a `K`-linear endomorphism still commutes with
the scalar action of `K` after forgetting to `k`-linearity. -/
private theorem restrictEndCommutesScalars {n : Type*} [Fintype n] [DecidableEq n]
    (f : Module.End K (n → K)) (x : K) :
    Commute (moduleEndRestrictScalarsAlgHom (k := k) (K := K) f)
      (Algebra.lsmul k k (n → K) x) := by
  -- Both composites act pointwise by `f (x • v)` and `x • f v`, and `f` is `K`-linear.
  change
    moduleEndRestrictScalarsAlgHom (k := k) (K := K) f * Algebra.lsmul k k (n → K) x =
      Algebra.lsmul k k (n → K) x * moduleEndRestrictScalarsAlgHom (k := k) (K := K) f
  ext v i
  simp [moduleEndRestrictScalarsAlgHom, Algebra.lsmul_coe, map_smul]

/-- Helper for Theorem 11.8.2: the split matrix model defines the `k`-algebra action of `A` on
the standard `K`-vector space `Fin n → K`. -/
private noncomputable def splitModelAction {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    A →ₐ[k] Module.End k (Fin n → K) := by
  let eEnd : A.baseChange K ≃ₐ[K] Module.End K (Fin n → K) :=
    e.trans (algEquivMatrix (Pi.basisFun K (Fin n))).symm
  letI : Algebra k ↑(A.baseChange K).toAlgCat := by
    change Algebra k (K ⊗[k] A)
    infer_instance
  letI : IsScalarTower k K ↑(A.baseChange K).toAlgCat := by
    change IsScalarTower k K (K ⊗[k] A)
    infer_instance
  let includeA : A →ₐ[k] A.baseChange K := Algebra.TensorProduct.includeRight
  let eEndk : A.baseChange K →ₐ[k] Module.End K (Fin n → K) := eEnd.toAlgHom.restrictScalars k
  let rhoK : A →ₐ[k] Module.End K (Fin n → K) := eEndk.comp includeA
  -- Route correction: fix one `K`-linear spelling of the split model and then forget scalars only
  -- once at the end.
  exact (moduleEndRestrictScalarsAlgHom (k := k) (K := K)).comp rhoK

omit [FiniteDimensional k K] in
/-- Helper for Theorem 11.8.2: the split-model action is faithful because it factors through the
injective base-change inclusion and the chosen matrix/endomorphism equivalence. -/
private theorem splitModelAction_injective {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Function.Injective (splitModelAction (A := A) (K := K) e) := by
  let eEnd : A.baseChange K ≃ₐ[K] Module.End K (Fin n → K) :=
    e.trans (algEquivMatrix (Pi.basisFun K (Fin n))).symm
  letI : Algebra k ↑(A.baseChange K).toAlgCat := by
    change Algebra k (K ⊗[k] A)
    infer_instance
  letI : IsScalarTower k K ↑(A.baseChange K).toAlgCat := by
    change IsScalarTower k K (K ⊗[k] A)
    infer_instance
  let includeA : A →ₐ[k] A.baseChange K := Algebra.TensorProduct.includeRight
  let eEndk : A.baseChange K →ₐ[k] Module.End K (Fin n → K) := eEnd.toAlgHom.restrictScalars k
  let rhoK : A →ₐ[k] Module.End K (Fin n → K) := eEndk.comp includeA
  intro a b hab
  -- Peel off the restriction-of-scalars map, the split model, and finally the base-change
  -- inclusion.
  apply includeA.injective
  apply eEnd.injective
  apply restrictEndInjective (k := k) (K := K)
  simpa [splitModelAction, eEnd, includeA, eEndk, rhoK] using hab

/-- Helper for Theorem 11.8.2: the image of the split-model action is the canonical simple
subalgebra used in the commutant construction. -/
private noncomputable def splitModelRange {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Subalgebra k (Module.End k (Fin n → K)) :=
  (splitModelAction (A := A) (K := K) e).range

/-- Helper for Theorem 11.8.2: the textbook commutant is the centralizer of the split-model range
inside `End_k(Fin n → K)`. -/
private noncomputable def splitModelCentralizer {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Subalgebra k (Module.End k (Fin n → K)) :=
  Subalgebra.centralizer k
    (splitModelRange (A := A) (K := K) e : Set (Module.End k (Fin n → K)))

/-- Helper for Theorem 11.8.2: the split-model action identifies `A` with its image subalgebra in
`End_k(Fin n → K)`. -/
private noncomputable def splitModelRangeAlgEquiv {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    A ≃ₐ[k] splitModelRange (A := A) (K := K) e := by
  -- Package the range as a bundled codomain so the image becomes a genuine algebra equivalence.
  refine AlgEquiv.ofBijective (splitModelAction (A := A) (K := K) e).rangeRestrict ?_
  constructor
  · intro a b hab
    exact splitModelAction_injective (A := A) (K := K) e (Subtype.ext_iff.mp hab)
  · exact AlgHom.rangeRestrict_surjective _

omit [FiniteDimensional k K] in
/-- Helper for Theorem 11.8.2: any `k`-algebra map out of the commutative field `K` has
pairwise-commuting image. -/
private theorem algHomFromFieldCommutes {B : Type z} [Semiring B] [Algebra k B]
    (f : K →ₐ[k] B) (x y : K) :
    Commute (f x) (f y) := by
  -- Commutativity is inherited from the source field through multiplicativity of `f`.
  change f x * f y = f y * f x
  simpa [map_mul] using congrArg f (mul_comm x y)

/-- Helper for Theorem 11.8.2: any finite-dimensional `k`-algebra can be shrunk to the witness
universe `v` without changing its algebra structure up to equivalence. -/
private theorem smallCarrierOfFiniteDimensional (A : CSA.{u, v} k) (B : Type z)
    [Ring B] [Algebra k B]
    [FiniteDimensional k B] :
    Small.{v} B := by
  -- Route correction: first shrink the base field into universe `v` through the injective
  -- algebra map `k → A`, then use a finite `k`-basis of `B` to realize `B` as a finite function
  -- space over that small field.
  letI : Small.{v} k := small_of_injective (f := algebraMap k A) (algebraMap k A).injective
  let b := Module.finBasis k B
  refine small_of_injective (f := fun x i ↦ equivShrink k (b.repr x i)) ?_
  intro x y hxy
  apply b.repr.injective
  ext i
  exact (equivShrink k).injective (congrFun hxy i)

/-- Helper for Theorem 11.8.2: shrinking a finite-dimensional central algebra preserves
centrality. -/
private theorem shrinkFiniteDimensionalIsCentral (A : CSA.{u, v} k) (B : Type z) [Ring B]
    [Algebra k B] [FiniteDimensional k B] [Algebra.IsCentral k B] :
    letI := smallCarrierOfFiniteDimensional (A := A) (k := k) B
    Algebra.IsCentral k (Shrink.{v} B) := by
  letI := smallCarrierOfFiniteDimensional (A := A) (k := k) B
  let e : Shrink.{v} B ≃ₐ[k] B := Shrink.algEquiv k B
  -- Pull a central element of the shrunk algebra back to `B`, use centrality there, and then
  -- transport the scalar description forward again.
  refine ⟨fun x hx ↦ ?_⟩
  have hx' : e x ∈ Subalgebra.center k B := by
    rw [Subalgebra.mem_center_iff] at hx ⊢
    intro b
    have hcomm : e.symm b * x = x * e.symm b := hx (e.symm b)
    exact by simpa using congrArg e hcomm
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hx'
  rw [Algebra.mem_bot]
  refine ⟨a, ?_⟩
  have hxe : e x = e (algebraMap k (Shrink.{v} B) a) := by
    simpa using ha
  exact e.injective hxe.symm

/-- Helper for Theorem 11.8.2: a finite central simple algebra can be repackaged on a carrier in
universe `v` by shrinking its underlying type. -/
private noncomputable def shrinkFiniteCentralSimple (B : Type z) [Ring B] [Algebra k B]
    [FiniteDimensional k B] [Algebra.IsCentral k B] [IsSimpleRing B] :
    CSA.{u, v} k :=
  letI := smallCarrierOfFiniteDimensional (A := A) (k := k) B
  -- Repackage the same algebra on the shrunk carrier and transport the structure fields through
  -- the tautological `Shrink` equivalence.
  { toAlgCat := AlgCat.of k (Shrink.{v} B)
    isCentral := shrinkFiniteDimensionalIsCentral (A := A) (k := k) B
    isSimple := IsSimpleRing.of_ringEquiv (Shrink.ringEquiv B).symm inferInstance
    fin_dim := (Shrink.algEquiv k B).symm.toLinearEquiv.finiteDimensional }

/-- Helper for Theorem 11.8.2: the shrink construction comes with the tautological algebra
equivalence back to the original carrier. -/
private noncomputable def shrinkFiniteCentralSimpleAlgEquiv (B : Type z) [Ring B] [Algebra k B]
    [FiniteDimensional k B] [Algebra.IsCentral k B] [IsSimpleRing B] :
    shrinkFiniteCentralSimple (A := A) (k := k) B ≃ₐ[k] B :=
  letI := smallCarrierOfFiniteDimensional (A := A) (k := k) B
  -- The shrunk witness is definitionally the same algebra carried by `Shrink B`.
  Shrink.algEquiv k B

/-- Helper for Theorem 11.8.2: the base field repackaged on the witness universe `v`. -/
private noncomputable def baseFieldRepresentative : CSA.{u, v} k :=
  shrinkFiniteCentralSimple (A := A) (k := k) k

/-- Helper for Theorem 11.8.2: the shrunk base-field representative is canonically equivalent to
`k`. -/
private noncomputable def baseFieldRepresentativeAlgEquiv :
    baseFieldRepresentative (A := A) (k := k) ≃ₐ[k] k :=
  shrinkFiniteCentralSimpleAlgEquiv (A := A) (k := k) k

omit [FiniteDimensional k K] in
/-- Helper for Theorem 11.8.2: the split-model range commutes with scalar endomorphisms coming
from the `K`-action on `Fin n → K`. -/
private theorem splitModelActionCommutesScalars {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) (a : A) (x : K) :
    Commute (splitModelAction (A := A) (K := K) e a)
      (Algebra.lsmul k k (Fin n → K) x) := by
  let eEnd : A.baseChange K ≃ₐ[K] Module.End K (Fin n → K) :=
    e.trans (algEquivMatrix (Pi.basisFun K (Fin n))).symm
  letI : Algebra k ↑(A.baseChange K).toAlgCat := by
    change Algebra k (K ⊗[k] A)
    infer_instance
  letI : IsScalarTower k K ↑(A.baseChange K).toAlgCat := by
    change IsScalarTower k K (K ⊗[k] A)
    infer_instance
  let includeA : A →ₐ[k] A.baseChange K := Algebra.TensorProduct.includeRight
  let eEndk : A.baseChange K →ₐ[k] Module.End K (Fin n → K) := eEnd.toAlgHom.restrictScalars k
  let rhoK : A →ₐ[k] Module.End K (Fin n → K) := eEndk.comp includeA
  -- Unfold the split-model action just far enough to expose the underlying `K`-linear map.
  simpa [splitModelAction, eEnd, includeA, eEndk, rhoK] using
    restrictEndCommutesScalars (k := k) (K := K) (rhoK a) x

omit [FiniteDimensional k K] in
/-- Helper for Theorem 11.8.2: the split-model range has `k`-dimension `n^2`. -/
private theorem splitModelRangeFinrank {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Module.finrank k (splitModelRange (A := A) (K := K) e) = (n : Nat) ^ 2 := by
  have hrange :
      Module.finrank k (splitModelRange (A := A) (K := K) e) = Module.finrank k A := by
    -- The split-model range is just `A` packaged as its image inside `End_k(Fin n → K)`.
    exact (splitModelRangeAlgEquiv (A := A) (K := K) e).toLinearEquiv.finrank_eq.symm
  have hbase : Module.finrank K (A.baseChange K) = Module.finrank k A := by
    -- Scalar extension to the finite field `K` preserves the dimension.
    change Module.finrank K (K ⊗[k] A) = Module.finrank k A
    exact Module.finrank_baseChange
  calc
    Module.finrank k (splitModelRange (A := A) (K := K) e) = Module.finrank k A := hrange
    _ = Module.finrank K (A.baseChange K) := hbase.symm
    _ = Module.finrank K (Matrix (Fin n) (Fin n) K) := e.toLinearEquiv.finrank_eq
    _ = (n : Nat) ^ 2 := by
      simpa [pow_two] using (Module.finrank_matrix K K (Fin n) (Fin n))

/-- Helper for Theorem 11.8.2: the ambient algebra `End_k(Fin n → K)` is simple because it is a
full matrix algebra over `k`. -/
private theorem splitModelAmbientEndIsSimple {n : ℕ+} :
    IsSimpleRing (Module.End k (Fin n → K)) := by
  let b : Module.Basis (Fin (Module.finrank k (Fin n → K))) k (Fin n → K) :=
    Module.finBasis k (Fin n → K)
  letI : Nonempty (Fin (Module.finrank k (Fin n → K))) :=
    ⟨⟨0, Module.finrank_pos (R := k) (M := Fin n → K)⟩⟩
  -- Fix one matrix model for the ambient endomorphism algebra and transport simplicity from the
  -- matrix ring.
  exact IsSimpleRing.of_ringEquiv (algEquivMatrix b).toRingEquiv.symm inferInstance

/-- Helper for Theorem 11.8.2: the ambient algebra `End_k(Fin n → K)` has square `k`-dimension. -/
private theorem splitModelAmbientEndFinrank {n : ℕ+} :
    Module.finrank k (Module.End k (Fin n → K)) =
      Module.finrank k (Fin n → K) * Module.finrank k (Fin n → K) := by
  -- This is the standard endomorphism-space dimension formula.
  simpa using (Module.finrank_linearMap k k (Fin n → K) (Fin n → K))

/-- Helper for Theorem 11.8.2: the standard split module `Fin n → K` has `k`-dimension
`n [K : k]`. -/
private theorem splitModelStandardModuleFinrank {n : ℕ+} :
    Module.finrank k (Fin n → K) = (n : Nat) * Module.finrank k K := by
  -- Count the `n` copies of `K` in the product representation.
  rw [Module.finrank_pi_fintype, Finset.sum_const_nat]
  · rw [Finset.card_univ, Fintype.card_fin]
  · intro x hx
    rfl

/-- Helper for Theorem 11.8.2: the ambient endomorphism algebra has `k`-dimension
`n^2 [K : k]^2` in one canonical normal form. -/
private theorem splitModelAmbientEndFinrankFactorized {n : ℕ+} :
    Module.finrank k (Module.End k (Fin n → K)) =
      (n : Nat) ^ 2 * (Module.finrank k K ^ 2) := by
  -- Route correction: package the ambient-dimension arithmetic before entering the
  -- centralizer proof, so the final theorem only cancels one positive factor.
  calc
    Module.finrank k (Module.End k (Fin n → K))
        = Module.finrank k (Fin n → K) * Module.finrank k (Fin n → K) :=
      splitModelAmbientEndFinrank (k := k) (K := K) (n := n)
    _ = ((n : Nat) * Module.finrank k K) * ((n : Nat) * Module.finrank k K) := by
      rw [splitModelStandardModuleFinrank (k := k) (K := K) (n := n)]
    _ = (n : Nat) ^ 2 * (Module.finrank k K ^ 2) := by
      simp only [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- Helper for Theorem 11.8.2: the ambient endomorphism algebra is central over `k` because it is
identified with a full matrix algebra over `k`. -/
private theorem splitModelAmbientEndIsCentral {n : ℕ+} :
    Algebra.IsCentral k (Module.End k (Fin n → K)) := by
  let b : Module.Basis (Fin (Module.finrank k (Fin n → K))) k (Fin n → K) :=
    Module.finBasis k (Fin n → K)
  let eMatrix :
      Module.End k (Fin n → K) ≃ₐ[k]
        Matrix (Fin (Module.finrank k (Fin n → K)))
          (Fin (Module.finrank k (Fin n → K))) k :=
    algEquivMatrix b
  refine ⟨fun x hx ↦ ?_⟩
  rw [Subalgebra.mem_center_iff] at hx
  let y := eMatrix x
  have hy :
      y ∈ Subalgebra.center k
        (Matrix (Fin (Module.finrank k (Fin n → K)))
          (Fin (Module.finrank k (Fin n → K))) k) := by
    rw [Subalgebra.mem_center_iff]
    intro M
    obtain ⟨f, rfl⟩ := eMatrix.surjective M
    simpa [y] using congrArg eMatrix (hx f)
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hy
  rw [Algebra.mem_bot]
  refine ⟨a, ?_⟩
  apply eMatrix.injective
  simpa [y] using ha.symm

omit [FiniteDimensional k K] in
/-- Helper for Theorem 11.8.2: the split-model range remains central over `k` because it is
`k`-algebra equivalent to `A`. -/
private theorem splitModelRangeIsCentral {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Algebra.IsCentral k (splitModelRange (A := A) (K := K) e) := by
  let R := splitModelRange (A := A) (K := K) e
  let eR := splitModelRangeAlgEquiv (A := A) (K := K) e
  refine ⟨fun x hx ↦ ?_⟩
  rw [Subalgebra.mem_center_iff] at hx
  let y : A := eR.symm x
  have hy : y ∈ Subalgebra.center k A := by
    rw [Subalgebra.mem_center_iff]
    intro a
    apply eR.injective
    simpa [y] using hx (eR a)
  obtain ⟨r, hr⟩ := (Algebra.IsCentral.mem_center_iff k).1 hy
  rw [Algebra.mem_bot]
  refine ⟨r, ?_⟩
  change algebraMap k R r = x
  simpa [R, y] using (congrArg eR hr).symm

/-- Helper for Theorem 11.8.2: the centralizer of the split-model range is simple by Theorem
11.7.1 applied inside `End_k(Fin n → K)`. -/
private theorem splitModelCentralizerIsSimple {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    IsSimpleRing (splitModelCentralizer (A := A) (K := K) e) := by
  let R := splitModelRange (A := A) (K := K) e
  let ambient := Module.End k (Fin n → K)
  letI : IsSimpleRing R := by
    -- Transport simplicity across the algebra equivalence from `A` to its split-model image.
    exact IsSimpleRing.of_ringEquiv (splitModelRangeAlgEquiv (A := A) (K := K) e).toRingEquiv
      inferInstance
  letI : IsSimpleRing ambient := splitModelAmbientEndIsSimple (k := k) (K := K) (n := n)
  letI : Algebra.IsCentral k ambient := splitModelAmbientEndIsCentral (k := k) (K := K) (n := n)
  let ambientCSA : CSA.{u, w} k := CSA.mk (AlgCat.of k ambient)
  -- Apply the centralizer simplicity theorem in the single ambient owner `End_k(Fin n → K)`.
  simpa [R, splitModelCentralizer] using
    (Subalgebra.isSimpleRing_centralizer
      (k := k) (A := ambientCSA) (B := R))

/-- Helper for Theorem 11.8.2: the centralizer of the split-model range is central over `k`,
because its center lies in the bicommutant, hence in the split-model range, and then in the center
of that range. -/
private theorem splitModelCentralizerIsCentral {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Algebra.IsCentral k (splitModelCentralizer (A := A) (K := K) e) := by
  let R := splitModelRange (A := A) (K := K) e
  let C := splitModelCentralizer (A := A) (K := K) e
  let ambient := Module.End k (Fin n → K)
  letI : IsSimpleRing R := by
    -- The split-model range is just `A` in a bundled ambient form.
    exact IsSimpleRing.of_ringEquiv (splitModelRangeAlgEquiv (A := A) (K := K) e).toRingEquiv
      inferInstance
  letI : IsSimpleRing ambient := splitModelAmbientEndIsSimple (k := k) (K := K) (n := n)
  letI : Algebra.IsCentral k ambient := splitModelAmbientEndIsCentral (k := k) (K := K) (n := n)
  let ambientCSA : CSA.{u, w} k := CSA.mk (AlgCat.of k ambient)
  have hCC : Subalgebra.centralizer k (C : Set (Module.End k (Fin n → K))) = R := by
    -- The double-centralizer theorem identifies the bicommutant with the original split-model
    -- range.
    simpa [R, C, splitModelCentralizer] using R.centralizer_centralizer_eq ambientCSA
  refine ⟨fun x hx ↦ ?_⟩
  have hxC :
      x.1 ∈ Subalgebra.centralizer k (C : Set (Module.End k (Fin n → K))) := by
    -- A central element of the commutant commutes with every element of that commutant.
    rw [Subalgebra.mem_centralizer_iff]
    rw [Subalgebra.mem_center_iff] at hx
    intro y hy
    exact congrArg Subtype.val (hx ⟨y, hy⟩)
  have hxR : x.1 ∈ R := by
    simpa [hCC] using hxC
  have hxCommRange : ∀ y ∈ R, y * x.1 = x.1 * y := by
    -- Membership in the commutant is exactly the ambient commuting relation with `R`.
    have hxInC : x.1 ∈ Subalgebra.centralizer k (R : Set (Module.End k (Fin n → K))) := by
      simpa [R, C, splitModelCentralizer] using (show x.1 ∈ C from x.2)
    exact
      (Subalgebra.mem_centralizer_iff
        (R := k) (s := (R : Set (Module.End k (Fin n → K)))) (z := x.1)).1 hxInC
  have hxCenterR : (⟨x.1, hxR⟩ : R) ∈ Subalgebra.center k R := by
    -- Because `x` already lies in the centralizer of `R`, its copy inside `R` is central there.
    rw [Subalgebra.mem_center_iff]
    intro y
    exact Subtype.ext (hxCommRange y.1 y.2)
  letI : Algebra.IsCentral k R := splitModelRangeIsCentral (A := A) (K := K) e
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hxCenterR
  rw [Algebra.mem_bot]
  refine ⟨a, ?_⟩
  -- The scalar description inside the range also describes `x` inside the commutant.
  apply Subtype.ext
  simpa using congrArg Subtype.val ha.symm

/-- Helper for Theorem 11.8.2: the split-model centralizer has `k`-dimension `[K : k]^2`. -/
private theorem splitModelCentralizerFinrankSq {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Module.finrank k (splitModelCentralizer (A := A) (K := K) e) =
      Module.finrank k K ^ 2 := by
  let R := splitModelRange (A := A) (K := K) e
  letI : IsSimpleRing R := by
    -- The split-model range remains simple because it is algebra equivalent to `A`.
    exact IsSimpleRing.of_ringEquiv
      (splitModelRangeAlgEquiv (A := A) (K := K) e).toRingEquiv inferInstance
  letI : Module.Free k R := Module.Free.of_divisionRing k R
  letI : IsSimpleRing (Module.End k (Fin n → K)) :=
    splitModelAmbientEndIsSimple (k := k) (K := K) (n := n)
  letI : Algebra.IsCentral k (Module.End k (Fin n → K)) :=
    splitModelAmbientEndIsCentral (k := k) (K := K) (n := n)
  let ambientCSA : CSA.{u, w} k := CSA.mk (AlgCat.of k (Module.End k (Fin n → K)))
  have hdim' :
      Module.finrank k ambientCSA =
        Module.finrank k ↥R *
          Module.finrank k
            ↥(Subalgebra.centralizer k ((R : Subalgebra k ambientCSA) : Set ambientCSA)) := by
    -- Record the centralizer dimension formula in the bundled `CSA` spelling first.
    exact R.finrank_mul_finrank_centralizer ambientCSA
  have hAmbientCSA :
      Module.finrank k ambientCSA = (n : Nat) ^ 2 * (Module.finrank k K ^ 2) := by
    -- Unbundle the ambient `CSA` once and reuse the factorized endomorphism-space formula.
    change Module.finrank k (Module.End k (Fin n → K)) =
      (n : Nat) ^ 2 * (Module.finrank k K ^ 2)
    exact splitModelAmbientEndFinrankFactorized (k := k) (K := K) (n := n)
  have hmain :
      (n : Nat) ^ 2 * Module.finrank k ↥(splitModelCentralizer (A := A) (K := K) e) =
        (n : Nat) ^ 2 * (Module.finrank k K ^ 2) := by
    -- Put both sides into the same canonical finrank normal form before cancelling.
    calc
      (n : Nat) ^ 2 * Module.finrank k ↥(splitModelCentralizer (A := A) (K := K) e)
          = Module.finrank k ↥R *
              Module.finrank k ↥(splitModelCentralizer (A := A) (K := K) e) := by
        rw [splitModelRangeFinrank (A := A) (K := K) e]
      _ = Module.finrank k ambientCSA := by
        simpa [R, splitModelCentralizer] using hdim'.symm
      _ = (n : Nat) ^ 2 * (Module.finrank k K ^ 2) := hAmbientCSA
  -- Cancel the positive factor coming from the matrix size.
  exact Nat.eq_of_mul_eq_mul_left (pow_pos n.2 2) hmain

omit [FiniteDimensional k K] in
/-- Helper for Theorem 11.8.2: scalar endomorphisms of the split module land in the commutant
algebra. -/
private theorem splitModelScalarEmbeddingToCentralizer {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Nonempty (K →ₐ[k] splitModelCentralizer (A := A) (K := K) e) := by
  let ι : K →ₐ[k] Module.End k (Fin n → K) := Algebra.lsmul k k (Fin n → K)
  have hι :
      ∀ x, ι x ∈ splitModelCentralizer (A := A) (K := K) e := by
    intro x
    -- It is enough to commute with the generators coming from the split-model action.
    rw [splitModelCentralizer, Subalgebra.mem_centralizer_iff]
    intro y hy
    rcases hy with ⟨a, rfl⟩
    exact (splitModelActionCommutesScalars (A := A) (K := K) e a x).eq
  exact ⟨ι.codRestrict (splitModelCentralizer (A := A) (K := K) e) hι⟩

/-- Helper for Theorem 11.8.2: the base field representative is Brauer equivalent to the
canonical unit representative. -/
private theorem brauerEquivalent_baseField_unit :
    IsBrauerEquivalent (baseFieldRepresentative (A := A) (k := k)) (unit.{u, v} k) := by
  -- Package the canonical `ULift` comparison into a `1 × 1` Brauer witness.
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  exact ⟨((Matrix.reindexAlgEquiv k (baseFieldRepresentative (A := A) (k := k))
    finOneEquiv).trans uniqueAlgEquiv).trans <|
    (baseFieldRepresentativeAlgEquiv (A := A) (k := k)).trans <|
    (ULift.algEquiv : ↑(unit.{u, v} k).toAlgCat ≃ₐ[k] k).symm.trans <|
      ((Matrix.reindexAlgEquiv k (unit.{u, v} k) finOneEquiv).trans uniqueAlgEquiv).symm⟩

/-- Helper for Theorem 11.8.2: tensoring on the right with the base field representative preserves
the Brauer class. -/
private theorem brauerEquivalent_tensorProduct_baseField (B : CSA.{u, v} k) :
    IsBrauerEquivalent (B.tensorProduct (baseFieldRepresentative (A := A) (k := k))) B := by
  let eBase : B.tensorProduct (baseFieldRepresentative (A := A) (k := k)) ≃ₐ[k] B :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[k] B)
      (baseFieldRepresentativeAlgEquiv (A := A) (k := k))).trans <|
        Algebra.TensorProduct.rid k k B
  exact CSA.brauerEquivalentOfAlgEquiv (k := k) eBase

/-- Helper for Theorem 11.8.2: tensoring on the left with the base field representative preserves
the Brauer class. -/
private theorem brauerEquivalent_baseField_tensorProduct (B : CSA.{u, v} k) :
    IsBrauerEquivalent ((baseFieldRepresentative (A := A) (k := k)).tensorProduct B) B := by
  let eBase : (baseFieldRepresentative (A := A) (k := k)).tensorProduct B ≃ₐ[k] B :=
    (Algebra.TensorProduct.congr (baseFieldRepresentativeAlgEquiv (A := A) (k := k))
      (AlgEquiv.refl : B ≃ₐ[k] B)).trans <|
        Algebra.TensorProduct.lid k B
  exact CSA.brauerEquivalentOfAlgEquiv (k := k) eBase

/-- Helper for Theorem 11.8.2: the base field representative is Brauer equivalent to
`B ⊗[k] Bᵐᵒᵖ`. -/
private theorem brauerEquivalent_baseField_tensorProduct_opposite (B : CSA.{u, v} k) :
    IsBrauerEquivalent (baseFieldRepresentative (A := A) (k := k))
      (B.tensorProduct B.opposite) := by
  exact IsBrauerEquivalent.trans (brauerEquivalent_baseField_unit (A := A) (k := k))
    (IsBrauerEquivalent.symm (CSA.brauerEquivalent_tensorProduct_opposite (k := k) B))

/-- Helper for Theorem 11.8.2: if `A ⊗[k] B` is Brauer-trivial, then `A` is Brauer equivalent to
`Bᵐᵒᵖ`. -/
private theorem brauerEquivalent_of_tensorProduct_unit_opposite {B : CSA.{u, v} k}
    (h : IsBrauerEquivalent (A.tensorProduct B) (baseFieldRepresentative (A := A) (k := k))) :
    IsBrauerEquivalent A B.opposite := by
  have hBaseToTensor :
      IsBrauerEquivalent (baseFieldRepresentative (A := A) (k := k))
        (B.tensorProduct B.opposite) := by
    -- Replace the base field representative by `B ⊗[k] Bᵐᵒᵖ` through the canonical neutral witness.
    exact brauerEquivalent_baseField_tensorProduct_opposite (A := A) (k := k) B
  have hAUnit :
      IsBrauerEquivalent A (A.tensorProduct (baseFieldRepresentative (A := A) (k := k))) := by
    -- Insert the explicit base-field tensor factor on the right.
    exact IsBrauerEquivalent.symm (brauerEquivalent_tensorProduct_baseField (A := A) (k := k) A)
  have hATensor :
      IsBrauerEquivalent A (A.tensorProduct (B.tensorProduct B.opposite)) := by
    -- Tensor the base-field replacement with the unchanged left factor `A`.
    exact IsBrauerEquivalent.trans hAUnit
      (CSA.brauerEquivalent_tensorProduct (k := k) (IsBrauerEquivalent.refl A) hBaseToTensor)
  have hAssoc :
      IsBrauerEquivalent (A.tensorProduct (B.tensorProduct B.opposite))
        ((A.tensorProduct B).tensorProduct B.opposite) := by
    -- Reassociate so that the hypothesis `h` applies to the left tensor factor.
    exact IsBrauerEquivalent.symm
      (CSA.brauerEquivalent_tensorProduct_assoc (k := k) A B B.opposite)
  have hLeftFactor :
      IsBrauerEquivalent ((A.tensorProduct B).tensorProduct B.opposite)
        ((baseFieldRepresentative (A := A) (k := k)).tensorProduct B.opposite) := by
    -- Tensor the hypothesis with the unchanged opposite factor.
    exact CSA.brauerEquivalent_tensorProduct (k := k) h
      (IsBrauerEquivalent.refl B.opposite)
  have hUnitTensor :
      IsBrauerEquivalent
        ((baseFieldRepresentative (A := A) (k := k)).tensorProduct B.opposite) B.opposite := by
    -- Remove the explicit base-field tensor factor on the left.
    exact brauerEquivalent_baseField_tensorProduct (A := A) (k := k) B.opposite
  -- Chaining the neutral-factor insertion, reassociation, and removal yields the desired inverse.
  exact IsBrauerEquivalent.trans hATensor <|
    IsBrauerEquivalent.trans hAssoc <|
      IsBrauerEquivalent.trans hLeftFactor hUnitTensor

/-- Helper for Theorem 11.8.2: the split-model commutant witness makes `A ⊗[k] B₀`
Brauer-trivial. -/
private theorem splitModelTensorProductBrauerUnit {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K)
    [Algebra.IsCentral k (splitModelCentralizer (A := A) (K := K) e)]
    [IsSimpleRing (splitModelCentralizer (A := A) (K := K) e)] :
    IsBrauerEquivalent
      (A.tensorProduct
        (shrinkFiniteCentralSimple (A := A) (k := k)
          (splitModelCentralizer (A := A) (K := K) e)))
      (baseFieldRepresentative (A := A) (k := k)) := by
  let R := splitModelRange (A := A) (K := K) e
  let C := splitModelCentralizer (A := A) (K := K) e
  let ambient := Module.End k (Fin n → K)
  letI : IsSimpleRing R := by
    -- The left tensor factor is the split-model copy of `A`.
    exact IsSimpleRing.of_ringEquiv (splitModelRangeAlgEquiv (A := A) (K := K) e).toRingEquiv
      inferInstance
  letI : Algebra.IsCentral k R := splitModelRangeIsCentral (A := A) (K := K) e
  letI : IsSimpleRing ambient := splitModelAmbientEndIsSimple (k := k) (K := K) (n := n)
  let b : Module.Basis (Fin (Module.finrank k (Fin n → K))) k (Fin n → K) :=
    Module.finBasis k (Fin n → K)
  letI : Algebra.IsCentral k ambient := splitModelAmbientEndIsCentral (k := k) (K := K) (n := n)
  let ambientCSA : CSA.{u, w} k := CSA.mk (AlgCat.of k ambient)
  have hTensorAmbient :
      IsBrauerEquivalent
        (A.tensorProduct (shrinkFiniteCentralSimple (A := A) (k := k) C))
        (shrinkFiniteCentralSimple (A := A) (k := k) ambient) := by
    -- First rewrite the tensor product as `R ⊗ C`, then use the centralizer tensor-product
    -- equivalence, and finally shrink the ambient algebra back to universe `v`.
    exact CSA.brauerEquivalentOfAlgEquiv (k := k) <|
      (Algebra.TensorProduct.congr
        (splitModelRangeAlgEquiv (A := A) (K := K) e)
        (shrinkFiniteCentralSimpleAlgEquiv (A := A) (k := k) C)).trans <|
      (Subalgebra.centralizerTensorProductAlgEquiv (k := k) (A := ambientCSA) (B := R)).trans <|
      (shrinkFiniteCentralSimpleAlgEquiv (A := A) (k := k) ambient).symm
  have hAmbientField :
      IsBrauerEquivalent
        (shrinkFiniteCentralSimple (A := A) (k := k) ambient)
        (baseFieldRepresentative (A := A) (k := k)) := by
    letI : NeZero (Module.finrank k (Fin n → K)) :=
      ⟨Nat.ne_of_gt (Module.finrank_pos (R := k) (M := Fin n → K))⟩
    let eMatrix :
      shrinkFiniteCentralSimple (A := A) (k := k) ambient ≃ₐ[k]
          Matrix (Fin (Module.finrank k (Fin n → K)))
            (Fin (Module.finrank k (Fin n → K))) k :=
      (shrinkFiniteCentralSimpleAlgEquiv (A := A) (k := k) ambient).trans
        (algEquivMatrix b)
    let eField :
        shrinkFiniteCentralSimple (A := A) (k := k) ambient ≃ₐ[k]
          Matrix (Fin (Module.finrank k (Fin n → K)))
            (Fin (Module.finrank k (Fin n → K)))
            (baseFieldRepresentative (A := A) (k := k)) :=
      eMatrix.trans <|
        matrix_coeffAlgEquiv (k := k) (n := Module.finrank k (Fin n → K))
          (baseFieldRepresentativeAlgEquiv (A := A) (k := k)).symm
    -- A full matrix algebra over `k` represents the neutral Brauer class.
    refine ⟨1, Module.finrank k (Fin n → K), one_ne_zero, NeZero.ne _, ?_⟩
    exact ⟨((Matrix.reindexAlgEquiv k
      (shrinkFiniteCentralSimple (A := A) (k := k) ambient) finOneEquiv).trans
        uniqueAlgEquiv).trans eField⟩
  -- Compose the tensor-product trivialization with the matrix-model identification of the base field.
  exact IsBrauerEquivalent.trans hTensorAmbient hAmbientField

/-- Helper for Theorem 11.8.2: a splitting field produces the textbook commutant witness in the
Brauer class of `A`. -/
lemma forward_commutant_witness_of_split
    (hA : A.IsSplitBy K) :
    ∃ B : CSA.{u, v} k,
      IsBrauerEquivalent A B ∧
        Nonempty (K →ₐ[k] B) ∧
        Module.finrank k B = Module.finrank k K ^ 2 := by
  rcases (A.isSplitBy_iff_exists_pnat_algEquiv_matrix K).1 hA with ⟨n, ⟨e⟩⟩
  let C := splitModelCentralizer (A := A) (K := K) e
  letI : IsSimpleRing C := splitModelCentralizerIsSimple (A := A) (K := K) e
  letI : Algebra.IsCentral k C := splitModelCentralizerIsCentral (A := A) (K := K) e
  let B₀ := shrinkFiniteCentralSimple (A := A) (k := k) C
  have hBrauerB₀ :
      IsBrauerEquivalent A B₀.opposite := by
    -- The commutant tensor-product model is Brauer-trivial, so cancellation yields the opposite
    -- representative of the commutant.
    exact brauerEquivalent_of_tensorProduct_unit_opposite (A := A) (k := k) (B := B₀) <|
      splitModelTensorProductBrauerUnit (A := A) (K := K) (k := k) e
  have hEmbedB₀ : Nonempty (K →ₐ[k] B₀) := by
    rcases splitModelScalarEmbeddingToCentralizer (A := A) (K := K) e with ⟨ιC⟩
    -- Transport the scalar embedding from the centralizer to its shrunk carrier.
    exact ⟨(shrinkFiniteCentralSimpleAlgEquiv (A := A) (k := k) C).symm.toAlgHom.comp ιC⟩
  have hEmbedOpp : Nonempty (K →ₐ[k] B₀.opposite) := by
    rcases hEmbedB₀ with ⟨ιB₀⟩
    -- The image of a field is commutative, so the same map lands in the opposite algebra.
    exact ⟨ιB₀.toOpposite (algHomFromFieldCommutes (k := k) (K := K) ιB₀)⟩
  have hdimB₀ :
      Module.finrank k B₀ = Module.finrank k K ^ 2 := by
    -- Shrinking the commutant preserves its `k`-dimension.
    calc
      Module.finrank k B₀ = Module.finrank k C := by
        exact (shrinkFiniteCentralSimpleAlgEquiv (A := A) (k := k) C).toLinearEquiv.finrank_eq
      _ = Module.finrank k K ^ 2 := splitModelCentralizerFinrankSq (A := A) (K := K) e
  have hdimOpp :
      Module.finrank k B₀.opposite = Module.finrank k K ^ 2 := by
    -- Passing to the opposite algebra does not change the underlying `k`-vector-space dimension.
    calc
      Module.finrank k B₀.opposite = Module.finrank k B₀ := by
        exact (MulOpposite.opLinearEquiv k (M := B₀)).finrank_eq.symm
      _ = Module.finrank k K ^ 2 := hdimB₀
  exact ⟨B₀.opposite, hBrauerB₀, hEmbedOpp, hdimOpp⟩

-- Proof sketch: for the forward implication, realize the split algebra as `End_K(V)`, take the
-- commutant of `A` in `End_k(V)`, and use the double-centralizer dimension formula to obtain a
-- Brauer-equivalent algebra containing `K` with `k`-dimension `[K : k]^2`. For the reverse
-- implication, use the embedded copy of `K` in `B`, identify `B ⊗[k] K` with the corresponding
-- centralizer in `End_k(B)`, and apply the centralizer criterion from the previous subsection.
/-- Theorem 11.8.2: a finite extension `K/k` splits the finite central simple `k`-algebra `A` if
and only if there exists a finite central simple `k`-algebra `B` Brauer equivalent to `A` that
contains `K` as a `k`-subalgebra and has `k`-dimension `[K : k]^2`. -/
@[stacks 074Z]
theorem isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq :
    A.IsSplitBy K ↔
      ∃ B : CSA.{u, v} k,
        IsBrauerEquivalent A B ∧
          Nonempty (K →ₐ[k] B) ∧
          Module.finrank k B = Module.finrank k K ^ 2 := by
  constructor
  · intro hA
    -- Route correction: package the source commutant construction as a named helper so the main
    -- theorem only records the final forward implication.
    exact A.forward_commutant_witness_of_split K hA
  · rintro ⟨B, hAB, hK, hdim⟩
    have hSplitB : B.IsSplitBy K := B.isSplitBy_of_self_embedding_finrank_sq K hK hdim
    -- Once the representative `B` is known to split, transport splitness back across Brauer
    -- equivalence using the base-change criterion.
    exact (A.isSplitBy_iff_of_isBrauerEquivalent_via_baseChange K hAB).2 hSplitB

end CSA
