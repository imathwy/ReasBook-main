import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.QuasiFinite.Basic
import stacks_proof.stacks_project.Chap10.Lemma_10_107_3
import stacks_proof.stacks_project.Chap10.Lemma_10_107_8
import stacks_proof.stacks_project.Chap10.Remark_10_107_12
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

open Matrix
open scoped TensorProduct

/-- Helper for Lemma 10.107.13: `AssocTriple R` is the type of finite matrix triples over `R`
used in Remark 10.107.12. -/
abbrev AssocTriple (R : Type u) [CommRing R] :=
  Σ n : ℕ, Matrix (Fin n) (Fin n) R × Matrix (Fin 1) (Fin n) R × Matrix (Fin n) (Fin 1) R

/-- Helper for Lemma 10.107.13: an associated matrix triple determines the source element
uniquely. -/
lemma associated_matrix_triple_eq {g g' : S} {n : ℕ}
    {P : Matrix (Fin n) (Fin n) R} {U : Matrix (Fin 1) (Fin n) R}
    {V : Matrix (Fin n) (Fin 1) R}
    (hg : is_associated_matrix_triple (R := R) g n P U V)
    (hg' : is_associated_matrix_triple (R := R) g' n P U V) :
    g = g' := by
  rcases hg with ⟨y, z, rfl, hU, hV⟩
  rcases hg' with ⟨y', z', hg', hU', hV'⟩
  let P' := P.map (algebraMap R S)
  have hrow : y ᵥ* P' = y' ᵥ* P' := by
    -- The common row matrix `U` forces the two row-vector products to coincide.
    apply Matrix.replicateRow_injective (ι := Fin 1)
    calc
      Matrix.replicateRow (Fin 1) (y ᵥ* P') = U.map (algebraMap R S) := hU.symm
      _ = Matrix.replicateRow (Fin 1) (y' ᵥ* P') := hU'
  have hcol : P' *ᵥ z = P' *ᵥ z' := by
    -- The common column matrix `V` forces the two column-vector products to coincide.
    apply Matrix.replicateCol_injective (ι := Fin 1)
    calc
      Matrix.replicateCol (Fin 1) (P' *ᵥ z) = V.map (algebraMap R S) := hV.symm
      _ = Matrix.replicateCol (Fin 1) (P' *ᵥ z') := hV'
  -- Route correction: the source proof compares the common row and column data first, then
  -- rewrites the scalar expression for `g` through the shared matrix product.
  calc
    y ᵥ* P' ⬝ᵥ z = y' ᵥ* P' ⬝ᵥ z := by rw [hrow]
    _ = y' ⬝ᵥ (P' *ᵥ z) := by rw [← Matrix.dotProduct_mulVec]
    _ = y' ⬝ᵥ (P' *ᵥ z') := by rw [hcol]
    _ = y' ᵥ* P' ⬝ᵥ z' := by rw [Matrix.dotProduct_mulVec]
    _ = g' := hg'.symm

/-- Helper for Lemma 10.107.13: an epic algebra embeds into the space of associated matrix
triples. -/
lemma associated_matrix_triple_embedding [Algebra.IsEpi R S] :
    Nonempty (S ↪ AssocTriple R) := by
  classical
  have htmul : ∀ g : S, g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g :=
    fun g ↦ ((Algebra.isEpi_iff_forall_one_tmul_eq R S).mp inferInstance g).symm
  choose n P U V htriple using
    fun g : S =>
      exists_associated_matrix_triple_of_tmul_one_eq_one_tmul (R := R) (S := S) g (htmul g)
  let τ : S → AssocTriple R := fun g ↦ ⟨n g, (P g, U g, V g)⟩
  refine ⟨
    { toFun := τ
      inj' := ?_ }⟩
  intro g g' hEq
  -- Equality of the chosen triples reduces directly to the uniqueness lemma above.
  have hgTriple :
      is_associated_matrix_triple (R := R) g (τ g).1 (τ g).2.1 (τ g).2.2.1 (τ g).2.2.2 := by
    simpa [τ] using htriple g
  have hg'Triple :
      is_associated_matrix_triple (R := R) g' (τ g).1 (τ g).2.1 (τ g).2.2.1 (τ g).2.2.2 :=
    Eq.ndrec
      (motive := fun t : AssocTriple R =>
        is_associated_matrix_triple (R := R) g' t.1 t.2.1 t.2.2.1 t.2.2.2)
      (by simpa [τ] using htriple g')
      hEq.symm
  exact associated_matrix_triple_eq (R := R) (g := g) (g' := g') hgTriple hg'Triple

/-- Helper for Lemma 10.107.13: encode an associated triple by its size and the lists of matrix,
row, and column entries. -/
def assocTripleToLists : AssocTriple R → ℕ × List R × List R × List R
  | ⟨n, (P, U, V)⟩ =>
      ( n
      , List.ofFn fun ij : Fin (n * n) => Matrix.vec P (finProdFinEquiv.symm ij)
      , List.ofFn fun j : Fin n => U 0 j
      , List.ofFn fun i : Fin n => V i 0 )

/-- Helper for Lemma 10.107.13: the list encoding of associated triples is injective. -/
lemma assocTripleToLists_injective :
    Function.Injective (assocTripleToLists (R := R)) := by
  intro x y hxy
  rcases x with ⟨n, P, U, V⟩
  rcases y with ⟨n', P', U', V'⟩
  have hn : n = n' := by
    simpa [assocTripleToLists] using congrArg Prod.fst hxy
  subst hn
  have hPList :
      List.ofFn (fun ij : Fin (n * n) => Matrix.vec P (finProdFinEquiv.symm ij)) =
        List.ofFn (fun ij : Fin (n * n) => Matrix.vec P' (finProdFinEquiv.symm ij)) := by
    simpa [assocTripleToLists] using congrArg (fun t ↦ t.2.1) hxy
  have hUList :
      List.ofFn (fun j : Fin n => U 0 j) = List.ofFn (fun j : Fin n => U' 0 j) := by
    simpa [assocTripleToLists] using congrArg (fun t ↦ t.2.2.1) hxy
  have hVList :
      List.ofFn (fun i : Fin n => V i 0) = List.ofFn (fun i : Fin n => V' i 0) := by
    simpa [assocTripleToLists] using congrArg (fun t ↦ t.2.2.2) hxy
  have hP : P = P' := by
    -- The flattened matrix entry list recovers every entry of `P`.
    ext i j
    have hEntries := List.ofFn_inj.mp hPList
    simpa using congrFun hEntries (finProdFinEquiv (j, i))
  have hU : U = U' := by
    -- The single-row list recovers every entry of `U`.
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    cases hi
    exact congrFun (List.ofFn_inj.mp hUList) j
  have hV : V = V' := by
    -- The single-column list recovers every entry of `V`.
    ext i j
    have hj : j = 0 := Subsingleton.elim _ _
    cases hj
    exact congrFun (List.ofFn_inj.mp hVList) i
  subst hP
  subst hU
  subst hV
  rfl

/-- Helper for Lemma 10.107.13: over an infinite base ring, associated triples have cardinality at
most the cardinality of the base ring. -/
lemma associated_triple_cardinal_le_of_infinite [Infinite R] :
    Cardinal.lift.{v} (Cardinal.mk (AssocTriple R)) ≤ Cardinal.lift.{v} (Cardinal.mk R) := by
  have hencode0 :
      Cardinal.lift (Cardinal.mk (AssocTriple R)) ≤
        Cardinal.lift (Cardinal.mk (ℕ × List R × List R × List R)) :=
    Cardinal.lift_mk_le_lift_mk_of_injective (assocTripleToLists_injective (R := R))
  have hencode :
      Cardinal.lift.{v} (Cardinal.mk (AssocTriple R)) ≤
        Cardinal.lift.{v} (Cardinal.mk (ℕ × List R × List R × List R)) :=
    by simpa [Cardinal.lift_id] using Cardinal.lift_monotone hencode0
  have hlist : Cardinal.mk (List R) = Cardinal.mk R :=
    Cardinal.mk_list_eq_mk R
  have hR : Cardinal.aleph0 ≤ Cardinal.mk R :=
    Cardinal.aleph0_le_mk R
  have hcodomain : Cardinal.mk (ℕ × List R × List R × List R) = Cardinal.mk R := by
    calc
      Cardinal.mk (ℕ × List R × List R × List R)
          = Cardinal.aleph0 * Cardinal.mk R * Cardinal.mk R * Cardinal.mk R := by
              simp [Cardinal.mk_prod, hlist]
      _ = Cardinal.mk R := by
            rw [Cardinal.aleph0_mul_eq hR, Cardinal.mul_eq_self hR, Cardinal.mul_eq_self hR]
  calc
    Cardinal.lift.{v} (Cardinal.mk (AssocTriple R))
        ≤ Cardinal.lift.{v} (Cardinal.mk (ℕ × List R × List R × List R)) := hencode
    _ = Cardinal.lift.{v} (Cardinal.mk R) := by rw [hcodomain]

/-- Helper for Lemma 10.107.13: an epic algebra admits at most one algebra map to any target. -/
lemma algHom_eq_of_isEpi [Algebra.IsEpi R S] {T : Type*} [CommRing T] [Algebra R T]
    (f g : S →ₐ[R] T) :
    f = g := by
  ext s
  simpa using
    congr(Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _)
      $((Algebra.isEpi_iff_forall_one_tmul_eq R S).mp inferInstance s)).symm

/-- Helper for Lemma 10.107.13: base change of an epic algebra remains epic without a
same-universe restriction on the target algebra. -/
lemma algebra_isEpi_tensorProduct_of_isEpi_univ {R' : Type u} [CommRing R'] [Algebra R R']
    [Algebra.IsEpi R S] :
    Algebra.IsEpi R' (R' ⊗[R] S) := by
  -- The tensor product is initial among `R'`-algebras equipped with an `R`-algebra map from `S`.
  refine (algebra_isEpi_iff_includeLeft_eq_includeRight (R := R') (S := R' ⊗[R] S)).mpr ?_
  apply Algebra.TensorProduct.ext
  · -- Both maps are `R'`-algebra morphisms, so they agree on the left tensor factor.
    apply AlgHom.ext
    intro x
    simpa using
      (Algebra.TensorProduct.tmul_one_eq_one_tmul
        (R := R') (A := R' ⊗[R] S) (B := R' ⊗[R] S) x)
  · -- On the right tensor factor, equality reduces to the original epimorphism `R → S`.
    exact algHom_eq_of_isEpi (R := R) (S := S)
      ((Algebra.TensorProduct.includeLeft :
          R' ⊗[R] S →ₐ[R'] (R' ⊗[R] S) ⊗[R'] (R' ⊗[R] S))
        |>.restrictScalars R |>.comp Algebra.TensorProduct.includeRight)
      ((Algebra.TensorProduct.includeRight :
          R' ⊗[R] S →ₐ[R'] (R' ⊗[R] S) ⊗[R'] (R' ⊗[R] S))
        |>.restrictScalars R |>.comp Algebra.TensorProduct.includeRight)

/-- Helper for Lemma 10.107.13: the fibers over residue fields of an epic algebra are finite as
modules over the residue field. -/
lemma fiber_moduleFinite_of_isEpi [Algebra.IsEpi R S] (P : Ideal R) [P.IsPrime] :
    Module.Finite P.ResidueField (P.Fiber S) := by
  let _ : Algebra.IsEpi P.ResidueField (P.Fiber S) :=
    algebra_isEpi_tensorProduct_of_isEpi_univ (R := R) (S := S) (R' := P.ResidueField)
  rcases epi_field_subsingleton_or_alg_equiv (k := P.ResidueField) (S := P.Fiber S) with hsub | he
  · let _ : Subsingleton (P.Fiber S) := hsub
    let _ : Module.FinitePresentation P.ResidueField (P.Fiber S) := inferInstance
    infer_instance
  · let e := he.some
    exact Module.Finite.of_surjective e.toLinearEquiv.toLinearMap e.surjective

/-- Helper for Lemma 10.107.13: an epic algebra is quasi-finite in the fiberwise sense. -/
lemma quasiFinite_of_isEpi [Algebra.IsEpi R S] :
    Algebra.QuasiFinite R S := by
  exact ⟨fun P _ ↦ fiber_moduleFinite_of_isEpi (R := R) (S := S) P⟩

/-- Helper for Lemma 10.107.13: a finite commutative ring is Artinian. -/
lemma isArtinianRing_of_finite [Finite R] :
    IsArtinianRing R := by
  let _ : IsNoetherianRing R := inferInstance
  let _ : Ring.KrullDimLE 0 R := Ring.KrullDimLE.mk₀ fun I hI ↦ by
    let _ : Finite (R ⧸ I) :=
      Finite.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    exact Ideal.Quotient.maximal_of_isField I (Finite.isField_of_domain (R ⧸ I))
  exact (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero).2 ⟨inferInstance, inferInstance⟩

-- Domain-style sampling for this item:
-- - primary domain: commutative algebra of ring epimorphisms, controlled via the tensor-product
--   criterion and finite matrix witnesses over the base ring;
-- - sampled owner API: `Algebra.isEpi_iff_forall_one_tmul_eq`,
--   `tmul_one_eq_one_tmul_iff_exists_finite_matrix_expression`, and the source-facing bridge
--   `exists_associated_matrix_triple_of_tmul_one_eq_one_tmul`;
-- - `source-facing`: the cardinality comparison `|S| ≤ |R|`;
-- - `core/canonical`: Lemma `10.107.11`, which organizes the epicity relation `g ⊗ 1 = 1 ⊗ g`
--   by finite matrix data over `R`;
-- - `bridge/view`: Remark `10.107.12`, which repackages those matrix witnesses as an associated
--   triple `(P, U, V)` with row and column data landing in the image of `R`.
--
-- Proof sketch: by `Algebra.isEpi_iff_forall_one_tmul_eq`, epimorphy gives
-- `g ⊗ₜ[R] 1 = 1 ⊗ₜ[R] g` for every `g : S`. The owner theorem
-- `tmul_one_eq_one_tmul_iff_exists_finite_matrix_expression` supplies finite matrix witness data
-- over `R`, and Remark `10.107.12` compresses that data to an associated triple `(P, U, V)`. The
-- source uniqueness argument shows that one triple cannot be associated to two different elements
-- of `S`, so `S` injects into the set of finite triples over `R`. That set has cardinality at
-- most `|R|`; in the finite-ring case the source reduces to surjectivity of an epimorphism from an
-- Artinian ring.
/-- Lemma 10.107.13: if `R → S` is an epimorphism of commutative rings, then the cardinality of
`S` is at most the cardinality of `R`. -/
@[stacks 04W0]
theorem cardinalMk_le_of_isEpi [Algebra.IsEpi R S] :
    Cardinal.lift.{u} (Cardinal.mk S) ≤ Cardinal.lift.{v} (Cardinal.mk R) := by
  rcases finite_or_infinite R with hR | hR
  · let _ : Finite R := hR
    let _ : IsArtinianRing R := isArtinianRing_of_finite (R := R)
    let _ : Algebra.QuasiFinite R S := quasiFinite_of_isEpi (R := R) (S := S)
    let _ : Module.Finite R S := Module.Finite.of_quasiFinite
    have hsurj : Function.Surjective (algebraMap R S) :=
      (Algebra.isEpi_iff_surjective_algebraMap_of_finite (R := R) (A := S)).mp inferInstance
    -- In the finite-source branch, quasi-finiteness upgrades to module-finiteness, so the
    -- epicity criterion collapses to surjectivity.
    exact Cardinal.lift_mk_le_lift_mk_of_surjective hsurj
  · let _ : Infinite R := hR
    obtain ⟨e⟩ := associated_matrix_triple_embedding (R := R) (S := S)
    have hembed :
        Cardinal.lift.{u} (Cardinal.mk S) ≤ Cardinal.lift.{v} (Cardinal.mk (AssocTriple R)) :=
      Cardinal.lift_mk_le_lift_mk_of_injective e.injective
    -- In the infinite-source branch, the source-faithful triple-counting argument closes the
    -- cardinal estimate.
    exact hembed.trans (associated_triple_cardinal_le_of_infinite (R := R))

end
