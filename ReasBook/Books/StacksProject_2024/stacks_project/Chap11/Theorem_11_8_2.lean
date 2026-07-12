import Mathlib
import StacksProject_2024.Chap11.Definition_11_8_1
import StacksProject_2024.Chap11.Lemma_11_5_1

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

universe u v w

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
    {k : Type u} [Field k] {B : CSA.{u, v} k} {n : ℕ} [NeZero n] {D : Type v}
    [DivisionRing D] [Algebra k D] [FiniteDimensional k D] [Algebra.IsCentral k D]
    (e : B ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    IsBrauerEquivalent B (CSA.mk (AlgCat.of k D)) := by
  -- Package the direct matrix presentation as the `1 × 1` stabilization witness.
  refine ⟨1, n, one_ne_zero, NeZero.ne n, ?_⟩
  exact ⟨((reindexAlgEquiv k B finOneEquiv).trans uniqueAlgEquiv).trans e⟩

/-- Helper for Theorem 11.8.2: a coefficient algebra equivalence induces the corresponding matrix
algebra equivalence by entrywise transport. -/
private noncomputable theorem matrix_coeffAlgEquiv
    {k : Type u} [Field k] (n : ℕ) {R S : Type v} [Semiring R] [Semiring S]
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

/-- Helper for Theorem 11.8.2: scalar extension identifies a matrix algebra with the matrix
algebra over the scalar-extended coefficients. -/
noncomputable theorem baseChange_matrix_algEquiv_matrix_baseChange (n : ℕ) :
    K ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin n) (Fin n) (A.baseChange K) := by
  let eK : K ≃ₐ[K] Matrix (Fin 1) (Fin 1) K :=
    ((Matrix.reindexAlgEquiv K K finOneEquiv).trans uniqueAlgEquiv).symm
  let eTensor :
      K ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[K]
        Matrix (Fin 1) (Fin 1) K ⊗[k] Matrix (Fin n) (Fin n) A :=
    Algebra.TensorProduct.congr eK
      (AlgEquiv.refl (Matrix (Fin n) (Fin n) A))
  let eKronecker :
      Matrix (Fin 1) (Fin 1) K ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[K]
        Matrix (Fin 1 × Fin n) (Fin 1 × Fin n) (K ⊗[k] A) :=
    Matrix.kroneckerTMulAlgEquiv (Fin 1) (Fin n) k K K A
  let eProd : Fin 1 × Fin n ≃ Fin n :=
    finProdFinEquiv.trans (finCongr (show 1 * n = n by simp))
  -- Repackage the left scalar factor as a `1 × 1` matrix algebra, apply the Kronecker tensor
  -- equivalence, and then collapse the product index.
  exact eTensor.trans <| eKronecker.trans <| Matrix.reindexAlgEquiv K (A.baseChange K) eProd

/-- Helper for Theorem 11.8.2: a matrix-stabilization Brauer witness lifts across scalar
extension. -/
noncomputable theorem baseChange_of_matrix_brauer_witness {B : CSA.{u, v} k} {n m : ℕ}
    (e : Matrix (Fin n) (Fin n) A ≃ₐ[k] Matrix (Fin m) (Fin m) B) :
    Matrix (Fin n) (Fin n) (A.baseChange K) ≃ₐ[K] Matrix (Fin m) (Fin m) (B.baseChange K) := by
  let eTensor :
      K ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[K]
        K ⊗[k] Matrix (Fin m) (Fin m) B :=
    Algebra.TensorProduct.congr (AlgEquiv.refl K) e
  -- Move the scalar extension through both matrix algebras, apply the original witness over `k`,
  -- and then move back to the canonical base-changed coefficient algebras.
  exact
    (A.baseChange_matrix_algEquiv_matrix_baseChange (K := K) n).symm.trans <|
      eTensor.trans <|
        B.baseChange_matrix_algEquiv_matrix_baseChange (K := K) m

/-- Helper for Theorem 11.8.2: a split base change is Brauer equivalent to the base field over
the extension. -/
lemma split_imp_brauerEquivalent_baseField :
    A.IsSplitBy K → IsBrauerEquivalent (A.baseChange K) (CSA.mk (AlgCat.of K K)) := by
  rintro ⟨n, hSplit⟩
  by_cases hn : n = 0
  · rcases hSplit with ⟨e⟩
    -- A matrix algebra of size `0` cannot be isomorphic to the nontrivial algebra `A.baseChange K`.
    exfalso
    subst hn
    exact zero_ne_one <| e.injective <| Subsingleton.elim _ _
  · rcases hSplit with ⟨e⟩
    -- Repackage the split matrix model directly as the matrix-stabilization witness.
    refine ⟨1, n, one_ne_zero, hn, ?_⟩
    exact ⟨((reindexAlgEquiv K (A.baseChange K) finOneEquiv).trans uniqueAlgEquiv).trans e⟩

/-- Helper for Theorem 11.8.2: Brauer equivalence survives scalar extension. -/
lemma isBrauerEquivalent_baseChange {B : CSA.{u, v} k}
    (hAB : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (A.baseChange K) (B.baseChange K) := by
  rcases hAB with ⟨n, m, hn, hm, ⟨e⟩⟩
  -- Route correction: keep the Brauer bookkeeping here minimal and delegate the recurring
  -- scalar-extension/matrix transport to the theorem-local helper layer.
  refine ⟨n, m, hn, hm, ?_⟩
  exact ⟨A.baseChange_of_matrix_brauer_witness (K := K) e⟩

/-- Helper for Theorem 11.8.2: over the extension field `K`, splitness is equivalent to Brauer
equivalence of `A.baseChange K` with the base field representative. -/
lemma isSplitBy_iff_brauerEquivalent_baseField :
    A.IsSplitBy K ↔ IsBrauerEquivalent (A.baseChange K) (CSA.mk (AlgCat.of K K)) := by
  constructor
  · exact A.split_imp_brauerEquivalent_baseField K
  · intro hBrauer
    letI : IsArtinianRing (A.baseChange K) := IsArtinianRing.of_finite K (A.baseChange K)
    -- Follow the source route: first choose a division-algebra matrix model of `A.baseChange K`.
    obtain ⟨n, hn, D, hDdiv, hDalg, hDfinite, ⟨e⟩⟩ :=
      IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K (A.baseChange K)
    letI : NeZero n := hn
    letI : DivisionRing D := hDdiv
    letI : Algebra K D := hDalg
    letI : Module.Finite K D := hDfinite
    letI : FiniteDimensional K D := inferInstance
    letI : Algebra.IsCentral K (Matrix (Fin n) (Fin n) D) :=
      Algebra.IsCentral.of_algEquiv K (A.baseChange K) _ e
    letI : Algebra.IsCentral K D := matrix_central_implies_division_central (k := K) n D
    have hAD : IsBrauerEquivalent (A.baseChange K) (CSA.mk (AlgCat.of K D)) :=
      matrix_model_isBrauerEquivalent_division (k := K) e
    -- The trivial Brauer class forces the coefficient division algebra to be the field `K`.
    have hDK : IsBrauerEquivalent (CSA.mk (AlgCat.of K D)) (CSA.mk (AlgCat.of K K)) :=
      IsBrauerEquivalent.trans (IsBrauerEquivalent.symm hAD) hBrauer
    rcases (division_algebras_are_similar_iff K D K).1 hDK with ⟨eDK⟩
    -- Replace the division coefficients in the matrix model by `K` itself.
    exact ⟨n, ⟨e.trans (matrix_coeffAlgEquiv (k := K) n eDK)⟩⟩

/-- Helper for Theorem 11.8.2: Brauer-equivalent representatives are split by the same finite
extension. -/
lemma isSplitBy_iff_of_isBrauerEquivalent_via_baseChange {B : CSA.{u, v} k}
    (hAB : IsBrauerEquivalent A B) :
    A.IsSplitBy K ↔ B.IsSplitBy K := by
  -- Rewrite both sides by the base-changed Brauer-class criterion, then transport the class
  -- across scalar extension.
  rw [A.isSplitBy_iff_brauerEquivalent_baseField K, B.isSplitBy_iff_brauerEquivalent_baseField K]
  have hbase : IsBrauerEquivalent (A.baseChange K) (B.baseChange K) :=
    A.isBrauerEquivalent_baseChange K hAB
  constructor
  · intro hSplit
    exact IsBrauerEquivalent.trans (IsBrauerEquivalent.symm hbase) hSplit
  · intro hSplit
    exact IsBrauerEquivalent.trans hbase hSplit

/-- Helper for Theorem 11.8.2: the image field of an embedding `K →ₐ[k] B` has the same
`k`-dimension as `K`. -/
private theorem fieldRange_finrank_eq_of_embedding
    {B : CSA.{u, v} k} (ι : K →ₐ[k] B) :
    Module.finrank k K = Module.finrank k ι.fieldRange := by
  -- Replace the embedded copy of `K` by its canonical image field inside `B`.
  exact (AlgEquiv.ofInjectiveField ι).toLinearEquiv.finrank_eq

/-- Helper for Theorem 11.8.2: the image of an embedded field with the square-dimension formula is
its own centralizer. -/
private theorem fieldRange_centralizer_eq_of_finrank_sq
    {B : CSA.{u, v} k} (ι : K →ₐ[k] B)
    (hdim : Module.finrank k B = Module.finrank k K ^ 2) :
    Subalgebra.centralizer k (ι.fieldRange : Set B) = ι.fieldRange := by
  have hdimRange : Module.finrank k B = Module.finrank k ι.fieldRange ^ 2 := by
    -- Transport the square-dimension formula across the canonical equivalence `K ≃ ι(K)`.
    calc
      Module.finrank k B = Module.finrank k K ^ 2 := hdim
      _ = Module.finrank k ι.fieldRange ^ 2 := by
        rw [fieldRange_finrank_eq_of_embedding (k := k) (K := K) ι]
  have hfield : IsField ι.fieldRange := by infer_instance
  -- Lemma 11.7.3 turns the square-dimension statement into the centralizer computation.
  exact
    ((subfield_tfae_finrank_sq_centralizer_eq_maximal_commutative
      (A := B) ι.fieldRange hfield).out 0 1) hdimRange

/-- Helper for Theorem 11.8.2: the image of an embedded field with the square-dimension formula is
maximal commutative. -/
private theorem fieldRange_isMaximalCommutative_of_finrank_sq
    {B : CSA.{u, v} k} (ι : K →ₐ[k] B)
    (hdim : Module.finrank k B = Module.finrank k K ^ 2) :
    ι.fieldRange.IsMaximalCommutative := by
  have hdimRange : Module.finrank k B = Module.finrank k ι.fieldRange ^ 2 := by
    -- As above, replace `K` by the canonical image field inside `B`.
    calc
      Module.finrank k B = Module.finrank k K ^ 2 := hdim
      _ = Module.finrank k ι.fieldRange ^ 2 := by
        rw [fieldRange_finrank_eq_of_embedding (k := k) (K := K) ι]
  have hfield : IsField ι.fieldRange := by infer_instance
  -- The TFAE from Lemma 11.7.3 packages the same hypothesis as maximal commutativity.
  exact
    ((subfield_tfae_finrank_sq_centralizer_eq_maximal_commutative
      (A := B) ι.fieldRange hfield).out 0 2) hdimRange

/-- Helper for Theorem 11.8.2: a `K`-algebra model of `B.baseChange K` as an endomorphism algebra
already exhibits `K` as a splitting field of `B`. -/
private noncomputable theorem isSplitBy_of_baseChange_algEquiv_moduleEnd
    {B : CSA.{u, v} k} {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (e : B.baseChange K ≃ₐ[K] Module.End K V) :
    B.IsSplitBy K := by
  let b : Basis (Fin (Module.finrank K V)) K V := Module.finBasis K V
  -- Once the base change is identified with `End_K(V)`, choose a finite `K`-basis of `V` and
  -- rewrite endomorphisms as a full matrix algebra.
  refine ⟨Module.finrank K V, ?_⟩
  exact ⟨e.trans (Module.End.algEquivMatrix b)⟩

/-- Helper for Theorem 11.8.2: an embedded field acts on the ambient algebra by right
multiplication. -/
private instance embeddedFieldRightModule {B : CSA.{u, v} k} (ι : K →ₐ[k] B) : Module K B := by
  refine
    { smul := fun c x ↦ x * ι c
      one_smul := ?_
      mul_smul := ?_
      smul_zero := ?_
      smul_add := ?_
      zero_smul := ?_
      add_smul := ?_ }
  · intro x
    simp
  · intro a b x
    rw [show x * ι (a * b) = x * (ι a * ι b) by rw [map_mul]]
    rw [mul_assoc]
    congr 1
    exact mul_comm (ι a) (ι b)
  · intro c
    simp
  · intro c x y
    simp [mul_add]
  · intro x
    simp
  · intro a b x
    simp [add_mul]

/-- Helper for Theorem 11.8.2: the right-multiplication action of an embedded field is compatible
with the original `k`-scalar structure. -/
private instance embeddedFieldRightIsScalarTower {B : CSA.{u, v} k} (ι : K →ₐ[k] B) :
    IsScalarTower k K B := by
  refine ⟨?_⟩
  intro r c x
  calc
    (r • c) • x = x * ι ((algebraMap k K r) * c) := rfl
    _ = x * (algebraMap k B r * ι c) := by rw [map_mul, AlgHom.commutes]
    _ = (x * algebraMap k B r) * ι c := by rw [mul_assoc]
    _ = (algebraMap k B r * x) * ι c := by
          rw [Algebra.commutes (R := k) (A := B) r x]
    _ = r • (c • x) := by rw [Algebra.smul_def, mul_assoc]

/-- Helper for Theorem 11.8.2: left multiplication on `B` is `K`-linear for the right action
coming from an embedded field. -/
private theorem embeddedFieldLeftMulAlgHom {B : CSA.{u, v} k} (ι : K →ₐ[k] B) :
    B →ₐ[k] Module.End K B := by
  refine
    { toFun := fun b ↦
        { toFun := fun x ↦ b * x
          map_add' := ?_
          map_smul' := ?_ }
      map_zero' := ?_
      map_one' := ?_
      map_add' := ?_
      map_mul' := ?_
      commutes' := ?_ }
  · intro x y
    simp [mul_add]
  · intro c x
    change b * (x * ι c) = (b * x) * ι c
    rw [mul_assoc]
  · ext x
    simp
  · ext x
    simp
  · intro b₁ b₂
    ext x
    simp [add_mul]
  · intro b₁ b₂
    ext x
    simp [mul_assoc]
  · intro r
    ext x
    change algebraMap k B r * x = x * ι (algebraMap k K r)
    rw [AlgHom.commutes]
    exact Algebra.commutes (R := k) (A := B) r x

/-- Helper for Theorem 11.8.2: the base change `B ⊗[k] K` acts on `B` by left multiplication on
the `B`-factor and right multiplication on the `K`-factor. -/
private theorem baseChange_action_to_moduleEnd {B : CSA.{u, v} k} (ι : K →ₐ[k] B) :
    B.baseChange K →ₐ[K] Module.End K B := by
  -- The universal property of base change packages the `k`-algebra map given by left
  -- multiplication into a `K`-algebra map from `B.baseChange K`.
  exact (AlgHom.liftEquiv k K B (Module.End K B)) (embeddedFieldLeftMulAlgHom (k := k) (K := K) ι)

/-- Helper for Theorem 11.8.2: if a Brauer-equivalent representative already contains `K` with
the square-dimension condition, then that representative is split by `K`. -/
private theorem isSplitBy_of_embedded_field_centralizer
    {B : CSA.{u, v} k} (ι : K →ₐ[k] B)
    (hdim : Module.finrank k B = Module.finrank k K ^ 2)
    (_hcentralizer : Subalgebra.centralizer k (ι.fieldRange : Set B) = ι.fieldRange) :
    B.IsSplitBy K := by
  letI : FiniteDimensional K B := FiniteDimensional.right k K B
  let φ : B.baseChange K →ₐ[K] Module.End K B :=
    baseChange_action_to_moduleEnd (k := k) (K := K) ι
  have hφ_inj : Function.Injective φ := RingHom.injective φ.toRingHom
  have hfinrankB : Module.finrank K B = Module.finrank k K := by
    -- The square-dimension hypothesis makes `B` a `K`-vector space of dimension `[K : k]`.
    apply Nat.eq_of_mul_eq_mul_left Module.finrank_pos
    calc
      Module.finrank k K * Module.finrank K B = Module.finrank k B := by
        simpa using (Module.finrank_mul_finrank k K B)
      _ = Module.finrank k K ^ 2 := by simpa using hdim
      _ = Module.finrank k K * Module.finrank k K := by rw [pow_two]
  have hφ_dim :
      Module.finrank K (B.baseChange K) = Module.finrank K (Module.End K B) := by
    -- Compare the source and target dimensions over `K`.
    calc
      Module.finrank K (B.baseChange K) = Module.finrank k B := by
        simpa [CSA.baseChange] using (Module.finrank_baseChange (R := K) (S := k) (M' := B))
      _ = Module.finrank k K ^ 2 := by simpa using hdim
      _ = Module.finrank K B * Module.finrank K B := by rw [hfinrankB, pow_two]
      _ = Module.finrank K (Module.End K B) := by
            simpa using (Module.finrank_linearMap K K B B).symm
  have hφ_surj : Function.Surjective φ := by
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hφ_dim).mp hφ_inj
  -- Route correction: replace the earlier centralizer transport loop by the direct action of the
  -- base change on `B`, then finish by dimension comparison.
  exact isSplitBy_of_baseChange_algEquiv_moduleEnd (k := k) (K := K)
    (B := B) (V := B) (AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩)

/-- Helper for Theorem 11.8.2: if a Brauer-equivalent representative already contains `K` with
the square-dimension condition, then that representative is split by `K`. -/
lemma isSplitBy_of_self_embedding_finrank_sq
    {B : CSA.{u, v} k}
    (hK : Nonempty (K →ₐ[k] B))
    (hdim : Module.finrank k B = Module.finrank k K ^ 2) :
    B.IsSplitBy K := by
  rcases hK with ⟨ι⟩
  have hcentralizer :
      Subalgebra.centralizer k (ι.fieldRange : Set B) = ι.fieldRange :=
    fieldRange_centralizer_eq_of_finrank_sq (k := k) (K := K) ι hdim
  -- The square-dimension work is finished above; from here on the proof is exactly the centralizer
  -- model-to-split-model bridge isolated in the dedicated helper.
  exact isSplitBy_of_embedded_field_centralizer (k := k) (K := K) ι hdim hcentralizer

/-- Helper for Theorem 11.8.2: a split model of `A.baseChange K` induces the ambient
`k`-algebra action of `A` on the standard `K`-vector space `Fin n → K`. -/
private theorem split_model_action_to_end
    {n : ℕ} (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    A →ₐ[k] Module.End k (Fin n → K) := by
  let ρK : A.baseChange K →ₐ[K] Module.End K (Fin n → K) :=
    e.trans (Module.End.algEquivMatrix (Pi.basisFun K (Fin n))).symm
  -- First let `A.baseChange K` act through the split matrix model, then forget from `K`-linear
  -- maps to `k`-linear maps.
  refine
    { toFun := fun a ↦
        { toFun := fun v ↦ ρK ((Algebra.TensorProduct.includeRight : A →ₐ[k] A.baseChange K) a) v
          map_add' := by
            intro x y
            simp [ρK]
          map_smul' := by
            intro c v
            simpa [Algebra.smul_def] using
              (ρK ((Algebra.TensorProduct.includeRight : A →ₐ[k] A.baseChange K) a)).map_smul
                ((algebraMap k K) c) v }
      map_zero' := by
        ext v i
        simp [ρK]
      map_one' := by
        ext v i
        simp [ρK]
      map_add' := by
        intro a b
        ext v i
        simp [ρK]
      map_mul' := by
        intro a b
        ext v i
        simp [ρK]
      commutes' := by
        intro c
        ext v i
        simp [ρK, Algebra.algebraMap_eq_smul_one, smul_assoc] }

/-- Helper for Theorem 11.8.2: the ambient `A`-action coming from a split model is `K`-linear,
so scalar endomorphisms lie in its centralizer inside `Module.End k (Fin n → K)`. -/
private theorem split_model_action_commutes_with_scalars
    {n : ℕ} (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K)
    (a : A) (c : K) (v : Fin n → K) :
    split_model_action_to_end (A := A) (K := K) e a (c • v) =
      c • split_model_action_to_end (A := A) (K := K) e a v := by
  let ρK : A.baseChange K →ₐ[K] Module.End K (Fin n → K) :=
    e.trans (Module.End.algEquivMatrix (Pi.basisFun K (Fin n))).symm
  -- Unfold the action back to the underlying `K`-linear endomorphism and use its `K`-linearity.
  simpa [split_model_action_to_end, ρK, Algebra.smul_def] using
    (ρK ((Algebra.TensorProduct.includeRight : A →ₐ[k] A.baseChange K) a)).map_smul c v

/-- Helper for Theorem 11.8.2: scalar endomorphisms of `Fin n → K` define a `K`-subalgebra of the
centralizer of the split-model `A`-action. -/
private theorem split_model_scalar_embedding_to_centralizer
    {n : ℕ} (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Nonempty
      (K →ₐ[k]
        Subalgebra.centralizer k
          ((split_model_action_to_end (A := A) (K := K) e).range :
            Set (Module.End k (Fin n → K)))) := by
  let ρ := split_model_action_to_end (A := A) (K := K) e
  let C := Subalgebra.centralizer k (ρ.range : Set (Module.End k (Fin n → K)))
  -- The source proof inserts `K` into the commutant by scalar endomorphisms of the split module.
  refine ⟨
    { toFun := fun c ↦
        ⟨{ toFun := fun v ↦ c • v
           map_add' := by
             intro x y
             simp [smul_add]
           map_smul' := by
             intro r v
             simp [Algebra.smul_def, smul_assoc, mul_comm] },
          ?_⟩
      map_zero' := by
        ext v i
        simp
      map_one' := by
        ext v i
        simp
      map_add' := by
        intro c d
        ext v i
        simp [add_smul]
      map_mul' := by
        intro c d
        ext v i
        simp [mul_smul]
      commutes' := by
        intro r
        ext v i
        simp [Algebra.smul_def, smul_assoc] }⟩
  -- Every element of the image of `ρ` is `K`-linear, so it commutes with scalar maps.
  rw [Subalgebra.mem_centralizer_iff]
  intro f hf
  rcases hf with ⟨a, rfl⟩
  ext v i
  simpa using (split_model_action_commutes_with_scalars (A := A) (K := K) e a c v).symm

/-- Helper for Theorem 11.8.2: a splitting field produces the textbook commutant witness in the
Brauer class of `A`. -/
private theorem split_model_centralizer_witness
    {n : ℕ} (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    ∃ B : CSA.{u, v} k,
      IsBrauerEquivalent A B ∧
        Nonempty (K →ₐ[k] B) ∧
        Module.finrank k B = Module.finrank k K ^ 2 := by
  -- Route correction: isolate the forward-direction blocker at the actual source witness, namely
  -- the commutant of the `A`-action inside `Module.End k (Fin n → K)`.
  let ρ := split_model_action_to_end (A := A) (K := K) e
  let C := Subalgebra.centralizer k (ρ.range : Set (Module.End k (Fin n → K)))
  have hK :
      Nonempty (K →ₐ[k] C) :=
    split_model_scalar_embedding_to_centralizer (A := A) (K := K) e
  -- TODO: identify `Cᵐᵒᵖ` as a central simple representative, then package the remaining two
  -- source-faithful facts: `A ~ Cᵐᵒᵖ` via the centralizer tensor-product algebra equivalence, and
  -- `Module.finrank k C = Module.finrank k K ^ 2` via the centralizer dimension formula in
  -- `Module.End k (Fin n → K)`.
  sorry

/-- Helper for Theorem 11.8.2: a splitting field produces the textbook commutant witness in the
Brauer class of `A`. -/
lemma forward_commutant_witness_of_split
    (hA : A.IsSplitBy K) :
    ∃ B : CSA.{u, v} k,
      IsBrauerEquivalent A B ∧
        Nonempty (K →ₐ[k] B) ∧
        Module.finrank k B = Module.finrank k K ^ 2 := by
  rcases hA with ⟨n, ⟨e⟩⟩
  -- The public forward helper now reduces immediately to the split-model commutant witness.
  exact split_model_centralizer_witness (A := A) (K := K) e

/-- Helper for Theorem 11.8.2: a representative that already contains `K` with the required
square dimension supplies the existential witness for its own Brauer class. -/
lemma exists_brauerEquivalent_with_subfield_finrank_sq_self
    {B : CSA.{u, v} k}
    (hK : Nonempty (K →ₐ[k] B))
    (hdim : Module.finrank k B = Module.finrank k K ^ 2) :
    ∃ C : CSA.{u, v} k,
      IsBrauerEquivalent B C ∧
        Nonempty (K →ₐ[k] C) ∧
        Module.finrank k C = Module.finrank k K ^ 2 := by
  -- Use the given representative itself; only the Brauer-equivalence bookkeeping is needed.
  exact ⟨B, IsBrauerEquivalent.refl _, hK, hdim⟩

/-- Helper for Theorem 11.8.2: the existential witness predicate is invariant under replacing the
ambient algebra by a Brauer-equivalent representative. -/
lemma exists_brauerEquivalent_with_subfield_finrank_sq_iff_of_isBrauerEquivalent
    {B : CSA.{u, v} k} (hAB : IsBrauerEquivalent A B) :
    (∃ C : CSA.{u, v} k,
      IsBrauerEquivalent A C ∧
        Nonempty (K →ₐ[k] C) ∧
        Module.finrank k C = Module.finrank k K ^ 2) ↔
      ∃ C : CSA.{u, v} k,
        IsBrauerEquivalent B C ∧
          Nonempty (K →ₐ[k] C) ∧
          Module.finrank k C = Module.finrank k K ^ 2 := by
  constructor
  · rintro ⟨C, hAC, hK, hdim⟩
    -- Compose the Brauer-equivalence witnesses to move the ambient class from `A` to `B`.
    exact ⟨C, IsBrauerEquivalent.trans (IsBrauerEquivalent.symm hAB) hAC, hK, hdim⟩
  · rintro ⟨C, hBC, hK, hdim⟩
    -- Compose in the opposite order to move the witness back from `B` to `A`.
    exact ⟨C, IsBrauerEquivalent.trans hAB hBC, hK, hdim⟩

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

/-- Brauer-equivalent finite central simple algebras have the same finite splitting fields. -/
theorem isSplitBy_iff_of_isBrauerEquivalent {B : CSA.{u, v} k}
    (hAB : IsBrauerEquivalent A B) :
    A.IsSplitBy K ↔ B.IsSplitBy K := by
  -- Use the base-changed Brauer-class criterion instead of re-entering the main theorem.
  exact A.isSplitBy_iff_of_isBrauerEquivalent_via_baseChange K hAB

end CSA
