import Mathlib
import Mathlib.LinearAlgebra.Matrix.ToLin
import StacksProject_2024.Chap11.Definition_11_8_1
import StacksProject_2024.Chap11.Lemma_11_5_1
import StacksProject_2024.Chap11.Lemma_11_7_3
import StacksProject_2024.Chap11.Theorem_11_8_2.BaseChangeMatrix

-- Declarations for this theorem-local support file are maintained manually during proof rescue.

/- Domain-style sampling for Theorem 11.8.2 support:
- primary domain: the stable reverse-direction splitness criterion and Brauer-invariance API
  needed downstream from Theorem 11.8.2;
- sampled owner declarations:
  `CSA.IsSplitBy`,
  `CSA.baseChange`,
  `IsBrauerEquivalent`,
  `CSA.baseChange_of_matrix_brauer_witness`;
- best owner abstraction: this file is `core/canonical`; it packages the finished owner-level
  splitness transport API without importing the unfinished forward commutant witness from the
  monolithic theorem file;
- primitive data: a representative `B : CSA k`, a `k`-algebra embedding `K →ₐ[k] B`, the
  square-dimension hypothesis `Module.finrank k B = Module.finrank k K ^ 2`, and Brauer
  equivalence `IsBrauerEquivalent A B`;
- derived API: direct splitness from an embedded field and invariance of splitness under Brauer
  equivalence.

Source/core/bridge triage:
- `source-facing`: none; this is a support file extracted from Theorem 11.8.2;
- `core/canonical`: `CSA.IsSplitBy` and `A.baseChange K`;
- `bridge/view`: Brauer-equivalence transport of splitness and the direct embedded-field split
  criterion. -/

universe u v w z

namespace CSA

open scoped TensorProduct
open Algebra.TensorProduct
open Matrix

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)
variable (K : Type w) [Field K] [Algebra k K] [FiniteDimensional k K]

/-- Helper for Theorem 11.8.2 support: centrality of a matrix algebra forces centrality of its
division coefficients. -/
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

/-- Helper for Theorem 11.8.2 support: a matrix model over a central division algebra packages
the corresponding Brauer-equivalence witness. -/
private theorem matrix_model_isBrauerEquivalent_division
    {k : Type u} [Field k] {B : CSA.{u, v} k} {n : ℕ} [NeZero n] {D : Type v}
    [DivisionRing D] [Algebra k D] [FiniteDimensional k D] [Algebra.IsCentral k D]
    (e : B ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    IsBrauerEquivalent B (CSA.mk (AlgCat.of k D)) := by
  -- Package the direct matrix presentation as the `1 × 1` stabilization witness.
  refine ⟨1, n, one_ne_zero, NeZero.ne n, ?_⟩
  exact ⟨((reindexAlgEquiv k B finOneEquiv).trans uniqueAlgEquiv).trans e⟩

/-- Helper for Theorem 11.8.2 support: a coefficient algebra equivalence induces the
corresponding matrix algebra equivalence by entrywise transport. -/
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

omit [FiniteDimensional k K] in
/-- Helper for Theorem 11.8.2 support: a split base change is Brauer equivalent to the base field
over the extension. -/
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

omit [FiniteDimensional k K] in
/-- Helper for Theorem 11.8.2 support: Brauer equivalence survives scalar extension. -/
lemma isBrauerEquivalent_baseChange {B : CSA.{u, v} k}
    (hAB : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (A.baseChange K) (B.baseChange K) := by
  rcases hAB with ⟨n, m, hn, hm, ⟨e⟩⟩
  -- Route correction: keep the Brauer bookkeeping here minimal and delegate the recurring
  -- scalar-extension/matrix transport to the dedicated base-change helper file.
  refine ⟨n, m, hn, hm, ?_⟩
  exact ⟨A.baseChange_of_matrix_brauer_witness (K := K) e⟩

omit [FiniteDimensional k K] in
/-- Helper for Theorem 11.8.2 support: over the extension field `K`, splitness is equivalent to
Brauer equivalence of `A.baseChange K` with the base field representative. -/
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
    have hDK : IsBrauerEquivalent (CSA.mk (AlgCat.of K D)) (CSA.mk (AlgCat.of K K)) :=
      IsBrauerEquivalent.trans (IsBrauerEquivalent.symm hAD) hBrauer
    letI : Small.{w} D := Small.mk' (Module.finBasis K D).equivFun.toEquiv
    let eShrink : Shrink.{w} D ≃ₐ[K] D := Shrink.algEquiv K D
    letI : Algebra.IsCentral K (Shrink.{w} D) := by
      refine ⟨fun x hx ↦ ?_⟩
      have hx' : eShrink x ∈ Subalgebra.center K D := by
        rw [Subalgebra.mem_center_iff] at hx ⊢
        intro b
        have hcomm : eShrink.symm b * x = x * eShrink.symm b := hx (eShrink.symm b)
        exact by simpa using congrArg eShrink hcomm
      obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff K).1 hx'
      rw [Algebra.mem_bot]
      refine ⟨a, ?_⟩
      have hxe : eShrink x = eShrink (algebraMap K (Shrink.{w} D) a) := by
        simpa using ha
      exact eShrink.injective hxe.symm
    have hShrink :
        IsBrauerEquivalent (CSA.mk (AlgCat.of K (Shrink.{w} D))) (CSA.mk (AlgCat.of K D)) :=
      by
        refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
        exact ⟨((reindexAlgEquiv K (CSA.mk (AlgCat.of K (Shrink.{w} D))) finOneEquiv).trans
          uniqueAlgEquiv).trans <| eShrink.trans <|
            ((reindexAlgEquiv K (CSA.mk (AlgCat.of K D)) finOneEquiv).trans uniqueAlgEquiv).symm⟩
    have hShrinkK :
        IsBrauerEquivalent (CSA.mk (AlgCat.of K (Shrink.{w} D))) (CSA.mk (AlgCat.of K K)) :=
      IsBrauerEquivalent.trans hShrink hDK
    -- The trivial Brauer class forces the coefficient division algebra to be the field `K`.
    rcases (division_algebras_are_similar_iff K K (Shrink.{w} D)).1
        (IsBrauerEquivalent.symm hShrinkK) with ⟨eKD'⟩
    let eKD : K ≃ₐ[K] D := eKD'.trans eShrink
    -- Replace the division coefficients in the matrix model by `K` itself.
    exact ⟨n, ⟨e.trans (matrix_coeffAlgEquiv (k := K) n eKD.symm)⟩⟩

omit [FiniteDimensional k K] in
/-- Helper for Theorem 11.8.2 support: Brauer-equivalent representatives are split by the same
finite extension. -/
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

/-- Helper for Theorem 11.8.2 support: an embedded field of square degree splits the ambient
finite central simple algebra. -/
lemma isSplitBy_of_self_embedding_finrank_sq
    {B : CSA.{u, v} k}
    (hK : Nonempty (K →ₐ[k] B))
    (hdim : Module.finrank k B = Module.finrank k K ^ 2) :
    B.IsSplitBy K := by
  rcases hK with ⟨ι⟩
  letI : Module K B :=
    { smul := fun c x ↦ x * ι c
      one_smul := by
        intro x
        change x * ι 1 = x
        simp
      mul_smul := by
        intro a b x
        change x * ι (a * b) = (x * ι b) * ι a
        have hcomm : ι a * ι b = ι b * ι a := by
          simpa [map_mul] using congrArg ι (mul_comm a b)
        rw [map_mul, mul_assoc, hcomm]
      smul_zero := by
        intro c
        change (0 : B) * ι c = 0
        simp
      smul_add := by
        intro c x y
        change (x + y) * ι c = x * ι c + y * ι c
        rw [add_mul]
      zero_smul := by
        intro x
        change x * ι 0 = 0
        simp
      add_smul := by
        intro a b x
        change x * ι (a + b) = x * ι a + x * ι b
        rw [map_add, mul_add] }
  letI : IsScalarTower k K B :=
    ⟨fun r c x ↦ by
      -- Expand both scalar actions into multiplication via the field embedding.
      calc
        (r • c) • x = x * ι ((algebraMap k K r) * c) := by
          rw [Algebra.smul_def]
          rfl
        _ = x * (algebraMap k B r * ι c) := by rw [map_mul, AlgHom.commutes]
        _ = (x * algebraMap k B r) * ι c := by rw [mul_assoc]
        _ = (algebraMap k B r * x) * ι c := by
              rw [(Algebra.commutes (R := k) (A := B) r x).symm]
        _ = (algebraMap k B r) * (x * ι c) := by rw [← mul_assoc]
        _ = r • c • x := by
          rw [Algebra.smul_def]
          change (algebraMap k B r) * (x * ι c) = (algebraMap k B r) * (x * ι c)
          rfl⟩
  letI : FiniteDimensional K B := FiniteDimensional.right k K B
  let ψ : B →ₐ[k] Module.End K B := by
    -- Package left multiplication into the universal `Module.End` algebra.
    refine
      { toFun := fun b ↦
          { toFun := fun x ↦ b * x
            map_add' := by
              intro x y
              rw [mul_add]
            map_smul' := by
              intro c x
              change b * (x * ι c) = (b * x) * ι c
              rw [mul_assoc] }
        map_zero' := by
          ext x
          simp
        map_one' := by
          ext x
          simp
        map_add' := by
          intro b₁ b₂
          ext x
          change (b₁ + b₂) * x = b₁ * x + b₂ * x
          rw [add_mul]
        map_mul' := by
          intro b₁ b₂
          ext x
          change b₁ * b₂ * x = b₁ * (b₂ * x)
          rw [mul_assoc]
        commutes' := by
          intro r
          ext x
          change (algebraMap k B r) * x = r • x
          rw [Algebra.smul_def] }
  let φ : B.baseChange K →ₐ[K] Module.End K B :=
    (AlgHom.liftEquiv k K B (Module.End K B))
      ψ
  have hφ_inj : Function.Injective φ := RingHom.injective φ.toRingHom
  have hfinrankB : Module.finrank K B = Module.finrank k K := by
    -- Compare the two ways of computing `[B : k]`.
    apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := k) (M := K))
    calc
      Module.finrank k K * Module.finrank K B = Module.finrank k B := by
        simpa using (Module.finrank_mul_finrank k K B)
      _ = Module.finrank k K ^ 2 := by simpa using hdim
      _ = Module.finrank k K * Module.finrank k K := by rw [pow_two]
  have hφ_dim :
      Module.finrank K (B.baseChange K) = Module.finrank K (Module.End K B) := by
    -- Rewrite both sides as the same square dimension over `K`.
    calc
      Module.finrank K (B.baseChange K) = Module.finrank k B := by
        change Module.finrank K (K ⊗[k] B) = Module.finrank k B
        exact Module.finrank_baseChange (R := K) (S := k) (M' := B)
      _ = Module.finrank k K ^ 2 := by simpa using hdim
      _ = Module.finrank K B * Module.finrank K B := by rw [hfinrankB, pow_two]
      _ = Module.finrank K (Module.End K B) := by
            simpa using (Module.finrank_linearMap K K B B).symm
  have hφ_surj : Function.Surjective φ := by
    let φₗ : B.baseChange K →ₗ[K] Module.End K B := φ.toLinearMap
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hφ_dim).mp hφ_inj
  let b : Module.Basis (Fin (Module.finrank K B)) K B := Module.finBasis K B
  -- Identify the base change with the endomorphism algebra and then with matrices.
  refine ⟨Module.finrank K B, ?_⟩
  exact ⟨(AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩).trans (algEquivMatrix b)⟩

omit [FiniteDimensional k K] in
/-- Brauer-equivalent finite central simple algebras have the same finite splitting fields. -/
theorem isSplitBy_iff_of_isBrauerEquivalent {B : CSA.{u, v} k}
    (hAB : IsBrauerEquivalent A B) :
    A.IsSplitBy K ↔ B.IsSplitBy K := by
  -- Use the base-changed Brauer-class criterion instead of re-entering the unfinished forward
  -- implication of Theorem 11.8.2.
  exact A.isSplitBy_iff_of_isBrauerEquivalent_via_baseChange K hAB

end

end CSA
