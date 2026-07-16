import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.RealizationCore
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.BrauerRelationSeparator
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.TracelessCommutator

/-!
Support for Serre part `(b)` of Theorem 18-18.2-1, over the residue field itself.

This file connects the tautological Brauer character over `k` with honest traces, and upgrades
the Jacobson-density machinery of `BrauerRelationSeparator` from the trace-one separator to the
realization of an arbitrary base-field endomorphism of a chosen simple factor (acting as zero on
the other supported factors).
-/

noncomputable section

universe u x

open CategoryTheory
open scoped Representation

namespace Representation

variable {p : ℕ} [Fact p.Prime]
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

section TraceIdentity

/-- Over `k` itself, the Brauer character with the tautological lift is the honest trace. -/
theorem modularCharacter_value_eq_trace
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (t : { g : G // IsPRegular p g }) :
    modularCharacter (fun y : PrimeToPRoot p k ↦ ((y : kˣ) : k)) ρ t =
      LinearMap.trace k V (ρ t.1) := by
  rw [modularCharacter_eq_roots_sum (p := p) (k := k) (G := G)
    (lift := fun y : PrimeToPRoot p k ↦ ((y : kˣ) : k)) (f := fun μ ↦ μ) (fun y ↦ rfl) ρ t]
  rw [LinearMap.trace_eq_matrix_trace k (Module.Free.chooseBasis k V) (ρ t.1),
    Matrix.trace_eq_sum_roots_charpoly]
  rw [Multiset.map_id']
  rfl

end TraceIdentity

section BlockRealization

/-- A basis of the module synonym of a finite-dimensional representation. -/
private def asModuleBasisLocal (E : FDRep k G) :
    Module.Basis (Module.Basis.ofVectorSpaceIndex k E.V) k (asModule E.ρ) :=
  (Module.Basis.ofVectorSpace k E.V).map (Representation.asModuleEquiv E.ρ).symm

@[simp] private theorem asModuleEquiv_asModuleBasisLocal (E : FDRep k G)
    (b : Module.Basis.ofVectorSpaceIndex k E.V) :
    Representation.asModuleEquiv E.ρ (asModuleBasisLocal E b) =
      Module.Basis.ofVectorSpace k E.V b := by
  rfl

/-- The coordinatewise basis of a finite support product of module synonyms. -/
private def supportProductBasisLocal (E : ι → FDRep k G) (s : Finset ι) :
    Module.Basis
      (Sigma fun a : s.attach ↦ Module.Basis.ofVectorSpaceIndex k (E a.1).V)
      k (∀ a : s.attach, asModule (E a.1).ρ) :=
  Pi.basis fun a ↦ asModuleBasisLocal (E a.1)

/-- Jacobson density realizes any base-field endomorphism of one simple supported factor by an
element of `k[G]` acting as zero on every other supported factor. -/
theorem exists_realizing_single_block
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    (s : Finset ι) {i : ι} (hi : i ∈ s)
    (uV : Module.End k (E i).V) :
    ∃ t : MonoidAlgebra k G,
      Representation.asAlgebraHom (E i).ρ t = uV ∧
        ∀ j ∈ s, j ≠ i → Representation.asAlgebraHom (E j).ρ t = 0 := by
  classical
  let i' : s.attach := ⟨⟨i, hi⟩, by simp⟩
  letI : DecidableEq ι := Classical.decEq ι
  letI : Simple (E i) := hE_simple i
  let ρi : Representation k G (E i) := (E i).ρ
  letI : Representation.IsIrreducible ρi := by
    simpa [ρi] using (FDRep.isIrreducible_of_simple (E i))
  let baseModEi : Module k (asModule (E i).ρ) := Representation.instModuleAsModule (E i).ρ
  letI : Module k (asModule (E i).ρ) := baseModEi
  let e0 : asModule (E i).ρ ≃ₗ[k] E i := Representation.asModuleEquiv (E i).ρ
  let u : Module.End k (asModule (E i).ρ) := e0.symm.conj uV
  letI (a : s.attach) : Module (MonoidAlgebra k G) (asModule (E a.1).ρ) :=
    Representation.instModuleMonoidAlgebraAsModule (ρ := (E a.1).ρ)
  letI : Module (MonoidAlgebra k G) (∀ a : s.attach, asModule (E a.1).ρ) :=
    Pi.module s.attach (fun a : s.attach ↦ asModule (E a.1).ρ) (MonoidAlgebra k G)
  let q :
      Module.End
        (Module.End (MonoidAlgebra k G) (∀ a : s.attach, asModule (E a.1).ρ))
        (∀ a : s.attach, asModule (E a.1).ρ) :=
    support_product_baseFieldBlockEndomorphism_is_EndLinear_local
      (E := E) hE_simple hE_pairwise (s := s) i' u
  let B := supportProductBasisLocal (k := k) (G := G) E s
  let sample : Finset (∀ a : s.attach, asModule (E a.1).ρ) := Finset.univ.image B
  obtain ⟨t, ht⟩ :=
    @jacobson_density
      (MonoidAlgebra k G) _ (∀ a : s.attach, asModule (E a.1).ρ) _
      (support_product_module_local (E := E) (s := s))
      (support_product_isSemisimpleModule_local (k := k) (G := G) E hE_simple s)
      q sample
  refine ⟨t, ?_, ?_⟩
  · let eρi : asModule (E i).ρ ≃ₗ[k] (E i).V := Representation.asModuleEquiv (E i).ρ
    have hself :
        Representation.asAlgebraHom (E i).ρ t = eρi.conj u := by
      apply (Module.Basis.ofVectorSpace k (E i).V).ext
      intro b
      have hbasis :
          q (B ⟨i', b⟩) = t • B ⟨i', b⟩ :=
        ht (B ⟨i', b⟩) (by simp [sample])
      have hbasis_i := congrArg (fun x ↦ x i') hbasis
      have hcoord :
          Representation.asModuleEquiv (E i).ρ (q (B ⟨i', b⟩) i') =
            ((Representation.asAlgebraHom (E i).ρ) t)
              (Representation.asModuleEquiv (E i).ρ ((B ⟨i', b⟩) i')) := by
        simpa [Representation.asModuleEquiv_map_smul] using
          congrArg (Representation.asModuleEquiv (E i).ρ) hbasis_i
      have hqsingle :=
        support_product_baseFieldBlockEndomorphism_single_self_local
          (E := E) hE_simple hE_pairwise (s := s) i' u
          (asModuleBasisLocal (E i) b)
      have hbasis_vector :
          B ⟨i', b⟩ =
            LinearMap.single (MonoidAlgebra k G)
              (fun a : s.attach ↦ asModule (E a.1).ρ) i'
              (asModuleBasisLocal (E i) b) := by
        simp [B, supportProductBasisLocal, i']
      have hqcoord :
          q (B ⟨i', b⟩) i' = u (asModuleBasisLocal (E i) b) := by
        rw [hbasis_vector]
        change (support_product_baseFieldBlockEndomorphism_is_EndLinear_local
            (E := E) hE_simple hE_pairwise (s := s) i' u
            (LinearMap.single (MonoidAlgebra k G)
              (fun a : s.attach ↦ asModule (E a.1).ρ) i'
              (asModuleBasisLocal (E i) b))) i' =
          u (asModuleBasisLocal (E i) b)
        have hqsingle_i := congrArg (fun y ↦ y i') hqsingle
        have hsingle_apply :
            (LinearMap.single (MonoidAlgebra k G)
              (fun a : s.attach ↦ asModule (E a.1).ρ) i'
              (u (asModuleBasisLocal (E i) b))) i' =
            u (asModuleBasisLocal (E i) b) := by
          simp [LinearMap.single_apply]
        exact hqsingle_i.trans hsingle_apply
      have hu_basis :
          Representation.asModuleEquiv (E i).ρ (u (asModuleBasisLocal (E i) b)) =
            uV ((Module.Basis.ofVectorSpace k (E i).V) b) := by
        simp [u, e0, LinearEquiv.conj_apply]
      have hfinal :
          uV ((Module.Basis.ofVectorSpace k (E i).V) b) =
            ((Representation.asAlgebraHom (E i).ρ) t)
              ((Module.Basis.ofVectorSpace k (E i).V) b) := by
        calc
          uV ((Module.Basis.ofVectorSpace k (E i).V) b) =
              Representation.asModuleEquiv (E i).ρ (q (B ⟨i', b⟩) i') := by
                rw [hqcoord, hu_basis]
          _ = ((Representation.asAlgebraHom (E i).ρ) t)
                (Representation.asModuleEquiv (E i).ρ ((B ⟨i', b⟩) i')) := hcoord
          _ = ((Representation.asAlgebraHom (E i).ρ) t)
                ((Module.Basis.ofVectorSpace k (E i).V) b) := by
                simp [B, supportProductBasisLocal, i',
                  asModuleEquiv_asModuleBasisLocal]
      simpa [u, e0, eρi, LinearEquiv.conj_apply] using hfinal.symm
    have hu_eq : eρi.conj u = uV := by
      ext x
      simp [u, e0, eρi, LinearEquiv.conj_apply]
    rw [hself, hu_eq]
  · intro j hj hji
    let j' : s.attach := ⟨⟨j, hj⟩, by simp⟩
    have hji' : j' ≠ i' := by
      intro h
      apply hji
      exact congrArg (fun x : s.attach ↦ (x.1 : ι)) h
    apply (Module.Basis.ofVectorSpace k (E j).V).ext
    intro b
    have hbasis :
        q (B ⟨j', b⟩) = t • B ⟨j', b⟩ :=
      ht (B ⟨j', b⟩) (by simp [sample])
    have hbasis_j := congrArg (fun x ↦ x j') hbasis
    have hcoord :
        Representation.asModuleEquiv (E j).ρ (q (B ⟨j', b⟩) j') =
          ((Representation.asAlgebraHom (E j).ρ) t)
            (Representation.asModuleEquiv (E j).ρ ((B ⟨j', b⟩) j')) := by
      simpa [Representation.asModuleEquiv_map_smul] using
        congrArg (Representation.asModuleEquiv (E j).ρ) hbasis_j
    have hqzero :=
      support_product_baseFieldBlockEndomorphism_single_offDiag_local
        (E := E) hE_simple hE_pairwise (s := s) i' j' hji' u
        (asModuleBasisLocal (E j) b)
    have hbasis_vector :
        B ⟨j', b⟩ =
          LinearMap.single (MonoidAlgebra k G)
            (fun a : s.attach ↦ asModule (E a.1).ρ) j'
            (asModuleBasisLocal (E j) b) := by
      simp [B, supportProductBasisLocal, j']
    have hqcoord :
        q (B ⟨j', b⟩) j' = 0 := by
      rw [hbasis_vector]
      change (support_product_baseFieldBlockEndomorphism_is_EndLinear_local
          (E := E) hE_simple hE_pairwise (s := s) i' u
          (LinearMap.single (MonoidAlgebra k G)
            (fun a : s.attach ↦ asModule (E a.1).ρ) j'
            (asModuleBasisLocal (E j) b))) j' = 0
      simpa using congrArg (fun y ↦ y j') hqzero
    have hfinal :
        0 =
          ((Representation.asAlgebraHom (E j).ρ) t)
            ((Module.Basis.ofVectorSpace k (E j).V) b) := by
      calc
        0 = Representation.asModuleEquiv (E j).ρ (q (B ⟨j', b⟩) j') := by
              rw [hqcoord]
              simp
        _ = ((Representation.asAlgebraHom (E j).ρ) t)
              (Representation.asModuleEquiv (E j).ρ ((B ⟨j', b⟩) j')) := hcoord
        _ = ((Representation.asAlgebraHom (E j).ρ) t)
              ((Module.Basis.ofVectorSpace k (E j).V) b) := by
              simp [B, supportProductBasisLocal, j',
                asModuleEquiv_asModuleBasisLocal]
    simpa using hfinal.symm

end BlockRealization

section ActionAnnihilation

open MonoidAlgebra in
/-- Helper for Theorem 18-18.2-1: the canonical representation attached to a `k[G]`-module acts
by the module structure. -/
private theorem ofModule'_asAlgebraHom_apply_groupAlgebra_local
    (M : Type u) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
    [IsScalarTower k (MonoidAlgebra k G) M]
    (r : MonoidAlgebra k G) (m : M) :
    ((Representation.ofModule' (k := k) (G := G) M).asAlgebraHom r) m = r • m := by
  refine MonoidAlgebra.induction_on
    (p := fun s : MonoidAlgebra k G ↦
      ((Representation.ofModule' (k := k) (G := G) M).asAlgebraHom s) m = s • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

/-- Helper for Theorem 18-18.2-1: the module synonym of `Representation.ofModule' M` is the
original module. -/
private theorem nonempty_ofModule'_asModuleLinearEquiv_groupAlgebra_local
    (M : Type u) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
    [IsScalarTower k (MonoidAlgebra k G) M] :
    Nonempty
      ((Representation.ofModule' (k := k) (G := G) M).asModule ≃ₗ[MonoidAlgebra k G] M) := by
  let toFun : (Representation.ofModule' (k := k) (G := G) M).asModule → M :=
    fun x ↦ (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x
  let invFun : M → (Representation.ofModule' (k := k) (G := G) M).asModule :=
    fun x ↦ (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv.symm x
  have hsmul : ∀ (r : MonoidAlgebra k G) x, toFun (r • x) = r • toFun x := by
    intro r x
    calc
      (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv (r • x)
          = ((Representation.ofModule' (k := k) (G := G) M).asAlgebraHom r)
              ((Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x) := by
            simpa using
              (Representation.asModuleEquiv_map_smul
                (ρ := Representation.ofModule' (k := k) (G := G) M) r x)
      _ = r • (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x := by
            simpa [toFun] using
              (ofModule'_asAlgebraHom_apply_groupAlgebra_local (k := k) (G := G) M r
                ((Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x))
  exact ⟨{
    toFun := toFun
    invFun := invFun
    left_inv := fun x ↦ by simp [toFun, invFun]
    right_inv := fun x ↦ by simp [toFun, invFun]
    map_add' := fun x y ↦ rfl
    map_smul' := hsmul }⟩

/-- Helper for Theorem 18-18.2-1: a simple `k[G]`-module gives an irreducible representation. -/
private theorem ofModule'_isIrreducible_of_isSimpleModule_groupAlgebra_local
    (M : Type u) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
    [IsScalarTower k (MonoidAlgebra k G) M]
    [IsSimpleModule (MonoidAlgebra k G) M] :
    (Representation.ofModule' (k := k) (G := G) M).IsIrreducible := by
  rcases nonempty_ofModule'_asModuleLinearEquiv_groupAlgebra_local (k := k) (G := G) M with
    ⟨eM⟩
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule
      (Representation.ofModule' (k := k) (G := G) M)).2
      (@IsSimpleModule.congr (MonoidAlgebra k G) inferInstance
        ((Representation.ofModule' (k := k) (G := G) M).asModule)
        (Representation.ofModule' (k := k) (G := G) M).instAddCommGroupAsModule
        (Representation.ofModule' (k := k) (G := G) M).instModuleMonoidAlgebraAsModule
        M inferInstance inferInstance eM inferInstance)

/-- Helper: zero actions transport along isomorphisms of representations. -/
private theorem asAlgebraHom_eq_zero_of_iso {V W : FDRep k G} (e : V ≅ W)
    {x : MonoidAlgebra k G}
    (hW : Representation.asAlgebraHom W.ρ x = 0) :
    Representation.asAlgebraHom V.ρ x = 0 := by
  have hconj :
      Representation.asAlgebraHom V.ρ x =
        ((FDRep.isoToLinearEquiv e).symm.conj) (Representation.asAlgebraHom W.ρ x) := by
    refine MonoidAlgebra.induction_on
      (p := fun y : MonoidAlgebra k G ↦
        Representation.asAlgebraHom V.ρ y =
          ((FDRep.isoToLinearEquiv e).symm.conj) (Representation.asAlgebraHom W.ρ y)) x ?_ ?_ ?_
    · intro g
      simp only [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one]
      rw [FDRep.Iso.conj_ρ e g]
      ext v
      simp [LinearEquiv.conj_apply]
    · intro a b ha hb
      rw [map_add, map_add, ha, hb, map_add]
    · intro r a ha
      rw [map_smul, map_smul, ha, map_smul]
  rw [hconj, hW, map_zero]

/-- If an element of the group algebra acts as zero on every member of a complete irreducible
family, it lies in every maximal left ideal, hence in the (nilpotent) Jacobson radical. -/
theorem isNilpotent_of_forall_asAlgebraHom_eq_zero
    (E : ι → FDRep k G) (hE_complete : IsCompleteIrreducibleFamily E)
    {x : MonoidAlgebra k G}
    (hx : ∀ j, Representation.asAlgebraHom (E j).ρ x = 0) :
    IsNilpotent x := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  haveI hfinKG : Module.Finite k (MonoidAlgebra k G) :=
    Module.Finite.equiv (Finsupp.linearEquivFunOnFinite k k G).symm
  -- `x` lies in every maximal left ideal of `k[G]`.
  have hjac : x ∈ Ideal.jacobson (⊥ : Ideal (MonoidAlgebra k G)) := by
    rw [Ideal.jacobson]
    rw [Submodule.mem_sInf]
    rintro m ⟨-, hmax⟩
    haveI : IsSimpleModule (MonoidAlgebra k G) (MonoidAlgebra k G ⧸ m) := by
      rw [isSimpleModule_iff_isCoatom]
      exact hmax.out
    haveI : FiniteDimensional k (MonoidAlgebra k G ⧸ m) :=
      Module.Finite.of_surjective ((m.mkQ).restrictScalars k)
        (Submodule.mkQ_surjective m)
    have hirr := ofModule'_isIrreducible_of_isSimpleModule_groupAlgebra_local (k := k) (G := G)
      (MonoidAlgebra k G ⧸ m)
    obtain ⟨j, ⟨e⟩⟩ :=
      IsCompleteIrreducibleFamily.exists_iso_of_representation E hE_complete
        (Representation.ofModule' (k := k) (G := G) (MonoidAlgebra k G ⧸ m)) hirr
    have hzero : Representation.asAlgebraHom
        (FDRep.of (Representation.ofModule' (k := k) (G := G)
          (MonoidAlgebra k G ⧸ m))).ρ x = 0 :=
      asAlgebraHom_eq_zero_of_iso e (hx j)
    have happly :
        Representation.asAlgebraHom
          (Representation.ofModule' (k := k) (G := G) (MonoidAlgebra k G ⧸ m)) x
          (Submodule.Quotient.mk (1 : MonoidAlgebra k G)) = 0 := by
      have hofρ :
          Representation.asAlgebraHom
            (FDRep.of (Representation.ofModule' (k := k) (G := G)
              (MonoidAlgebra k G ⧸ m))).ρ x =
            Representation.asAlgebraHom
              (Representation.ofModule' (k := k) (G := G) (MonoidAlgebra k G ⧸ m)) x := by
        rfl
      rw [← hofρ, hzero]
      rfl
    have hsmul :
        (x • (Submodule.Quotient.mk (1 : MonoidAlgebra k G) : MonoidAlgebra k G ⧸ m)) = 0 := by
      rw [← ofModule'_asAlgebraHom_apply_groupAlgebra_local (k := k) (G := G) _ x
        (Submodule.Quotient.mk (1 : MonoidAlgebra k G))]
      exact happly
    have hx_mem : x ∈ m := by
      rwa [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
        Submodule.Quotient.mk_eq_zero] at hsmul
    exact hx_mem
  -- The Jacobson radical of the Artinian group algebra is nilpotent.
  haveI hart : IsArtinianRing (MonoidAlgebra k G) := by
    haveI : IsArtinian k (MonoidAlgebra k G) := inferInstance
    show IsArtinian (MonoidAlgebra k G) (MonoidAlgebra k G)
    exact isArtinian_of_tower k inferInstance
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := MonoidAlgebra k G)
  refine ⟨n, ?_⟩
  have hxpow : x ^ n ∈ (Ideal.jacobson (⊥ : Ideal (MonoidAlgebra k G))) ^ n :=
    Ideal.pow_mem_pow hjac n
  rw [hn] at hxpow
  simpa using hxpow

end ActionAnnihilation

section CommutatorRealization

/-- If an element of `k[G]` has trace zero on every member of a finite pairwise-nonisomorphic
simple family, it differs from a sum of additive commutators by an element acting as zero on the
whole family. -/
theorem exists_commutator_realization_of_traces_zero
    [Fintype ι]
    (E : ι → FDRep k G) (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    (u : MonoidAlgebra k G)
    (htr : ∀ j, LinearMap.trace k (E j).V (Representation.asAlgebraHom (E j).ρ u) = 0) :
    ∃ v ∈ AddSubgroup.closure
        {z : MonoidAlgebra k G | ∃ a b : MonoidAlgebra k G, z = a * b - b * a},
      ∀ j, Representation.asAlgebraHom (E j).ρ (u - v) = 0 := by
  classical
  have hdec := fun j ↦ end_trace_zero_eq_sum_commutators
    (Representation.asAlgebraHom (E j).ρ u) (htr j)
  choose L hL using hdec
  have hreal : ∀ (j : ι) (f : Module.End k (E j).V),
      ∃ t : MonoidAlgebra k G, Representation.asAlgebraHom (E j).ρ t = f ∧
        ∀ j', j' ≠ j → Representation.asAlgebraHom (E j').ρ t = 0 := by
    intro j f
    obtain ⟨t, h1, h2⟩ := exists_realizing_single_block E hE_simple hE_pairwise Finset.univ
      (Finset.mem_univ j) f
    exact ⟨t, h1, fun j' hj' ↦ h2 j' (Finset.mem_univ j') hj'⟩
  choose realize hreal1 hreal2 using hreal
  set vj : ι → MonoidAlgebra k G := fun j ↦
    ((L j).map fun fg ↦
      realize j fg.1 * realize j fg.2 - realize j fg.2 * realize j fg.1).sum
    with hvjdef
  refine ⟨∑ j, vj j, ?_, ?_⟩
  · refine AddSubgroup.sum_mem _ ?_
    intro j _
    rw [hvjdef]
    refine AddSubgroup.list_sum_mem _ ?_
    intro z hz
    rw [List.mem_map] at hz
    obtain ⟨fg, _, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨_, _, rfl⟩
  · intro j'
    have hvj_zero : ∀ j, j ≠ j' → Representation.asAlgebraHom (E j').ρ (vj j) = 0 := by
      intro j hj
      rw [hvjdef]
      rw [map_list_sum]
      refine List.sum_eq_zero ?_
      intro z hz
      rw [List.map_map, List.mem_map] at hz
      obtain ⟨fg, _, rfl⟩ := hz
      have hz1 : Representation.asAlgebraHom (E j').ρ (realize j fg.1) = 0 :=
        hreal2 j fg.1 j' (Ne.symm hj)
      have hz2 : Representation.asAlgebraHom (E j').ρ (realize j fg.2) = 0 :=
        hreal2 j fg.2 j' (Ne.symm hj)
      show Representation.asAlgebraHom (E j').ρ
          (realize j fg.1 * realize j fg.2 - realize j fg.2 * realize j fg.1) = 0
      rw [map_sub, map_mul, map_mul, hz1, hz2]
      simp
    have hvj_self : Representation.asAlgebraHom (E j').ρ (vj j') =
        Representation.asAlgebraHom (E j').ρ u := by
      rw [hvjdef]
      rw [map_list_sum, List.map_map]
      rw [hL j']
      congr 1
      refine List.map_congr_left ?_
      intro fg _
      show Representation.asAlgebraHom (E j').ρ
          (realize j' fg.1 * realize j' fg.2 - realize j' fg.2 * realize j' fg.1) =
        fg.1 * fg.2 - fg.2 * fg.1
      rw [map_sub, map_mul, map_mul, hreal1 j' fg.1, hreal1 j' fg.2]
    have hsum : Representation.asAlgebraHom (E j').ρ (∑ j, vj j) =
        Representation.asAlgebraHom (E j').ρ u := by
      rw [map_sum]
      rw [Finset.sum_eq_single j']
      · exact hvj_self
      · intro j _ hj
        exact hvj_zero j hj
      · intro h
        exact absurd (Finset.mem_univ j') h
    rw [map_sub, hsum, sub_self]

end CommutatorRealization

section ClassCoefficientFunctional

/-- The sum of the coefficients of a group-algebra element over one conjugacy class. -/
noncomputable def classCoeffSum (cc : ConjClasses G) :
    MonoidAlgebra k G →ₗ[k] k where
  toFun x := ∑ g ∈ (Set.toFinite cc.carrier).toFinset, x g
  map_add' x y := by
    simp [Finset.sum_add_distrib]
  map_smul' r x := by
    simp [Finset.mul_sum]

open scoped Classical in
theorem classCoeffSum_single (cc : ConjClasses G) (g : G) (r : k) :
    classCoeffSum (k := k) cc (MonoidAlgebra.single g r) =
      if g ∈ cc.carrier then r else 0 := by
  show (∑ h ∈ (Set.toFinite cc.carrier).toFinset, MonoidAlgebra.single g r h) = _
  by_cases hg : g ∈ cc.carrier
  · rw [if_pos hg]
    rw [Finset.sum_eq_single g]
    · simp [MonoidAlgebra.single_apply]
    · intro h _ hhg
      simp [MonoidAlgebra.single_apply, Ne.symm hhg]
    · intro hnot
      exact absurd ((Set.toFinite cc.carrier).mem_toFinset.mpr hg) hnot
  · rw [if_neg hg]
    refine Finset.sum_eq_zero ?_
    intro h hh
    have hhg : h ≠ g := by
      intro rfl_eq
      exact hg (by simpa using (Set.toFinite cc.carrier).mem_toFinset.mp (rfl_eq ▸ hh))
    simp [MonoidAlgebra.single_apply, Ne.symm hhg]

/-- The class-coefficient functional kills additive commutators of the group algebra. -/
theorem classCoeffSum_commutator (cc : ConjClasses G) (x y : MonoidAlgebra k G) :
    classCoeffSum (k := k) cc (x * y - y * x) = 0 := by
  classical
  -- bilinear reduction to single basis vectors
  have hsingle : ∀ (g h : G) (r s : k),
      classCoeffSum (k := k) cc
        (MonoidAlgebra.single g r * MonoidAlgebra.single h s -
          MonoidAlgebra.single h s * MonoidAlgebra.single g r) = 0 := by
    intro g h r s
    rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single]
    rw [map_sub, classCoeffSum_single, classCoeffSum_single]
    have hconj : g * h ∈ cc.carrier ↔ h * g ∈ cc.carrier := by
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mem_carrier_iff_mk_eq]
      constructor
      · intro hgh
        rw [← hgh]
        exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g, by group⟩)
      · intro hhg
        rw [← hhg]
        exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h, by group⟩)
    by_cases hgh : g * h ∈ cc.carrier
    · rw [if_pos hgh, if_pos (hconj.mp hgh), mul_comm r s, sub_self]
    · rw [if_neg hgh, if_neg (fun h' ↦ hgh (hconj.mpr h')), sub_self]
  -- extend bilinearly
  have hleft : ∀ (x y : MonoidAlgebra k G),
      classCoeffSum (k := k) cc (x * y - y * x) = 0 := by
    intro x y
    refine MonoidAlgebra.induction_on
      (p := fun x : MonoidAlgebra k G ↦
        classCoeffSum (k := k) cc (x * y - y * x) = 0) x ?_ ?_ ?_
    · intro g
      refine MonoidAlgebra.induction_on
        (p := fun y : MonoidAlgebra k G ↦
          classCoeffSum (k := k) cc
            (MonoidAlgebra.of k G g * y - y * MonoidAlgebra.of k G g) = 0) y ?_ ?_ ?_
      · intro h
        simpa [MonoidAlgebra.of_apply] using hsingle g h 1 1
      · intro a b ha hb
        have : MonoidAlgebra.of k G g * (a + b) - (a + b) * MonoidAlgebra.of k G g =
            (MonoidAlgebra.of k G g * a - a * MonoidAlgebra.of k G g) +
              (MonoidAlgebra.of k G g * b - b * MonoidAlgebra.of k G g) := by
          noncomm_ring
        rw [this, map_add, ha, hb, add_zero]
      · intro r a ha
        have : MonoidAlgebra.of k G g * (r • a) - (r • a) * MonoidAlgebra.of k G g =
            r • (MonoidAlgebra.of k G g * a - a * MonoidAlgebra.of k G g) := by
          rw [smul_sub, mul_smul_comm, smul_mul_assoc]
        rw [this, map_smul, ha, smul_zero]
    · intro a b ha hb
      have : (a + b) * y - y * (a + b) =
          (a * y - y * a) + (b * y - y * b) := by noncomm_ring
      rw [this, map_add, ha, hb, add_zero]
    · intro r a ha
      have : (r • a) * y - y * (r • a) = r • (a * y - y * a) := by
        rw [smul_sub, smul_mul_assoc, mul_smul_comm]
      rw [this, map_smul, ha, smul_zero]
  exact hleft x y

/-- The class-coefficient functional kills the whole additive commutator subgroup. -/
theorem classCoeffSum_eq_zero_of_mem_commutator (cc : ConjClasses G)
    {z : MonoidAlgebra k G}
    (hz : z ∈ AddSubgroup.closure
      {w : MonoidAlgebra k G | ∃ a b : MonoidAlgebra k G, w = a * b - b * a}) :
    classCoeffSum (k := k) cc z = 0 := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
      obtain ⟨a, b, rfl⟩ := hw
      exact classCoeffSum_commutator cc a b
  | zero => simp
  | add a b _ _ ha hb =>
      rw [map_add, ha, hb, add_zero]
  | neg a _ ha =>
      rw [map_neg, ha, neg_zero]

end ClassCoefficientFunctional

end Representation
