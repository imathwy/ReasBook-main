import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_2
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_5
import StacksProject_2024.stacks_project.Chap10.Lemma_10_143_9
import StacksProject_2024.stacks_project.Chap15.Definition_15_105_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_6
import StacksProject_2024.stacks_project.Chap15.Lemma_15_105_7
import StacksProject_2024.stacks_project.Chap15.Lemma_15_105_5
import StacksProject_2024.stacks_project.Chap15.Lemma_15_105_9
import StacksProject_2024.stacks_project.Chap15.Lemma_15_105_16
import StacksProject_2024.stacks_project.Chap15.Lemma_15_105_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open IntermediateField
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Under

universe u v

section

variable {K : Type u} [Field K]
variable {B : Type u} [CommRing B] [Algebra K B]

section WeaklyEtale

variable [Algebra.IsWeaklyEtale K B]

/- Domain-style sampling for Lemma 15.106.1:
- primary domain: weakly étale commutative `K`-algebras over a field and their finite-type
  subalgebras, quotients, and tensor products;
- sampled owner declarations:
  `Algebra.IsWeaklyEtale`,
  `isReduced_of_isWeaklyEtale`,
  `etale_of_fg_subalgebra_of_isWeaklyEtale`,
  `Algebra.Etale.iff_exists_algEquiv_prod`,
  `Algebra.IsSeparable`,
  `isSeparable_of_flat_tensorSquareMultiplication`,
  `Algebra.IsWeaklyEtale.comp`;
- best owner abstraction: the canonical owner is `Algebra.IsWeaklyEtale K B`; finite generation of
  a `K`-subalgebra belongs primitively to `A.FG`, while the `FiniteType` phrasing in part `(3)` is
  a downstream bridge from the existing owner theorem in `Lemma 15.105.16` to
  `Algebra.Etale.iff_exists_algEquiv_prod`;
- primitive data: the weakly étale owner class on `K → B`, the subalgebra `A : Subalgebra K B`,
  and field structure when part `(5)` specializes to a field extension;
- derived API: reducedness, the finite-product classification bridge for finitely generated
  subalgebras, the canonical separability owner in the field case, and the tensor-product closure
  obtained by reusing the base-change and composition API from `15.105.*`.

This file therefore keeps the Stacks source-facing consequences, but it should not introduce a
parallel owner-level API where the chapter already proved the canonical theorem upstream.
-/

/-- Helper for Lemma 15.106.1: every finitely generated `K`-subalgebra of a weakly étale
`K`-algebra should be étale over `K`. -/
theorem etale_of_fg_subalgebra_of_isWeaklyEtale_over_field_stage
    (A : Subalgebra K B) (hA : A.FG) :
    Algebra.Etale K A := by
  -- Route correction: reuse the canonical owner theorem from `Lemma 15.105.16` directly.
  exact etale_of_fg_subalgebra_of_isWeaklyEtale A hA

/-- Helper for Lemma 15.106.1: a weakly étale algebra over a field is absolutely flat because
every singleton-generated subalgebra is étale, hence a finite product of fields. -/
lemma isAbsolutelyFlatRing_of_isWeaklyEtale_over_field_local :
    [Algebra K B] →
    [Algebra.IsWeaklyEtale K B] →
    IsAbsolutelyFlatRing B := by
  refine ⟨fun x ↦ ?_⟩
  let A := Algebra.adjoin K ({x} : Set B)
  -- The singleton-generated stage is finitely generated, so part `(3)` classifies it.
  have hAfg : A.FG := by
    rw [Subalgebra.fg_iff_finiteType A]
    exact Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x)
  obtain ⟨I, hI, Ai, hField, hAlg, e, _hsep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp
      (etale_of_fg_subalgebra_of_isWeaklyEtale_over_field_stage A hAfg)
  let y : A := ⟨x, Algebra.subset_adjoin (by simp)⟩
  let _ : Fintype I := Fintype.ofFinite I
  letI : ∀ i, Field (Ai i) := hField
  letI : ∀ i, Algebra K (Ai i) := hAlg
  letI : ∀ i, IsAbsolutelyFlatRing (Ai i) := fun i ↦ inferInstance
  letI : IsAbsolutelyFlatRing (∀ i, Ai i) := inferInstance
  obtain ⟨z, hz⟩ := IsAbsolutelyFlatRing.exists_factor (A := ∀ i, Ai i) (e y)
  refine ⟨((e.symm z : A) : B), ?_⟩
  -- Transport the product-side factorization back through the algebra equivalence.
  have hy : y = y ^ 2 * e.symm z := by
    simpa using congrArg e.symm hz
  exact congrArg (fun t : A ↦ (t : B)) hy

-- Proof sketch: over a field, weakly étaleness already forces absolute flatness, and reducedness
-- is the nilpotent-free consequence of the absolute-flat factorization criterion.
/-- Lemma 15.106.1 (1): if `B` is weakly étale over a field `K`, then `B` is reduced. -/
theorem isReduced_of_isWeaklyEtale_over_field
    [Algebra K B] [Algebra.IsWeaklyEtale K B] : IsReduced B := by
  let _ : IsAbsolutelyFlatRing B :=
    isAbsolutelyFlatRing_of_isWeaklyEtale_over_field_local (K := K) (B := B)
  exact isReduced_of_isAbsolutelyFlatRing (A := B)

/-- Helper for Lemma 15.106.1: the singleton-generated `K`-subalgebra of a weakly étale
`K`-algebra is finite over `K`. -/
lemma moduleFinite_of_adjoin_singleton_isWeaklyEtale_stage (x : B) :
    Module.Finite K (Algebra.adjoin K ({x} : Set B)) := by
  classical
  let A : Subalgebra K B := Algebra.adjoin K ({x} : Set B)
  -- The singleton-generated stage is finitely generated, so part `(3)` identifies it with a
  -- finite product of finite separable field extensions.
  have hAfg : A.FG := by
    rw [Subalgebra.fg_iff_finiteType A]
    exact Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x)
  obtain ⟨I, hI, Ai, hField, hAlg, e, hsep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp
      (etale_of_fg_subalgebra_of_isWeaklyEtale_over_field_stage A hAfg)
  let _ : Fintype I := Fintype.ofFinite I
  letI : ∀ i, Field (Ai i) := hField
  letI : ∀ i, Algebra K (Ai i) := hAlg
  letI : ∀ i, Module.Finite K (Ai i) := fun i ↦ (hsep i).1
  let _ : Module.Finite K (Π i, Ai i) := inferInstance
  let _ : Module.Finite K A := Module.Finite.equiv e.symm.toLinearEquiv
  simpa [A] using (inferInstance : Module.Finite K A)

-- Proof sketch: by Lemma `15.105.16`, every finitely generated `K`-subalgebra of `B` is étale
-- over `K`, hence finite over `K`; finite algebras over a field are integral, and every element
-- of `B` lies in some finitely generated `K`-subalgebra.
/-- Lemma 15.106.1 (2): if `B` is weakly étale over a field `K`, then `B` is integral over `K`. -/
theorem isIntegral_of_isWeaklyEtale_over_field
    : Algebra.IsIntegral K B := by
  refine ⟨fun x ↦ ?_⟩
  let A : Subalgebra K B := Algebra.adjoin K ({x} : Set B)
  let y : A := ⟨x, Algebra.subset_adjoin (by simp)⟩
  -- The singleton-generated stage is finite over `K`, hence every one of its elements is
  -- integral over `K`.
  let _ : Module.Finite K A := by
    simpa [A] using moduleFinite_of_adjoin_singleton_isWeaklyEtale_stage (K := K) (B := B) x
  let _ : Algebra.IsIntegral K A := Algebra.IsIntegral.of_finite K A
  -- Map the integral element from the stage back to the ambient algebra.
  simpa [A, y] using IsIntegral.map A.val (Algebra.IsIntegral.isIntegral y)

/-- Lemma 15.106.1 (3), source-facing finite-product form: any finitely generated `K`-subalgebra
of a weakly étale `K`-algebra is isomorphic to a finite product of finite separable extensions
of `K`. -/
theorem exists_algEquiv_prod_of_fg_subalgebra_of_isWeaklyEtale_over_field
    (A : Subalgebra K B) (hA : A.FG) :
    ∃ (I : Type u) (_ : Finite I) (Ai : I → Type u) (_ : ∀ i, Field (Ai i))
      (_ : ∀ i, Algebra K (Ai i)) (_ : A ≃ₐ[K] Π i, Ai i),
      ∀ i, Module.Finite K (Ai i) ∧ Algebra.IsSeparable K (Ai i) := by
  exact (Algebra.Etale.iff_exists_algEquiv_prod K A).mp
    (etale_of_fg_subalgebra_of_isWeaklyEtale_over_field_stage A hA)

/-- Helper for Lemma 15.106.1: an absolutely flat commutative ring with only trivial idempotents
is a field. -/
lemma isField_of_idempotents_trivial_of_isAbsolutelyFlatRing
    {R : Type v} [CommRing R] [Nontrivial R] [IsAbsolutelyFlatRing R]
    (hidem : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    IsField R := by
  -- Trivial idempotents force the usual local-ring criterion in an absolutely flat ring.
  let hlocal : IsLocalRing R := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
    obtain ⟨b, hx⟩ := IsAbsolutelyFlatRing.exists_factor (A := R) x
    have he : IsIdempotentElem (x * b) := by
      -- The idempotent is the source-proof choice `e = x * b`.
      have hx' : x * (x * b) = x := by
        calc
          x * (x * b) = x ^ 2 * b := by ring
          _ = x := hx.symm
      calc
        (x * b) * (x * b) = (x * (x * b)) * b := by ring
        _ = x * b := by rw [hx']
    rcases hidem (x * b) he with hxb0 | hxb1
    · -- If `x * b = 0`, then the factorization forces `x = 0`, so `1 - x = 1` is a unit.
      right
      have hx0 : x = 0 := by
        calc
          x = x ^ 2 * b := hx
          _ = x * (x * b) := by ring
          _ = 0 := by simp [hxb0]
      simpa [hx0]
    · -- If `x * b = 1`, then `x` is already a unit with inverse `b`.
      left
      exact ⟨⟨x, b, hxb1, by simpa [mul_comm] using hxb1⟩, rfl⟩
  let _ : IsLocalRing R := hlocal
  -- The local absolutely-flat criterion from Definition `15.105.1` finishes the proof.
  exact isField_of_localRing_exists_factor (R := R) fun r ↦
    IsAbsolutelyFlatRing.exists_factor (A := R) r

-- Proof sketch: by `etale_of_fg_subalgebra_of_isWeaklyEtale`, every weakly étale `K`-algebra over
-- a field is a filtered colimit of finite products of finite separable field extensions. Such a
-- nontrivial product is a field exactly when it has only the trivial idempotents `0` and `1`,
-- and this criterion passes to `B`.
/-- Lemma 15.106.1 (4): a weakly étale `K`-algebra `B` is a field if and only if it has no
nontrivial idempotents. -/
theorem isField_iff_idempotents_eq_zero_or_one_of_isWeaklyEtale_over_field
    [Algebra K B] [Algebra.IsWeaklyEtale K B]
    [Nontrivial B] :
    IsField B ↔ ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  constructor
  · intro hB e he
    let _ : Field B := hB.toField
    -- In a field, the idempotent equation factors as `e * (e - 1) = 0`.
    have hmul : e * (e - 1) = 0 := by
      calc
        e * (e - 1) = e * e - e := by ring
        _ = 0 := by simpa [IsIdempotentElem] using sub_eq_zero.mpr he
    rcases mul_eq_zero.mp hmul with he0 | he1
    · exact Or.inl he0
    · exact Or.inr (sub_eq_zero.mp he1)
  · intro hidem
    let _ : IsAbsolutelyFlatRing B :=
      isAbsolutelyFlatRing_of_isWeaklyEtale_over_field_local (K := K) (B := B)
    -- Over a field, weak étaleness gives absolute flatness, so the idempotent criterion closes.
    exact isField_of_idempotents_trivial_of_isAbsolutelyFlatRing (R := B) hidem

/-- Helper for Lemma 15.106.1: the tensor-square flatness criterion for separability works
without forcing the two field universes to agree. -/
theorem isSeparable_of_flat_tensorSquareMultiplication_mixed_universe
    {L : Type v} [Field L] [Algebra K L]
    (hflat : (Algebra.TensorProduct.lmul' K : L ⊗[K] L →ₐ[K] L).Flat) :
    Algebra.IsSeparable K L := by
  refine ⟨fun x ↦ ?_⟩
  let M : IntermediateField K L := K⟮x⟯
  letI : Algebra M L := M.val.toAlgebra
  letI : IsScalarTower K M L := inferInstance
  have hML : (algebraMap M L).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hMflat : (Algebra.TensorProduct.lmul' K : M ⊗[K] M →ₐ[K] M).Flat :=
    Algebra.tensorSquareMul_flat_of_faithfullyFlat hML hflat
  letI : Algebra.FormallyUnramified K M :=
    Algebra.FormallyUnramified.of_tensorSquareMul_flat hMflat
  letI : Algebra.EssFiniteType K M := (IntermediateField.essFiniteType_iff).2 <|
    by simpa [M] using IntermediateField.fg_adjoin_finset ({x} : Finset L)
  have hsepM : Algebra.IsSeparable K M := Algebra.FormallyUnramified.isSeparable K M
  -- The simple intermediate field `K⟮x⟯` records separability of the chosen element.
  exact (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
    (F := K) (E := L) (x := x)).mp <| by
      simpa [M] using hsepM

-- Proof sketch: if `B` is a field, then part `(4)` together with
-- `etale_of_fg_subalgebra_of_isWeaklyEtale` reduces to the case of a single finite separable
-- field extension at each finitely generated stage. Taking the filtered colimit shows that every
-- element of `B` is separable over `K`; algebraicity is absorbed canonically by
-- `Algebra.IsSeparable`.
/-- Lemma 15.106.1 (5): if a weakly étale `K`-algebra `B` is a field, then `B` is a separable
algebraic extension of `K`. -/
theorem isSeparable_of_isField_of_isWeaklyEtale_over_field
    (hB : IsField B) :
    Algebra.IsSeparable K B := by
  let _ : Field B := hB.toField
  -- Once `B` is a field, the weakly étale tensor-square flatness is exactly the hypothesis of
  -- Lemma `15.105.15`.
  exact isSeparable_of_flat_tensorSquareMultiplication_mixed_universe
    (K := K) (L := B) (inferInstance : Algebra.IsWeaklyEtale K B).flat_tensorSquareMultiplication

/-- Helper for Lemma 15.106.1: finitely generated `K`-subalgebras of a `K`-subalgebra of `B`
remain étale after mapping them into `B`. -/
lemma etale_of_fg_subalgebra_of_subalgebra_isWeaklyEtale_over_field_stage
    (A : Subalgebra K B) (C : Subalgebra K A) (hC : C.FG) :
    Algebra.Etale K C := by
  let e : C ≃ₐ[K] C.map A.val :=
    Subalgebra.equivMapOfInjective C A.val Subtype.val_injective
  have hCmap_finiteType : Algebra.FiniteType K (C.map A.val) := by
    let _ : Algebra.FiniteType K C := (Subalgebra.fg_iff_finiteType C).mp hC
    exact Algebra.FiniteType.of_surjective e.toAlgHom e.surjective
  have hCmap_fg : (C.map A.val).FG := by
    rw [Subalgebra.fg_iff_finiteType (C.map A.val)]
    infer_instance
  have hCmap_et : Algebra.Etale K (C.map A.val) :=
    etale_of_fg_subalgebra_of_isWeaklyEtale_over_field_stage (K := K) (B := B)
      (C.map A.val) hCmap_fg
  let _ : Algebra.Etale K (C.map A.val) := hCmap_et
  -- Pull étaleness back along the canonical equivalence with the mapped stage in `B`.
  exact Algebra.Etale.of_equiv e.symm

/-- Helper for Lemma 15.106.1: every finite adjoin stage inside a `K`-subalgebra of `B` is étale
over `K`. -/
lemma etale_adjoin_finite_of_subalgebra_isWeaklyEtale_over_field_stage
    (A : Subalgebra K B) (s : Finset A) :
    Algebra.Etale K (Algebra.adjoin K (s : Set A)) := by
  -- Convert the finite generator set into the canonical `FG` owner used by the stage theorem.
  have hfg : (Algebra.adjoin K (s : Set A)).FG := by
    rw [Subalgebra.fg_iff_finiteType (Algebra.adjoin K (s : Set A))]
    exact Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  -- The source route now applies directly to the chosen finite adjoin stage.
  exact
    etale_of_fg_subalgebra_of_subalgebra_isWeaklyEtale_over_field_stage
      (K := K) (B := B) A (Algebra.adjoin K (s : Set A)) hfg

/-- Helper for Lemma 15.106.1: the finite adjoin stages inside a fixed `K`-subalgebra form a
directed family under inclusion. -/
lemma directed_adjoin_finite_subalgebra_family (A : Subalgebra K B) :
    Directed (· ≤ ·) (fun s : Finset A ↦ Algebra.adjoin K (s : Set A)) := by
  classical
  intro s t
  refine ⟨s ∪ t, ?_, ?_⟩
  · -- Enlarging the finite generator set enlarges the corresponding adjoin stage.
    exact Algebra.adjoin_mono <| by
      intro x hx
      simpa using Finset.mem_union.mpr (Or.inl hx)
  · -- The symmetric inclusion handles the right stage.
    exact Algebra.adjoin_mono <| by
      intro x hx
      simpa using Finset.mem_union.mpr (Or.inr hx)

/-- Helper for Lemma 15.106.1: finite adjoin stages inside a subalgebra have supremum `⊤`. -/
lemma iSup_adjoin_finite_subalgebra_family_eq_top (A : Subalgebra K B) :
    iSup (fun s : Finset A ↦ Algebra.adjoin K (s : Set A)) = (⊤ : Subalgebra K A) := by
  classical
  let S : Finset A → Subalgebra K A := fun s ↦ Algebra.adjoin K (s : Set A)
  have hdir : Directed (· ≤ ·) S :=
    directed_adjoin_finite_subalgebra_family (K := K) (B := B) A
  exact top_le_iff.mp <| by
    intro a _
    -- Every element belongs to the singleton-generated stage, so it lies in the directed supremum.
    change a ∈ ((iSup S : Subalgebra K A) : Set A)
    rw [Subalgebra.coe_iSup_of_directed hdir]
    refine Set.mem_iUnion.2 ?_
    refine ⟨{a}, ?_⟩
    exact Algebra.subset_adjoin (by simp)

/-- Helper for Lemma 15.106.1: a filtered colimit of étale algebras over a field is weakly
étale. -/
lemma isWeaklyEtale_of_isFilteredColimitOfEtale_local
    {R : Type u} {S : Type u} [Field R] [CommRing S] [Algebra R S]
    (hcolim : (algebraMap R S).IsFilteredColimitOfEtale) :
    Algebra.IsWeaklyEtale R S := by
  refine
    { moduleFlat := by
        infer_instance
      flat_tensorSquareMultiplication := by
        let _ : Algebra (S ⊗[R] S) S := (Algebra.TensorProduct.lmul' R).toAlgebra
        let _ : IsScalarTower S (S ⊗[R] S) S :=
          IsScalarTower.of_algebraMap_eq fun s ↦ by
            change s = (Algebra.TensorProduct.lmul' R) (algebraMap S (S ⊗[R] S) s)
            simp [Algebra.TensorProduct.lmul'_apply_tmul]
        have htensorS :
            (algebraMap S (S ⊗[R] S)).IsFilteredColimitOfEtale :=
          RingHom.filteredColimitOfEtale_baseChange
            (R := R) (A := S) (R' := S) hcolim
        have htensorR :
            (algebraMap R (S ⊗[R] S)).IsFilteredColimitOfEtale :=
          RingHom.isFilteredColimitOfEtale_comp
            (algebraMap R S) (algebraMap S (S ⊗[R] S)) hcolim htensorS
        have hmul :
            (algebraMap (S ⊗[R] S) S).IsFilteredColimitOfEtale :=
          RingHom.isFilteredColimitOfEtale_of_isFilteredColimitOfEtale_over_common_base
            (R := R) (A := S ⊗[R] S) (B := S) htensorR hcolim
        have hflatMul : Module.Flat (S ⊗[R] S) S :=
          flat_of_isFilteredColimitOfEtale hmul
        have halg :
            (algebraMap (S ⊗[R] S) S).Flat :=
          RingHom.flat_algebraMap_iff.mpr hflatMul
        simpa [RingHom.algebraMap_toAlgebra] using halg }

/-- Helper for Lemma 15.106.1: a finite-stage family of `K`-subalgebras indexed by finite sets
packages into the owner `(algebraMap K C).IsFilteredColimitOfEtale` once the family is directed,
stagewise étale, and has supremum `⊤`. -/
lemma algebraMap_isFilteredColimitOfEtale_of_finite_stage_family
    {γ : Type v} {C : Type u} [CommRing C] [Algebra K C]
    (T : Finset γ → Subalgebra K C)
    (hdir : Directed (· ≤ ·) T)
    (hEt : ∀ s : Finset γ, Algebra.Etale K (T s))
    (hSup : iSup T = (⊤ : Subalgebra K C)) :
    (algebraMap K C).IsFilteredColimitOfEtale := by
  -- TODO for Lemma 15.106.1: package the directed `Finset`-indexed family into
  -- `Under (CommRingCat.of K)`, build the colimit desc map with `Subalgebra.iSupLift`, and then
  -- invoke `RingHom.algebraMap_isFilteredColimitOfEtale_of_isColimit`.
  let _ := hdir
  let _ := hEt
  let _ := hSup
  sorry

-- Proof sketch: a `K`-subalgebra is the filtered colimit of its finitely generated
-- `K`-subalgebras. Each finitely generated stage is étale over `K` by
-- `etale_of_fg_subalgebra_of_isWeaklyEtale`, hence weakly étale; then Lemma `15.105.14 (3)` gives
-- weak étaleness of the filtered colimit.
/-- Lemma 15.106.1 (6): any `K`-subalgebra of a weakly étale `K`-algebra is weakly étale over
`K`. -/
theorem isWeaklyEtale_subalgebra_of_isWeaklyEtale_over_field
    (A : Subalgebra K B) :
    Algebra.IsWeaklyEtale K A := by
  -- Route correction: follow the source proof literally through the finite adjoin stages
  -- `s ↦ Algebra.adjoin K (s : Set A)` rather than reverting to an arbitrary `FG` stage wrapper.
  have hdir :
      Directed (· ≤ ·) (fun s : Finset A ↦ Algebra.adjoin K (s : Set A)) :=
    directed_adjoin_finite_subalgebra_family (K := K) (B := B) A
  have hEt : ∀ s : Finset A, Algebra.Etale K (Algebra.adjoin K (s : Set A)) := fun s ↦
    etale_adjoin_finite_of_subalgebra_isWeaklyEtale_over_field_stage (K := K) (B := B) A s
  have hSup :
      iSup (fun s : Finset A ↦ Algebra.adjoin K (s : Set A)) = (⊤ : Subalgebra K A) :=
    iSup_adjoin_finite_subalgebra_family_eq_top (K := K) (B := B) A
  -- The finite adjoin stages give the source-faithful ind-étale presentation of `A`.
  have hcolim : (algebraMap K A).IsFilteredColimitOfEtale :=
    algebraMap_isFilteredColimitOfEtale_of_finite_stage_family
      (K := K) (C := A) (fun s : Finset A ↦ Algebra.adjoin K (s : Set A))
      hdir hEt hSup
  -- The local ind-étale-to-weakly-étale bridge keeps the source proof inside this file.
  exact isWeaklyEtale_of_isFilteredColimitOfEtale_local hcolim

-- Proof sketch: every quotient of a finite product of finite separable field extensions is again
-- a product of some of those factors, hence weakly étale over `K`. Express the quotient of `B` as
-- a filtered colimit of quotients of finitely generated weakly étale subalgebras and apply Lemma
-- `15.105.14 (3)`.
/-- Helper for Lemma 15.106.1: the quotient image stages of finite adjoin subalgebras are
directed by enlarging the finite generator set. -/
lemma directed_image_adjoin_finite_quotient_stage_family (I : Ideal B) :
    Directed (· ≤ ·)
      (fun s : Finset B ↦ (Algebra.adjoin K (s : Set B)).map (Ideal.Quotient.mkₐ K I)) := by
  classical
  intro s t
  refine ⟨s ∪ t, ?_, ?_⟩
  · -- Mapping preserves the stage inclusion coming from `s ⊆ s ∪ t`.
    exact Subalgebra.map_mono <| Algebra.adjoin_mono <| by
      intro x hx
      simpa using Finset.mem_union.mpr (Or.inl hx)
  · -- The right inclusion is identical after swapping the two finite sets.
    exact Subalgebra.map_mono <| Algebra.adjoin_mono <| by
      intro x hx
      simpa using Finset.mem_union.mpr (Or.inr hx)

/-- Helper for Lemma 15.106.1: the quotient image stages of finite adjoin subalgebras have
supremum `⊤`. -/
lemma iSup_image_adjoin_finite_quotient_stage_family_eq_top (I : Ideal B) :
    iSup
        (fun s : Finset B ↦
          (Algebra.adjoin K (s : Set B)).map (Ideal.Quotient.mkₐ K I)) =
      (⊤ : Subalgebra K (B ⧸ I)) := by
  classical
  let T : Finset B → Subalgebra K (B ⧸ I) := fun s ↦
    (Algebra.adjoin K (s : Set B)).map (Ideal.Quotient.mkₐ K I)
  have hdir : Directed (· ≤ ·) T :=
    directed_image_adjoin_finite_quotient_stage_family (K := K) (B := B) I
  exact top_le_iff.mp <| by
    intro x _
    rcases Ideal.Quotient.mkₐ_surjective K I x with ⟨b, rfl⟩
    -- A lift `b : B` already lies in the singleton image stage.
    change (Ideal.Quotient.mkₐ K I) b ∈ ((iSup T : Subalgebra K (B ⧸ I)) : Set (B ⧸ I))
    rw [Subalgebra.coe_iSup_of_directed hdir]
    refine Set.mem_iUnion.2 ?_
    refine ⟨{b}, ?_⟩
    simpa [T] using
      (show (Ideal.Quotient.mkₐ K I) b ∈
          (Algebra.adjoin K ({b} : Set B)).map (Ideal.Quotient.mkₐ K I) from
        ⟨⟨b, Algebra.subset_adjoin (by simp)⟩, rfl⟩)

/-- Helper for Lemma 15.106.1: each finite quotient image stage of a weakly étale `K`-algebra
is étale over `K`. -/
lemma etale_image_adjoin_finite_quotient_stage
    (I : Ideal B) (s : Finset B) :
    Algebra.Etale K ((Algebra.adjoin K (s : Set B)).map (Ideal.Quotient.mkₐ K I)) := by
  let A : Subalgebra K B := Algebra.adjoin K (s : Set B)
  let φA : A →ₐ[K] B ⧸ I := (Ideal.Quotient.mkₐ K I).comp A.val
  have hAfg : A.FG := by
    -- The finite adjoin stage is finitely generated over `K` by construction.
    rw [Subalgebra.fg_iff_finiteType A]
    exact Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  obtain ⟨J, hJ, L, hField, hAlg, eA, hsep⟩ :=
    exists_algEquiv_prod_of_fg_subalgebra_of_isWeaklyEtale_over_field
      (K := K) (B := B) A hAfg
  let _ : Fintype J := Fintype.ofFinite J
  letI : ∀ j, Field (L j) := hField
  letI : ∀ j, Algebra K (L j) := hAlg
  let P : Type u := Π j, L j
  have hCompRange :
      (φA.comp eA.symm.toAlgHom).range = φA.range := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨eA.symm p, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨eA a, by simpa using congrArg φA (AlgEquiv.symm_apply_apply eA a)⟩
  let τ : P →ₐ[K] ↥((φA.comp eA.symm.toAlgHom).range) :=
    (φA.comp eA.symm.toAlgHom).rangeRestrict
  letI : Algebra P ↥((φA.comp eA.symm.toAlgHom).range) := τ.toRingHom.toAlgebra
  have hτsurj :
      Function.Surjective (algebraMap P ↥((φA.comp eA.symm.toAlgHom).range)) := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  have hP_et : Algebra.Etale K P := by
    let _ : Algebra.Etale K A :=
      etale_of_fg_subalgebra_of_isWeaklyEtale_over_field_stage (K := K) (B := B) A hAfg
    -- Transport étaleness of the finite adjoin stage across the product decomposition from part
    -- `(3)`.
    exact Algebra.Etale.of_equiv eA
  letI : ∀ j, Module.Finite K (L j) := fun j ↦ (hsep j).1
  letI : Module.Finite K P := inferInstance
  letI : Algebra.FiniteType K P := inferInstance
  letI : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing K P
  letI : ∀ j, IsAbsolutelyFlatRing (L j) := fun j ↦ inferInstance
  letI : IsAbsolutelyFlatRing P := inferInstance
  letI : IsScalarTower K P ↥((φA.comp eA.symm.toAlgHom).range) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      simpa [RingHom.algebraMap_toAlgebra, τ] using (τ.commutes x).symm
  letI : Module.Flat P ↥((φA.comp eA.symm.toAlgHom).range) := inferInstance
  have hτkerfg :
      (RingHom.ker (algebraMap P ↥((φA.comp eA.symm.toAlgHom).range))).FG := by
    exact
      Ideal.FG.of_isNoetherianRing
        (RingHom.ker (algebraMap P ↥((φA.comp eA.symm.toAlgHom).range)))
  letI : Algebra.FinitePresentation P ↥((φA.comp eA.symm.toAlgHom).range) := by
    exact
      Algebra.FinitePresentation.of_surjective
        (f := Algebra.ofId P ↥((φA.comp eA.symm.toAlgHom).range)) hτsurj hτkerfg
  obtain ⟨u, _hu, hloc⟩ :=
    exists_idempotent_localizationAway_of_surjective_of_flat_of_finitePresentation
      (R := P) (S := ↥((φA.comp eA.symm.toAlgHom).range)) hτsurj
  letI : IsLocalization.Away u ↥((φA.comp eA.symm.toAlgHom).range) := hloc
  letI : Algebra.Etale P ↥((φA.comp eA.symm.toAlgHom).range) :=
    Algebra.Etale.of_isLocalizationAway u
  have hCompRange_et :
      Algebra.Etale K ↥((φA.comp eA.symm.toAlgHom).range) := by
    -- The quotient image stage is an idempotent localization of the finite product stage, hence
    -- étale over `K` by composition.
    exact
      Algebra.Etale.comp (R := K) (A := P)
        (B := ↥((φA.comp eA.symm.toAlgHom).range))
  have hRange_et : Algebra.Etale K ↥φA.range := by
    let eCompRange :
        ↥((φA.comp eA.symm.toAlgHom).range) ≃ₐ[K] ↥φA.range :=
      Subalgebra.equivOfEq (φA.comp eA.symm.toAlgHom).range φA.range hCompRange
    exact Algebra.Etale.of_equiv eCompRange
  have hRange :
      φA.range = A.map (Ideal.Quotient.mkₐ K I) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  let eRange :
      φA.range ≃ₐ[K] A.map (Ideal.Quotient.mkₐ K I) :=
    Subalgebra.equivOfEq φA.range (A.map (Ideal.Quotient.mkₐ K I)) hRange
  -- Finally transport the range-level étaleness to the textbook `Subalgebra.map` presentation.
  exact
    let _ : Algebra.Etale K ↥φA.range := hRange_et
    Algebra.Etale.of_equiv eRange

/-- Lemma 15.106.1 (7): any quotient `K`-algebra of a weakly étale `K`-algebra is weakly étale
over `K`. -/
theorem isWeaklyEtale_quotient_of_isWeaklyEtale_over_field
    (I : Ideal B) :
    Algebra.IsWeaklyEtale K (B ⧸ I) := by
  -- Route correction: use the source-faithful quotient stages
  -- `s ↦ (Algebra.adjoin K (s : Set B)).map (Ideal.Quotient.mkₐ K I)` rather than arbitrary
  -- finitely generated subalgebras of the quotient.
  have hdir :
      Directed (· ≤ ·)
        (fun s : Finset B ↦ (Algebra.adjoin K (s : Set B)).map (Ideal.Quotient.mkₐ K I)) :=
    directed_image_adjoin_finite_quotient_stage_family (K := K) (B := B) I
  have hSup :
      iSup
          (fun s : Finset B ↦
            (Algebra.adjoin K (s : Set B)).map (Ideal.Quotient.mkₐ K I)) =
        (⊤ : Subalgebra K (B ⧸ I)) :=
    iSup_image_adjoin_finite_quotient_stage_family_eq_top (K := K) (B := B) I
  have hEt :
      ∀ s : Finset B,
        Algebra.Etale K
          ((Algebra.adjoin K (s : Set B)).map (Ideal.Quotient.mkₐ K I)) := fun s ↦
    etale_image_adjoin_finite_quotient_stage (K := K) (B := B) I s
  -- The quotient is the ind-étale colimit of its finite image stages, exactly as in the source.
  have hcolim : (algebraMap K (B ⧸ I)).IsFilteredColimitOfEtale :=
    algebraMap_isFilteredColimitOfEtale_of_finite_stage_family
      (K := K) (C := B ⧸ I)
      (fun s : Finset B ↦ (Algebra.adjoin K (s : Set B)).map (Ideal.Quotient.mkₐ K I))
      hdir hEt hSup
  exact isWeaklyEtale_of_isFilteredColimitOfEtale_local hcolim

end WeaklyEtale

-- Proof sketch: write both weakly étale `K`-algebras as filtered colimits of finite étale
-- `K`-algebras by `etale_of_fg_subalgebra_of_isWeaklyEtale`. Tensor products of finite étale
-- algebras over a field are again finite étale, so the tensor product is a filtered colimit of
-- weakly étale `K`-algebras; conclude with Lemma `15.105.14 (3)`.
/-- Lemma 15.106.1 (8): the tensor product of two weakly étale `K`-algebras is weakly étale over
`K`. -/
theorem isWeaklyEtale_tensorProduct_of_isWeaklyEtale_over_field
    {B' : Type u} [CommRing B'] [Algebra K B']
    [Algebra.IsWeaklyEtale K B] [Algebra.IsWeaklyEtale K B'] :
    Algebra.IsWeaklyEtale K (B ⊗[K] B') := by
  let hKB : Algebra.IsWeaklyEtale K B := inferInstance
  let hBT : Algebra.IsWeaklyEtale B (B ⊗[K] B') :=
    (inferInstance : Algebra.IsWeaklyEtale K B').baseChange
  exact (Algebra.IsWeaklyEtale.comp hKB hBT : Algebra.IsWeaklyEtale K (B ⊗[K] B'))

end
