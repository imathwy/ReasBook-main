import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Serre.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver

/-!
# Reduction commutes with base change of the DVR (support for Remark 16-16.3-5)

For a stable `A`-lattice `L` inside `X : FDRep K G`, this module constructs the base-change stable
`A'`-lattice `latBaseStableLattice L` inside `FDRep.scalarExtension X` and proves the equivariant
reduction isomorphism `reduction(A' ⊗ L) ≅ k' ⊗_k reduction(L)`.
-/

noncomputable section

open CategoryTheory
open scoped Representation TensorProduct MonoidAlgebra Pointwise

universe u

namespace Representation

namespace StableLattice

-- ===================== GENERAL REDUCTION LEMMAS =====================
section GeneralReduction
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [CommRing K] [Algebra A K]
variable {G : Type u} [Monoid G]
variable {E : Type u} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]
variable {ρ : Representation K G E}

/-- The residue field acts on the reduction compatibly with the base ring. -/
instance reductionScalarTower (L : StableLattice A ρ) :
    IsScalarTower A (IsLocalRing.ResidueField A) L.reduction := by
  refine ⟨fun a c x => ?_⟩
  refine Quotient.inductionOn' c (fun c => ?_)
  refine Quotient.inductionOn' x (fun y => ?_)
  show ((a • (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) c :
          IsLocalRing.ResidueField A)) • (Submodule.Quotient.mk y : L.reduction))
     = a • ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) c :
          IsLocalRing.ResidueField A) • (Submodule.Quotient.mk y : L.reduction))
  rw [StableLattice.reduction_smul_mk]
  have hsmul : (a • (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) c :
        IsLocalRing.ResidueField A))
      = (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (a * c) :
        IsLocalRing.ResidueField A) := by
    rw [map_mul]; rfl
  rw [hsmul, StableLattice.reduction_smul_mk, mul_smul, ← Submodule.Quotient.mk_smul]

end GeneralReduction

section GeneralFinrank
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Monoid G]
variable {E : Type u} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]
variable {ρ : Representation K G E}

/-- The reduction of a stable lattice over a DVR is finite-dimensional over the residue field. -/
instance reductionFinite (L : StableLattice A ρ) :
    Module.Finite (IsLocalRing.ResidueField A) L.reduction := by
  haveI : Submodule.IsLattice K L.toSubmodule := L.isLattice
  haveI hfin : Module.Finite A L.toSubmodule :=
    (Module.Finite.iff_fg).2 (Submodule.IsLattice.fg (A := K))
  haveI : Module.Finite A L.reduction := Module.Finite.of_surjective
    (L.maximalIdealSubmodule.mkQ) (Submodule.mkQ_surjective _)
  exact Module.Finite.of_restrictScalars_finite A (IsLocalRing.ResidueField A) L.reduction

/-- For a stable lattice over a DVR, the residue-field dimension of the reduction equals the
dimension of the ambient `K`-representation. -/
theorem reduction_finrank_eq (L : StableLattice A ρ) :
    Module.finrank (IsLocalRing.ResidueField A) L.reduction = Module.finrank K E := by
  haveI : Submodule.IsLattice K L.toSubmodule := L.isLattice
  haveI hfin : Module.Finite A L.toSubmodule :=
    (Module.Finite.iff_fg).2 (Submodule.IsLattice.fg (A := K))
  haveI : Module.IsTorsionFree A K := Module.IsTorsionFree.trans_faithfulSMul A (A := K) (M := K)
  haveI : Module.IsTorsionFree A E := Module.IsTorsionFree.trans (S := A) (R := K) (M := E)
  haveI : Module.Free A L.toSubmodule := Module.free_of_finite_type_torsion_free'
  set k := IsLocalRing.ResidueField A with hk
  let e : ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] L.toSubmodule) ≃ₗ[A] L.reduction :=
    TensorProduct.quotTensorEquivQuotSMul L.toSubmodule (IsLocalRing.maximalIdeal A)
  let Ψ : (k ⊗[A] L.toSubmodule) →ₗ[k] L.reduction :=
    (L.maximalIdealSubmodule.mkQ).liftBaseChange k
  have hfun : ∀ z, Ψ z = e z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact (map_zero e).symm
    | add a b ha hb => rw [show Ψ (a + b) = Ψ a + Ψ b from map_add Ψ a b,
        show e (a + b) = e a + e b from map_add e a b, ha, hb]
    | tmul c y =>
        refine Quotient.inductionOn' c (fun c => ?_)
        show Ψ ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) c) ⊗ₜ[A] y)
            = e ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) c) ⊗ₜ[A] y)
        rw [show Ψ ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) c) ⊗ₜ[A] y)
              = (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) c) • L.maximalIdealSubmodule.mkQ y
              from LinearMap.liftBaseChange_tmul k _ _ y]
        rw [Submodule.mkQ_apply, StableLattice.reduction_smul_mk,
          TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
  have hbij : Function.Bijective Ψ := by
    have heq : (Ψ : (k ⊗[A] L.toSubmodule) → L.reduction) = e := funext hfun
    rw [heq]; exact e.bijective
  let Φ : (k ⊗[A] L.toSubmodule) ≃ₗ[k] L.reduction := LinearEquiv.ofBijective Ψ hbij
  rw [← Φ.finrank_eq, Module.finrank_baseChange]
  unfold Module.finrank
  rw [Submodule.IsLattice.rank' K L.toSubmodule]

end GeneralFinrank


-- ===================== BASE-CHANGE LATTICE ======================

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

variable {A' : Type u} [CommRing A'] [IsLocalRing A'] [IsDomain A']
  [IsDiscreteValuationRing A'] [Algebra A A'] [Module.Finite A A']
  [FaithfulSMul A A'] [IsLocalHom (algebraMap A A')]
variable {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K']
  [IsFractionRing A' K'] [Algebra K K'] [IsScalarTower A A' K']
  [IsScalarTower A K K']
variable [Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]
  [IsScalarTower A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')]

variable {X : FDRep K G}

/-- Canonical `A`-linear map `L.toSubmodule → K' ⊗[K] X.V`, `l ↦ 1 ⊗ₜ (l : X.V)`. -/
def latBaseMap (L : StableLattice A X.ρ) :
    L.toSubmodule →ₗ[A] (K' ⊗[K] X.V) :=
  (TensorProduct.mk K K' X.V 1).restrictScalars A ∘ₗ
    (L.toSubmodule.subtype.restrictScalars A)

@[simp] theorem latBaseMap_apply (L : StableLattice A X.ρ) (l : L.toSubmodule) :
    latBaseMap (K' := K') L l = (1 : K') ⊗ₜ[K] (l : X.V) := rfl

/-- The base-change lattice carrier inside `K' ⊗[K] X.V`: the range of the `A'`-linear extension
of `latBaseMap`, equivalently the `A'`-span of `{1 ⊗ l : l ∈ L}`. -/
def latBaseSubmodule (L : StableLattice A X.ρ) : Submodule A' (K' ⊗[K] X.V) :=
  LinearMap.range ((latBaseMap (K' := K') L).liftBaseChange A')

theorem latBaseSubmodule_eq_span (L : StableLattice A X.ρ) :
    latBaseSubmodule (A' := A') (K' := K') L
      = Submodule.span A' (Set.range (latBaseMap (K' := K') L)) := by
  rw [latBaseSubmodule, LinearMap.range_liftBaseChange, LinearMap.coe_range]

theorem latBaseMap_mem (L : StableLattice A X.ρ) (l : L.toSubmodule) :
    latBaseMap (K' := K') L l ∈ latBaseSubmodule (A' := A') (K' := K') L :=
  ⟨(1 : A') ⊗ₜ[A] l, by rw [LinearMap.liftBaseChange_tmul, one_smul]⟩

/-- The scalar-extended action sends a base-change generator to another base-change generator. -/
theorem scalarExtension_latBaseMap (L : StableLattice A X.ρ) (g : G) (l : L.toSubmodule) :
    (Representation.scalarExtension X.ρ g) (latBaseMap (K' := K') L l)
      = latBaseMap (K' := K') L (L.toRepresentation g l) := by
  rw [latBaseMap_apply, latBaseMap_apply]
  rw [show ((L.toRepresentation g l : L.toSubmodule) : X.V) = X.ρ g (l : X.V) from
        L.toRepresentation_apply_coe g l]
  change ((Module.End.baseChangeHom K K' X.V) (X.ρ g)) ((1 : K') ⊗ₜ[K] (l : X.V))
      = (1 : K') ⊗ₜ[K] (X.ρ g (l : X.V))
  exact LinearMap.baseChange_tmul (f := X.ρ g) (A := K') (1 : K') (l : X.V)

theorem latBaseSubmodule_stable (L : StableLattice A X.ρ) (g : G)
    ⦃x : K' ⊗[K] X.V⦄
    (hx : x ∈ latBaseSubmodule (A' := A') (K' := K') L) :
    (Representation.scalarExtension X.ρ g) x ∈ latBaseSubmodule (A' := A') (K' := K') L := by
  rw [latBaseSubmodule_eq_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨l, rfl⟩ := hy
      rw [scalarExtension_latBaseMap]
      exact Submodule.subset_span ⟨_, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ ha

theorem latBaseSubmodule_fg (L : StableLattice A X.ρ) :
    (latBaseSubmodule (A' := A') (K' := K') L).FG := by
  haveI : Submodule.IsLattice K L.toSubmodule := L.isLattice
  haveI : Module.Finite A L.toSubmodule := by
    have : (L.toSubmodule).FG := Submodule.IsLattice.fg (A := K)
    exact (Module.Finite.iff_fg).2 this
  rw [latBaseSubmodule, LinearMap.range_eq_map]
  exact Submodule.FG.map _
    ((Module.Finite.iff_fg (N := (⊤ : Submodule A' (A' ⊗[A] L.toSubmodule)))).1 inferInstance)

/-- Every element `1 ⊗ v` (`v ∈ X.V`) lies in the `K'`-span of the base-change generators, because
`L` `K`-spans `X.V`. -/
theorem one_tmul_mem_spanK' (L : StableLattice A X.ρ) (v : X.V) :
    ((1 : K') ⊗ₜ[K] v : K' ⊗[K] X.V)
      ∈ Submodule.span K' (Set.range (latBaseMap (K' := K') L)) := by
  haveI : Submodule.IsLattice K L.toSubmodule := L.isLattice
  have hv : v ∈ Submodule.span K (↑L.toSubmodule : Set X.V) := by
    rw [Submodule.IsLattice.span_eq_top (A := K) (M := L.toSubmodule)]; trivial
  induction hv using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩
  | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | add a c _ _ ha hc => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hc
  | smul r a _ ha =>
      have hrw : ((1 : K') ⊗ₜ[K] (r • a) : K' ⊗[K] X.V)
          = (algebraMap K K' r) • ((1 : K') ⊗ₜ[K] a) := by
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
        congr 1
        simp [Algebra.smul_def]
      rw [hrw]
      exact Submodule.smul_mem _ _ ha

theorem latBaseSubmodule_spanK'_top (L : StableLattice A X.ρ) :
    Submodule.span K' (latBaseSubmodule (A' := A') (K' := K') L : Set (K' ⊗[K] X.V)) = ⊤ := by
  refine le_antisymm le_top ?_
  -- it suffices that the span contains every pure tensor `c ⊗ v`.
  have hbase : Submodule.span K' (Set.range (latBaseMap (K' := K') L)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    clear ‹x ∈ ⊤›
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | tmul c v =>
        have hcv : (c ⊗ₜ[K] v : K' ⊗[K] X.V) = c • ((1 : K') ⊗ₜ[K] v) := by
          rw [TensorProduct.smul_tmul']; congr 1; simp
        rw [hcv]
        exact Submodule.smul_mem _ _ (one_tmul_mem_spanK' (K' := K') L v)
  rw [← hbase]
  apply Submodule.span_mono
  rintro _ ⟨l, rfl⟩
  exact latBaseMap_mem (A' := A') (K' := K') L l

theorem latBaseSubmodule_isLattice (L : StableLattice A X.ρ) :
    Submodule.IsLattice K' (latBaseSubmodule (A' := A') (K' := K') L) :=
  { fg := latBaseSubmodule_fg (A' := A') (K' := K') L
    span_eq_top := latBaseSubmodule_spanK'_top (A' := A') (K' := K') L }

/-- The base-change stable `A'`-lattice of `Representation.scalarExtension X.ρ`. -/
def latBaseStableLattice (L : StableLattice A X.ρ) :
    StableLattice A' (Representation.scalarExtension (k := K') X.ρ) where
  toSubmodule := latBaseSubmodule (A' := A') (K' := K') L
  apply_mem_toSubmodule g x hx := latBaseSubmodule_stable (A' := A') (K' := K') L g hx
  isLattice := latBaseSubmodule_isLattice (A' := A') (K' := K') L


-- ===================== REDUCTION ISO ======================

/-- Residue-field map factors through `A → A'`. -/
theorem residue_algebraMap_eq_A' (a : A) :
    algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a)
    = algebraMap A' (IsLocalRing.ResidueField A') (algebraMap A A' a) := by
  rw [show (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a)
        = algebraMap A (IsLocalRing.ResidueField A) a from rfl]
  rw [← IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A') a]
  rw [← IsScalarTower.algebraMap_apply A A' (IsLocalRing.ResidueField A') a]

/-- The base-change residue-field scalar acts on a class via `A → A'`. -/
theorem latBaseReduction_residue_smul (L : StableLattice A X.ρ) (a : A)
    (z : (latBaseStableLattice (A' := A') (K' := K') L).toSubmodule) :
    (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a)) •
        (Submodule.Quotient.mk z : (latBaseStableLattice (A' := A') (K' := K') L).reduction)
      = Submodule.Quotient.mk ((algebraMap A A' a) • z) := by
  rw [residue_algebraMap_eq_A', algebraMap_smul, Submodule.Quotient.mk_smul]

/-- The `A`-linear map `L.toSubmodule → L'.reduction`, `l ↦ class of (1 ⊗ l)`. -/
def latBaseReductionMap0 (L : StableLattice A X.ρ) :
    L.toSubmodule →ₗ[A]
      (latBaseStableLattice (A' := A') (K' := K') L).reduction :=
  (((latBaseStableLattice (A' := A') (K' := K') L).maximalIdealSubmodule.mkQ).restrictScalars A) ∘ₗ
    (LinearMap.codRestrict
      ((latBaseStableLattice (A' := A') (K' := K') L).toSubmodule.restrictScalars A)
      (latBaseMap (K' := K') L)
      (fun l => latBaseMap_mem (A' := A') (K' := K') L l))

@[simp] theorem latBaseReductionMap0_apply (L : StableLattice A X.ρ) (l : L.toSubmodule) :
    latBaseReductionMap0 (A' := A') (K' := K') L l
      = Submodule.Quotient.mk
          (⟨latBaseMap (K' := K') L l, latBaseMap_mem (A' := A') (K' := K') L l⟩ :
            (latBaseStableLattice (A' := A') (K' := K') L).toSubmodule) := rfl

theorem latBaseReductionMap0_kills (L : StableLattice A X.ρ) :
    L.maximalIdealSubmodule ≤ LinearMap.ker (latBaseReductionMap0 (A' := A') (K' := K') L) := by
  rw [StableLattice.maximalIdealSubmodule, Submodule.smul_le]
  intro a ha x _
  rw [LinearMap.mem_ker, map_smul, latBaseReductionMap0_apply,
    ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    StableLattice.maximalIdealSubmodule]
  have hav : (a • (⟨latBaseMap (K' := K') L x, latBaseMap_mem (A' := A') (K' := K') L x⟩ :
        (latBaseStableLattice (A' := A') (K' := K') L).toSubmodule))
      = (algebraMap A A' a) • (⟨latBaseMap (K' := K') L x,
          latBaseMap_mem (A' := A') (K' := K') L x⟩ :
        (latBaseStableLattice (A' := A') (K' := K') L).toSubmodule) := by
    rw [algebraMap_smul]
  rw [hav]
  exact Submodule.smul_mem_smul (map_nonunit (algebraMap A A') a ha) Submodule.mem_top

set_option maxHeartbeats 4000000 in
/-- The equivariant reduction equivalence: the reduction of the base-change lattice is the
scalar extension of the reduction. -/
def latBaseReductionEquiv (L : StableLattice A X.ρ) :
    (latBaseStableLattice (A' := A') (K' := K') L).reductionRepresentation.Equiv
      (Representation.scalarExtension (k := IsLocalRing.ResidueField A')
        L.reductionRepresentation) := by
  letI : Module (IsLocalRing.ResidueField A)
      (latBaseStableLattice (A' := A') (K' := K') L).reduction :=
    Module.compHom (latBaseStableLattice (A' := A') (K' := K') L).reduction
      (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A'))
  haveI hstk : IsScalarTower (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')
      (latBaseStableLattice (A' := A') (K' := K') L).reduction :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  -- ι : L.reduction →ₗ[k] L'.reduction
  let ι : L.reduction →ₗ[IsLocalRing.ResidueField A]
      (latBaseStableLattice (A' := A') (K' := K') L).reduction :=
    { toFun := Submodule.liftQ L.maximalIdealSubmodule
        (latBaseReductionMap0 (A' := A') (K' := K') L)
        (latBaseReductionMap0_kills (A' := A') (K' := K') L)
      map_add' := by intro x y; simp
      map_smul' := by
        intro c x
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) c
        refine Quotient.inductionOn' x (fun y => ?_)
        show Submodule.liftQ _ _ _
            ((IsLocalRing.residue A a) •
              (Submodule.Quotient.mk y : L.reduction))
          = (IsLocalRing.residue A a) •
              Submodule.liftQ _ _ _ (Submodule.Quotient.mk y : L.reduction)
        rw [show (IsLocalRing.residue A a) • (Submodule.Quotient.mk y : L.reduction)
              = (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a :
                  IsLocalRing.ResidueField A) • (Submodule.Quotient.mk y : L.reduction) from rfl,
          StableLattice.reduction_smul_mk, Submodule.liftQ_apply, Submodule.liftQ_apply,
          map_smul, latBaseReductionMap0_apply, ← Submodule.Quotient.mk_smul]
        show Submodule.Quotient.mk
              (a • (⟨latBaseMap (K' := K') L y,
                latBaseMap_mem (A' := A') (K' := K') L y⟩ :
                (latBaseStableLattice (A' := A') (K' := K') L).toSubmodule))
          = (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')
              (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a)) •
              (Submodule.Quotient.mk
                (⟨latBaseMap (K' := K') L y,
                  latBaseMap_mem (A' := A') (K' := K') L y⟩ :
                  (latBaseStableLattice (A' := A') (K' := K') L).toSubmodule) :
                (latBaseStableLattice (A' := A') (K' := K') L).reduction)
        rw [latBaseReduction_residue_smul, algebraMap_smul] }
  -- ι_mk apply lemma
  have hι_mk : ∀ l : L.toSubmodule,
      ι (Submodule.Quotient.mk l)
        = Submodule.Quotient.mk
            (⟨latBaseMap (K' := K') L l, latBaseMap_mem (A' := A') (K' := K') L l⟩ :
              (latBaseStableLattice (A' := A') (K' := K') L).toSubmodule) := fun l => rfl
  -- Ψ := ι.liftBaseChange k' : k' ⊗[k] L.reduction → L'.reduction
  let Ψ : (IsLocalRing.ResidueField A' ⊗[IsLocalRing.ResidueField A] L.reduction) →ₗ[IsLocalRing.ResidueField A']
      (latBaseStableLattice (A' := A') (K' := K') L).reduction :=
    ι.liftBaseChange (IsLocalRing.ResidueField A')
  -- Ψ apply on a generator
  have hΨ_tmul : ∀ (c : IsLocalRing.ResidueField A') (l : L.toSubmodule),
      Ψ (c ⊗ₜ[IsLocalRing.ResidueField A] (Submodule.Quotient.mk l : L.reduction))
        = c • (Submodule.Quotient.mk
            (⟨latBaseMap (K' := K') L l, latBaseMap_mem (A' := A') (K' := K') L l⟩ :
              (latBaseStableLattice (A' := A') (K' := K') L).toSubmodule) :
            (latBaseStableLattice (A' := A') (K' := K') L).reduction) := by
    intro c l
    show ι.liftBaseChange (IsLocalRing.ResidueField A')
        (c ⊗ₜ[IsLocalRing.ResidueField A] (Submodule.Quotient.mk l : L.reduction)) = _
    rw [LinearMap.liftBaseChange_tmul, hι_mk]
  -- SURJECTIVITY of Ψ
  have hsurj : Function.Surjective Ψ := by
    intro w
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
      (latBaseStableLattice (A' := A') (K' := K') L).maximalIdealSubmodule w
    -- x : L'.toSubmodule, x.val ∈ latBaseSubmodule = span A' (range latBaseMap)
    have hx : (x : K' ⊗[K] X.V) ∈ Submodule.span A' (Set.range (latBaseMap (K' := K') L)) := by
      rw [← latBaseSubmodule_eq_span]; exact x.property
    -- induction on membership (membership erased from motive)
    have key : ∀ (v : K' ⊗[K] X.V),
        v ∈ Submodule.span A' (Set.range (latBaseMap (K' := K') L)) →
        ∀ (hmem : v ∈ latBaseSubmodule (A' := A') (K' := K') L),
        (Submodule.Quotient.mk (⟨v, hmem⟩ :
          (latBaseStableLattice (A' := A') (K' := K') L).toSubmodule) :
          (latBaseStableLattice (A' := A') (K' := K') L).reduction) ∈ LinearMap.range Ψ := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨l, rfl⟩ := hy
          intro hmem
          exact ⟨(1 : IsLocalRing.ResidueField A') ⊗ₜ[IsLocalRing.ResidueField A]
            (Submodule.Quotient.mk l : L.reduction), by rw [hΨ_tmul, one_smul]⟩
      | zero =>
          intro hmem
          refine ⟨0, ?_⟩
          rw [map_zero]
          rw [show (⟨(0 : K' ⊗[K] X.V), hmem⟩ :
              (latBaseStableLattice (A' := A') (K' := K') L).toSubmodule) = 0 from rfl]
          rw [Submodule.Quotient.mk_zero]
      | add p q hp hq ihp ihq =>
          intro hmem
          obtain ⟨wp, hwp⟩ := ihp (by rw [latBaseSubmodule_eq_span]; exact hp)
          obtain ⟨wq, hwq⟩ := ihq (by rw [latBaseSubmodule_eq_span]; exact hq)
          refine ⟨wp + wq, ?_⟩
          rw [map_add, hwp, hwq]
          rw [show (⟨p + q, hmem⟩ :
              (latBaseStableLattice (A' := A') (K' := K') L).toSubmodule)
              = (⟨p, _⟩ : (latBaseStableLattice (A' := A') (K' := K') L).toSubmodule)
                + (⟨q, _⟩ : (latBaseStableLattice (A' := A') (K' := K') L).toSubmodule) from rfl]
          rw [Submodule.Quotient.mk_add]
      | smul a p hp ih =>
          intro hmem
          obtain ⟨wp, hwp⟩ := ih (by rw [latBaseSubmodule_eq_span]; exact hp)
          refine ⟨(IsLocalRing.residue A' a) • wp, ?_⟩
          rw [map_smul, hwp]
          rw [show (IsLocalRing.residue A' a)
                = (algebraMap A' (IsLocalRing.ResidueField A') a) from rfl,
            algebraMap_smul, ← Submodule.Quotient.mk_smul]
          rfl
    obtain ⟨w', hw'⟩ := key x.val hx x.property
    exact ⟨w', by rw [hw']⟩
  -- bijectivity via equal finrank
  have hfinrank :
      Module.finrank (IsLocalRing.ResidueField A')
          (IsLocalRing.ResidueField A' ⊗[IsLocalRing.ResidueField A] L.reduction)
        = Module.finrank (IsLocalRing.ResidueField A')
            (latBaseStableLattice (A' := A') (K' := K') L).reduction := by
    rw [Module.finrank_baseChange, reduction_finrank_eq L]
    rw [reduction_finrank_eq (latBaseStableLattice (A' := A') (K' := K') L)]
    rw [Module.finrank_baseChange]
  have hinj : Function.Injective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).mpr hsurj
  let Φ :
      (IsLocalRing.ResidueField A' ⊗[IsLocalRing.ResidueField A] L.reduction) ≃ₗ[IsLocalRing.ResidueField A']
        (latBaseStableLattice (A' := A') (K' := K') L).reduction :=
    LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  -- scalarExtension apply on tmul
  have hscal : ∀ (g : G) (c : IsLocalRing.ResidueField A') (y : L.reduction),
      (Representation.scalarExtension (k := IsLocalRing.ResidueField A')
          L.reductionRepresentation g) (c ⊗ₜ[IsLocalRing.ResidueField A] y)
        = c ⊗ₜ[IsLocalRing.ResidueField A] (L.reductionRepresentation g y) := by
    intro g c y
    change ((Module.End.baseChangeHom (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A')
        L.reduction) (L.reductionRepresentation g)) (c ⊗ₜ[IsLocalRing.ResidueField A] y) = _
    exact LinearMap.baseChange_tmul (f := L.reductionRepresentation g)
      (A := IsLocalRing.ResidueField A') c y
  -- Ψ-equivariance
  have hΨ_equiv : ∀ (g : G)
      (z : IsLocalRing.ResidueField A' ⊗[IsLocalRing.ResidueField A] L.reduction),
      Ψ ((Representation.scalarExtension (k := IsLocalRing.ResidueField A')
          L.reductionRepresentation g) z)
        = (latBaseStableLattice (A' := A') (K' := K') L).reductionRepresentation g (Ψ z) := by
    intro g z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
    | tmul c l =>
        refine Quotient.inductionOn' l (fun l => ?_)
        show Ψ ((Representation.scalarExtension (k := IsLocalRing.ResidueField A')
              L.reductionRepresentation g)
            (c ⊗ₜ[IsLocalRing.ResidueField A] (Submodule.Quotient.mk l : L.reduction)))
          = (latBaseStableLattice (A' := A') (K' := K') L).reductionRepresentation g
              (Ψ (c ⊗ₜ[IsLocalRing.ResidueField A] (Submodule.Quotient.mk l : L.reduction)))
        rw [hscal, StableLattice.reductionRepresentation_apply_mk, hΨ_tmul, hΨ_tmul,
          map_smul, StableLattice.reductionRepresentation_apply_mk]
        have hsub : ((latBaseStableLattice (A' := A') (K' := K') L).toRepresentation g
            ⟨latBaseMap (K' := K') L l, latBaseMap_mem (A' := A') (K' := K') L l⟩ :
            (latBaseStableLattice (A' := A') (K' := K') L).toSubmodule)
            = ⟨latBaseMap (K' := K') L (L.toRepresentation g l),
                latBaseMap_mem (A' := A') (K' := K') L (L.toRepresentation g l)⟩ := by
          apply Subtype.ext
          rw [StableLattice.toRepresentation_apply_coe]
          exact scalarExtension_latBaseMap (K' := K') L g l
        rw [hsub]
  -- assemble the Representation.Equiv via Φ.symm
  refine Representation.Equiv.mk Φ.symm ?_
  intro g
  -- want: Φ.symm ∘ₗ L'.redRep g = (scalarExt L.redRep g) ∘ₗ Φ.symm
  apply LinearMap.ext
  intro w
  apply Φ.injective
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [show (Φ.symm : _ →ₗ[_] _) = (Φ.symm : _ ≃ₗ[_] _).toLinearMap from rfl]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  -- goal: L'.redRep g w = Φ ((scalarExt L.redRep g) (Φ.symm w))
  have hg := hΨ_equiv g (Φ.symm w)
  show (latBaseStableLattice (A' := A') (K' := K') L).reductionRepresentation g w
    = Φ ((Representation.scalarExtension (k := IsLocalRing.ResidueField A')
        L.reductionRepresentation g) (Φ.symm w))
  rw [show Φ ((Representation.scalarExtension (k := IsLocalRing.ResidueField A')
        L.reductionRepresentation g) (Φ.symm w))
      = Ψ ((Representation.scalarExtension (k := IsLocalRing.ResidueField A')
        L.reductionRepresentation g) (Φ.symm w)) from rfl]
  rw [hg]
  show (latBaseStableLattice (A' := A') (K' := K') L).reductionRepresentation g w
    = (latBaseStableLattice (A' := A') (K' := K') L).reductionRepresentation g (Ψ (Φ.symm w))
  congr 1
  exact (Φ.apply_symm_apply w).symm

set_option maxHeartbeats 4000000 in
theorem latBaseReduction_nonempty_iso (L : StableLattice A X.ρ) :
    Nonempty (FDRep.of (latBaseStableLattice (K' := K') L).reductionRepresentation ≅
      FDRep.scalarExtension (k := IsLocalRing.ResidueField A')
        (FDRep.of L.reductionRepresentation)) := by
  exact ⟨Representation.Equiv.toFDRepIso (latBaseReductionEquiv (A' := A') (K' := K') L)⟩


end StableLattice

end Representation
