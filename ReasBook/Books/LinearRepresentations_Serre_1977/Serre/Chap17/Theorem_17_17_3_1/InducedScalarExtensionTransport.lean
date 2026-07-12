import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_1
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_4_1.IdentityProjectionRepresentativeSeeds
import LinearRepresentations_Serre_1977.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.ResidueFieldLift
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CliffordIsotypicTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicOrbitSpan
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ProperOvergroupRecursion
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftInductionTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ULiftScalarExtensionPreparation

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

open CategoryTheory Rep
open scoped Representation

section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {G : Type v} [Group G] [Finite G]
variable {p : ℕ}

variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type w} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable {C P : Subgroup G}

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance inducedScalarExtensionTransportResidueFieldModule
    {W : Type*} [AddCommGroup W] [Module k W] : Module A W :=
  Module.compHom W (algebraMap A k)
local instance inducedScalarExtensionTransportResidueFieldIsScalarTower
    {W : Type*} [AddCommGroup W] [Module k W] : IsScalarTower A k W :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: scalar extension carries the `A`-valued finitely supported
coefficient functions in the induced source to the corresponding `k`-valued functions. -/
noncomputable abbrev induced_scalarExtension_coeff_equiv_local :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    TensorProduct A k (G →₀ A) ≃ₗ[k] (G →₀ k) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  simpa using (TensorProduct.finsuppScalarRight A k k G)

/-- Helper for Theorem 17-17.3-1: on a single-supported coefficient tensor, the coefficient
transport is exactly the expected residue-field scalar on that support point. -/
theorem induced_scalarExtension_coeff_equiv_tmul_single_local
    (z : k) (g : G) (a : A) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    induced_scalarExtension_coeff_equiv_local (z ⊗ₜ[A] Finsupp.single g a) =
        Finsupp.single g ((algebraMap A k a) * z) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  ext g'
  by_cases h : g' = g
  · -- On the support point, the transport is just the scalar action of `a` on `z`.
    simpa [h, Algebra.smul_def] using
      (TensorProduct.finsuppScalarRight_apply_tmul_apply
        (R := A) (S := k) (M := k) (ι := G)
        (m := z) (p := Finsupp.single g a) (i := g'))
  · -- Away from the support, both finitely supported functions vanish.
    simpa [h] using
      (TensorProduct.finsuppScalarRight_apply_tmul_apply
        (R := A) (S := k) (M := k) (ι := G)
        (m := z) (p := Finsupp.single g a) (i := g'))

/-- Helper for Theorem 17-17.3-1: the coefficient transport sends the standard induced basis
coefficient `single g 1` to the corresponding residue-field basis coefficient. -/
theorem induced_scalarExtension_coeff_equiv_tmul_single_one_local
    (z : k) (g : G) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    induced_scalarExtension_coeff_equiv_local (z ⊗ₜ[A] Finsupp.single g (1 : A)) =
        Finsupp.single g z := by
  -- Specialize the general coefficient formula to the unit coefficient used by `IndV.mk`.
  simpa using
    induced_scalarExtension_coeff_equiv_tmul_single_local
      (A := A) (G := G) z g (1 : A)

/-- Helper for Theorem 17-17.3-1: the inverse coefficient transport rewrites a residue-field basis
coefficient as the corresponding pure tensor over `A`. -/
theorem induced_scalarExtension_coeff_equiv_symm_single_local
    (z : k) (g : G) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    (induced_scalarExtension_coeff_equiv_local (A := A) (G := G)).symm (Finsupp.single g z) =
        z ⊗ₜ[A] Finsupp.single g (1 : A) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  -- Apply the already established forward formula and solve by injectivity of the equivalence.
  apply (induced_scalarExtension_coeff_equiv_local (A := A) (G := G)).injective
  simpa using
    induced_scalarExtension_coeff_equiv_tmul_single_one_local
      (A := A) (G := G) z g

/-- Helper for Theorem 17-17.3-1: before descending to `Coinvariants`, the scalar extension of the
raw induced source is canonically identified with the raw induced source of the scalar-extended
representation. -/
noncomputable def induced_scalarExtension_source_raw_tensor_equiv_local
    {W0 : Type x} [AddCommGroup W0] [Module A W0] :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    TensorProduct A k (TensorProduct A (G →₀ A) W0) ≃ₗ[k]
      TensorProduct k (G →₀ k) (TensorProduct A k W0) := by
  let _ : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  let _ : Module A k := Algebra.toModule
  let _ : Module k k := Semiring.toModule
  let _ : Module k (G →₀ k) := Finsupp.module G k
  let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let X := TensorProduct A (G →₀ A) W0
  let e0 :
      TensorProduct A k X ≃ₗ[k] TensorProduct k k (TensorProduct A k X) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A k k k X).symm
  let e1 :
      TensorProduct k k (TensorProduct A k X) ≃ₗ[k] TensorProduct A (TensorProduct k k k) X :=
    (TensorProduct.AlgebraTensorModule.assoc A k k k k X).symm
  let e2 :
      TensorProduct A (TensorProduct k k k) X ≃ₗ[k]
        TensorProduct k (TensorProduct A k (G →₀ A)) (TensorProduct A k W0) :=
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm A A k k k (G →₀ A) k W0).symm
  let e3 :
      TensorProduct k (TensorProduct A k (G →₀ A)) (TensorProduct A k W0) ≃ₗ[k]
        TensorProduct k (G →₀ k) (TensorProduct A k W0) :=
    TensorProduct.congr
      (induced_scalarExtension_coeff_equiv_local (A := A) (G := G))
      (LinearEquiv.refl k (TensorProduct A k W0))
  simpa [X] using (((e0.trans e1).trans e2).trans e3)

/-- Helper for Theorem 17-17.3-1: the raw forward tensor transport is the forward linear map of
the pre-coinvariants scalar-extension/source equivalence. -/
noncomputable abbrev induced_scalarExtension_source_hom_local
    {W0 : Type x} [AddCommGroup W0] [Module A W0] :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    TensorProduct A k (TensorProduct A (G →₀ A) W0) →ₗ[k]
      TensorProduct k (G →₀ k) (TensorProduct A k W0) := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  exact
    (induced_scalarExtension_source_raw_tensor_equiv_local
      (A := A) (G := G) (W0 := W0)).toLinearMap

/-- Helper for Theorem 17-17.3-1: the raw inverse tensor transport is the inverse linear map of
the pre-coinvariants scalar-extension/source equivalence. -/
noncomputable abbrev induced_scalarExtension_source_inv_local
    {W0 : Type x} [AddCommGroup W0] [Module A W0] :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    TensorProduct k (G →₀ k) (TensorProduct A k W0) →ₗ[k]
      TensorProduct A k (TensorProduct A (G →₀ A) W0) := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  exact
    (induced_scalarExtension_source_raw_tensor_equiv_local
      (A := A) (G := G) (W0 := W0)).symm.toLinearMap

/-- Helper for Theorem 17-17.3-1: on the standard pure tensor corresponding to `IndV.mk`, the raw
forward transport only moves the coefficient function across scalar extension. -/
theorem induced_scalarExtension_source_hom_apply_basis_local
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (z : k) (g : G) (x : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    induced_scalarExtension_source_hom_local
        (W0 := W0)
        (z ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] x)) =
      (Finsupp.single g z) ⊗ₜ[k] (1 ⊗ₜ[A] x) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  -- Unfold the explicit raw comparison and rewrite each tensor reassociation on the chosen basis
  -- tensor. The only genuine content is the coefficient-transport formula.
  simp [induced_scalarExtension_source_hom_local,
    induced_scalarExtension_source_raw_tensor_equiv_local,
    induced_scalarExtension_coeff_equiv_local,
    TensorProduct.finsuppScalarRight_apply_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.assoc_symm_tmul]

/-- Helper for Theorem 17-17.3-1: the raw inverse transport sends a scalar-extended basis tensor
back to the corresponding pure tensor over `A`. -/
theorem induced_scalarExtension_source_inv_apply_basis_local
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (z : k) (g : G) (x : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    induced_scalarExtension_source_inv_local
        (W0 := W0)
        ((Finsupp.single g z) ⊗ₜ[k] (1 ⊗ₜ[A] x)) =
      z ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] x) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  -- The inverse composite first rewrites the coefficient basis vector back to a pure tensor, then
  -- cancels the auxiliary base change and reassociates the tensor factors back to the source.
  simp [induced_scalarExtension_source_inv_local,
    induced_scalarExtension_source_raw_tensor_equiv_local,
    induced_scalarExtension_coeff_equiv_local,
    TensorProduct.finsuppScalarRight_symm_apply_single,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.AlgebraTensorModule.assoc_tmul]

/-- Helper for Theorem 17-17.3-1: on a single-supported coefficient tensor with arbitrary
coefficient, the raw forward transport rewrites only the coefficient function and leaves the source
vector untouched. This is the coefficient-level step still needed in the quotient descent. -/
theorem induced_scalarExtension_source_hom_apply_single_local
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (z : k) (g : G) (a : A) (x : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    induced_scalarExtension_source_hom_local
        (A := A) (G := G) (W0 := W0)
        (z ⊗ₜ[A] ((Finsupp.single g a) ⊗ₜ[A] x)) =
      (Finsupp.single g ((algebraMap A k a) * z)) ⊗ₜ[k] (1 ⊗ₜ[A] x) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  -- Unfold the raw comparison once; the only nontrivial step is the already isolated coefficient
  -- transport on the singleton basis vector.
  simp [induced_scalarExtension_source_hom_local,
    induced_scalarExtension_source_raw_tensor_equiv_local,
    induced_scalarExtension_coeff_equiv_local,
    TensorProduct.finsuppScalarRight_apply_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.assoc_symm_tmul]
  simpa [Algebra.smul_def]

/-- Helper for Theorem 17-17.3-1: the scalar-extended source action on a singleton-supported pure
tensor is already the translated singleton formula from Serre's induced-model relation. -/
theorem induced_scalarExtension_source_sourceAct_apply_single_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (h : H) (z : k) (g : G) (a : A) (xU : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let sourceAct :=
      (Representation.scalarExtension
        (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) h
    sourceAct (z ⊗ₜ[A] ((Finsupp.single g a) ⊗ₜ[A] xU)) =
      z ⊗ₜ[A] ((Finsupp.single ((h : G) * g) a) ⊗ₜ[A] (ρA_HU h xU)) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  -- Normalize the scalar-extended source action before applying the raw tensor transport.
  change
    (((Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU) h).baseChange
      k) (z ⊗ₜ[A] ((Finsupp.single g a) ⊗ₜ[A] xU)) =
      z ⊗ₜ[A] ((Finsupp.single ((h : G) * g) a) ⊗ₜ[A] (ρA_HU h xU))
  rw [LinearMap.baseChange_tmul, Representation.tprod_apply, TensorProduct.map_tmul]
  simp [Representation.ofMulAction_single]

/-- Helper for Theorem 17-17.3-1: the target induced action on a singleton-supported pure tensor
is the translated singleton formula after scalar extension on the subgroup source. -/
theorem induced_scalarExtension_source_targetAct_apply_single_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (h : H) (c : k) (g : G) (xU : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let targetAct :=
      Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
        (Representation.scalarExtension ρA_HU) h
    targetAct ((Finsupp.single g c) ⊗ₜ[k] ((1 : k) ⊗ₜ[A] xU)) =
      (Finsupp.single ((h : G) * g) c) ⊗ₜ[k] ((1 : k) ⊗ₜ[A] (ρA_HU h xU)) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  -- Normalize the target action directly on the singleton-supported tensor.
  change
    (Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
        (Representation.scalarExtension ρA_HU) h)
      ((Finsupp.single g c) ⊗ₜ[k] ((1 : k) ⊗ₜ[A] xU)) =
        (Finsupp.single ((h : G) * g) c) ⊗ₜ[k] ((1 : k) ⊗ₜ[A] (ρA_HU h xU))
  rw [Representation.tprod_apply, TensorProduct.map_tmul]
  simp [Representation.ofMulAction_single]
  have hbase :
      (ρA_HU.scalarExtension h) ((1 : k) ⊗ₜ[A] xU) = (1 : k) ⊗ₜ[A] (ρA_HU h xU) := by
    change ((ρA_HU h).baseChange k) ((1 : k) ⊗ₜ[A] xU) = (1 : k) ⊗ₜ[A] (ρA_HU h xU)
    rw [LinearMap.baseChange_tmul]
  exact congrArg (fun y ↦ (Finsupp.single ((h : G) * g) c) ⊗ₜ[k] y) hbase

/-- Helper for Theorem 17-17.3-1: the raw forward tensor transport already commutes with the
singleton-supported induction relation on arbitrary coefficients. This is the generator-level
compatibility needed before descending through coinvariants. -/
theorem induced_scalarExtension_source_hom_commutes_on_single_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (h : H) (z : k) (g : G) (a : A) (xU : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let sourceAct :=
      (Representation.scalarExtension
        (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) h
    let targetAct :=
      Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
        (Representation.scalarExtension ρA_HU) h
    induced_scalarExtension_source_hom_local
        (A := A) (G := G) (W0 := W0)
        (sourceAct (z ⊗ₜ[A] ((Finsupp.single g a) ⊗ₜ[A] xU))) =
      targetAct
        (induced_scalarExtension_source_hom_local
          (A := A) (G := G) (W0 := W0)
          (z ⊗ₜ[A] ((Finsupp.single g a) ⊗ₜ[A] xU))) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let sourceAct :=
    ((Representation.scalarExtension
      (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) h :
      TensorProduct A k (TensorProduct A (G →₀ A) W0) →ₗ[k]
        TensorProduct A k (TensorProduct A (G →₀ A) W0))
  let targetAct :=
    ((Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
      (Representation.scalarExtension ρA_HU)) h :
      TensorProduct k (G →₀ k) (TensorProduct A k W0) →ₗ[k]
        TensorProduct k (G →₀ k) (TensorProduct A k W0))
  let _ := sourceAct
  let _ := targetAct
  dsimp only [sourceAct, targetAct]
  -- First normalize the source action, then apply the already-proved raw singleton transport.
  rw [induced_scalarExtension_source_sourceAct_apply_single_local
    (A := A) (G := G) (ρA_HU := ρA_HU)]
  rw [induced_scalarExtension_source_hom_apply_single_local
    (A := A) (G := G) (W0 := W0)]
  -- Normalize the target action on the transported singleton tensor; both sides are now identical.
  rw [induced_scalarExtension_source_hom_apply_single_local
    (A := A) (G := G) (W0 := W0)]
  rw [induced_scalarExtension_source_targetAct_apply_single_local
    (A := A) (G := G) (ρA_HU := ρA_HU)]

/-- Helper for Theorem 17-17.3-1: the raw forward tensor transport respects the full induction
relation, so it can be descended through `Representation.Coinvariants.map`. -/
theorem induced_scalarExtension_source_hom_rel_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (h : H) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    induced_scalarExtension_source_hom_local
        (A := A) (G := G) (W0 := W0) ∘ₗ
      ((Representation.scalarExtension
        (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) h) =
      Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
          (Representation.scalarExtension ρA_HU) h ∘ₗ
        induced_scalarExtension_source_hom_local
          (A := A) (G := G) (W0 := W0) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let sourceAct :=
    ((Representation.scalarExtension
      (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) h :
      TensorProduct A k (TensorProduct A (G →₀ A) W0) →ₗ[k]
        TensorProduct A k (TensorProduct A (G →₀ A) W0))
  let targetAct :=
    ((Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
      (Representation.scalarExtension ρA_HU)) h :
      TensorProduct k (G →₀ k) (TensorProduct A k W0) →ₗ[k]
        TensorProduct k (G →₀ k) (TensorProduct A k W0))
  let sourceMap :=
    induced_scalarExtension_source_hom_local (A := A) (G := G) (W0 := W0) ∘ₗ sourceAct
  let targetMap :=
    targetAct ∘ₗ induced_scalarExtension_source_hom_local (A := A) (G := G) (W0 := W0)
  -- Extend the singleton commutation relation first across coefficient sums, then across both
  -- tensor factors, so the map descends through the full induction relation.
  apply LinearMap.ext
  intro v
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · simp [sourceAct, targetAct]
  · intro z y
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp [sourceAct, targetAct]
    · intro f xU
      induction f using Finsupp.induction_linear with
      | zero =>
          simp [sourceAct, targetAct, sourceMap, targetMap]
      | add f₁ f₂ hf₁ hf₂ =>
          simpa [sourceMap, targetMap, TensorProduct.add_tmul, TensorProduct.tmul_add,
            map_add, hf₁, hf₂]
      | single g a =>
          simpa [sourceMap, targetMap, sourceAct, targetAct] using
            induced_scalarExtension_source_hom_commutes_on_single_local
              (A := A) (G := G) (ρA_HU := ρA_HU) h z g a xU
    · intro y₁ y₂ hy₁ hy₂
      simpa [sourceMap, targetMap, TensorProduct.tmul_add, map_add, hy₁, hy₂]
  · intro v₁ v₂ hv₁ hv₂
    simpa [sourceMap, targetMap, map_add, hv₁, hv₂]

/-- Helper for Theorem 17-17.3-1: once the raw forward tensor transport is known to commute with
the induction relation, the inverse map inherits the same compatibility by transport through the
raw tensor equivalence. -/
theorem induced_scalarExtension_source_inv_rel_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (h : H) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (G →₀ k) := Finsupp.module G k
    let _ : Module k (TensorProduct A k W0) := TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    induced_scalarExtension_source_inv_local
        (A := A) (G := G) (W0 := W0) ∘ₗ
      Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
          (Representation.scalarExtension ρA_HU) h =
      ((Representation.scalarExtension
          (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) h) ∘ₗ
        induced_scalarExtension_source_inv_local
          (A := A) (G := G) (W0 := W0) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (G →₀ k) := Finsupp.module G k
  letI : Module k (TensorProduct A k W0) := TensorProduct.leftModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let rawHom :=
    induced_scalarExtension_source_hom_local (A := A) (G := G) (W0 := W0)
  let rawInv :=
    induced_scalarExtension_source_inv_local (A := A) (G := G) (W0 := W0)
  let sourceAct :=
    ((Representation.scalarExtension
      (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU)) h :
      TensorProduct A k (TensorProduct A (G →₀ A) W0) →ₗ[k]
        TensorProduct A k (TensorProduct A (G →₀ A) W0))
  let targetAct :=
    ((Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
      (Representation.scalarExtension ρA_HU)) h :
      TensorProduct k (G →₀ k) (TensorProduct A k W0) →ₗ[k]
        TensorProduct k (G →₀ k) (TensorProduct A k W0))
  let _ := rawHom
  let _ := rawInv
  let _ := sourceAct
  let _ := targetAct
  -- Conjugate the forward relation through the raw tensor equivalence instead of normalizing the
  -- inverse action separately.
  apply LinearMap.ext
  intro v
  let rawEquiv :=
    induced_scalarExtension_source_raw_tensor_equiv_local
      (A := A) (G := G) (W0 := W0)
  apply rawEquiv.injective
  have hforward :
      rawHom (sourceAct (rawInv v)) = targetAct (rawHom (rawInv v)) := by
    simpa [rawHom, sourceAct, targetAct] using
      LinearMap.congr_fun
        (induced_scalarExtension_source_hom_rel_local
          (A := A) (G := G) (ρA_HU := ρA_HU) h)
        (rawInv v)
  calc
    rawHom (rawInv (targetAct v)) = targetAct v := by
      simp [rawHom, rawInv]
    _ = targetAct (rawHom (rawInv v)) := by
      simp [rawHom, rawInv]
    _ = rawHom (sourceAct (rawInv v)) := hforward.symm



end

end Representation
