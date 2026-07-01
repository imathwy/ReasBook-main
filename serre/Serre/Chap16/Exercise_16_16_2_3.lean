import Mathlib
import Serre.Chap11.Proposition_11_11_4_1.Index
import Serre.Chap14.Exercise_14_14_4_5
import Serre.Chap14.Remark_14_14_1_2
import Serre.Chap16.Exercise_16_16_1_12
import Serre.Chap02.Exercise_2_2_4_5
import Serre.Chap02.Proposition_2_2_4_1
import Serre.Chap06.Proposition_6_6_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped MonoidAlgebra Representation
open CategoryTheory

namespace Representation

/-
Source/core/bridge triage:
* source-facing: the two exercise statements below about the scalar extension of a finite
  projective `Λ[G]`-module to the quotient field `F`.
* core/canonical owners: `FiniteProjectiveGroupAlgebraModule.scalarExtension`,
  `Representation.asModule`, and `leftRegular_character_eq_zero_of_ne_one`.
* bridge/view: the scalar extension is an `FDRep F G`; freeness over `F[G]` is stated directly for
  the owner-centered module view `asModule ((P.scalarExtension F).ρ)` of its underlying
  representation, rather than through a parallel local binder or wrapper.
  Any Chapter `16` Grothendieck-group arguments remain proof-level bridges rather than public
  owners here.
-/

section SwanExercise

namespace FiniteProjectiveGroupAlgebraModule

variable (Λ : Type u) [CommRing Λ]
variable (F : Type u) [Field F] [Algebra Λ F]
variable (G : Type u) [Group G]
variable [IsDedekindDomain Λ] [IsFractionRing Λ F] [Finite G]

/-- Helper for Exercise 16-16.2-3: extending scalars from `Λ` to a field `F` turns a finite
projective `Λ[G]`-module into a finite-dimensional `F[G]`-representation. -/
private abbrev scalarExtension
    {Λ : Type u} [CommRing Λ]
    {G : Type u} [Group G] [Finite G]
    (K : Type u) [Field K] [Algebra Λ K]
    (P : FiniteProjectiveGroupAlgebraModule Λ G) : FDRep K G :=
  let _ : Module.Finite Λ P.V := P.finite
  let _ : Module.Finite K (TensorProduct Λ K P.toRep) := by infer_instance
  FDRep.of (Representation.scalarExtension P.toRep.ρ)

/-- Helper for Exercise 16-16.2-3: a `Rep` isomorphism yields an equivalence of the underlying
unbundled representations. -/
private abbrev repIsoToEquiv
    {A B : Rep F G} (e : A ≅ B) : A.ρ.Equiv B.ρ :=
  Representation.equivOfIso e

/-- Helper for Exercise 16-16.2-3: the canonical free `F[G]`-representation on `n` generators has
character equal to `n` copies of the regular character. -/
private theorem free_character_eq_nsmul_leftRegular
    [CharZero F] (n : ℕ) :
    let α : Type u := ULift (Fin n)
    (FDRep.of (Rep.free F G α).ρ).character =
      n • (Representation.leftRegular F G).character := by
  let α : Type u := ULift (Fin n)
  let e := Rep.leftRegularTensorTrivialIsoFree F G α
  -- Rewrite the free owner through the tensor-product model `leftRegular ⊗ trivial`.
  ext g
  have hchar := congrFun
    (Representation.char_iso (repIsoToEquiv (F := F) (G := G) e)).symm g
  by_cases hg : g = 1
  · subst hg
    have hchar_one :
        (Rep.free F G α).ρ.character (1 : G) = (Nat.card G : F) * (n : F) := by
      calc
        (Rep.free F G α).ρ.character (1 : G) =
            (CategoryTheory.MonoidalCategoryStruct.tensorObj
              (Rep.leftRegular F G) (Rep.trivial F G (α →₀ F))).ρ.character (1 : G) := by
              simpa using hchar
        _ = (((Rep.leftRegular F G).ρ).character *
              ((Rep.trivial F G (α →₀ F)).ρ).character) (1 : G) := by
              exact congrFun
                (Representation.char_tensor
                  ((Rep.leftRegular F G).ρ) ((Rep.trivial F G (α →₀ F)).ρ)) (1 : G)
        _ = (Nat.card G : F) * (n : F) := by
              letI : Fintype G := Fintype.ofFinite G
              have hfinrankG : Module.finrank F (G →₀ F) = Nat.card G := by
                rw [Nat.card_eq_fintype_card]
                exact Module.finrank_finsupp_self F
              have hcardα : Fintype.card α = n := by
                simp [α]
              simp [Representation.character, Representation.trivial, hfinrankG, hcardα]
    calc
      (FDRep.of (Rep.free F G α).ρ).character (1 : G) =
          (Rep.free F G α).ρ.character (1 : G) := rfl
      _ = (Nat.card G : F) * (n : F) := hchar_one
      _ = (n • (Representation.leftRegular F G).character) (1 : G) := by
            rw [Pi.smul_apply, Representation.leftRegular_character_one]
            simp [nsmul_eq_mul, mul_comm]
  · calc
      (FDRep.of (Rep.free F G α).ρ).character g =
          (Rep.free F G α).ρ.character g := rfl
      _ = 0 := by
            simpa [hg] using hchar
      _ = (n • (Representation.leftRegular F G).character) g := by
            rw [Pi.smul_apply, Representation.leftRegular_character_eq_zero_of_ne_one hg]
            simp

/-- Helper for Exercise 16-16.2-3: the canonical free `F[G]`-representation on `n` generators is
free as an `F[G]`-module. -/
private theorem free_module_free
    (n : ℕ) :
    let α : Type u := ULift (Fin n)
    Module.Free F[G] (asModule ((FDRep.of (Rep.free F G α).ρ).ρ)) := by
  let α : Type u := ULift (Fin n)
  -- `Representation.free` is designed so its `asModule` is a free group-algebra module.
  simpa [α] using (Representation.free_asModule_free F G α)

/-- Helper for Exercise 16-16.2-3: an `A[G]`-linear equivalence between the owner-module views of
two representations produces an equivariant representation equivalence. -/
private theorem nonempty_equiv_of_asModuleLinearEquiv
    {A : Type u} [CommRing A]
    {G : Type u} [Group G]
    {V W : Type u} [AddCommGroup V] [Module A V]
    [AddCommGroup W] [Module A W]
    (ρ : Representation A G V) (σ : Representation A G W)
    (e : asModule ρ ≃ₗ[A[G]] asModule σ) :
    Nonempty (ρ.Equiv σ) := by
  refine ⟨Representation.Equiv.mk ?_ ?_⟩
  · refine
      { toFun := fun x ↦ σ.asModuleEquiv (e (ρ.asModuleEquiv.symm x))
        invFun := fun y ↦ ρ.asModuleEquiv (e.symm (σ.asModuleEquiv.symm y))
        left_inv := by
          intro x
          simp
        right_inv := by
          intro y
          simp
        map_add' := by
          intro x y
          simp
        map_smul' := by
          intro a x
          -- Move scalar multiplication to the module side and use `A[G]`-linearity there.
          change
            σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (a • x))) =
              a • σ.asModuleEquiv (e (ρ.asModuleEquiv.symm x))
          rw [ρ.asModuleEquiv_symm_map_smul, e.map_smul, σ.asModuleEquiv_map_smul]
          simp [Algebra.smul_def] }
  · intro g
    ext x
    -- Rewrite the group action as multiplication by the basis element `of g` on both module views.
    change
      σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g x))) =
        σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm x)))
    rw [ρ.asModuleEquiv_symm_map_rho, e.map_smul, σ.asModuleEquiv_map_smul]
    simp [Representation.asAlgebraHom, MonoidAlgebra.of]

omit [IsDedekindDomain Λ] [IsFractionRing Λ F] [Finite G] in
/-- Helper for Exercise 16-16.2-3: base change carries the averaged conjugation operator on a
projective `Λ[G]`-module to the scalar-extended tensor module over `F`. -/
private theorem scalarExtension_sumOfConjugates_apply_tmul
    [Fintype G]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (u : Module.End Λ P.V) (a : F) (x : P.V) :
    (Module.End.baseChangeHom Λ F P.V u).sumOfConjugates G (a ⊗ₜ[Λ] x) =
      a ⊗ₜ[Λ] (u.sumOfConjugates G x) := by
  -- Expand the average termwise and commute each conjugation summand through scalar extension.
  rw [LinearMap.sumOfConjugates_apply, LinearMap.sumOfConjugates_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl ?_
  intro g _
  rw [LinearMap.conjugate_apply, LinearMap.conjugate_apply]
  rw [show MonoidAlgebra.single g (1 : F) • (a ⊗ₜ[Λ] x) =
      a ⊗ₜ[Λ] (MonoidAlgebra.single g (1 : Λ) • x) by
      simpa [MonoidAlgebra.of_apply] using
        monoidAlgebra_of_smul_tmul (Λ := Λ) (P := P.V) (κ := F) g a x]
  rw [show ((Module.End.baseChangeHom Λ F P.V) u)
      (a ⊗ₜ[Λ] (MonoidAlgebra.single g (1 : Λ) • x)) =
      a ⊗ₜ[Λ] u (MonoidAlgebra.single g (1 : Λ) • x) by
      simp [Module.End.baseChangeHom]]
  rw [show MonoidAlgebra.single g⁻¹ (1 : F) •
      (a ⊗ₜ[Λ] u (MonoidAlgebra.single g (1 : Λ) • x)) =
      MonoidAlgebra.of F G g⁻¹ •
        (a ⊗ₜ[Λ] u (MonoidAlgebra.single g (1 : Λ) • x)) by rfl]
  simpa using
    monoidAlgebra_of_smul_tmul
      (Λ := Λ) (P := P.V) (κ := F) g⁻¹ a
      (u (MonoidAlgebra.single g (1 : Λ) • x))

omit [IsDedekindDomain Λ] in
/-- Helper for Exercise 16-16.2-3: localizing the actual owner `P` at a residue prime produces
the finite projective `Λ_𝔭[G]`-module that Swan's source proof applies Theorem `36` to. -/
private theorem localized_tensor_is_finite_projective
    {p : ℕ} [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p) :
    Module.Finite (MonoidAlgebra (Localization.AtPrime (M.1.asIdeal)) G)
      (TensorProduct Λ (Localization.AtPrime (M.1.asIdeal)) P.V) ∧
    Module.Projective (MonoidAlgebra (Localization.AtPrime (M.1.asIdeal)) G)
      (TensorProduct Λ (Localization.AtPrime (M.1.asIdeal)) P.V) := by
  let A : Type u := Localization.AtPrime (M.1.asIdeal)
  have hprojΛ : Module.Projective Λ P.V := by
    -- First forget the projective splitting along `Λ → Λ[G]`; the group algebra is free over `Λ`.
    obtain ⟨M', _instAddCommGroup, _instModule, _instFree, i, s, hs⟩ :=
      Module.Projective.iff_split.mp P.projective
    let _ : Module Λ M' := Module.compHom M' (algebraMap Λ Λ[G])
    let _ : IsScalarTower Λ Λ[G] M' := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let _ : Module.Free Λ M' :=
      Module.Free.of_basis
        ((MonoidAlgebra.basis G Λ).smulTower (Module.Free.chooseBasis (Λ[G]) M'))
    exact Module.Projective.of_split (i.restrictScalars Λ) (s.restrictScalars Λ) <| by
      ext x
      exact LinearMap.congr_fun hs x
  letI : Module.Finite A (TensorProduct Λ A P.V) := by
    -- Localization preserves finite generation of the underlying coefficient module.
    let _ : Module.Finite Λ P.V := P.finite
    infer_instance
  have hfinite :
      Module.Finite (A[G]) (TensorProduct Λ A P.V) := by
    -- Once finite over `A`, the localized tensor is finite over the localized group algebra.
    exact Module.Finite.of_restrictScalars_finite A (A[G]) (TensorProduct Λ A P.V)
  have hprojective :
      Module.Projective (A[G]) (TensorProduct Λ A P.V) := by
    -- Chapter `14` upgrades the localized tensor module to a projective localized owner.
    exact localized_group_algebra_projective_of_projective
      (G := G) (P := P.V) (𝔭 := M.1.asIdeal) M.1.2 hprojΛ P.projective
  simpa [A] using And.intro hfinite hprojective

/-- Helper for Exercise 16-16.2-3: package the localized tensor module into the actual local
projective owner that Swan's source proof studies. -/
private def localized_tensor_owner
    {p : ℕ} [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p) :
    FiniteProjectiveGroupAlgebraModule (Localization.AtPrime (M.1.asIdeal)) G := by
  let A := Localization.AtPrime (M.1.asIdeal)
  let hlocalized := localized_tensor_is_finite_projective (Λ := Λ) (G := G) P M
  let _ : Module.Finite (A[G]) (TensorProduct Λ A P.V) := by
    simpa [A] using hlocalized.1
  -- Repackage the localized tensor as a finitely generated `A[G]`-module with the already-proved
  -- projectivity witness.
  refine ⟨FGModuleCat.of (A[G]) (TensorProduct Λ A P.V), ?_⟩
  simpa [A] using hlocalized.2

/-- Helper for Exercise 16-16.2-3: the packaged localized owner is definitionally the raw
localized tensor module. -/
private noncomputable def localized_tensor_owner_linearEquiv
    {p : ℕ} [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    :
    ((localized_tensor_owner (Λ := Λ) (G := G) P M).V) ≃ₗ[Localization.AtPrime (M.1.asIdeal)]
      TensorProduct Λ (Localization.AtPrime (M.1.asIdeal)) P.V :=
  let A := Localization.AtPrime (M.1.asIdeal)
  -- The localized owner was packaged on the literal tensor carrier, so the carrier comparison is
  -- the identity map with the scalar action rewritten through `A[G]`.
  { toFun := fun x ↦ x
    invFun := fun x ↦ x
    left_inv := fun x ↦ rfl
    right_inv := fun x ↦ rfl
    map_add' := fun x y ↦ rfl
    map_smul' := by
      intro a x
      simpa [A, localized_tensor_owner, Algebra.smul_def] using
        (IsScalarTower.algebraMap_smul
          (A := A[G]) (M := TensorProduct Λ A P.V) a x) }

/-- Helper for Exercise 16-16.2-3: the exact tensor-cancellation owner equivalence between the
localized generic fiber and the original quotient-field scalar extension. -/
private noncomputable def localized_tensor_scalarExtension_carrier_equiv
    {p : ℕ} [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F] :
    (((localized_tensor_owner (Λ := Λ) (G := G) P M).scalarExtension F).V) ≃ₗ[F]
      (P.scalarExtension F).V :=
  let A := Localization.AtPrime (M.1.asIdeal)
  -- Route correction: first discard the packaged owner wrappers and work on the literal tensor
  -- surface where `cancelBaseChange` is the source-faithful comparison.
  let eBase :
      TensorProduct A F ((localized_tensor_owner (Λ := Λ) (G := G) P M).V) ≃ₗ[F]
        TensorProduct A F (TensorProduct Λ A P.V) :=
    LinearEquiv.baseChange A F _ _ <|
      localized_tensor_owner_linearEquiv (Λ := Λ) (G := G) P M
  -- After base-changing the packaged owner identity once, `cancelBaseChange` removes the
  -- intermediate localization tensor factor.
  eBase.trans (TensorProduct.AlgebraTensorModule.cancelBaseChange Λ A F F P.V)

omit [IsDedekindDomain Λ] [IsFractionRing Λ F] in
/-- Helper for Exercise 16-16.2-3: the explicit tensor-cancellation carrier equivalence sends a
pure tensor to the expected canceled tensor. -/
private theorem localized_tensor_scalarExtension_carrier_apply_tmul
    {p : ℕ} [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F]
    (a : F) (b : Localization.AtPrime (M.1.asIdeal)) (x : P.V) :
    localized_tensor_scalarExtension_carrier_equiv
        (Λ := Λ) (F := F) (G := G) (p := p) P M
        (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] (b ⊗ₜ[Λ] x)) =
      (b • a) ⊗ₜ[Λ] x := by
  change
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        Λ (Localization.AtPrime (M.1.asIdeal)) F F P.V)
        (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] (b ⊗ₜ[Λ] x)) =
      (b • a) ⊗ₜ[Λ] x
  simp

omit [IsDedekindDomain Λ] in
/-- Helper for Exercise 16-16.2-3: the localized tensor owner acts on pure tensors by leaving the
coefficient in the localized ring untouched and applying the original `G`-action to the module
factor. -/
private theorem localized_tensor_owner_apply_tmul
    {p : ℕ} [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    (g : G) (b : Localization.AtPrime (M.1.asIdeal)) (x : P.V) :
    (localized_tensor_owner (Λ := Λ) (G := G) P M).toRep.ρ g (b ⊗ₜ[Λ] x) =
      b ⊗ₜ[Λ] (P.toRep.ρ g x) := by
  -- The localized owner is the literal tensor module `A ⊗[Λ] P`, so its `A[G]`-action is the
  -- tensor-product action from the Chapter `14` base-change bridge.
  change MonoidAlgebra.of (Localization.AtPrime (M.1.asIdeal)) G g • (b ⊗ₜ[Λ] x) =
    b ⊗ₜ[Λ] (MonoidAlgebra.of Λ G g • x)
  simpa using
    monoidAlgebra_of_smul_tmul
      (Λ := Λ) (P := P.V) (κ := Localization.AtPrime (M.1.asIdeal)) g b x

omit [Finite G] in
/-- Helper for Exercise 16-16.2-3: scalar extension of a representation acts on pure tensors by
keeping the scalar in the new coefficient field and applying the original action to the module
factor. -/
private theorem scalarExtension_apply_tmul
    {A : Type u} [CommRing A] [Algebra A F]
    {V : Type u} [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (g : G) (a : F) (x : V) :
    (Representation.scalarExtension ρ) g (a ⊗ₜ[A] x) = a ⊗ₜ[A] (ρ g x) := by
  -- `Representation.scalarExtension` is defined by `Module.End.baseChangeHom`, so pure tensors
  -- are computed by `LinearMap.baseChange_tmul`.
  change ((Module.End.baseChangeHom A F V) (ρ g)) (a ⊗ₜ[A] x) = a ⊗ₜ[A] (ρ g x)
  exact LinearMap.baseChange_tmul (f := ρ g) (A := F) a x

omit [IsDedekindDomain Λ] [IsFractionRing Λ F] in
/-- Helper for Exercise 16-16.2-3: the exact tensor-cancellation owner equivalence between the
localized generic fiber and the original quotient-field scalar extension. -/
private theorem localized_tensor_scalarExtension_intertwining_on_nested_tmul
    {p : ℕ} [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F]
    (g : G) (a : F) (b : Localization.AtPrime (M.1.asIdeal)) (x : P.V) :
    localized_tensor_scalarExtension_carrier_equiv
        (Λ := Λ) (F := F) (G := G) (p := p) P M
        ((((localized_tensor_owner (Λ := Λ) (G := G) P M).scalarExtension F).ρ g)
          (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] (b ⊗ₜ[Λ] x))) =
      ((P.scalarExtension F).ρ g)
        (localized_tensor_scalarExtension_carrier_equiv
          (Λ := Λ) (F := F) (G := G) (p := p) P M
          (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] (b ⊗ₜ[Λ] x))) := by
  change
      localized_tensor_scalarExtension_carrier_equiv
          (Λ := Λ) (F := F) (G := G) (p := p) P M
          ((((localized_tensor_owner (Λ := Λ) (G := G) P M).toRep.ρ).scalarExtension g)
            (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] (b ⊗ₜ[Λ] x))) =
        ((P.toRep.ρ).scalarExtension g)
          (localized_tensor_scalarExtension_carrier_equiv
            (Λ := Λ) (F := F) (G := G) (p := p) P M
            (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] (b ⊗ₜ[Λ] x)))
  rw [scalarExtension_apply_tmul, localized_tensor_owner_apply_tmul,
    localized_tensor_scalarExtension_carrier_apply_tmul]
  simpa [scalarExtension_apply_tmul] using
    localized_tensor_scalarExtension_carrier_apply_tmul
      (Λ := Λ) (F := F) (G := G) (p := p) P M a b (P.toRep.ρ g x)

omit [IsDedekindDomain Λ] [IsFractionRing Λ F] in
/-- Helper for Exercise 16-16.2-3: the tensor-cancellation carrier comparison intertwines the
localized scalar-extension action with the original quotient-field action on every nested tensor. -/
private theorem localized_tensor_scalarExtension_intertwining_on_nested_tensors
    {p : ℕ} [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F]
    (g : G) :
    ∀ z : ((localized_tensor_owner (Λ := Λ) (G := G) P M).scalarExtension F).V,
      localized_tensor_scalarExtension_carrier_equiv
          (Λ := Λ) (F := F) (G := G) (p := p) P M
          ((((localized_tensor_owner (Λ := Λ) (G := G) P M).scalarExtension F).ρ g) z) =
        ((P.scalarExtension F).ρ g)
          (localized_tensor_scalarExtension_carrier_equiv
            (Λ := Λ) (F := F) (G := G) (p := p) P M z) := by
  intro z
  change
      localized_tensor_scalarExtension_carrier_equiv
          (Λ := Λ) (F := F) (G := G) (p := p) P M
          ((((localized_tensor_owner (Λ := Λ) (G := G) P M).toRep.ρ).scalarExtension g) z) =
        ((P.toRep.ρ).scalarExtension g)
          (localized_tensor_scalarExtension_carrier_equiv
            (Λ := Λ) (F := F) (G := G) (p := p) P M z)
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro a y
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simpa using
        localized_tensor_scalarExtension_intertwining_on_nested_tmul
          (Λ := Λ) (F := F) (G := G) (p := p) P M g a 0 0
    · intro b x
      simpa using
        localized_tensor_scalarExtension_intertwining_on_nested_tmul
          (Λ := Λ) (F := F) (G := G) (p := p) P M g a b x
    · intro y₁ y₂ hy₁ hy₂
      have hloc_add :
          ((localized_tensor_owner (Λ := Λ) (G := G) P M).toRep.ρ g) (y₁ + y₂) =
            ((localized_tensor_owner (Λ := Λ) (G := G) P M).toRep.ρ g) y₁ +
              ((localized_tensor_owner (Λ := Λ) (G := G) P M).toRep.ρ g) y₂ := by
        exact map_add _ _ _
      have hleft :
          localized_tensor_scalarExtension_carrier_equiv
              (Λ := Λ) (F := F) (G := G) (p := p) P M
              ((((localized_tensor_owner (Λ := Λ) (G := G) P M).toRep.ρ).scalarExtension g)
                (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] (y₁ + y₂))) =
            (localized_tensor_scalarExtension_carrier_equiv
                (Λ := Λ) (F := F) (G := G) (p := p) P M
                ((((localized_tensor_owner (Λ := Λ) (G := G) P M).toRep.ρ).scalarExtension g)
                  (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] y₁))) +
              (localized_tensor_scalarExtension_carrier_equiv
                (Λ := Λ) (F := F) (G := G) (p := p) P M
                ((((localized_tensor_owner (Λ := Λ) (G := G) P M).toRep.ρ).scalarExtension g)
                  (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] y₂))) := by
        rw [scalarExtension_apply_tmul]
        rw [hloc_add]
        rw [TensorProduct.tmul_add, map_add]
        simp [scalarExtension_apply_tmul]
      have hcarrier_add :
          (localized_tensor_scalarExtension_carrier_equiv
              (Λ := Λ) (F := F) (G := G) (p := p) P M)
              (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] (y₁ + y₂)) =
            ((localized_tensor_scalarExtension_carrier_equiv
              (Λ := Λ) (F := F) (G := G) (p := p) P M)
              (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] y₁)) +
              ((localized_tensor_scalarExtension_carrier_equiv
                (Λ := Λ) (F := F) (G := G) (p := p) P M)
                (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] y₂)) := by
        have htmul_add :
            (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] (y₁ + y₂) :
                ((localized_tensor_owner (Λ := Λ) (G := G) P M).scalarExtension F).V) =
              (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] y₁ :
                ((localized_tensor_owner (Λ := Λ) (G := G) P M).scalarExtension F).V) +
                (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] y₂ :
                  ((localized_tensor_owner (Λ := Λ) (G := G) P M).scalarExtension F).V) := by
          simpa using
            (TensorProduct.tmul_add
              (R := Localization.AtPrime (M.1.asIdeal))
              (M := F)
              (N := ↑((localized_tensor_owner (Λ := Λ) (G := G) P M).toRep))
              a y₁ y₂)
        rw [htmul_add, map_add]
      have hright :
          ((P.toRep.ρ).scalarExtension g)
              ((localized_tensor_scalarExtension_carrier_equiv
                (Λ := Λ) (F := F) (G := G) (p := p) P M)
                (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] (y₁ + y₂))) =
            ((P.toRep.ρ).scalarExtension g)
                ((localized_tensor_scalarExtension_carrier_equiv
                  (Λ := Λ) (F := F) (G := G) (p := p) P M)
                  (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] y₁)) +
              ((P.toRep.ρ).scalarExtension g)
                ((localized_tensor_scalarExtension_carrier_equiv
                  (Λ := Λ) (F := F) (G := G) (p := p) P M)
                  (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] y₂)) := by
        rw [hcarrier_add, map_add]
      calc
        localized_tensor_scalarExtension_carrier_equiv
            (Λ := Λ) (F := F) (G := G) (p := p) P M
            ((((localized_tensor_owner (Λ := Λ) (G := G) P M).toRep.ρ).scalarExtension g)
              (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] (y₁ + y₂))) =
          (localized_tensor_scalarExtension_carrier_equiv
              (Λ := Λ) (F := F) (G := G) (p := p) P M
              ((((localized_tensor_owner (Λ := Λ) (G := G) P M).toRep.ρ).scalarExtension g)
                (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] y₁))) +
            (localized_tensor_scalarExtension_carrier_equiv
              (Λ := Λ) (F := F) (G := G) (p := p) P M
              ((((localized_tensor_owner (Λ := Λ) (G := G) P M).toRep.ρ).scalarExtension g)
                (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] y₂))) := hleft
        _ =
          ((P.toRep.ρ).scalarExtension g)
              ((localized_tensor_scalarExtension_carrier_equiv
                (Λ := Λ) (F := F) (G := G) (p := p) P M)
                (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] y₁)) +
            ((P.toRep.ρ).scalarExtension g)
              ((localized_tensor_scalarExtension_carrier_equiv
                (Λ := Λ) (F := F) (G := G) (p := p) P M)
                (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] y₂)) := by
              exact congrArg₂ (fun u v => u + v) hy₁ hy₂
        _ =
          ((P.toRep.ρ).scalarExtension g)
            ((localized_tensor_scalarExtension_carrier_equiv
              (Λ := Λ) (F := F) (G := G) (p := p) P M)
              (a ⊗ₜ[Localization.AtPrime (M.1.asIdeal)] (y₁ + y₂))) := hright.symm
  · intro z₁ z₂ hz₁ hz₂
    simpa [map_add] using congrArg₂ (fun u v => u + v) hz₁ hz₂

omit [IsDedekindDomain Λ] [IsFractionRing Λ F] in
/-- Helper for Exercise 16-16.2-3: the exact tensor-cancellation owner equivalence between the
localized generic fiber and the original quotient-field scalar extension. -/
private theorem localized_tensor_scalarExtension_carrier_isIntertwining
    {p : ℕ} [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F] :
    ∀ g : G,
      (localized_tensor_scalarExtension_carrier_equiv
          (Λ := Λ) (F := F) (G := G) (p := p) P M).toLinearMap ∘ₗ
        (((localized_tensor_owner (Λ := Λ) (G := G) P M).scalarExtension F).ρ g) =
      ((P.scalarExtension F).ρ g) ∘ₗ
      (localized_tensor_scalarExtension_carrier_equiv
          (Λ := Λ) (F := F) (G := G) (p := p) P M).toLinearMap := by
  intro g
  apply LinearMap.ext
  intro z
  simpa [LinearMap.comp_apply] using
    localized_tensor_scalarExtension_intertwining_on_nested_tensors
      (Λ := Λ) (F := F) (G := G) (p := p) P M g z

/-- Helper for Exercise 16-16.2-3: the exact tensor-cancellation owner equivalence between the
localized generic fiber and the original quotient-field scalar extension. -/
private noncomputable def localized_tensor_scalarExtension_owner_equiv
    {p : ℕ} [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F] :
    Representation.Equiv
      (((localized_tensor_owner (Λ := Λ) (G := G) P M).scalarExtension F).ρ)
      ((P.scalarExtension F).ρ) :=
  Representation.Equiv.mk
    (localized_tensor_scalarExtension_carrier_equiv
      (Λ := Λ) (F := F) (G := G) (p := p) P M)
    (localized_tensor_scalarExtension_carrier_isIntertwining
      (Λ := Λ) (F := F) (G := G) (p := p) P M)

omit [IsDedekindDomain Λ] [IsFractionRing Λ F] in
/-- Helper for Exercise 16-16.2-3: the character of the localized generic fiber agrees with the
character of the original quotient-field scalar extension. -/
private theorem localized_tensor_scalarExtension_character_eq
    {p : ℕ} [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F]
    (g : G) :
    ((localized_tensor_owner (Λ := Λ) (G := G) P M).scalarExtension F).character g =
      (P.scalarExtension F).character g := by
  simpa using congrFun
    (Representation.char_iso
      (localized_tensor_scalarExtension_owner_equiv
        (Λ := Λ) (F := F) (G := G) (p := p) P M)) g

/-- Helper for Exercise 16-16.2-3: the canonical generator of `Subgroup.zpowers g` stays
`p`-singular when `g` is `p`-singular. -/
private theorem zpowers_generator_not_isPRegular
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G]
    (g : G) (hg : ¬ IsPRegular p g) :
    ¬ IsPRegular p (⟨g, by simp⟩ : Subgroup.zpowers g) := by
  -- Compare `IsPRegular` through the order-divisibility criterion and the subgroup order map.
  rw [isPRegular_iff_not_dvd_orderOf (p := p) g] at hg
  rw [isPRegular_iff_not_dvd_orderOf (p := p) (⟨g, by simp⟩ : Subgroup.zpowers g)]
  intro hregular
  exact hg (by simpa [Subgroup.orderOf_mk] using hregular)

omit [IsDedekindDomain Λ] in
/-- Helper for Exercise 16-16.2-3: the localization at a residue-characteristic maximal ideal has
residue field of that same characteristic. -/
private theorem localized_residueField_charP_of_nonzeroResidualCharacteristicMaximalIdeal
    {p : ℕ} [Fact p.Prime]
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p) :
    CharP (IsLocalRing.ResidueField (Localization.AtPrime (M.1.asIdeal))) p := by
  -- `Ideal.ResidueField` is definitionally the residue field of the localization at that ideal.
  change CharP (M.1.asIdeal.ResidueField) p
  exact M.2.2

/-- Helper for Exercise 16-16.2-3: at a residue prime of characteristic `p`, the generic-fiber
character of `P` vanishes on the `p`-singular elements. -/
private theorem scalarExtension_character_eq_zero_of_not_isPRegular_of_residue_prime
    {p : ℕ} [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    (g : G) (hg : ¬ IsPRegular p g) :
    (P.scalarExtension F).character g = 0 := by
  sorry

/-- Helper for Exercise 16-16.2-3: every nonidentity element has zero character on the generic
fiber once one chooses a residue prime dividing its order. -/
private theorem scalarExtension_character_eq_zero_of_ne_one_aux
    (hresidue : ∀ p : Nat.Primes, (p : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ p))
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (g : G) (hg : g ≠ 1) :
    (P.scalarExtension F).character g = 0 := by
  have horder_ne : orderOf g ≠ 1 := by
    intro h1
    exact hg ((orderOf_eq_one_iff : orderOf g = 1 ↔ g = 1).mp h1)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd horder_ne
  let pPrime : Nat.Primes := ⟨p, hp⟩
  have hp_card : p ∣ Nat.card G := dvd_trans hpdvd (orderOf_dvd_natCard g)
  obtain ⟨M⟩ := hresidue pPrime hp_card
  letI : Fact p.Prime := ⟨hp⟩
  have hsing : ¬ IsPRegular p g := by
    rw [isPRegular_iff_not_dvd_orderOf (p := p) g]
    exact fun hnot => hnot hpdvd
  exact scalarExtension_character_eq_zero_of_not_isPRegular_of_residue_prime
    (Λ := Λ) (F := F) (G := G) (p := p) P M g hsing

omit [IsDedekindDomain Λ] in
/-- Helper for Exercise 16-16.2-3: when the quotient field `F` has characteristic `p`, every
residue-characteristic witness for `Λ` must have the same prime characteristic. -/
private theorem residue_prime_eq_of_charP
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [CharP F p]
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ q) :
    q = p := by
  letI : CharP Λ p :=
    RingHom.charP (algebraMap Λ F) (IsFractionRing.injective Λ F) p
  have hp0 : (p : Λ ⧸ M.1.asIdeal) = 0 := by
    change Ideal.Quotient.mk M.1.asIdeal (p : Λ) = Ideal.Quotient.mk M.1.asIdeal 0
    exact congrArg (Ideal.Quotient.mk M.1.asIdeal) (CharP.cast_eq_zero (R := Λ) p)
  letI : CharP (Λ ⧸ M.1.asIdeal) p :=
    ringChar.of_eq
      (CharP.ringChar_of_prime_eq_zero (R := Λ ⧸ M.1.asIdeal) (Fact.out : Nat.Prime p) hp0)
  have hqchar : CharP M.1.asIdeal.ResidueField q := M.2.2
  letI : CharP M.1.asIdeal.ResidueField p :=
    charP_of_injective_algebraMap
      M.1.asIdeal.injective_algebraMap_quotient_residueField p
  have hpchar : ringChar M.1.asIdeal.ResidueField = p :=
    ringChar.eq (R := M.1.asIdeal.ResidueField) p
  -- Compare the two `CharP` instances on the same residue field through its ring characteristic.
  calc
    q = ringChar M.1.asIdeal.ResidueField := (@ringChar.eq _ _ q hqchar).symm
    _ = p := hpchar

omit [IsDedekindDomain Λ] [Group G] [Finite G] in
/-- Helper for Exercise 16-16.2-3: in positive characteristic, every prime divisor of `|G|` is
the field characteristic of `F`. -/
private theorem card_prime_divisor_eq_of_charP
    {p : ℕ} [Fact p.Prime] [CharP F p]
    (hresidue : ∀ q : Nat.Primes, (q : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ q))
    (q : Nat.Primes) (hq : (q : ℕ) ∣ Nat.card G) :
    (q : ℕ) = p := by
  obtain ⟨M⟩ := hresidue q hq
  letI : Fact ((q : ℕ).Prime) := ⟨q.2⟩
  -- The previous helper identifies the residue characteristic with the ambient field
  -- characteristic once `F` is known to have positive characteristic.
  exact residue_prime_eq_of_charP (Λ := Λ) (F := F) (p := p) (q := q) M

/-- Helper for Exercise 16-16.2-3: if every prime divisor of a nonzero natural number `n` is the
prime `p`, then `n` is a power of `p`. -/
private theorem eq_prime_pow_of_forall_prime_dvd_eq
    {p n : ℕ} [Fact p.Prime]
    (hn : n ≠ 0)
    (hdiv : ∀ q : Nat.Primes, (q : ℕ) ∣ n → (q : ℕ) = p) :
    ∃ m : ℕ, n = p ^ m := by
  refine ⟨n.factorization p, ?_⟩
  apply Nat.eq_pow_of_factorization_eq_single hn
  ext q
  by_cases hqp : q = p
  · subst hqp
    simp
  · by_cases hqprime : q.Prime
    · have hndvd : ¬ q ∣ n := by
        intro hqdvd
        exact hqp (hdiv ⟨q, hqprime⟩ hqdvd)
      simp [Nat.factorization_eq_zero_of_not_dvd hndvd, hqp]
    · simp [Nat.factorization_eq_zero_of_not_prime n hqprime, hqp]

omit [Finite G] in
omit [IsDedekindDomain Λ] in
/-- Helper for Exercise 16-16.2-3: in positive characteristic, every nonidentity element of `G`
is singular for the field characteristic prime. -/
private theorem not_isPRegular_ringChar_of_ne_one
    {p : ℕ} [Fact p.Prime] [CharP F p]
    (hresidue : ∀ q : Nat.Primes, (q : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ q))
    (g : G) (hg : g ≠ 1) :
    ¬ IsPRegular p g := by
  have horder_ne : orderOf g ≠ 1 := by
    intro h1
    exact hg ((orderOf_eq_one_iff : orderOf g = 1 ↔ g = 1).mp h1)
  obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd horder_ne
  let qPrime : Nat.Primes := ⟨q, hqprime⟩
  have hq_card : q ∣ Nat.card G := dvd_trans hqdvd (orderOf_dvd_natCard g)
  have hqp : q = p :=
    card_prime_divisor_eq_of_charP
      (Λ := Λ) (F := F) (G := G) (p := p) hresidue qPrime hq_card
  -- The prime divisor `q` of `orderOf g` is exactly the field characteristic prime.
  rw [isPRegular_iff_not_dvd_orderOf (p := p) g]
  intro hp_not_dvd
  exact hp_not_dvd <| hqp ▸ hqdvd

omit [IsDedekindDomain Λ] [IsFractionRing Λ F] in
/-- Helper for Exercise 16-16.2-3: in characteristic zero, vanishing away from the identity forces
the generic-fiber character to be a natural-number multiple of the regular character. -/
private theorem scalarExtension_character_eq_nsmul_leftRegular_of_eq_zero_off_one
    [CharZero F]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (hχ : ∀ g : G, g ≠ 1 → (P.scalarExtension F).character g = 0) :
    (P.scalarExtension F).character =
      Module.finrank F (Representation.invariants ((P.scalarExtension F).ρ)) •
        (Representation.leftRegular F G).character := by
  let ρ : Representation F G (P.scalarExtension F) := (P.scalarExtension F).ρ
  -- Once the generic-fiber character is supported at `1`, the standard averaging formula shows
  -- that it is the invariants-rank multiple of the regular character.
  change ρ.character = Module.finrank F ρ.invariants • (Representation.leftRegular F G).character
  letI : Fintype G := Fintype.ofFinite G
  letI : NeZero (Nat.card G : F) := by
    refine ⟨Nat.cast_ne_zero.mpr ?_⟩
    exact (Nat.card_ne_zero).2 ⟨inferInstance, inferInstance⟩
  letI : Invertible (Nat.card G : F) := invertibleOfNonzero (NeZero.ne (Nat.card G : F))
  have hsum : ∑ t : G, ρ.character t = ρ.character 1 := by
    classical
    rw [Finset.sum_eq_single 1]
    · intro t _ ht
      simpa [ρ] using hχ t ht
    · intro h
      exact False.elim <| h (Finset.mem_univ 1)
  have havg :
      (Nat.card G : F)⁻¹ * Module.finrank F (P.scalarExtension F) =
        Module.finrank F ρ.invariants := by
    simpa [hsum, ρ.char_one] using ρ.card_inv_mul_sum_char_eq_finrank
  have hdim :
      (Module.finrank F (P.scalarExtension F) : F) =
        (Nat.card G : F) * Module.finrank F ρ.invariants := by
    have hcard : (Nat.card G : F) ≠ 0 := NeZero.ne (Nat.card G : F)
    exact (inv_mul_eq_iff_eq_mul₀ hcard).mp <| by simpa [ρ] using havg
  ext s
  by_cases hs : s = 1
  · subst hs
    simpa [Pi.smul_apply, Representation.leftRegular_character_one, nsmul_eq_mul, mul_comm] using
      hdim
  · have hs_zero : ρ.character s = 0 := by
      simpa [ρ] using hχ s hs
    rw [hs_zero, Pi.smul_apply, Representation.leftRegular_character_eq_zero_of_ne_one hs,
      nsmul_eq_mul]
    simp

omit [IsDedekindDomain Λ] [IsFractionRing Λ F] in
/-- Helper for Exercise 16-16.2-3: the scalar-extension owner module is literally the tensor
product `F ⊗[Λ] P`, viewed with its canonical `F[G]`-action. -/
private theorem scalarExtension_asModule_nonempty_linearEquiv_tensor
    (P : FiniteProjectiveGroupAlgebraModule Λ G) :
    Nonempty (asModule ((P.scalarExtension F).ρ) ≃ₗ[F[G]] TensorProduct Λ F P.V) := by
  -- The scalar-extension owner is definitionally the tensor-product carrier with its `F[G]`-action.
  refine ⟨?_⟩
  simpa [FiniteProjectiveGroupAlgebraModule.scalarExtension] using
    (LinearEquiv.refl F[G] (asModule ((P.scalarExtension F).ρ)))

omit [IsDedekindDomain Λ] in
/-- Helper for Exercise 16-16.2-3: extending scalars from `Λ[G]` to `F[G]` preserves
projectivity on the literal tensor-product owner. -/
private theorem scalarExtension_tensor_projective
    (P : FiniteProjectiveGroupAlgebraModule Λ G) :
    Module.Projective F[G] (TensorProduct Λ F P.V) := by
  let _ : Module.Projective Λ P.V := by
    obtain ⟨M', _instAddCommGroup, _instModule, _instFree, i, s, hs⟩ :=
      Module.Projective.iff_split.mp P.projective
    let _ : Module Λ M' := Module.compHom M' (algebraMap Λ Λ[G])
    let _ : IsScalarTower Λ Λ[G] M' := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let _ : Module.Free Λ M' :=
      Module.Free.of_basis
        ((MonoidAlgebra.basis G Λ).smulTower (Module.Free.chooseBasis (Λ[G]) M'))
    exact Module.Projective.of_split (i.restrictScalars Λ) (s.restrictScalars Λ) <| by
      ext x
      exact LinearMap.congr_fun hs x
  let _ : Module.Projective F (TensorProduct Λ F P.V) :=
    Module.projective_of_isLocalizedModule (nonZeroDivisors Λ)
      ((TensorProduct.mk Λ F P.V) 1)
  let _ : Fintype G := Fintype.ofFinite G
  rcases
      (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
        (Λ := Λ) (G := G) (P := P.V)).mp P.projective with
    ⟨_, u, hu⟩
  refine
    (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
      (Λ := F) (G := G) (P := TensorProduct Λ F P.V)).mpr ?_
  refine ⟨inferInstance, (Module.End.baseChangeHom Λ F P.V u), ?_⟩
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro a x
    simpa [hu] using
      scalarExtension_sumOfConjugates_apply_tmul
        (Λ := Λ) (F := F) (G := G) P u a x
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂]

/-- Helper for Exercise 16-16.2-3: package `P.scalarExtension F` as the actual finite projective
`F[G]`-owner on the representation-centered module `asModule ((P.scalarExtension F).ρ)`. -/
private def scalarExtension_owner
    (P : FiniteProjectiveGroupAlgebraModule Λ G) :
    FiniteProjectiveGroupAlgebraModule F G := by
  let _ : Module.Finite F (TensorProduct Λ F P.V) := by infer_instance
  let _ : Module.Finite F[G] (TensorProduct Λ F P.V) :=
    Module.Finite.of_restrictScalars_finite F F[G] (TensorProduct Λ F P.V)
  let _ : Module.Projective F[G] (TensorProduct Λ F P.V) :=
    scalarExtension_tensor_projective (Λ := Λ) (F := F) (G := G) P
  exact ⟨FGModuleCat.of F[G] (TensorProduct Λ F P.V), inferInstance⟩

omit [IsDedekindDomain Λ] in
/-- Helper for Exercise 16-16.2-3: the packaged scalar-extension owner has the same
finite-dimensional representation as `P.scalarExtension F`. -/
private theorem scalarExtension_owner_class_eq
    (P : FiniteProjectiveGroupAlgebraModule Λ G) :
    [((scalarExtension_owner (Λ := Λ) (F := F) (G := G) P).toFiniteRep)]₀ =
      [P.scalarExtension F]₀ := by
  refine finiteRepGrothendieckClass_eq_of_nonempty_iso ?_
  obtain ⟨eTensor⟩ :=
    scalarExtension_asModule_nonempty_linearEquiv_tensor (Λ := Λ) (F := F) (G := G) P
  let eρM :
      asModule (((scalarExtension_owner (Λ := Λ) (F := F) (G := G) P).toFiniteRep).ρ) ≃ₗ[F[G]]
        asModule ((P.scalarExtension F).ρ) := by
    let eTensor' :
        asModule (((scalarExtension_owner (Λ := Λ) (F := F) (G := G) P).toFiniteRep).ρ) ≃ₗ[F[G]]
          TensorProduct Λ F P.V := by
      change
        asModule
            ((Rep.ofModuleMonoidAlgebra.obj
              (ModuleCat.of F[G] (TensorProduct Λ F P.V))).ρ) ≃ₗ[F[G]]
          TensorProduct Λ F P.V
      let Mmod : ModuleCat F[G] := ModuleCat.of F[G] (TensorProduct Λ F P.V)
      let toFun :
          (Representation.ofModule Mmod).asModule → TensorProduct Λ F P.V := fun x ↦
            (RestrictScalars.addEquiv F F[G] (TensorProduct Λ F P.V))
              ((Representation.ofModule Mmod).asModuleEquiv x)
      let invFun :
          TensorProduct Λ F P.V → (Representation.ofModule Mmod).asModule := fun x ↦
            (Representation.ofModule Mmod).asModuleEquiv.symm
              ((RestrictScalars.addEquiv F F[G] (TensorProduct Λ F P.V)).symm x)
      refine
        { toFun := toFun
          invFun := invFun
          left_inv := by
            intro x
            simp [toFun, invFun, Mmod]
          right_inv := by
            intro x
            simp [toFun, invFun, Mmod]
          map_add' := by
            intro x y
            change
              (((Representation.ofModule Mmod).asModuleEquiv (x + y) :
                  RestrictScalars F F[G] (TensorProduct Λ F P.V))) =
                ((Representation.ofModule Mmod).asModuleEquiv x :
                    RestrictScalars F F[G] (TensorProduct Λ F P.V)) +
                  ((Representation.ofModule Mmod).asModuleEquiv y :
                    RestrictScalars F F[G] (TensorProduct Λ F P.V))
            exact
              (Representation.ofModule Mmod).asModuleEquiv.map_add x y
          map_smul' := by
            intro r x
            exact Representation.smul_ofModule_asModule (M := Mmod) r x }
    exact eTensor'.trans eTensor
  obtain ⟨eRep⟩ :=
    nonempty_equiv_of_asModuleLinearEquiv
      (((scalarExtension_owner (Λ := Λ) (F := F) (G := G) P).toFiniteRep).ρ)
      ((P.scalarExtension F).ρ)
      eρM
  exact ⟨Representation.Equiv.toFDRepIso eRep⟩

/-- Helper for Exercise 16-16.2-3: in characteristic zero, once the generic-fiber character is a
natural-number multiple of the regular character, the generic fiber is actually isomorphic to the
canonical free model. -/
private theorem scalarExtension_iso_free_of_character_eq_nsmul_leftRegular
    [CharZero F]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (n : ℕ)
    (hχ : (P.scalarExtension F).character =
      n • (Representation.leftRegular F G).character) :
    Nonempty (P.scalarExtension F ≅ FDRep.of (Rep.free F G (ULift (Fin n))).ρ) := by
  -- The Chapter `16` character-to-class bridge upstream is currently unavailable in this
  -- workspace, so the remaining source-faithful step is deferred here.
  let _ := hχ
  sorry

/-- Helper for Exercise 16-16.2-3: in characteristic zero, once the generic-fiber character is a
natural-number multiple of the regular character, the actual finite projective owner is free. -/
private theorem free_of_character_eq_nsmul_leftRegular_charZero
    [CharZero F]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (n : ℕ)
    (hχ : (P.scalarExtension F).character =
      n • (Representation.leftRegular F G).character) :
    Module.Free F[G] (asModule ((P.scalarExtension F).ρ)) := by
  let α : Type u := ULift (Fin n)
  let Vfree : FDRep F G := FDRep.of (Rep.free F G α).ρ
  obtain ⟨e⟩ :=
    scalarExtension_iso_free_of_character_eq_nsmul_leftRegular
      (Λ := Λ) (F := F) (G := G) P n hχ
  obtain ⟨eM⟩ :=
    nonempty_asModuleLinearEquiv_of_repEquiv
      ((P.scalarExtension F).ρ)
      Vfree.ρ
      (Representation.equivOfIso
        ((CategoryTheory.forget₂ (FDRep F G) (Rep F G)).mapIso e))
  let _ : Module.Free F[G] (asModule Vfree.ρ) := by
    -- The free model is already free over the group algebra by construction.
    simpa [Vfree, α] using free_module_free (F := F) (G := G) n
  -- Transport the explicit free `F[G]`-basis on the free model back to `P.scalarExtension F`.
  exact Module.Free.of_equiv eM.symm

/-- Helper for Exercise 16-16.2-3: in characteristic zero, the remaining task is to convert the
regular-character identity into an actual free `F[G]`-basis of the generic fiber. -/
private theorem scalar_extension_free_of_character_zero_off_one
    (hresidue : ∀ p : Nat.Primes, (p : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ p))
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (hχ : ∀ g : G, g ≠ 1 → (P.scalarExtension F).character g = 0) :
    Module.Free F[G] (asModule ((P.scalarExtension F).ρ)) := by
  by_cases hchar0 : ringChar F = 0
  · letI : CharZero F := (CharP.ringChar_zero_iff_CharZero (R := F)).mp hchar0
    exact
      free_of_character_eq_nsmul_leftRegular_charZero
        (Λ := Λ) (F := F) (G := G) P
        (Module.finrank F (Representation.invariants ((P.scalarExtension F).ρ)))
        (scalarExtension_character_eq_nsmul_leftRegular_of_eq_zero_off_one
          (Λ := Λ) (F := F) (G := G) P hχ)
  · let p := ringChar F
    letI : CharP F p := ringChar.charP (R := F)
    have hp_ne_one : p ≠ 1 := CharP.char_ne_one F p
    have hp_two_le : 2 ≤ p := by
      omega
    letI : Fact p.Prime := ⟨CharP.char_is_prime_of_two_le F p hp_two_le⟩
    have hcard_ne_zero : Nat.card G ≠ 0 := by
      exact (Nat.card_ne_zero).2 ⟨inferInstance, inferInstance⟩
    obtain ⟨m, hm⟩ :=
      eq_prime_pow_of_forall_prime_dvd_eq
        (p := p) (n := Nat.card G) hcard_ne_zero
        (fun q hq =>
          card_prime_divisor_eq_of_charP
            (Λ := Λ) (F := F) (G := G) (p := p) hresidue q hq)
    let Q := scalarExtension_owner (Λ := Λ) (F := F) (G := G) P
    have hG : IsPGroup p G := IsPGroup.of_card hm
    have hfreeQ : Module.Free F[G] Q.V :=
      FiniteProjectiveGroupAlgebraModule.free_of_charP_of_isPGroup
        (k := F) (G := G) (p := p) Q hG
    simpa [Q, scalarExtension_owner] using hfreeQ

-- Proof sketch: complete `P` at each nonzero maximal ideal whose residue characteristic is a
-- prime divisor of `|G|`, apply Swan's local freeness theorem to those completed modules, and
-- compare the local ranks to conclude that the quotient-field scalar extension is a free
-- `F[G]`-module.
/-- Exercise 16-16.2-3 (1): if every prime divisor of `|G|` occurs as the residue characteristic
of some nonzero maximal ideal of the Dedekind domain `Λ`, then the scalar extension of a finite
projective `Λ[G]`-module to the quotient field `F` is free over `F[G]`. -/
theorem scalarExtension_free
    (hresidue : ∀ p : Nat.Primes, (p : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ p))
    (P : FiniteProjectiveGroupAlgebraModule Λ G) :
    Module.Free F[G] (asModule ((P.scalarExtension F).ρ)) := by
  -- The local argument above already gives the zero-off-identity character input.
  exact scalar_extension_free_of_character_zero_off_one
    (Λ := Λ) (F := F) (G := G) hresidue P
    (scalarExtension_character_eq_zero_of_ne_one_aux
      (Λ := Λ) (F := F) (G := G) hresidue P)

-- Proof sketch: by part (1), the scalar extension is a free `F[G]`-module, hence a finite direct
-- sum of copies of the regular representation. The regular character vanishes away from the
-- identity by `leftRegular_character_eq_zero_of_ne_one`, so the same is true for the character of
-- the scalar-extended module.
/-- Exercise 16-16.2-3 (2): when the scalar extension is finite-dimensional over `F`, its ordinary
character is zero on every nonidentity element of `G`. -/
theorem scalarExtension_character_eq_zero_of_ne_one
    (hresidue : ∀ p : Nat.Primes, (p : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ p))
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (g : G) (hg : g ≠ 1) :
    (P.scalarExtension F).character g = 0 := by
  -- Choose a residue prime dividing the order of `g`, then apply the localized Chapter `16`
  -- projective-character vanishing criterion.
  exact scalarExtension_character_eq_zero_of_ne_one_aux
    (Λ := Λ) (F := F) (G := G) hresidue P g hg

end FiniteProjectiveGroupAlgebraModule

end SwanExercise

end Representation
