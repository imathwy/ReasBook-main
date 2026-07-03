import Mathlib
import Serre.Chap11.Proposition_11_11_4_1.Index
import Serre.Chap14.Exercise_14_14_4_5
import Serre.Chap16.Corollary_16_16_1_7
import Serre.Chap16.Exercise_16_16_1_12
import Serre.Chap02.Exercise_2_2_4_5
import Serre.Chap02.Proposition_2_2_4_1
import Serre.Chap06.Proposition_6_6_2_1

noncomputable section

universe u

open scoped MonoidAlgebra Representation

namespace Representation

section SwanExercise

namespace FiniteProjectiveGroupAlgebraModule

variable (Λ : Type u) [CommRing Λ]
variable (F : Type u) [Field F] [Algebra Λ F]
variable (G : Type u) [Group G]
variable [IsDedekindDomain Λ] [IsFractionRing Λ F] [Finite G]

/-- Helper for Exercise 16-16.2-3: extending scalars from `Λ` to a field `K` turns a finite
projective `Λ[G]`-module into a finite-dimensional `K[G]`-representation. -/
abbrev scalarExtension
    {Λ : Type u} [CommRing Λ]
    {G : Type u} [Group G] [Finite G]
    (K : Type u) [Field K] [Algebra Λ K]
    (P : FiniteProjectiveGroupAlgebraModule Λ G) : FDRep K G :=
  let _ : Module.Finite Λ P.V := P.finite
  let _ : Module.Finite K (TensorProduct Λ K P.toRep) := by infer_instance
  FDRep.of (Representation.scalarExtension P.toRep.ρ)

/-- Helper for Exercise 16-16.2-3: a `Rep` isomorphism yields an equivalence of the underlying
unbundled representations. -/
abbrev repIsoToEquiv
    {A B : Rep F G} (e : A ≅ B) : A.ρ.Equiv B.ρ :=
  Representation.equivOfIso e

/-- Helper for Exercise 16-16.2-3: the canonical free `F[G]`-representation on `n` generators has
character equal to `n` copies of the regular character. -/
theorem free_character_eq_nsmul_leftRegular
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
              simpa using congrFun
                (Representation.char_tensor
                  ((Rep.leftRegular F G).ρ) ((Rep.trivial F G (α →₀ F)).ρ)) (1 : G)
        _ = (Nat.card G : F) * (n : F) := by
              letI : Fintype G := Fintype.ofFinite G
              have hfinrankG : Module.finrank F (G →₀ F) = Nat.card G := by
                simpa [Nat.card_eq_fintype_card] using
                  (show Module.finrank F (G →₀ F) = Fintype.card G from
                    Module.finrank_finsupp_self F)
              have hcardα : Fintype.card α = n := by
                simp [α]
              simp [Representation.character, Representation.trivial, hfinrankG, hcardα]
    calc
      (FDRep.of (Rep.free F G α).ρ).character (1 : G) =
          (Rep.free F G α).ρ.character (1 : G) := rfl
      _ = (Nat.card G : F) * (n : F) := hchar_one
      _ = (Nat.card G : F) * (n : F) := by
            rfl
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
theorem free_module_free
    (n : ℕ) :
    let α : Type u := ULift (Fin n)
    Module.Free F[G] (asModule ((FDRep.of (Rep.free F G α).ρ).ρ)) := by
  let α : Type u := ULift (Fin n)
  -- `Representation.free` is designed so its `asModule` is a free group-algebra module.
  simpa [α] using (Representation.free_asModule_free F G α)

/-- Helper for Exercise 16-16.2-3: an `A[G]`-linear equivalence between the owner-module views of
two representations produces an equivariant representation equivalence. -/
theorem nonempty_equiv_of_asModuleLinearEquiv
    {A : Type u} [CommRing A]
    {G : Type u} [Group G]
    {V W : Type u} [AddCommGroup V] [Module A V]
    [AddCommGroup W] [Module A W]
    (ρ : Representation A G V) (σ : Representation A G W)
    (e : asModule ρ ≃ₗ[A[G]] asModule σ) :
    Nonempty (ρ.Equiv σ) := by
  refine ⟨Representation.Equiv.mk ?_ ?_⟩
  refine
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
  intro g
  ext x
  -- Rewrite the group action as multiplication by the basis element `of g` on both module views.
  change
    σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g x))) =
      σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm x)))
  rw [ρ.asModuleEquiv_symm_map_rho, e.map_smul, σ.asModuleEquiv_map_smul]
  simp [Representation.asAlgebraHom, MonoidAlgebra.of]

/-- Helper for Exercise 16-16.2-3: base change carries the averaged conjugation operator on a
projective `Λ[G]`-module to the scalar-extended tensor module over `F`. -/
theorem scalarExtension_sumOfConjugates_apply_tmul
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
      simpa [Module.End.baseChangeHom] using
        (LinearMap.baseChange_tmul (f := u) (A := F) a
          (MonoidAlgebra.single g (1 : Λ) • x))]
  rw [show MonoidAlgebra.single g⁻¹ (1 : F) •
      (a ⊗ₜ[Λ] u (MonoidAlgebra.single g (1 : Λ) • x)) =
      MonoidAlgebra.of F G g⁻¹ •
        (a ⊗ₜ[Λ] u (MonoidAlgebra.single g (1 : Λ) • x)) by rfl]
  simpa using
    monoidAlgebra_of_smul_tmul
      (Λ := Λ) (P := P.V) (κ := F) g⁻¹ a
      (u (MonoidAlgebra.single g (1 : Λ) • x))

/-- Helper for Exercise 16-16.2-3: localizing the actual owner `P` at a residue prime produces
the finite projective `Λ_𝔭[G]`-module that Swan's source proof applies Theorem `36` to. -/
theorem localized_tensor_is_finite_projective
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
def localized_tensor_owner
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
noncomputable def localized_tensor_owner_linearEquiv
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
noncomputable def localized_tensor_scalarExtension_carrier_equiv
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

/-- Helper for Exercise 16-16.2-3: the explicit tensor-cancellation carrier equivalence sends a
pure tensor to the expected canceled tensor. -/
theorem localized_tensor_scalarExtension_carrier_apply_tmul
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
  simpa using
    (TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul
      Λ (Localization.AtPrime (M.1.asIdeal)) F F a b x)

/-- Helper for Exercise 16-16.2-3: the localized tensor owner acts on pure tensors by leaving the
coefficient in the localized ring untouched and applying the original `G`-action to the module
factor. -/
theorem localized_tensor_owner_apply_tmul
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

/-- Helper for Exercise 16-16.2-3: scalar extension of a representation acts on pure tensors by
keeping the scalar in the new coefficient field and applying the original action to the module
factor. -/
theorem scalarExtension_apply_tmul
    {A : Type u} [CommRing A] [Algebra A F]
    {V : Type u} [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (g : G) (a : F) (x : V) :
    (Representation.scalarExtension ρ) g (a ⊗ₜ[A] x) = a ⊗ₜ[A] (ρ g x) := by
  -- `Representation.scalarExtension` is defined by `Module.End.baseChangeHom`, so pure tensors
  -- are computed by `LinearMap.baseChange_tmul`.
  change ((Module.End.baseChangeHom A F V) (ρ g)) (a ⊗ₜ[A] x) = a ⊗ₜ[A] (ρ g x)
  exact LinearMap.baseChange_tmul (f := ρ g) (A := F) a x

/-- Helper for Exercise 16-16.2-3: the exact tensor-cancellation owner equivalence between the
localized generic fiber and the original quotient-field scalar extension. -/
theorem localized_tensor_scalarExtension_intertwining_on_nested_tmul
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

/-- Helper for Exercise 16-16.2-3: the tensor-cancellation carrier comparison intertwines the
localized scalar-extension action with the original quotient-field action on every nested tensor. -/
theorem localized_tensor_scalarExtension_intertwining_on_nested_tensors
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

/-- Helper for Exercise 16-16.2-3: the exact tensor-cancellation owner equivalence between the
localized generic fiber and the original quotient-field scalar extension. -/
theorem localized_tensor_scalarExtension_carrier_isIntertwining
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
  -- Route correction: prove the equality pointwise on the literal nested tensor carrier, then
  -- package that pointwise comparison as the desired linear-map identity.
  intro g
  apply LinearMap.ext
  intro z
  simpa [LinearMap.comp_apply] using
    localized_tensor_scalarExtension_intertwining_on_nested_tensors
      (Λ := Λ) (F := F) (G := G) (p := p) P M g z

/-- Helper for Exercise 16-16.2-3: the exact tensor-cancellation owner equivalence between the
localized generic fiber and the original quotient-field scalar extension. -/
noncomputable def localized_tensor_scalarExtension_owner_equiv
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

/-- Helper for Exercise 16-16.2-3: the character of the localized generic fiber agrees with the
character of the original quotient-field scalar extension. -/
theorem localized_tensor_scalarExtension_character_eq
    {p : ℕ} [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F]
    (g : G) :
    ((localized_tensor_owner (Λ := Λ) (G := G) P M).scalarExtension F).character g =
      (P.scalarExtension F).character g := by
  -- Transport the character across the explicit owner-level tensor-cancellation equivalence.
  simpa using congrFun
    (Representation.char_iso
      (localized_tensor_scalarExtension_owner_equiv
        (Λ := Λ) (F := F) (G := G) (p := p) P M)) g

end FiniteProjectiveGroupAlgebraModule

end SwanExercise

end Representation
