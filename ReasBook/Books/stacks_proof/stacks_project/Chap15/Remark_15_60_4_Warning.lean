import StacksProject_2024.Chap15.Lemma_15_60_1
import StacksProject_2024.Chap15.Lemma_15_92_16
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.PrincipalIdeal
import StacksProject_2024.Chap10.Lemma_10_109_4
import StacksProject_2024.Chap10.Lemma_10_109_9
import StacksProject_2024.Chap15.Lemma_15_60_2
import StacksProject_2024.Chap15.Lemma_15_75_3
import StacksProject_2024.Chap15.Lemma_15_75_4
import StacksProject_2024.Chap15.Lemma_15_75_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open MvPolynomial
open Opposite
open Polynomial
open scoped DerivedTensorChangeOfRings DerivedTensorProduct DerivedTensorWithAlgebra

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

namespace Remark15604Warning

section

variable (k : Type*) [CommRing k]

local notation "Rxy" => MvPolynomial (Fin 2) k

/-- The quotient ring `A = k[x, y] / (xy)` from Remark `15.60.4`. -/
abbrev Ring : Type _ :=
  Rxy ⧸ principalIdeal ((X (0 : Fin 2) : Rxy) * (X (1 : Fin 2) : Rxy))

local notation "A" => Ring k
local notation "DModA" => DerivedCategory (ModuleCat A)
private abbrev single₀ : ModuleCat A ⥤ DModA := ModuleCat.single0Functor

/-- The class of `x` in the quotient ring `A = k[x, y] / (xy)`. -/
abbrev x : Ring k :=
  Ideal.Quotient.mk _ (X (0 : Fin 2) : Rxy)

/-- Helper for Remark 15.60.4 (Warning): the class of `y` in the quotient ring
`A = k[x, y] / (xy)`. -/
abbrev y : Ring k :=
  Ideal.Quotient.mk _ (X (1 : Fin 2) : Rxy)

/-- The object `N = A / (x)` viewed in `D(A)`. -/
abbrev N : DModA :=
  Functor.obj (single₀ k) (ModuleCat.of A (A ⧸ principalIdeal (x k)))

/-- The object `N' = A` viewed in `D(A)`. -/
abbrev NPrime : DModA :=
  Functor.obj (single₀ k) (ModuleCat.of A A)

end

end Remark15604Warning

section

variable (k : Type*) [CommRing k]

local notation "R" => MvPolynomial (Fin 2) k
local notation "A" => Remark15604Warning.Ring k
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "x" => Remark15604Warning.x k
local notation "y" => Remark15604Warning.y k
local notation "N" => Remark15604Warning.N k
local notation "N'" => Remark15604Warning.NPrime k
local notation "singleCpx₀" => CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)

/-- Helper for Remark 15.60.4 (Warning): multiplication by `x` on the regular `A`-module, viewed
as a degree-zero cochain map. -/
private abbrev multiplicationByXMap :
    ModuleCat.of A A ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (LinearMap.mulRight A x)

/-- Helper for Remark 15.60.4 (Warning): multiplication by `xy` on the regular `A`-module,
viewed as a degree-zero cochain map. -/
private abbrev multiplicationByXYMap :
    ModuleCat.of A A ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (LinearMap.mulRight A (x * y))

/-- Helper for Remark 15.60.4 (Warning): multiplication by `xy` on the regular `A`-module
vanishes because the relation `xy = 0` already holds in `A`. -/
private theorem multiplicationByXYMap_eq_zero :
    multiplicationByXYMap (k := k) = 0 := by
  -- The quotient relation `xy = 0` turns the right-multiplication endomorphism into the zero map.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  simp [multiplicationByXYMap, LinearMap.mulRight_apply,
    Remark15604Warning.x_mul_y_eq_zero (k := k)]

/-- Helper for Remark 15.60.4 (Warning): after applying the degree-zero single functor, the
regular-module `xy` endomorphism is still zero. -/
private theorem single_multiplicationByXYMap_eq_zero :
    (singleCpx₀).map (multiplicationByXYMap (k := k)) =
      (0 :
        (singleCpx₀).obj (ModuleCat.of A A) ⟶
          (singleCpx₀).obj (ModuleCat.of A A)) := by
  -- The single functor preserves the zero morphism, so the previous module-level vanishing
  -- immediately upgrades to the cochain map used in the mapping-cone model.
  simp [multiplicationByXYMap_eq_zero (k := k)]

/-- Helper for Remark 15.60.4 (Warning): the explicit two-term cochain model
`A \xrightarrow{x} A` in degrees `-1` and `0`. -/
private abbrev stage0KoszulModel :
    CochainComplex (ModuleCat A) ℤ :=
  CochainComplex.mappingCone ((singleCpx₀).map (multiplicationByXMap (k := k)))

/-- Helper for Remark 15.60.4 (Warning): scalar extension sends the regular `R`-module to the
regular `A`-module. -/
private noncomputable def extendScalars_regular_iso :
    ((ModuleCat.extendScalars (algebraMap R A)).obj (ModuleCat.of R R)) ≅
      ModuleCat.of A A := by
  -- Rewrite exact scalar extension on the regular module as the ordinary tensor product `A ⊗[R] R`
  -- and collapse the right regular factor by the tensor-unit isomorphism.
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.rid R A).toModuleIso

/-- Helper for Remark 15.60.4 (Warning): tensoring the regular `A`-module with an `A`-module on
the right collapses to that module. -/
private noncomputable def regular_leftTensor_module_iso
    (M : Type*) [AddCommGroup M] [Module A M] :
    ModuleCat.of A (A ⊗[A] M) ≅ ModuleCat.of A M := by
  -- The left tensor factor is the regular module, so `A ⊗[A] M ≃ M`.
  simpa using (TensorProduct.lid A M).toModuleIso

/-- Helper for Remark 15.60.4 (Warning): the degree-zero regular `A`-module is the tensor unit in
`D(A)`. -/
private noncomputable def regular_single0_tensorUnit_iso :
    ModuleCat.single0Functor.obj (ModuleCat.of A A) ≅ 𝟙_ DModA :=
  ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
    (ModuleCat.of A A)) ≪≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat A)).app
      ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj
        (ModuleCat.of A A))).symm

/-- Helper for Remark 15.60.4 (Warning): tensoring with the degree-zero regular `A`-module is the
identity on `D(A)`. -/
private noncomputable def tensor_regular_single0_iso
    (K : DModA) :
    K ⊗[A]^L (ModuleCat.single0Functor.obj (ModuleCat.of A A)) ≅ K :=
  -- Compare the source-facing derived tensor product with the owner tensor, identify `A[0]` with
  -- the tensor unit, and then apply the right unitor.
  (derivedCategory_tensorObj_iso_derivedTensorProduct
      K (ModuleCat.single0Functor.obj (ModuleCat.of A A))).symm ≪≫
    whiskerLeftIso K (regular_single0_tensorUnit_iso (k := k)) ≪≫
      ρ_ K

/-- Helper for Remark 15.60.4 (Warning): after scalar extension, multiplication by `X₀` becomes
multiplication by the class `x` on the regular `A`-module. -/
private theorem extendScalars_mul_X0_transport :
    (ModuleCat.extendScalars (algebraMap R A)).map
        (ModuleCat.ofHom (LinearMap.mulRight R (X (0 : Fin 2) : R))) =
      (extendScalars_regular_iso (k := k)).hom ≫
        multiplicationByXMap (k := k) ≫
          (extendScalars_regular_iso (k := k)).inv := by
  -- Compare the two `A`-linear maps on pure tensors `a ⊗ r`; both send them to
  -- `a * algebraMap R A (r * X₀)`.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [ModuleCat.ExtendScalars.map']
  · intro a r
    simp [extendScalars_regular_iso, multiplicationByXMap, ModuleCat.ExtendScalars.map',
      LinearMap.baseChange_tmul, LinearMap.mulRight_apply, Remark15604Warning.x,
      TensorProduct.rid_tmul, mul_assoc]
  · intro z w hz hw
    simp [hz, hw]

/-- Helper for Remark 15.60.4 (Warning): after scalar extension, multiplication by `X₀X₁`
becomes multiplication by the class `xy` on the regular `A`-module. -/
private theorem extendScalars_mul_XY_transport :
    (ModuleCat.extendScalars (algebraMap R A)).map
        (ModuleCat.ofHom
          (LinearMap.mulRight R ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))) =
      (extendScalars_regular_iso (k := k)).hom ≫
        multiplicationByXYMap (k := k) ≫
          (extendScalars_regular_iso (k := k)).inv := by
  -- Compare the two `A`-linear maps on pure tensors; both multiply by the image of `X₀X₁`.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [ModuleCat.ExtendScalars.map']
  · intro a r
    simp [extendScalars_regular_iso, multiplicationByXYMap, ModuleCat.ExtendScalars.map',
      LinearMap.baseChange_tmul, LinearMap.mulRight_apply, Remark15604Warning.x,
      Remark15604Warning.y, TensorProduct.rid_tmul, mul_assoc]
  · intro z w hz hw
    simp [hz, hw]

/-- Helper for Remark 15.60.4 (Warning): scalar extension carries the degree-zero single complex
on the regular `R`-module to the degree-zero single complex on the regular `A`-module. -/
private noncomputable def extendScalars_single_regular_iso :
    (((ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((singleCpx₀R).obj (ModuleCat.of R R))) ≅
      (singleCpx₀).obj (ModuleCat.of A A) :=
  ((Functor.mapCochainComplexSingleFunctor
      (ModuleCat.extendScalars (algebraMap R A)) (0 : ℤ)).app
      (ModuleCat.of R R)) ≪≫
    Functor.mapIso singleCpx₀ (extendScalars_regular_iso (k := k))

/-- Helper for Remark 15.60.4 (Warning): positive cochain degrees of the extended homotopy cofiber
vanish, so the remaining cone-bridge work only has to compare degrees `0` and `-1`. -/
private theorem extend_homotopyCofiber_isZero_pos
    {C : ChainComplex (ModuleCat A) ℕ} (φ : C ⟶ C) (m : ℕ) :
    CategoryTheory.Limits.IsZero
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
        (HomologicalComplex.homotopyCofiber φ)).X (m + 1 : ℤ)) := by
  -- Positive integers are not in the image of `n ↦ -n`, so extension by zero kills these terms.
  change CategoryTheory.Limits.IsZero (((HomologicalComplex.homotopyCofiber φ).extend
      ComplexShape.embeddingDownNat).X (m + 1 : ℤ))
  apply (HomologicalComplex.homotopyCofiber φ).isZero_extend_X
    ComplexShape.embeddingDownNat (m + 1 : ℤ)
  intro i hi
  dsimp [ComplexShape.embeddingDownNat] at hi
  omega

/-- Helper for Remark 15.60.4 (Warning): if the extension of `C` is concentrated in degree `0`,
then every negative degree `-(m + 1)` of the extended cochain complex vanishes. -/
private theorem singleton_extend_isZero_neg_succ
    {C : ChainComplex (ModuleCat A) ℕ} {M : ModuleCat A}
    (e :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj C) ≅
        (singleCpx₀).obj M)
    (m : ℕ) :
    CategoryTheory.Limits.IsZero
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj C).X
        (-((m + 1 : ℕ) : ℤ))) := by
  -- Transport the vanishing from the degree-zero single complex along the chosen comparison `e`.
  have hsingle :
      CategoryTheory.Limits.IsZero (((singleCpx₀).obj M).X (-((m + 1 : ℕ) : ℤ))) := by
    apply (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) (0 : ℤ) M (-((m + 1 : ℕ) : ℤ)))
    omega
  exact hsingle.of_iso (e.app _)

/-- Helper for Remark 15.60.4 (Warning): under a degree-zero single-complex identification, every
positive chain degree of `C` vanishes. -/
private theorem singleton_chain_isZero_succ
    {C : ChainComplex (ModuleCat A) ℕ} {M : ModuleCat A}
    (e :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj C) ≅
        (singleCpx₀).obj M)
    (m : ℕ) :
    CategoryTheory.Limits.IsZero (C.X (m + 1)) := by
  -- Degree `m + 1` of the chain complex becomes cochain degree `-(m + 1)` after extension.
  simpa using singleton_extend_isZero_neg_succ (e := e) m

/-- Helper for Remark 15.60.4 (Warning): once `C` is concentrated in degree `0`, the extended
homotopy cofiber has no terms below degree `-1`. -/
private theorem singleton_homotopyCofiber_isZero_neg_two_succ
    {C : ChainComplex (ModuleCat A) ℕ} {M : ModuleCat A}
    (φ : C ⟶ C)
    (e :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj C) ≅
        (singleCpx₀).obj M)
    (m : ℕ) :
    CategoryTheory.Limits.IsZero
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
        (HomologicalComplex.homotopyCofiber φ)).X (-((m + 2 : ℕ) : ℤ))) := by
  -- The degree `m + 2` cone term is a biproduct of the `m + 1` and `m + 2` terms of `C`,
  -- and both of those vanish because `e` identifies the extension of `C` with `M[0]`.
  change CategoryTheory.Limits.IsZero ((HomologicalComplex.homotopyCofiber φ).X (m + 2))
  refine HomologicalComplex.homotopyCofiber.isZero_X _ _ ?_ (fun j hj ↦ ?_)
  · exact singleton_chain_isZero_succ (e := e) (m := m + 1)
  · obtain rfl := (ComplexShape.down ℕ).next_eq' hj
    exact singleton_chain_isZero_succ (e := e) m

/-- Helper for Remark 15.60.4 (Warning): the literal mapping cone of a degree-zero single-complex
self-map is supported only in degrees `0` and `-1`. -/
private theorem single_map_mappingCone_isZero_outside
    {M : ModuleCat A} (g : M ⟶ M) {i : ℤ} (hi0 : i ≠ 0) (hiNegOne : i ≠ -1) :
    CategoryTheory.Limits.IsZero ((CochainComplex.mappingCone ((singleCpx₀).map g)).X i) := by
  -- Rewrite the cone term as the biproduct of the two neighboring single-complex terms, both of
  -- which are zero away from the window `{0, -1}`.
  have hleft :
      CategoryTheory.Limits.IsZero (((singleCpx₀).obj M).X (i + 1)) := by
    apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M (i + 1))
    intro hi
    apply hiNegOne
    linarith
  have hright :
      CategoryTheory.Limits.IsZero (((singleCpx₀).obj M).X i) := by
    apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M i)
    exact hi0
  exact (CochainComplex.mappingCone.isZero_X_iff (φ := (singleCpx₀).map g) i).2 ⟨hleft, hright⟩

/-- Helper for Remark 15.60.4 (Warning): if the left summand is zero, then the projection
`X ⊞ Y ⟶ Y` is an isomorphism in `ModuleCat A`. -/
private theorem biprod_snd_isIso_of_isZero_left
    {X Y : ModuleCat A} [HasBinaryBiproduct X Y] (hX : CategoryTheory.Limits.IsZero X) :
    IsIso (Limits.biprod.snd : X ⊞ Y ⟶ Y) := by
  letI : CategoryTheory.Limits.IsZero X := hX
  have hfst_zero : (Limits.biprod.fst : X ⊞ Y ⟶ X) = 0 := by
    exact hX.eq_of_tgt _ _
  -- Use `biprod.inr` as the inverse and collapse the vanished left summand.
  refine ⟨⟨Limits.biprod.inr, ?_, ?_⟩⟩
  · -- Compare both endomorphisms of the biproduct through their two projections.
    apply Limits.biprod.hom_ext
    · simpa [Category.assoc, hfst_zero]
    · simp [Category.assoc]
  · simp

/-- Helper for Remark 15.60.4 (Warning): if the right summand is zero, then the projection
`X ⊞ Y ⟶ X` is an isomorphism in `ModuleCat A`. -/
private theorem biprod_fst_isIso_of_isZero_right
    {X Y : ModuleCat A} [HasBinaryBiproduct X Y] (hY : CategoryTheory.Limits.IsZero Y) :
    IsIso (Limits.biprod.fst : X ⊞ Y ⟶ X) := by
  letI : CategoryTheory.Limits.IsZero Y := hY
  have hsnd_zero : (Limits.biprod.snd : X ⊞ Y ⟶ Y) = 0 := by
    exact hY.eq_of_tgt _ _
  -- Use `biprod.inl` as the inverse and collapse the vanished right summand.
  refine ⟨⟨Limits.biprod.inl, ?_, ?_⟩⟩
  · -- Compare both endomorphisms of the biproduct through their two projections.
    apply Limits.biprod.hom_ext
    · simp [Category.assoc]
    · simpa [Category.assoc, hsnd_zero]
  · simp

/-- Helper for Remark 15.60.4 (Warning): degree `0` of the literal mapping cone on `M[0]`
identifies with the degree-`0` term of `M[0]`. -/
private noncomputable theorem single_map_mappingCone_component_zero_iso
    {M : ModuleCat A} (g : M ⟶ M) :
    ((CochainComplex.mappingCone ((singleCpx₀).map g)).X 0) ≅
      (((singleCpx₀).obj M).X 0) := by
  have hleft :
      CategoryTheory.Limits.IsZero (((singleCpx₀).obj M).X 1) := by
    -- The degree-`1` term of a degree-zero single complex vanishes.
    apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M 1)
    omega
  letI :
      IsIso ((CochainComplex.mappingCone.snd ((singleCpx₀).map g)).v 0 0 (add_zero 0)) := by
    -- In degree `0`, the cone term is `((singleCpx₀).obj M).X 1 ⊞ ((singleCpx₀).obj M).X 0`,
    -- so the projection to the second summand is invertible because the first summand is zero.
    simpa using biprod_snd_isIso_of_isZero_left (X := ((singleCpx₀).obj M).X 1)
      (Y := ((singleCpx₀).obj M).X 0) hleft
  -- Package the invertible degreewise projection as an object isomorphism.
  exact asIso ((CochainComplex.mappingCone.snd ((singleCpx₀).map g)).v 0 0 (add_zero 0))

/-- Helper for Remark 15.60.4 (Warning): degree `-1` of the literal mapping cone on `M[0]`
identifies with the degree-`0` term of `M[0]`. -/
private noncomputable theorem single_map_mappingCone_component_neg_one_iso
    {M : ModuleCat A} (g : M ⟶ M) :
    ((CochainComplex.mappingCone ((singleCpx₀).map g)).X (-1)) ≅
      (((singleCpx₀).obj M).X 0) := by
  have hright :
      CategoryTheory.Limits.IsZero (((singleCpx₀).obj M).X (-1)) := by
    -- The degree-`-1` term of a degree-zero single complex vanishes.
    apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M (-1))
    omega
  letI :
      IsIso ((CochainComplex.mappingCone.fst ((singleCpx₀).map g)).1.v (-1) 0 rfl) := by
    -- In degree `-1`, the cone term is `((singleCpx₀).obj M).X 0 ⊞ ((singleCpx₀).obj M).X (-1)`,
    -- so the projection to the first summand is invertible because the second summand is zero.
    simpa using biprod_fst_isIso_of_isZero_right (X := ((singleCpx₀).obj M).X 0)
      (Y := ((singleCpx₀).obj M).X (-1)) hright
  -- Package the invertible degreewise projection as an object isomorphism.
  exact asIso ((CochainComplex.mappingCone.fst ((singleCpx₀).map g)).1.v (-1) 0 rfl)

/-- Helper for Remark 15.60.4 (Warning): once the extension of `C` is concentrated in degree `0`,
the extended homotopy cofiber is supported only in cochain degrees `0` and `-1`. -/
private theorem singleton_homotopyCofiber_isZero_outside
    {C : ChainComplex (ModuleCat A) ℕ} {M : ModuleCat A}
    (φ : C ⟶ C)
    (e :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj C) ≅
        (singleCpx₀).obj M)
    {i : ℤ} (hi0 : i ≠ 0) (hiNegOne : i ≠ -1) :
    CategoryTheory.Limits.IsZero
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
        (HomologicalComplex.homotopyCofiber φ)).X i) := by
  -- Split by the integer shape: positive degrees are killed by extension, degree `-1` is the only
  -- surviving negative degree, and everything further left vanishes by the two-term cone support.
  cases i using Int with
  | ofNat n =>
      cases n with
      | zero =>
          contradiction
      | succ m =>
          simpa using extend_homotopyCofiber_isZero_pos (φ := φ) m
  | negSucc n =>
      cases n with
      | zero =>
          contradiction
      | succ m =>
          simpa using singleton_homotopyCofiber_isZero_neg_two_succ
            (φ := φ) (e := e) m

/-- Helper for Remark 15.60.4 (Warning): degree `0` of the extended homotopy cofiber identifies
with the degree-`0` term of the transported single complex. -/
private noncomputable theorem singleton_homotopyCofiber_component_zero_iso
    {C : ChainComplex (ModuleCat A) ℕ} {M : ModuleCat A}
    (φ : C ⟶ C)
    (e :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj C) ≅
        (singleCpx₀).obj M) :
    (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
      (HomologicalComplex.homotopyCofiber φ)).X 0) ≅
      (((singleCpx₀).obj M).X 0) := by
  letI : IsIso (HomologicalComplex.homotopyCofiber.sndX φ 0) := by
    -- In chain degree `0`, the homotopy cofiber has no shifted summand, so `sndX` is the
    -- canonical identity comparison with `C.X 0`.
    simpa [HomologicalComplex.homotopyCofiber.sndX, ComplexShape.down]
  -- Transport degree `0` first back to the nat-indexed chain complex, then across `e`.
  exact
    ((HomologicalComplex.homotopyCofiber φ).extendXIso
        ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl) ≪≫
      asIso (HomologicalComplex.homotopyCofiber.sndX φ 0) ≪≫
        (C.extendXIso ComplexShape.embeddingDownNat
          (i := 0) (i' := 0) rfl).symm ≪≫
          asIso (e.hom.f 0)

/-- Helper for Remark 15.60.4 (Warning): degree `-1` of the extended homotopy cofiber identifies
with the degree-`0` term of the transported single complex. -/
private noncomputable theorem singleton_homotopyCofiber_component_neg_one_iso
    {C : ChainComplex (ModuleCat A) ℕ} {M : ModuleCat A}
    (φ : C ⟶ C)
    (e :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj C) ≅
        (singleCpx₀).obj M) :
    (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
      (HomologicalComplex.homotopyCofiber φ)).X (-1)) ≅
      (((singleCpx₀).obj M).X 0) := by
  have hright : CategoryTheory.Limits.IsZero (C.X 1) := by
    -- Degree `1` of `C` vanishes because `e` identifies the extension of `C` with `M[0]`.
    simpa using singleton_chain_isZero_succ (e := e) (m := 0)
  letI : IsIso (Limits.biprod.fst : C.X 0 ⊞ C.X 1 ⟶ C.X 0) := by
    -- In chain degree `1`, the shifted summand `C.X 1` is zero, so projection to `C.X 0`
    -- identifies the cone term with the surviving left summand.
    simpa using biprod_fst_isIso_of_isZero_right (X := C.X 0) (Y := C.X 1) hright
  -- Rewrite cochain degree `-1` as chain degree `1`, collapse the zero right summand, and then
  -- transport the surviving `C.X 0` term through `e`.
  exact
    ((HomologicalComplex.homotopyCofiber φ).extendXIso
        ComplexShape.embeddingDownNat (i := 1) (i' := -1) rfl) ≪≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod φ 1 0 (by simp [ComplexShape.down])) ≪≫
        asIso (Limits.biprod.fst : C.X 0 ⊞ C.X 1 ⟶ C.X 0) ≪≫
          (C.extendXIso ComplexShape.embeddingDownNat
            (i := 0) (i' := 0) rfl).symm ≪≫
            asIso (e.hom.f 0)

/-- Helper for Remark 15.60.4 (Warning): if an extended chain complex is identified with the
degree-zero single complex on `M` and the transported endomorphism is conjugate to the
corresponding single-complex map, then the extended homotopy cofiber should identify with the
literal mapping cone of that map. -/
private theorem singleton_homotopyCofiber_conjugate_single_map_iso_mappingCone
    {C : ChainComplex (ModuleCat A) ℕ} {M : ModuleCat A}
    (φ : C ⟶ C) (g : M ⟶ M)
    (e :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj C) ≅
        (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M)
    (hconj :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map φ) =
        e.hom ≫
          (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).map g ≫
            e.inv) :
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
      (HomologicalComplex.homotopyCofiber φ)) ≅
        CochainComplex.mappingCone
          ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).map g) := by
  -- Route correction: the generic singleton-cone bridge is already available in the dedicated
  -- helper file, so we now reuse that owner theorem instead of reproving the same transport-heavy
  -- `-1 → 0` differential comparison locally.
  exact
    CategoryTheory.extend_homotopyCofiber_conjugate_single_map_iso_mappingCone
      (φ := φ) (g := g) (e := e) (hconj := hconj)

/-- Helper for Remark 15.60.4 (Warning): every positive exterior power of the zero free module
`Fin 0 → A` is the zero object. -/
private theorem stage0_isZero_exteriorPower_empty (i : ℕ) (hi : 1 ≤ i) :
    CategoryTheory.Limits.IsZero ((ModuleCat.of A (Fin 0 → A)).exteriorPower i) := by
  -- Positive exterior powers of the empty free module are generated only by the zero tensor.
  rw [ModuleCat.isZero_iff_subsingleton]
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi) with ⟨j, rfl⟩
  have hbot :
      (⋀[A]^(j + 1) (Fin 0 → A) : Submodule A (ExteriorAlgebra A (Fin 0 → A))) = ⊥ := by
    calc
      (⋀[A]^(j + 1) (Fin 0 → A) : Submodule A (ExteriorAlgebra A (Fin 0 → A))) =
          Submodule.span A (Set.range (ExteriorAlgebra.ιMulti A (j + 1) :
            (Fin (j + 1) → Fin 0 → A) → ExteriorAlgebra A (Fin 0 → A))) := by
        symm
        exact exteriorPower.ιMulti_span_fixedDegree (R := A) (n := j + 1) (M := Fin 0 → A)
      _ = ⊥ := by
        apply le_antisymm
        · rw [Submodule.span_le]
          rintro _ ⟨g, rfl⟩
          have hg : g = 0 := funext fun k ↦ Subsingleton.elim _ _
          rw [hg]
          simpa using (ExteriorAlgebra.ιMulti A (j + 1)).map_zero
        · exact bot_le
  refine ⟨fun x y ↦ ?_⟩
  have hx : x = 0 := by
    simpa [hbot] using x.2
  have hy : y = 0 := by
    simpa [hbot] using y.2
  exact hx.trans hy.symm

/-- Helper for Remark 15.60.4 (Warning): after transporting the first empty-family Koszul
differential through `⋀¹(0) ≃ 0` and `⋀⁰(0) ≃ A`, it becomes the zero linear form on
`Fin 0 → A`. -/
private theorem stage0_empty_family_first_differential_linearMap_eq_linearForm :
    (exteriorPower.zeroEquiv A (Fin 0 → A)).toLinearMap.comp
        (koszulDifferentialLinearMap
          (koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ x))) 0) =
      (koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ x))).comp
        (exteriorPower.oneEquiv A (Fin 0 → A)).toLinearMap := by
  -- Normalize the first differential on generators before identifying the empty-family stage with
  -- the degree-zero single complex on `A`.
  apply exteriorPower.linearMap_ext
  ext m
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply]
  have hone :
      (exteriorPower.oneEquiv A (Fin 0 → A)) (exteriorPower.ιMulti A 1 m) = m 0 := by
    simpa using (exteriorPower.oneEquiv_ιMulti (R := A) (M := Fin 0 → A) (f := m))
  have hone' :
      (koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ x)))
          ((exteriorPower.oneEquiv A (Fin 0 → A)) (exteriorPower.ιMulti A 1 m)) =
        (koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ x))) (m 0) := by
    simp [hone]
  have hone'' :
      (koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ x)))
          ((exteriorPower.oneEquiv A (Fin 0 → A)).toLinearMap
            (exteriorPower.ιMulti A 1 m)) =
        (koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ x))) (m 0) := by
    simpa using hone'
  rw [hone'']
  apply_fun (exteriorPower.zeroEquiv A (Fin 0 → A)).symm using
    (exteriorPower.zeroEquiv A (Fin 0 → A)).symm.injective
  simp [exteriorPower.zeroEquiv_symm_apply]
  apply Subtype.ext
  simpa [ExteriorAlgebra.ιMulti, Algebra.algebraMap_eq_smul_one, koszulDifferentialLinearMap] using
    (CliffordAlgebra.contractLeft_ι
      (Q := 0) (d := koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ x))) (x := m 0))

/-- Helper for Remark 15.60.4 (Warning): the first empty-family Koszul differential vanishes after
transporting degree `0` through `⋀⁰(0) ≃ A`. -/
private theorem stage0_empty_family_first_differential_comp_iso0_eq_zero :
    (K^•(Fin.init (fun _ : Fin 1 ↦ x))).d 1 0 ≫
      (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom = 0 := by
  -- Once the first differential is rewritten as the empty-family linear form, it is zero because
  -- every vector in `Fin 0 → A` is the zero vector.
  change
    ModuleCat.ofHom
      (((exteriorPower.zeroEquiv A (Fin 0 → A)).toLinearMap.comp
        (koszulDifferentialLinearMap
          (koszulLinearForm (Fin.init (fun _ : Fin 1 ↦ x))) 0))) = 0
  change ModuleCat.ofHom _ = ModuleCat.ofHom 0
  congr 1
  rw [stage0_empty_family_first_differential_linearMap_eq_linearForm (k := k)]
  ext z
  have hz : z = 0 := funext fun i ↦ funext fun j ↦ Fin.elim0 j
  simp [hz, koszulLinearForm]

/-- Helper for Remark 15.60.4 (Warning): the empty-family `Fin 0` Koszul stage is already the
degree-zero single chain complex on `A`. -/
private noncomputable abbrev stage0_empty_family_koszul_single_iso :
    K^•(Fin.init (fun _ : Fin 1 ↦ x)) ≅
      (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A A) := by
  let hom :
      K^•(Fin.init (fun _ : Fin 1 ↦ x)) ⟶
        (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A A) :=
    (ChainComplex.toSingle₀Equiv
        (K^•(Fin.init (fun _ : Fin 1 ↦ x)))
        (ModuleCat.of A A)).symm
      ⟨(ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom,
        stage0_empty_family_first_differential_comp_iso0_eq_zero (k := k)⟩
  let inv :
      (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A A) ⟶
        K^•(Fin.init (fun _ : Fin 1 ↦ x)) :=
    (ChainComplex.fromSingle₀Equiv
        (K^•(Fin.init (fun _ : Fin 1 ↦ x)))
        (ModuleCat.of A A)).symm
      ((ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv)
  refine CategoryTheory.Iso.mk hom inv ?_ ?_
  · -- Compare the endomorphism of the empty-family Koszul stage degreewise.
    apply HomologicalComplex.hom_ext
    intro i
    cases i with
    | zero =>
        have hhom0 :
            hom.f 0 = (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom := by
          simpa [hom] using
            (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
              (C := K^•(Fin.init (fun _ : Fin 1 ↦ x)))
              (X := ModuleCat.of A A)
              (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom)
              (hf := stage0_empty_family_first_differential_comp_iso0_eq_zero (k := k)))
        have hinv0 :
            inv.f 0 = (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv := by
          simpa [inv] using
            (ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
              (C := K^•(Fin.init (fun _ : Fin 1 ↦ x)))
              (X := ModuleCat.of A A)
              (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv))
        simpa [HomologicalComplex.comp_f, hhom0, hinv0] using
          (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom_inv_id
    | succ m =>
        -- Every positive degree of the empty-family stage is already zero.
        exact
          (stage0_isZero_exteriorPower_empty (k := k) (m + 1)
            (Nat.succ_le_succ (Nat.zero_le m))).eq_of_src _ _
  · -- Maps out of a degree-zero single chain complex are determined by their degree-zero component.
    apply HomologicalComplex.from_single_hom_ext
    have hhom0 :
        hom.f 0 = (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom := by
      simpa [hom] using
        (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
          (C := K^•(Fin.init (fun _ : Fin 1 ↦ x)))
          (X := ModuleCat.of A A)
          (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom)
          (hf := stage0_empty_family_first_differential_comp_iso0_eq_zero (k := k)))
    have hinv0 :
        inv.f 0 = (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv := by
      simpa [inv] using
        (ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
          (C := K^•(Fin.init (fun _ : Fin 1 ↦ x)))
          (X := ModuleCat.of A A)
          (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv))
    simpa [HomologicalComplex.comp_f, hhom0, hinv0] using
      (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv_hom_id

/-- Helper for Remark 15.60.4 (Warning): the degree-zero identification `⋀⁰(0) ≃ A` transports
scalar multiplication on `⋀⁰(0)` to right multiplication on `A`. -/
private theorem stage0_empty_exteriorPower_iso0_conjugates_mulRight (r : A) :
    (r • 𝟙 ((ModuleCat.of A (Fin 0 → A)).exteriorPower 0)) =
      (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom ≫
        ModuleCat.ofHom (LinearMap.mulRight A r) ≫
          (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv := by
  -- Apply `⋀⁰(0) ≃ A`; after this transport both sides are the same multiplication map on `A`.
  ext z
  have hhom_injective :
      Function.Injective
        ((ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom.hom) := by
    intro y₁ y₂ hy
    have hy' := congrArg
      (fun t ↦ (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv.hom t) hy
    simpa using hy'
  apply_fun ((ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom.hom) using
    hhom_injective
  simp [mul_comm]

/-- Helper for Remark 15.60.4 (Warning): on the nat-indexed empty-family Koszul stage, scalar
multiplication by `x` is conjugate to the degree-zero single-complex map induced by multiplication
on `A`. -/
private theorem stage0_empty_family_koszul_single_iso_conjugates_scalar :
    (x • 𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ x)))) =
      (stage0_empty_family_koszul_single_iso (k := k)).hom ≫
        (ChainComplex.single₀ (ModuleCat A)).map (multiplicationByXMap (k := k)) ≫
          (stage0_empty_family_koszul_single_iso (k := k)).inv := by
  -- Compare both chain maps degreewise. Degree `0` is the transported scalar action from the
  -- previous helper, and every positive degree vanishes because the empty-family stage is zero.
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      have hs :
          ((x • 𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ x)))).f 0) =
            ModuleCat.ofHom
              (x •
                (LinearMap.id :
                  ((ModuleCat.of A (Fin 0 → A)).exteriorPower 0) →ₗ[A]
                    ((ModuleCat.of A (Fin 0 → A)).exteriorPower 0))) := by
        rfl
      have hhom0 :
          (stage0_empty_family_koszul_single_iso (k := k)).hom.f 0 =
            (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom := by
        simpa [stage0_empty_family_koszul_single_iso] using
          (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
            (C := K^•(Fin.init (fun _ : Fin 1 ↦ x)))
            (X := ModuleCat.of A A)
            (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).hom)
            (hf := stage0_empty_family_first_differential_comp_iso0_eq_zero (k := k)))
      have hinv0 :
          (stage0_empty_family_koszul_single_iso (k := k)).inv.f 0 =
            (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv := by
        simpa [stage0_empty_family_koszul_single_iso] using
          (ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
            (C := K^•(Fin.init (fun _ : Fin 1 ↦ x)))
            (X := ModuleCat.of A A)
            (f := (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin 0 → A))).inv))
      have hsingle0 :
          ((ChainComplex.single₀ (ModuleCat A)).map (multiplicationByXMap (k := k))).f 0 =
            multiplicationByXMap (k := k) := by
        simpa using
          (HomologicalComplex.single_map_f_self
            (V := ModuleCat A) (c := ComplexShape.down ℕ) (j := (0 : ℕ))
            (f := multiplicationByXMap (k := k)))
      rw [hs]
      rw [show
          ((stage0_empty_family_koszul_single_iso (k := k)).hom ≫
            (ChainComplex.single₀ (ModuleCat A)).map (multiplicationByXMap (k := k)) ≫
            (stage0_empty_family_koszul_single_iso (k := k)).inv).f 0 =
            (stage0_empty_family_koszul_single_iso (k := k)).hom.f 0 ≫
              multiplicationByXMap (k := k) ≫
              (stage0_empty_family_koszul_single_iso (k := k)).inv.f 0 by
            simp [HomologicalComplex.comp_f, hsingle0]]
      rw [hhom0, hinv0]
      simpa [multiplicationByXMap] using
        stage0_empty_exteriorPower_iso0_conjugates_mulRight (k := k) (r := x)
  | succ m =>
      -- Positive degrees of the empty-family stage are zero, so there is only one map out of
      -- them on either side.
      exact
        (stage0_isZero_exteriorPower_empty (k := k) (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m))).eq_of_src _ _

/-- Helper for Remark 15.60.4 (Warning): extending the empty-family `Fin 0` Koszul stage to `ℤ`
gives the canonical degree-zero single complex on `A`. -/
private abbrev stage0_empty_family_koszul_extended_single_iso :
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
      (K^•(Fin.init (fun _ : Fin 1 ↦ x)))) ≅
    (singleCpx₀).obj (ModuleCat.of A A) :=
  -- First normalize the empty-family stage on the nat-indexed chain complex, then extend that
  -- normalization to `ℤ` via the canonical `extendSingleIso`.
  ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).mapIso
      (stage0_empty_family_koszul_single_iso (k := k))) ≪≫
    (HomologicalComplex.extendSingleIso
      ComplexShape.embeddingDownNat (ModuleCat.of A A) (0 : ℕ) (0 : ℤ) rfl)

/-- Helper for Remark 15.60.4 (Warning): extending a degree-zero single-complex map from `ℕ` to
`ℤ` commutes with the canonical `extendSingleIso` identification. -/
private theorem stage0_extend_single0_map_transport {M N : ModuleCat A} (g : M ⟶ N) :
    HomologicalComplex.extendMap ((ChainComplex.single₀ (ModuleCat A)).map g)
        ComplexShape.embeddingDownNat ≫
      (HomologicalComplex.extendSingleIso
        ComplexShape.embeddingDownNat N (0 : ℕ) (0 : ℤ) rfl).hom =
    (HomologicalComplex.extendSingleIso
      ComplexShape.embeddingDownNat M (0 : ℕ) (0 : ℤ) rfl).hom ≫
      (singleCpx₀).map g := by
  -- Rewrite the target as the explicit `up ℤ` single-complex map, then compare degreewise.
  change HomologicalComplex.extendMap ((ChainComplex.single₀ (ModuleCat A)).map g)
      ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso
      ComplexShape.embeddingDownNat N (0 : ℕ) (0 : ℤ) rfl).hom =
      (HomologicalComplex.extendSingleIso
        ComplexShape.embeddingDownNat M (0 : ℕ) (0 : ℤ) rfl).hom ≫
        (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) (0 : ℤ)).map g
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst hi
    simp [HomologicalComplex.comp_f,
      HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := 0) (i' := 0)
        (by simp),
      HomologicalComplex.extendSingleIso_hom_f (e := ComplexShape.embeddingDownNat)
        (X := N) (i := 0) (i' := 0) (h := rfl),
      HomologicalComplex.extendSingleIso_hom_f (e := ComplexShape.embeddingDownNat)
        (X := M) (i := 0) (i' := 0) (h := rfl),
      HomologicalComplex.single_map_f_self, Category.assoc]
  · by_cases hpre : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = i
    · obtain ⟨j, rfl⟩ := hpre
      cases j with
      | zero =>
          contradiction
      | succ j =>
          -- Away from degree `0`, the target single complex is zero.
          exact
            (HomologicalComplex.isZero_single_obj_X
              (ComplexShape.up ℤ) (0 : ℤ) N (-((Nat.succ j : ℕ) : ℤ)) (by omega)).eq_of_tgt _ _
    · -- If `i` is not in the image of the embedding, the extended source term is also zero.
      exact (((ChainComplex.single₀ (ModuleCat A)).obj M).isZero_extend_X
        ComplexShape.embeddingDownNat i (fun j hij ↦ hpre ⟨j, hij⟩)).eq_of_src _ _

/-- Helper for Remark 15.60.4 (Warning): on `embeddingDownNat`, the extension functor map is
definitionally the owner-level `extendMap`. -/
private theorem stage0_embeddingDownNat_extendFunctor_map_eq_extendMap
    {C D : ChainComplex (ModuleCat A) ℕ} (φ : C ⟶ D) :
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map φ) =
      HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat :=
  rfl

/-- Helper for Remark 15.60.4 (Warning): after transporting the extended empty-family scalar
endomorphism through the canonical `Fin 0`-to-`singleCpx₀` identification, one gets the explicit
degree-zero single-complex map induced by multiplication by `x`. -/
private theorem stage0_empty_family_koszul_extended_single_iso_conjugates_scalar :
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map
        (x • 𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ x))))) =
      (stage0_empty_family_koszul_extended_single_iso (k := k)).hom ≫
        (singleCpx₀).map (multiplicationByXMap (k := k)) ≫
          (stage0_empty_family_koszul_extended_single_iso (k := k)).inv := by
  -- The nat-indexed conjugation is already proved, and the remaining issue is purely transport
  -- across `extendMap` and `extendSingleIso`.
  let e₀ := stage0_empty_family_koszul_single_iso (k := k)
  let e₁ :=
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).mapIso e₀)
  let e₂ :=
    HomologicalComplex.extendSingleIso
      ComplexShape.embeddingDownNat (ModuleCat.of A A) (0 : ℕ) (0 : ℤ) rfl
  have hnat :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map
          (x • 𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ x))))) =
        e₁.hom ≫
          HomologicalComplex.extendMap
            ((ChainComplex.single₀ (ModuleCat A)).map
              (multiplicationByXMap (k := k)))
            ComplexShape.embeddingDownNat ≫
              e₁.inv := by
    simpa [e₁, Functor.map_comp, HomologicalComplex.extendMap_comp,
      stage0_embeddingDownNat_extendFunctor_map_eq_extendMap (k := k)] using
      congrArg
        (fun t ↦ HomologicalComplex.extendMap t ComplexShape.embeddingDownNat)
        (stage0_empty_family_koszul_single_iso_conjugates_scalar (k := k))
  have htransport :
      HomologicalComplex.extendMap
          ((ChainComplex.single₀ (ModuleCat A)).map
            (multiplicationByXMap (k := k)))
          ComplexShape.embeddingDownNat =
        e₂.hom ≫
          (singleCpx₀).map (multiplicationByXMap (k := k)) ≫
            e₂.inv := by
    calc
      HomologicalComplex.extendMap
          ((ChainComplex.single₀ (ModuleCat A)).map
            (multiplicationByXMap (k := k)))
          ComplexShape.embeddingDownNat =
        HomologicalComplex.extendMap
            ((ChainComplex.single₀ (ModuleCat A)).map
              (multiplicationByXMap (k := k)))
            ComplexShape.embeddingDownNat ≫
          (e₂.hom ≫ e₂.inv) := by simp
      _ =
        ((HomologicalComplex.extendMap
              ((ChainComplex.single₀ (ModuleCat A)).map
                (multiplicationByXMap (k := k)))
              ComplexShape.embeddingDownNat ≫
            e₂.hom) ≫
          e₂.inv) := by
            simp [Category.assoc]
      _ =
        (e₂.hom ≫ (singleCpx₀).map (multiplicationByXMap (k := k))) ≫
          e₂.inv := by
            simpa [e₂] using
              congrArg
                (fun t ↦ t ≫ e₂.inv)
                (stage0_extend_single0_map_transport
                  (k := k) (g := multiplicationByXMap (k := k)))
      _ =
        e₂.hom ≫
          (singleCpx₀).map (multiplicationByXMap (k := k)) ≫
            e₂.inv := by simp [Category.assoc]
  have hcombined :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map
          (x • 𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ x))))) =
        e₁.hom ≫
          e₂.hom ≫
            (singleCpx₀).map (multiplicationByXMap (k := k)) ≫
              e₂.inv ≫
                e₁.inv := by
    calc
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map
          (x • 𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ x))))) =
        e₁.hom ≫
          HomologicalComplex.extendMap
            ((ChainComplex.single₀ (ModuleCat A)).map
              (multiplicationByXMap (k := k)))
            ComplexShape.embeddingDownNat ≫
              e₁.inv := hnat
      _ =
        e₁.hom ≫
          (e₂.hom ≫
            (singleCpx₀).map (multiplicationByXMap (k := k)) ≫
              e₂.inv) ≫
            e₁.inv := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦ e₁.hom ≫ t ≫ e₁.inv)
                  htransport
      _ =
        e₁.hom ≫
          e₂.hom ≫
            (singleCpx₀).map (multiplicationByXMap (k := k)) ≫
              e₂.inv ≫
                e₁.inv := by simp [Category.assoc]
  simpa [stage0_empty_family_koszul_extended_single_iso, e₁, e₂, Category.assoc] using hcombined

/-- Helper for Remark 15.60.4 (Warning): the extended homotopy cofiber of multiplication by `x`
on the empty-family Koszul stage is the explicit two-term mapping cone `A \xrightarrow{x} A`. -/
private theorem stage0_singleton_homotopyCofiber_to_mappingCone_x :
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
      (HomologicalComplex.homotopyCofiber
        (x • 𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ x)))))) ≅
      stage0KoszulModel (k := k) := by
  -- Instantiate the generic singleton-cone bridge with the empty-family stage and the transported
  -- scalar endomorphism `A[0] --x--> A[0]`.
  exact
    singleton_homotopyCofiber_conjugate_single_map_iso_mappingCone
      (φ := x • 𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ x))))
      (g := multiplicationByXMap (k := k))
      (e := stage0_empty_family_koszul_extended_single_iso (k := k))
      (hconj := stage0_empty_family_koszul_extended_single_iso_conjugates_scalar (k := k))

/- Domain-style sampling for Remark 15.60.4:
- primary domain: change-of-rings derived tensor products in derived categories of modules over a
  quotient of a polynomial ring, together with the chapter's one-variable powered-Koszul stage
  owner for the two-term complex `A ⟶ A`;
- sampled owner declarations of the same kind:
  `ModuleCat.single0Functor`,
  `principalIdeal`,
  `derivedTensorChangeOfRings`,
  `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`;
- best owner abstraction: `derivedTensorChangeOfRings` owns the two change-of-rings tensor
  objects, `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory` owns the derived
  restriction-of-scalars operation, `ModuleCat.single0Functor` owns the degree-zero derived
  objects, `principalIdeal` owns the one-generator ideals `(xy)` and `(x)`, while the
  source-facing objects of the warning itself are the public abbreviations
  `Remark15604Warning.Ring k`, `Remark15604Warning.x k`, `Remark15604Warning.N k`, and
  `Remark15604Warning.NPrime k`; the canonical stage
  `(derivedCompletionKoszulPowersDerivedInverseSystem (fun _ : Fin 1 ↦ x)).obj (Opposite.op 0)`
  from Lemma `15.92.16` represents the two-term complex `A \xrightarrow{x} A`;
- primitive data: the ring `A = k[x, y] / (xy)`, the element `x ∈ A`, and the degree-zero derived
  objects `N = (A / (x))[0]` and `N' = A[0]`;
- derived API: the canonical degree-zero owner `ModuleCat.single0Functor`, the derived
  restriction-of-scalars images of `N` and `N'`, the two change-of-rings tensor objects, the
  canonical Koszul model
  `(derivedCompletionKoszulPowersDerivedInverseSystem (fun _ : Fin 1 ↦ x)).obj (Opposite.op 0)`,
  the split model `N[1] ⊞ N`, and the comparison/non-isomorphism theorems.

Source/core/bridge triage:
- `source-facing`: the warning counterexample objects `N`, `N'`, their restriction-of-scalars
  images, their two change-of-rings tensor products, and the statement that the resulting objects
  of `D(A)` are not isomorphic;
- `core/canonical`: `derivedTensorChangeOfRings`,
  `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory`, the powered Koszul tower
  `K^•[n](f)`, and `derivedCompletionKoszulPowersDerivedInverseSystem`;
- `bridge/view`: the two comparison theorems identifying the source-facing tensors with the
  canonical two-term Koszul model and the split object. -/

-- Proof sketch: in the quotient by `(xy)`, the defining relation says exactly that the classes of
-- `x` and `y` multiply to zero.
/-- Helper for Remark 15.60.4 (Warning): the coordinate classes satisfy `x * y = 0` in
`A = k[x, y] / (xy)`. -/
theorem Remark15604Warning.x_mul_y_eq_zero : x * y = 0 := by
  -- Reduce to the quotient relation defining `A`.
  change
    Ideal.Quotient.mk
        (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))
        ((X (0 : Fin 2) : R) * X (1 : Fin 2)) =
      0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

-- Proof sketch: the quotient ring is commutative, so the symmetric relation follows from
-- `x * y = 0`.
/-- Helper for Remark 15.60.4 (Warning): the coordinate classes also satisfy `y * x = 0`. -/
theorem Remark15604Warning.y_mul_x_eq_zero : y * x = 0 := by
  -- Commute the factors and reuse the defining relation.
  simpa [mul_comm] using Remark15604Warning.x_mul_y_eq_zero (k := k)

local notation "singleCpx₀R" => CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)

/-- Helper for Remark 15.60.4 (Warning): multiplying a two-variable polynomial by the first
coordinate variable is injective. -/
private theorem mul_X0_injective :
    Function.Injective (fun p : R ↦ p * (X (0 : Fin 2) : R)) := by
  intro p q hpq
  ext d
  -- Read off the coefficient shifted by one copy of `X₀`.
  have hcoeff :=
    congrArg
      (fun z : R ↦ z.coeff (d + Finsupp.single (0 : Fin 2) 1))
      hpq
  simpa [zero_add] using
    (MvPolynomial.coeff_mul_X
      (m := d) (s := (0 : Fin 2)) (p := p)).trans <|
      hcoeff.trans <|
        (MvPolynomial.coeff_mul_X
          (m := d) (s := (0 : Fin 2)) (p := q)).symm

/-- Helper for Remark 15.60.4 (Warning): multiplying a two-variable polynomial by the second
coordinate variable is injective. -/
private theorem mul_X1_injective :
    Function.Injective (fun p : R ↦ p * (X (1 : Fin 2) : R)) := by
  intro p q hpq
  ext d
  -- Read off the coefficient shifted by one copy of `X₁`.
  have hcoeff :=
    congrArg
      (fun z : R ↦ z.coeff (d + Finsupp.single (1 : Fin 2) 1))
      hpq
  simpa [zero_add] using
    (MvPolynomial.coeff_mul_X
      (m := d) (s := (1 : Fin 2)) (p := p)).trans <|
      hcoeff.trans <|
        (MvPolynomial.coeff_mul_X
          (m := d) (s := (1 : Fin 2)) (p := q)).symm

/-- Helper for Remark 15.60.4 (Warning): multiplying a two-variable polynomial by `X₀ X₁` is
injective. -/
private theorem mul_X0_mul_X1_injective :
    Function.Injective
      (fun p : R ↦ p * ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))) := by
  intro p q hpq
  -- First cancel the rightmost `X₁`, then cancel the remaining `X₀`.
  have h₁' :
      (p * (X (0 : Fin 2) : R)) * (X (1 : Fin 2) : R) =
        (q * (X (0 : Fin 2) : R)) * (X (1 : Fin 2) : R) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hpq
  have h₁ :
      p * (X (0 : Fin 2) : R) = q * (X (0 : Fin 2) : R) := by
    exact (mul_X1_injective (k := k)) h₁'
  exact mul_X0_injective (k := k) h₁

/-- Helper for Remark 15.60.4 (Warning): the quotient map `R → R/(X₀)` kills multiplication by
`X₀`. -/
private theorem polynomialXMap_comp_coordinate_quotient_mk_eq_zero :
    ModuleCat.ofHom
        (LinearMap.mulRight R (X (0 : Fin 2) : R)) ≫
      ModuleCat.ofHom
        ((Ideal.Quotient.mkₐ R (principalIdeal (X (0 : Fin 2) : R))).toLinearMap) =
        0 := by
  -- The composite lands in the defining principal ideal.
  ext p
  change Ideal.Quotient.mk (principalIdeal (X (0 : Fin 2) : R))
      (p * X (0 : Fin 2)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rw [principalIdeal]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

/-- Helper for Remark 15.60.4 (Warning): the quotient map `R → R/(X₀X₁)` kills multiplication by
`X₀X₁`. -/
private theorem polynomialXYMap_comp_node_ring_quotient_mk_eq_zero :
    ModuleCat.ofHom
        (LinearMap.mulRight R ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))) ≫
      ModuleCat.ofHom
        ((Ideal.Quotient.mkₐ R
          (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))).toLinearMap) =
        0 := by
  -- The composite lands in the defining principal ideal.
  ext p
  change Ideal.Quotient.mk
      (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))
      (p * (X (0 : Fin 2) * X (1 : Fin 2))) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rw [principalIdeal]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

/-- Helper for Remark 15.60.4 (Warning): the coordinate quotient `A/(x)` is also the quotient of
`R = k[x,y]` by `(X₀)`. -/
private noncomputable def coordinateQuotientTargetAlgHom :
    R →ₐ[k] (A ⧸ principalIdeal x) :=
  (Ideal.Quotient.mkₐ A (principalIdeal x)).comp
    (Ideal.Quotient.mkₐ R
      (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))))

/-- Helper for Remark 15.60.4 (Warning): the quotient map from `R` onto `A/(x)` is surjective. -/
private theorem coordinateQuotientTargetAlgHom_surjective :
    Function.Surjective (coordinateQuotientTargetAlgHom (k := k)) := by
  intro q
  -- Lift first across `A → A/(x)`, then across `R → A`.
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective A (principalIdeal x) q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mkₐ_surjective R
    (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))) a
  exact ⟨r, rfl⟩

/-- Helper for Remark 15.60.4 (Warning): the kernel of the quotient map `R → A/(x)` is the
principal ideal `(X₀)`. -/
private theorem coordinateQuotientTargetAlgHom_ker_eq :
    RingHom.ker (coordinateQuotientTargetAlgHom (k := k)).toRingHom =
      principalIdeal (X (0 : Fin 2) : R) := by
  ext p
  constructor
  · intro hp
    change coordinateQuotientTargetAlgHom (k := k) p = 0 at hp
    change Ideal.Quotient.mk (principalIdeal x)
        (Ideal.Quotient.mk
          (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))) p) = 0 at hp
    rw [Ideal.Quotient.eq_zero_iff_mem] at hp
    rw [principalIdeal] at hp
    rcases Ideal.mem_span_singleton'.mp hp with ⟨a, ha⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mkₐ_surjective R
      (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))) a
    have hdiff :
        Ideal.Quotient.mk
            (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))
            (p - r * X (0 : Fin 2)) = 0 := by
      simpa [ha, Remark15604Warning.x, map_sub] using
        congrArg
          (fun z : A ⧸ principalIdeal x ↦
            z - Ideal.Quotient.mk (principalIdeal x)
              (Ideal.Quotient.mk
                (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))
                (r * X (0 : Fin 2))))
          ha
    rw [Ideal.Quotient.eq_zero_iff_mem] at hdiff
    have hxy_le_x :
        principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)) ≤
          principalIdeal (X (0 : Fin 2) : R) := by
      rw [principalIdeal, principalIdeal]
      refine Ideal.span_le.2 ?_
      intro z hz
      rcases hz with rfl
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    have hleft :
        p - r * X (0 : Fin 2) ∈ principalIdeal (X (0 : Fin 2) : R) :=
      hxy_le_x hdiff
    have hright :
        r * X (0 : Fin 2) ∈ principalIdeal (X (0 : Fin 2) : R) := by
      rw [principalIdeal]
      exact Ideal.mem_span_singleton'.2 ⟨r, by simp [mul_comm]⟩
    convert Ideal.add_mem (principalIdeal (X (0 : Fin 2) : R)) hleft hright using 1
    simpa using (sub_add_cancel p (r * X (0 : Fin 2))).symm
  · intro hp
    rw [principalIdeal] at hp
    rcases Ideal.mem_span_singleton'.mp hp with ⟨r, rfl⟩
    change Ideal.Quotient.mk (principalIdeal x)
        (Ideal.Quotient.mk
          (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))
          (r * X (0 : Fin 2))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [principalIdeal]
    exact Ideal.mem_span_singleton'.2 ⟨
      Ideal.Quotient.mk
        (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))) r,
      by simp [Remark15604Warning.x, mul_comm]⟩

/-- Helper for Remark 15.60.4 (Warning): quotienting `R = k[x,y]` by `(X₀)` identifies the
resulting ring with the coordinate quotient `A/(x)`. -/
private noncomputable def coordinateQuotientAlgEquiv :
    (R ⧸ principalIdeal (X (0 : Fin 2) : R)) ≃ₐ[k] (A ⧸ principalIdeal x) :=
  (Ideal.quotientEquivAlgOfEq k
      (coordinateQuotientTargetAlgHom_ker_eq (k := k)).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (coordinateQuotientTargetAlgHom_surjective (k := k)))

/-- Helper for Remark 15.60.4 (Warning): on module categories, the coordinate quotient `A/(x)`
is the same `R`-module as `R/(X₀)`. -/
private noncomputable def coordinateQuotientModuleIso :
    ModuleCat.of R (R ⧸ principalIdeal (X (0 : Fin 2) : R)) ≅
      ModuleCat.of R (A ⧸ principalIdeal x) :=
  (coordinateQuotientAlgEquiv (k := k)).toLinearEquiv.toModuleIso

/-- Helper for Remark 15.60.4 (Warning): derived restriction of scalars carries a degree-zero
`A`-module to the degree-zero complex on its underlying `R`-module. -/
private noncomputable def restrictScalars_single0_iso
    (M : ModuleCat A) :
    ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
      (ModuleCat.single0Functor.obj M)) ≅
      (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj M) :=
  -- Compute derived restriction on the explicit degree-zero cochain complex.
  (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M)) ≪≫
    (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.restrictScalars (algebraMap R A))
          (0 : ℤ)).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
      ((ModuleCat.restrictScalars (algebraMap R A)).obj M)).symm

/-- Helper for Remark 15.60.4 (Warning): the restriction of `N = A/(x)` to `R` is the degree-zero
single complex on `R/(X₀)`. -/
private noncomputable def restricted_coordinate_quotient_single_iso :
    ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ≅
      (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj
        (ModuleCat.of R (R ⧸ principalIdeal (X (0 : Fin 2) : R))) :=
  -- First forget the `A`-action, then rewrite the underlying module by the quotient isomorphism.
  restrictScalars_single0_iso (k := k)
      (ModuleCat.of A (A ⧸ principalIdeal x)) ≪≫
    (Functor.mapIso
      (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ))
      (coordinateQuotientModuleIso (k := k)).symm)

/-- Helper for Remark 15.60.4 (Warning): the restriction of `N' = A` to `R` is already the
degree-zero single complex on `R/(X₀X₁)`. -/
private noncomputable def restricted_node_ring_single_iso :
    ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') ≅
      (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj
        (ModuleCat.of R A) :=
  -- Forgetting scalars on the regular `A`-module changes only the ambient ring.
  restrictScalars_single0_iso (k := k) (ModuleCat.of A A)

/-- Helper for Remark 15.60.4 (Warning): the zero cochain gives the canonical map from the
two-term resolution cone to a degree-zero quotient complex. -/
private theorem resolution_desc_condition
    {Q : ModuleCat R}
    (f : ModuleCat.of R R ⟶ ModuleCat.of R R)
    (q : ModuleCat.of R R ⟶ Q)
    (hcomp : f ≫ q = 0) :
    δ (-1) 0
        (0 :
          Cochain
            ((singleCpx₀R).obj (ModuleCat.of R R))
            ((singleCpx₀R).obj Q)
            (-1)) =
      Cochain.ofHom (((singleCpx₀R).map f) ≫ (singleCpx₀R).map q) := by
  -- The `mappingCone.desc` compatibility is exactly the vanishing of the short-complex composite.
  rw [δ_zero]
  simp [hcomp]

/-- Helper for Remark 15.60.4 (Warning): package the standard map from the cone of a one-step
free resolution to the degree-zero quotient complex. -/
private abbrev resolutionToSingleComplexMap
    {Q : ModuleCat R}
    (f : ModuleCat.of R R ⟶ ModuleCat.of R R)
    (q : ModuleCat.of R R ⟶ Q)
    (hcomp : f ≫ q = 0) :
    CochainComplex.mappingCone ((singleCpx₀R).map f) ⟶
      (singleCpx₀R).obj Q :=
  CochainComplex.mappingCone.desc
    ((singleCpx₀R).map f)
    0
    ((singleCpx₀R).map q)
    (resolution_desc_condition (f := f) (q := q) hcomp)

/-- Helper for Remark 15.60.4 (Warning): the explicit cone-to-quotient map is the canonical
`mappingCone.descShortComplex` map attached to the underlying short complex. -/
private theorem resolutionToSingleComplexMap_eq_descShortComplex
    {Q : ModuleCat R}
    (f : ModuleCat.of R R ⟶ ModuleCat.of R R)
    (q : ModuleCat.of R R ⟶ Q)
    (hcomp : f ≫ q = 0) :
    resolutionToSingleComplexMap (f := f) (q := q) hcomp =
      CochainComplex.mappingCone.descShortComplex
        ((ShortComplex.mk f q hcomp).map singleCpx₀R) := by
  -- Both sides are the same `mappingCone.desc` presentation.
  rfl

/-- Helper for Remark 15.60.4 (Warning): the short exact sequence
`0 → R --X₀→ R → R/(X₀) → 0` is the source-faithful free resolution of `N_R`. -/
private theorem coordinate_quotient_shortExact :
    (ShortComplex.mk
        (ModuleCat.ofHom (LinearMap.mulRight R (X (0 : Fin 2) : R)))
        (ModuleCat.ofHom
          ((Ideal.Quotient.mkₐ R (principalIdeal (X (0 : Fin 2) : R))).toLinearMap))
        (polynomialXMap_comp_coordinate_quotient_mk_eq_zero (k := k))).ShortExact := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk
      (ModuleCat.ofHom (LinearMap.mulRight R (X (0 : Fin 2) : R)))
      (ModuleCat.ofHom
        ((Ideal.Quotient.mkₐ R (principalIdeal (X (0 : Fin 2) : R))).toLinearMap))
      (polynomialXMap_comp_coordinate_quotient_mk_eq_zero (k := k))
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- The image of multiplication by `X₀` is exactly the kernel of the quotient map.
    change S.Exact
    rw [S.moduleCat_exact_iff_range_eq_ker]
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      refine LinearMap.mem_ker.mpr ?_
      change Ideal.Quotient.mk (principalIdeal (X (0 : Fin 2) : R))
          (q * X (0 : Fin 2)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      rw [principalIdeal]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · intro hp
      change Ideal.Quotient.mk (principalIdeal (X (0 : Fin 2) : R)) p = 0 at hp
      rw [Ideal.Quotient.eq_zero_iff_mem] at hp
      rw [principalIdeal] at hp
      rcases Ideal.mem_span_singleton'.mp hp with ⟨q, hq⟩
      refine LinearMap.mem_range.mpr ⟨q, ?_⟩
      simpa [LinearMap.mulRight_apply, mul_comm] using hq
  · -- Injectivity is exactly the polynomial coefficient argument for multiplication by `X₀`.
    refine (ModuleCat.mono_iff_injective _).2 ?_
    simpa [LinearMap.mulRight_apply] using (mul_X0_injective (k := k))
  · -- Every quotient class has a representative polynomial.
    refine (ModuleCat.epi_iff_surjective _).2 ?_
    intro q
    refine Quotient.inductionOn' q ?_
    intro p
    exact ⟨p, rfl⟩

/-- Helper for Remark 15.60.4 (Warning): the short exact sequence
`0 → R --X₀X₁→ R → R/(X₀X₁) → 0` is the source-faithful free resolution of `N'_R`. -/
private theorem node_ring_shortExact :
    (ShortComplex.mk
        (ModuleCat.ofHom
          (LinearMap.mulRight R ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))))
        (ModuleCat.ofHom
          ((Ideal.Quotient.mkₐ R
            (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))).toLinearMap))
        (polynomialXYMap_comp_node_ring_quotient_mk_eq_zero (k := k))).ShortExact := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk
      (ModuleCat.ofHom
        (LinearMap.mulRight R ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))))
      (ModuleCat.ofHom
        ((Ideal.Quotient.mkₐ R
          (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))).toLinearMap))
      (polynomialXYMap_comp_node_ring_quotient_mk_eq_zero (k := k))
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- The image of multiplication by `X₀X₁` is exactly the kernel of the quotient map.
    change S.Exact
    rw [S.moduleCat_exact_iff_range_eq_ker]
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      refine LinearMap.mem_ker.mpr ?_
      change Ideal.Quotient.mk
          (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))
          (q * (X (0 : Fin 2) * X (1 : Fin 2))) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      rw [principalIdeal]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · intro hp
      change Ideal.Quotient.mk
          (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))
          p = 0 at hp
      rw [Ideal.Quotient.eq_zero_iff_mem] at hp
      rw [principalIdeal] at hp
      rcases Ideal.mem_span_singleton'.mp hp with ⟨q, hq⟩
      refine LinearMap.mem_range.mpr ⟨q, ?_⟩
      simpa [LinearMap.mulRight_apply, mul_comm, mul_left_comm, mul_assoc] using hq
  · -- Injectivity is the coefficient-shift argument applied twice, once for each variable.
    refine (ModuleCat.mono_iff_injective _).2 ?_
    simpa [LinearMap.mulRight_apply] using (mul_X0_mul_X1_injective (k := k))
  · -- Every class modulo `(X₀X₁)` has a representative polynomial.
    refine (ModuleCat.epi_iff_surjective _).2 ?_
    intro q
    refine Quotient.inductionOn' q ?_
    intro p
    exact ⟨p, rfl⟩

/-- Helper for Remark 15.60.4 (Warning): the free resolution `R --X₀→ R` gives a quasi-isomorphism
from its mapping cone to the degree-zero complex on `R/(X₀)`. -/
private theorem coordinate_quotient_resolution_quasiIso :
    QuasiIso
      (resolutionToSingleComplexMap
        (f := ModuleCat.ofHom (LinearMap.mulRight R (X (0 : Fin 2) : R)))
        (q := ModuleCat.ofHom
          ((Ideal.Quotient.mkₐ R (principalIdeal (X (0 : Fin 2) : R))).toLinearMap))
        (polynomialXMap_comp_coordinate_quotient_mk_eq_zero (k := k))) := by
  -- Transport the source-faithful short exact row to degree-zero cochain complexes.
  simpa [resolutionToSingleComplexMap_eq_descShortComplex] using
    CochainComplex.mappingCone.quasiIso_descShortComplex
      (coordinate_quotient_shortExact (k := k))

/-- Helper for Remark 15.60.4 (Warning): the free resolution `R --X₀X₁→ R` gives a
quasi-isomorphism from its mapping cone to the degree-zero complex on `R/(X₀X₁)`. -/
private theorem node_ring_resolution_quasiIso :
    QuasiIso
      (resolutionToSingleComplexMap
        (f := ModuleCat.ofHom
          (LinearMap.mulRight R ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))))
        (q := ModuleCat.ofHom
          ((Ideal.Quotient.mkₐ R
            (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))).toLinearMap))
        (polynomialXYMap_comp_node_ring_quotient_mk_eq_zero (k := k))) := by
  -- Transport the source-faithful short exact row to degree-zero cochain complexes.
  simpa [resolutionToSingleComplexMap_eq_descShortComplex] using
    CochainComplex.mappingCone.quasiIso_descShortComplex
      (node_ring_shortExact (k := k))

/-- Helper for Remark 15.60.4 (Warning): the restriction of `N = A/(x)` to `R` is represented by
the two-term free resolution `R \xrightarrow{X₀} R`. -/
private theorem restricted_coordinate_quotient_iso_x_resolution :
    IsIsomorphic
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N)
      (DerivedCategory.Q.obj
        (CochainComplex.mappingCone
          ((singleCpx₀R).map
            (ModuleCat.ofHom (LinearMap.mulRight R (X (0 : Fin 2) : R)))))) := by
  let π :=
    resolutionToSingleComplexMap
      (f := ModuleCat.ofHom (LinearMap.mulRight R (X (0 : Fin 2) : R)))
      (q := ModuleCat.ofHom
        ((Ideal.Quotient.mkₐ R (principalIdeal (X (0 : Fin 2) : R))).toLinearMap))
      (polynomialXMap_comp_coordinate_quotient_mk_eq_zero (k := k))
  letI : QuasiIso π := coordinate_quotient_resolution_quasiIso (k := k)
  let eResolution :
      DerivedCategory.Q.obj
          (CochainComplex.mappingCone
            ((singleCpx₀R).map
              (ModuleCat.ofHom (LinearMap.mulRight R (X (0 : Fin 2) : R))))) ≅
        (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj
          (ModuleCat.of R (R ⧸ principalIdeal (X (0 : Fin 2) : R))) :=
    asIso (DerivedCategory.Q.map π)
  -- Rewrite the derived restriction-of-scalars object through the explicit quotient module.
  refine ⟨(restricted_coordinate_quotient_single_iso (k := k)).symm ≪≫ eResolution.symm⟩

/-- Helper for Remark 15.60.4 (Warning): the restriction of `N' = A` to `R` is represented by the
two-term free resolution `R \xrightarrow{X₀X₁} R`. -/
private theorem restricted_node_ring_iso_xy_resolution :
    IsIsomorphic
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N')
      (DerivedCategory.Q.obj
        (CochainComplex.mappingCone
          ((singleCpx₀R).map
            (ModuleCat.ofHom
              (LinearMap.mulRight R
                ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))))))) := by
  let π :=
    resolutionToSingleComplexMap
      (f := ModuleCat.ofHom
        (LinearMap.mulRight R ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))))
      (q := ModuleCat.ofHom
        ((Ideal.Quotient.mkₐ R
          (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))).toLinearMap))
      (polynomialXYMap_comp_node_ring_quotient_mk_eq_zero (k := k))
  letI : QuasiIso π := node_ring_resolution_quasiIso (k := k)
  let eResolution :
      DerivedCategory.Q.obj
          (CochainComplex.mappingCone
            ((singleCpx₀R).map
              (ModuleCat.ofHom
                (LinearMap.mulRight R
                  ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))))) ≅
        (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj
          (ModuleCat.of R A) :=
    asIso (DerivedCategory.Q.map π)
  -- For `N' = A`, restriction of scalars changes only the ambient ring.
  refine ⟨(restricted_node_ring_single_iso (k := k)).symm ≪≫ eResolution.symm⟩

-- Proof sketch: in the warning example `N = A/(x)` and `N' = A`. The remark computes
-- `((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) \otimes_R^{\mathbf L}
-- N'` as the two-term complex `A \xrightarrow{x} A`, while
-- `((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') \otimes_R^{\mathbf L}
-- N` is computed as `N[1] ⊞ N`.
/-- The change-of-rings object
`((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗_R^{\mathbf L} N'`
is represented by the two-term complex `A \xrightarrow{x} A`, namely the canonical derived
powered-Koszul stage. -/
/-- Helper for Remark 15.60.4 (Warning): tensoring the two-term free resolution
`R \xrightarrow{X₀} R` with the regular `A`-module `A[0]` computes the explicit two-term
cochain model `A \xrightarrow{x} A`. -/
private theorem x_resolution_tensor_regular_module_iso_mappingCone_x :
    ((DerivedCategory.Q.obj
        (CochainComplex.mappingCone
          ((singleCpx₀R).map
            (ModuleCat.ofHom (LinearMap.mulRight R (X (0 : Fin 2) : R)))))) ⊗[R]^L[A] N') ≅
      DerivedCategory.Q.obj (stage0KoszulModel (k := k)) := by
  let E : CochainComplex (ModuleCat R) ℤ :=
    CochainComplex.mappingCone
      ((singleCpx₀R).map
        (ModuleCat.ofHom (LinearMap.mulRight R (X (0 : Fin 2) : R))))
  let Ext :
      CochainComplex (ModuleCat R) ℤ ⥤ CochainComplex (ModuleCat A) ℤ :=
    (ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)
  have hEFlat : E.IsTermwiseFlat := by
    -- The cone has only copies of the free module `R` in degrees `0` and `-1`.
    infer_instance
  have hELE : E.IsStrictlyLE 0 := by
    -- The literal two-term resolution is supported in cochain degrees `-1` and `0`.
    infer_instance
  let eBase :
      ((DerivedCategory.Q.obj E) ⊗[R]^L[A]) ≅
        DerivedCategory.Q.obj (Ext.obj E) :=
    CategoryTheory.derivedTensorWithAlgebra_obj_iso_of_termwiseFlat_of_isStrictlyLE
      (A := R) (B := A) (E := E) hEFlat hELE
  let eTensor :
      ((DerivedCategory.Q.obj E) ⊗[R]^L[A] N') ≅
        (DerivedCategory.Q.obj (Ext.obj E) ⊗[A]^L N') :=
    Functor.mapIso (derivedTensorProduct N') eBase
  let eUnit :
      (DerivedCategory.Q.obj (Ext.obj E) ⊗[A]^L N') ≅
        DerivedCategory.Q.obj (Ext.obj E) := by
    -- Collapse the right tensor factor `N' = A[0]` by the regular-module tensor-unit isomorphism.
    simpa [Remark15604Warning.NPrime] using
      (tensor_regular_single0_iso
        (k := k) (K := DerivedCategory.Q.obj (Ext.obj E)))
  have hconj :
      Ext.map
          ((singleCpx₀R).map
            (ModuleCat.ofHom (LinearMap.mulRight R (X (0 : Fin 2) : R)))) =
        (extendScalars_single_regular_iso (k := k)).hom ≫
          (singleCpx₀).map (multiplicationByXMap (k := k)) ≫
            (extendScalars_single_regular_iso (k := k)).inv := by
    -- The single-functor transport reduces the comparison to the module-level map transport
    -- `X₀ ↦ x`.
    calc
      Ext.map
          ((singleCpx₀R).map
            (ModuleCat.ofHom (LinearMap.mulRight R (X (0 : Fin 2) : R)))) =
        ((Functor.mapCochainComplexSingleFunctor
            (ModuleCat.extendScalars (algebraMap R A)) (0 : ℤ)).app
            (ModuleCat.of R R)).hom ≫
          (singleCpx₀).map
            ((ModuleCat.extendScalars (algebraMap R A)).map
              (ModuleCat.ofHom (LinearMap.mulRight R (X (0 : Fin 2) : R)))) ≫
            ((Functor.mapCochainComplexSingleFunctor
              (ModuleCat.extendScalars (algebraMap R A)) (0 : ℤ)).app
              (ModuleCat.of R R)).inv := by
          simpa [Ext] using
            (Functor.mapCochainComplexSingleFunctor
              (ModuleCat.extendScalars (algebraMap R A)) (0 : ℤ)).naturality
              (ModuleCat.ofHom (LinearMap.mulRight R (X (0 : Fin 2) : R)))
      _ =
        ((Functor.mapCochainComplexSingleFunctor
            (ModuleCat.extendScalars (algebraMap R A)) (0 : ℤ)).app
            (ModuleCat.of R R)).hom ≫
          (singleCpx₀).map
            ((extendScalars_regular_iso (k := k)).hom ≫
              multiplicationByXMap (k := k) ≫
                (extendScalars_regular_iso (k := k)).inv) ≫
            ((Functor.mapCochainComplexSingleFunctor
              (ModuleCat.extendScalars (algebraMap R A)) (0 : ℤ)).app
              (ModuleCat.of R R)).inv := by
          rw [extendScalars_mul_X0_transport (k := k)]
      _ =
        (extendScalars_single_regular_iso (k := k)).hom ≫
          (singleCpx₀).map (multiplicationByXMap (k := k)) ≫
            (extendScalars_single_regular_iso (k := k)).inv := by
          simp [extendScalars_single_regular_iso, Category.assoc]
  let eStrict :
      Ext.obj E ≅ stage0KoszulModel (k := k) :=
    CochainComplex.mappingCone.map
      (Ext.map
        ((singleCpx₀R).map
          (ModuleCat.ofHom (LinearMap.mulRight R (X (0 : Fin 2) : R))))
      )
      ((singleCpx₀).map (multiplicationByXMap (k := k)))
      (extendScalars_single_regular_iso (k := k)).hom
      (extendScalars_single_regular_iso (k := k)).hom
      hconj
  -- First compute derived scalar extension on the bounded flat cone, then collapse the regular
  -- degree-zero tensor factor, and finally identify the strict scalar-extended cone with
  -- `A \xrightarrow{x} A`.
  exact eTensor ≪≫ eUnit ≪≫ DerivedCategory.Q.mapIso eStrict

/-- The change-of-rings object
`((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗_R^{\mathbf L} N'`
is represented by the two-term complex `A \xrightarrow{x} A`, namely the canonical derived
powered-Koszul stage. -/
theorem Remark15604Warning.nTensorNPrime_iso_koszulStage0 :
    IsIsomorphic
      (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗[R]^L[A] N')
      ((derivedCompletionKoszulPowersDerivedInverseSystem (fun _ : Fin 1 ↦ x)).obj (op 0)) := by
  rcases restricted_coordinate_quotient_iso_x_resolution (k := k) with ⟨eResolution⟩
  rcases stage0_koszul_owner_iso_mappingCone_x (k := k) with ⟨eStage⟩
  refine ⟨?_⟩
  -- First replace `N_R` by the explicit `R --X₀→ R` free resolution, then apply the dedicated
  -- change-of-rings cone comparison, and finally rewrite the explicit cone as the canonical
  -- stage-`0` powered-Koszul owner.
  exact
    (Functor.mapIso (derivedTensorChangeOfRings (algebraMap R A) N') eResolution) ≪≫
      (x_resolution_tensor_regular_module_iso_mappingCone_x (k := k)) ≪≫
        eStage.symm

/-- Helper for Remark 15.60.4 (Warning): the canonical stage-`0` one-variable Koszul owner is the
derived image of the explicit two-term model `A \xrightarrow{x} A`. -/
private theorem stage0_koszul_owner_iso_mappingCone_x_of_cone_adapter
    (hcone :
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).obj
        (HomologicalComplex.homotopyCofiber
          (x • 𝟙 (K^•(Fin.init (fun _ : Fin 1 ↦ x)))))) ≅
        stage0KoszulModel (k := k)) :
    IsIsomorphic
      ((derivedCompletionKoszulPowersDerivedInverseSystem (fun _ : Fin 1 ↦ x)).obj (op 0))
      (DerivedCategory.Q.obj (stage0KoszulModel (k := k))) := by
  -- First rewrite the stage-`0` owner as the extended homotopy cofiber from the one-variable
  -- Koszul decomposition, then localize the resulting cone identification.
  refine ⟨?_⟩
  exact
    DerivedCategory.Q.mapIso
      (((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).mapIso
          (koszulComplex_iso_homotopyCofiber_truncate_last (f := fun _ : Fin 1 ↦ x))) ≪≫
        hcone)

/-- Helper for Remark 15.60.4 (Warning): the canonical stage-`0` one-variable Koszul owner is the
derived image of the explicit two-term model `A \xrightarrow{x} A`. -/
private theorem stage0_koszul_owner_iso_mappingCone_x :
    IsIsomorphic
      ((derivedCompletionKoszulPowersDerivedInverseSystem (fun _ : Fin 1 ↦ x)).obj (op 0))
      (DerivedCategory.Q.obj (stage0KoszulModel (k := k))) := by
  -- Route correction: isolate the source-faithful normalization of the one-variable stage to the
  -- explicit cone model before using it both in the tensor computation and in perfectness.
  -- The stage-`0` cone adapter is now isolated separately, so the owner-level statement is just
  -- functorial transport.
  exact
    stage0_koszul_owner_iso_mappingCone_x_of_cone_adapter
      (k := k)
      (stage0_singleton_homotopyCofiber_to_mappingCone_x (k := k))

/-- Helper for Remark 15.60.4 (Warning): the regular `A`-module is perfect. This is the length-zero
finite projective resolution input used later for the explicit two-term cone model. -/
private theorem regular_module_isPerfect :
    (ModuleCat.of A A).IsPerfect := by
  -- The regular module has a length-zero finite projective resolution by itself.
  rw [ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms]
  refine ⟨0, ?_⟩
  rw [ModuleCat.hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff]
  constructor <;> infer_instance

/-- Helper for Remark 15.60.4 (Warning): the cochain-level degree-zero model of the regular module
is perfect in `D(A)`. This is the source-facing owner form needed when the stage-`0` Koszul
object is normalized to an explicit mapping-cone complex. -/
private theorem single_complex_regular_module_isPerfect :
    (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj
        (ModuleCat.of A A))).IsPerfect := by
  let P : ObjectProperty DModA := DerivedCategory.IsPerfect
  -- Transport the regular-module perfectness across the canonical `single₀ ≅ Q ∘ singleCpx₀`
  -- comparison.
  exact
    P.prop_of_iso
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
        (ModuleCat.of A A)))
      (regular_module_isPerfect (k := k))

/-- Helper for Remark 15.60.4 (Warning): the explicit two-term cochain model
`A \xrightarrow{x} A` is a perfect object of `D(A)`. -/
private theorem stage0_koszul_model_isPerfect :
    (DerivedCategory.Q.obj (stage0KoszulModel (k := k))).IsPerfect := by
  let P : ObjectProperty DModA := DerivedCategory.IsPerfect
  let T : CategoryTheory.Pretriangulated.Triangle DModA :=
    DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle
        ((singleCpx₀).map (multiplicationByXMap (k := k))))
  have hT : T ∈ CategoryTheory.Pretriangulated.distTriang DModA := by
    -- View the explicit cone as the third vertex of the standard distinguished mapping-cone
    -- triangle in the derived category.
    simpa [T, stage0KoszulModel] using
      DerivedCategory.mappingCone_triangle_distinguished
        ((singleCpx₀).map (multiplicationByXMap (k := k)))
  have h₁ : P T.obj₁ := by
    -- The source of the cone triangle is the degree-zero complex on the regular module.
    simpa [T] using single_complex_regular_module_isPerfect (k := k)
  have h₂ : P T.obj₂ := by
    -- The target of the cone triangle is the same degree-zero perfect object.
    simpa [T] using single_complex_regular_module_isPerfect (k := k)
  have h₃ : P T.obj₃ :=
    P.ext_of_isTriangulatedClosed₃ T hT h₁ h₂
  -- The third vertex of the mapping-cone triangle is exactly the explicit two-term model.
  simpa [T, stage0KoszulModel] using h₃

/-- Helper for Remark 15.60.4 (Warning): the mapping cone of the zero self-map on `M[0]`
splits as the shifted degree-zero object together with the original degree-zero object. -/
private theorem zero_single_map_mappingCone_iso_shift_biprod
    (M : ModuleCat A) :
    DerivedCategory.Q.obj
        (CochainComplex.mappingCone ((singleCpx₀).map (0 : M ⟶ M))) ≅
      (ModuleCat.single0Functor.obj M)⟦(1 : ℤ)⟧ ⊞ ModuleCat.single0Functor.obj M := by
  let β : (singleCpx₀).obj M ⟶ (singleCpx₀).obj M :=
    (singleCpx₀).map (0 : M ⟶ M)
  let T : CategoryTheory.Pretriangulated.Triangle DModA :=
    DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle β)
  have hT : T ∈ CategoryTheory.Pretriangulated.distTriang DModA := by
    -- The standard mapping-cone triangle is distinguished in the derived category.
    simpa [T, β] using DerivedCategory.mappingCone_triangle_distinguished β
  have hTrot : T.rotate ∈ CategoryTheory.Pretriangulated.distTriang DModA := by
    -- Rotate once so the zero map becomes the third edge, where the split-triangle theorem applies.
    exact CategoryTheory.Pretriangulated.rot_of_distTriang _ hT
  have hzero_rot : T.rotate.mor₃ = 0 := by
    -- In the rotated triangle the third edge is `-(Q.map β)⟦1⟧'`, which vanishes because `β = 0`.
    change -((DerivedCategory.Q.map β)⟦(1 : ℤ)⟧') = 0
    simp [β]
  obtain ⟨e, _, _⟩ :=
    CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang T.rotate hTrot hzero_rot
  let eSingle :
      DerivedCategory.Q.obj ((singleCpx₀).obj M) ≅ ModuleCat.single0Functor.obj M :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M).symm
  -- Transport the canonical split obtained from the rotated triangle to the textbook order
  -- `M[1] ⊞ M`.
  exact
    e ≪≫
      Limits.biprod.braiding _ _ ≪≫
        Limits.biprod.mapIso
          ((shiftFunctor DModA (1 : ℤ)).mapIso eSingle)
          eSingle

/-- Helper for Remark 15.60.4 (Warning): the scalar-extended `xy` cone is already the literal
zero self-map cone on the regular degree-zero single complex. -/
private noncomputable theorem single_multiplicationByXYMap_mappingCone_iso_zero :
    CochainComplex.mappingCone ((singleCpx₀).map (multiplicationByXYMap (k := k))) ≅
      CochainComplex.mappingCone
        ((singleCpx₀).map (0 : ModuleCat.of A A ⟶ ModuleCat.of A A)) := by
  -- The degree-zero single map itself is zero, so the two mapping-cone objects are definitionally
  -- the same after rewriting the horizontal differential.
  exact eqToIso (by rw [single_multiplicationByXYMap_eq_zero (k := k)])

/-- Helper for Remark 15.60.4 (Warning): shorthand for the degree-zero single cochain complex on
an `A`-module. -/
private abbrev singleZeroCpx (M : ModuleCat A) : CochainComplex (ModuleCat A) ℤ :=
  (singleCpx₀).obj M

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ

/-- Helper for Remark 15.60.4 (Warning): postcomposing a descended tensor-totalization map can be
checked on each `(p,q)` summand. -/
@[reassoc]
private theorem iTensorObj_mapBifunctorDesc_assoc
    {K L : CpxA} (n : ℤ) {B C : ModuleCat A}
    (f : ∀ p q
      (_h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (ModuleCat A)).obj (K.X p)).obj (L.X q) ⟶ B)
    (u : B ⟶ C) (p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
        HomologicalComplex.mapBifunctorDesc
          (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat A))
          (c := ComplexShape.up ℤ) (A := B) (j := n) f ≫ u =
      f p q h ≫ u := by
  -- Cross the `tensorObj` abbreviation once, then invoke the owner universal-property formula
  -- `ι_mapBifunctorDesc`.
  simpa only [HomologicalComplex.ιTensorObj] using
    congrArg (fun t ↦ t ≫ u)
      (HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat A))
        (c := ComplexShape.up ℤ) (A := B) (j := n) (f := f) p q h)

/-- Helper for Remark 15.60.4 (Warning): away from degree `0`, the single complex contributes a
zero summand to the tensor totalization. -/
private theorem tensor_single0_off_diagonal_isZero
    (E : CpxA) (M : ModuleCat A) (p q : ℤ) (hq : q ≠ 0) :
    CategoryTheory.Limits.IsZero (((curriedTensor (ModuleCat A)).obj (E.X p)).obj
      ((singleZeroCpx (k := k) M).X q)) := by
  -- Apply `tensorLeft (E.X p)` to the vanishing off-degree term of the single complex.
  exact
    CategoryTheory.Functor.map_isZero ((curriedTensor (ModuleCat A)).obj (E.X p))
      (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) (0 : ℤ) M q hq)

/-- Helper for Remark 15.60.4 (Warning): on the surviving degree-`0` summand, tensoring with the
single complex is exactly right tensoring by the underlying module. -/
private noncomputable theorem tensor_single0_diagonal_iso
    (E : CpxA) (M : ModuleCat A) (n : ℤ) :
    ((curriedTensor (ModuleCat A)).obj (E.X n)).obj
      ((singleZeroCpx (k := k) M).X 0) ≅
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n := by
  -- The right-tensor complex is degreewise, so only the canonical degree-`0` identification of
  -- the single complex remains.
  simpa using
    CategoryTheory.Functor.mapIso ((curriedTensor (ModuleCat A)).obj (E.X n))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M)

/-- Helper for Remark 15.60.4 (Warning): the forward degreewise comparison keeps only the unique
diagonal summand of the tensor totalization. -/
private noncomputable theorem tensor_single0_component_hom
    (E : CpxA) (M : ModuleCat A) (n : ℤ) :
    (HomologicalComplex.tensorObj E (singleZeroCpx (k := k) M)).X n ⟶
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n := by
  -- Descend out of the total tensor coproduct, sending only the surviving `(n,0)` summand to the
  -- degreewise right-tensor term.
  exact
    HomologicalComplex.mapBifunctorDesc
      (K₁ := E)
      (K₂ := singleZeroCpx (k := k) M)
      (F := curriedTensor (ModuleCat A))
      (c := ComplexShape.up ℤ)
      (A := (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n))
      (j := n)
      (fun p q h ↦ by
        by_cases hq : q = 0
        · subst hq
          have hp : p = n := by simpa using h
          subst p
          exact (tensor_single0_diagonal_iso (k := k) E M n).hom
        · exact 0)

/-- Helper for Remark 15.60.4 (Warning): on the surviving diagonal summand, the forward tensor
comparison is the canonical degreewise identification. -/
@[reassoc]
private theorem tensor_single0_component_hom_diag
    (E : CpxA) (M : ModuleCat A) (n : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n) :
    HomologicalComplex.ιTensorObj E (singleZeroCpx (k := k) M) n 0 n h ≫
      tensor_single0_component_hom (k := k) E M n =
        (tensor_single0_diagonal_iso (k := k) E M n).hom := by
  let B :
      ModuleCat A :=
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n
  let f : ∀ p q
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (ModuleCat A)).obj (E.X p)).obj
        ((singleZeroCpx (k := k) M).X q) ⟶ B :=
    fun p q h' ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h'
        subst p
        exact (tensor_single0_diagonal_iso (k := k) E M n).hom
      · exact 0
  -- Evaluate the descended tensor map on the unique surviving `(n,0)` summand.
  simpa [tensor_single0_component_hom, B, f] using
    (iTensorObj_mapBifunctorDesc_assoc
      (k := k) (K := E) (L := singleZeroCpx (k := k) M)
      (n := n) (B := B) (C := B) f (𝟙 B) n 0 h)

/-- Helper for Remark 15.60.4 (Warning): away from the diagonal summand, the forward tensor
comparison vanishes. -/
@[reassoc]
private theorem tensor_single0_component_hom_off_diagonal
    (E : CpxA) (M : ModuleCat A) (n p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n)
    (hq : q ≠ 0) :
    HomologicalComplex.ιTensorObj E (singleZeroCpx (k := k) M) p q n h ≫
      tensor_single0_component_hom (k := k) E M n =
        0 := by
  let B :
      ModuleCat A :=
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n
  let f : ∀ p' q'
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p', q') = n),
      ((curriedTensor (ModuleCat A)).obj (E.X p')).obj
        ((singleZeroCpx (k := k) M).X q') ⟶ B :=
    fun p' q' h' ↦ by
      by_cases hq' : q' = 0
      · subst hq'
        have hp' : p' = n := by simpa using h'
        subst p'
        exact (tensor_single0_diagonal_iso (k := k) E M n).hom
      · exact 0
  -- Off the diagonal, the defining branch of the descended map is literally zero.
  simpa [tensor_single0_component_hom, B, f, hq] using
    (iTensorObj_mapBifunctorDesc_assoc
      (k := k) (K := E) (L := singleZeroCpx (k := k) M)
      (n := n) (B := B) (C := B) f (𝟙 B) p q h)

/-- Helper for Remark 15.60.4 (Warning): the inverse degreewise tensor comparison reinserts the
surviving diagonal summand into the tensor totalization. -/
private noncomputable theorem tensor_single0_component_inv
    (E : CpxA) (M : ModuleCat A) (n : ℤ) :
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n ⟶
      (HomologicalComplex.tensorObj E (singleZeroCpx (k := k) M)).X n := by
  -- Reinsert the unique surviving degree `(n,0)` after inverting the diagonal identification.
  exact
    (tensor_single0_diagonal_iso (k := k) E M n).inv ≫
      HomologicalComplex.ιTensorObj E (singleZeroCpx (k := k) M) n 0 n
        (by simp)

/-- Helper for Remark 15.60.4 (Warning): in each total degree, tensoring with a degree-zero
single complex collapses to the unique surviving diagonal summand. -/
private noncomputable theorem tensor_single0_component_iso
    (E : CpxA) (M : ModuleCat A) (n : ℤ) :
    (HomologicalComplex.tensorObj E (singleZeroCpx (k := k) M)).X n ≅
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n := by
  -- Package the forward and inverse diagonal collapse maps as a degreewise isomorphism.
  refine
    { hom := tensor_single0_component_hom (k := k) E M n
      inv := tensor_single0_component_inv (k := k) E M n
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    by_cases hq : q = 0
    · subst hq
      have hp : p = n := by simpa using h
      subst p
      change
        ((HomologicalComplex.ιTensorObj E (singleZeroCpx (k := k) M) n 0 n h ≫
            tensor_single0_component_hom (k := k) E M n) ≫
          tensor_single0_component_inv (k := k) E M n) =
          HomologicalComplex.ιTensorObj E (singleZeroCpx (k := k) M) n 0 n h ≫
            𝟙 ((HomologicalComplex.tensorObj E (singleZeroCpx (k := k) M)).X n)
      simpa [tensor_single0_component_inv, Category.assoc] using
        congrArg (fun m ↦ m ≫ tensor_single0_component_inv (k := k) E M n)
          (tensor_single0_component_hom_diag (k := k) E M n h)
    · change
        ((HomologicalComplex.ιTensorObj E (singleZeroCpx (k := k) M) p q n h ≫
            tensor_single0_component_hom (k := k) E M n) ≫
          tensor_single0_component_inv (k := k) E M n) =
          HomologicalComplex.ιTensorObj E (singleZeroCpx (k := k) M) p q n h ≫
            𝟙 ((HomologicalComplex.tensorObj E (singleZeroCpx (k := k) M)).X n)
      rw [tensor_single0_component_hom_off_diagonal (k := k) E M n p q h hq]
      simp only [CategoryTheory.Limits.zero_comp, Category.comp_id]
      symm
      exact (tensor_single0_off_diagonal_isZero (k := k) E M p q hq).eq_of_src _ _
  · let h0 : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n := by
      simp
    change
      ((tensor_single0_diagonal_iso (k := k) E M n).inv ≫
          HomologicalComplex.ιTensorObj E (singleZeroCpx (k := k) M) n 0 n h0) ≫
        tensor_single0_component_hom (k := k) E M n =
          𝟙 ((((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E).X n)
    calc
      ((tensor_single0_diagonal_iso (k := k) E M n).inv ≫
          HomologicalComplex.ιTensorObj E (singleZeroCpx (k := k) M) n 0 n h0) ≫
        tensor_single0_component_hom (k := k) E M n
          = (tensor_single0_diagonal_iso (k := k) E M n).inv ≫
              (HomologicalComplex.ιTensorObj E (singleZeroCpx (k := k) M) n 0 n h0 ≫
                tensor_single0_component_hom (k := k) E M n) := by
                  simp [Category.assoc]
      _ = (tensor_single0_diagonal_iso (k := k) E M n).inv ≫
            (tensor_single0_diagonal_iso (k := k) E M n).hom := by
              simpa using
                congrArg
                  (fun m ↦ (tensor_single0_diagonal_iso (k := k) E M n).inv ≫ m)
                  (tensor_single0_component_hom_diag (k := k) E M n h0)
      _ = 𝟙 _ := by simp

/-- Helper for Remark 15.60.4 (Warning): the diagonal tensor comparison is natural in the
differential of the left cochain complex. -/
private theorem tensor_single0_diagonal_iso_hom_naturality
    (E : CpxA) (M : ModuleCat A) (i j : ℤ)
    (_hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single0_diagonal_iso (k := k) E M i).hom ≫
        (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E).d i j =
      (((curriedTensor (ModuleCat A)).map (E.d i j)).app
          ((singleZeroCpx (k := k) M).X 0)) ≫
        (tensor_single0_diagonal_iso (k := k) E M j).hom := by
  -- The degreewise comparison comes from functoriality applied to `singleObjXSelf`.
  simpa [tensor_single0_diagonal_iso, CategoryTheory.Functor.mapHomologicalComplex_obj_d,
    singleZeroCpx] using
    (((curriedTensor (ModuleCat A)).map (E.d i j)).naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).hom)

/-- Helper for Remark 15.60.4 (Warning): the inverse diagonal tensor comparison satisfies the
same naturality square rewritten for the chain-level inverse map. -/
private theorem tensor_single0_diagonal_iso_inv_naturality
    (E : CpxA) (M : ModuleCat A) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single0_diagonal_iso (k := k) E M i).inv ≫
        (((curriedTensor (ModuleCat A)).map (E.d i j)).app
          ((singleZeroCpx (k := k) M).X 0)) =
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E).d i j ≫
        (tensor_single0_diagonal_iso (k := k) E M j).inv := by
  -- Cancel the target diagonal isomorphism and reuse the forward naturality square.
  apply (cancel_mono (tensor_single0_diagonal_iso (k := k) E M j).hom).1
  simpa [Category.assoc] using
    calc
      (tensor_single0_diagonal_iso (k := k) E M i).inv ≫
          (((curriedTensor (ModuleCat A)).map (E.d i j)).app
            ((singleZeroCpx (k := k) M).X 0)) ≫
          (tensor_single0_diagonal_iso (k := k) E M j).hom
        = (tensor_single0_diagonal_iso (k := k) E M i).inv ≫
            ((tensor_single0_diagonal_iso (k := k) E M i).hom ≫
              (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj E).d i j) := by
                  rw [tensor_single0_diagonal_iso_hom_naturality (k := k) E M i j hij]
      _ =
          (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E).d i j := by
            simp

/-- Helper for Remark 15.60.4 (Warning): the inverse degreewise tensor comparison already
respects the cochain differential. -/
private theorem tensor_single0_component_inv_comm
    (E : CpxA) (M : ModuleCat A) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    tensor_single0_component_inv (k := k) E M i ≫
        (HomologicalComplex.tensorObj E (singleZeroCpx (k := k) M)).d i j =
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E).d i j ≫
        tensor_single0_component_inv (k := k) E M j := by
  have hj : j = i + 1 := by
    simpa [ComplexShape.up, eq_comm] using hij
  subst hj
  -- Expand the total differential; the vertical contribution vanishes because the single complex
  -- has zero outgoing differential in degree `0`.
  simp only [tensor_single0_component_inv, Category.assoc,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq
      (K₁ := E)
      (K₂ := singleZeroCpx (k := k) M)
      (F := curriedTensor (ModuleCat A))
      (c := ComplexShape.up ℤ)
      (h := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))
      (i₂ := 0)
      (j := i + 1)
      (h' := by simp)]
  rw [HomologicalComplex.mapBifunctor.d₂_eq
      (K₁ := E)
      (K₂ := singleZeroCpx (k := k) M)
      (F := curriedTensor (ModuleCat A))
      (c := ComplexShape.up ℤ)
      (i₁ := i)
      (h := (show (ComplexShape.up ℤ).Rel 0 (0 + 1) by simp))
      (j := i + 1)
      (h' := by simp)]
  have hsingle : ((singleZeroCpx (k := k) M).d 0 (0 + 1)) = 0 := rfl
  rw [hsingle, Functor.map_zero, CategoryTheory.Limits.zero_comp, smul_zero,
    CategoryTheory.Limits.comp_zero, add_zero]
  rw [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, 0) = 1 by
      rfl, one_smul]
  rw [← Category.assoc]
  rw [tensor_single0_diagonal_iso_inv_naturality
      (k := k) (E := E) (M := M) (i := i) (j := i + 1)
      (hij := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))]
  simp [HomologicalComplex.ιTensorObj, Category.assoc]

/-- Helper for Remark 15.60.4 (Warning): tensoring a cochain complex with a degree-zero single
complex is canonically the same as tensoring on the right by the underlying module. -/
private noncomputable theorem tensor_single0_complex_iso
    (E : CpxA) (M : ModuleCat A) :
    HomologicalComplex.tensorObj E (singleZeroCpx (k := k) M) ≅
      ((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E := by
  -- Assemble the degreewise diagonal-collapse isomorphisms and use the inverse-chain-map lemma to
  -- discharge the compatibility with differentials.
  exact
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ tensor_single0_component_iso (k := k) E M n)
      (fun i j hij ↦ by
        apply (cancel_mono (tensor_single0_component_iso (k := k) E M j).inv).1
        apply (cancel_epi (tensor_single0_component_iso (k := k) E M i).inv).1
        simpa [Category.assoc] using
          tensor_single0_component_inv_comm (k := k) E M i j hij)

/-- Helper for Remark 15.60.4 (Warning): right tensoring the degree-zero regular complex by the
coordinate quotient `A/(x)` stays degree-zero and identifies with the single complex on `A/(x)`. -/
private noncomputable theorem tensor_right_regular_single0_coordinate_quotient_iso :
    ((CategoryTheory.MonoidalCategory.tensorRight
        (ModuleCat.of A (A ⧸ principalIdeal x))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (singleZeroCpx (k := k) (ModuleCat.of A A)) ≅
      singleZeroCpx (k := k) (ModuleCat.of A (A ⧸ principalIdeal x)) := by
  -- First use the canonical single-complex transport for `tensorRight`, then collapse the left
  -- regular factor `A ⊗[A] A/(x)`.
  exact
    ((HomologicalComplex.singleMapHomologicalComplex
        (CategoryTheory.MonoidalCategory.tensorRight
          (ModuleCat.of A (A ⧸ principalIdeal x)))
        (ComplexShape.up ℤ) (0 : ℤ)).app (ModuleCat.of A A)) ≪≫
      Functor.mapIso singleCpx₀
        (regular_leftTensor_module_iso (k := k) (M := A ⧸ principalIdeal x))

/-- Helper for Remark 15.60.4 (Warning): right tensoring the zero-map cone on the regular
degree-zero complex by `A/(x)` gives the zero-map cone on `A/(x)[0]` at cochain level. -/
private noncomputable theorem tensor_right_zero_regular_mappingCone_coordinate_quotient_complex_iso :
    (((CategoryTheory.MonoidalCategory.tensorRight
        (ModuleCat.of A (A ⧸ principalIdeal x))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone
        ((singleCpx₀).map (0 : ModuleCat.of A A ⟶ ModuleCat.of A A)))) ≅
      CochainComplex.mappingCone
        ((singleCpx₀).map
          (0 :
            ModuleCat.of A (A ⧸ principalIdeal x) ⟶
              ModuleCat.of A (A ⧸ principalIdeal x))) := by
  let Mq : ModuleCat A := ModuleCat.of A (A ⧸ principalIdeal x)
  let F :
      CochainComplex (ModuleCat A) ℤ ⥤ CochainComplex (ModuleCat A) ℤ :=
    (CategoryTheory.MonoidalCategory.tensorRight Mq).mapHomologicalComplex (ComplexShape.up ℤ)
  let E :
      CochainComplex (ModuleCat A) ℤ :=
    CochainComplex.mappingCone ((singleCpx₀).map (0 : ModuleCat.of A A ⟶ ModuleCat.of A A))
  let T :
      CochainComplex (ModuleCat A) ℤ :=
    CochainComplex.mappingCone ((singleCpx₀).map (0 : Mq ⟶ Mq))
  refine HomologicalComplex.Hom.isoOfComponents ?_ ?_
  · intro i
    by_cases hi0 : i = 0
    · subst hi0
      -- In degree `0`, both complexes identify with the coordinate quotient module.
      exact
        (Functor.mapIso (CategoryTheory.MonoidalCategory.tensorRight Mq)
          (single_map_mappingCone_component_zero_iso
            (M := ModuleCat.of A A) (g := (0 : ModuleCat.of A A ⟶ ModuleCat.of A A)))) ≪≫
          (Functor.mapIso (CategoryTheory.MonoidalCategory.tensorRight Mq)
            (HomologicalComplex.singleObjXSelf
              (ComplexShape.up ℤ) (0 : ℤ) (ModuleCat.of A A))) ≪≫
            (regular_leftTensor_module_iso (k := k) (M := A ⧸ principalIdeal x)) ≪≫
              ((single_map_mappingCone_component_zero_iso
                (M := Mq) (g := (0 : Mq ⟶ Mq))) ≪≫
                (HomologicalComplex.singleObjXSelf
                  (ComplexShape.up ℤ) (0 : ℤ) Mq)).symm
    · by_cases hiNegOne : i = -1
      · subst hiNegOne
        -- In degree `-1`, the same collapse identifies the surviving source term with `A/(x)`.
        exact
          (Functor.mapIso (CategoryTheory.MonoidalCategory.tensorRight Mq)
            (single_map_mappingCone_component_neg_one_iso
              (M := ModuleCat.of A A) (g := (0 : ModuleCat.of A A ⟶ ModuleCat.of A A)))) ≪≫
            (Functor.mapIso (CategoryTheory.MonoidalCategory.tensorRight Mq)
              (HomologicalComplex.singleObjXSelf
                (ComplexShape.up ℤ) (0 : ℤ) (ModuleCat.of A A))) ≪≫
              (regular_leftTensor_module_iso (k := k) (M := A ⧸ principalIdeal x)) ≪≫
                ((single_map_mappingCone_component_neg_one_iso
                  (M := Mq) (g := (0 : Mq ⟶ Mq))) ≪≫
                  (HomologicalComplex.singleObjXSelf
                    (ComplexShape.up ℤ) (0 : ℤ) Mq)).symm
      · -- Outside degrees `0` and `-1`, both complexes are zero.
        let hSrc :
            CategoryTheory.Limits.IsZero ((F.obj E).X i) :=
          CategoryTheory.Functor.map_isZero (CategoryTheory.MonoidalCategory.tensorRight Mq)
            (single_map_mappingCone_isZero_outside
              (M := ModuleCat.of A A)
              (g := (0 : ModuleCat.of A A ⟶ ModuleCat.of A A)) hi0 hiNegOne)
        let hTgt :
            CategoryTheory.Limits.IsZero (T.X i) :=
          single_map_mappingCone_isZero_outside
            (M := Mq) (g := (0 : Mq ⟶ Mq)) hi0 hiNegOne
        exact hSrc.isoZero ≪≫ hTgt.isoZero.symm
  · intro i j hij
    have hj : j = i + 1 := by
      simpa [ComplexShape.up, eq_comm] using hij
    subst hj
    have hFd : (F.obj E).d i (i + 1) = 0 := by
      -- The source differential is the image of the zero cone differential under right tensoring.
      simp [F, E, CategoryTheory.Functor.mapHomologicalComplex_obj_d]
    have hTd : T.d i (i + 1) = 0 := by
      -- The target cone is also built from the zero map between degree-zero single complexes.
      simp [T]
    rw [hFd, hTd, CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]

/-- Helper for Remark 15.60.4 (Warning): tensoring the zero-map cone on the regular degree-zero
complex with `N = (A/(x))[0]` yields the zero-map cone on `N[0]` in `D(A)`. -/
private noncomputable theorem zero_regular_mappingCone_tensor_coordinate_quotient_iso :
    (DerivedCategory.Q.obj
        (CochainComplex.mappingCone
          ((singleCpx₀).map (0 : ModuleCat.of A A ⟶ ModuleCat.of A A))) ⊗[A]^L N) ≅
      DerivedCategory.Q.obj
        (CochainComplex.mappingCone
          ((singleCpx₀).map
            (0 :
              ModuleCat.of A (A ⧸ principalIdeal x) ⟶
                ModuleCat.of A (A ⧸ principalIdeal x)))) := by
  let Mq : ModuleCat A := ModuleCat.of A (A ⧸ principalIdeal x)
  let E :
      CochainComplex (ModuleCat A) ℤ :=
    CochainComplex.mappingCone ((singleCpx₀).map (0 : ModuleCat.of A A ⟶ ModuleCat.of A A))
  let eTensor :
      (DerivedCategory.Q.obj E ⊗[A]^L N) ≅
        DerivedCategory.Q.obj (HomologicalComplex.tensorObj E (singleZeroCpx (k := k) Mq)) :=
    (derivedCategory_tensorObj_iso_derivedTensorProduct
      (DerivedCategory.Q.obj E) N).symm ≪≫
      ((Iso.refl _) ⊗ᵢ ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app Mq)) ≪≫
        (Functor.Monoidal.μIso
          (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DModA)
          E (singleZeroCpx (k := k) Mq)).symm
  -- First compute the derived tensor by the strict tensor complex, then collapse tensoring with
  -- `Mq[0]` to right tensoring, and finally identify the resulting zero cone with the literal
  -- zero-map cone on `Mq[0]`.
  exact
    eTensor ≪≫
      DerivedCategory.Q.mapIso (tensor_single0_complex_iso (k := k) E Mq) ≪≫
        DerivedCategory.Q.mapIso
          (tensor_right_zero_regular_mappingCone_coordinate_quotient_complex_iso (k := k))

/-- The second change-of-rings object
`((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') ⊗_R^{\mathbf L} N`
is represented by `N[1] ⊞ N`. -/
/-- Helper for Remark 15.60.4 (Warning): tensoring the two-term free resolution
`R \xrightarrow{X₀X₁} R` with the coordinate quotient `N = (A/(x))[0]` computes the zero-map
cone on `N`. -/
private theorem xy_resolution_tensor_coordinate_quotient_iso_zero_mappingCone :
    ((DerivedCategory.Q.obj
        (CochainComplex.mappingCone
          ((singleCpx₀R).map
            (ModuleCat.ofHom
              (LinearMap.mulRight R
                ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))))) ⊗[R]^L[A] N) ≅
      DerivedCategory.Q.obj
        (CochainComplex.mappingCone
          ((singleCpx₀).map
            (0 :
              ModuleCat.of A (A ⧸ principalIdeal x) ⟶
                ModuleCat.of A (A ⧸ principalIdeal x)))) := by
  let Mq : ModuleCat A := ModuleCat.of A (A ⧸ principalIdeal x)
  let E : CochainComplex (ModuleCat R) ℤ :=
    CochainComplex.mappingCone
      ((singleCpx₀R).map
        (ModuleCat.ofHom
          (LinearMap.mulRight R ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))))
  let Ext :
      CochainComplex (ModuleCat R) ℤ ⥤ CochainComplex (ModuleCat A) ℤ :=
    (ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)
  have hEFlat : E.IsTermwiseFlat := by
    -- The two-term free resolution is termwise flat because both nonzero terms are copies of `R`.
    infer_instance
  have hELE : E.IsStrictlyLE 0 := by
    -- The explicit cone is supported only in cochain degrees `-1` and `0`.
    infer_instance
  let eBase :
      ((DerivedCategory.Q.obj E) ⊗[R]^L[A]) ≅
        DerivedCategory.Q.obj (Ext.obj E) :=
    CategoryTheory.derivedTensorWithAlgebra_obj_iso_of_termwiseFlat_of_isStrictlyLE
      (A := R) (B := A) (E := E) hEFlat hELE
  let eTensor :
      ((DerivedCategory.Q.obj E) ⊗[R]^L[A] N) ≅
        (DerivedCategory.Q.obj (Ext.obj E) ⊗[A]^L N) :=
    Functor.mapIso (derivedTensorProduct N) eBase
  have hconj :
      Ext.map
          ((singleCpx₀R).map
            (ModuleCat.ofHom
              (LinearMap.mulRight R ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))))) =
        (extendScalars_single_regular_iso (k := k)).hom ≫
          (singleCpx₀).map (multiplicationByXYMap (k := k)) ≫
            (extendScalars_single_regular_iso (k := k)).inv := by
    -- The single-functor transport again reduces the comparison to the module-level scalar
    -- extension formula for multiplication by `X₀X₁`.
    calc
      Ext.map
          ((singleCpx₀R).map
            (ModuleCat.ofHom
              (LinearMap.mulRight R ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))))) =
        ((Functor.mapCochainComplexSingleFunctor
            (ModuleCat.extendScalars (algebraMap R A)) (0 : ℤ)).app
            (ModuleCat.of R R)).hom ≫
          (singleCpx₀).map
            ((ModuleCat.extendScalars (algebraMap R A)).map
              (ModuleCat.ofHom
                (LinearMap.mulRight R ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))))) ≫
            ((Functor.mapCochainComplexSingleFunctor
              (ModuleCat.extendScalars (algebraMap R A)) (0 : ℤ)).app
              (ModuleCat.of R R)).inv := by
          simpa [Ext] using
            (Functor.mapCochainComplexSingleFunctor
              (ModuleCat.extendScalars (algebraMap R A)) (0 : ℤ)).naturality
              (ModuleCat.ofHom
                (LinearMap.mulRight R ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R))))
      _ =
        ((Functor.mapCochainComplexSingleFunctor
            (ModuleCat.extendScalars (algebraMap R A)) (0 : ℤ)).app
            (ModuleCat.of R R)).hom ≫
          (singleCpx₀).map
            ((extendScalars_regular_iso (k := k)).hom ≫
              multiplicationByXYMap (k := k) ≫
                (extendScalars_regular_iso (k := k)).inv) ≫
            ((Functor.mapCochainComplexSingleFunctor
              (ModuleCat.extendScalars (algebraMap R A)) (0 : ℤ)).app
              (ModuleCat.of R R)).inv := by
          rw [extendScalars_mul_XY_transport (k := k)]
      _ =
        (extendScalars_single_regular_iso (k := k)).hom ≫
          (singleCpx₀).map (multiplicationByXYMap (k := k)) ≫
            (extendScalars_single_regular_iso (k := k)).inv := by
          simp [extendScalars_single_regular_iso, Category.assoc]
  let eStrict :
      Ext.obj E ≅
        CochainComplex.mappingCone ((singleCpx₀).map (multiplicationByXYMap (k := k))) :=
    CochainComplex.mappingCone.map
      (Ext.map
        ((singleCpx₀R).map
          (ModuleCat.ofHom
            (LinearMap.mulRight R ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))))
      )
      ((singleCpx₀).map (multiplicationByXYMap (k := k)))
      (extendScalars_single_regular_iso (k := k)).hom
      (extendScalars_single_regular_iso (k := k)).hom
      hconj
  -- First perform scalar extension on the bounded flat `R`-cone, then rewrite the transported
  -- `xy` differential to zero, and finally tensor the resulting zero cone with `N = (A/(x))[0]`.
  exact
    eTensor ≪≫
      Functor.mapIso (derivedTensorProduct N) (DerivedCategory.Q.mapIso eStrict) ≪≫
        Functor.mapIso (derivedTensorProduct N)
          (DerivedCategory.Q.mapIso
            (single_multiplicationByXYMap_mappingCone_iso_zero (k := k))) ≪≫
          (zero_regular_mappingCone_tensor_coordinate_quotient_iso (k := k))

/-- The second change-of-rings object
`((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') ⊗_R^{\mathbf L} N`
is represented by `N[1] ⊞ N`. -/
theorem Remark15604Warning.nPrimeTensorN_iso_shiftBiproduct :
    IsIsomorphic
      (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') ⊗[R]^L[A] N)
      (N⟦(1 : ℤ)⟧ ⊞ N) := by
  rcases restricted_node_ring_iso_xy_resolution (k := k) with ⟨eResolution⟩
  refine ⟨?_⟩
  -- First replace `N'_R` by the explicit `R --X₀X₁→ R` free resolution, then rewrite the
  -- resulting tensor as the zero-map cone on `N`, and finally split that cone.
  exact
    (Functor.mapIso (derivedTensorChangeOfRings (algebraMap R A) N) eResolution) ≪≫
      (xy_resolution_tensor_coordinate_quotient_iso_zero_mappingCone (k := k)) ≪≫
        (zero_single_map_mappingCone_iso_shift_biprod
          (k := k) (M := ModuleCat.of A (A ⧸ principalIdeal x)))

/-- Helper for Remark 15.60.4 (Warning): multiplication by `x` has image equal to the principal
ideal `(x) ⊆ A`. -/
private theorem mul_x_range_eq_principalIdeal :
    LinearMap.range (LinearMap.mulLeft A x) = principalIdeal x := by
  -- The image consists exactly of multiples of `x`.
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    rw [principalIdeal]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · intro hz
    rw [principalIdeal] at hz
    rcases Ideal.mem_span_singleton.mp hz with ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    simp [LinearMap.mulLeft_apply, mul_comm]

/-- Helper for Remark 15.60.4 (Warning): multiplication by `y` has image equal to the principal
ideal `(y) ⊆ A`. -/
private theorem mul_y_range_eq_principalIdeal :
    LinearMap.range (LinearMap.mulLeft A y) = principalIdeal y := by
  -- The image consists exactly of multiples of `y`.
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    rw [principalIdeal]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · intro hz
    rw [principalIdeal] at hz
    rcases Ideal.mem_span_singleton.mp hz with ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    simp [LinearMap.mulLeft_apply, mul_comm]

/-- Helper for Remark 15.60.4 (Warning): the quotient map `A → A/(x)` has kernel `(x)` at the
module level. -/
private theorem quotient_by_x_ker :
    LinearMap.ker ((Ideal.Quotient.mkₐ A (principalIdeal x)).toLinearMap) = principalIdeal x := by
  -- The linear kernel is the defining quotient ideal.
  ext z
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Helper for Remark 15.60.4 (Warning): the quotient map `A → A/(y)` has kernel `(y)` at the
module level. -/
private theorem quotient_by_y_ker :
    LinearMap.ker ((Ideal.Quotient.mkₐ A (principalIdeal y)).toLinearMap) = principalIdeal y := by
  -- The linear kernel is the defining quotient ideal.
  ext z
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Helper for Remark 15.60.4 (Warning): `0 → range(·x) → A → A/(x) → 0` is short exact. This is
the range-form half of the periodic coordinate syzygy package from the source proof. -/
private theorem coordinate_range_shortExact_x :
    (ShortComplex.mk
      (ModuleCat.ofHom (LinearMap.range (LinearMap.mulLeft A x)).subtype)
      (ModuleCat.ofHom (Ideal.Quotient.mkₐ A (principalIdeal x)).toLinearMap)
      (by
        -- Elements in the range are multiples of `x`, hence vanish in the quotient by `(x)`.
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun z ↦ by
          change Ideal.Quotient.mk (principalIdeal x) z.1 = 0
          exact (Ideal.Quotient.eq_zero_iff_mem).2 <| by
            rw [← mul_x_range_eq_principalIdeal (k := k)]
            exact z.2)).ShortExact := by
  -- Exactness is the source-facing statement `range(·x) = ker(A → A/(x))`.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · let S : ShortComplex (ModuleCat A) :=
      ShortComplex.mk
        (ModuleCat.ofHom (LinearMap.range (LinearMap.mulLeft A x)).subtype)
        (ModuleCat.ofHom (Ideal.Quotient.mkₐ A (principalIdeal x)).toLinearMap)
        (by
          apply ModuleCat.hom_ext
          exact LinearMap.ext fun z ↦ by
            change Ideal.Quotient.mk (principalIdeal x) z.1 = 0
            exact (Ideal.Quotient.eq_zero_iff_mem).2 <| by
              rw [← mul_x_range_eq_principalIdeal (k := k)]
              exact z.2)
    change S.Exact
    rw [S.moduleCat_exact_iff_range_eq_ker]
    change
      LinearMap.range ((ModuleCat.ofHom (LinearMap.range (LinearMap.mulLeft A x)).subtype : _).hom) =
        LinearMap.ker ((Ideal.Quotient.mkₐ A (principalIdeal x)).toLinearMap)
    rw [quotient_by_x_ker (k := k)]
    simpa [S, Submodule.range_subtype] using mul_x_range_eq_principalIdeal (k := k)
  · exact (ModuleCat.mono_iff_injective _).2 fun a b h => Subtype.ext h
  · exact (ModuleCat.epi_iff_surjective _).2 (Ideal.Quotient.mkₐ_surjective A (principalIdeal x))

/-- Helper for Remark 15.60.4 (Warning): `0 → range(·y) → A → A/(y) → 0` is short exact. This is
the second range-form half of the periodic coordinate syzygy package from the source proof. -/
private theorem coordinate_range_shortExact_y :
    (ShortComplex.mk
      (ModuleCat.ofHom (LinearMap.range (LinearMap.mulLeft A y)).subtype)
      (ModuleCat.ofHom (Ideal.Quotient.mkₐ A (principalIdeal y)).toLinearMap)
      (by
        -- Elements in the range are multiples of `y`, hence vanish in the quotient by `(y)`.
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun z ↦ by
          change Ideal.Quotient.mk (principalIdeal y) z.1 = 0
          exact (Ideal.Quotient.eq_zero_iff_mem).2 <| by
            rw [← mul_y_range_eq_principalIdeal (k := k)]
            exact z.2)).ShortExact := by
  -- Exactness is the source-facing statement `range(·y) = ker(A → A/(y))`.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · let S : ShortComplex (ModuleCat A) :=
      ShortComplex.mk
        (ModuleCat.ofHom (LinearMap.range (LinearMap.mulLeft A y)).subtype)
        (ModuleCat.ofHom (Ideal.Quotient.mkₐ A (principalIdeal y)).toLinearMap)
        (by
          apply ModuleCat.hom_ext
          exact LinearMap.ext fun z ↦ by
            change Ideal.Quotient.mk (principalIdeal y) z.1 = 0
            exact (Ideal.Quotient.eq_zero_iff_mem).2 <| by
              rw [← mul_y_range_eq_principalIdeal (k := k)]
              exact z.2)
    change S.Exact
    rw [S.moduleCat_exact_iff_range_eq_ker]
    change
      LinearMap.range ((ModuleCat.ofHom (LinearMap.range (LinearMap.mulLeft A y)).subtype : _).hom) =
        LinearMap.ker ((Ideal.Quotient.mkₐ A (principalIdeal y)).toLinearMap)
    rw [quotient_by_y_ker (k := k)]
    simpa [S, Submodule.range_subtype] using mul_y_range_eq_principalIdeal (k := k)
  · exact (ModuleCat.mono_iff_injective _).2 fun a b h => Subtype.ext h
  · exact (ModuleCat.epi_iff_surjective _).2 (Ideal.Quotient.mkₐ_surjective A (principalIdeal y))

section

variable [Nontrivial k]

/-- Helper for Remark 15.60.4 (Warning): evaluating `A = k[x,y]/(xy)` at `x = X`, `y = 0`
produces a quotient map to `k[X]`. -/
private noncomputable def quotientToPolynomialX :
    A →ₐ[k] Polynomial k :=
  Ideal.Quotient.liftₐ
    (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))
    (MvPolynomial.aeval
      (fun i : Fin 2 ↦ if i = 0 then (Polynomial.X : Polynomial k) else 0))
    (by
      -- The defining relation `xy` maps to `X * 0 = 0`.
      intro φ hφ
      rcases Ideal.mem_span_singleton.mp (by simpa [principalIdeal] using hφ) with ⟨ψ, rfl⟩
      simp [mul_assoc])

/-- Helper for Remark 15.60.4 (Warning): evaluating `A = k[x,y]/(xy)` at `x = 0`, `y = X`
produces a quotient map to `k[X]`. -/
private noncomputable def quotientToPolynomialY :
    A →ₐ[k] Polynomial k :=
  Ideal.Quotient.liftₐ
    (principalIdeal ((X (0 : Fin 2) : R) * (X (1 : Fin 2) : R)))
    (MvPolynomial.aeval
      (fun i : Fin 2 ↦ if i = 1 then (Polynomial.X : Polynomial k) else 0))
    (by
      -- The defining relation `xy` maps to `0 * X = 0`.
      intro φ hφ
      rcases Ideal.mem_span_singleton.mp (by simpa [principalIdeal] using hφ) with ⟨ψ, rfl⟩
      simp [mul_assoc])

/-- Helper for Remark 15.60.4 (Warning): under the `x = X`, `y = 0` specialization, the class of
`x` maps to the polynomial variable `X`. -/
private theorem quotientToPolynomialX_map_x :
    quotientToPolynomialX (k := k) x = Polynomial.X := by
  -- Evaluate the quotient lift on the class of the first variable.
  simp [quotientToPolynomialX, Remark15604Warning.x]

/-- Helper for Remark 15.60.4 (Warning): under the `x = X`, `y = 0` specialization, the class of
`y` vanishes. -/
private theorem quotientToPolynomialX_map_y :
    quotientToPolynomialX (k := k) y = 0 := by
  -- Evaluate the quotient lift on the class of the second variable.
  simp [quotientToPolynomialX, Remark15604Warning.y]

/-- Helper for Remark 15.60.4 (Warning): under the `x = 0`, `y = X` specialization, the class of
`x` vanishes. -/
private theorem quotientToPolynomialY_map_x :
    quotientToPolynomialY (k := k) x = 0 := by
  -- Evaluate the quotient lift on the class of the first variable.
  simp [quotientToPolynomialY, Remark15604Warning.x]

/-- Helper for Remark 15.60.4 (Warning): under the `x = 0`, `y = X` specialization, the class of
`y` maps to the polynomial variable `X`. -/
private theorem quotientToPolynomialY_map_y :
    quotientToPolynomialY (k := k) y = Polynomial.X := by
  -- Evaluate the quotient lift on the class of the second variable.
  simp [quotientToPolynomialY, Remark15604Warning.y]

/-- Helper for Remark 15.60.4 (Warning): the quotient `A / (x)` maps to `k[X]` by sending the
residue class of `y` to `X`. -/
private noncomputable def quotientByXToPolynomial :
    A ⧸ principalIdeal x →ₐ[k] Polynomial k :=
  Ideal.Quotient.liftₐ
    (principalIdeal x)
    (quotientToPolynomialY (k := k))
    (by
      intro a ha
      rw [principalIdeal] at ha
      rcases Ideal.mem_span_singleton.mp ha with ⟨b, rfl⟩
      simp [map_mul, quotientToPolynomialY_map_x (k := k)])

/-- Helper for Remark 15.60.4 (Warning): the quotient `A / (y)` maps to `k[X]` by sending the
residue class of `x` to `X`. -/
private noncomputable def quotientByYToPolynomial :
    A ⧸ principalIdeal y →ₐ[k] Polynomial k :=
  Ideal.Quotient.liftₐ
    (principalIdeal y)
    (quotientToPolynomialX (k := k))
    (by
      intro a ha
      rw [principalIdeal] at ha
      rcases Ideal.mem_span_singleton.mp ha with ⟨b, rfl⟩
      simp [map_mul, quotientToPolynomialX_map_y (k := k)])

/-- Helper for Remark 15.60.4 (Warning): the quotient class of `y` in `A / (x)` maps to `X`. -/
private theorem quotientByXToPolynomial_map_y :
    quotientByXToPolynomial (k := k) (Ideal.Quotient.mk (principalIdeal x) y) = Polynomial.X := by
  -- Unfold to the defining specialization `x = 0`, `y = X`.
  simp [quotientByXToPolynomial, quotientToPolynomialY_map_y (k := k)]

/-- Helper for Remark 15.60.4 (Warning): the quotient class of `x` in `A / (y)` maps to `X`. -/
private theorem quotientByYToPolynomial_map_x :
    quotientByYToPolynomial (k := k) (Ideal.Quotient.mk (principalIdeal y) x) = Polynomial.X := by
  -- Unfold to the defining specialization `x = X`, `y = 0`.
  simp [quotientByYToPolynomial, quotientToPolynomialX_map_x (k := k)]

/-- Helper for Remark 15.60.4 (Warning): the quotient class of `x` vanishes in `A / (x)`. -/
private theorem quotientByX_mk_x_eq_zero :
    Ideal.Quotient.mk (principalIdeal x) x = (0 : A ⧸ principalIdeal x) := by
  -- This is the defining quotient relation for `(x)`.
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self x

/-- Helper for Remark 15.60.4 (Warning): the quotient class of `xy` already vanishes in
`A / (x)`. This is the algebra input needed when the scalar-extended `R \xrightarrow{X₀X₁} R`
resolution is rewritten as the zero-map cone on the coordinate quotient. -/
private theorem quotientByX_mk_xy_eq_zero :
    Ideal.Quotient.mk (principalIdeal x) (x * y) = (0 : A ⧸ principalIdeal x) := by
  -- The relation `xy = 0` already holds in `A`, so its image in the quotient ring is zero.
  simpa [Remark15604Warning.x_mul_y_eq_zero (k := k)]

/-- Helper for Remark 15.60.4 (Warning): the quotient class of `y` vanishes in `A / (y)`. -/
private theorem quotientByY_mk_y_eq_zero :
    Ideal.Quotient.mk (principalIdeal y) y = (0 : A ⧸ principalIdeal y) := by
  -- This is the defining quotient relation for `(y)`.
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self y

/-- Helper for Remark 15.60.4 (Warning): evaluating at the quotient class of `y` reconstructs
`A / (x)` from `k[X]`. -/
private noncomputable def polynomialToQuotientByX :
    Polynomial k →ₐ[k] (A ⧸ principalIdeal x) :=
  Polynomial.aeval (Ideal.Quotient.mkₐ A (principalIdeal x) y)

/-- Helper for Remark 15.60.4 (Warning): evaluating at the quotient class of `x` reconstructs
`A / (y)` from `k[X]`. -/
private noncomputable def polynomialToQuotientByY :
    Polynomial k →ₐ[k] (A ⧸ principalIdeal y) :=
  Polynomial.aeval (Ideal.Quotient.mkₐ A (principalIdeal y) x)

/-- Helper for Remark 15.60.4 (Warning): the `A / (x) ↔ k[X]` comparison is a right inverse on
the polynomial side. -/
private theorem quotientByX_polynomial_right_inverse :
    (quotientByXToPolynomial (k := k)).comp (polynomialToQuotientByX (k := k)) =
      AlgHom.id k (Polynomial k) := by
  -- Compare algebra maps out of `k[X]` on the generator `X`.
  ext p : 1
  simp [polynomialToQuotientByX, quotientByXToPolynomial_map_y (k := k)]

/-- Helper for Remark 15.60.4 (Warning): the `A / (y) ↔ k[X]` comparison is a right inverse on
the polynomial side. -/
private theorem quotientByY_polynomial_right_inverse :
    (quotientByYToPolynomial (k := k)).comp (polynomialToQuotientByY (k := k)) =
      AlgHom.id k (Polynomial k) := by
  -- Compare algebra maps out of `k[X]` on the generator `X`.
  ext p : 1
  simp [polynomialToQuotientByY, quotientByYToPolynomial_map_x (k := k)]

/-- Helper for Remark 15.60.4 (Warning): the `A / (x) ↔ k[X]` comparison is a left inverse on
the quotient side. -/
private theorem quotientByX_polynomial_left_inverse :
    (polynomialToQuotientByX (k := k)).comp (quotientByXToPolynomial (k := k)) =
      AlgHom.id k (A ⧸ principalIdeal x) := by
  -- Reduce first to a representative in `A`, then to a polynomial representative in `k[x,y]`.
  ext q
  refine Quotient.inductionOn' q ?_
  intro a
  refine Quotient.inductionOn' a ?_
  intro φ
  simp [polynomialToQuotientByX, quotientByXToPolynomial, quotientToPolynomialY,
    quotientByX_mk_x_eq_zero (k := k), Remark15604Warning.x, Remark15604Warning.y]

/-- Helper for Remark 15.60.4 (Warning): the `A / (y) ↔ k[X]` comparison is a left inverse on
the quotient side. -/
private theorem quotientByY_polynomial_left_inverse :
    (polynomialToQuotientByY (k := k)).comp (quotientByYToPolynomial (k := k)) =
      AlgHom.id k (A ⧸ principalIdeal y) := by
  -- Reduce first to a representative in `A`, then to a polynomial representative in `k[x,y]`.
  ext q
  refine Quotient.inductionOn' q ?_
  intro a
  refine Quotient.inductionOn' a ?_
  intro φ
  simp [polynomialToQuotientByY, quotientByYToPolynomial, quotientToPolynomialX,
    quotientByY_mk_y_eq_zero (k := k), Remark15604Warning.x, Remark15604Warning.y]

/-- Helper for Remark 15.60.4 (Warning): quotienting by `(x)` identifies the coordinate quotient
with the polynomial ring in the remaining variable. -/
private noncomputable theorem quotientByXAlgEquivPolynomial :
    A ⧸ principalIdeal x ≃ₐ[k] Polynomial k := by
  refine
    { toAlgHom := quotientByXToPolynomial (k := k)
      invFun := polynomialToQuotientByX (k := k)
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    simpa using congrArg (fun f : A ⧸ principalIdeal x →ₐ[k] A ⧸ principalIdeal x ↦ f q)
      (quotientByX_polynomial_left_inverse (k := k))
  · intro p
    simpa using congrArg (fun f : Polynomial k →ₐ[k] Polynomial k ↦ f p)
      (quotientByX_polynomial_right_inverse (k := k))

/-- Helper for Remark 15.60.4 (Warning): quotienting by `(y)` identifies the coordinate quotient
with the polynomial ring in the remaining variable. -/
private noncomputable theorem quotientByYAlgEquivPolynomial :
    A ⧸ principalIdeal y ≃ₐ[k] Polynomial k := by
  refine
    { toAlgHom := quotientByYToPolynomial (k := k)
      invFun := polynomialToQuotientByY (k := k)
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    simpa using congrArg (fun f : A ⧸ principalIdeal y →ₐ[k] A ⧸ principalIdeal y ↦ f q)
      (quotientByY_polynomial_left_inverse (k := k))
  · intro p
    simpa using congrArg (fun f : Polynomial k →ₐ[k] Polynomial k ↦ f p)
      (quotientByY_polynomial_right_inverse (k := k))

/-- Helper for Remark 15.60.4 (Warning): multiplication by `X` on `k[X]` is injective. -/
private theorem polynomial_eq_zero_of_mul_X_eq_zero {p : Polynomial k}
    (h : p * Polynomial.X = 0) :
    p = 0 := by
  -- Compare the coefficient of `X^(n + 1)` to recover every coefficient of `p`.
  ext n
  have hcoeff := congrArg (fun q : Polynomial k ↦ q.coeff (n + 1)) h
  simpa using hcoeff

/-- Helper for Remark 15.60.4 (Warning): in `A = k[x,y]/(xy)`, multiplication by `y` has kernel
exactly `(x)`. This packages the source syzygy `A/(x) ≃ (y)` in kernel form. -/
private theorem coordinate_mul_y_ker_eq_principalIdeal_x :
    LinearMap.ker (LinearMap.mulLeft A y) = principalIdeal x := by
  -- Route correction: instead of proving the kernel equality by ad hoc quotient calculations,
  -- transport to `k[X]`, where `X` is visibly a non-zero-divisor.
  ext a
  constructor
  · intro ha
    let π : A →+* A ⧸ principalIdeal x := Ideal.Quotient.mkₐ A (principalIdeal x)
    have hbar : π a * π y = 0 := by
      simpa [π, map_mul, mul_comm] using congrArg π ha
    have hpoly :
        (quotientByXAlgEquivPolynomial (k := k)) (π a) * Polynomial.X = 0 := by
      simpa [map_mul, quotientByXToPolynomial_map_y (k := k), mul_comm] using
        congrArg (quotientByXAlgEquivPolynomial (k := k)) hbar
    have hzero :
        (quotientByXAlgEquivPolynomial (k := k)) (π a) = 0 :=
      polynomial_eq_zero_of_mul_X_eq_zero (k := k) hpoly
    have : π a = 0 := (quotientByXAlgEquivPolynomial (k := k)).injective hzero
    exact (Ideal.Quotient.eq_zero_iff_mem).1 this
  · intro ha
    rw [principalIdeal] at ha
    rcases Ideal.mem_span_singleton.mp ha with ⟨b, rfl⟩
    -- Multiples of `x` are annihilated by `y` because `xy = 0` in the quotient ring.
    change y * (b * x) = 0
    calc
      y * (b * x) = b * (y * x) := by ring
      _ = 0 := by simp [Remark15604Warning.y_mul_x_eq_zero (k := k)]

/-- Helper for Remark 15.60.4 (Warning): in `A = k[x,y]/(xy)`, multiplication by `x` has kernel
exactly `(y)`. This is the symmetric source syzygy `A/(y) ≃ (x)`. -/
private theorem coordinate_mul_x_ker_eq_principalIdeal_y :
    LinearMap.ker (LinearMap.mulLeft A x) = principalIdeal y := by
  -- Transport the kernel computation to `k[X]`, where multiplication by `X` is injective.
  ext a
  constructor
  · intro ha
    let π : A →+* A ⧸ principalIdeal y := Ideal.Quotient.mkₐ A (principalIdeal y)
    have hbar : π a * π x = 0 := by
      simpa [π, map_mul, mul_comm] using congrArg π ha
    have hpoly :
        (quotientByYAlgEquivPolynomial (k := k)) (π a) * Polynomial.X = 0 := by
      simpa [map_mul, quotientByYToPolynomial_map_x (k := k), mul_comm] using
        congrArg (quotientByYAlgEquivPolynomial (k := k)) hbar
    have hzero :
        (quotientByYAlgEquivPolynomial (k := k)) (π a) = 0 :=
      polynomial_eq_zero_of_mul_X_eq_zero (k := k) hpoly
    have : π a = 0 := (quotientByYAlgEquivPolynomial (k := k)).injective hzero
    exact (Ideal.Quotient.eq_zero_iff_mem).1 this
  · intro ha
    rw [principalIdeal] at ha
    rcases Ideal.mem_span_singleton.mp ha with ⟨b, rfl⟩
    -- Multiples of `y` are annihilated by `x` because `xy = 0` in the quotient ring.
    change x * (b * y) = 0
    calc
      x * (b * y) = b * (x * y) := by ring
      _ = 0 := by simp [Remark15604Warning.x_mul_y_eq_zero (k := k)]

/-- Helper for Remark 15.60.4 (Warning): quotienting by `(x)` identifies `A / (x)` with the image
of multiplication by `y`. -/
private noncomputable theorem coordinate_quotient_by_x_equiv_range_mul_y :
    (A ⧸ principalIdeal x) ≃ₗ[A] LinearMap.range (LinearMap.mulLeft A y) :=
  (Submodule.quotEquivOfEq
      (principalIdeal x)
      (LinearMap.ker (LinearMap.mulLeft A y))
      (coordinate_mul_y_ker_eq_principalIdeal_x (k := k)).symm).trans
    ((LinearMap.mulLeft A y).quotKerEquivRange)

/-- Helper for Remark 15.60.4 (Warning): quotienting by `(y)` identifies `A / (y)` with the image
of multiplication by `x`. -/
private noncomputable theorem coordinate_quotient_by_y_equiv_range_mul_x :
    (A ⧸ principalIdeal y) ≃ₗ[A] LinearMap.range (LinearMap.mulLeft A x) :=
  (Submodule.quotEquivOfEq
      (principalIdeal y)
      (LinearMap.ker (LinearMap.mulLeft A x))
      (coordinate_mul_x_ker_eq_principalIdeal_y (k := k)).symm).trans
    ((LinearMap.mulLeft A x).quotKerEquivRange)

/-- Helper for Remark 15.60.4 (Warning): the two coordinate quotients are 2-periodic syzygies of
each other, so neither admits any finite projective-dimension bound. -/
private theorem coordinate_quotients_no_projective_dimension_bound :
    (∀ n : ℕ, ¬ HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ principalIdeal x)) n) ∧
      (∀ n : ℕ, ¬ HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ principalIdeal y)) n) := by
  -- Follow the source proof literally: descend alternately across the two short exact sequences.
  let P : ℕ → Prop := fun n =>
    ¬ HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ principalIdeal x)) n ∧
      ¬ HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ principalIdeal y)) n
  have hstep : ∀ n : ℕ, P n → P (n + 1) := by
    intro n hn
    rcases hn with ⟨hx, hy⟩
    constructor
    · intro hpd
      letI : Projective (ModuleCat.of A A) := by infer_instance
      have hA : HasProjectiveDimensionLE (ModuleCat.of A A) n := by infer_instance
      have hrange :
          HasProjectiveDimensionLE
            (ModuleCat.of A (LinearMap.range (LinearMap.mulLeft A x))) n := by
        exact CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLE_X₁
          (coordinate_range_shortExact_x (k := k))
          n
          hA
          hpd
      have hy' : HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ principalIdeal y)) n := by
        exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
          (M := ModuleCat.of A (LinearMap.range (LinearMap.mulLeft A x)))
          (N := ModuleCat.of A (A ⧸ principalIdeal y))
          ((coordinate_quotient_by_y_equiv_range_mul_x (k := k)).symm)
          n
      exact hy hy'
    · intro hpd
      letI : Projective (ModuleCat.of A A) := by infer_instance
      have hA : HasProjectiveDimensionLE (ModuleCat.of A A) n := by infer_instance
      have hrange :
          HasProjectiveDimensionLE
            (ModuleCat.of A (LinearMap.range (LinearMap.mulLeft A y))) n := by
        exact CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLE_X₁
          (coordinate_range_shortExact_y (k := k))
          n
          hA
          hpd
      have hx' : HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ principalIdeal x)) n := by
        exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
          (M := ModuleCat.of A (LinearMap.range (LinearMap.mulLeft A y)))
          (N := ModuleCat.of A (A ⧸ principalIdeal x))
          ((coordinate_quotient_by_x_equiv_range_mul_y (k := k)).symm)
          n
      exact hx hx'
  have hbase : P 0 := by
    constructor
    · intro hpd
      exact quotient_by_x_not_projective (k := k)
        ((projective_iff_hasProjectiveDimensionLE_zero _).2 hpd)
    · intro hpd
      exact quotient_by_y_not_projective (k := k)
        ((projective_iff_hasProjectiveDimensionLE_zero _).2 hpd)
  exact fun n ↦ (Nat.rec hbase hstep n)

/-- Helper for Remark 15.60.4 (Warning): the coordinate quotient `A / (x)` is not perfect. -/
private theorem quotient_by_x_not_perfect :
    ¬ (ModuleCat.of A (A ⧸ principalIdeal x)).IsPerfect := by
  -- Perfectness would first produce a finite projective-dimension bound, forbidden above.
  exact
    quotient_by_x_not_perfect_of_no_projective_dimension_bound
      (k := k)
      (coordinate_quotients_no_projective_dimension_bound (k := k)).1

/-- Helper for Remark 15.60.4 (Warning): the polynomial variable `X` is not contained in the
principal square ideal `(X^2)` of `k[X]`. -/
private theorem polynomial_X_not_mem_principalPowerIdeal_two :
    (Polynomial.X : Polynomial k) ∉ principalPowerIdeal (Polynomial.X : Polynomial k) 2 := by
  -- Compare the coefficient of `X` in any putative multiple of `X^2`.
  intro hX
  rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] at hX
  rcases Ideal.mem_span_singleton.mp hX with ⟨p, hp⟩
  have hcoeff := congrArg (fun q : Polynomial k ↦ q.coeff 1) hp
  simpa using hcoeff

/-- Helper for Remark 15.60.4 (Warning): the class of `x` is not contained in the square ideal
`(x)^2 ⊆ A`. -/
private theorem x_not_mem_principalPowerIdeal_two :
    x ∉ principalPowerIdeal x 2 := by
  -- Transport a hypothetical membership to `k[X]`, where it becomes `X ∈ (X^2)`.
  intro hx
  rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] at hx
  rcases Ideal.mem_span_singleton.mp hx with ⟨a, ha⟩
  have himage :
      (Polynomial.X : Polynomial k) ∈ principalPowerIdeal (Polynomial.X : Polynomial k) 2 := by
    rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow]
    refine Ideal.mem_span_singleton.mpr ⟨quotientToPolynomialX (k := k) a, ?_⟩
    -- Apply the specialization sending `x` to `X` and `y` to `0`.
    simpa [ha, quotientToPolynomialX_map_x (k := k), map_mul, map_pow]
  exact polynomial_X_not_mem_principalPowerIdeal_two (k := k) himage

/-- Helper for Remark 15.60.4 (Warning): the class of `y` is not contained in the square ideal
`(y)^2 ⊆ A`. -/
private theorem y_not_mem_principalPowerIdeal_two :
    y ∉ principalPowerIdeal y 2 := by
  -- Transport a hypothetical membership to `k[X]`, where it becomes `X ∈ (X^2)`.
  intro hy
  rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] at hy
  rcases Ideal.mem_span_singleton.mp hy with ⟨a, ha⟩
  have himage :
      (Polynomial.X : Polynomial k) ∈ principalPowerIdeal (Polynomial.X : Polynomial k) 2 := by
    rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow]
    refine Ideal.mem_span_singleton.mpr ⟨quotientToPolynomialY (k := k) a, ?_⟩
    -- Apply the specialization sending `x` to `0` and `y` to `X`.
    simpa [ha, quotientToPolynomialY_map_y (k := k), map_mul, map_pow]
  exact polynomial_X_not_mem_principalPowerIdeal_two (k := k) himage

/-- Helper for Remark 15.60.4 (Warning): the coordinate quotient `A / (x)` is not projective as an
`A`-module. -/
private theorem quotient_by_x_not_projective :
    ¬ Module.Projective A (A ⧸ principalIdeal x) := by
  intro hproj
  letI : Module.Projective A (A ⧸ principalIdeal x) := hproj
  let π : A →ₗ[A] (A ⧸ principalIdeal x) :=
    (Ideal.Quotient.mkₐ A (principalIdeal x)).toLinearMap
  let s : (A ⧸ principalIdeal x) →ₗ[A] A :=
    Classical.choose
      (Module.projective_lifting_property π LinearMap.id
        (Ideal.Quotient.mkₐ_surjective A (principalIdeal x)))
  have hs : π.comp s = LinearMap.id :=
    Classical.choose_spec
      (Module.projective_lifting_property π LinearMap.id
        (Ideal.Quotient.mkₐ_surjective A (principalIdeal x)))
  let a : A := s 1
  have hπa : π a = 1 := by
    -- The chosen lift is a section of the quotient map.
    change (π.comp s) 1 = 1
    simpa [a, hs]
  have hxa : x * a = 0 := by
    -- The class of `x` vanishes in `A/(x)`, so `x` annihilates the lifted generator.
    calc
      x * a = x • a := by simp [smul_eq_mul]
      _ = s (x • (1 : A ⧸ principalIdeal x)) := by
        simpa [a, smul_eq_mul] using (s.map_smul x (1 : A ⧸ principalIdeal x)).symm
      _ = s 0 := by
        congr 1
        change (Ideal.Quotient.mk (principalIdeal x) x) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_span_singleton_self x
      _ = 0 := by simp
  let e : A := 1 - a
  have he_mem : e ∈ principalIdeal x := by
    -- The difference `1 - a` lies in the kernel of the quotient map.
    have hπe : π e = 0 := by
      simpa [e, hπa]
    rw [Ideal.Quotient.eq_zero_iff_mem] at hπe
    exact hπe
  rcases Ideal.mem_span_singleton.mp (by simpa [principalIdeal] using he_mem) with ⟨b, hb⟩
  have hx_square : x ∈ principalPowerIdeal x 2 := by
    -- Since `x a = 0` and `e = 1 - a ∈ (x)`, we get `x = x e ∈ (x)^2`.
    rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow]
    refine Ideal.mem_span_singleton.mpr ⟨b, ?_⟩
    calc
      x = x * e := by
        simpa [e, sub_eq_add_neg, mul_add, hxa]
      _ = x * (b * x) := by rw [hb]
      _ = b * (x ^ 2) := by ring
  exact x_not_mem_principalPowerIdeal_two (k := k) hx_square

/-- Helper for Remark 15.60.4 (Warning): the coordinate quotient `A / (y)` is not projective as an
`A`-module. -/
private theorem quotient_by_y_not_projective :
    ¬ Module.Projective A (A ⧸ principalIdeal y) := by
  intro hproj
  letI : Module.Projective A (A ⧸ principalIdeal y) := hproj
  let π : A →ₗ[A] (A ⧸ principalIdeal y) :=
    (Ideal.Quotient.mkₐ A (principalIdeal y)).toLinearMap
  let s : (A ⧸ principalIdeal y) →ₗ[A] A :=
    Classical.choose
      (Module.projective_lifting_property π LinearMap.id
        (Ideal.Quotient.mkₐ_surjective A (principalIdeal y)))
  have hs : π.comp s = LinearMap.id :=
    Classical.choose_spec
      (Module.projective_lifting_property π LinearMap.id
        (Ideal.Quotient.mkₐ_surjective A (principalIdeal y)))
  let a : A := s 1
  have hπa : π a = 1 := by
    -- The chosen lift is a section of the quotient map.
    change (π.comp s) 1 = 1
    simpa [a, hs]
  have hya : y * a = 0 := by
    -- The class of `y` vanishes in `A/(y)`, so `y` annihilates the lifted generator.
    calc
      y * a = y • a := by simp [smul_eq_mul]
      _ = s (y • (1 : A ⧸ principalIdeal y)) := by
        simpa [a, smul_eq_mul] using (s.map_smul y (1 : A ⧸ principalIdeal y)).symm
      _ = s 0 := by
        congr 1
        change (Ideal.Quotient.mk (principalIdeal y) y) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_span_singleton_self y
      _ = 0 := by simp
  let e : A := 1 - a
  have he_mem : e ∈ principalIdeal y := by
    -- The difference `1 - a` lies in the kernel of the quotient map.
    have hπe : π e = 0 := by
      simpa [e, hπa]
    rw [Ideal.Quotient.eq_zero_iff_mem] at hπe
    exact hπe
  rcases Ideal.mem_span_singleton.mp (by simpa [principalIdeal] using he_mem) with ⟨b, hb⟩
  have hy_square : y ∈ principalPowerIdeal y 2 := by
    -- Since `y a = 0` and `e = 1 - a ∈ (y)`, we get `y = y e ∈ (y)^2`.
    rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow]
    refine Ideal.mem_span_singleton.mpr ⟨b, ?_⟩
    calc
      y = y * e := by
        simpa [e, sub_eq_add_neg, mul_add, hya]
      _ = y * (b * y) := by rw [hb]
      _ = b * (y ^ 2) := by ring
  exact y_not_mem_principalPowerIdeal_two (k := k) hy_square

/-- Helper for Remark 15.60.4 (Warning): a perfect `A`-module has some finite projective-dimension
bound. This isolates the perfectness-to-projective-dimension bridge before the warning-specific
alternating syzygy argument is applied. -/
private theorem exists_projectiveDimensionBound_of_isPerfect
    (M : ModuleCat A) (hM : M.IsPerfect) :
    ∃ d : ℕ, HasProjectiveDimensionLE M d := by
  -- Route correction: separate the generic perfectness bridge from the warning-specific quotient
  -- syzygy computation, so the remaining blocker is only the alternating short-exact descent.
  rcases
      (ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms M).1 hM with
    ⟨d, hd⟩
  have hfinite : HasFiniteProjectiveResolutionLengthLE M d := by
    cases d with
    | zero =>
        -- In degree `0`, forgetting the finite-generation clause leaves projectivity of `M`.
        simpa [HasFiniteProjectiveResolutionLengthLE,
          ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms] using hd.1
    | succ n =>
        -- For positive length, forget the finite-projective structure on each term.
        rcases hd with ⟨P, δ, π, hπ, hδπ, hδ, hinj⟩
        refine ⟨fun i ↦ (P i).obj, ?_, fun i ↦ (δ i).hom, π, hπ, hδπ, hδ, hinj⟩
        intro i
        let _ : Module.Projective A (P i).obj := (P i).property.2
        infer_instance
  -- Translate the bounded projective resolution into the owner notion `HasProjectiveDimensionLE`.
  exact ⟨d, (projectiveDimensionLE_tfae_resolution_conditions (M := M) d).out 1 0 hfinite⟩

/-- Helper for Remark 15.60.4 (Warning): if the coordinate quotient `A / (x)` were perfect, then
it would satisfy some finite projective-dimension bound. -/
private theorem quotient_by_x_hasProjectiveDimensionLE_of_isPerfect
    (hN : (ModuleCat.of A (A ⧸ principalIdeal x)).IsPerfect) :
    ∃ d : ℕ, HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ principalIdeal x)) d := by
  -- Specialize the generic perfectness bridge to the quotient module used in the warning.
  exact
    exists_projectiveDimensionBound_of_isPerfect
      (k := k)
      (M := ModuleCat.of A (A ⧸ principalIdeal x))
      hN

/-- Helper for Remark 15.60.4 (Warning): once the source-faithful alternating syzygy argument
shows that `A / (x)` has no finite projective-dimension bound, perfectness is impossible. -/
private theorem quotient_by_x_not_perfect_of_no_projective_dimension_bound
    (hpd : ∀ d : ℕ, ¬ HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ principalIdeal x)) d) :
    ¬ (ModuleCat.of A (A ⧸ principalIdeal x)).IsPerfect := by
  -- Any perfectness witness would first produce a finite projective-dimension bound.
  intro hperfect
  rcases quotient_by_x_hasProjectiveDimensionLE_of_isPerfect (k := k) hperfect with ⟨d, hd⟩
  exact hpd d hd

/-- Helper for Remark 15.60.4 (Warning): the canonical stage-`0` one-variable Koszul owner is
perfect. Once the stage is normalized to the explicit two-term complex `A \xrightarrow{x} A`,
perfectness is transported from that bounded finite-projective model. -/
private theorem stage0_koszul_owner_isPerfect :
    ((derivedCompletionKoszulPowersDerivedInverseSystem (fun _ : Fin 1 ↦ x)).obj
      (op 0)).IsPerfect := by
  let P : ObjectProperty DModA := DerivedCategory.IsPerfect
  have hmodel : P (DerivedCategory.Q.obj (stage0KoszulModel (k := k))) :=
    stage0_koszul_model_isPerfect (k := k)
  rcases stage0_koszul_owner_iso_mappingCone_x (k := k) with ⟨eModel⟩
  -- Transport perfectness back along the stage-`0` normalization isomorphism.
  exact P.prop_of_iso eModel hmodel

/- Remark 15.60.4 (Warning): for any nontrivial commutative ring `k`, with `R = k[x,y]`,
`A = R/(xy)`, `N = A/(x)`, and `N' = A`, the two change-of-rings derived tensor products
`((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗_R^{\mathbf L} N'`
and
`((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') ⊗_R^{\mathbf L} N`
are not isomorphic in `D(A)`.
-/
theorem Remark15604Warning.counterexample :
    ¬ IsIsomorphic
      (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗[R]^L[A] N')
      (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') ⊗[R]^L[A] N) :=
  by
    -- Route correction: the module-theoretic periodic obstruction is already closed, so the
    -- remaining argument only transports perfectness through the two derived tensor computations.
    rintro ⟨e⟩
    let P : ObjectProperty DModA := DerivedCategory.IsPerfect
    have hstage0 : P (((derivedCompletionKoszulPowersDerivedInverseSystem
        (fun _ : Fin 1 ↦ x)).obj (op 0))) :=
      stage0_koszul_owner_isPerfect (k := k)
    have hfirst :
        P ((((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗[R]^L[A]
          N')) := by
      rcases Remark15604Warning.nTensorNPrime_iso_koszulStage0 (k := k) with ⟨eTensor⟩
      -- The first source-faithful tensor computation identifies the object with the stage-`0`
      -- Koszul owner, which is perfect.
      exact P.prop_of_iso eTensor hstage0
    have hsecond :
        P ((((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') ⊗[R]^L[A]
          N)) := by
      -- Transport perfectness across the hypothetical isomorphism from the first tensor object.
      exact P.prop_of_iso e hfirst
    have hsplit : P (N⟦(1 : ℤ)⟧ ⊞ N) := by
      rcases Remark15604Warning.nPrimeTensorN_iso_shiftBiproduct (k := k) with ⟨eSplit⟩
      -- The second source-faithful tensor computation identifies the object with `N[1] ⊞ N`.
      exact P.prop_of_iso eSplit hsecond
    have hNperfect : N.IsPerfect := (isPerfect_summands_of_biprod (N⟦(1 : ℤ)⟧) N hsplit).2
    -- The second summand is exactly the coordinate quotient `A / (x)`, contradicting the periodic
    -- non-perfectness obstruction established above.
    exact quotient_by_x_not_perfect (k := k) <| by
      simpa [ModuleCat.IsPerfect, Remark15604Warning.N] using hNperfect

end

end

end CategoryTheory
