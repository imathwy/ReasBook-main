import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_75_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_8
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_9
import StacksProject_2024.stacks_project.Chap15.Lemma_15_67_10
import StacksProject_2024.stacks_project.Chap15.Lemma_15_75_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_75_3

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open ObjectProperty.IsStableUnderRetracts
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "single₀A" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)
local notation "single₀B" => DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)

/-- Helper for Lemma 15.75.8: the identity map preserves addition on the restricted regular
`B`-module viewed as an `A`-module. -/
private theorem restrictScalars_regular_refl_map_add
    (x y : ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))) :
    (Equiv.refl B).toFun (x + y) = (Equiv.refl B).toFun x + (Equiv.refl B).toFun y :=
  rfl

/-- Helper for Lemma 15.75.8: the identity map preserves the `A`-scalar action on the restricted
regular `B`-module. -/
private theorem restrictScalars_regular_refl_map_smul
    (a : A)
    (x : ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))) :
    (Equiv.refl B).toFun (a • x) = (RingHom.id A) a • (Equiv.refl B).toFun x := by
  simpa [Algebra.smul_def]

/-- Helper for Lemma 15.75.8: the restricted regular `B`-module is linearly equivalent to the
canonical `A`-module structure on `B`. -/
private noncomputable def restrictScalars_regular_linearEquiv :
    (((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) : ModuleCat A) ≃ₗ[A]
      (ModuleCat.of A B : ModuleCat A) :=
  { toEquiv := Equiv.refl B
    map_add' := restrictScalars_regular_refl_map_add (A := A) (B := B)
    map_smul' := restrictScalars_regular_refl_map_smul (A := A) (B := B) }

/-- Helper for Lemma 15.75.8: restricting the regular `B`-module to `A` gives the usual
`A`-module structure on `B`. -/
private noncomputable def restrictScalars_regular_hom :
    (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ⟶ ModuleCat.of A B :=
  (restrictScalars_regular_linearEquiv (A := A) (B := B)).toLinearMap

/-- Helper for Lemma 15.75.8: the inverse map of the canonical restricted-regular-module
identification. -/
private noncomputable def restrictScalars_regular_inv :
    ModuleCat.of A B ⟶ (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) :=
  (restrictScalars_regular_linearEquiv (A := A) (B := B)).symm.toLinearMap

/-- Helper for Lemma 15.75.8: the canonical map from the restricted regular `B`-module to the
underlying `A`-module on `B` is inverse to its explicit inverse. -/
private theorem restrictScalars_regular_hom_inv_id :
    restrictScalars_regular_hom (A := A) (B := B) ≫
      restrictScalars_regular_inv (A := A) (B := B) =
        𝟙 (ModuleCat.of A B) := by
  ext x
  rfl

/-- Helper for Lemma 15.75.8: the explicit inverse really inverts the canonical restricted
regular-module map. -/
private theorem restrictScalars_regular_inv_hom_id :
    restrictScalars_regular_inv (A := A) (B := B) ≫
      restrictScalars_regular_hom (A := A) (B := B) =
        𝟙 ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) := by
  ext x
  rfl

/-- Helper for Lemma 15.75.8: restricting the regular `B`-module to `A` gives the usual
`A`-module structure on `B`. -/
private noncomputable def restrictScalars_regular_iso :
    (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ≅ ModuleCat.of A B :=
  { hom := restrictScalars_regular_hom (A := A) (B := B)
    inv := restrictScalars_regular_inv (A := A) (B := B)
    hom_inv_id := restrictScalars_regular_hom_inv_id (A := A) (B := B)
    inv_hom_id := restrictScalars_regular_inv_hom_id (A := A) (B := B) }

/-- Helper for Lemma 15.75.8: derived restriction of scalars commutes with the degree-zero copy
of the regular `B`-module. -/
private noncomputable def restrictScalars_single0_regular_iso :
    ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
      (single₀B.obj (ModuleCat.of B B))) ≅
      single₀A.obj ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
  (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat B) (0 : ℤ)).app
        (ModuleCat.of B B))) ≪≫
    (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B B)) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.restrictScalars (algebraMap A B))
          (0 : ℤ)).app (ModuleCat.of B B)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))).symm

/-- Helper for Lemma 15.75.8: the degree-zero regular `B`-module is the tensor unit in `D(B)`. -/
private noncomputable def regular_single0_tensorUnit_iso :
    single₀B.obj (ModuleCat.of B B) ≅ 𝟙_ DModB :=
  ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat B) (0 : ℤ)).app (ModuleCat.of B B)) ≪≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat B)).app
      ((CochainComplex.singleFunctor (ModuleCat B) (0 : ℤ)).obj (ModuleCat.of B B))).symm

/-- Helper for Lemma 15.75.8: tensoring with the degree-zero regular `B`-module is canonically
the identity on `D(B)`. -/
private noncomputable def tensor_regular_single0_iso (K : DModB) :
    K ⊗[B]^L (single₀B.obj (ModuleCat.of B B)) ≅ K :=
  (derivedCategory_tensorObj_iso_derivedTensorProduct
      K (single₀B.obj (ModuleCat.of B B))).symm ≪≫
    whiskerLeftIso K (regular_single0_tensorUnit_iso (B := B)) ≪≫
      ρ_ K

/-- Helper for Lemma 15.75.8: after restricting scalars to `A`, tensoring with `B[0]` still
collapses to the original restricted complex. -/
private noncomputable def restrictScalars_tensor_regular_single0_iso (K : DModB) :
    ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
      (K ⊗[B]^L (single₀B.obj (ModuleCat.of B B)))) ≅
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K) :=
  ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).mapIso
    (tensor_regular_single0_iso (B := B) K)

/-- Helper for Lemma 15.75.8: tor-amplitude in a fixed interval is invariant under isomorphism
after restriction of scalars to `A`. -/
private theorem hasTorAmplitudeIn_of_iso
    {a b : ℤ} {K L : DModA} (e : K ≅ L) :
    HasTorAmplitudeIn K a b ↔ HasTorAmplitudeIn L a b := by
  constructor
  · intro h M i hi
    -- Proof comment: transport the tested homology object along the tensor image of `e`.
    exact
      (h M i hi).of_iso
        ((DerivedCategory.homologyFunctor (ModuleCat A) i).mapIso
          ((derivedTensorProduct (single₀A.obj M)).mapIso e.symm))
  · intro h M i hi
    -- Proof comment: use the inverse tensor transport for the converse direction.
    exact
      (h M i hi).of_iso
        ((DerivedCategory.homologyFunctor (ModuleCat A) i).mapIso
          ((derivedTensorProduct (single₀A.obj M)).mapIso e))

/-- Helper for Lemma 15.75.8: after restricting scalars to `A`, a free rank-`n + 1` `B`-module
splits as one copy of the restricted regular module plus a free rank-`n` summand. -/
private noncomputable def restrictScalars_finSuccArrowLinearEquiv (n : ℕ) :
    (Fin (n + 1) → B) ≃ₗ[A] (B × (Fin n → B)) where
  toEquiv := (Fin.consEquiv fun _ : Fin (n + 1) => B).symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Helper for Lemma 15.75.8: if the restricted regular `B`-module is pseudo-coherent over `A`,
then the same holds for every finite free `B`-module after restriction of scalars. -/
private theorem restrictScalars_finite_free_single_isPseudoCoherent
    (hBpc : ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)).IsPseudoCoherent) :
    ∀ n : ℕ,
      ((single₀A).obj
        ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B (Fin n → B)))).IsPseudoCoherent
  | 0 => by
      let Q : ObjectProperty DModA := fun X ↦ X.IsPseudoCoherent
      have hzero :
          ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B (Fin 0 → B))) ≅
            ModuleCat.of A PUnit :=
        (LinearEquiv.ofSubsingleton _ _).toModuleIso
      have hsingleZeroObj : IsZero ((single₀A).obj (ModuleCat.of A PUnit)) := by
        let hzeroModule : IsZero (ModuleCat.of A PUnit) :=
          ModuleCat.isZero_of_subsingleton (ModuleCat.of A PUnit)
        exact (single₀A).map_isZero hzeroModule
      have hQpunit : Q ((single₀A).obj (ModuleCat.of A PUnit)) := by
        exact ObjectProperty.prop_of_isZero (P := Q) hsingleZeroObj
      exact Q.prop_of_iso ((single₀A).mapIso hzero).symm hQpunit
  | n + 1 => by
      let Q : ObjectProperty DModA := fun X ↦ X.IsPseudoCoherent
      letI :
          PreservesBinaryBiproducts
            (DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)) :=
        CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts
          (DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ))
      let eModule :
          ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B (Fin (n + 1) → B))) ≅
            ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ⊞
              ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B (Fin n → B))) :=
        (restrictScalars_finSuccArrowLinearEquiv (A := A) (B := B) n).toModuleIso ≪≫
          (ModuleCat.biprodIsoProd
            ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))
            ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B (Fin n → B)))).symm
      let eSingle :
          ((single₀A).obj
            ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B (Fin (n + 1) → B)))) ≅
              (((single₀A).obj
                ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))) ⊞
                ((single₀A).obj
                  ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B (Fin n → B))))) :=
        ((single₀A).mapIso eModule) ≪≫
          (single₀A).mapBiprod
            ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))
            ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B (Fin n → B)))
      have hbiprod :
          Q ((((single₀A).obj
              ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))) ⊞
              ((single₀A).obj
                ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B (Fin n → B)))))) := by
        exact Q.prop_biprod hBpc (restrictScalars_finite_free_single_isPseudoCoherent hBpc n)
      exact Q.prop_of_iso eSingle.symm hbiprod

/-- Helper for Lemma 15.75.8: if the restricted regular `B`-module is pseudo-coherent over `A`,
then the same holds for every finite projective `B`-module after restriction of scalars. -/
private theorem restrictScalars_finite_projective_single_isPseudoCoherent
    (hBpc : ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)).IsPseudoCoherent)
    (P : FiniteProjectiveModuleCat B) :
    ((single₀A).obj ((ModuleCat.restrictScalars (algebraMap A B)).obj P.obj)).IsPseudoCoherent := by
  let Q : ObjectProperty DModA := fun X ↦ X.IsPseudoCoherent
  let _ : Module.Finite B P.obj := P.property.1
  let _ : Module.Projective B P.obj := P.property.2
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' B P.obj
  let πCat : ModuleCat.of B (Fin n → B) ⟶ P.obj := ModuleCat.ofHom π
  letI : Epi πCat := (ModuleCat.epi_iff_surjective _).2 hπ
  letI : Projective P.obj := by
    infer_instance
  let σCat : P.obj ⟶ ModuleCat.of B (Fin n → B) :=
    Projective.factorThru (𝟙 P.obj) πCat
  have hsplit : σCat ≫ πCat = 𝟙 P.obj := by
    exact Projective.factorThru_comp (𝟙 P.obj) πCat
  let r : Retract P.obj (ModuleCat.of B (Fin n → B)) := ⟨σCat, πCat, hsplit⟩
  let resSingle : ModuleCat B ⥤ DModA :=
    ModuleCat.restrictScalars (algebraMap A B) ⋙ single₀A
  have hfree :
      Q (resSingle.obj (ModuleCat.of B (Fin n → B))) :=
    restrictScalars_finite_free_single_isPseudoCoherent (A := A) (B := B) hBpc n
  exact Q.prop_of_retract (r.map resSingle) hfree

/-- Helper for Lemma 15.75.8: restriction of scalars lowers the left tor-amplitude bound by the
tor-dimension bound of the regular `B`-module over `A`. -/
private theorem hasTorAmplitudeIn_restrictScalars_of_moduleHasTorDimensionLE_local
    {a b : ℤ} {n : ℕ}
    (K : DModB)
    (hB : ModuleHasTorDimensionLE (ModuleCat.of A B) n)
    (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeIn
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
      (a - (n : ℤ)) b := by
  have hRegular :
      HasTorAmplitudeIn
        (single₀A.obj ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)))
        (-(n : ℤ)) 0 := by
    -- Proof comment: identify the restricted regular module with the canonical `A`-module `B`.
    exact
      (hasTorAmplitudeIn_of_iso (A := A)
        ((single₀A).mapIso (restrictScalars_regular_iso (A := A) (B := B)))).2 <| by
        simpa [ModuleHasTorDimensionLE] using hB
  have hRestrictedRegular :
      HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj
          (single₀B.obj (ModuleCat.of B B)))
        (-(n : ℤ)) 0 := by
    -- Proof comment: align the restricted `B[0]` object with the canonical degree-zero
    -- `A`-object of the underlying module `B`.
    exact
      (hasTorAmplitudeIn_of_iso (A := A)
        (restrictScalars_single0_regular_iso (A := A) (B := B))).2 hRegular
  have hTensor :
      HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj
          (K ⊗[B]^L (single₀B.obj (ModuleCat.of B B))))
        (a - (n : ℤ)) b := by
    -- Proof comment: specialize the base-change tensor estimate to the regular object `B[0]`.
    simpa [sub_eq_add_neg] using
      (hasTorAmplitudeIn_restrictScalars_derivedTensorProduct
        (A := A) (B := B) (a := a) (b := b) (c := -(n : ℤ)) (d := (0 : ℤ))
        K (single₀B.obj (ModuleCat.of B B)) hK hRestrictedRegular)
  -- Proof comment: replace `K ⊗^L_B B[0]` by `K` using the restricted right-unit comparison.
  exact
    (hasTorAmplitudeIn_of_iso (A := A)
      (restrictScalars_tensor_regular_single0_iso (A := A) (B := B) K)).1 hTensor

/- Domain-style sampling for Lemma 15.75.8:
- primary domain: perfect objects in derived categories under restriction of scalars along the
  algebra map `A → B`;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `ModuleCat.IsPerfect`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`,
  `isPseudoCoherent_iff_restrictScalars`,
  `hasTorAmplitudeIn_restrictScalars_of_moduleHasTorDimensionLE`;
- best owner abstraction: this theorem is a `source-facing` restriction-of-scalars bridge for
  perfectness, while the actual restriction construction is owned canonically by the exact derived
  functor `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`; the assumption that
  `B` is perfect as an `A`-module is kept as the source-faithful hypothesis rather than being
  replaced by the later ring-map owner `RingHom.IsPerfectRingMap`, which lives at a different
  layer;
- primitive vs. derived:
  primitive data are the derived `B`-complex `K`, the perfectness hypothesis on the `A`-module
  `B`, and the perfectness hypothesis on `K`;
  derived API is the perfectness statement for the restricted object
  `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)`;
- source/core/bridge triage:
  `source-facing`: `isPerfect_restrictScalars_of_module_isPerfect`;
  `core/canonical`: `K.IsPerfect`, `(ModuleCat.of A B).IsPerfect`, and the functor
    `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
  `bridge/view`: the restriction-of-scalars image
    `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)`.
-/

-- Proof sketch: apply Lemma `15.75.2` to the perfect `A`-module `B` and to the perfect
-- `B`-complex `K` to obtain pseudo-coherence and finite tor dimension. Use
-- `isPseudoCoherent_iff_restrictScalars` for the pseudo-coherent part and
-- `hasTorAmplitudeIn_restrictScalars_of_moduleHasTorDimensionLE` for a finite tor-amplitude
-- interval after restriction of scalars. Then reassemble perfection with Lemma `15.75.2`.
/-- Lemma 15.75.8: if `A → B` is a ring map, `B` is perfect as an `A`-module, and `K^•` is
perfect over `B`, then `K^•` is perfect over `A` after restriction of scalars. -/
theorem isPerfect_restrictScalars_of_module_isPerfect
    (K : DModB) (hB : (ModuleCat.of A B).IsPerfect) (hK : K.IsPerfect) :
    (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K : DModA)).IsPerfect := by
  let KA : DModA := ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K : DModA)
  have hBdecomp :
      (ModuleCat.of A B).IsPseudoCoherent ∧ ModuleHasFiniteTorDimension (ModuleCat.of A B) :=
    (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension (ModuleCat.of A B)).1 hB
  have hBpc : ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)).IsPseudoCoherent := by
    -- Proof comment: perfectness of `B` over `A` supplies the pseudo-coherence hypothesis needed
    -- for all restricted finite-projective `B`-modules.
    simpa using hBdecomp.1
  have hKdecomp : K.IsPseudoCoherent ∧ HasFiniteTorDimension K :=
    (CategoryTheory.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension (R := B) K).1 hK
  have hKApc : KA.IsPseudoCoherent := by
    rcases hK with ⟨L, e, hL⟩
    let L' : CochainComplex (ModuleCat A) ℤ :=
      ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
    rcases hL.bounded with ⟨aL, bL, hLGE, hLLE⟩
    have hL'minus : CochainComplex.minus (ModuleCat A) L' := by
      refine (CochainComplex.minus_iff (ModuleCat A) L').2 ?_
      exact ⟨bL, by simpa [L'] using hLLE⟩
    have hL'term :
        ∀ i : ℤ, (L'.X i).IsPseudoCoherent := by
      intro i
      let P : FiniteProjectiveModuleCat B := ⟨L.X i, ⟨hL.finite i, hL.projective i⟩⟩
      have hSingle :
          ((single₀A).obj ((ModuleCat.restrictScalars (algebraMap A B)).obj P.obj)).IsPseudoCoherent :=
        restrictScalars_finite_projective_single_isPseudoCoherent (A := A) (B := B) hBpc P
      simpa [ModuleCat.IsPseudoCoherent, L', P] using hSingle
    have hL'pc : L'.IsPseudoCoherent :=
      CochainComplex.isPseudoCoherent_of_boundedAbove_of_termwise L' hL'minus hL'term
    let eRes :
        DerivedCategory.Q.obj L' ≅ KA :=
      (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategoryFactors.app L).symm) ≪≫
        (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).mapIso e.symm)
    exact isPseudoCoherent_of_iso (R := A) eRes hL'pc
  rcases ModuleCat.exists_moduleHasTorDimensionLE_of_isPerfect (ModuleCat.of A B) hB with ⟨d, hd⟩
  rcases hKdecomp.2 with ⟨a, b, hKab⟩
  have hKAamp : HasTorAmplitudeIn KA (a - (d : ℤ)) b :=
    hasTorAmplitudeIn_restrictScalars_of_moduleHasTorDimensionLE_local
      (A := A) (B := B) (a := a) (b := b) (n := d) K hd hKab
  -- Proof comment: recombine the descended pseudo-coherence and finite tor-amplitude bounds
  -- using the perfectness characterization from Lemma `15.75.2`.
  exact
    (CategoryTheory.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension (R := A) KA).2
      ⟨hKApc, hKAamp.hasFiniteTorDimension⟩

end

end CategoryTheory
