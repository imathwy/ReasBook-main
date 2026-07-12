import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Lemma_13_37_2
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.«15_74_0_2»
import StacksProject_2024.Chap15.Proposition_15_79_3

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite

universe u w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/-
Domain-style sampling for Lemma 15.127.3:
- primary domain: rigid duality for perfect objects in the monoidal derived category `D(R)`;
- sampled owner declarations:
  `ExactPairing`,
  `HasLeftDual`,
  `derivedDualExactPairing`,
  `leftDualIso`,
  `DerivedCategory.IsPerfect`;
- best owner abstraction:
  `source-facing`: the existence theorem that `M` admits a duality datum exactly when `M` is
    perfect, together with the identification of any chosen dual object with the canonical derived
    dual `Mᵛ⟮H⟯ = R\mathrm{Hom}_R(M, R[0])`;
  `core/canonical`: an arbitrary exact pairing `ExactPairing N M` and the chapter owner
    `DerivedCategory.IsPerfect`;
  `bridge/view`: the canonical pairing `derivedDualExactPairing` attached to a perfect object and
    the uniqueness isomorphism `leftDualIso` comparing any other left dual with it.

Primitive data are only the chosen derived-internal-Hom package `H`, the object `M`, and an
arbitrary exact pairing `ExactPairing N M`. The canonical dual `Mᵛ⟮H⟯` and the comparison from a
chosen dual object are derived API, so this file should recall `derivedDualExactPairing` for the
forward half, state the converse for arbitrary dual data, and keep the uniqueness isomorphism only
as a bridge to the canonical derived dual.
-/

-- Proof sketch: the forward implication is the canonical perfect-dual construction recalled from
-- the derived dual API. For the converse, the current file state closes through the compactness
-- characterization of perfect objects: an exact pairing gives a natural comparison
-- `Hom(M, -) ≅ Hom(𝟙, N ⊗ -)`, the left tensor functor preserves discrete coproducts, and the
-- tensor unit is compact because it is represented by `R[0]`.
--
-- Route correction: the earlier chain-level retract helpers remain available below, but the final
-- closing argument now follows the stabilized compactness route rather than reopening the old
-- tensor-braiding detour.
/-- Helper for Lemma 15.127.3: if `N` is a left dual of `M`, then tensoring on the left by `N`
preserves discrete coproducts because braiding identifies it with the left adjoint
`tensorRight N`. -/
private theorem tensorLeft_preserves_discrete_coproducts_of_exactPairing
    {M N : DMod} [ExactPairing N M] (I : Type*) :
    PreservesColimitsOfShape (Discrete I) (tensorLeft N) := by
  -- Proof comment: `tensorRight N` is left adjoint to `tensorRight M`, and braiding transports
  -- that coproduct-preservation statement to `tensorLeft N`.
  letI : (tensorRight N).IsLeftAdjoint := (tensorRightAdjunction N M).isLeftAdjoint
  letI : PreservesColimitsOfShape (Discrete I) (tensorRight N) := by
    infer_instance
  exact preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N).symm

/-- Helper for Lemma 15.127.3: precomposing with the right unitor inverse recovers the original
map out of `M`. -/
private theorem right_unitor_source_hom_left_inv
    {M X : DMod}
    (f : M ⟶ X) :
    (ρ_ M).inv ≫ (ρ_ M).hom ≫ f = f := by
  -- Proof comment: cancel the right-unitor isomorphism before reading the remaining composite.
  simp

/-- Helper for Lemma 15.127.3: precomposing with the right unitor and then its inverse recovers
the original map out of `M ⊗ 𝟙`. -/
private theorem right_unitor_source_hom_right_inv
    {M X : DMod}
    (f : M ⊗ 𝟙_ DMod ⟶ X) :
    (ρ_ M).hom ≫ (ρ_ M).inv ≫ f = f := by
  -- Proof comment: cancel the inverse right-unitor pair on the source side.
  simp

/-- Helper for Lemma 15.127.3: precomposition by the right unitor is additive on Hom groups. -/
private theorem right_unitor_source_hom_map_add
    {M X : DMod}
    (f g : M ⟶ X) :
    (ρ_ M).hom ≫ (f + g) = (ρ_ M).hom ≫ f + (ρ_ M).hom ≫ g := by
  -- Proof comment: composition in the preadditive Hom group distributes over addition.
  simp [Preadditive.comp_add]

/-- Helper for Lemma 15.127.3: the right unitor identifies `Hom(M, X)` with
`Hom(M ⊗ 𝟙, X)` additively. -/
private noncomputable def right_unitor_source_hom_add_equiv
    (M X : DMod) :
    (M ⟶ X) ≃+ (M ⊗ 𝟙_ DMod ⟶ X) :=
  { toFun := fun f ↦ (ρ_ M).hom ≫ f
    invFun := fun g ↦ (ρ_ M).inv ≫ g
    left_inv := right_unitor_source_hom_left_inv
    right_inv := right_unitor_source_hom_right_inv
    map_add' := right_unitor_source_hom_map_add }

/-- Helper for Lemma 15.127.3: after transporting across the right unitor, the exact pairing
gives the additive Hom-group bijection `Hom(M, X) ≃+ Hom(𝟙, N ⊗ X)`. -/
private noncomputable def exactPairing_hom_add_equiv
    {M N X : DMod} [ExactPairing N M] :
    (M ⟶ X) ≃+ (𝟙_ DMod ⟶ N ⊗ X) :=
  (right_unitor_source_hom_add_equiv M X).trans
    (tensorLeftHomEquiv (𝟙_ DMod) N M X)

/-- Helper for Lemma 15.127.3: after transporting across the right unitor, the exact pairing
gives the ordinary Hom-set bijection `Hom(M, X) ≃ Hom(𝟙, N ⊗ X)`. -/
private noncomputable def exactPairing_hom_equiv
    {M N X : DMod} [ExactPairing N M] :
    (M ⟶ X) ≃ (𝟙_ DMod ⟶ N ⊗ X) :=
  (exactPairing_hom_add_equiv (M := M) (N := N) (X := X)).toEquiv

/-- Helper for Lemma 15.127.3: the Hom-set equivalence is natural in the target variable. -/
private theorem exactPairing_hom_equiv_naturality
    {M N X Y : DMod} [ExactPairing N M]
    (g : M ⟶ X)
    (f : X ⟶ Y) :
    exactPairing_hom_equiv (M := M) (N := N) (X := Y) (g ≫ f) =
      exactPairing_hom_equiv (M := M) (N := N) (X := X) g ≫ N ◁ f := by
  -- Proof comment: after undoing the source right-unitor transport, this is exactly the recalled
  -- target-variable naturality of `tensorLeftHomEquiv`.
  simpa [exactPairing_hom_equiv, right_unitor_source_hom_add_equiv]
    using
      (tensorLeftHomEquiv_naturality
        (X := 𝟙_ DMod) (Y := N) (Y' := M)
        (f := (ρ_ M).hom ≫ g) f)

/-- Helper for Lemma 15.127.3: an exact pairing upgrades the pointwise Hom-set bijection to a
natural isomorphism of represented Type-valued functors. -/
private noncomputable def exactPairing_coyoneda_iso
    {M N : DMod} [ExactPairing N M] :
    coyoneda.obj (op M) ≅ tensorLeft N ⋙ coyoneda.obj (op (𝟙_ DMod)) :=
  NatIso.ofComponents
    (fun X ↦
      (exactPairing_hom_equiv (M := M) (N := N) (X := X)).toIso)
    (fun {X Y} f ↦ by
      -- Proof comment: naturality is exactly the target-variable naturality of
      -- `tensorLeftHomEquiv`, after reassociating the right-unitor insertion.
      funext g
      exact exactPairing_hom_equiv_naturality (M := M) (N := N) g f)

/-- Helper for Lemma 15.127.3: the degree-zero single complex on the free rank-one module is a
bounded finite-projective complex. -/
private theorem single_zero_ring_complex_isBoundedFiniteProjective :
    CochainComplex.IsBoundedFiniteProjective
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj (ModuleCat.of R R)) := by
  -- Proof comment: the single complex is supported in degree `0`, so every off-zero term is the
  -- zero module while the degree-zero term is the free rank-one module `R`.
  refine ⟨⟨0, 0, ?_, ?_⟩, ?_, ?_⟩
  · simpa using
      (inferInstance :
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
          (ModuleCat.of R R)).IsStrictlyGE (0 : ℤ))
  · simpa using
      (inferInstance :
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
          (ModuleCat.of R R)).IsStrictlyLE (0 : ℤ))
  · intro i
    by_cases hi : i = 0
    · subst hi
      simpa using
        (Module.Finite.equiv
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℤ) (0 : ℤ) (ModuleCat.of R R)).toLinearEquiv.symm
          (inferInstance : Module.Finite R (ModuleCat.of R R)))
    · let hzero :
        CategoryTheory.Limits.IsZero
          (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
            (ModuleCat.of R R)).X i) :=
        HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) (0 : ℤ) (ModuleCat.of R R) i hi
      simpa using
        (Module.Finite.equiv hzero.isoZero.toLinearEquiv.symm
          (by infer_instance : Module.Finite R (0 : ModuleCat R)))
  · intro i
    by_cases hi : i = 0
    · subst hi
      simpa using
        (Module.Projective.of_equiv
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℤ) (0 : ℤ) (ModuleCat.of R R)).toLinearEquiv.symm
          (inferInstance : Module.Projective R (ModuleCat.of R R)))
    · let hzero :
        CategoryTheory.Limits.IsZero
          (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
            (ModuleCat.of R R)).X i) :=
        HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) (0 : ℤ) (ModuleCat.of R R) i hi
      simpa using
        (Module.Projective.of_equiv hzero.isoZero.toLinearEquiv.symm
          (by infer_instance : Module.Projective R (0 : ModuleCat R)))

/-- Helper for Lemma 15.127.3: the tensor-unit model `R[0]` is perfect by its literal bounded
finite-projective representative. -/
private theorem ring_single_isPerfect_local :
    DerivedCategory.IsPerfect (ringSingle : DMod) := by
  -- Proof comment: witness perfectness by the degree-zero single complex that defines
  -- `ringSingle`.
  refine ⟨(CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj (ModuleCat.of R R), ?_, ?_⟩
  · simpa [ringSingle] using
      (Iso.refl
        ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj
          (ModuleCat.of R R)))
  · simpa using single_zero_ring_complex_isBoundedFiniteProjective (R := R)

/-- Helper for Lemma 15.127.3: the tensor unit of `D(R)` is compact because it is isomorphic to
`R[0]`, which is perfect and hence compact. -/
private theorem tensorUnit_isCompactObject :
    IsCompactObject (𝟙_ DMod) := by
  let P : ObjectProperty DMod := IsCompactObject
  have hringSingle : IsCompactObject (ringSingle : DMod) := by
    -- Proof comment: transport the known perfectness of `R[0]` across the perfect/compact
    -- equivalence.
    exact (isPerfect_iff_isCompactObject (ringSingle : DMod)).1 ring_single_isPerfect_local
  let e : (ringSingle : DMod) ≅ 𝟙_ DMod := by
    -- Proof comment: `ringSingle` is definitionally the degree-zero single complex, so the
    -- canonical tensor-unit comparison is the needed isomorphism.
    simpa [ringSingle] using (singleZeroIsoTensorUnit (R := R))
  -- Proof comment: compactness is stable under isomorphism.
  exact P.prop_of_iso e hringSingle

/-- Helper for Lemma 15.127.3: an exact pairing makes `M` compact by comparing
`preadditiveCoyoneda.obj (op M)` with a coproduct-preserving composite through the tensor unit. -/
private theorem exactPairing_isCompactObject
    {M N : DMod} [ExactPairing N M] :
    IsCompactObject M := by
  refine ⟨fun I ↦ ?_⟩
  let H : DMod ⥤ AddCommGrpCat := preadditiveCoyoneda.obj (op M)
  let _ : IsCompactObject (𝟙_ DMod) := tensorUnit_isCompactObject (R := R)
  let _ : PreservesColimitsOfShape (Discrete I) (tensorLeft N) :=
    tensorLeft_preserves_discrete_coproducts_of_exactPairing (M := M) (N := N) I
  let _ : PreservesColimitsOfShape (Discrete I)
      (tensorLeft N ⋙ preadditiveCoyoneda.obj (op (𝟙_ DMod))) := by
    infer_instance
  let _ : PreservesColimitsOfShape (Discrete I) (forget AddCommGrpCat) := by
    infer_instance
  let _ : PreservesColimitsOfShape (Discrete I)
      ((tensorLeft N ⋙ preadditiveCoyoneda.obj (op (𝟙_ DMod))) ⋙ forget AddCommGrpCat) := by
    exact
      CategoryTheory.Limits.comp_preservesColimitsOfShape
        (tensorLeft N ⋙ preadditiveCoyoneda.obj (op (𝟙_ DMod)))
        (forget AddCommGrpCat)
  have hcoyoneda : PreservesColimitsOfShape (Discrete I) (coyoneda.obj (op M)) := by
    -- Proof comment: after forgetting the additive structure, the exact pairing gives the usual
    -- represented-Hom comparison with the tensor-unit functor.
    simpa [Functor.assoc] using
      (CategoryTheory.Limits.preservesColimitsOfShape_of_natIso
        (J := Discrete I)
        ((exactPairing_coyoneda_iso (M := M) (N := N)).symm) :
        PreservesColimitsOfShape (Discrete I) (coyoneda.obj (op M)))
  let _ : PreservesColimitsOfShape (Discrete I) (H ⋙ forget AddCommGrpCat) := by
    simpa [H, Functor.assoc] using hcoyoneda
  let _ : ReflectsColimits (forget AddCommGrpCat) := by
    infer_instance
  let _ : ReflectsColimitsOfShape (Discrete I) (forget AddCommGrpCat) :=
    CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits
      (J := Discrete I) (forget AddCommGrpCat)
  -- Proof comment: `forget AddCommGrpCat` reflects colimits, so coproduct preservation of the
  -- underlying represented set-valued functor lifts back to `preadditiveCoyoneda`.
  simpa [H] using
    (CategoryTheory.Limits.preservesColimitsOfShape_of_reflects_of_preserves
      H (forget AddCommGrpCat) : PreservesColimitsOfShape (Discrete I) H)

/-- Lemma 15.127.3 (converse): if `M` admits a duality datum in the monoidal category `D(R)`,
then `M` is perfect. -/
@[stacks 0FNS]
theorem exactPairing_isPerfect
    {M N : DMod} (hpair : ExactPairing N M) :
    DerivedCategory.IsPerfect M := by
  letI : ExactPairing N M := hpair
  -- Proof comment: the exact pairing gives the compactness comparison, and compactness is
  -- equivalent to perfectness in `D(R)`.
  have hcompact : IsCompactObject M := exactPairing_isCompactObject (M := M) (N := N)
  -- Proof comment: invoke the established perfect-compact equivalence for `D(R)`.
  exact (isPerfect_iff_isCompactObject M).2 hcompact

/- Bridge/view for Lemma `15.127.3`: uniqueness of left duals is already owned by
`leftDualIso`. For a chosen pairing `hpair : ExactPairing N M`, the textbook comparison
`N ≅ M^\vee` is obtained directly by comparing `hpair` with the canonical derived-dual pairing,
so this file should not introduce a second wrapper around that owner declaration. -/
recall leftDualIso
    {C : Type _} [Category C] [MonoidalCategory C]
    {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) :
    X₁ ≅ X₂

end

end CategoryTheory
