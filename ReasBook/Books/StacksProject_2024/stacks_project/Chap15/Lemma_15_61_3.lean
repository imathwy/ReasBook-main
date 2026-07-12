import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.RingTheory.TensorProduct.Maps
import StacksProject_2024.Chap10.Lemma_10_76_1
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Lemma_15_60_3
import StacksProject_2024.Chap15.Definition_15_61_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ModuleCat ComplexShape
open scoped TensorProduct DerivedTensorWithAlgebra

noncomputable section

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] HasDerivedCategory.standard

section

variable {R R' A B A' B' : Type u}
variable [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R' A'] [Algebra R' B']
variable [Module.Flat R R']

local notation "ATensor" => TensorProduct R A R'
local notation "BTensor" => TensorProduct R R' B
local notation "extScalars" => ModuleCat.extendScalars (algebraMap R R')

private noncomputable def restrictScalarsSelfEquiv
    (T : Type u) [CommRing T] [Algebra R T] :
    ↑((ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T T)) ≃ₗ[T] T :=
  { __ := AddEquiv.refl T
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower
    (T : Type u) [CommRing T] [Algebra R T] :
    IsScalarTower R T
      ↑((ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T T)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/- 
Domain-style sampling for Lemma 15.61.3:
- primary domain: flat base change for the owner bifunctor `Tor` in module
  categories over commutative rings;
- sampled owner declarations of the same kind:
  `Tor`,
  `torBaseChangeHom`,
  `flat_tor_base_change_map_isIso`,
  `ModuleCat.extendScalars`;
- best owner abstraction: the Chapter 10 owner map `torBaseChangeHom` for `R → R'`;
- primitive data: the ring map `R → R'`, the two `R`-algebras `A`, `B`, and the two explicit
  `R'`-algebra comparison maps `A ⊗[R] R' → A'` and `R' ⊗[R] B → B'`;
- derived API: the source-facing comparison to `Tor_i^{R'}(A', B')`, obtained by composing the
  owner base-change map with functoriality in the two module variables.

Source/core/bridge triage:
- `source-facing`: the comparison morphism
  `torBaseChangeComparison : Tor_i^R(A, B) ⊗[R] R' ⟶ Tor_i^{R'}(A', B')`;
- `core/canonical`: `torBaseChangeHom` for the flat ring map `R → R'`;
- `bridge/view`: the explicit comparison maps `A ⊗[R] R' → A'` and `R' ⊗[R] B → B'`; the
  left-variable map is converted to the owner `extendScalars` order by
  `Algebra.TensorProduct.commRight`, and then both maps induce the target-side `Tor` morphism in
  `ModuleCat R'`.
-/

section

/-- Helper for Lemma 15.61.3: the map on the first Tor variable induced by
`A ⊗[R] R' → A'`, rewritten in the owner `extendScalars` order. -/
private noncomputable def tor_base_change_left_hom
    (aMap : A ⊗[R] R' →ₐ[R'] A') :
    (extScalars).obj (of R A) ⟶ of R' A' :=
  let aTensorEquiv :
      TensorProduct R ((ModuleCat.restrictScalars (algebraMap R R')).obj (of R' R')) (of R A) ≃ₗ[R']
        R' ⊗[R] A :=
    TensorProduct.AlgebraTensorModule.congr
      (restrictScalarsSelfEquiv R')
      (LinearEquiv.refl R A)
  let aLinear :
      TensorProduct R ((ModuleCat.restrictScalars (algebraMap R R')).obj (of R' R')) (of R A) →ₗ[R']
        A' :=
    ((aMap.comp (Algebra.TensorProduct.commRight R R' A).toAlgHom).toLinearMap).comp
      aTensorEquiv.toLinearMap
  ofHom aLinear

/-- Helper for Lemma 15.61.3: the map on the second Tor variable induced by
`R' ⊗[R] B → B'`. -/
private noncomputable def tor_base_change_right_hom
    (bMap : R' ⊗[R] B →ₐ[R'] B') :
    (extScalars).obj (of R B) ⟶ of R' B' :=
  let bTensorEquiv :
      TensorProduct R ((ModuleCat.restrictScalars (algebraMap R R')).obj (of R' R')) (of R B) ≃ₗ[R']
        R' ⊗[R] B :=
    TensorProduct.AlgebraTensorModule.congr
      (restrictScalarsSelfEquiv R')
      (LinearEquiv.refl R B)
  let bLinear :
      TensorProduct R ((ModuleCat.restrictScalars (algebraMap R R')).obj (of R' R')) (of R B) →ₗ[R']
        B' :=
    bMap.toLinearMap.comp bTensorEquiv.toLinearMap
  ofHom bLinear

/-- Helper for Lemma 15.61.3: after the Chapter 10 flat base-change map, the remaining tail is
the Tor-functoriality composite induced by the comparison maps on the two variables. -/
private noncomputable def tor_base_change_tail
    (aMap : A ⊗[R] R' →ₐ[R'] A')
    (bMap : R' ⊗[R] B →ₐ[R'] B')
    (i : ℕ) :
    (((Tor (ModuleCat R') i).obj ((extScalars).obj (of R A))).obj
      ((extScalars).obj (of R B))) ⟶
      Tor[R', i](A', B') :=
  let F := Tor (ModuleCat R') i
  (F.map (tor_base_change_left_hom (R := R) (R' := R') (A := A) (A' := A') aMap)).app
      ((extScalars).obj (of R B)) ≫
    (F.obj (of R' A')).map
      (tor_base_change_right_hom (R := R) (R' := R') (B := B) (B' := B') bMap)

/-- The source-facing comparison of Lemma 15.61.3: start with the Chapter 10 owner
`torBaseChangeHom` for `R → R'`, then apply functoriality in the two variables to reach
`Tor_i^{R'}(A', B')`. -/
def torBaseChangeComparison
    (aMap : A ⊗[R] R' →ₐ[R'] A')
    (bMap : R' ⊗[R] B →ₐ[R'] B')
    (i : ℕ) :
    (extScalars).obj (Tor[R, i](A, B)) ⟶ Tor[R', i](A', B') :=
  letI : Algebra ATensor A' := aMap.toAlgebra
  letI : Algebra BTensor B' := bMap.toAlgebra
  torBaseChangeHom (algebraMap R R') (RingHom.flat_algebraMap_iff.mpr inferInstance)
      (of R A) (of R B) i ≫
    tor_base_change_tail (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
      aMap bMap i

/-- Helper for Lemma 15.61.3: the initial flat base-change map from Chapter 10 is already an
isomorphism. -/
private theorem tor_base_change_initial_isIso
    (i : ℕ) :
    IsIso
      (torBaseChangeHom
        (algebraMap R R')
        (RingHom.flat_algebraMap_iff.mpr inferInstance)
        (of R A)
        (of R B)
        i) := by
  -- Chapter 10 proves the owner flat base-change comparison for every Tor degree.
  simpa using
    flat_tor_base_change_map_isIso
      (algebraMap R R')
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
      A
      B
      i

/-- Helper for Lemma 15.61.3: restricting scalars commutes with taking derived homology. -/
private noncomputable def restrict_scalars_homology_iso
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (L : DerivedCategory (ModuleCat T)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat S) n).obj
        (((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory).obj L) ≅
      (ModuleCat.restrictScalars (algebraMap S T)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat T) n).obj L) :=
  let K := DerivedCategory.Q.objPreimage L
  let FK := ((ModuleCat.restrictScalars (algebraMap S T)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let eT :
      ((DerivedCategory.homologyFunctor (ModuleCat T) n).obj L) ≅
        K.homology n :=
    ((DerivedCategory.homologyFunctor (ModuleCat T) n).mapIso
      (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) n).app K
  -- Move to a chosen complex representative and compare homology before and after restriction.
  (DerivedCategory.homologyFunctor (ModuleCat S) n).mapIso
      (((((
          (ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm) ≪≫
          ((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategoryFactors.app K))) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat S) n).app FK ≪≫
    (K.sc n).mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T)) ≪≫
      (ModuleCat.restrictScalars (algebraMap S T)).mapIso eT.symm

/-- Helper for Lemma 15.61.3: the `R' → A ⊗[R] R' → A'` route is the canonical `R' → A'`
algebra map. -/
private theorem tor_base_change_left_comp_eq
    (aMap : A ⊗[R] R' →ₐ[R'] A') :
    letI : Algebra ATensor A' := aMap.toAlgebra
    (algebraMap ATensor A').comp (algebraMap R' ATensor) = algebraMap R' A' := by
  -- The comparison map `aMap` is an `R'`-algebra morphism, so it agrees with the canonical
  -- `R'`-structure after precomposing with the right tensor-factor inclusion.
  letI : Algebra ATensor A' := aMap.toAlgebra
  ext x
  change aMap ((algebraMap R' ATensor) x) = (algebraMap R' A') x
  exact aMap.commutes x

/-- Helper for Lemma 15.61.3: the `R' → R' ⊗[R] B → B'` route is the canonical `R' → B'`
algebra map. -/
private theorem tor_base_change_right_comp_eq
    (bMap : R' ⊗[R] B →ₐ[R'] B') :
    letI : Algebra BTensor B' := bMap.toAlgebra
    (algebraMap BTensor B').comp (algebraMap R' BTensor) = algebraMap R' B' := by
  -- The comparison map `bMap` is also an `R'`-algebra morphism, so the right tensor-factor
  -- inclusion composes to the standard `R'`-algebra structure on `B'`.
  letI : Algebra BTensor B' := bMap.toAlgebra
  ext x
  change bMap ((algebraMap R' BTensor) x) = (algebraMap R' B') x
  exact bMap.commutes x

/-- Helper for Lemma 15.61.3: the middle step of the source proof is the canonical
iterated-vs-direct derived scalar-extension isomorphism from `R'` to `A'`. -/
private noncomputable abbrev tor_base_change_middle_compIso
    (aMap : A ⊗[R] R' →ₐ[R'] A') :
    letI : Algebra ATensor A' := aMap.toAlgebra
    derivedTensorWithAlgebra (algebraMap R' ATensor) ⋙
        derivedTensorWithAlgebra (algebraMap ATensor A') ≅
      derivedTensorWithAlgebra (algebraMap R' A') :=
  -- This is exactly the owner comparison between iterated and direct derived scalar extension.
  letI : Algebra ATensor A' := aMap.toAlgebra
  derivedTensorWithAlgebraCompIso
    (algebraMap R' ATensor)
    (algebraMap ATensor A')
    (algebraMap R' A')
    (tor_base_change_left_comp_eq (R := R) (R' := R') (A := A) (A' := A') aMap)

/-- Helper for Lemma 15.61.3: taking degree `-i` homology of the middle derived scalar-extension
isomorphism gives the transport between the left and right base-change steps. -/
private noncomputable abbrev tor_base_change_middle_compIso_homology
    (aMap : A ⊗[R] R' →ₐ[R'] A')
    (i : ℕ) :
    letI : Algebra ATensor A' := aMap.toAlgebra
    (DerivedCategory.homologyFunctor (ModuleCat A') (-((i : ℤ)))).obj
        ((derivedTensorWithAlgebra (algebraMap ATensor A')).obj
          ((derivedTensorWithAlgebra (algebraMap R' ATensor)).obj
            ((DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ)).obj (of R' BTensor)))) ≅
      (DerivedCategory.homologyFunctor (ModuleCat A') (-((i : ℤ)))).obj
        ((derivedTensorWithAlgebra (algebraMap R' A')).obj
          ((DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ)).obj (of R' BTensor))) :=
  -- Naming this homology isomorphism isolates the reassociation transport from the left/right
  -- flat base-change comparisons.
  letI : Algebra ATensor A' := aMap.toAlgebra
  (DerivedCategory.homologyFunctor (ModuleCat A') (-((i : ℤ)))).mapIso
    ((tor_base_change_middle_compIso (R := R) (R' := R') (A := A) (A' := A') aMap).app
      ((DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ)).obj (of R' BTensor)))

/-- Helper for Lemma 15.61.3: the middle homology transport is the hom of a named isomorphism,
so it is already an isomorphism before handling the outer flat base-change comparisons. -/
private theorem tor_base_change_middle_compIso_homology_isIso
    (aMap : A ⊗[R] R' →ₐ[R'] A')
    (i : ℕ) :
    letI : Algebra ATensor A' := aMap.toAlgebra
    IsIso
      ((tor_base_change_middle_compIso_homology
        (R := R) (R' := R') (A := A) (B := B) (A' := A') aMap i).hom) := by
  -- Name the mapped homology isomorphism explicitly so the target morphism becomes `e.hom`.
  let e :=
    (DerivedCategory.homologyFunctor (ModuleCat A') (-((i : ℤ)))).mapIso
      ((tor_base_change_middle_compIso
        (R := R) (R' := R') (A := A) (A' := A') aMap).app
          ((DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ)).obj
            (of R' BTensor)))
  change IsIso e.hom
  infer_instance

/-- Helper for Lemma 15.61.3: flat extension of scalars is exact, so its induced derived-category
functor is already its own left derived functor. -/
private theorem extend_scalars_mapDerivedCategoryh_isLeftDerivedFunctor
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    [CategoryTheory.Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars (algebraMap S T))] :
    ((ModuleCat.extendScalars (algebraMap S T)).mapDerivedCategory).IsLeftDerivedFunctor
      ((ModuleCat.extendScalars (algebraMap S T)).mapDerivedCategoryFactorsh.hom)
      (HomotopyCategory.quasiIso (ModuleCat S) (ComplexShape.up ℤ)) := by
  let F : ModuleCat S ⥤ ModuleCat T := ModuleCat.extendScalars (algebraMap S T)
  -- Exact flat extension preserves quasi-isomorphisms, so its exact derived functor is already
  -- the required left-derived functor.
  simpa [F] using
    (Functor.isLeftDerivedFunctor_of_inverts
      (HomotopyCategory.quasiIso (ModuleCat S) (ComplexShape.up ℤ))
      F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh)

/-- Helper for Lemma 15.61.3: the additive homotopy-to-derived bridge attached to a module
functor. -/
private abbrev map_homotopy_category_to_derived
    {C : Type u} {E : Type u} [Category C] [Category E] [Preadditive C] [Abelian E]
    [HasDerivedCategory E] (F : C ⥤ E) [F.Additive] :
    HomotopyCategory C (up ℤ) ⥤ DerivedCategory E :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- Helper for Lemma 15.61.3: scalar extension is additive on module categories. -/
local instance extendScalars_additive_local
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap S T)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (algebraMap S T)).left_adjoint_additive

/-- Helper for Lemma 15.61.3: flat scalar extension preserves finite limits. -/
local instance extendScalars_preservesFiniteLimits
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T] :
    CategoryTheory.Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap S T)) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr (show Module.Flat S T from inferInstance))

/-- Helper for Lemma 15.61.3: the adjoint-side description of the owner homology comparison is
obtained by unfolding the definition once. -/
private theorem derived_tensor_homology_comparison_adjoint_eq
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (K : DerivedCategory (ModuleCat S)) (i : ℤ) :
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap S T)).homEquiv _ _)
        (derivedTensorWithAlgebraHomologyComparison T K i) =
      (DerivedCategory.homologyFunctor (ModuleCat S) i).map
          ((derivedTensorWithAlgebraAdjunction (R := S) (A := T)).unit.app K) ≫
        (restrict_scalars_homology_iso
          ((derivedTensorWithAlgebra (algebraMap S T)).obj K) i).hom := by
  -- Unfold the owner comparison once; the resulting term is definitionally the adjoint-side
  -- homology map built from the derived adjunction unit and the restriction-of-scalars transport.
  rw [derivedTensorWithAlgebraHomologyComparison]
  simp only [Equiv.apply_symm_apply]
  rfl

/-- Helper for Lemma 15.61.3: postcomposing the homology image of the derived adjunction-unit
naturality square preserves the equality needed in the source-faithful tail comparison. -/
private theorem derived_adjunction_unit_homology_naturality_postcompose
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat S)}
    (f : K ⟶ L)
    (g :
      (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
          (((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory).obj
            ((derivedTensorWithAlgebra (algebraMap S T)).obj L)) ⟶
        (ModuleCat.restrictScalars (algebraMap S T)).obj
          ((DerivedCategory.homologyFunctor (ModuleCat T) i).obj
            ((derivedTensorWithAlgebra (algebraMap S T)).obj L))) :
    let HS := DerivedCategory.homologyFunctor (ModuleCat S) i
    let η := (derivedTensorWithAlgebraAdjunction (R := S) (A := T)).unit
    HS.map f ≫ HS.map (η.app L) ≫ g =
      HS.map (η.app K) ≫
        HS.map
          (((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory).map
            ((derivedTensorWithAlgebra (algebraMap S T)).map f)) ≫
          g := by
  let HS := DerivedCategory.homologyFunctor (ModuleCat S) i
  let η := (derivedTensorWithAlgebraAdjunction (R := S) (A := T)).unit
  have hη :
      HS.map f ≫ HS.map (η.app L) =
        HS.map (η.app K) ≫
          HS.map
            (((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory).map
              ((derivedTensorWithAlgebra (algebraMap S T)).map f)) := by
    -- Naturality of the derived adjunction unit moves the source morphism across the unit.
    simpa [HS, Functor.map_comp] using
      congrArg (fun h ↦ HS.map h) (η.naturality f)
  -- Postcompose the unit square by the later transport morphism and reassociate once.
  simpa [HS, η, Category.assoc] using congrArg (fun h ↦ h ≫ g) hη

/-- Helper for Lemma 15.61.3: under restriction of scalars, the homology map of a short-complex
morphism rewrites into the forward `mapHomologyIso` form used by the explicit transport square. -/
private theorem restrict_scalars_mapHomologyIso_hom_formula
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    {S₁ S₂ : ShortComplex (ModuleCat T)}
    (φ : S₁ ⟶ S₂) :
    (ModuleCat.restrictScalars (algebraMap S T)).map (ShortComplex.homologyMap φ) =
      (S₁.mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T))).inv ≫
        ShortComplex.homologyMap
          (((ModuleCat.restrictScalars (algebraMap S T)).mapShortComplex).map φ) ≫
        (S₂.mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T))).hom := by
  -- Start from the inverse-form naturality square already available for `mapHomologyIso`, then
  -- solve for the forward restriction-of-scalars homology map used below.
  calc
    (ModuleCat.restrictScalars (algebraMap S T)).map (ShortComplex.homologyMap φ) =
        (ModuleCat.restrictScalars (algebraMap S T)).map (ShortComplex.homologyMap φ) ≫
          (S₂.mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T))).inv ≫
            (S₂.mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T))).hom := by
      simp
    _ =
        (S₁.mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T))).inv ≫
          ShortComplex.homologyMap
            (((ModuleCat.restrictScalars (algebraMap S T)).mapShortComplex).map φ) ≫
          (S₂.mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T))).hom := by
      -- Postcompose the inverse-form naturality square by the target comparison isomorphism.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ≫ (S₂.mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T))).hom)
          (ShortComplex.mapHomologyIso_inv_naturality
            (F := ModuleCat.restrictScalars (algebraMap S T)) (φ := φ))

/-- Helper for Lemma 15.61.3: once a canonical `Q.objPreimage` representative of a derived
morphism is fixed, the restriction-of-scalars transport square reduces to the naturality of
`mapDerivedCategoryFactors`. -/
private theorem restrict_scalars_q_objPreimage_transport_bridge
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    {K L : DerivedCategory (ModuleCat T)}
    (f : K ⟶ L)
    (β : DerivedCategory.Q.objPreimage K ⟶ DerivedCategory.Q.objPreimage L)
    (hβ :
      DerivedCategory.Q.map β =
        (DerivedCategory.Q.objObjPreimageIso K).hom ≫ f ≫
          (DerivedCategory.Q.objObjPreimageIso L).inv) :
    let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
    let K' := DerivedCategory.Q.objPreimage K
    let L' := DerivedCategory.Q.objPreimage L
    res.mapDerivedCategory.map f ≫
        ((((res.mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          (res.mapDerivedCategoryFactors.app L')).hom) =
      ((((res.mapDerivedCategory).mapIso
          (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
        (res.mapDerivedCategoryFactors.app K')).hom) ≫
        DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β) := by
  let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
  let K' := DerivedCategory.Q.objPreimage K
  let L' := DerivedCategory.Q.objPreimage L
  let eK : DerivedCategory.Q.obj K' ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let eL : DerivedCategory.Q.obj L' ≅ L := DerivedCategory.Q.objObjPreimageIso L
  have hf :
      f = eK.inv ≫ DerivedCategory.Q.map β ≫ eL.hom := by
    -- Reexpress `f` by conjugating the chosen representative with the standard preimage
    -- isomorphisms.
    simpa [eK, eL, Category.assoc] using
      (congrArg (fun k ↦ eK.inv ≫ k ≫ eL.hom) hβ).symm
  -- After rewriting through `β`, the transport square is exactly the naturality of
  -- `mapDerivedCategoryFactors`.
  calc
    res.mapDerivedCategory.map f ≫
        ((((res.mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          (res.mapDerivedCategoryFactors.app L')).hom) =
      (((res.mapDerivedCategory).mapIso eK).symm).hom ≫
        (res.mapDerivedCategory.map (DerivedCategory.Q.map β) ≫
          (res.mapDerivedCategoryFactors.app L').hom) := by
        -- The `Q.objObjPreimageIso` conjugations cancel around the chosen representative.
        rw [hf]
        simp [res, K', L', eK, eL, Functor.map_comp, Category.assoc]
    _ =
      (((res.mapDerivedCategory).mapIso eK).symm).hom ≫
        ((res.mapDerivedCategoryFactors.app K').hom ≫
          DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) := by
        -- This is the naturality square for the derived comparison.
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ (((res.mapDerivedCategory).mapIso eK).symm).hom ≫ k)
            (res.mapDerivedCategoryFactors.hom.naturality β)
    _ =
      ((((res.mapDerivedCategory).mapIso
          (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
        (res.mapDerivedCategoryFactors.app K')).hom) ≫
        DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β) := by
        simp [res, K', eK, Category.assoc]

/-- Helper for Lemma 15.61.3: the homology map of a chosen `Q.objPreimage` representative
conjugates to the derived homology map of the induced morphism. -/
private theorem q_objPreimage_homologyMap_conjugated
    {T : Type u} [CommRing T]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat T)}
    (f : K ⟶ L)
    (β : DerivedCategory.Q.objPreimage K ⟶ DerivedCategory.Q.objPreimage L)
    (hβ :
      DerivedCategory.Q.map β =
        (DerivedCategory.Q.objObjPreimageIso K).hom ≫ f ≫
          (DerivedCategory.Q.objObjPreimageIso L).inv) :
    let HT := DerivedCategory.homologyFunctor (ModuleCat T)
    let K' := DerivedCategory.Q.objPreimage K
    let L' := DerivedCategory.Q.objPreimage L
    let eK : (HT i).obj K ≅ K'.homology i :=
      ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app K'
    let eL : (HT i).obj L ≅ L'.homology i :=
      ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
    HomologicalComplex.homologyMap β i =
      eK.inv ≫ (HT i).map f ≫ eL.hom := by
  let HT := DerivedCategory.homologyFunctor (ModuleCat T)
  let K' := DerivedCategory.Q.objPreimage K
  let L' := DerivedCategory.Q.objPreimage L
  let eQK : DerivedCategory.Q.obj K' ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let eQL : DerivedCategory.Q.obj L' ≅ L := DerivedCategory.Q.objObjPreimageIso L
  let ηK := (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app K'
  let ηL := (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
  let eK : (HT i).obj K ≅ K'.homology i :=
    ((HT i).mapIso eQK).symm ≪≫ ηK
  let eL : (HT i).obj L ≅ L'.homology i :=
    ((HT i).mapIso eQL).symm ≪≫ ηL
  have hnat :
      (HT i).map (DerivedCategory.Q.map β) ≫ ηL.hom =
        ηK.hom ≫ HomologicalComplex.homologyMap β i := by
    -- Naturality identifies the derived homology map of `Q.map β` with the chain-level one.
    simpa [ηK, ηL] using
      (DerivedCategory.homologyFunctorFactors_hom_naturality
        (C := ModuleCat T) β i)
  have hconj :
      HomologicalComplex.homologyMap β i =
        ηK.inv ≫ (HT i).map (DerivedCategory.Q.map β) ≫ ηL.hom := by
    have hpre :
        ηK.inv ≫ (ηK.hom ≫ HomologicalComplex.homologyMap β i) =
          ηK.inv ≫ ((HT i).map (DerivedCategory.Q.map β) ≫ ηL.hom) := by
      -- Precompose by the inverse source comparison to isolate the chain-level homology map.
      simpa [Category.assoc] using
        congrArg (fun k ↦ ηK.inv ≫ k) hnat.symm
    simpa [Category.assoc] using hpre
  have hf :
      f = eQK.inv ≫ DerivedCategory.Q.map β ≫ eQL.hom := by
    -- Reexpress `f` by conjugating the representative with the standard preimage isomorphisms.
    simpa [eQK, eQL, Category.assoc] using
      (congrArg (fun k ↦ eQK.inv ≫ k ≫ eQL.hom) hβ).symm
  have hstep :
      ηK.inv ≫ (HT i).map (DerivedCategory.Q.map β) ≫ ηL.hom =
        eK.inv ≫ (HT i).map f ≫ eL.hom := by
    -- Rewrite the represented derived morphism to the actual target morphism `f`.
    rw [hf]
    simp [HT, eK, eL, eQK, eQL, ηK, ηL, Functor.map_comp, Category.assoc]
  -- Replace `Q.map β` by the target morphism `f`.
  exact hconj.trans hstep

/-- Helper for Lemma 15.61.3: the restriction-of-scalars transport square is equally valid for an
arbitrary source representative `Y` of a derived morphism. -/
private theorem restrict_scalars_q_representative_transport_bridge
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    {K L : DerivedCategory (ModuleCat T)}
    {Y : CochainComplex (ModuleCat T) ℤ}
    (f : K ⟶ L)
    (eY : DerivedCategory.Q.obj Y ≅ K)
    (β : Y ⟶ DerivedCategory.Q.objPreimage L)
    (hβ :
      DerivedCategory.Q.map β =
        eY.hom ≫ f ≫
          (DerivedCategory.Q.objObjPreimageIso L).inv) :
    let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
    let L' := DerivedCategory.Q.objPreimage L
    res.mapDerivedCategory.map f ≫
        ((((res.mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          (res.mapDerivedCategoryFactors.app L')).hom) =
      ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
          (res.mapDerivedCategoryFactors.app Y)).hom) ≫
        DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β) := by
  let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
  let L' := DerivedCategory.Q.objPreimage L
  let eL : DerivedCategory.Q.obj L' ≅ L := DerivedCategory.Q.objObjPreimageIso L
  have hf :
      f = eY.inv ≫ DerivedCategory.Q.map β ≫ eL.hom := by
    -- Reexpress `f` through the chosen representative `β`.
    simpa [eL, Category.assoc] using
      (congrArg (fun k ↦ eY.inv ≫ k ≫ eL.hom) hβ).symm
  -- After this conjugation, the claim is the naturality square for
  -- `mapDerivedCategoryFactors.hom`.
  calc
    res.mapDerivedCategory.map f ≫
        ((((res.mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          (res.mapDerivedCategoryFactors.app L')).hom) =
      (((res.mapDerivedCategory).mapIso eY).symm).hom ≫
        (res.mapDerivedCategory.map (DerivedCategory.Q.map β) ≫
          (res.mapDerivedCategoryFactors.app L').hom) := by
        -- The source and target `Q`-model isomorphisms collapse the conjugated form of `f`.
        rw [hf]
        simp [res, L', eL, Functor.map_comp, Category.assoc]
    _ =
      (((res.mapDerivedCategory).mapIso eY).symm).hom ≫
        ((res.mapDerivedCategoryFactors.app Y).hom ≫
          DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) := by
        -- This is exactly the naturality of the derived comparison on the representative `β`.
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ (((res.mapDerivedCategory).mapIso eY).symm).hom ≫ k)
            (res.mapDerivedCategoryFactors.hom.naturality β)
    _ =
      ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
          (res.mapDerivedCategoryFactors.app Y)).hom) ≫
        DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β) := by
        simp [res, Category.assoc]

/-- Helper for Lemma 15.61.3: the short-complex homology map induced by a cochain map is
definitionally the usual homological-complex homology map in degree `i`. -/
private theorem shortComplexFunctor_homologyMap_eq
    {T : Type u} [CommRing T]
    {Y Z : CochainComplex (ModuleCat T) ℤ}
    (β : Y ⟶ Z) (i : ℤ) :
    ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat T) (up ℤ) i).map β) =
      HomologicalComplex.homologyMap β i := by
  -- The short-complex model of degree-`i` homology is defined by this forgetful reindexing.
  rfl

/-- Helper for Lemma 15.61.3: restriction of scalars commutes definitionally with the
degree-`i` short-complex functor on cochain complexes. -/
private theorem restrict_scalars_shortComplexFunctor_map_eq
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    {Y Z : CochainComplex (ModuleCat T) ℤ}
    (β : Y ⟶ Z) (i : ℤ) :
    (((ModuleCat.restrictScalars (algebraMap S T)).mapShortComplex).map
        ((HomologicalComplex.shortComplexFunctor (ModuleCat T) (up ℤ) i).map β)) =
      ((HomologicalComplex.shortComplexFunctor (ModuleCat S) (up ℤ) i).map
        (((ModuleCat.restrictScalars (algebraMap S T)).mapHomologicalComplex (up ℤ)).map β)) := by
  -- Both sides are the same short-complex morphism after unfolding the functorial definitions.
  rfl

/-- Helper for Lemma 15.61.3: after rewriting the short-complex transport square for
restriction of scalars, the source `mapHomologyIso` comparison cancels and yields the cochain
level homology-map formula in the forward orientation used below. -/
private theorem restrict_scalars_mapHomologyIso_source_cancel
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    {Y Z : CochainComplex (ModuleCat T) ℤ}
    (β : Y ⟶ Z) (i : ℤ) :
    let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
    ((Y.sc i).mapHomologyIso res).hom ≫
        res.map (HomologicalComplex.homologyMap β i) =
      HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
        ((Z.sc i).mapHomologyIso res).hom := by
  let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
  have hformula :
      res.map (HomologicalComplex.homologyMap β i) =
        ((Y.sc i).mapHomologyIso res).inv ≫
          HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
            ((Z.sc i).mapHomologyIso res).hom := by
    -- Rewrite the short-complex comparison into the cochain-level homology map.
    simpa [shortComplexFunctor_homologyMap_eq, restrict_scalars_shortComplexFunctor_map_eq] using
      (restrict_scalars_mapHomologyIso_hom_formula
        (S := S) (T := T)
        (S₁ := Y.sc i) (S₂ := Z.sc i)
        ((HomologicalComplex.shortComplexFunctor (ModuleCat T) (up ℤ) i).map β))
  -- Cancel the source `mapHomologyIso` inverse from the forward short-complex transport square.
  change ((Y.sc i).mapHomologyIso res).hom ≫
      res.map (HomologicalComplex.homologyMap β i) =
    HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
      ((Z.sc i).mapHomologyIso res).hom
  have hpre :
      ((Y.sc i).mapHomologyIso res).hom ≫
          res.map (HomologicalComplex.homologyMap β i) =
        ((Y.sc i).mapHomologyIso res).hom ≫
          (((Y.sc i).mapHomologyIso res).inv ≫
            HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
              ((Z.sc i).mapHomologyIso res).hom) :=
    congrArg (fun k ↦ ((Y.sc i).mapHomologyIso res).hom ≫ k) hformula
  simpa [Category.assoc] using hpre

/-- Helper for Lemma 15.61.3: the homology transport through `mapHomologyIso` depends only on the
chosen chain representative, not on using the canonical source preimage. -/
private theorem restrict_scalars_q_representative_homology_transport
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat T)}
    {Y : CochainComplex (ModuleCat T) ℤ}
    (β : Y ⟶ DerivedCategory.Q.objPreimage L) :
    let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
    let HS := DerivedCategory.homologyFunctor (ModuleCat S)
    let L' := DerivedCategory.Q.objPreimage L
    let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
    let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
    (HS i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
        ((L'.sc i).mapHomologyIso res).hom =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
        ((Y.sc i).mapHomologyIso res).hom ≫
        res.map (HomologicalComplex.homologyMap β i) := by
  let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
  let HS := DerivedCategory.homologyFunctor (ModuleCat S)
  let L' := DerivedCategory.Q.objPreimage L
  let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
  let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
  have hnat :
      (HS i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i := by
    -- Naturality identifies the derived homology map with the chain-level homology map on the
    -- chosen representative.
    simpa [FY, FL] using
      (DerivedCategory.homologyFunctorFactors_hom_naturality
        (C := ModuleCat S)
        ((res.mapHomologicalComplex (up ℤ)).map β) i)
  have hmap :
      ((Y.sc i).mapHomologyIso res).hom ≫
          res.map (HomologicalComplex.homologyMap β i) =
        HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
          ((L'.sc i).mapHomologyIso res).hom :=
    restrict_scalars_mapHomologyIso_source_cancel
      (S := S) (T := T) (β := β) (i := i)
  have hnat' :
      (HS i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
            ((L'.sc i).mapHomologyIso res).hom := by
    -- Postcompose the derived naturality square by the target `mapHomologyIso`.
    simpa [Category.assoc] using
      congrArg (fun k ↦ k ≫ ((L'.sc i).mapHomologyIso res).hom) hnat
  have hmap' :
      ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
            ((L'.sc i).mapHomologyIso res).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫
            res.map (HomologicalComplex.homologyMap β i) := by
    -- Precompose the forward `mapHomologyIso` transport by the source comparison on `FY`.
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫ k)
        hmap.symm
  -- Splice the derived naturality square with the forward `mapHomologyIso` transport.
  exact hnat'.trans hmap'

/-- Helper for Lemma 15.61.3: the homology map of an arbitrary representative roof conjugates to
the derived homology map of the underlying morphism. -/
private theorem q_representative_homologyMap_conjugated
    {T : Type u} [CommRing T]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat T)}
    {Y : CochainComplex (ModuleCat T) ℤ}
    (f : K ⟶ L)
    (eY : DerivedCategory.Q.obj Y ≅ K)
    (β : Y ⟶ DerivedCategory.Q.objPreimage L)
    (hβ :
      DerivedCategory.Q.map β =
        eY.hom ≫ f ≫
          (DerivedCategory.Q.objObjPreimageIso L).inv) :
    let HT := DerivedCategory.homologyFunctor (ModuleCat T)
    let eSrc : (HT i).obj K ≅ Y.homology i :=
      ((HT i).mapIso eY).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y
    let L' := DerivedCategory.Q.objPreimage L
    let eL : (HT i).obj L ≅ L'.homology i :=
      ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
    HomologicalComplex.homologyMap β i =
      eSrc.inv ≫ (HT i).map f ≫ eL.hom := by
  let HT := DerivedCategory.homologyFunctor (ModuleCat T)
  let eSrc : (HT i).obj K ≅ Y.homology i :=
    ((HT i).mapIso eY).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y
  let L' := DerivedCategory.Q.objPreimage L
  let eL : (HT i).obj L ≅ L'.homology i :=
    ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
  let eQL : DerivedCategory.Q.obj L' ≅ L := DerivedCategory.Q.objObjPreimageIso L
  let ηY := (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y
  let ηL := (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
  have hnat :
      (HT i).map (DerivedCategory.Q.map β) ≫ ηL.hom =
        ηY.hom ≫ HomologicalComplex.homologyMap β i := by
    -- Naturality identifies the derived homology map of `Q.map β` with the chain-level one.
    simpa [ηY, ηL] using
      (DerivedCategory.homologyFunctorFactors_hom_naturality
        (C := ModuleCat T) β i)
  have hconj :
      HomologicalComplex.homologyMap β i =
        ηY.inv ≫ (HT i).map (DerivedCategory.Q.map β) ≫ ηL.hom := by
    have hpre :
        ηY.inv ≫ (ηY.hom ≫ HomologicalComplex.homologyMap β i) =
          ηY.inv ≫ ((HT i).map (DerivedCategory.Q.map β) ≫ ηL.hom) := by
      -- Precompose by the inverse source comparison to isolate the chain-level homology map.
      simpa [Category.assoc] using
        congrArg (fun k ↦ ηY.inv ≫ k) hnat.symm
    simpa [Category.assoc] using hpre
  have hf :
      f = eY.inv ≫ DerivedCategory.Q.map β ≫ eQL.hom := by
    -- Reexpress `f` through the chosen representative `β`.
    simpa [eQL, Category.assoc] using
      (congrArg (fun k ↦ eY.inv ≫ k ≫ eQL.hom) hβ).symm
  have hstep :
      ηY.inv ≫ (HT i).map (DerivedCategory.Q.map β) ≫ ηL.hom =
        eSrc.inv ≫ (HT i).map f ≫ eL.hom := by
    -- Rewrite the represented derived morphism to the actual target morphism `f`.
    rw [hf]
    simp [HT, eSrc, eL, eQL, ηY, ηL, Functor.map_comp, Category.assoc]
  -- Replace `Q.map β` by the target morphism `f`.
  exact hconj.trans hstep

/-- Helper for Lemma 15.61.3: once the source morphism is represented by an arbitrary roof, the
restriction-of-scalars homology square becomes fully explicit. -/
private theorem restrict_scalars_homology_iso_naturality_of_representative
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat T)}
    (f : K ⟶ L)
    {Y : CochainComplex (ModuleCat T) ℤ}
    (eY : DerivedCategory.Q.obj Y ≅ K)
    (β : Y ⟶ DerivedCategory.Q.objPreimage L)
    (hβ :
      DerivedCategory.Q.map β =
        eY.hom ≫ f ≫
          (DerivedCategory.Q.objObjPreimageIso L).inv) :
    let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
    let HS := DerivedCategory.homologyFunctor (ModuleCat S)
    let HT := DerivedCategory.homologyFunctor (ModuleCat T)
    let L' := DerivedCategory.Q.objPreimage L
    let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
    let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
    let eSrc : (HT i).obj K ≅ Y.homology i :=
      ((HT i).mapIso eY).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y
    let eL : (HT i).obj L ≅ L'.homology i :=
      ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
    (HS i).map (res.mapDerivedCategory.map f) ≫
        ((HS i).mapIso
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
            (res.mapDerivedCategoryFactors.app L')))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
        ((L'.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eL.symm).hom =
      ((HS i).mapIso
          ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
            (res.mapDerivedCategoryFactors.app Y)))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
        ((Y.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eSrc.symm).hom ≫
        res.map ((HT i).map f) := by
  let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
  let HS := DerivedCategory.homologyFunctor (ModuleCat S)
  let HT := DerivedCategory.homologyFunctor (ModuleCat T)
  let L' := DerivedCategory.Q.objPreimage L
  let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
  let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
  let eSrc : (HT i).obj K ≅ Y.homology i :=
    ((HT i).mapIso eY).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y
  let eL : (HT i).obj L ≅ L'.homology i :=
    ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
  have hbridge :
      res.mapDerivedCategory.map f ≫
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
            (res.mapDerivedCategoryFactors.app L')).hom) =
        ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
            (res.mapDerivedCategoryFactors.app Y)).hom) ≫
          DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β) :=
    restrict_scalars_q_representative_transport_bridge
      (S := S) (T := T) (f := f) (eY := eY) (β := β) hβ
  have hbridge_homology :
      (HS i).map (res.mapDerivedCategory.map f) ≫
          ((HS i).mapIso
            ((((res.mapDerivedCategory).mapIso
                (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
              (res.mapDerivedCategoryFactors.app L')))).hom =
        ((HS i).mapIso
            ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
              (res.mapDerivedCategoryFactors.app Y)))).hom ≫
          (HS i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) := by
    -- Apply degree-`i` homology to the transport bridge between the derived morphism and the
    -- chosen cochain representative.
    simpa [Functor.map_comp, Functor.mapIso_hom, Category.assoc] using
      congrArg (fun k ↦ (HS i).map k) hbridge
  have htransport :
      (HS i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫
          res.map (HomologicalComplex.homologyMap β i) :=
    restrict_scalars_q_representative_homology_transport
      (S := S) (T := T) (i := i) (K := K) (L := L) (β := β)
  have hβ_homology :
      res.map (HomologicalComplex.homologyMap β i) ≫ (res.mapIso eL.symm).hom =
        (res.mapIso eSrc.symm).hom ≫ res.map ((HT i).map f) := by
    -- Map the representative-level conjugation formula through restriction of scalars and cancel
    -- the target `mapIso` tail explicitly.
    have hconj :
        HomologicalComplex.homologyMap β i =
          eSrc.inv ≫ (HT i).map f ≫ eL.hom :=
      q_representative_homologyMap_conjugated
        (T := T) (i := i) (f := f) (eY := eY) (β := β) hβ
    rw [hconj]
    simp [Functor.map_comp, Category.assoc]
  let sourceComparison :
      (HS i).obj (res.mapDerivedCategory.obj K) ⟶
        (HS i).obj (DerivedCategory.Q.obj ((res.mapHomologicalComplex (up ℤ)).obj Y)) :=
    ((HS i).mapIso
      ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
        (res.mapDerivedCategoryFactors.app Y)))).hom
  have hstep₁ :
      (HS i).map (res.mapDerivedCategory.map f) ≫
          ((HS i).mapIso
            ((((res.mapDerivedCategory).mapIso
                (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
              (res.mapDerivedCategoryFactors.app L')))).hom ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom ≫
          (res.mapIso eL.symm).hom =
        sourceComparison ≫
          (HS i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom ≫
          (res.mapIso eL.symm).hom := by
    -- Append the remaining homology-side tail to the derived representative bridge.
    simpa [sourceComparison, Category.assoc] using
      congrArg
        (fun k ↦ k ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom ≫
          (res.mapIso eL.symm).hom)
        hbridge_homology
  have hstep₂ :
      sourceComparison ≫
          (HS i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom ≫
          (res.mapIso eL.symm).hom =
        sourceComparison ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫
          res.map (HomologicalComplex.homologyMap β i) ≫
          (res.mapIso eL.symm).hom := by
    -- Replace the transported chain-level homology map by the forward representative transport.
    simpa [sourceComparison, Category.assoc] using
      congrArg
        (fun k ↦ sourceComparison ≫ k ≫ (res.mapIso eL.symm).hom)
        htransport
  have hstep₃ :
      sourceComparison ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫
          res.map (HomologicalComplex.homologyMap β i) ≫
          (res.mapIso eL.symm).hom =
        sourceComparison ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫
          (res.mapIso eSrc.symm).hom ≫
          res.map ((HT i).map f) := by
    -- Replace the representative cochain homology map by the derived homology map of `f`.
    simpa [sourceComparison, Category.assoc] using
      congrArg
        (fun k ↦ sourceComparison ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫ k)
        hβ_homology
  -- Expose the chosen roof on the derived side, then replace the cochain-level homology map by
  -- the conjugated derived homology map of `f`.
  exact hstep₁.trans (hstep₂.trans hstep₃)

/-- Helper for Lemma 15.61.3: every morphism into a derived object can be represented by a roof
whose target is the chosen `Q.objPreimage` model of that object. -/
private theorem exists_quasi_iso_fraction_to_preimage
    {T : Type u}
    [CommRing T]
    {K₀ : CochainComplex (ModuleCat T) ℤ}
    {L : DerivedCategory (ModuleCat T)}
    (α : DerivedCategory.Q.obj K₀ ⟶ L) :
    ∃ (Y : CochainComplex (ModuleCat T) ℤ) (σ : Y ⟶ K₀) (_ : QuasiIso σ)
      (β : Y ⟶ DerivedCategory.Q.objPreimage L),
      DerivedCategory.Q.map σ ≫ α =
        DerivedCategory.Q.map β ≫ (DerivedCategory.Q.objObjPreimageIso L).hom := by
  let γ :
      DerivedCategory.Q.obj K₀ ⟶
        DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage L) :=
    α ≫ (DerivedCategory.Q.objObjPreimageIso L).inv
  obtain ⟨Y, σ, hσ, β, hγ⟩ := DerivedCategory.right_fac γ
  refine ⟨Y, σ, ?_, β, ?_⟩
  · -- `right_fac` returns a denominator inverted by `Q`, which is exactly a quasi-isomorphism.
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso] at hσ
    exact hσ
  -- Cancel the target preimage isomorphism introduced in the transported factorization.
  calc
    DerivedCategory.Q.map σ ≫ α =
        DerivedCategory.Q.map σ ≫
          (α ≫ (DerivedCategory.Q.objObjPreimageIso L).inv) ≫
            (DerivedCategory.Q.objObjPreimageIso L).hom := by
          simp [Category.assoc]
    _ = DerivedCategory.Q.map σ ≫ γ ≫
          (DerivedCategory.Q.objObjPreimageIso L).hom := by
          rfl
    _ = DerivedCategory.Q.map σ ≫
          (inv (DerivedCategory.Q.map σ) ≫ DerivedCategory.Q.map β) ≫
            (DerivedCategory.Q.objObjPreimageIso L).hom := by
          rw [hγ]
    _ = DerivedCategory.Q.map β ≫
          (DerivedCategory.Q.objObjPreimageIso L).hom := by
          simp [Category.assoc]

/-- Helper for Lemma 15.61.3: restricting scalars commutes naturally with taking derived
homology. -/
private theorem restrict_scalars_homology_iso_denominator_cancel
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (i : ℤ)
    {K : DerivedCategory (ModuleCat T)}
    {Y : CochainComplex (ModuleCat T) ℤ}
    (σ : Y ⟶ DerivedCategory.Q.objPreimage K)
    [QuasiIso σ] :
    let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
    let HS := DerivedCategory.homologyFunctor (ModuleCat S)
    let HT := DerivedCategory.homologyFunctor (ModuleCat T)
    let K' := DerivedCategory.Q.objPreimage K
    let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
    let FK := (res.mapHomologicalComplex (up ℤ)).obj K'
    let eY : DerivedCategory.Q.obj Y ≅ K :=
      (asIso (DerivedCategory.Q.map σ)) ≪≫ DerivedCategory.Q.objObjPreimageIso K
    let eSrc : (HT i).obj K ≅ Y.homology i :=
      ((HT i).mapIso eY).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y
    let eK : (HT i).obj K ≅ K'.homology i :=
      ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app K'
    ((HS i).mapIso
        ((((res.mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
          (res.mapDerivedCategoryFactors.app K')))).hom ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FK).hom ≫
      ((K'.sc i).mapHomologyIso res).hom ≫
      (res.mapIso eK.symm).hom =
    ((HS i).mapIso
        ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
          (res.mapDerivedCategoryFactors.app Y)))).hom ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
      ((Y.sc i).mapHomologyIso res).hom ≫
      (res.mapIso eSrc.symm).hom := by
  let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
  let K' := DerivedCategory.Q.objPreimage K
  let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
  let FK := (res.mapHomologicalComplex (up ℤ)).obj K'
  letI : IsIso (DerivedCategory.Q.map σ) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let eY : DerivedCategory.Q.obj Y ≅ K :=
    (asIso (DerivedCategory.Q.map σ)) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let eSrc :
      ((DerivedCategory.homologyFunctor (ModuleCat T) i).obj K) ≅
        Y.homology i :=
    ((DerivedCategory.homologyFunctor (ModuleCat T) i).mapIso eY).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y
  let eK :
      ((DerivedCategory.homologyFunctor (ModuleCat T) i).obj K) ≅
        K'.homology i :=
    ((DerivedCategory.homologyFunctor (ModuleCat T) i).mapIso
      (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app K'
  have hσ :
      DerivedCategory.Q.map σ =
        eY.hom ≫ (𝟙 K) ≫ (DerivedCategory.Q.objObjPreimageIso K).inv := by
    -- The chosen denominator roof is just the identity representative of `K` after conjugation
    -- by the standard `Q.objPreimage` isomorphism.
    simp [eY, Category.assoc]
  have hcancel :=
    restrict_scalars_homology_iso_naturality_of_representative
      (S := S) (T := T) (i := i)
      (K := K) (L := K) (f := 𝟙 K)
      (eY := eY) (β := σ) hσ
  -- Specializing the representative naturality theorem to the identity morphism removes the
  -- denominator transport and recovers the canonical source-side comparison for `Q.objPreimage K`.
  simpa [res, K', FY, FK, eY, eSrc, eK, Functor.mapIso_hom, Iso.trans_hom,
    Functor.map_comp, Category.assoc] using hcancel

/-- Helper for Lemma 15.61.3: restricting scalars commutes naturally with taking derived
homology. -/
private theorem restrict_scalars_homology_iso_naturality_expanded
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat T)}
    (f : K ⟶ L) :
    let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
    let HS := DerivedCategory.homologyFunctor (ModuleCat S)
    let HT := DerivedCategory.homologyFunctor (ModuleCat T)
    let K' := DerivedCategory.Q.objPreimage K
    let L' := DerivedCategory.Q.objPreimage L
    let FK := (res.mapHomologicalComplex (up ℤ)).obj K'
    let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
    let eK : (HT i).obj K ≅ K'.homology i :=
      ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app K'
    let eL : (HT i).obj L ≅ L'.homology i :=
      ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
    (HS i).map (res.mapDerivedCategory.map f) ≫
        ((HS i).mapIso
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
            (res.mapDerivedCategoryFactors.app L')))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
        ((L'.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eL.symm).hom =
      ((HS i).mapIso
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
            (res.mapDerivedCategoryFactors.app K')))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FK).hom ≫
        ((K'.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eK.symm).hom ≫
        res.map ((HT i).map f) := by
  let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
  let HS := DerivedCategory.homologyFunctor (ModuleCat S) i
  let HT := DerivedCategory.homologyFunctor (ModuleCat T) i
  let K' := DerivedCategory.Q.objPreimage K
  let L' := DerivedCategory.Q.objPreimage L
  let FK := (res.mapHomologicalComplex (up ℤ)).obj K'
  let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
  let eK : HT.obj K ≅ K'.homology i :=
    (HT.mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app K'
  let eL : HT.obj L ≅ L'.homology i :=
    (HT.mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
  obtain ⟨Y, σ, hσ, β, hβfac⟩ :=
    exists_quasi_iso_fraction_to_preimage
      (T := T) (K₀ := K') (L := L)
      ((DerivedCategory.Q.objObjPreimageIso K).hom ≫ f)
  let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
  letI : QuasiIso σ := hσ
  letI : IsIso (DerivedCategory.Q.map σ) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let eY : DerivedCategory.Q.obj Y ≅ K :=
    (asIso (DerivedCategory.Q.map σ)) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have hβ :
      DerivedCategory.Q.map β =
        eY.hom ≫ f ≫ (DerivedCategory.Q.objObjPreimageIso L).inv := by
    have hβ' :
        DerivedCategory.Q.map σ ≫
            ((DerivedCategory.Q.objObjPreimageIso K).hom ≫ f) ≫
            (DerivedCategory.Q.objObjPreimageIso L).inv =
          DerivedCategory.Q.map β := by
      -- Postcompose the chosen right-fraction equality by the inverse target preimage
      -- isomorphism to isolate the numerator roof.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ≫ (DerivedCategory.Q.objObjPreimageIso L).inv)
          hβfac
    calc
      DerivedCategory.Q.map β =
          DerivedCategory.Q.map σ ≫
              ((DerivedCategory.Q.objObjPreimageIso K).hom ≫ f) ≫
                (DerivedCategory.Q.objObjPreimageIso L).inv := hβ'.symm
      _ = eY.hom ≫ f ≫ (DerivedCategory.Q.objObjPreimageIso L).inv := by
        simp [eY, Category.assoc]
  have hrep :=
    restrict_scalars_homology_iso_naturality_of_representative
      (S := S) (T := T) (i := i)
      (K := K) (L := L) (f := f)
      (eY := eY) (β := β) hβ
  have hcancel :=
    restrict_scalars_homology_iso_denominator_cancel
      (S := S) (T := T) (i := i)
      (K := K) (σ := σ)
  have hcancel_post :
      (HS.mapIso
          ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
            (res.mapDerivedCategoryFactors.app Y)))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
        ((Y.sc i).mapHomologyIso res).hom ≫
        (res.mapIso
          (((HT.mapIso eY).symm ≪≫
            (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y).symm)).hom ≫
        res.map (HT.map f) =
      (HS.mapIso
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
            (res.mapDerivedCategoryFactors.app K')))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FK).hom ≫
        ((K'.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eK.symm).hom ≫
        res.map (HT.map f) := by
    -- Cancel the denominator roof once and then postcompose by the actual homology map of `f`.
    simpa [res, HS, HT, K', FY, FK, eY, eK, Functor.mapIso_hom, Iso.trans_hom,
      Functor.map_comp, Category.assoc] using
      congrArg (fun k ↦ k ≫ res.map (HT.map f)) hcancel.symm
  -- Represent `f` by a right fraction into `Q.objPreimage L`, then splice the numerator roof
  -- with the identity-case denominator cancellation on `K`.
  exact hrep.trans hcancel_post

/-- Helper for Lemma 15.61.3: restricting scalars commutes naturally with taking derived
homology. -/
private theorem restrict_scalars_homology_iso_naturality
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat T)}
    (f : K ⟶ L) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).map
        (((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory).map f) ≫
        (restrict_scalars_homology_iso L i).hom =
        (restrict_scalars_homology_iso K i).hom ≫
          (ModuleCat.restrictScalars (algebraMap S T)).map
            ((DerivedCategory.homologyFunctor (ModuleCat T) i).map f) := by
  -- The public naturality statement is just the condensed form of the expanded transport square.
  simpa [restrict_scalars_homology_iso, Category.assoc, Iso.trans_hom, Functor.mapIso_hom] using
    (restrict_scalars_homology_iso_naturality_expanded
      (S := S) (T := T) (i := i) (f := f))

/-- Helper for Lemma 15.61.3: the owner homology comparison is natural in the source derived
object. -/
private theorem derived_tensor_homology_comparison_naturality
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat S)}
    (f : K ⟶ L) :
    (ModuleCat.extendScalars (algebraMap S T)).map
        ((DerivedCategory.homologyFunctor (ModuleCat S) i).map f) ≫
      derivedTensorWithAlgebraHomologyComparison T L i =
        derivedTensorWithAlgebraHomologyComparison T K i ≫
          (DerivedCategory.homologyFunctor (ModuleCat T) i).map
            ((derivedTensorWithAlgebra (algebraMap S T)).map f) := by
  let HS := DerivedCategory.homologyFunctor (ModuleCat S) i
  let η := (derivedTensorWithAlgebraAdjunction (R := S) (A := T)).unit
  -- Apply the scalar-extension/restriction adjunction; after rewriting both sides to the
  -- adjoint model, only the restriction-of-scalars homology naturality square remains.
  refine ((ModuleCat.extendRestrictScalarsAdj (algebraMap S T)).homEquiv _ _).injective ?_
  rw [CategoryTheory.Adjunction.homEquiv_naturality_left]
  rw [CategoryTheory.Adjunction.homEquiv_naturality_right]
  rw [derived_tensor_homology_comparison_adjoint_eq (S := S) (T := T) (K := L) (i := i)]
  rw [derived_tensor_homology_comparison_adjoint_eq (S := S) (T := T) (K := K) (i := i)]
  calc
    HS.map f ≫ HS.map (η.app L) ≫
        (restrict_scalars_homology_iso
          ((derivedTensorWithAlgebra (algebraMap S T)).obj L) i).hom =
      HS.map (η.app K) ≫
          HS.map
            (((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory).map
              ((derivedTensorWithAlgebra (algebraMap S T)).map f)) ≫
        (restrict_scalars_homology_iso
          ((derivedTensorWithAlgebra (algebraMap S T)).obj L) i).hom := by
        simpa using
          (derived_adjunction_unit_homology_naturality_postcompose
            (S := S) (T := T) (i := i) (f := f)
            (g := (restrict_scalars_homology_iso
              ((derivedTensorWithAlgebra (algebraMap S T)).obj L) i).hom))
    _ = HS.map (η.app K) ≫
          ((restrict_scalars_homology_iso
              ((derivedTensorWithAlgebra (algebraMap S T)).obj K) i).hom ≫
            (ModuleCat.restrictScalars (algebraMap S T)).map
              ((DerivedCategory.homologyFunctor (ModuleCat T) i).map
                ((derivedTensorWithAlgebra (algebraMap S T)).map f))) := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ HS.map (η.app K) ≫ k)
            (restrict_scalars_homology_iso_naturality
              (S := S) (T := T) (i := i)
              (f := (derivedTensorWithAlgebra (algebraMap S T)).map f))
    _ = HS.map (η.app K) ≫
          (restrict_scalars_homology_iso
            ((derivedTensorWithAlgebra (algebraMap S T)).obj K) i).hom ≫
          (ModuleCat.restrictScalars (algebraMap S T)).map
            ((DerivedCategory.homologyFunctor (ModuleCat T) i).map
              ((derivedTensorWithAlgebra (algebraMap S T)).map f)) := by
        simp

/-- Helper for Lemma 15.61.3: exact flat scalar extension agrees with the owner derived scalar
extension functor. -/
private noncomputable def flat_extend_scalars_mapDerivedCategory_iso
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T] :
    (ModuleCat.extendScalars (algebraMap S T)).mapDerivedCategory ≅
      derivedTensorWithAlgebra (algebraMap S T) := by
  let F₀ : ModuleCat S ⥤ ModuleCat T := ModuleCat.extendScalars (algebraMap S T)
  let F :
      HomotopyCategory (ModuleCat S) (up ℤ) ⥤
        DerivedCategory (ModuleCat T) :=
    map_homotopy_category_to_derived F₀
  letI :
      F.HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (ModuleCat S) (ComplexShape.up ℤ)) := by
    simpa [F, F₀] using
      (extendScalarsToDerived_hasLeftDerivedFunctor
        (R := S) (A := T) (algebraMap S T))
  letI :
      F₀.mapDerivedCategory.IsLeftDerivedFunctor
        F₀.mapDerivedCategoryFactorsh.hom
        (HomotopyCategory.quasiIso (ModuleCat S) (ComplexShape.up ℤ)) := by
    simpa [F₀] using
      (extend_scalars_mapDerivedCategoryh_isLeftDerivedFunctor (S := S) (T := T))
  -- Compare exact flat scalar extension with the owner total-left-derived scalar extension.
  simpa [derivedTensorWithAlgebra, F, F₀] using
    (Functor.leftDerivedNatIso
      F₀.mapDerivedCategory
      (F.totalLeftDerived
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleCat S) (ComplexShape.up ℤ)))
      F₀.mapDerivedCategoryFactorsh.hom
      (Functor.totalLeftDerivedCounit
        F
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleCat S) (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (ModuleCat S) (ComplexShape.up ℤ))
      (Iso.refl _))

/-- Helper for Lemma 15.61.3: whiskering the forward map of `leftDerivedNatIso` by the
localization functor and then composing with the target counit recovers the original
prederived comparison morphism. -/
private theorem Functor.leftDerivedNatIso_hom_assoc_totalLeftDerivedCounit
    {C D H : Type*} [Category C] [Category D] [Category H]
    {L : C ⥤ D} {W : MorphismProperty C} [L.IsLocalization W]
    {F F' : C ⥤ H} {LF LF' : D ⥤ H}
    {α : L ⋙ LF ⟶ F} {α' : L ⋙ LF' ⟶ F'}
    [LF.IsLeftDerivedFunctor α W] [LF'.IsLeftDerivedFunctor α' W]
    (e : F' ≅ F) :
    Functor.whiskerLeft L (Functor.leftDerivedNatIso LF' LF α' α W e).hom ≫ α =
      α' ≫ e.hom := by
  -- Expand `leftDerivedNatIso` to the underlying `leftDerivedNatTrans`, then use the defining
  -- left-derived factorization identity.
  simpa [Functor.leftDerivedNatIso] using
    (Functor.leftDerivedNatTrans_fac LF' LF α' α W e.hom)

/-- Helper for Lemma 15.61.3: exact flat scalar extension commutes with taking homology. -/
private noncomputable def flat_extend_scalars_homology_iso
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T]
    (L : DerivedCategory (ModuleCat S)) (i : ℤ) :
    (ModuleCat.extendScalars (algebraMap S T)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat S) i).obj L) ≅
      (DerivedCategory.homologyFunctor (ModuleCat T) i).obj
        (((ModuleCat.extendScalars (algebraMap S T)).mapDerivedCategory).obj L) := by
  let K := DerivedCategory.Q.objPreimage L
  let FK :=
    ((ModuleCat.extendScalars (algebraMap S T)).mapHomologicalComplex (up ℤ)).obj K
  let eS :
      (DerivedCategory.homologyFunctor (ModuleCat S) i).obj L ≅ K.homology i :=
    ((DerivedCategory.homologyFunctor (ModuleCat S) i).mapIso
      (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app K
  let e :
      (DerivedCategory.homologyFunctor (ModuleCat T) i).obj
          (((ModuleCat.extendScalars (algebraMap S T)).mapDerivedCategory).obj L) ≅
        (ModuleCat.extendScalars (algebraMap S T)).obj
          ((DerivedCategory.homologyFunctor (ModuleCat S) i).obj L) :=
    (DerivedCategory.homologyFunctor (ModuleCat T) i).mapIso
        (((((ModuleCat.extendScalars (algebraMap S T)).mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm) ≪≫
          ((ModuleCat.extendScalars (algebraMap S T)).mapDerivedCategoryFactors.app K)) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app FK ≪≫
      (K.sc i).mapHomologyIso (ModuleCat.extendScalars (algebraMap S T)) ≪≫
        (ModuleCat.extendScalars (algebraMap S T)).mapIso eS.symm
  -- Pass to a chosen complex representative, commute homology past exact flat extension, and
  -- invert the comparison to obtain the source-facing orientation.
  exact e.symm

/-- Helper for Lemma 15.61.3: under flatness, the scalar extension of homology agrees with the
homology of the owner derived scalar extension. -/
private noncomputable def flat_derived_tensor_homology_iso
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T]
    (K : DerivedCategory (ModuleCat S)) (i : ℤ) :
    (ModuleCat.extendScalars (algebraMap S T)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat S) i).obj K) ≅
      (DerivedCategory.homologyFunctor (ModuleCat T) i).obj
        ((derivedTensorWithAlgebra (algebraMap S T)).obj K) :=
  -- First commute exact flat scalar extension with homology, then rewrite exact extension as the
  -- owner derived scalar-extension functor.
  flat_extend_scalars_homology_iso (S := S) (T := T) K i ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat T) i).mapIso
      ((flat_extend_scalars_mapDerivedCategory_iso (S := S) (T := T)).app K)

/-- Helper for Lemma 15.61.3: the remaining flat comparison is the adjoint-side bridge between
the owner homology comparison and the explicit flat homology isomorphism. -/
private theorem flat_derived_tensor_homology_iso_hom
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T]
    (K : DerivedCategory (ModuleCat S)) (i : ℤ) :
    (flat_derived_tensor_homology_iso (S := S) (T := T) K i).hom =
      (flat_extend_scalars_homology_iso (S := S) (T := T) K i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat T) i).map
          ((flat_extend_scalars_mapDerivedCategory_iso (S := S) (T := T)).app K).hom := by
  -- Unfold the explicit flat homology isomorphism into its exact-extension part followed by the
  -- comparison from exact flat extension to the owner derived functor.
  simp [flat_derived_tensor_homology_iso]

/-- Helper for Lemma 15.61.3: under the ordinary module adjunction, the explicit flat homology
isomorphism transposes to the exact adjunction unit followed by restriction of scalars applied to
its defining composite. -/
private theorem flat_derived_tensor_homology_iso_adjoint_eq
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T]
    (K : DerivedCategory (ModuleCat S)) (i : ℤ) :
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap S T)).homEquiv _ _)
        ((flat_derived_tensor_homology_iso (S := S) (T := T) K i).hom) =
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap S T)).unit.app
          ((DerivedCategory.homologyFunctor (ModuleCat S) i).obj K) ≫
        (ModuleCat.restrictScalars (algebraMap S T)).map
          (flat_extend_scalars_homology_iso (S := S) (T := T) K i).hom) ≫
        (ModuleCat.restrictScalars (algebraMap S T)).map
          ((DerivedCategory.homologyFunctor (ModuleCat T) i).map
            ((flat_extend_scalars_mapDerivedCategory_iso (S := S) (T := T)).app K).hom) := by
  -- Rewrite the hom-set transpose by `Adjunction.homEquiv_unit`, then expand the explicit flat
  -- homology isomorphism into its exact and derived comparison pieces.
  rw [flat_derived_tensor_homology_iso_hom (S := S) (T := T) (K := K) (i := i)]
  rw [CategoryTheory.Adjunction.homEquiv_unit]
  simp [Functor.map_comp, Category.assoc]

/-- Helper for Lemma 15.61.3: the remaining flat comparison is the adjoint-side bridge between
the owner homology comparison and the explicit flat homology isomorphism. -/
private theorem flat_derived_tensor_homology_comparison_adjoint_bridge
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T]
    (K : DerivedCategory (ModuleCat S)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).map
        ((derivedTensorWithAlgebraAdjunction (R := S) (A := T)).unit.app K) ≫
      (restrict_scalars_homology_iso
        ((derivedTensorWithAlgebra (algebraMap S T)).obj K) i).hom =
        ((ModuleCat.extendRestrictScalarsAdj (algebraMap S T)).unit.app
            ((DerivedCategory.homologyFunctor (ModuleCat S) i).obj K) ≫
          (ModuleCat.restrictScalars (algebraMap S T)).map
            (flat_extend_scalars_homology_iso (S := S) (T := T) K i).hom) ≫
          (ModuleCat.restrictScalars (algebraMap S T)).map
            ((DerivedCategory.homologyFunctor (ModuleCat T) i).map
              ((flat_extend_scalars_mapDerivedCategory_iso (S := S) (T := T)).app K).hom) := by
  -- Route correction: isolate the remaining adjoint-side flat comparison as one bridge theorem,
  -- rather than expanding both sides inside the main comparison equality.
  have htarget :
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap S T)).homEquiv _ _)
          ((flat_derived_tensor_homology_iso (S := S) (T := T) K i).hom) =
        ((ModuleCat.extendRestrictScalarsAdj (algebraMap S T)).unit.app
            ((DerivedCategory.homologyFunctor (ModuleCat S) i).obj K) ≫
          (ModuleCat.restrictScalars (algebraMap S T)).map
            (flat_extend_scalars_homology_iso (S := S) (T := T) K i).hom) ≫
          (ModuleCat.restrictScalars (algebraMap S T)).map
            ((DerivedCategory.homologyFunctor (ModuleCat T) i).map
              ((flat_extend_scalars_mapDerivedCategory_iso (S := S) (T := T)).app K).hom) := by
    -- The right-hand side is already the ordinary module-adjunction transpose of the explicit
    -- flat homology isomorphism.
    simpa using
      (flat_derived_tensor_homology_iso_adjoint_eq
        (S := S) (T := T) (K := K) (i := i))
  -- TODO(Lemma 15.61.3): unfold `restrict_scalars_homology_iso` and the chosen
  -- `Q.objPreimage` model of `flat_extend_scalars_homology_iso`, then rewrite the unit term to
  -- the exact `leftDerivedNatIso` component used in `flat_extend_scalars_mapDerivedCategory_iso`.
  -- The exact adjunction side is now isolated in `htarget`; the remaining blocker is only the
  -- derived-unit identification.
  sorry

/-- Helper for Lemma 15.61.3: the flat outer comparison should be rewritten to the explicit flat
homology isomorphism. -/
private theorem flat_derived_tensor_homology_comparison_eq
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T]
    (K : DerivedCategory (ModuleCat S)) (i : ℤ) :
    derivedTensorWithAlgebraHomologyComparison T K i =
      (flat_derived_tensor_homology_iso (S := S) (T := T) K i).hom := by
  -- Compare both morphisms after applying the ordinary scalar-extension/restriction hom-set
  -- equivalence for `S → T`.
  refine ((ModuleCat.extendRestrictScalarsAdj (algebraMap S T)).homEquiv _ _).injective ?_
  rw [derived_tensor_homology_comparison_adjoint_eq (S := S) (T := T) (K := K) (i := i)]
  rw [flat_derived_tensor_homology_iso]
  -- On the derived side, rewrite the final comparison by adjunction naturality and then apply
  -- the isolated adjoint-side flat bridge.
  change _ =
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap S T)).homEquiv _ _)
      ((flat_extend_scalars_homology_iso (S := S) (T := T) K i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat T) i).map
          ((flat_extend_scalars_mapDerivedCategory_iso (S := S) (T := T)).app K).hom)
  rw [CategoryTheory.Adjunction.homEquiv_naturality_right]
  rw [CategoryTheory.Adjunction.homEquiv_unit]
  simpa [Category.assoc] using
    (flat_derived_tensor_homology_comparison_adjoint_bridge
      (S := S) (T := T) (K := K) (i := i))

/-- Helper for Lemma 15.61.3: every outer flat scalar-extension comparison is an isomorphism once
it is rewritten to the explicit flat homology isomorphism. -/
private theorem derived_tensor_homology_comparison_isIso_of_flat
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T]
    (K : DerivedCategory (ModuleCat S)) (i : ℤ) :
    IsIso (derivedTensorWithAlgebraHomologyComparison T K i) := by
  -- After rewriting to the explicit flat homology isomorphism, the goal is immediate from the
  -- isomorphism structure of `flat_derived_tensor_homology_iso`.
  rw [flat_derived_tensor_homology_comparison_eq (S := S) (T := T) (K := K) (i := i)]
  infer_instance

/-- Helper for Lemma 15.61.3: once the Chapter 10 base-change isomorphism is factored off, it
remains to show that the Tor-functoriality tail is an isomorphism. -/
private theorem tor_base_change_tail_isIso
    (aMap : A ⊗[R] R' →ₐ[R'] A')
    (bMap : R' ⊗[R] B →ₐ[R'] B')
    (i : ℕ) (hi : 0 < i)
    (haFlat :
      letI : Algebra (A ⊗[R] R') A' := aMap.toAlgebra
      Module.Flat (A ⊗[R] R') A')
    (hbFlat :
      letI : Algebra (R' ⊗[R] B) B' := bMap.toAlgebra
      Module.Flat (R' ⊗[R] B) B') :
    IsIso
      (tor_base_change_tail
        (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
        aMap bMap i) := by
  -- TODO(Lemma 15.61.3): use the source-faithful factorization of `tor_base_change_tail` into
  -- the two outer homology-comparison maps and the middle reassociation isomorphism, then combine
  -- the middle `IsIso` with flatness of `A'` and `B'`.
  sorry

-- Proof sketch: the first arrow is the owner flat base-change isomorphism from Chapter 10. The
-- second arrow is induced by `aMap` after converting `extendScalars` from `R' ⊗[R] A` to the
-- source-facing order `A ⊗[R] R'` via `Algebra.TensorProduct.commRight`, and the third arrow is
-- induced by `bMap`. In positive degree, the extra flatness hypotheses on `A'` and `B'` are used
-- to prove that this composite is an isomorphism.
/-- Lemma 15.61.3: for a commutative square of rings
`A ← R → B`, `A' ← R' → B'` with `R'` flat over `R`, `A'` flat over `A ⊗[R] R'`, and `B'`
flat over `R' ⊗[R] B`, together with the corresponding `R'`-algebra comparison maps
`A ⊗[R] R' → A'` and `R' ⊗[R] B → B'`, the canonical comparison from the base change of
`Tor_i^R(A, B)` to `Tor_i^{R'}(A', B')` is an isomorphism for every positive degree `i`. -/
theorem torBaseChangeComparison_isIso
    (aMap : A ⊗[R] R' →ₐ[R'] A')
    (bMap : R' ⊗[R] B →ₐ[R'] B')
    (i : ℕ) (hi : 0 < i)
    (haFlat :
      letI : Algebra (A ⊗[R] R') A' := aMap.toAlgebra
      Module.Flat (A ⊗[R] R') A')
    (hbFlat :
      letI : Algebra (R' ⊗[R] B) B' := bMap.toAlgebra
      Module.Flat (R' ⊗[R] B) B') :
    IsIso (torBaseChangeComparison aMap bMap i) := by
  letI : Algebra ATensor A' := aMap.toAlgebra
  letI : Algebra BTensor B' := bMap.toAlgebra
  letI : Module.Flat ATensor A' := haFlat
  letI : Module.Flat BTensor B' := hbFlat
  -- The first factor is the Chapter 10 base-change isomorphism, and the new tail theorem isolates
  -- the remaining source-faithful derived comparison.
  let _ :
      IsIso
        (torBaseChangeHom
          (algebraMap R R')
          (RingHom.flat_algebraMap_iff.mpr inferInstance)
          (of R A)
          (of R B)
          i) :=
    tor_base_change_initial_isIso (R := R) (R' := R') (A := A) (B := B) i
  let _ :
      IsIso
        (tor_base_change_tail
          (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
          aMap bMap i) :=
    tor_base_change_tail_isIso
      (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
      aMap bMap i hi haFlat hbFlat
  -- With both factors isolated as isomorphisms, the composite comparison is an isomorphism.
  let hcomp :
      IsIso
        (torBaseChangeHom
          (algebraMap R R')
          (RingHom.flat_algebraMap_iff.mpr inferInstance)
          (of R A)
          (of R B)
          i ≫
        tor_base_change_tail
          (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B')
          aMap bMap i) := by
    infer_instance
  simpa [torBaseChangeComparison] using hcomp

end

end
