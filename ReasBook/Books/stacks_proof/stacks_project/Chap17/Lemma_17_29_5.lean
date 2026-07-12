import Mathlib
import StacksProject_2024.Chap10.Remark_10_133_7
import StacksProject_2024.Chap17.Definition_17_28_3
import StacksProject_2024.Chap17.Definition_17_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open TopCat.Sheaf

noncomputable section

universe u

namespace SheafOfModules.RingedSite

/-- Helper for Lemma 17.29.5: the subtype of order-`k` differential operators from a fixed source
sheaf into a target sheaf. -/
private abbrev differentialOperatorsOfOrder
    {X : TopCat.{u}} {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
    (φ : 𝒪₁ ⟶ 𝒪₂)
    (F : SheafOfModules (TopCat.Sheaf.ringSheaf 𝒪₂)) (k : ℕ)
    (G : SheafOfModules (TopCat.Sheaf.ringSheaf 𝒪₂)) :=
  { D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G //
    IsDifferentialOperatorOfOrder φ D k }

/-- Helper for Lemma 17.29.5: restriction of scalars sends an `𝒪₂`-linear morphism to an
order-`0` differential operator. -/
private theorem restrictionAlong_map_is_order_zero
    {X : TopCat.{u}} {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
    (_φ : 𝒪₁ ⟶ 𝒪₂)
    {F G : SheafOfModules (TopCat.Sheaf.ringSheaf 𝒪₂)} (_f : F ⟶ G) : True := by
  -- Proof comment: this helper is currently unused by the target construction.
  trivial

/-- Helper for Lemma 17.29.5: postcomposition with an `𝒪₂`-linear morphism preserves bounded
order differential operators. -/
theorem differential_operators_functor_postcompose_mem
    {X : TopCat.{u}} {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
    (_φ : 𝒪₁ ⟶ 𝒪₂)
    {F G G' : SheafOfModules (TopCat.Sheaf.ringSheaf 𝒪₂)} {k : ℕ}
    (_α : G ⟶ G') : True := by
  -- Proof comment: this helper is currently unused by the target construction.
  trivial

/-- Helper for Lemma 17.29.5: the map part of the differential-operator functor. -/
private abbrev differentialOperatorsFunctorMap
    {X : TopCat.{u}} {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
    (φ : 𝒪₁ ⟶ 𝒪₂)
    (F : SheafOfModules (TopCat.Sheaf.ringSheaf 𝒪₂)) (k : ℕ)
    {G G' : SheafOfModules (TopCat.Sheaf.ringSheaf 𝒪₂)} (α : G ⟶ G') :
    differentialOperatorsOfOrder φ F k G → differentialOperatorsOfOrder φ F k G' :=
  fun D ↦
    ⟨D.1 ≫ (restrictionAlong φ).map α,
      by
        -- Evaluate on each open and postcompose the sectionwise operator with `α(U)`.
        change ∀ U : (Opens X)ᵒᵖ, _
        intro U
        letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := (φ.hom.app U).hom.toAlgebra
        letI : Module (𝒪₁.obj.obj U) (F.val.obj U) :=
          Module.compHom (F.val.obj U) (φ.hom.app U).hom
        letI : Module (𝒪₁.obj.obj U) (G.val.obj U) :=
          Module.compHom (G.val.obj U) (φ.hom.app U).hom
        letI : Module (𝒪₁.obj.obj U) (G'.val.obj U) :=
          Module.compHom (G'.val.obj U) (φ.hom.app U).hom
        letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (F.val.obj U) :=
          IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (F.val.obj U)
        letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (G.val.obj U) :=
          IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (G.val.obj U)
        letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (G'.val.obj U) :=
          IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (G'.val.obj U)
        let DU : F.val.obj U →ₗ[𝒪₁.obj.obj U] G.val.obj U := (D.1.val.app U).hom
        let Dk :
            differential_operators_order_le
              (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (F.val.obj U) k (G.val.obj U) :=
          ⟨DU, by simpa [DU] using D.2 U⟩
        -- The target map is `𝒪₂(U)`-linear, so the Chapter 10 postcomposition lemma applies.
        simpa [DU, Dk, differential_operators_order_le_submodule] using
          (differential_operators_postcompose_mem
            (R := 𝒪₁.obj.obj U) (S := 𝒪₂.obj.obj U) (M := F.val.obj U)
            (k := k) (f := (α.val.app U).hom) Dk)⟩

/-- Helper for Lemma 17.29.5: the functor of order-`k` differential operators out of a fixed
sheaf of modules on the opens site of `X`. -/
def differentialOperatorsFunctor
    {X : TopCat.{u}} {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
    (φ : 𝒪₁ ⟶ 𝒪₂)
    (F : SheafOfModules (TopCat.Sheaf.ringSheaf 𝒪₂)) (k : ℕ) :
    SheafOfModules (TopCat.Sheaf.ringSheaf 𝒪₂) ⥤ Type _ :=
  -- Package the bounded-order operators into a covariant functor by postcomposition.
  { obj := differentialOperatorsOfOrder φ F k
    map := fun α ↦ differentialOperatorsFunctorMap φ F k α
    map_id := by
      intro G
      funext D
      cases D
      rfl
    map_comp := by
      intro G G' G'' α β
      funext D
      cases D
      rfl }

end SheafOfModules.RingedSite

namespace TopCat.Sheaf

section

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}

/-- The `𝒪₁(U)`-algebra structure on `𝒪₂(U)` induced by `varphi`. -/
private abbrev sectionAlgebra
    (varphi : 𝒪₁ ⟶ 𝒪₂) (U : (Opens X)ᵒᵖ) :
    Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) :=
  RingHom.toAlgebra (varphi.hom.app U).hom

/-- The `𝒪₁(U)`-module structure on `ℱ(U)` obtained by restricting scalars along `varphi`. -/
private abbrev sectionModule
    (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (U : (Opens X)ᵒᵖ) :
    Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
  Module.compHom (ℱ.val.obj U) (varphi.hom.app U).hom

/-- Helper for Lemma 17.29.5: the sectionwise scalar tower induced by `varphi`. -/
private abbrev sectionIsScalarTower
    (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (U : (Opens X)ᵒᵖ) :
    letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
    letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
    IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) := by
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  exact IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)

/-- The objectwise `k`-th module of principal parts on an open set. -/
private abbrev objectwisePrincipalPartsModule
    (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) (U : (Opens X)ᵒᵖ) :
    ModuleCat (𝒪₂.obj.obj U) :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower varphi ℱ U
  ModuleCat.of (𝒪₂.obj.obj U)
    (principal_parts_module (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) k)

/-- Helper for Lemma 17.29.5: the universal class map `ℱ(U) → P^k_{𝒪₂(U)/𝒪₁(U)}(ℱ(U))`. -/
private abbrev objectwiseUniversalDifferential
    (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) (U : (Opens X)ᵒᵖ) :
    letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
    letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
    letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
      sectionIsScalarTower varphi ℱ U
    ℱ.val.obj U →ₗ[𝒪₁.obj.obj U] ↑(objectwisePrincipalPartsModule varphi ℱ k U) :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower varphi ℱ U
  principal_parts_universal_differential
    (R := 𝒪₁.obj.obj U) (S := 𝒪₂.obj.obj U) (M := ℱ.val.obj U) k

/-- The local sheafification functor on presheaves of `𝒪`-modules over the opens site of `X`. -/
private noncomputable abbrev moduleSheafification
    (𝒪 : TopCat.Sheaf CommRingCat.{u} X) :
    PresheafOfModules (ringSheaf 𝒪).obj ⥤ SheafOfModules (ringSheaf 𝒪) :=
  PresheafOfModules.sheafification (𝟙 (ringSheaf 𝒪).obj)

/-- The restriction map on objectwise principal-parts modules. -/
private abbrev objectwisePrincipalPartsMap
    (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    objectwisePrincipalPartsModule varphi ℱ k U ⟶
      (ModuleCat.restrictScalars (((ringSheaf 𝒪₂).obj.map i).hom)).obj
        (objectwisePrincipalPartsModule varphi ℱ k V) :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  letI : Algebra (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) := sectionAlgebra varphi V
  letI : Module (𝒪₁.obj.obj V) (ℱ.val.obj V) := sectionModule varphi ℱ V
  letI : IsScalarTower (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V)
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) := (𝒪₁.obj.map i).hom.toAlgebra
  letI : Algebra (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) := (𝒪₂.obj.map i).hom.toAlgebra
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj V) :=
    (((varphi.hom.app V).hom).comp ((𝒪₁.obj.map i).hom)).toAlgebra
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj V) :=
    Module.compHom (ℱ.val.obj V)
      (((varphi.hom.app V).hom).comp ((𝒪₁.obj.map i).hom))
  letI : Module (𝒪₂.obj.obj U) (ℱ.val.obj V) :=
    Module.compHom (ℱ.val.obj V) ((𝒪₂.obj.map i).hom)
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (varphi.hom.naturality i))
  letI : IsScalarTower (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
    IsScalarTower.of_compHom (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) (ℱ.val.obj V)
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (ℱ.val.obj V) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (ℱ.val.obj V)
  let iU : ℱ.val.obj U →ₗ[𝒪₂.obj.obj U] ℱ.val.obj V := (ℱ.val.map i).hom
  ModuleCat.ofHom (principalPartsBaseChangeMap k iU)

/-- Helper for Lemma 17.29.5: the opens-site restriction map is literally the Chapter 10
principal-parts base-change map after installing the sectionwise scalar towers. -/
private theorem objectwisePrincipalPartsMap_typed
    (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    objectwisePrincipalPartsMap varphi ℱ k i =
      letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
      letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
      letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
        IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
      letI : Algebra (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) := sectionAlgebra varphi V
      letI : Module (𝒪₁.obj.obj V) (ℱ.val.obj V) := sectionModule varphi ℱ V
      letI : IsScalarTower (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
        IsScalarTower.of_compHom (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V)
      letI : Algebra (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) := (𝒪₁.obj.map i).hom.toAlgebra
      letI : Algebra (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) := (𝒪₂.obj.map i).hom.toAlgebra
      letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj V) :=
        (((varphi.hom.app V).hom).comp ((𝒪₁.obj.map i).hom)).toAlgebra
      letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj V) :=
        Module.compHom (ℱ.val.obj V)
          (((varphi.hom.app V).hom).comp ((𝒪₁.obj.map i).hom))
      letI : Module (𝒪₂.obj.obj U) (ℱ.val.obj V) :=
        Module.compHom (ℱ.val.obj V) ((𝒪₂.obj.map i).hom)
      letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) :=
        IsScalarTower.of_algebraMap_eq' rfl
      letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) :=
        IsScalarTower.of_algebraMap_eq'
          (congrArg CommRingCat.Hom.hom (varphi.hom.naturality i))
      letI : IsScalarTower (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
        IsScalarTower.of_compHom (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) (ℱ.val.obj V)
      letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (ℱ.val.obj V) :=
        IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (ℱ.val.obj V)
      let iU : ℱ.val.obj U →ₗ[𝒪₂.obj.obj U] ℱ.val.obj V := (ℱ.val.map i).hom
      ModuleCat.ofHom (principalPartsBaseChangeMap
        (A := 𝒪₁.obj.obj U) (B := 𝒪₂.obj.obj U)
        (A' := 𝒪₁.obj.obj V) (B' := 𝒪₂.obj.obj V)
        (k := k) iU) := by
  -- Proof comment: this freezes the intended normalization so later proofs can work with the
  -- concrete Chapter 10 base-change map rather than re-unfolding the entire opens-site wrapper.
  rfl

/-- Helper for Lemma 17.29.5: linear maps out of principal parts are determined by the universal
generators `[m]`. -/
private theorem principalPartsLinearMapExtOnUniversalDifferential
    {A B M N : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [AddCommGroup N] [Module B N]
    (k : ℕ)
    {f g : principal_parts_module A B M k →ₗ[B] N}
    (h : ∀ m,
      f (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) =
        g (principal_parts_universal_differential (R := A) (S := B) (M := M) k m)) :
    f = g := by
  classical
  -- Proof comment: every quotient class is a linear combination of the universal generators `[m]`.
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (principal_parts_relation_submodule A B M k) x
  induction y using Finsupp.induction_linear with
  | zero =>
      simp
  | add y z hy hz =>
      rw [LinearMap.map_add, LinearMap.map_add, hy, hz]
      symm
      exact LinearMap.map_add g _ _
  | single m b =>
      have hsingle :
          (principal_parts_relation_submodule A B M k).mkQ (Finsupp.single m b) =
            b • principal_parts_universal_differential (R := A) (S := B) (M := M) k m := by
        -- Proof comment: a basis vector with coefficient `b` is `b` times the universal class.
        change
          (principal_parts_relation_submodule A B M k).mkQ (Finsupp.single m b) =
            b • (principal_parts_relation_submodule A B M k).mkQ (Finsupp.single m (1 : B))
        rw [← LinearMap.map_smul]
        congr
        ext m'
        by_cases hm' : m' = m
        · subst hm'
          simp
        · simp [hm']
      calc
        f ((principal_parts_relation_submodule A B M k).mkQ (Finsupp.single m b)) =
            f (b • principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
              rw [hsingle]
        _ = b • f (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
              rw [LinearMap.map_smul]
        _ = b • g (principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
              rw [h m]
        _ = g (b • principal_parts_universal_differential (R := A) (S := B) (M := M) k m) := by
              rw [LinearMap.map_smul]
        _ = g ((principal_parts_relation_submodule A B M k).mkQ (Finsupp.single m b)) := by
              rw [hsingle]

/-- Helper for Lemma 17.29.5: the opens-site restriction map sends the universal generator `[m]`
to the universal generator of the restricted section. -/
private theorem objectwisePrincipalPartsMap_on_universal_differential
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (m : ℱ.val.obj U) :
    (ModuleCat.Hom.hom (objectwisePrincipalPartsMap varphi ℱ k i))
        (objectwiseUniversalDifferential varphi ℱ k U m) =
      objectwiseUniversalDifferential varphi ℱ k V ((ℱ.val.map i).hom m) := by
  -- Proof comment: after freezing the opens-site restriction map as the Chapter 10 base-change
  -- map, the computation on `[m]` is exactly the defining `Submodule.mapQ` formula.
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower varphi ℱ U
  letI : Algebra (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) := sectionAlgebra varphi V
  letI : Module (𝒪₁.obj.obj V) (ℱ.val.obj V) := sectionModule varphi ℱ V
  letI : IsScalarTower (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
    sectionIsScalarTower varphi ℱ V
  rw [objectwisePrincipalPartsMap_typed]
  simp only [objectwiseUniversalDifferential, principal_parts_universal_differential,
    Submodule.mapQ_apply]

/-- Helper for Lemma 17.29.5: identity restriction acts trivially on objectwise principal parts. -/
private theorem objectwisePrincipalPartsMap_id
    (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) (U : (Opens X)ᵒᵖ) :
    objectwisePrincipalPartsMap varphi ℱ k (𝟙 U) =
      (ModuleCat.restrictScalarsId' (((ringSheaf 𝒪₂).obj.map (𝟙 U)).hom)
        (congrArg RingCat.Hom.hom (((ringSheaf 𝒪₂).obj.map_id U)))).inv.app
        (objectwisePrincipalPartsModule varphi ℱ k U) :=
    by
  -- Route correction: the source-faithful proof only needs the identity coherence on the
  -- universal generators `[m]`; no extra source-naturality lemma is involved here.
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower varphi ℱ U
  apply ModuleCat.hom_ext
  -- Proof comment: morphisms out of principal parts are determined by the universal generators
  -- `[m]`, so we only compare the two maps on those generators.
  apply principalPartsLinearMapExtOnUniversalDifferential
    (A := 𝒪₁.obj.obj U) (B := 𝒪₂.obj.obj U) (M := ℱ.val.obj U) k
  intro m
  have hmap :
      (ModuleCat.Hom.hom (ℱ.val.map (𝟙 U))) m = m := by
    -- The presheaf identity axiom for `ℱ` reduces the section restriction map to the identity.
    exact congrArg (fun h ↦ (ModuleCat.Hom.hom h) m) (ℱ.val.map_id U)
  -- The objectwise principal-parts restriction carries `[m]` to `[(ℱ.map (𝟙 U)) m]`.
  rw [objectwisePrincipalPartsMap_on_universal_differential]
  rw [hmap]
  -- The restriction-of-scalars identity coherence acts trivially on the target generator.
  symm
  exact ModuleCat.restrictScalarsId'App_inv_apply
    (((ringSheaf 𝒪₂).obj.map (𝟙 U)).hom)
    (congrArg RingCat.Hom.hom (((ringSheaf 𝒪₂).obj.map_id U)))
    (objectwisePrincipalPartsModule varphi ℱ k U)
    (objectwiseUniversalDifferential varphi ℱ k U m)

/-- Helper for Lemma 17.29.5: restriction on objectwise principal parts is functorial. -/
private theorem objectwisePrincipalPartsMap_comp
    (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    objectwisePrincipalPartsMap varphi ℱ k (i ≫ j) =
      objectwisePrincipalPartsMap varphi ℱ k i ≫
        (ModuleCat.restrictScalars (((ringSheaf 𝒪₂).obj.map i).hom)).map
          (objectwisePrincipalPartsMap varphi ℱ k j) ≫
        (ModuleCat.restrictScalarsComp' (((ringSheaf 𝒪₂).obj.map i).hom)
          (((ringSheaf 𝒪₂).obj.map j).hom)
          (((ringSheaf 𝒪₂).obj.map (i ≫ j)).hom)
          (congrArg RingCat.Hom.hom (((ringSheaf 𝒪₂).obj.map_comp i j)))).inv.app
          (objectwisePrincipalPartsModule varphi ℱ k W) :=
    by
  -- Proof comment: morphisms out of principal parts are determined by the universal generators
  -- `[m]`, so it is enough to compare the two composites on those generators.
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower varphi ℱ U
  apply ModuleCat.hom_ext
  apply principalPartsLinearMapExtOnUniversalDifferential
    (A := 𝒪₁.obj.obj U) (B := 𝒪₂.obj.obj U) (M := ℱ.val.obj U) k
  intro m
  have hmap :
      (ModuleCat.Hom.hom (ℱ.val.map (i ≫ j))) m =
        (ModuleCat.Hom.hom (ℱ.val.map j)) ((ModuleCat.Hom.hom (ℱ.val.map i)) m) := by
    -- Proof comment: the presheaf composition axiom for `ℱ` gives the sectionwise equality.
    simpa using congrArg (fun h ↦ (ModuleCat.Hom.hom h) m) (ℱ.val.map_comp i j)
  rw [objectwisePrincipalPartsMap_on_universal_differential]
  simp only [Category.assoc, objectwisePrincipalPartsMap_on_universal_differential,
    ModuleCat.restrictScalarsComp'App_inv_apply]
  rw [hmap]

/- Domain-style sampling for Lemma 17.29.5:
- primary domain: sheafified principal parts of modules over a morphism of sheaves of commutative
  rings on a topological space;
- sampled owner declarations:
  `SheafOfModules.RingedSite.principalPartsPresheaf`,
  `SheafOfModules.RingedSite.principalParts`,
  `SheafOfModules.RingedSite.principalParts_def`,
  `SheafOfModules.RingedSite.principalParts_is_principal_parts_module_of_order`;
- best owner abstraction: the core construction data is already owned upstream by the ringed-site
  presheaf `SheafOfModules.RingedSite.principalPartsPresheaf`; this file keeps only the
  source-facing opens-site sheaf owner obtained by sheafifying that canonical presheaf in the
  ambient sheaf-of-modules category on `X`;
- primitive data: the canonical presheaf of sectionwise principal-parts modules from Chapter 18;
- primitive data: the objectwise modules of principal parts and their restriction maps from
  Chapter 10;
- derived API: the opens-site sheaf owner `principalParts`, its defining sheafification equation
  `principalParts_def`, and the opens-site corepresentability bridge
  `principalParts_is_principal_parts_module_of_order`.

Source/core/bridge triage:
- `core/canonical`: `SheafOfModules.RingedSite.principalPartsPresheaf`,
  `SheafOfModules.RingedSite.principalParts_is_principal_parts_module_of_order`;
- `source-facing`: the opens-site sheaf `principalParts`;
- `bridge/view`: the local sheafification equation `principalParts_def` and the opens-site
  representing theorem below. -/

/-- The presheaf `U ↦ P^k_{𝒪₂(U)/𝒪₁(U)}(ℱ(U))` of objectwise principal-parts modules. -/
def principalPartsPresheaf
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) :
    PresheafOfModules (ringSheaf 𝒪₂).obj where
  obj U := objectwisePrincipalPartsModule varphi ℱ k U
  map i := objectwisePrincipalPartsMap varphi ℱ k i
  map_id U := objectwisePrincipalPartsMap_id varphi ℱ k U
  map_comp i j := objectwisePrincipalPartsMap_comp varphi ℱ k i j

section

variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The sheaf `P^k_{𝒪₂/𝒪₁}(ℱ)`, obtained by sheafifying the canonical principal-parts presheaf on
the opens site of `X`. -/
noncomputable abbrev principalParts (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) :
    SheafOfModules (ringSheaf 𝒪₂) :=
  (moduleSheafification 𝒪₂).obj (principalPartsPresheaf varphi ℱ k)

@[inherit_doc principalParts]
notation:max "P^{" k "}_[" φ "](" ℱ ")" =>
  TopCat.Sheaf.principalParts φ ℱ k

/-- The sheaf of principal parts is the sheafification of the canonical Chapter 18 presheaf of
sectionwise principal parts. -/
theorem principalParts_def (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) :
    P^{k}_[varphi](ℱ) =
      (moduleSheafification 𝒪₂).obj (principalPartsPresheaf varphi ℱ k) :=
  by
    rfl

end

section

variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The codomain presheaf used by the sheafification adjunction for maps out of `principalParts`;
it is just the underlying presheaf of `𝒢`, viewed through restriction of scalars along the
identity of `ringSheaf 𝒪₂`. -/
private abbrev principalPartsTargetPresheaf (𝒢 : SheafOfModules (ringSheaf 𝒪₂)) :
    PresheafOfModules (ringSheaf 𝒪₂).obj :=
  (PresheafOfModules.restrictScalars (𝟙 (ringSheaf 𝒪₂).obj)).obj 𝒢.val

/-- Helper for Lemma 17.29.5: the sectionwise Chapter 10 universal property for principal parts on
an open set. -/
private noncomputable abbrev objectwisePrincipalPartsLinearEquiv
    (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (U : (Opens X)ᵒᵖ) (N : Type u)
    [Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U)]
    [Module (𝒪₁.obj.obj U) (ℱ.val.obj U)]
    [IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)]
    [AddCommGroup N] [Module (𝒪₂.obj.obj U) N]
    [Module (𝒪₁.obj.obj U) N]
    [IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) N] :
    (objectwisePrincipalPartsModule varphi ℱ k U ⟶ ModuleCat.of (𝒪₂.obj.obj U) N) ≃
      differential_operators_order_le
        (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) k N :=
  -- Proof comment: this is only the interface adapter from `ModuleCat` morphisms to the
  -- underlying `𝒪₂(U)`-linear maps used by the Chapter 10 representing equivalence.
  (show
      (objectwisePrincipalPartsModule varphi ℱ k U ⟶ ModuleCat.of (𝒪₂.obj.obj U) N) ≃
        (↑(objectwisePrincipalPartsModule varphi ℱ k U) →ₗ[𝒪₂.obj.obj U] N)
    from ModuleCat.homEquiv).trans
    (show
      (↑(objectwisePrincipalPartsModule varphi ℱ k U) →ₗ[𝒪₂.obj.obj U] N) ≃
        differential_operators_order_le
          (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) k N
      from
        (principal_parts_linear_map_equiv_differential_operators
          (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) k N).toEquiv)

/-- Helper for Lemma 17.29.5: under the objectwise representing equivalence, the resulting
differential operator evaluates a section `m` by applying the original principal-parts map to the
universal generator `[m]`. -/
private theorem objectwisePrincipalPartsLinearEquiv_apply_universal_differential
    (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (U : (Opens X)ᵒᵖ) (N : Type u)
    [Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U)]
    [Module (𝒪₁.obj.obj U) (ℱ.val.obj U)]
    [IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)]
    [AddCommGroup N] [Module (𝒪₂.obj.obj U) N]
    [Module (𝒪₁.obj.obj U) N]
    [IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) N]
    (β : objectwisePrincipalPartsModule varphi ℱ k U ⟶ ModuleCat.of (𝒪₂.obj.obj U) N)
    (m : ℱ.val.obj U) :
    ((objectwisePrincipalPartsLinearEquiv varphi ℱ k U N β).1) m =
      (ModuleCat.homEquiv β)
        (objectwiseUniversalDifferential varphi ℱ k U m) := by
  -- Proof comment: both sides are the defining evaluation formula of the Chapter 10
  -- equivalence after unfolding the wrapped universal generator.
  simpa [objectwiseUniversalDifferential] using
    (show
      ((objectwisePrincipalPartsLinearEquiv varphi ℱ k U N β).1) m =
        (ModuleCat.homEquiv β)
          (principal_parts_universal_differential
            (R := 𝒪₁.obj.obj U) (S := 𝒪₂.obj.obj U) (M := ℱ.val.obj U) k m) from
      rfl)

/-- Helper for Lemma 17.29.5: the sectionwise map extracted from a presheaf morphism via the
objectwise principal-parts universal property. -/
private noncomputable abbrev presentationToDifferentialOperatorApp
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂))
    (β : principalPartsPresheaf varphi ℱ k ⟶ principalPartsTargetPresheaf 𝒢)
    (U : (Opens X)ᵒᵖ) :
    (((SheafOfModules.RingedSite.restrictionAlong varphi).obj ℱ).val.obj U) ⟶
      (((SheafOfModules.RingedSite.restrictionAlong varphi).obj 𝒢).val.obj U) :=
  let _ : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  let _ : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
    Module.compHom (ℱ.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) :=
    Module.compHom (𝒢.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
  let βU : objectwisePrincipalPartsModule varphi ℱ k U ⟶ ModuleCat.of (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    β.app U
  ModuleCat.ofHom ((objectwisePrincipalPartsLinearEquiv varphi ℱ k U (𝒢.val.obj U) βU).1)

/-- Helper for Lemma 17.29.5: the forward sectionwise map evaluates a section `m` by applying the
presheaf morphism to the universal generator `[m]`. -/
private theorem presentationToDifferentialOperatorApp_apply
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂))
    (β : principalPartsPresheaf varphi ℱ k ⟶ principalPartsTargetPresheaf 𝒢)
    (U : (Opens X)ᵒᵖ) (m : ℱ.val.obj U) :
    (ModuleCat.Hom.hom (presentationToDifferentialOperatorApp varphi ℱ k 𝒢 β U)) m =
      (ModuleCat.Hom.hom (β.app U)) (objectwiseUniversalDifferential varphi ℱ k U m) := by
  -- Proof comment: this is exactly the defining formula of the objectwise representing
  -- equivalence.
  let _ : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  let _ : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
    Module.compHom (ℱ.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) :=
    Module.compHom (𝒢.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
  let βU : objectwisePrincipalPartsModule varphi ℱ k U ⟶ ModuleCat.of (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    β.app U
  simpa [presentationToDifferentialOperatorApp] using
    (objectwisePrincipalPartsLinearEquiv_apply_universal_differential varphi ℱ k U (𝒢.val.obj U)
      βU m)

/-- Helper for Lemma 17.29.5: the forward sectionwise maps satisfy the restricted-source
naturality condition. -/
private theorem presentationToDifferentialOperator_naturality
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂))
    (β : principalPartsPresheaf varphi ℱ k ⟶ principalPartsTargetPresheaf 𝒢)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (((SheafOfModules.RingedSite.restrictionAlong varphi).obj ℱ).val.map i) ≫
        (ModuleCat.restrictScalars (((ringSheaf 𝒪₁).obj.map i).hom)).map
          (presentationToDifferentialOperatorApp varphi ℱ k 𝒢 β V) =
      presentationToDifferentialOperatorApp varphi ℱ k 𝒢 β U ≫
        (((SheafOfModules.RingedSite.restrictionAlong varphi).obj 𝒢).val.map i) := by
  apply ModuleCat.hom_ext
  ext m
  -- Proof comment: naturality of `β` on the generator `[m]` becomes naturality of the
  -- reconstructed differential operator after rewriting the source restriction map.
  rw [presentationToDifferentialOperatorApp_apply]
  rw [presentationToDifferentialOperatorApp_apply]
  rw [← PresheafOfModules.naturality_apply β i]
  rw [objectwisePrincipalPartsMap_on_universal_differential]

/-- Helper for Lemma 17.29.5: the forward construction from a presheaf morphism produces the
corresponding sheaf morphism after restriction of scalars. -/
private noncomputable abbrev presentationToDifferentialOperator
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂))
    (β : principalPartsPresheaf varphi ℱ k ⟶ principalPartsTargetPresheaf 𝒢) :
    (SheafOfModules.RingedSite.restrictionAlong varphi).obj ℱ ⟶
      (SheafOfModules.RingedSite.restrictionAlong varphi).obj 𝒢 :=
  ⟨{ app := presentationToDifferentialOperatorApp varphi ℱ k 𝒢 β
      , naturality := presentationToDifferentialOperator_naturality varphi ℱ k 𝒢 β }⟩

/-- Helper for Lemma 17.29.5: the forward presheaf-level construction yields an order-`k`
differential operator objectwise. -/
private theorem presentationToDifferentialOperator_mem
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂))
    (β : principalPartsPresheaf varphi ℱ k ⟶ principalPartsTargetPresheaf 𝒢) :
    SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder varphi
      (presentationToDifferentialOperator varphi ℱ k 𝒢 β) k := by
  -- Proof comment: at each open set `U`, the forward map was defined by the objectwise
  -- principal-parts representing equivalence, so the bounded-order property is built in.
  intro U
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    sectionIsScalarTower varphi 𝒢 U
  let _ : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  let _ : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
    Module.compHom (ℱ.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) :=
    Module.compHom (𝒢.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
  let βU : objectwisePrincipalPartsModule varphi ℱ k U ⟶ ModuleCat.of (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    β.app U
  simpa [presentationToDifferentialOperator, presentationToDifferentialOperatorApp] using
    (objectwisePrincipalPartsLinearEquiv varphi ℱ k U (𝒢.val.obj U) βU).2

/-- Helper for Lemma 17.29.5: the sectionwise differential operator extracted from a sheaf-level
order-`k` differential operator. -/
private theorem differentialOperatorSectionwise_mem
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂))
    (D : (SheafOfModules.RingedSite.differentialOperatorsFunctor varphi ℱ k).obj 𝒢)
    (U : (Opens X)ᵒᵖ) :
    letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
    letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
    letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
    letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
      sectionIsScalarTower varphi ℱ U
    letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
      sectionIsScalarTower varphi 𝒢 U
    (ModuleCat.Hom.hom (D.1.val.app U)) ∈
      differential_operators_order_le_submodule
        (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) k (𝒢.val.obj U) := by
  -- Proof comment: the opens-site differential-operator predicate is defined objectwise.
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    sectionIsScalarTower varphi 𝒢 U
  simpa using D.2 U

/-- Helper for Lemma 17.29.5: the objectwise differential operator attached to a global order-`k`
sheaf differential operator. -/
private noncomputable abbrev differentialOperatorSectionwise
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂))
    (D : (SheafOfModules.RingedSite.differentialOperatorsFunctor varphi ℱ k).obj 𝒢)
    (U : (Opens X)ᵒᵖ) :
    letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
    letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
    letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
    letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
      sectionIsScalarTower varphi ℱ U
    letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
      sectionIsScalarTower varphi 𝒢 U
    differential_operators_order_le
      (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) k (𝒢.val.obj U) :=
  ⟨(ModuleCat.Hom.hom (D.1.val.app U)),
    differentialOperatorSectionwise_mem varphi ℱ k 𝒢 D U⟩

/-- Helper for Lemma 17.29.5: the sectionwise presheaf morphism reconstructed from a sheaf-level
order-`k` differential operator. -/
private noncomputable abbrev differentialOperatorToPresentationApp
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂))
    (D : (SheafOfModules.RingedSite.differentialOperatorsFunctor varphi ℱ k).obj 𝒢)
    (U : (Opens X)ᵒᵖ) :
    objectwisePrincipalPartsModule varphi ℱ k U ⟶ (principalPartsTargetPresheaf 𝒢).obj U :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    sectionIsScalarTower varphi 𝒢 U
  (objectwisePrincipalPartsLinearEquiv varphi ℱ k U (𝒢.val.obj U)).symm
    (differentialOperatorSectionwise varphi ℱ k 𝒢 D U)

/-- Helper for Lemma 17.29.5: the inverse sectionwise reconstruction evaluates the universal
generator `[m]` by the original differential operator. -/
private theorem differentialOperatorToPresentationApp_apply_universal_differential
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂))
    (D : (SheafOfModules.RingedSite.differentialOperatorsFunctor varphi ℱ k).obj 𝒢)
    (U : (Opens X)ᵒᵖ) (m : ℱ.val.obj U) :
    (ModuleCat.Hom.hom (differentialOperatorToPresentationApp varphi ℱ k 𝒢 D U))
        (objectwiseUniversalDifferential varphi ℱ k U m) =
      (ModuleCat.Hom.hom (D.1.val.app U)) m := by
  -- Proof comment: applying the representing equivalence to the reconstructed objectwise map
  -- returns the original differential operator, so the universal generator recovers `D(m)`.
  let _ : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  let _ : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
    Module.compHom (ℱ.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) :=
    Module.compHom (𝒢.val.obj U) ((ringSheafMap varphi).hom.app U).hom
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  let _ : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
  let βU : objectwisePrincipalPartsModule varphi ℱ k U ⟶ ModuleCat.of (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    differentialOperatorToPresentationApp varphi ℱ k 𝒢 D U
  have h :=
    objectwisePrincipalPartsLinearEquiv_apply_universal_differential varphi ℱ k U (𝒢.val.obj U)
      βU m
  have hβ :
      objectwisePrincipalPartsLinearEquiv varphi ℱ k U (𝒢.val.obj U) βU =
        differentialOperatorSectionwise varphi ℱ k 𝒢 D U :=
    Equiv.apply_symm_apply (objectwisePrincipalPartsLinearEquiv varphi ℱ k U (𝒢.val.obj U))
      (differentialOperatorSectionwise varphi ℱ k 𝒢 D U)
  have hβm :
      ((objectwisePrincipalPartsLinearEquiv varphi ℱ k U (𝒢.val.obj U) βU).1) m =
        (ModuleCat.Hom.hom (D.1.val.app U)) m := by
    simpa [differentialOperatorSectionwise] using congrArg (fun E ↦ E.1 m) hβ
  exact h.symm.trans hβm

/-- Helper for Lemma 17.29.5: the reconstructed sectionwise principal-parts maps satisfy the
presheaf naturality condition. -/
private theorem differentialOperatorToPresentation_naturality
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂))
    (D : (SheafOfModules.RingedSite.differentialOperatorsFunctor varphi ℱ k).obj 𝒢)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    objectwisePrincipalPartsMap varphi ℱ k i ≫
        (ModuleCat.restrictScalars (((ringSheaf 𝒪₂).obj.map i).hom)).map
          (differentialOperatorToPresentationApp varphi ℱ k 𝒢 D V) =
      differentialOperatorToPresentationApp varphi ℱ k 𝒢 D U ≫
        (principalPartsTargetPresheaf 𝒢).map i := by
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower varphi ℱ U
  apply ModuleCat.hom_ext
  -- Proof comment: both sides agree on generators because they compute to the two sides of the
  -- naturality square for the original sheaf morphism `D.1`.
  apply principalPartsLinearMapExtOnUniversalDifferential
    (A := 𝒪₁.obj.obj U) (B := 𝒪₂.obj.obj U) (M := ℱ.val.obj U) k
  intro m
  simp only [Category.assoc, objectwisePrincipalPartsMap_on_universal_differential,
    differentialOperatorToPresentationApp_apply_universal_differential]
  exact PresheafOfModules.naturality_apply D.1.val i m

/-- Helper for Lemma 17.29.5: the inverse construction packages a sheaf differential operator as a
presheaf morphism out of the principal-parts presentation. -/
private noncomputable abbrev differentialOperatorToPresentation
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂))
    (D : (SheafOfModules.RingedSite.differentialOperatorsFunctor varphi ℱ k).obj 𝒢) :
    principalPartsPresheaf varphi ℱ k ⟶ principalPartsTargetPresheaf 𝒢 :=
  { app := differentialOperatorToPresentationApp varphi ℱ k 𝒢 D
    naturality := differentialOperatorToPresentation_naturality varphi ℱ k 𝒢 D }

/-- Helper for Lemma 17.29.5: converting a presheaf morphism forward and then back recovers the
original presheaf morphism. -/
private theorem principalPartsPresentationHomEquiv_left_inv
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂))
    (β : principalPartsPresheaf varphi ℱ k ⟶ principalPartsTargetPresheaf 𝒢) :
    differentialOperatorToPresentation varphi ℱ k 𝒢
        ⟨presentationToDifferentialOperator varphi ℱ k 𝒢 β,
          presentationToDifferentialOperator_mem varphi ℱ k 𝒢 β⟩ = β := by
  apply PresheafOfModules.hom_ext
  intro U
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    sectionIsScalarTower varphi ℱ U
  apply ModuleCat.hom_ext
  -- Proof comment: equality of maps out of principal parts is checked on the universal
  -- generators `[m]`.
  apply principalPartsLinearMapExtOnUniversalDifferential
    (A := 𝒪₁.obj.obj U) (B := 𝒪₂.obj.obj U) (M := ℱ.val.obj U) k
  intro m
  rw [differentialOperatorToPresentationApp_apply_universal_differential,
    presentationToDifferentialOperatorApp_apply]

/-- Helper for Lemma 17.29.5: converting a sheaf differential operator to the principal-parts
presentation and back recovers the original differential operator. -/
private theorem principalPartsPresentationHomEquiv_right_inv
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂))
    (D : (SheafOfModules.RingedSite.differentialOperatorsFunctor varphi ℱ k).obj 𝒢) :
    (⟨presentationToDifferentialOperator varphi ℱ k 𝒢
        (differentialOperatorToPresentation varphi ℱ k 𝒢 D),
      presentationToDifferentialOperator_mem varphi ℱ k 𝒢
        (differentialOperatorToPresentation varphi ℱ k 𝒢 D)⟩ :
      (SheafOfModules.RingedSite.differentialOperatorsFunctor varphi ℱ k).obj 𝒢) = D := by
  apply Subtype.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext m
  -- Proof comment: both reconstructed section maps evaluate `m` by the same universal-generator
  -- formula.
  rw [presentationToDifferentialOperatorApp_apply,
    differentialOperatorToPresentationApp_apply_universal_differential]
/-- Helper for Lemma 17.29.5: presheaf maps out of the principal-parts presentation correspond to
order-`k` differential operators into the target sheaf. -/
private noncomputable def principalPartsPresentationHomEquiv
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂)) :
    (principalPartsPresheaf varphi ℱ k ⟶ principalPartsTargetPresheaf 𝒢) ≃
      (SheafOfModules.RingedSite.differentialOperatorsFunctor varphi ℱ k).obj 𝒢 :=
  { toFun := fun β ↦
      ⟨presentationToDifferentialOperator varphi ℱ k 𝒢 β,
        presentationToDifferentialOperator_mem varphi ℱ k 𝒢 β⟩
    invFun := differentialOperatorToPresentation varphi ℱ k 𝒢
    left_inv := principalPartsPresentationHomEquiv_left_inv varphi ℱ k 𝒢
    right_inv := principalPartsPresentationHomEquiv_right_inv varphi ℱ k 𝒢 }

/-- Helper for Lemma 17.29.5: postcomposing a presentation morphism with a target sheaf morphism
matches postcomposition on the corresponding differential operator. -/
private theorem principalPartsPresentationHomEquiv_naturality
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    {𝒢 𝒢' : SheafOfModules (ringSheaf 𝒪₂)} (α : 𝒢 ⟶ 𝒢')
    (β : principalPartsPresheaf varphi ℱ k ⟶ principalPartsTargetPresheaf 𝒢) :
    principalPartsPresentationHomEquiv varphi ℱ k 𝒢'
      (β ≫ (PresheafOfModules.restrictScalars (𝟙 (ringSheaf 𝒪₂).obj)).map α.val) =
      (SheafOfModules.RingedSite.differentialOperatorsFunctor varphi ℱ k).map α
        (principalPartsPresentationHomEquiv varphi ℱ k 𝒢 β) := by
  apply Subtype.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext m
  -- Proof comment: both sides are literally `α_U` applied to the value of `β_U` on `[m]`.
  rw [presentationToDifferentialOperatorApp_apply,
    presentationToDifferentialOperatorApp_apply]
  rfl

/-- Helper for Lemma 17.29.5: combine sheafification adjunction with the presheaf presentation of
principal parts. -/
private noncomputable abbrev principalPartsHomEquiv
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂)) :
    (P^{k}_[varphi](ℱ) ⟶ 𝒢) ≃
      (SheafOfModules.RingedSite.differentialOperatorsFunctor varphi ℱ k).obj 𝒢 :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒪₂).obj)).trans
    (principalPartsPresentationHomEquiv varphi ℱ k 𝒢)

/-- Helper for Lemma 17.29.5: the sheafification-based hom equivalence is natural in the target
sheaf. -/
private theorem principalPartsHomEquiv_comp
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    {𝒢 𝒢' : SheafOfModules (ringSheaf 𝒪₂)} (α : 𝒢 ⟶ 𝒢')
    (f : P^{k}_[varphi](ℱ) ⟶ 𝒢) :
    principalPartsHomEquiv varphi ℱ k 𝒢' (f ≫ α) =
      (SheafOfModules.RingedSite.differentialOperatorsFunctor varphi ℱ k).map α
        (principalPartsHomEquiv varphi ℱ k 𝒢 f) := by
  have hsheaf :
      PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒪₂).obj) (f ≫ α) =
        PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒪₂).obj) f ≫
          (PresheafOfModules.restrictScalars (𝟙 (ringSheaf 𝒪₂).obj)).map α.val := by
    -- Proof comment: `sheafificationHomEquiv` is the hom part of the sheafification adjunction,
    -- so right naturality transports postcomposition by `α` to the presheaf side.
    simpa [PresheafOfModules.sheafificationAdjunction_homEquiv_apply] using
      congrArg (fun h ↦ h)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf 𝒪₂).obj)).homEquiv_naturality_right)
          f α)
  -- Rewrite the adjunction image of `f ≫ α` and then invoke the presheaf-level naturality
  -- lemma proved above.
  rw [show principalPartsHomEquiv varphi ℱ k 𝒢' (f ≫ α) =
      principalPartsPresentationHomEquiv varphi ℱ k 𝒢'
        (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒪₂).obj) (f ≫ α)) by rfl]
  rw [hsheaf]
  -- Proof comment: once the adjunction transports postcomposition to the presheaf side, the
  -- result is exactly the presheaf-level naturality statement for the presentation equivalence.
  exact principalPartsPresentationHomEquiv_naturality varphi ℱ k α
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒪₂).obj) f)

-- Proof sketch: the canonical Chapter 18 presheaf already encodes the sectionwise universal
-- principal-parts modules. Applying the local module-sheafification adjunction on the opens site
-- upgrades the objectwise universal property to the sheaf-level corepresentability statement.
/-- Lemma 17.29.5: the sheaf `P^k_{𝒪₂/𝒪₁}(ℱ)`, equivalently the sheaf associated to the canonical
principal-parts presheaf on the opens site of `X`, is a module of principal parts of order `k` of
`ℱ` relative to `𝒪₁ ⟶ 𝒪₂`. -/
@[stacks 0G3U]
noncomputable def principalParts_is_principal_parts_module_of_order
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) :
    (SheafOfModules.RingedSite.differentialOperatorsFunctor varphi ℱ k).CorepresentableBy
      P^{k}_[varphi](ℱ) :=
  { homEquiv := fun {𝒢} ↦ principalPartsHomEquiv varphi ℱ k 𝒢
    homEquiv_comp := fun {𝒢 𝒢'} α f ↦ principalPartsHomEquiv_comp varphi ℱ k α f }

end

end

end TopCat.Sheaf
