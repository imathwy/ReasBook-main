import Mathlib
import StacksProject_2024.Chap06.Example_6_9_3
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_4_1
import StacksProject_2024.Chap17.Definition_17_10_6
import StacksProject_2024.Chap17.Lemma_17_10_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace
open TopCat
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

private instance : PreservesLimits (forget (CommAlgCat.{0} ℝ)) := by
  simpa using
    (inferInstance :
      PreservesLimits ((commAlgCatEquivUnder (CommRingCat.of ℝ)).functor ⋙
        Under.forget (CommRingCat.of ℝ) ⋙ forget CommRingCat))

private instance opensMapOfRestrictFinal {X : RingedSpace.{u}} (U : Opens X) :
    Functor.Final (Opens.map (X.ofRestrict U.isOpenEmbedding).hom.base) := by
  let hU : IsOpenMap U.inclusion' := U.isOpenEmbedding.isOpenMap
  simpa using
    (CategoryTheory.Functor.final_of_adjunction hU.adjunction :
      Functor.Final (Opens.map U.inclusion'))

/- Domain-style sampling for Example 17.10.9:
- primary domain: morphisms between restricted free `\mathcal O_X`-module sheaves and the
  canonical module-sheaf owner attached to free `Γ(U, \mathcal O_U)`-modules on the restricted
  ringed space `X|_U`;
- inspected owner declarations:
  `globalSectionsModuleFunctor`,
  `associatedModuleSheaf`,
  `SheafOfModules.pullbackObjFreeIso`,
  `continuousRealFunctionsSheaf`;
- best owner abstraction: on `X|_U`, the source-facing question is whether a restricted free-sheaf
  morphism is induced by a morphism between free `Γ(U, \mathcal O_U)`-modules; the public API
  should therefore quantify over those module maps directly, while any explicit bridge from module
  data to the restricted free sheaves remains internal;
- primitive data: an open `U`, basis types `I` and `J`, and a morphism between the free
  `Γ(U, \mathcal O_U)`-modules on those bases;
- derived API: the source-facing predicate saying that a restricted free-sheaf morphism is induced
  by such a module map, together with the glued-line counterexample below.

Source/core/bridge triage:
- `source-facing`: “this restricted morphism comes from a morphism of free
  `Γ(U, \mathcal O_U)`-modules”;
- `core/canonical`: the Chapter 17 owner `globalSectionsModuleFunctor` / `associatedModuleSheaf`
  on the restricted ringed space and the canonical restriction pullback `j^*`;
- `bridge/view`: the concrete map from a free `Γ(U, \mathcal O_U)`-module morphism to a morphism
  of restricted free sheaves, which stays private below. -/

private abbrev restrictedRingedSpace
    {X : RingedSpace.{u}} (U : Opens X) : RingedSpace.{u} :=
  X.restrict U.isOpenEmbedding

private abbrev restrictedRingCatSheaf
    {X : RingedSpace.{u}} (U : Opens X) :=
  RingedSpace.ringCatSheaf (restrictedRingedSpace U)

private abbrev restrictedGlobalSectionsRing
    {X : RingedSpace.{u}} (U : Opens X) :=
  (restrictedRingedSpace U).presheaf.obj (op ⊤)

private abbrev restrictedGlobalSectionsFreeModule
    {X : RingedSpace.{u}} (U : Opens X) (I : Type u) :
    ModuleCat (restrictedGlobalSectionsRing U) :=
  ModuleCat.of (restrictedGlobalSectionsRing U) (I →₀ restrictedGlobalSectionsRing U)

private abbrev topToRestrictedOpen
    {X : RingedSpace.{u}} (U : Opens X)
    (V : (Opens (restrictedRingedSpace U))ᵒᵖ) :
    op (⊤ : Opens (restrictedRingedSpace U)) ⟶ V :=
  (homOfLE (show unop V ≤ (⊤ : Opens (restrictedRingedSpace U)) from by
    intro x hx
    trivial)).op

/-- A global section `r ∈ Γ(U, \mathcal O_U)` determines the corresponding global section of the
unit sheaf on the restricted ringed space `X|_U`. -/
private noncomputable def unitSectionOfGlobalSectionsOnOpen
    {X : RingedSpace.{u}} (U : Opens X)
    (r : restrictedGlobalSectionsRing U) :
    (SheafOfModules.unit (restrictedRingCatSheaf U)).sections :=
  PresheafOfModules.sectionsMk
    (fun V ↦ ((restrictedRingedSpace U).presheaf.map (topToRestrictedOpen U V)).hom r)
    (by
      intro V W f
      change (CommRingCat.Hom.hom ((restrictedRingedSpace U).presheaf.map f))
          ((CommRingCat.Hom.hom
              ((restrictedRingedSpace U).presheaf.map (topToRestrictedOpen U V))) r) =
        (CommRingCat.Hom.hom
            ((restrictedRingedSpace U).presheaf.map (topToRestrictedOpen U W))) r
      have htop : topToRestrictedOpen U W = topToRestrictedOpen U V ≫ f := Subsingleton.elim _ _
      have hcomp :
          (CommRingCat.Hom.hom
              ((restrictedRingedSpace U).presheaf.map (topToRestrictedOpen U W))) r =
            (CommRingCat.Hom.hom ((restrictedRingedSpace U).presheaf.map f))
              ((CommRingCat.Hom.hom
                  ((restrictedRingedSpace U).presheaf.map (topToRestrictedOpen U V))) r) := by
        have hmapComp :=
          (restrictedRingedSpace U).presheaf.map_comp (topToRestrictedOpen U V) f
        have hmap := congrArg (fun g ↦ g r) (congrArg CommRingCat.Hom.hom hmapComp)
        simpa [htop] using hmap
      exact hcomp.symm)

/-- A finitely supported family of coefficients in `Γ(U, \mathcal O_U)` determines the
corresponding global section of the free sheaf on `X|_U`. -/
private noncomputable def freeSectionOfGlobalSectionsFinsuppOnOpen
    {X : RingedSpace.{u}} (U : Opens X)
    {J : Type u}
    (a : J →₀ restrictedGlobalSectionsRing U) :
    (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules).sections :=
  (SheafOfModules.unitHomEquiv
      (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules))
    (a.sum fun j r ↦
      (SheafOfModules.unitHomEquiv
          (SheafOfModules.unit (restrictedRingCatSheaf U))).symm
        (unitSectionOfGlobalSectionsOnOpen U r) ≫
          (show SheafOfModules.unit (restrictedRingCatSheaf U) ⟶
              (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules)
            from @SheafOfModules.ιFree _ _ _ (restrictedRingCatSheaf U) _ _ _ J j))

/-- A morphism of free `Γ(U, \mathcal O_U)`-modules induces canonically a morphism of free sheaves
on the restricted ringed space `X|_U`. This is private bridge data for the public predicate
`IsInducedByGlobalSectionsModuleMapOnOpen`. -/
private noncomputable def freeSheafMapOnOpen
    {X : RingedSpace.{u}} (U : Opens X)
    {I J : Type u}
    (ψ : restrictedGlobalSectionsFreeModule U I ⟶ restrictedGlobalSectionsFreeModule U J) :
    (SheafOfModules.free.{u} I : (restrictedRingedSpace U).Modules) ⟶
      (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules) :=
  (SheafOfModules.freeHomEquiv
      (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules)).symm
    (fun i ↦
      freeSectionOfGlobalSectionsFinsuppOnOpen U ((ψ.hom) (Finsupp.single i 1)))

/-- The canonical morphism between restricted free sheaves obtained from a morphism of free
`Γ(U, \mathcal O_U)`-modules, transported through the restriction isomorphisms
`SheafOfModules.pullbackObjFreeIso`. This bridge stays private; the public surface keeps only the
source-facing proposition that such a module map exists. -/
private noncomputable def restrictedFreeSheafMapOnOpen
    {X : RingedSpace.{u}} (U : Opens X)
    {I J : Type u}
    (ψ : restrictedGlobalSectionsFreeModule U I ⟶ restrictedGlobalSectionsFreeModule U J) :
    ((X.ofRestrict U.isOpenEmbedding)^*).obj (SheafOfModules.free.{u} I : X.Modules) ⟶
      ((X.ofRestrict U.isOpenEmbedding)^*).obj (SheafOfModules.free.{u} J : X.Modules) :=
  let eI :
      ((X.ofRestrict U.isOpenEmbedding)^*).obj (SheafOfModules.free.{u} I : X.Modules) ≅
        (SheafOfModules.free.{u} I : (restrictedRingedSpace U).Modules) :=
    SheafOfModules.pullbackObjFreeIso
      (RingedSpace.Hom.toRingCatSheafHom (X.ofRestrict U.isOpenEmbedding)) I
  let eJ :
      ((X.ofRestrict U.isOpenEmbedding)^*).obj (SheafOfModules.free.{u} J : X.Modules) ≅
        (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules) :=
    SheafOfModules.pullbackObjFreeIso
      (RingedSpace.Hom.toRingCatSheafHom (X.ofRestrict U.isOpenEmbedding)) J
  let m :
      (SheafOfModules.free.{u} I : (restrictedRingedSpace U).Modules) ⟶
        (SheafOfModules.free.{u} J : (restrictedRingedSpace U).Modules) :=
    freeSheafMapOnOpen U ψ
  eI.hom ≫ m ≫ eJ.inv

/-- A morphism between the restrictions of two free `\mathcal O_X`-module sheaves to `U` is
induced by a morphism of free `Γ(U, \mathcal O_U)`-modules if, after transport through the
canonical free-sheaf restriction isomorphisms, it is the induced morphism on the restricted
ringed space. The module map is part of the public data; the concrete bridge to restricted free
sheaves is kept internal. -/
def IsInducedByGlobalSectionsModuleMapOnOpen
    {X : RingedSpace.{u}} (U : Opens X)
    {I J : Type u}
    (φ :
      ((X.ofRestrict U.isOpenEmbedding)^*).obj (SheafOfModules.free.{u} I : X.Modules) ⟶
        ((X.ofRestrict U.isOpenEmbedding)^*).obj (SheafOfModules.free.{u} J : X.Modules)) :
    Prop :=
  ∃ ψ :
      ModuleCat.of ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))
          (I →₀ (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) ⟶
        ModuleCat.of ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))
          (J →₀ (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)),
    φ = restrictedFreeSheafMapOnOpen U ψ

/-- A morphism of free `\mathcal O_X`-module sheaves is locally induced by a module map at `x` if
this happens on some open neighbourhood of `x`. -/
def LocallyIsInducedByGlobalSectionsModuleMapAt
    {X : RingedSpace.{u}}
    (x : X)
    {I J : Type u}
    (φ : (SheafOfModules.free.{u} I : X.Modules) ⟶ SheafOfModules.free.{u} J) : Prop :=
  ∃ (U : Opens X) (_ : x ∈ U),
    IsInducedByGlobalSectionsModuleMapOnOpen U
      (((X.ofRestrict U.isOpenEmbedding)^*).map φ)

-- Proof sketch: unfold `LocallyIsInducedByGlobalSectionsModuleMapAt`; the statement is exactly the
-- defining expansion saying that the restricted morphism is induced by a module map on some
-- neighbourhood of `x`.
/-- A free-sheaf morphism is locally induced by a module map at `x` exactly when some
neighbourhood of `x` carries such a description for its restriction. -/
theorem locallyIsInducedByGlobalSectionsModuleMapAt_iff
    {X : RingedSpace.{u}}
    (x : X)
    {I J : Type u}
    (φ : (SheafOfModules.free.{u} I : X.Modules) ⟶ SheafOfModules.free.{u} J) :
    LocallyIsInducedByGlobalSectionsModuleMapAt x φ ↔
      ∃ (U : Opens X) (_ : x ∈ U),
        IsInducedByGlobalSectionsModuleMapOnOpen U
          (((X.ofRestrict U.isOpenEmbedding)^*).map φ) :=
  Iff.rfl

/-- Two points `(n, x)` and `(m, y)` in countably many copies of `\mathbb R` represent the same
point of the glued real line when the real coordinates agree and the branch index matters only at
the origin. -/
def gluedRealLineSetoid : Setoid (ℕ × ℝ) where
  r a b := a.2 = b.2 ∧ (a.2 = 0 → a.1 = b.1)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨rfl, fun _ ↦ rfl⟩
    · intro a b hab
      rcases hab with ⟨h₂, h₀⟩
      refine ⟨h₂.symm, ?_⟩
      intro hb0
      exact (h₀ (by simpa [h₂] using hb0)).symm
    · intro a b c hab hbc
      rcases hab with ⟨hab₂, hab₀⟩
      rcases hbc with ⟨hbc₂, hbc₀⟩
      refine ⟨hab₂.trans hbc₂, ?_⟩
      intro ha0
      have hb0 : b.2 = 0 := by
        simpa [hab₂] using ha0
      exact (hab₀ ha0).trans (hbc₀ hb0)

/-- The topological space obtained by gluing countably many copies of `\mathbb R` away from the
origin. -/
abbrev gluedRealLine : TopCat :=
  TopCat.of (Quotient gluedRealLineSetoid)

/-- The distinguished origin on the `0`th branch of the glued real line. -/
def gluedRealLineOrigin : gluedRealLine :=
  Quotient.mk'' (0, (0 : ℝ))

/-- The ringed space whose structure sheaf is the sheaf of continuous real-valued functions on the
glued real line. -/
private abbrev continuousRealFunctionsCommRingSheaf (X : TopCat.{0}) :
    TopCat.Sheaf CommRingCat X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ (CommAlgCat.{0} ℝ) CommRingCat)).obj
    (continuousRealFunctionsSheaf X)

/-- The ringed space whose structure sheaf is the sheaf of continuous real-valued functions on the
glued real line. -/
noncomputable def gluedRealLineRingedSpace : RingedSpace :=
  { carrier := gluedRealLine
    presheaf := (continuousRealFunctionsCommRingSheaf gluedRealLine).1
    IsSheaf := (continuousRealFunctionsCommRingSheaf gluedRealLine).2 }

/-- The distinguished glued origin, now regarded as a point of the ringed-space counterexample. -/
noncomputable def gluedRealLinePoint : gluedRealLineRingedSpace := by
  change gluedRealLine
  exact gluedRealLineOrigin

-- Proof sketch: take the ringed space obtained from countably many copies of `\mathbb R` glued at
-- the origin and its sheaf of continuous real-valued functions. The displayed morphism from the
-- countable free module sheaf to the doubly countable free module sheaf is defined by the locally
-- finite family `e_j ↦ \sum_i f_j 1_{L_i} e_{ij}`; the argument in the text shows that on every
-- neighbourhood of the glued point this restriction cannot be represented by a matrix with only
-- finitely many nonzero entries in each column, hence it is not induced by a module map over
-- `Γ(U, \mathcal O_U)`.
/-- Example 17.10.9: on the glued real line with structure sheaf of continuous real-valued
functions, there exists a morphism from the countable free `\mathcal O_X`-module sheaf to the
doubly countable free `\mathcal O_X`-module sheaf whose restriction to no neighbourhood of the
glued origin is induced by a morphism between the corresponding free
`Γ(U, \mathcal O_U)`-modules. In the textbook example, the morphism sends
`e_j` to `\sum_i f_j 1_{L_i} e_{ij}`. -/
theorem gluedRealLine_exists_free_module_sheaf_morphism_not_locally_induced_by_globalSectionsModuleMap :
    ∃ φ :
      (SheafOfModules.free (ULift ℕ) : gluedRealLineRingedSpace.Modules) ⟶
        (SheafOfModules.free (ULift (ℕ × ℕ)) : gluedRealLineRingedSpace.Modules),
      ¬ LocallyIsInducedByGlobalSectionsModuleMapAt gluedRealLinePoint φ := sorry

/-- The glued-line counterexample yields the source-facing existential statement that a morphism of
sheaves associated to free modules need not locally come from a morphism of modules. -/
theorem exists_free_module_sheaf_morphism_not_locally_induced_by_globalSectionsModuleMap :
    ∃ (X : RingedSpace) (x : X),
      ∃ φ :
        (SheafOfModules.free (ULift ℕ) : X.Modules) ⟶
          (SheafOfModules.free (ULift (ℕ × ℕ)) : X.Modules),
        ¬ LocallyIsInducedByGlobalSectionsModuleMapAt x φ := by
  obtain ⟨φ, hφ⟩ :=
    gluedRealLine_exists_free_module_sheaf_morphism_not_locally_induced_by_globalSectionsModuleMap
  exact ⟨gluedRealLineRingedSpace, gluedRealLinePoint, φ, hφ⟩

end AlgebraicGeometry
