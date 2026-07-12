import Mathlib
import StacksProject_2024.Chap06.Definition_6_7_1
import StacksProject_2024.Chap06.Extension_by_zero_by_the_initial_object
import StacksProject_2024.Chap06.Lemma_6_31_7

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens
open scoped TopCat

noncomputable section

universe u

/- Domain-style sampling for Lemma 17.19.1:
- primary domain: set-valued sheaves on a topological space, lower shriek along an open immersion,
  and coproduct presentations by lower-shriek constant sheaves;
- sampled owner declarations:
  `openSubsetSheafExtensionByInitialObject`,
  `constantSheaf`,
  `HasCoproduct`,
  `∐`;
- best owner abstraction: the core/canonical owners are the Chapter 6 lower-shriek functor `j! U`
  and the constant sheaf functor, with the canonical coproduct owner `HasCoproduct` / `∐` on the
  corresponding family. The source-facing surface in this file should therefore be the thin bridge
  `lowerShriekConstantSheaf U S`, i.e. the canonical composite
  `((j! U).obj ((constantSheaf ...).obj S))`, together with the notation `j![U, S]`;
- primitive data: an open subset `U ⊆ X` and a value type `S`;
- derived API: the notation `j![U, S]` and the epimorphic presentation theorem below.

Source/core/bridge triage:
- `source-facing`: the lower-shriek constant sheaf `j_{U!}\underline S` and the existence of an
  epimorphic coproduct presentation by such sheaves over basis opens;
- `core/canonical`: the Chapter 6 owner `j! U`, `constantSheaf`, and the coproduct owner
  `HasCoproduct` / `∐` in `Sh(X)`;
- `bridge/view`: `lowerShriekConstantSheaf U S`, identifying the source phrase “extension by the
  empty set of the constant sheaf” with the canonical composite `constantSheaf ⋙ j! U`.
-/

section

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

attribute [local instance] CategoryTheory.Types.instConcreteCategory
attribute [local instance] CategoryTheory.Types.instFunLike

local instance (I : Type u) : HasColimitsOfShape (Discrete I) (TopCat.Sheaf (Type u) X) :=
  by
    let _ : HasColimitsOfShape (Discrete I) (Type u) := by infer_instance
    change HasColimitsOfShape (Discrete I)
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
    exact CategoryTheory.Sheaf.instHasColimitsOfShape

/- The source-facing sheaf `j_{U!}\underline S` is not a second public owner: the recurring public
surface is the notation `j![U, S]`, implemented by the thin canonical bridge below. -/
/-- The lower-shriek constant sheaf `j_{U!}\underline S` on `X`, built from the canonical
extension-by-zero functor `j! U` and the constant sheaf on the open subspace `U`. -/
noncomputable abbrev lowerShriekConstantSheaf
    (U : Opens X) (S : Type u) : Sh(X) :=
  (j! U).obj
    ((constantSheaf (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
      (Type u)).obj S)

notation:max "j![" U ", " S "]" => lowerShriekConstantSheaf U S

/-- Helper for Lemma 17.19.1: a fixed singleton type living in the same universe as the sheaf
values. -/
abbrev SingletonType : Type u := ULift.{u} PUnit

/-- Helper for Lemma 17.19.1: every stalk element of a sheaf is represented by a section on a
basis open containing the given point. -/
lemma basis_stalk_representative
    (B : Set (Opens X)) (hB : Opens.IsBasis B) (ℱ : Sh(X))
    (x : X) (t : ℱ.presheaf.stalk x) :
    ∃ (U : Opens X), U ∈ B ∧ ∃ hxU : x ∈ U,
      ∃ s : ℱ.presheaf.obj (op U), ℱ.presheaf.germ U x hxU s = t := by
  -- Start from an arbitrary representative of the germ.
  obtain ⟨V, hxV, sV, hsV⟩ := TopCat.Presheaf.germ_exist ℱ.presheaf x t
  -- Refine that neighborhood to a basis open still containing the point.
  obtain ⟨_, ⟨U, hUB, rfl⟩, hxU, hUV⟩ := hB.exists_subset_of_mem_open hxV V.2
  refine ⟨U, hUB, hxU, ?_⟩
  refine ⟨ℱ.presheaf.map (homOfLE hUV).op sV, ?_⟩
  rw [← hsV]
  simpa using TopCat.Presheaf.germ_res_apply ℱ.presheaf (homOfLE hUV) x hxU sV

/-- Helper for Lemma 17.19.1: the top open of a topological space is terminal in its category of
opens. -/
noncomputable def top_open_isTerminal (Y : TopCat.{u}) : IsTerminal (⊤ : Opens Y) :=
  IsTerminal.ofUniqueHom (fun U : Opens Y ↦ Opens.leTop U) (fun _ _ ↦ Subsingleton.elim _ _)

/-- Helper for Lemma 17.19.1: the canonical generator of the singleton constant sheaf over the top
open. -/
noncomputable def singleton_constant_top_section
    (Y : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology Y) (Type u)] :
    ((constantSheaf (Opens.grothendieckTopology Y) (Type u)).obj SingletonType).obj.obj
      (op (⊤ : Opens Y)) :=
  ((CategoryTheory.constantSheafAdj (Opens.grothendieckTopology Y) (Type u)
      (top_open_isTerminal Y)).unit.app SingletonType)
    (default : SingletonType)

/-- Helper for Lemma 17.19.1: a section over the top open determines a morphism from the singleton
constant sheaf. -/
noncomputable def top_section_to_singleton_constant_hom
    {Y : TopCat.{u}}
    [HasWeakSheafify (Opens.grothendieckTopology Y) (Type u)]
    (ℱ : Sh(Y))
    (s : ℱ.presheaf.obj (op (⊤ : Opens Y))) :
    ((constantSheaf (Opens.grothendieckTopology Y) (Type u)).obj SingletonType) ⟶ ℱ :=
  let adj :=
    CategoryTheory.constantSheafAdj (Opens.grothendieckTopology Y) (Type u)
      (top_open_isTerminal Y)
  (adj.homEquiv _ _).symm ((Equiv.funUnique SingletonType _).symm s)

/-- Helper for Lemma 17.19.1: the morphism attached to a top-open section sends the canonical
singleton generator back to that section. -/
theorem top_section_to_singleton_constant_hom_app_top
    {Y : TopCat.{u}}
    [HasWeakSheafify (Opens.grothendieckTopology Y) (Type u)]
    (ℱ : Sh(Y))
    (s : ℱ.presheaf.obj (op (⊤ : Opens Y))) :
    (top_section_to_singleton_constant_hom ℱ s).hom.app (op (⊤ : Opens Y))
        (singleton_constant_top_section Y) = s := by
  let adj :=
    CategoryTheory.constantSheafAdj (Opens.grothendieckTopology Y) (Type u)
      (top_open_isTerminal Y)
  -- Evaluate the adjunction unit formula at the unique element of the singleton type.
  have h₀ :
      (adj.homEquiv SingletonType ℱ) (top_section_to_singleton_constant_hom ℱ s) =
        adj.unit.app SingletonType ≫
          ((CategoryTheory.sheafSections (Opens.grothendieckTopology Y) (Type u)).obj
            (op (⊤ : Opens Y))).map (top_section_to_singleton_constant_hom ℱ s) := by
    simpa [adj] using
      (adj.homEquiv_unit (X := SingletonType) (Y := ℱ)
        (f := top_section_to_singleton_constant_hom ℱ s))
  have h :
      (Equiv.funUnique SingletonType _).symm s =
        adj.unit.app SingletonType ≫
          ((CategoryTheory.sheafSections (Opens.grothendieckTopology Y) (Type u)).obj
            (op (⊤ : Opens Y))).map (top_section_to_singleton_constant_hom ℱ s) := by
    have hEquiv :
        (adj.homEquiv SingletonType ℱ) (top_section_to_singleton_constant_hom ℱ s) =
          (Equiv.funUnique SingletonType _).symm s := by
      simpa [adj, top_section_to_singleton_constant_hom] using
        (Equiv.apply_symm_apply (adj.homEquiv SingletonType ℱ)
          ((Equiv.funUnique SingletonType _).symm s))
    exact hEquiv.symm.trans h₀
  -- The left-hand side evaluates to `s`, while the right-hand side is the image of the canonical
  -- singleton generator under the induced morphism.
  simpa [singleton_constant_top_section] using (congrFun h default).symm

/-- Helper for Lemma 17.19.1: the inclusion of the open subspace `U` sends its top open back to
`U` itself. -/
lemma pullback_top_open_obj_eq
    (U : Opens X) :
    ((U.isOpenEmbedding.functor).obj (⊤ : Opens (extensionByZeroOpenSubsetSpace U))) = U := by
  ext x
  simp [extensionByZeroOpenSubsetSpace]

/-- Helper for Lemma 17.19.1: the top-open section object of the pullback sheaf along the open
inclusion `U ↪ X` is canonically identified with the ambient section object over `U`. -/
noncomputable def pullback_top_open_section_iso
    (ℱ : Sh(X)) (U : Opens X) :
    ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ).presheaf.obj
      (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))) ≅
    ℱ.presheaf.obj (op U) :=
  let e :=
    (((TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).mapIso
      ((U.isOpenEmbedding.sheafPullbackIso (Type u)).app ℱ)).app
        (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))))
  let hObj :
      ((U.isOpenEmbedding.sheafPullback (Type u)).obj ℱ).obj.obj
          (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))) =
        ℱ.presheaf.obj (op U) := by
    -- The open-embedding pullback computes sections over the image open, which is exactly `U`.
    simpa [TopCat.Sheaf.forget, Topology.IsOpenEmbedding.sheafPullback,
      extensionByZeroOpenSubsetSpace] using
      congrArg (fun V ↦ ℱ.presheaf.obj (op V)) (pullback_top_open_obj_eq U)
  e ≪≫ eqToIso hObj

/-- Helper for Lemma 17.19.1: the transport from pullback top-open sections back to ambient
`U`-sections is the raw pullback comparison followed by the top-open identification. -/
theorem pullback_top_open_section_iso_hom_eq_raw_component
    (ℱ : Sh(X)) (U : Opens X) :
    (pullback_top_open_section_iso ℱ U).hom =
      let e :=
        (((TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).mapIso
          ((U.isOpenEmbedding.sheafPullbackIso (Type u)).app ℱ)).app
            (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))))
      let hObj :
          ((U.isOpenEmbedding.sheafPullback (Type u)).obj ℱ).obj.obj
              (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))) =
            ℱ.presheaf.obj (op U) := by
        simpa [TopCat.Sheaf.forget, Topology.IsOpenEmbedding.sheafPullback,
          extensionByZeroOpenSubsetSpace] using
          congrArg (fun V ↦ ℱ.presheaf.obj (op V)) (pullback_top_open_obj_eq U)
      e.hom ≫ eqToHom hObj := by
  rfl

/-- Helper for Lemma 17.19.1: transport a section on the ambient open `U` to the corresponding
top-open section of the pullback sheaf on the open subspace. -/
noncomputable abbrev ambient_section_to_pullback_top_section
    (ℱ : Sh(X)) (U : Opens X) (s : ℱ.presheaf.obj (op U)) :
    ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ).presheaf.obj
      (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))) :=
  (pullback_top_open_section_iso ℱ U).inv s

/-- Helper for Lemma 17.19.1: transport a top-open section of the pullback sheaf on the open
subspace back to an ambient section on `U`. -/
noncomputable abbrev pullback_top_section_to_ambient_section
    (ℱ : Sh(X)) (U : Opens X)
    (s :
      ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ).presheaf.obj
        (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U)))) :
    ℱ.presheaf.obj (op U) :=
  (pullback_top_open_section_iso ℱ U).hom s

/-- Helper for Lemma 17.19.1: transporting an ambient `U`-section to the pullback sheaf on the
open subspace and back is the identity. -/
theorem pullback_top_section_transport_roundtrip
    (ℱ : Sh(X)) (U : Opens X) (s : ℱ.presheaf.obj (op U)) :
    pullback_top_section_to_ambient_section ℱ U
        (ambient_section_to_pullback_top_section ℱ U s) = s := by
  -- The ambient-to-pullback transport is the inverse of the comparison isomorphism.
  simpa [ambient_section_to_pullback_top_section, pullback_top_section_to_ambient_section] using
    CategoryTheory.hom_inv_id_apply (pullback_top_open_section_iso ℱ U) s

/-- Helper for Lemma 17.19.1: transporting a pullback top-open section to the ambient open and
back is the identity. -/
theorem ambient_section_transport_roundtrip
    (ℱ : Sh(X)) (U : Opens X)
    (s :
      ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ).presheaf.obj
        (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U)))) :
    ambient_section_to_pullback_top_section ℱ U
        (pullback_top_section_to_ambient_section ℱ U s) = s := by
  -- This is the converse inverse/hom identity for the same top-open comparison isomorphism.
  simpa [ambient_section_to_pullback_top_section, pullback_top_section_to_ambient_section] using
    CategoryTheory.inv_hom_id_apply (pullback_top_open_section_iso ℱ U) s

/-- Helper for Lemma 17.19.1: transporting a top-open pullback section back to `U` commutes with
applying a morphism of sheaves. -/
theorem pullback_top_section_to_ambient_section_naturality
    {ℱ 𝒢 : Sh(X)} (φ : ℱ ⟶ 𝒢) (U : Opens X)
    (t :
      ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ).presheaf.obj
        (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U)))) :
    pullback_top_section_to_ambient_section 𝒢 U
        ((((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).map φ).hom.app
          (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U)))) t) =
      φ.hom.app (op U) (pullback_top_section_to_ambient_section ℱ U t) := by
  let W : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ :=
    op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))
  let η :=
    Functor.isoWhiskerRight (U.isOpenEmbedding.sheafPullbackIso (Type u))
      (TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U))
  -- Route correction: rewrite the transport map into the raw pullback comparison, then evaluate
  -- the naturality square at the top open of the subspace.
  have hη :
      (((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).map φ).hom.app W) ≫
          (((U.isOpenEmbedding.sheafPullbackIso (Type u)).hom.app 𝒢).hom.app W) =
        (((U.isOpenEmbedding.sheafPullbackIso (Type u)).hom.app ℱ).hom.app W) ≫
          φ.hom.app (((U.isOpenEmbedding.functor).op.obj W)) := by
    simpa [η, W, Topology.IsOpenEmbedding.sheafPullback, TopCat.Sheaf.forget,
      Functor.sheafPushforwardContinuous, Functor.comp_map,
      ObjectProperty.FullSubcategory.comp_hom, Presheaf.comp_app, Sheaf.comp_app,
      Category.assoc] using
      congrArg (fun τ ↦ τ.app W) (η.hom.naturality φ)
  let hOp : ((U.isOpenEmbedding.functor).op.obj W) = op U := by
    simpa [W] using congrArg Opposite.op (pullback_top_open_obj_eq U)
  -- Natural transformation naturality transports the ambient morphism across the equality
  -- `((U.isOpenEmbedding.functor).obj ⊤) = U`.
  have hCast :
      φ.hom.app (op U)
        (ℱ.presheaf.map (eqToHom hOp)
          ((((U.isOpenEmbedding.sheafPullbackIso (Type u)).hom.app ℱ).hom.app W) t)) =
      𝒢.presheaf.map (eqToHom hOp)
        (φ.hom.app (((U.isOpenEmbedding.functor).op.obj W))
          ((((U.isOpenEmbedding.sheafPullbackIso (Type u)).hom.app ℱ).hom.app W) t)) := by
    simpa [FunctorToTypes.map_comp_apply] using
      congrFun (φ.hom.naturality (eqToHom hOp))
        ((((U.isOpenEmbedding.sheafPullbackIso (Type u)).hom.app ℱ).hom.app W) t)
  -- Evaluating the raw comparison square on `t` and then transporting along `hOp` gives the
  -- ambient `U`-section equality.
  have hEval := congrFun hη t
  calc
    pullback_top_section_to_ambient_section 𝒢 U
        ((((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).map φ).hom.app
          W) t) =
      𝒢.presheaf.map (eqToHom hOp)
        ((((U.isOpenEmbedding.sheafPullbackIso (Type u)).hom.app 𝒢).hom.app W)
          ((((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).map φ).hom.app
            W) t)) := by
      simp [W, pullback_top_section_to_ambient_section, pullback_top_open_section_iso,
        eqToHom_map, TopCat.Sheaf.forget, Topology.IsOpenEmbedding.sheafPullback,
        extensionByZeroOpenSubsetSpace]
    _ = 𝒢.presheaf.map (eqToHom hOp)
          (φ.hom.app (((U.isOpenEmbedding.functor).op.obj W))
            ((((U.isOpenEmbedding.sheafPullbackIso (Type u)).hom.app ℱ).hom.app W) t)) := by
      exact congrArg (𝒢.presheaf.map (eqToHom hOp)) hEval
    _ = φ.hom.app (op U)
          (ℱ.presheaf.map (eqToHom hOp)
            ((((U.isOpenEmbedding.sheafPullbackIso (Type u)).hom.app ℱ).hom.app W) t)) := by
      exact hCast.symm
    _ = φ.hom.app (op U) (pullback_top_section_to_ambient_section ℱ U t) := by
      simp [W, pullback_top_section_to_ambient_section, pullback_top_open_section_iso,
        eqToHom_map, TopCat.Sheaf.forget, Topology.IsOpenEmbedding.sheafPullback,
        extensionByZeroOpenSubsetSpace]

/-- Helper for Lemma 17.19.1: the canonical singleton section of `j![U, PUnit]` over `U`. -/
noncomputable def lowerShriek_singleton_generator_section
    (U : Opens X) :
    (j![U, SingletonType]).presheaf.obj (op U) :=
  let constSingleton :=
    (constantSheaf (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
      (Type u)).obj SingletonType
  let topGenerator :
      ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj
        (j![U, SingletonType])).presheaf.obj
        (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))) :=
    (((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom.app constSingleton).hom.app
      (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))))
        (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U))
  -- Apply the unit `constSingleton ⟶ j^{-1} j_! constSingleton` at the top open, then transport
  -- the resulting pullback section back to an ambient section over `U`.
  pullback_top_section_to_ambient_section (j![U, SingletonType]) U topGenerator

/-- Helper for Lemma 17.19.1: a section on `U` induces a morphism from the lower-shriek singleton
constant sheaf `j![U, PUnit]` to the ambient sheaf. -/
noncomputable def section_to_lowerShriek_singleton_hom
    (ℱ : Sh(X)) (U : Opens X) (s : ℱ.presheaf.obj (op U)) :
    j![U, SingletonType] ⟶ ℱ :=
  let transportedSection := ambient_section_to_pullback_top_section ℱ U s
  -- Route correction: the section must first be viewed on the top open of the pullback sheaf on
  -- the open subspace before the adjunction `j_! ⊣ j^{-1}` can be applied.
  ((OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U).homEquiv _ _).symm
    (top_section_to_singleton_constant_hom
      ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ)
      transportedSection)

/-- Helper for Lemma 17.19.1: on the pullback side, the morphism attached to a section sends the
top singleton generator to the transported section. -/
theorem section_to_lowerShriek_singleton_hom_generator_pullback
    (ℱ : Sh(X)) (U : Opens X) (s : ℱ.presheaf.obj (op U)) :
    let constSingleton :=
      (constantSheaf (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
        (Type u)).obj SingletonType
    let topGenerator :
        ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj
          (j![U, SingletonType])).presheaf.obj
          (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))) :=
      (((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom.app
        constSingleton).hom.app (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))))
        (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U))
    (((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).map
      (section_to_lowerShriek_singleton_hom ℱ U s)).hom.app
        (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U)))) topGenerator =
      ambient_section_to_pullback_top_section ℱ U s := by
  let constSingleton :=
    (constantSheaf (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
      (Type u)).obj SingletonType
  let transportedSection := ambient_section_to_pullback_top_section ℱ U s
  let adj := OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U
  -- The adjunction sends our chosen lower-shriek morphism back to the morphism classified by the
  -- transported section on the pullback side.
  have hAdj :
      top_section_to_singleton_constant_hom
          ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ)
          transportedSection =
        (adj.unit.app constSingleton) ≫
          (TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).map
            (section_to_lowerShriek_singleton_hom ℱ U s) := by
    have hUnit :
        (adj.homEquiv constSingleton ℱ) (section_to_lowerShriek_singleton_hom ℱ U s) =
          (adj.unit.app constSingleton) ≫
            (TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).map
              (section_to_lowerShriek_singleton_hom ℱ U s) := by
      simpa [adj] using
        (adj.homEquiv_unit (X := constSingleton) (Y := ℱ)
          (f := section_to_lowerShriek_singleton_hom ℱ U s))
    have hEquiv :
        (adj.homEquiv constSingleton ℱ) (section_to_lowerShriek_singleton_hom ℱ U s) =
          top_section_to_singleton_constant_hom
            ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ)
            transportedSection := by
      change (adj.homEquiv constSingleton ℱ)
          (((adj.homEquiv constSingleton ℱ).symm)
            (top_section_to_singleton_constant_hom
              ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ)
              transportedSection)) =
        top_section_to_singleton_constant_hom
          ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ)
          transportedSection
      exact Equiv.apply_symm_apply (adj.homEquiv constSingleton ℱ)
        (top_section_to_singleton_constant_hom
          ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ)
          transportedSection)
    exact hEquiv.symm.trans hUnit
  -- Evaluate the unit identity on the canonical singleton generator of the constant sheaf.
  have hApp :
      (top_section_to_singleton_constant_hom
          ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ)
          transportedSection).hom.app
          (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U)))
          (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U)) =
        (((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).map
          (section_to_lowerShriek_singleton_hom ℱ U s)).hom.app
            (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))))
          (((adj.unit.app constSingleton).hom.app
            (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))))
            (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U))) := by
    simpa [FunctorToTypes.map_comp_apply] using
      congrArg
        (fun κ ↦ κ.hom.app (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U)))
          (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U)))
        hAdj
  calc
    (((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).map
      (section_to_lowerShriek_singleton_hom ℱ U s)).hom.app
        (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))))
      ((((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom.app
        constSingleton).hom.app (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))))
        (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U))) =
        (((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).map
          (section_to_lowerShriek_singleton_hom ℱ U s)).hom.app
            (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))))
          (((adj.unit.app constSingleton).hom.app
            (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))))
            (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U))) := by
      rw [← OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso_hom_app
        (C := Type u) U constSingleton]
    _ =
        (top_section_to_singleton_constant_hom
          ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ)
          transportedSection).hom.app
          (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U)))
          (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U)) := by
      exact hApp.symm
    _ = transportedSection := by
      simpa [transportedSection] using
        top_section_to_singleton_constant_hom_app_top
          ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ)
          transportedSection

/-- Helper for Lemma 17.19.1: the lower-shriek morphism attached to a section sends the canonical
singleton generator over `U` back to that section. -/
theorem section_to_lowerShriek_singleton_hom_generator
    (ℱ : Sh(X)) (U : Opens X) (s : ℱ.presheaf.obj (op U)) :
    (section_to_lowerShriek_singleton_hom ℱ U s).hom.app (op U)
        (lowerShriek_singleton_generator_section (X := X) U) = s := by
  let constSingleton :=
    (constantSheaf (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
      (Type u)).obj SingletonType
  let topGenerator :
      ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj
        (j![U, SingletonType])).presheaf.obj
        (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))) :=
    (((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom.app
      constSingleton).hom.app (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))))
      (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U))
  -- Route correction: first compute on the pullback side via the adjunction unit, then transport
  -- the resulting top-open equality back to the ambient section over `U`.
  rw [lowerShriek_singleton_generator_section]
  calc
    (section_to_lowerShriek_singleton_hom ℱ U s).hom.app (op U)
        (pullback_top_section_to_ambient_section (j![U, SingletonType]) U topGenerator) =
      pullback_top_section_to_ambient_section ℱ U
        ((((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).map
          (section_to_lowerShriek_singleton_hom ℱ U s)).hom.app
            (op (⊤ : Opens (extensionByZeroOpenSubsetSpace U)))) topGenerator) := by
      symm
      exact pullback_top_section_to_ambient_section_naturality
        (φ := section_to_lowerShriek_singleton_hom ℱ U s) U topGenerator
    _ = pullback_top_section_to_ambient_section ℱ U
        (ambient_section_to_pullback_top_section ℱ U s) := by
      exact congrArg (pullback_top_section_to_ambient_section ℱ U)
        (by
          simpa [constSingleton, topGenerator] using
            section_to_lowerShriek_singleton_hom_generator_pullback ℱ U s)
    _ = s := pullback_top_section_transport_roundtrip ℱ U s

-- Proof sketch: for each stalk element `s ∈ ℱ_x`, choose a basis open `U(x,s)` and a section of
-- `ℱ` over `U(x,s)` representing `s`; Lemma 6.31.4 identifies such a section with a morphism
-- `j_{U(x,s)!}\underline{*} ⟶ ℱ`, and the induced coproduct map is stalkwise surjective, hence
-- epimorphic.
/-- Lemma 17.19.1: every sheaf of sets on `X` is an epimorphic image of a coproduct of lower-shriek
images `j_{U_i!}\underline{S_i}` with each `U_i` in the basis `B` and each `S_i` finite. The
exported source object is the canonical coproduct `∐ fun i ↦ j![U i, S i]`. -/
@[stacks 0CAH]
theorem exists_epi_from_coproduct_of_basis_extension_by_empty_constant_sheaves
    (B : Set (Opens X)) (hB : Opens.IsBasis B) (ℱ : Sh(X)) :
    ∃ (I : Type u) (U : I → Opens X) (S : I → Type u)
      (hU : ∀ i, U i ∈ B) (hS : ∀ i, Finite (S i)),
      ∃ φ : (∐ fun i : I ↦ j![U i, S i]) ⟶ ℱ, Epi φ := by
  classical
  let I : Type u := Σ x : X, ℱ.presheaf.stalk x
  let U : I → Opens X := fun i ↦ Classical.choose (basis_stalk_representative B hB ℱ i.1 i.2)
  let hU : ∀ i, U i ∈ B := fun i ↦ (Classical.choose_spec
    (basis_stalk_representative B hB ℱ i.1 i.2)).1
  let representative_exists :
      ∀ i, ∃ hxU : i.1 ∈ U i, ∃ s : ℱ.presheaf.obj (op (U i)),
        ℱ.presheaf.germ (U i) i.1 hxU s = i.2 := fun i ↦
    (Classical.choose_spec (basis_stalk_representative B hB ℱ i.1 i.2)).2
  let hxU : ∀ i, i.1 ∈ U i := fun i ↦ Classical.choose (representative_exists i)
  let s : ∀ i, ℱ.presheaf.obj (op (U i)) := fun i ↦
    Classical.choose (Classical.choose_spec (representative_exists i))
  let hs : ∀ i, ℱ.presheaf.germ (U i) i.1 (hxU i) (s i) = i.2 := fun i ↦
    Classical.choose_spec (Classical.choose_spec (representative_exists i))
  let S : I → Type u := fun _ ↦ SingletonType
  let φ : (∐ fun i : I ↦ j![U i, S i]) ⟶ ℱ :=
    Limits.Sigma.desc (fun i ↦ section_to_lowerShriek_singleton_hom ℱ (U i) (s i))
  refine ⟨I, U, S, hU, fun _ ↦ inferInstance, φ, ?_⟩
  have hstalk :
      ∀ x : X, Function.Surjective ((TopCat.Presheaf.stalkFunctor (Type u) x).map φ.hom) := by
    intro x t
    let i : I := ⟨x, t⟩
    let preSection :
        (∐ fun j : I ↦ j![U j, S j]).presheaf.obj (op (U i)) :=
      ((Limits.Sigma.ι (fun j : I ↦ j![U j, S j]) i).hom.app (op (U i)))
        (lowerShriek_singleton_generator_section (X := X) (U i))
    refine ⟨TopCat.Presheaf.germ (∐ fun j : I ↦ j![U j, S j]).presheaf
      (U i) x (hxU i) preSection, ?_⟩
    -- The chosen summand indexed by `(x, t)` maps the canonical singleton germ to the desired
    -- stalk element because its representing section was chosen to have germ `t`.
    have hmap :
        ((TopCat.Presheaf.stalkFunctor (Type u) x).map φ.hom)
            ((∐ fun j : I ↦ j![U j, S j]).presheaf.germ (U i) x (hxU i) preSection) =
          ℱ.presheaf.germ (U i) x (hxU i) (φ.hom.app (op (U i)) preSection) := by
      simpa using
        (TopCat.Presheaf.stalkFunctor_map_germ_apply (U i) x (hxU i) φ.hom preSection)
    have hsection :
        φ.hom.app (op (U i)) preSection = s i := by
      calc
        φ.hom.app (op (U i)) preSection =
            (section_to_lowerShriek_singleton_hom ℱ (U i) (s i)).hom.app
              (op (U i)) (lowerShriek_singleton_generator_section (X := X) (U i)) := by
          simpa [φ, preSection, FunctorToTypes.map_comp_apply] using
            congrArg
              (fun κ ↦ κ.hom.app (op (U i))
                (lowerShriek_singleton_generator_section (X := X) (U i)))
              (Limits.Sigma.ι_desc
                (fun j : I ↦ section_to_lowerShriek_singleton_hom ℱ (U j) (s j)) i)
        _ = s i := section_to_lowerShriek_singleton_hom_generator ℱ (U i) (s i)
    rw [hmap, hsection]
    simpa [i] using hs i
  have hloc : TopCat.Presheaf.IsLocallySurjective φ.hom :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks φ.hom).2 hstalk
  exact (TopCat.Sheaf.isLocallySurjective_iff_epi φ).1 hloc

end
