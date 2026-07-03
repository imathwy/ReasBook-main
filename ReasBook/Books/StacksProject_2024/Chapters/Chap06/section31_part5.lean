import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_6_31_11 (from Chap06) -/
open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe v u

/-
Domain-style sampling for Lemma 6.31.11:
- primary domain: extension by the initial object for sheaves of algebraic structures along an
  open immersion;
- sampled owner API:
  `OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem`,
  `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`;
- owner abstraction: the Chapter 6 owner is the open-subset extension-by-initial-object adjunction
  and its stalk description, not a new local wrapper;
- primitive data: the open subset `U`, the sheaf `𝒢`, and the canonical map `initial.to` on the
  stalks;
- derived API: the fully faithful instance and the essential-image criterion.

Source/core/bridge triage:
- `source-facing`: the Stacks-project statements that `j_!` is fully faithful and that its
  essential image is detected by initial stalks outside `U`;
- `core/canonical`: `OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction` together with
  the owner-side stalk theorem outside `U`;
- `bridge/view`: this file’s algebraic-structure specialization of those owner declarations.

The public API here should therefore keep only the source-facing fully-faithful and essential-image
statements, while reusing the owner adjunction and stalk theorem directly rather than keeping a
parallel local stalk-initial wrapper.
-/

section

variable {X : TopCat.{v}}

variable {C : Type u} [Category.{v} C] [HasInitial C] [HasColimits C] [HasLimits C]
variable {FC : C → C → Type v} {CC : C → Type v}
variable [hFunLike : ∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [hConcrete : ConcreteCategory.{v} C FC]
variable [hPreservesLimits : PreservesLimits (CategoryTheory.forget C)]
variable [hPreservesFilteredColimits : PreservesFilteredColimits (CategoryTheory.forget C)]
variable [hReflectsIsomorphisms : (CategoryTheory.forget C).ReflectsIsomorphisms]
variable [hWeakSheafify : CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C]

include FC CC hFunLike hConcrete hPreservesLimits hPreservesFilteredColimits
  hReflectsIsomorphisms

-- Proof sketch: the restriction functor to the open subspace is the sheaf pushforward along the
-- inclusion-of-opens functor, and `j_!` is its left adjoint. As in the set-valued case, the unit
-- is an isomorphism because on opens lying in `U` the construction agrees with the original sheaf.
/-- Lemma 6.31.11 (1): for a type of algebraic structures with an initial object, extension by the
initial object along the inclusion `j : U ↪ X` is a fully faithful functor on sheaves. -/
instance openSubsetSheafExtensionByInitialObject_fullyFaithful
    (U : Opens X) :
    (((j! U) :
      (extensionByZeroOpenSubsetSpace U).Sheaf C ⥤ X.Sheaf C)).FullyFaithful := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  letI : IsIso h.unit := by
    change IsIso
      ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom)
    infer_instance
  simpa using h.fullyFaithfulLOfIsIsoUnit

/-- Helper for Lemma 6.31.11: the presheaf stalk pullback isomorphism is natural in the presheaf
argument. -/
private theorem presheaf_stalkPullbackIso_hom_naturality
    {Y : TopCat.{v}} (f : X ⟶ Y) {ℱ 𝒢 : Y.Presheaf C} (η : ℱ ⟶ 𝒢) (x : X) :
    (TopCat.Presheaf.stalkFunctor C (f x)).map η ≫
        (TopCat.Presheaf.stalkPullbackIso C f 𝒢 x).hom =
      (TopCat.Presheaf.stalkPullbackIso C f ℱ x).hom ≫
        (TopCat.Presheaf.stalkFunctor C x).map
          ((TopCat.Presheaf.pullback C f).map η) := by
  -- Compare both morphisms after precomposing with germs; the pullback stalk isomorphism is built
  -- from those germs and the pullback-pushforward unit.
  apply TopCat.Presheaf.stalk_hom_ext ℱ
  intro V hx
  let h₁ := TopCat.Presheaf.stalkFunctor_map_germ (C := C) V (f x) hx η
  let h₂𝒢 := TopCat.Presheaf.germ_stalkPullbackHom (C := C) f 𝒢 x V hx
  let h₂ℱ := TopCat.Presheaf.germ_stalkPullbackHom (C := C) f ℱ x V hx
  let h₃ := TopCat.Presheaf.stalkFunctor_map_germ (C := C) ((Opens.map f).obj V) x hx
    ((TopCat.Presheaf.pullback C f).map η)
  let A :=
    ℱ.germ V (f x) hx ≫ (TopCat.Presheaf.stalkFunctor C (f x)).map η ≫
      TopCat.Presheaf.stalkPullbackHom C f 𝒢 x
  let B :=
    η.app (op V) ≫ 𝒢.germ V (f x) hx ≫ TopCat.Presheaf.stalkPullbackHom C f 𝒢 x
  let D :=
    ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app ℱ).app (op V) ≫
      ((TopCat.Presheaf.pullback C f).map η).app (op ((Opens.map f).obj V)) ≫
        ((TopCat.Presheaf.pullback C f).obj 𝒢).germ ((Opens.map f).obj V) x hx
  let C₁ :=
    η.app (op V) ≫
      ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app 𝒢).app (op V) ≫
        ((TopCat.Presheaf.pullback C f).obj 𝒢).germ ((Opens.map f).obj V) x hx
  let E :=
    ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app ℱ).app (op V) ≫
      ((TopCat.Presheaf.pullback C f).obj ℱ).germ ((Opens.map f).obj V) x hx ≫
        (TopCat.Presheaf.stalkFunctor C x).map ((TopCat.Presheaf.pullback C f).map η)
  let Z :=
    ℱ.germ V (f x) hx ≫ TopCat.Presheaf.stalkPullbackHom C f ℱ x ≫
      (TopCat.Presheaf.stalkFunctor C x).map ((TopCat.Presheaf.pullback C f).map η)
  have hA : A = B := by
    simpa [A, B, Category.assoc] using
      congrArg (fun k ↦ k ≫ TopCat.Presheaf.stalkPullbackHom C f 𝒢 x) h₁
  have hB : B = C₁ := by
    simpa [B, C₁, Category.assoc] using congrArg (fun k ↦ η.app (op V) ≫ k) h₂𝒢
  have hC : C₁ = D := by
    have hNat := NatTrans.congr_app
      ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.naturality η) (op V)
    simpa [C₁, D, Category.assoc] using
      congrArg
        (fun k ↦
          k ≫ ((TopCat.Presheaf.pullback C f).obj 𝒢).germ ((Opens.map f).obj V) x hx)
        hNat
  have hD : D = E := by
    simpa [D, E, Category.assoc] using
      congrArg
        (fun k ↦
          ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app ℱ).app (op V) ≫ k)
        h₃.symm
  have hE : E = Z := by
    simpa [E, Z, Category.assoc] using
      congrArg
        (fun k ↦
          k ≫
            (TopCat.Presheaf.stalkFunctor C x).map ((TopCat.Presheaf.pullback C f).map η))
        h₂ℱ.symm
  exact hA.trans (hB.trans (hC.trans (hD.trans hE)))

/-- Helper for Lemma 6.31.11: the sheaf stalk pullback comparison is natural in the sheaf
argument. -/
private theorem sheaf_stalkPullbackIso_hom_naturality
    {Y : TopCat.{v}} (f : X ⟶ Y) {ℱ 𝒢 : Y.Sheaf C} (η : ℱ ⟶ 𝒢) (x : X) :
    ((TopCat.Presheaf.stalkFunctor C (f x)).map η.hom) ≫
        (TopCat.Sheaf.stalkPullbackIso f 𝒢 x).hom =
      (TopCat.Sheaf.stalkPullbackIso f ℱ x).hom ≫
        ((TopCat.Presheaf.stalkFunctor C x).map
          (((TopCat.Sheaf.pullback C f).map η).hom)) := by
  -- Unfold the sheaf-level stalk comparison into the presheaf pullback iso, sheafification unit,
  -- and `pullbackIso.inv`, then move `η` through each factor.
  rw [TopCat.Sheaf.stalkPullbackIso_def, TopCat.Sheaf.stalkPullbackIso_def]
  simp only [Iso.trans_hom, Category.assoc]
  let σ :=
    CategoryTheory.sheafifyMap (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pullback C f).map η.hom)
  let τ𝒢 :=
    CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pullback C f).obj 𝒢.presheaf)
  let τℱ :=
    CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pullback C f).obj ℱ.presheaf)
  let π𝒢 :=
    (TopCat.Sheaf.forget C X).map
      ((TopCat.Sheaf.pullbackIso C f).inv.app 𝒢)
  let πℱ :=
    (TopCat.Sheaf.forget C X).map
      ((TopCat.Sheaf.pullbackIso C f).inv.app ℱ)
  have hsheafify :
      ((TopCat.Presheaf.stalkFunctor C x).map
          ((TopCat.Presheaf.pullback C f).map η.hom)) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map τ𝒢) =
      ((TopCat.Presheaf.stalkFunctor C x).map τℱ) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map σ) := by
    -- This is the stalked form of `toSheafify_naturality`.
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor C x).map k)
      (CategoryTheory.toSheafify_naturality
        (J := Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback C f).map η.hom))
  have hpullbackIso :
      ((TopCat.Presheaf.stalkFunctor C x).map σ) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) =
      ((TopCat.Presheaf.stalkFunctor C x).map πℱ) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map
          (((TopCat.Sheaf.pullback C f).map η).hom)) := by
    -- This is the stalked form of naturality for `TopCat.Sheaf.pullbackIso.inv`.
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor C x).map k)
      (by
        simpa [σ, π𝒢, πℱ] using congrArg
          (fun k ↦ (TopCat.Sheaf.forget C X).map k)
          (((TopCat.Sheaf.pullbackIso C f).inv).naturality η))
  have hstep₁ :
    ((TopCat.Presheaf.stalkFunctor C (f x)).map η.hom) ≫
        (TopCat.Presheaf.stalkPullbackIso C f 𝒢.presheaf x).hom ≫
        ((TopCat.Presheaf.stalkFunctor C x).map τ𝒢) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) =
      (TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
        ((TopCat.Presheaf.stalkFunctor C x).map
          ((TopCat.Presheaf.pullback C f).map η.hom)) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map τ𝒢) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) := by
    -- First move `η` through the presheaf-level stalk pullback comparison.
    simpa [Category.assoc] using congrArg
      (fun k ↦
        k ≫
          ((TopCat.Presheaf.stalkFunctor C x).map τ𝒢) ≫
            ((TopCat.Presheaf.stalkFunctor C x).map π𝒢))
      (presheaf_stalkPullbackIso_hom_naturality (C := C) f η.hom x)
  have hstep₂ :
      (TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor C x).map
            ((TopCat.Presheaf.pullback C f).map η.hom)) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map τ𝒢) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor C x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map σ) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) := by
    -- Next move `η` through the sheafification unit.
    have hstep₂' :
        (((TopCat.Presheaf.stalkFunctor C x).map
              ((TopCat.Presheaf.pullback C f).map η.hom)) ≫
            ((TopCat.Presheaf.stalkFunctor C x).map τ𝒢)) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) =
          (((TopCat.Presheaf.stalkFunctor C x).map τℱ) ≫
              ((TopCat.Presheaf.stalkFunctor C x).map σ)) ≫
            ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) := by
      exact congrArg
        (fun k ↦ k ≫ ((TopCat.Presheaf.stalkFunctor C x).map π𝒢))
        hsheafify
    simpa [Category.assoc] using congrArg
      (fun k ↦ (TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫ k)
      hstep₂'
  have hstep₃ :
      (TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor C x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map σ) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor C x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map πℱ) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map
            (((TopCat.Sheaf.pullback C f).map η).hom)) := by
    -- Finally move `η` through the `pullbackIso.inv` comparison.
    have hpullbackIso' :
        ((TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
            ((TopCat.Presheaf.stalkFunctor C x).map τℱ)) ≫
            (((TopCat.Presheaf.stalkFunctor C x).map σ) ≫
              ((TopCat.Presheaf.stalkFunctor C x).map π𝒢)) =
          ((TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
              ((TopCat.Presheaf.stalkFunctor C x).map τℱ)) ≫
            (((TopCat.Presheaf.stalkFunctor C x).map πℱ) ≫
              ((TopCat.Presheaf.stalkFunctor C x).map
                (((TopCat.Sheaf.pullback C f).map η).hom))) := by
      exact congrArg
        (fun k ↦
          ((TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
              ((TopCat.Presheaf.stalkFunctor C x).map τℱ)) ≫
            k)
        hpullbackIso
    simpa [Category.assoc] using hpullbackIso'
  exact hstep₁.trans (hstep₂.trans hstep₃)

/-- Helper for Lemma 6.31.11: on points of `U`, the counit stalk map followed by the stalk
pullback comparison agrees with the explicit stalk identification coming from the unit isomorphism.
-/
private theorem counit_stalk_map_comp_stalkPullbackIso_eq_of_mem
    (U : Opens X) (𝒢 : X.Sheaf C) (x : X) (hx : x ∈ (U : Set X)) :
    let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
    let h : (j! U) ⊣ TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
      OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
    let R := TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)
    let explicit :
        (((j! U).obj (R.obj 𝒢)).presheaf.stalk x) ≅ (R.obj 𝒢).presheaf.stalk xU :=
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
          xU) ≪≫
        ((TopCat.Presheaf.stalkFunctor C xU).mapIso
          ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).mapIso
            (asIso (h.unit.app (R.obj 𝒢))))).symm
    ((TopCat.Presheaf.stalkFunctor C x).map (h.counit.app 𝒢).hom) ≫
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom =
      explicit.hom := by
  let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
  let h : (j! U) ⊣ TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  let R := TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)
  have hunit : IsIso (h.unit.app (R.obj 𝒢)) := by
    change IsIso ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom.app
      (R.obj 𝒢))
    infer_instance
  letI : IsIso (h.unit.app (R.obj 𝒢)) := hunit
  let explicit :
      (((j! U).obj (R.obj 𝒢)).presheaf.stalk x) ≅ (R.obj 𝒢).presheaf.stalk xU :=
    (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
        xU) ≪≫
      ((TopCat.Presheaf.stalkFunctor C xU).mapIso
        ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).mapIso
          (asIso (h.unit.app (R.obj 𝒢))))).symm
  change ((TopCat.Presheaf.stalkFunctor C x).map (h.counit.app 𝒢).hom) ≫
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom =
    explicit.hom
  -- Route correction: prove the inside-`U` comparison by sheaf-level naturality of
  -- `stalkPullbackIso`, then rewrite `R.map ε` to the inverse unit via the right triangle.
  let e : R.obj 𝒢 ≅ R.obj ((j! U).obj (R.obj 𝒢)) :=
    @asIso _ _ _ _ (h.unit.app (R.obj 𝒢)) hunit
  have hright :
      R.map (h.counit.app 𝒢) = inv (h.unit.app (R.obj 𝒢)) := by
    -- Precompose the right triangle with the inverse unit to isolate `R.map ε`.
    have htriangle :
        h.unit.app (R.obj 𝒢) ≫ R.map (h.counit.app 𝒢) = 𝟙 (R.obj 𝒢) := by
      simpa [R] using h.right_triangle_components 𝒢
    have := congrArg (fun k ↦ inv (h.unit.app (R.obj 𝒢)) ≫ k) htriangle
    simpa [Category.assoc] using this
  have hnat :
      ((TopCat.Presheaf.stalkFunctor C x).map (h.counit.app 𝒢).hom) ≫
          (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom =
        (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
            xU).hom ≫
          ((TopCat.Presheaf.stalkFunctor C xU).map (R.map (h.counit.app 𝒢)).hom) := by
    -- First move the counit across the sheaf stalk pullback comparison.
    simpa [R] using sheaf_stalkPullbackIso_hom_naturality
      (C := C) (f := extensionByZeroOpenSubsetInclusion U) (η := h.counit.app 𝒢) (x := xU)
  rw [hnat]
  have hforget :
      (R.map (h.counit.app 𝒢)).hom =
        (TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map
          (inv (h.unit.app (R.obj 𝒢))) := by
    -- Rewrite the underlying presheaf map using the right-triangle identity.
    simpa [hright] using congrArg
      (fun k ↦ (TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map k) hright
  let stalkUnitIso :
      (R.obj 𝒢).presheaf.stalk xU ≅
        (R.obj ((j! U).obj (R.obj 𝒢))).presheaf.stalk xU :=
    (TopCat.Presheaf.stalkFunctor C xU).mapIso
      ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).mapIso e)
  have hstalk :
      ((TopCat.Presheaf.stalkFunctor C xU).map (R.map (h.counit.app 𝒢)).hom) =
        stalkUnitIso.inv := by
    -- Apply the stalk functor to the inverse-unit description of `R.map ε`.
    rw [hforget]
    have hforgetInv :
        ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.inv) =
          inv ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.hom) := by
      exact Functor.map_inv (TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)) e.hom
    simpa [stalkUnitIso, e] using congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor C xU).map k)
      hforgetInv
  have hcomp :
    (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
          xU).hom ≫
        ((TopCat.Presheaf.stalkFunctor C xU).map (R.map (h.counit.app 𝒢)).hom) =
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
          xU).hom ≫
        stalkUnitIso.inv := by
    -- Replace the stalk map of `R.map ε` by the inverse of the stalked unit.
    simpa using congrArg
      (fun k ↦
        (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
          xU).hom ≫ k)
      hstalk
  have hexplicit :
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
          xU).hom ≫
        stalkUnitIso.inv =
      explicit.hom := by
    -- This is exactly the explicit composite defining the inside-`U` stalk isomorphism.
    have hforgetInv :
        ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.inv) =
          inv ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.hom) := by
      exact Functor.map_inv (TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)) e.hom
    have heinv :
        (TopCat.Presheaf.stalkFunctor C xU).map
            ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.inv) =
          inv
            ((TopCat.Presheaf.stalkFunctor C xU).map
              ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.hom)) := by
      have hstalkInv :
          (TopCat.Presheaf.stalkFunctor C xU).map
              (inv ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.hom)) =
            inv
              ((TopCat.Presheaf.stalkFunctor C xU).map
                ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.hom)) := by
        exact Functor.map_inv (TopCat.Presheaf.stalkFunctor C xU)
          ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.hom)
      exact (congrArg
        (fun k ↦ (TopCat.Presheaf.stalkFunctor C xU).map k)
        hforgetInv).trans hstalkInv
    simp [explicit, stalkUnitIso, e, Category.assoc]
    have hstalkInv' :
        (TopCat.Presheaf.stalkFunctor C xU).map
            (inv
              ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map
                (h.unit.app (R.obj 𝒢)))) =
          inv
            ((TopCat.Presheaf.stalkFunctor C xU).map
              ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map
                (h.unit.app (R.obj 𝒢)))) := by
      exact Functor.map_inv (TopCat.Presheaf.stalkFunctor C xU)
        ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map
          (h.unit.app (R.obj 𝒢)))
    exact congrArg
      (fun k ↦
        (TopCat.Presheaf.stalkFunctor C xU).map
            (CategoryTheory.toSheafify
              (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
              ((TopCat.Presheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj
                ((TopCat.Sheaf.forget C X).obj ((j! U).obj (R.obj 𝒢))))) ≫
          (TopCat.Presheaf.stalkFunctor C xU).map
            ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map
              ((TopCat.Sheaf.pullbackIso C (extensionByZeroOpenSubsetInclusion U)).inv.app
                ((j! U).obj (R.obj 𝒢)))) ≫
          k)
      hstalkInv'
  exact hcomp.trans hexplicit

/-- Helper for Lemma 6.31.11: at points of `U`, the counit is stalkwise an isomorphism. -/
private theorem counit_stalk_map_isIso_of_mem
    (U : Opens X) (𝒢 : X.Sheaf C) (x : X) (hx : x ∈ (U : Set X)) :
    IsIso
      ((TopCat.Presheaf.stalkFunctor C x).map
        ((OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U).counit.app 𝒢).hom) := by
  let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
  let h : (j! U) ⊣ TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  let R := TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)
  have hunit : IsIso (h.unit.app (R.obj 𝒢)) := by
    change IsIso ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom.app
      (R.obj 𝒢))
    infer_instance
  let explicit :
      (((j! U).obj (R.obj 𝒢)).presheaf.stalk x) ≅ (R.obj 𝒢).presheaf.stalk xU :=
    (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
        xU) ≪≫
      ((TopCat.Presheaf.stalkFunctor C xU).mapIso
        ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).mapIso
          (asIso (h.unit.app (R.obj 𝒢))))).symm
  have hComp :
      IsIso
        (((TopCat.Presheaf.stalkFunctor C x).map (h.counit.app 𝒢).hom) ≫
          (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom) := by
    -- The source-faithful step is the explicit inside-`U` stalk comparison from the helper above.
    rw [counit_stalk_map_comp_stalkPullbackIso_eq_of_mem (C := C) U 𝒢 x hx]
    infer_instance
  -- Cancel the pullback stalk comparison to recover the counit stalk map itself.
  have :
      IsIso
        ((((TopCat.Presheaf.stalkFunctor C x).map (h.counit.app 𝒢).hom) ≫
            (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom) ≫
          inv (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom) := by
    exact inferInstance
  simpa [Category.assoc] using this

-- Proof sketch: if a sheaf is of the form `j_! ℱ`, then its stalks outside `U` are initial by the
-- extension-by-initial-object construction. Conversely, if the stalks of `𝒢` outside `U` are
-- initial, then the counit map `j_! j^{-1} 𝒢 ⟶ 𝒢` is an isomorphism on every stalk, hence an
-- isomorphism of sheaves, which places `𝒢` in the essential image of `j_!`.
/-- Lemma 6.31.11 (2): a sheaf of algebraic structures on `X` lies in the essential image of
extension by the initial object from `U` if and only if, at every point of `X \ U`, the canonical
map from the initial object of `C` to the stalk is an isomorphism. -/
theorem openSubsetSheafExtensionByInitialObject_essImage_iff_isIso_initial_to_stalk_of_not_mem
    (U : Opens X) (𝒢 : X.Sheaf C) :
    (j! U).essImage 𝒢 ↔
      ∀ x : X, x ∉ (U : Set X) →
        IsIso (initial.to (𝒢.presheaf.stalk x)) := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  let hFF :
      (((j! U) :
        (extensionByZeroOpenSubsetSpace U).Sheaf C ⥤ X.Sheaf C)).FullyFaithful :=
    openSubsetSheafExtensionByInitialObject_fullyFaithful U
  letI :
      (((j! U) :
        (extensionByZeroOpenSubsetSpace U).Sheaf C ⥤ X.Sheaf C)).Full :=
    hFF.full
  letI :
      (((j! U) :
        (extensionByZeroOpenSubsetSpace U).Sheaf C ⥤ X.Sheaf C)).Faithful :=
    hFF.faithful
  have hess : IsIso (h.counit.app 𝒢) ↔ (j! U).essImage 𝒢 := by
    simpa using
      (h.isIso_counit_app_iff_mem_essImage : IsIso (h.counit.app 𝒢) ↔ (j! U).essImage 𝒢)
  constructor
  · intro h𝒢 x hx
    letI : IsIso (h.counit.app 𝒢) := hess.mpr h𝒢
    have hε : IsIso ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢)) := by
      infer_instance
    letI : IsIso ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢)) := hε
    have hMap :
        IsIso
          ((TopCat.Presheaf.stalkFunctor C x).map
            ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢))) :=
      Functor.map_isIso (TopCat.Presheaf.stalkFunctor C x)
        ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢))
    letI :
        IsIso
          ((TopCat.Presheaf.stalkFunctor C x).map
            ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢))) :=
      hMap
    have hSource :
        IsInitial
          (((j! U).obj
              ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj 𝒢)).presheaf.stalk x) :=
      OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem U
        ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj 𝒢) hx
    have hTarget : IsInitial (𝒢.presheaf.stalk x) :=
      IsInitial.ofIso hSource
        (@asIso _ _ _ _
          ((TopCat.Presheaf.stalkFunctor C x).map
            ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢))) hMap)
    exact isIso_of_isInitial initialIsInitial hTarget (initial.to (𝒢.presheaf.stalk x))
  · intro h𝒢
    let ε := h.counit.app 𝒢
    have : IsIso ε := by
      rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
      intro x
      by_cases hx : x ∈ (U : Set X)
      · -- On `U`, the counit is inverse to the unit after transporting through the stalk pullback
        -- comparison.
        exact counit_stalk_map_isIso_of_mem (C := C) U 𝒢 x hx
      · let hSource :
            IsInitial
              (((j! U).obj
                  ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj 𝒢)).presheaf.stalk x) :=
          OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem U
            ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj 𝒢) hx
        letI : IsIso (initial.to (𝒢.presheaf.stalk x)) := h𝒢 x hx
        let hTarget : IsInitial (𝒢.presheaf.stalk x) :=
          IsInitial.ofIso initialIsInitial (asIso (initial.to (𝒢.presheaf.stalk x)))
        exact isIso_of_isInitial hSource hTarget ((TopCat.Presheaf.stalkFunctor C x).map ε.hom)
    exact hess.mp this

end

/-! ### Lemma_6_31_12 (from Chap06) -/
open CategoryTheory TopologicalSpace TopCat
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

/-
Domain-style sampling for Lemma 6.31.12:
- primary domain: extension by zero for sheaves of modules on a ringed space, together with
  fully-faithfulness and essential-image detection by vanishing stalks outside an open subset;
- sampled owner declarations:
  `moduleSheafExtensionByZeroAdjunction`,
  `moduleSheafExtensionByZeroFromOpen`,
  `openSubspaceModuleSheafExtensionByZero_stalk_isZero_of_not_mem`,
  `openSubsetSheafExtensionByInitialObject_essImage_iff_stalk_isZero_of_not_mem`;
- owner abstraction: the source-facing adjunction owner
  `moduleSheafExtensionByZeroAdjunction`, together with the abelian essential-image criterion from
  `Lemma_6_31_10`;
- primitive data: the ringed space `X`, the open subset `U`, the canonical extension-by-zero
  functor on module sheaves, and the underlying-additive-sheaf functor
  `SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)`;
- derived API: full faithfulness of the module extension-by-zero functor and the module-valued
  zero-stalk essential-image criterion, with the additive criterion used only as an internal
  bridge.

Source/core/bridge triage:
- `source-facing`: the Stacks-project module-sheaf statements in parts (1) and (2);
- `core/canonical`: the explicit `j_! ⊣ j^{-1}` owner from `Lemma_6_31_8` and the abelian owner
  criterion from `Lemma_6_31_10`;
- `bridge/view`: this file’s passage from module-valued stalks to underlying additive stalks via
  `SheafOfModules.toSheaf`.

This file should therefore keep the source-facing module-sheaf statements as the public API: no
new wrapper owner is needed, and the additive-stalk criterion should appear only internally in the
proof of part (2).
-/

section

variable {X : RingedSpace.{u}}

local notation "𝒪X" => RingedSpace.ringCatSheaf X

-- Proof sketch: the explicit extension-by-zero functor agrees with the usual left adjoint to
-- restriction along the open immersion `j : U ↪ X`, and the unit `id ⟶ j⁻¹ j_!` is an
-- isomorphism on module sheaves over `U`; hence `j_!` is fully faithful.
/-- First assertion of Lemma 6.31.12: for a ringed space `(X, \mathcal{O}_X)` and an open
subspace `j : U ↪ X`,
the canonical extension-by-zero functor
`j_! : \textit{Mod}(\mathcal{O}|_U) \to \textit{Mod}(\mathcal{O})`
is fully faithful. -/
instance openSubsetModuleSheafExtensionByZero_fullyFaithful
    (U : Opens X.carrier) :
    (openSubsetModuleSheafExtensionByZero U 𝒪X).FullyFaithful := by
  let h :
      openSubsetModuleSheafExtensionByZero U 𝒪X ⊣ moduleSheafRestrictionToOpen U 𝒪X :=
    openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U
  letI : IsIso h.unit := by
    change IsIso ((openSubspaceModuleSheafExtensionByZero_unitIso (X := X) U).hom)
    infer_instance
  simpa using h.fullyFaithfulLOfIsIsoUnit

/-- Helper for Lemma 6.31.12: after forgetting the module structure, restricting a module sheaf to
`U` agrees with pulling back the underlying additive sheaf along the open inclusion. -/
private noncomputable abbrev moduleSheafRestrictionToOpen_toSheafIso
    (U : Opens X.carrier) (𝒢 : SheafOfModules 𝒪X) :
    (SheafOfModules.toSheaf
        ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj 𝒪X)).obj
      ((moduleSheafRestrictionToOpen U 𝒪X).obj 𝒢) ≅
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj
        ((SheafOfModules.toSheaf 𝒪X).obj 𝒢) := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  let e₁ :=
    (SheafOfModules.toSheaf
        ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj 𝒪X)).mapIso
      ((moduleSheafRestrictionToOpen_compare_open_embedding_pushforward U 𝒪X).symm.app 𝒢)
  let e₂ :=
    ((Topology.IsOpenEmbedding.sheafPullbackIso AddCommGrpCat U.isOpenEmbedding).app
      ((SheafOfModules.toSheaf 𝒪X).obj 𝒢)).symm
  -- The concrete open-embedding restriction owner forgets directly to the naive additive
  -- pullback, and `sheafPullbackIso` identifies that naive pullback with the canonical one.
  simpa [SheafOfModules.toSheaf, SheafOfModules.pushforward] using e₁ ≪≫ e₂

/-- Helper for Lemma 6.31.12: the restriction-side comparison from modules to underlying additive
sheaves is natural in the ambient module sheaf. -/
private noncomputable abbrev moduleSheafRestrictionToOpen_toSheafNatIso
    (U : Opens X.carrier) :
    moduleSheafRestrictionToOpen U 𝒪X ⋙
        SheafOfModules.toSheaf
          ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj 𝒪X) ≅
      SheafOfModules.toSheaf 𝒪X ⋙
        TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion' := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  let e₁ := CategoryTheory.Functor.isoWhiskerRight
    (moduleSheafRestrictionToOpen_compare_open_embedding_pushforward U 𝒪X).symm
    (SheafOfModules.toSheaf
      ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj 𝒪X))
  let e₂ := CategoryTheory.Functor.isoWhiskerLeft
    (SheafOfModules.toSheaf 𝒪X)
    ((Topology.IsOpenEmbedding.sheafPullbackIso AddCommGrpCat U.isOpenEmbedding).symm)
  -- First rewrite restriction via the open-embedding pushforward owner, then replace the naive
  -- open-embedding pullback by the canonical sheaf pullback.
  exact e₁ ≪≫ e₂

/-- Helper for Lemma 6.31.12: `SheafOfModules.toSheaf` preserves and reflects isomorphisms on the
module counit component, so only the additive comparison remains to be checked. -/
private theorem openSubsetModuleSheafExtensionByZero_counit_isIso_iff_toSheaf_map
    (U : Opens X.carrier) (𝒢 : SheafOfModules 𝒪X) :
    IsIso ((openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U).counit.app 𝒢) ↔
      IsIso
        ((SheafOfModules.toSheaf 𝒪X).map
          ((openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U).counit.app 𝒢)) := by
  constructor
  · intro hCounit
    letI := hCounit
    -- Once the module counit is invertible, any functor preserves that invertibility.
    simpa using
      (Functor.map_isIso (SheafOfModules.toSheaf 𝒪X)
        ((openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U).counit.app 𝒢))
  · intro hCounit
    letI := hCounit
    -- Conversely, `toSheaf` reflects isomorphisms because it is faithful and its composition with
    -- `sheafToPresheaf` is the forgetful functor to additive presheaves.
    exact isIso_of_reflects_iso
      ((openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U).counit.app 𝒢)
      (SheafOfModules.toSheaf 𝒪X)

/-- Helper for Lemma 6.31.12: the restriction-side comparison is natural in the module counit. -/
private theorem moduleSheafRestrictionToOpen_toSheafNatIso_naturality_counit
    (U : Opens X.carrier) (𝒢 : SheafOfModules 𝒪X) :
    let A := (moduleSheafRestrictionToOpen U 𝒪X).obj 𝒢
    let ε := (openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U).counit.app 𝒢
    let e := moduleSheafRestrictionToOpen_toSheafIso (X := X) U 𝒢
    let e' := moduleSheafRestrictionToOpen_toSheafIso (X := X) U
      ((openSubsetModuleSheafExtensionByZero U 𝒪X).obj A)
    e'.hom ≫
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).map
        ((SheafOfModules.toSheaf 𝒪X).map ε) =
      (SheafOfModules.toSheaf
          ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj 𝒪X)).map
        ((moduleSheafRestrictionToOpen U 𝒪X).map ε) ≫
      e.hom := by
  let A := (moduleSheafRestrictionToOpen U 𝒪X).obj 𝒢
  let ε := (openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U).counit.app 𝒢
  let e := moduleSheafRestrictionToOpen_toSheafIso (X := X) U 𝒢
  let e' := moduleSheafRestrictionToOpen_toSheafIso (X := X) U
    ((openSubsetModuleSheafExtensionByZero U 𝒪X).obj A)
  have hnat := (moduleSheafRestrictionToOpen_toSheafNatIso (X := X) U).hom.naturality ε
  -- Expand the whiskered functors in the naturality square to isolate the concrete counit step.
  simpa [A, ε, e, e', Category.assoc] using hnat.symm

/-- Helper for Lemma 6.31.12: the presheaf stalk pullback comparison is natural in the presheaf
argument for sheaves of abelian groups. -/
private theorem presheaf_stalkPullbackIso_hom_naturality
    {Z Y : TopCat.{u}} (f : Z ⟶ Y)
    {ℱ 𝒢 : Y.Presheaf AddCommGrpCat.{u}} (η : ℱ ⟶ 𝒢) (x : Z) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map η ≫
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f 𝒢 x).hom =
      (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ x).hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η) := by
  -- Compare both morphisms after precomposing with every germ, where the pullback-stalk owner is
  -- defined.
  apply TopCat.Presheaf.stalk_hom_ext ℱ
  intro V hx
  let h₁ := TopCat.Presheaf.stalkFunctor_map_germ (C := AddCommGrpCat.{u}) V (f x) hx η
  let h₂𝒢 := TopCat.Presheaf.germ_stalkPullbackHom (C := AddCommGrpCat.{u}) f 𝒢 x V hx
  let h₂ℱ := TopCat.Presheaf.germ_stalkPullbackHom (C := AddCommGrpCat.{u}) f ℱ x V hx
  let h₃ := TopCat.Presheaf.stalkFunctor_map_germ (C := AddCommGrpCat.{u}) ((Opens.map f).obj V) x
    hx ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η)
  let A :=
    ℱ.germ V (f x) hx ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map η ≫
      TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f 𝒢 x
  let B :=
    η.app (Opposite.op V) ≫ 𝒢.germ V (f x) hx ≫
      TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f 𝒢 x
  let C :=
    η.app (Opposite.op V) ≫
      ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app 𝒢).app
        (Opposite.op V) ≫
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢).germ ((Opens.map f).obj V) x hx
  let D :=
    ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app ℱ).app
        (Opposite.op V) ≫
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η).app
          (Opposite.op ((Opens.map f).obj V)) ≫
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢).germ ((Opens.map f).obj V) x hx
  let E :=
    ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app ℱ).app
        (Opposite.op V) ≫
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj ℱ).germ ((Opens.map f).obj V) x hx ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η)
  let Z :=
    ℱ.germ V (f x) hx ≫ TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f ℱ x ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η)
  have hA : A = B := by
    simpa [A, B, Category.assoc] using h₁
  have hB : B = C := by
    simpa [B, C, Category.assoc] using congrArg
      (fun k ↦ η.app (Opposite.op V) ≫ k)
      h₂𝒢
  have hC : C = D := by
    have hNat := NatTrans.congr_app
      ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.naturality η)
      (Opposite.op V)
    simpa [C, D, Category.assoc] using
      congrArg
        (fun k ↦
          k ≫ ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢).germ ((Opens.map f).obj V)
            x hx)
        hNat
  have hD : D = E := by
    simpa [D, E, Category.assoc] using congrArg
      (fun k ↦
        ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app ℱ).app
            (Opposite.op V) ≫
          k)
      h₃.symm
  have hE : E = Z := by
    simpa [E, Z, Category.assoc] using congrArg
      (fun k ↦ k ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η))
      h₂ℱ.symm
  exact hA.trans (hB.trans (hC.trans (hD.trans hE)))

/-- Helper for Lemma 6.31.12: the sheaf stalk pullback comparison is natural in the sheaf
argument for sheaves of abelian groups. -/
private theorem sheaf_stalkPullbackIso_hom_naturality
    {Z Y : TopCat.{u}} (f : Z ⟶ Y)
    {ℱ 𝒢 : Y.Sheaf AddCommGrpCat.{u}} (η : ℱ ⟶ 𝒢) (x : Z) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map η.hom) ≫
        (TopCat.Sheaf.stalkPullbackIso f 𝒢 x).hom =
      (TopCat.Sheaf.stalkPullbackIso f ℱ x).hom ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map η).hom)) := by
  -- Unfold the sheaf-level stalk comparison into the presheaf pullback iso, sheafification unit,
  -- and `pullbackIso.inv`, then move `η` through each factor in turn.
  rw [TopCat.Sheaf.stalkPullbackIso_def, TopCat.Sheaf.stalkPullbackIso_def]
  simp only [Iso.trans_hom, Category.assoc]
  let σ :=
    CategoryTheory.sheafifyMap (Opens.grothendieckTopology Z)
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom)
  let τ𝒢 :=
    CategoryTheory.toSheafify (Opens.grothendieckTopology Z)
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢.presheaf)
  let τℱ :=
    CategoryTheory.toSheafify (Opens.grothendieckTopology Z)
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj ℱ.presheaf)
  let π𝒢 :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} Z).map
      ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).inv.app 𝒢)
  let πℱ :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} Z).map
      ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).inv.app ℱ)
  have hsheafify :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom)) ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τ𝒢) =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map σ) := by
    -- This is the stalked form of `toSheafify_naturality`.
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map k)
      (CategoryTheory.toSheafify_naturality
        (J := Opens.grothendieckTopology Z)
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom))
  have hpullbackIso :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map σ) ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map πℱ) ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map η).hom)) := by
    -- This is the stalked form of naturality for `TopCat.Sheaf.pullbackIso.inv`.
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map k)
      (by
        simpa [σ, π𝒢, πℱ] using congrArg
          (fun k ↦ (TopCat.Sheaf.forget AddCommGrpCat.{u} Z).map k)
          (((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).inv).naturality η))
  have h₁ :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map η.hom) ≫
          (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f 𝒢.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τ𝒢) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom)) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τ𝒢) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) := by
    -- First move `η` through the presheaf-level stalk pullback comparison.
    simpa [Category.assoc] using congrArg
      (fun k ↦
        k ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τ𝒢) ≫
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢))
      (presheaf_stalkPullbackIso_hom_naturality f η.hom x)
  have h₂ :
      (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom)) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τ𝒢) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map σ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) := by
    -- Next move `η` through the sheafification unit.
    simpa [Category.assoc] using congrArg
      (fun k ↦
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          k ≫ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢))
      hsheafify
  have h₃ :
      (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map σ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map πℱ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map η).hom)) := by
    -- Finally move `η` through the `pullbackIso.inv` comparison.
    have hpost :
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
            (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
              (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map σ) ≫
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢))) =
          (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
            (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
              (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map πℱ) ≫
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
                  (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map η).hom)))) := by
      exact congrArg
        (fun k ↦
          (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
            (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫ k))
        hpullbackIso
    simpa [Category.assoc] using hpost
  exact
    (by
      simpa [σ, τ𝒢, τℱ, π𝒢, πℱ, Category.assoc] using h₁.trans (h₂.trans h₃))

/-- Helper for Lemma 6.31.12: on points of `U`, the underlying-additive stalk map of the module
counit is an isomorphism. -/
private theorem moduleCounit_toSheaf_stalkMap_isIso_of_mem
    (U : Opens X.carrier) (𝒢 : SheafOfModules 𝒪X) (x : X.carrier) (hx : x ∈ (U : Set X.carrier)) :
    IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (((SheafOfModules.toSheaf 𝒪X).map
          ((openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U).counit.app 𝒢)).hom)) := by
  let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
  let h :
      openSubsetModuleSheafExtensionByZero U 𝒪X ⊣ moduleSheafRestrictionToOpen U 𝒪X :=
    openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U
  let R := moduleSheafRestrictionToOpen U 𝒪X
  let ε := h.counit.app 𝒢
  have hunit : IsIso (h.unit.app (R.obj 𝒢)) := by
    change IsIso ((openSubspaceModuleSheafExtensionByZero_unitIso (X := X) U).hom.app (R.obj 𝒢))
    infer_instance
  letI : IsIso (h.unit.app (R.obj 𝒢)) := hunit
  let unitIso :
      R.obj 𝒢 ≅ R.obj ((openSubsetModuleSheafExtensionByZero U 𝒪X).obj (R.obj 𝒢)) :=
    @asIso _ _ _ _ (h.unit.app (R.obj 𝒢)) hunit
  have hright : R.map ε = inv (h.unit.app (R.obj 𝒢)) := by
    have htriangle : h.unit.app (R.obj 𝒢) ≫ R.map ε = 𝟙 (R.obj 𝒢) := by
      simpa [R, ε] using h.right_triangle_components 𝒢
    have := congrArg (fun k ↦ inv (h.unit.app (R.obj 𝒢)) ≫ k) htriangle
    simpa [Category.assoc] using this
  let e := moduleSheafRestrictionToOpen_toSheafIso (X := X) U 𝒢
  let e' := moduleSheafRestrictionToOpen_toSheafIso (X := X) U
    ((openSubsetModuleSheafExtensionByZero U 𝒪X).obj (R.obj 𝒢))
  have hRmapIso : IsIso (R.map ε) := by
    rw [hright]
    change IsIso unitIso.inv
    infer_instance
  let toSheafRMap :=
    (SheafOfModules.toSheaf
      ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj 𝒪X)).map
      (R.map ε)
  letI :
      IsIso
        toSheafRMap := by
    infer_instance
  let toSheafRMapIso := asIso toSheafRMap
  let toSheafRMapPresheafIso :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso
      toSheafRMapIso
  let ePresheafIso :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso e
  let ePresheafIso' :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso e'
  let toSheafRMapStalkIso :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).mapIso toSheafRMapPresheafIso
  let eStalk := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).mapIso ePresheafIso
  let eStalk' := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).mapIso ePresheafIso'
  letI :
      IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
          toSheafRMap.hom) := by
    change IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map toSheafRMapPresheafIso.hom)
    infer_instance
  letI :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map e.hom.hom) := by
    change IsIso eStalk.hom
    infer_instance
  letI :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map e'.hom.hom) := by
    change IsIso eStalk'.hom
    infer_instance
  let pullbackToSheafMap :=
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).map
      ((SheafOfModules.toSheaf 𝒪X).map ε)
  have hnat := moduleSheafRestrictionToOpen_toSheafNatIso_naturality_counit (U := U) (𝒢 := 𝒢)
  have hnatStalkRaw := congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map k.hom)
      hnat
  have hPullbackMap :
      IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
          pullbackToSheafMap.hom) := by
    have hEq :
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
          ((moduleSheafRestrictionToOpen_toSheafIso (X := X) U
                ((openSubsetModuleSheafExtensionByZero U 𝒪X).obj (R.obj 𝒢))).hom.hom ≫
            ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).map
              ((SheafOfModules.toSheaf 𝒪X).map ε)).hom)) =
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
            (toSheafRMap.hom ≫ e.hom.hom)) := by
      simpa only [R, ε] using hnatStalkRaw
    have hCompSplit :
        IsIso
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
                (moduleSheafRestrictionToOpen_toSheafIso (X := X) U
                  ((openSubsetModuleSheafExtensionByZero U 𝒪X).obj (R.obj 𝒢))).hom.hom) ≫
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
              (((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).map
                ((SheafOfModules.toSheaf 𝒪X).map ε)).hom))) := by
      have :
          IsIso
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
              (toSheafRMap.hom ≫ e.hom.hom)) := by
        rw [Functor.map_comp]
        change IsIso (toSheafRMapStalkIso.hom ≫ eStalk.hom)
        infer_instance
      rw [← Functor.map_comp]
      rw [hEq]
      exact this
    have hCompRaw :
        IsIso
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
            (e'.hom.hom ≫ pullbackToSheafMap.hom)) := by
      rw [Functor.map_comp]
      simpa [e', pullbackToSheafMap] using hCompSplit
    have hComp :
        IsIso
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map e'.hom.hom) ≫
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map pullbackToSheafMap.hom)) := by
      simpa [e', pullbackToSheafMap, Functor.map_comp] using hCompRaw
    exact
      (isIso_comp_left_iff
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map e'.hom.hom)
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map pullbackToSheafMap.hom)).1 hComp
  letI :
      IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map pullbackToSheafMap.hom) := hPullbackMap
  let targetPullbackStalkIso :=
    TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U)
      ((SheafOfModules.toSheaf 𝒪X).obj 𝒢) xU
  let sourcePullbackStalkIso :=
    TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U)
      ((SheafOfModules.toSheaf 𝒪X).obj
        ((openSubsetModuleSheafExtensionByZero U 𝒪X).obj (R.obj 𝒢))) xU
  letI : IsIso targetPullbackStalkIso.hom := by
    infer_instance
  letI : IsIso sourcePullbackStalkIso.hom := by
    infer_instance
  have hpullbackNat :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
            (extensionByZeroOpenSubsetInclusion U xU)).map
          (((SheafOfModules.toSheaf 𝒪X).map ε).hom)) ≫
          targetPullbackStalkIso.hom =
        sourcePullbackStalkIso.hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map pullbackToSheafMap.hom) := by
    simpa [ε] using sheaf_stalkPullbackIso_hom_naturality
      (f := extensionByZeroOpenSubsetInclusion U)
      (η := (SheafOfModules.toSheaf 𝒪X).map ε)
      (x := xU)
  have hComp :
      IsIso
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
              (extensionByZeroOpenSubsetInclusion U xU)).map
            (((SheafOfModules.toSheaf 𝒪X).map ε).hom)) ≫
          targetPullbackStalkIso.hom) := by
    let sourceCompIso :=
      sourcePullbackStalkIso ≪≫
        @asIso _ _ _ _
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map pullbackToSheafMap.hom)
          hPullbackMap
    rw [hpullbackNat]
    change IsIso sourceCompIso.hom
    infer_instance
  have hMap :
      IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
            (extensionByZeroOpenSubsetInclusion U xU)).map
          (((SheafOfModules.toSheaf 𝒪X).map ε).hom)) :=
    (isIso_comp_right_iff
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
            (extensionByZeroOpenSubsetInclusion U xU)).map
          (((SheafOfModules.toSheaf 𝒪X).map ε).hom))
      targetPullbackStalkIso.hom).1 hComp
  simpa using hMap

/-- Helper for Lemma 6.31.12: a stalk module is zero exactly when its underlying additive stalk
is zero. -/
private theorem module_stalk_isZero_iff_underlying
    (x : X) (𝒢 : SheafOfModules 𝒪X) :
    IsZero
        (ModuleCat.of ((RingedSpace.ringCatSheaf X).presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk 𝒢.val.presheaf x)) ↔
      IsZero (TopCat.Presheaf.stalk 𝒢.val.presheaf x) := by
  let F :=
    forget₂ (ModuleCat ((RingedSpace.ringCatSheaf X).presheaf.stalk x)) AddCommGrpCat
  constructor
  · intro h
    simpa [F] using F.map_isZero h
  · intro h
    simp only [IsZero.iff_id_eq_zero] at h ⊢
    apply F.map_injective
    simpa [F] using h

-- Proof sketch: an extended module has zero stalks outside `U` by the explicit construction;
-- conversely, if a module sheaf on `X` has zero stalks off `U`, then the canonical counit
-- `j_! j⁻¹ 𝒢 ⟶ 𝒢` is an isomorphism on stalks, so `𝒢` belongs to the essential image.
/-- Lemma 6.31.12 (2): a sheaf of `\mathcal{O}_X`-modules on `X` lies in the essential image of
the canonical extension-by-zero functor from `U` if and only if all of its stalks at points of
`X \setminus U` are zero. -/
theorem openSubsetModuleSheafExtensionByZero_essImage_iff_stalk_isZero_of_not_mem
    (U : Opens X.carrier) (𝒢 : SheafOfModules 𝒪X) :
    (openSubsetModuleSheafExtensionByZero U 𝒪X).essImage 𝒢 ↔
      ∀ x : X, x ∉ (U : Set X.carrier) →
        IsZero
          (ModuleCat.of ((RingedSpace.ringCatSheaf X).presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk 𝒢.val.presheaf x)) := by
  let h :
      openSubsetModuleSheafExtensionByZero U 𝒪X ⊣ moduleSheafRestrictionToOpen U 𝒪X :=
    openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U
  have hFF : (openSubsetModuleSheafExtensionByZero U 𝒪X).FullyFaithful :=
    openSubsetModuleSheafExtensionByZero_fullyFaithful (X := X) U
  letI : (openSubsetModuleSheafExtensionByZero U 𝒪X).Full := hFF.full
  letI : (openSubsetModuleSheafExtensionByZero U 𝒪X).Faithful := hFF.faithful
  have hess : IsIso (h.counit.app 𝒢) ↔ (openSubsetModuleSheafExtensionByZero U 𝒪X).essImage 𝒢 := by
    -- For a fully faithful left adjoint, the counit detects essential-image membership.
    simpa using
      (h.isIso_counit_app_iff_mem_essImage :
        IsIso (h.counit.app 𝒢) ↔ (openSubsetModuleSheafExtensionByZero U 𝒪X).essImage 𝒢)
  constructor
  · intro h𝒢 x hx
    let ε := h.counit.app 𝒢
    let εAdd := (SheafOfModules.toSheaf 𝒪X).map ε
    letI : IsIso ε := hess.mpr h𝒢
    have hToSheaf :
        IsIso εAdd := by
      infer_instance
    letI : IsIso εAdd := hToSheaf
    have hStalkMap :
        IsIso
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map εAdd.hom) := by
      exact (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso εAdd).1 hToSheaf x
    let sourceSheaf :=
      (openSubsetModuleSheafExtensionByZero U 𝒪X).obj
        ((moduleSheafRestrictionToOpen U 𝒪X).obj 𝒢)
    have hSourceZero :
        IsZero
          (TopCat.Presheaf.stalk sourceSheaf.val.presheaf x) := by
      exact
        (module_stalk_isZero_iff_underlying (X := X) x sourceSheaf).1
          (openSubspaceModuleSheafExtensionByZero_stalk_isZero_of_not_mem
            (X := X) (U := U) ((moduleSheafRestrictionToOpen U 𝒪X).obj 𝒢) hx)
    have hTargetZero :
        IsZero (TopCat.Presheaf.stalk 𝒢.val.presheaf x) := by
      letI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map εAdd.hom) := hStalkMap
      exact IsZero.of_iso hSourceZero
        (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map εAdd.hom)).symm
    exact (module_stalk_isZero_iff_underlying (X := X) x 𝒢).2 hTargetZero
  · intro hZero
    let ε := h.counit.app 𝒢
    let εAdd := (SheafOfModules.toSheaf 𝒪X).map ε
    have hToSheaf :
        IsIso εAdd := by
      refine (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso εAdd).2 ?_
      intro x
      by_cases hx : x ∈ (U : Set X.carrier)
      · exact moduleCounit_toSheaf_stalkMap_isIso_of_mem (X := X) U 𝒢 x hx
      · let sourceSheaf :=
            (openSubsetModuleSheafExtensionByZero U 𝒪X).obj
              ((moduleSheafRestrictionToOpen U 𝒪X).obj 𝒢)
        have hSourceZero :
            IsZero (TopCat.Presheaf.stalk sourceSheaf.val.presheaf x) := by
          exact
            (module_stalk_isZero_iff_underlying (X := X) x sourceSheaf).1
              (openSubspaceModuleSheafExtensionByZero_stalk_isZero_of_not_mem
                (X := X) (U := U) ((moduleSheafRestrictionToOpen U 𝒪X).obj 𝒢) hx)
        have hTargetZero :
            IsZero (TopCat.Presheaf.stalk 𝒢.val.presheaf x) := by
          exact (module_stalk_isZero_iff_underlying (X := X) x 𝒢).1 (hZero x hx)
        exact hSourceZero.isIso hTargetZero
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map εAdd.hom)
    have : IsIso ε := by
      exact isIso_of_reflects_iso ε (SheafOfModules.toSheaf 𝒪X)
    exact hess.mp this

end

/-! ### Remark_6_31_13 (from Chap06) -/
open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instConcreteCategory CategoryTheory.Types.instFunLike

noncomputable section

universe u

/-
Domain-style sampling for Remark 6.31.13:
- primary domain: sheaves of sets on a topological space, the extension-by-initial-object functor
  along an open immersion, and the canonical limit-preservation owners
  `IsTerminal`, `PreservesLimit`, and `leftExactFunctor`;
- sampled owner declarations:
  `openSubsetSheafExtensionByInitialObject`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem`,
  `IsTerminal.isTerminalObj`,
  `leftExactFunctor`,
  `leftExactFunctor_iff`,
  `preservesFiniteLimits_of_preservesTerminal_and_pullbacks`;
- owner abstraction: the public owner is the functor `j! U` together with the standard terminal and
  left-exactness owners, not a parallel local wrapper around “image of a terminal object”;
- primitive data: the open subset `U` and a point `x ∉ U`; the stalk-initial statement outside `U`
  is upstream chapter API;
- derived API: failure of terminal-object preservation and hence failure of left exactness.

Source/core/bridge triage:
- `source-facing`: the remark that `j_!` on sheaves of sets is not left exact for `U ≠ X`;
- `core/canonical`: `PreservesLimit (Functor.empty _) (j! U)` and
  `leftExactFunctor _ _ (j! U)`;
- `bridge/view`: the companion statement that the image of a terminal sheaf is not terminal.
-/

section

variable {X : TopCat.{u}}

private theorem exists_not_mem_of_ne_top (U : Opens X) (hU : U ≠ ⊤) :
    ∃ x : X, x ∉ (U : Set X) := by
  classical
  by_contra h
  push Not at h
  apply hU
  ext x
  simp [h x]

private theorem stalk_nonempty_of_isTerminal (F : X.Sheaf (Type u)) (hF : IsTerminal F) (x : X) :
    Nonempty (F.presheaf.stalk x) := by
  let η :
      Sheaf.terminal (Opens.grothendieckTopology X) Types.isTerminalPUnit ⟶ F :=
    hF.from _
  exact ⟨F.presheaf.germ ⊤ x (by simp) ((η.1).app (op ⊤) PUnit.unit)⟩

/-- For a proper open subset `U ⊊ X`, extension by the empty set on sheaves of sets does not send
a terminal object of `Sh(U)` to a terminal object of `Sh(X)`. -/
theorem openSubsetSheafExtensionByInitialObject_obj_terminal_not_isTerminal_of_ne_top
    (U : Opens X) (hU : U ≠ ⊤) :
    ¬ Nonempty (IsTerminal (((j! U :
            (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u)).obj
          (⊤_ ((extensionByZeroOpenSubsetSpace U).Sheaf (Type u)))))) := by
  let T : (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) := ⊤_ _
  intro hT
  obtain ⟨x, hx⟩ := exists_not_mem_of_ne_top U hU
  have hEmpty : IsEmpty (((j! U).obj T).presheaf.stalk x) := by
    exact Concrete.empty_of_initial_of_preserves
      (((j! U).obj T).presheaf.stalk x) ⟨by
        simpa using
          OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem U T hx⟩
  exact hEmpty.false (stalk_nonempty_of_isTerminal ((j! U).obj T) hT.some x).some

/-- For a proper open subset `U ⊊ X`, extension by the empty set on sheaves of sets does not
preserve terminal objects. -/
theorem openSubsetSheafExtensionByInitialObject_not_preservesTerminal_of_ne_top
    (U : Opens X) (hU : U ≠ ⊤) :
    ¬ (PreservesLimit (Functor.empty.{0} ((extensionByZeroOpenSubsetSpace U).Sheaf (Type u)))
        (j! U : (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u))) := by
  intro hF
  letI :
      PreservesLimit (Functor.empty.{0} ((extensionByZeroOpenSubsetSpace U).Sheaf (Type u)))
        (j! U : (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u)) :=
    hF
  exact openSubsetSheafExtensionByInitialObject_obj_terminal_not_isTerminal_of_ne_top U hU
    ⟨terminalIsTerminal.isTerminalObj (j! U :
      (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u))⟩

/-- Remark 6.31.13: if `U` is a proper open subset of `X`, then extension by the empty set
`j_! : Sh(U) ⥤ Sh(X)` on sheaves of sets is not left exact. A witness is that it does not send a
terminal object of `Sh(U)` to a terminal object of `Sh(X)`. -/
theorem openSubsetSheafExtensionByInitialObject_not_leftExact_of_ne_top
    (U : Opens X) (hU : U ≠ ⊤) :
    ¬ (leftExactFunctor ((extensionByZeroOpenSubsetSpace U).Sheaf (Type u)) (X.Sheaf (Type u))
        (j! U : (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u))) := by
  intro hF
  letI : PreservesFiniteLimits
      (j! U : (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u)) := by
    simpa [leftExactFunctor_iff] using hF
  exact openSubsetSheafExtensionByInitialObject_not_preservesTerminal_of_ne_top U hU inferInstance

end
