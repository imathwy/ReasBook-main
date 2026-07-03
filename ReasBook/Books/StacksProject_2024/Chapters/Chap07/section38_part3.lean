import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_38_4 (from Chap07) -/
open CategoryTheory

universe w v u

namespace CategoryTheory

open GrothendieckTopology
open CategoryTheory.ObjectProperty

/- Domain-style sampling for Lemma 7.38.4:
- primary domain: conservative families of points on Grothendieck sites and their behavior under
  localization to slice sites;
- sampled owner declarations:
  `ObjectProperty.IsConservativeFamilyOfPoints`,
  `ObjectProperty.IsConservativeFamilyOfPoints.over`,
  `GrothendieckTopology.HasEnoughPoints`,
  the slice-site instance `[HasEnoughPoints (J.over U)]`;
- source/core/bridge triage:
  `source-facing`: the Stacks statement that a conservative family of points stays conservative on
    each localized site;
  `core/canonical`: the owner theorem `ObjectProperty.IsConservativeFamilyOfPoints.over` and the
    owner class `HasEnoughPoints`;
  `bridge/view`: the localized point construction `Φ.over x` and the derived slice enough-points
    instance.
- primitive data: an object property `P : ObjectProperty (Point J)` and the conservativity proof
  `P.IsConservativeFamilyOfPoints`;
- derived API: the localized family and the enough-points consequence for slice sites.

This file should therefore remain a direct recall/use of the owner theorem, not a parallel local
wrapper around localized point families.
-/

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C]
variable {P : ObjectProperty (Point.{w} J)} [ObjectProperty.Small.{w} P]
variable [J.WEqualsLocallyBijective (Type w)] [HasSheafify J (Type w)]
variable {U : C} [HasSheafify (J.over U) (Type w)]

/- Lemma 7.38.4: if `P` is a conservative family of points of the site `(C, J)`, then the
localized points `Φ.over x` for `Φ ∈ P` and `x : Φ.fiber.obj U` form a conservative family of
points of the localized site `(C/U, J.over U)`. This is the canonical mathlib statement encoding
the textbook family `{q_{i, x}}`. -/
recall IsConservativeFamilyOfPoints.over

end

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C]
variable [J.WEqualsLocallyBijective (Type w)] [HasSheafify J (Type w)]
variable {U : C} [HasSheafify (J.over U) (Type w)]
variable [HasEnoughPoints.{w} J]

/- Companion check: if the site `(C, J)` has enough points, then every localization `(C/U,
J.over U)` has enough points as well; in mathlib this is the canonical instance on `J.over U`. -/
#check (inferInstance : HasEnoughPoints.{w} (J.over U))

end

end CategoryTheory

/-! ### Lemma_7_38_5 (from Chap07) -/
open CategoryTheory.GrothendieckTopology Opposite

universe w v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C]

/- Domain-style sampling for Lemma 7.38.5:
- primary domain: points of Grothendieck sites, localized sites, and cover-local detection of
  isomorphisms of sheaves;
- sampled owner API:
  `GrothendieckTopology.CoversTop`,
  `GrothendieckTopology.HasEnoughPoints`,
  `GrothendieckTopology.Point.map`,
  `GrothendieckTopology.Point.sheafFiberMapIso`;
- source/core/bridge triage:
  `source-facing`: the Stacks criterion that enough points can be checked on a family covering the
    terminal object;
  `core/canonical`: the owners `J.CoversTop` and `J.HasEnoughPoints`;
  `bridge/view`: localized points on `(C / U i, J.over (U i))` are transported to points of
    `(C, J)` by the canonical cocontinuous localization functor `Over.forget (U i)` via
    `Point.map`, and the comparison on stalk functors is owned by `Point.sheafFiberMapIso`.

Primitive data are only the covering-family hypothesis `hcover` and the local enough-points
hypotheses `hlocal`. Any conservative-family packaging on the slice sites, and its transport to
`(C, J)`, is derived API through `HasEnoughPoints.exists_objectProperty` and `Point.map`, so this
file should stay a thin source-facing bridge theorem rather than introducing a second owner.
-/
/-- Lemma 7.38.5: if the family `U` covers the terminal object of the site `(C, J)` and each
localized site `(C / U i, J.over (U i))` has enough points, then `(C, J)` has enough points. This
is the canonical site-level reformulation of the Stacks hypothesis that
`∐ h_{U_i}^{\#} ⟶ *` is surjective. -/
theorem hasEnoughPoints_of_covering_family_and_slice_sites
    {I : Type w} (U : I → C) (hcover : J.CoversTop U)
    (hlocal : ∀ i : I, HasEnoughPoints.{w} (J.over (U i))) :
    HasEnoughPoints.{w} J := by
  have hlocal' :
      ∀ i : I, ∃ (ι : Type w) (p : ι → Point.{w} (J.over (U i))),
        (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints := fun i ↦
    hasEnoughPoints_iff_exists_conservativePointFamily.1 (hlocal i)
  choose ι p hp using hlocal'
  refine
    hasEnoughPoints_iff_exists_conservativePointFamily.2
      ⟨Σ i, ι i, fun s ↦ (p s.1 s.2).map (Over.forget (U s.1)) J, ?_⟩
  rw [isConservativePointFamily_iff]
  intro ℱ 𝒢 φ hφ
  have hslice :
      ∀ i : I, IsIso ((J.overPullback (Type w) (U i)).map φ) := by
    intro i
    exact
      (isConservativePointFamily_iff (p i)).1 (hp i)
        ((J.overPullback (Type w) (U i)).map φ) fun j ↦ by
          let e :
              ((p i j).map (Over.forget (U i)) J).sheafFiber ≅
                J.overPullback (Type w) (U i) ⋙ (p i j).sheafFiber :=
            (p i j).sheafFiberMapIso (Over.forget (U i)) J (Type w)
          exact (NatIso.isIso_map_iff e φ).1 (hφ ⟨i, j⟩)
  have hbij :
      ∀ (i : I) {Y : C} (g : Y ⟶ U i), Function.Bijective (φ.hom.app (op Y)) := by
    intro i Y g
    let φi := (J.overPullback (Type w) (U i)).map φ
    have hcomp :
        IsIso (((sheafToPresheaf (J.over (U i)) (Type w)).map φi).app (op (Over.mk g))) := by
      have : IsIso ((sheafToPresheaf (J.over (U i)) (Type w)).map φi) := by infer_instance
      exact (NatTrans.isIso_iff_isIso_app _).1 this _
    exact (isIso_iff_bijective _).1 (by
      simpa [GrothendieckTopology.overPullback] using hcomp)
  have hlocinj : Sheaf.IsLocallyInjective φ := by
    change Presheaf.IsLocallyInjective J φ.hom
    constructor
    intro X x y hxy
    refine J.superset_covering ?_ (hcover X.unop)
    intro Y g hg
    rw [Presheaf.equalizerSieve_apply]
    rcases hg with ⟨i, ⟨a⟩⟩
    have hxg : φ.hom.app (op Y) ((ℱ.obj.map g.op) x) = (𝒢.obj.map g.op) (φ.hom.app X x) := by
      simpa using congr_fun (φ.hom.naturality g.op) x
    have hyg : φ.hom.app (op Y) ((ℱ.obj.map g.op) y) = (𝒢.obj.map g.op) (φ.hom.app X y) := by
      simpa using congr_fun (φ.hom.naturality g.op) y
    have hmid : (𝒢.obj.map g.op) (φ.hom.app X x) = (𝒢.obj.map g.op) (φ.hom.app X y) := by
      simpa using congr_arg (𝒢.obj.map g.op) hxy
    apply (hbij i a).injective
    exact hxg.trans (hmid.trans hyg.symm)
  have hlocsurj : Sheaf.IsLocallySurjective φ := by
    change Presheaf.IsLocallySurjective J φ.hom
    constructor
    intro X s
    refine J.superset_covering ?_ (hcover X)
    intro Y g hg
    rw [Presheaf.imageSieve_apply]
    rcases hg with ⟨i, ⟨a⟩⟩
    obtain ⟨t, ht⟩ := (hbij i a).surjective ((𝒢.obj.map g.op) s)
    exact ⟨t, ht⟩
  exact (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨hlocinj, hlocsurj⟩

end

end CategoryTheory

/-! ### Lemma_7_38_6 (from Chap07) -/
open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Limits

noncomputable section

universe w v₁ v₂ u₁ u₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Helper for Lemma 7.38.6: once the composite fiber functor `u ⋙ Φ.fiber` is realized by a
point `Ψ`, the presheaf-fiber comparison from Lemma `7.34.1` specializes to `Type w`. -/
noncomputable def pointwise_composite_presheafFiberIso
    (u : C ⥤ D)
    [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension F]
    (Φ : Point.{w} K) (Ψ : Point.{w} J)
    [HasColimitsOfShape (u ⋙ Φ.fiber).Elementsᵒᵖ (Type w)]
    (hΨ : Ψ.fiber = u ⋙ Φ.fiber) :
    (u.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w) ⋙ Φ.presheafFiber ≅ Ψ.presheafFiber := by
  -- First compare the pushforward presheaf fiber with the composite fiber functor `u ⋙ Φ.fiber`.
  let e :
      (u.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w) ⋙ Φ.presheafFiber ≅
        (u ⋙ Φ.fiber).presheafFiber :=
    (((u.op.lanAdjunction (Type w)).comp (presheafCostalkAdjunction Φ.fiber)).ofNatIsoRight
        (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.whiskeringLeftObjCompIso u.op Φ.fiber.op).symm)).leftAdjointUniq
      (presheafCostalkAdjunction (u ⋙ Φ.fiber))
  -- Then rewrite the resulting presheaf fiber along the chosen identification with `Ψ.fiber`.
  let e' : (u ⋙ Φ.fiber).presheafFiber ≅ Ψ.presheafFiber := by
    let hpresheaf : (u ⋙ Φ.fiber).presheafFiber = Ψ.presheafFiber := by
      cases Ψ
      simp at hΨ
      cases hΨ
      rfl
    exact eqToIso hpresheaf
  exact e ≪≫ e'

/-- Helper for Lemma 7.38.6: for each point `Φ` in the conservative family on `(D, K)`, the
stalk of `u.sheafPullback` at `Φ` is canonically identified with the stalk of a point of
`(C, J)` realizing the composite fiber functor `u ⋙ Φ.fiber`. -/
noncomputable def pointwise_composite_sheafFiberIso
    (u : C ⥤ D) [u.IsContinuous J K]
    [HasWeakSheafify K (Type w)]
    [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension F]
    (P : ObjectProperty (Point.{w} K))
    (hpoint : ∀ Φ : P.FullSubcategory, ∃ Ψ : Point.{w} J, Ψ.fiber = u ⋙ Φ.obj.fiber)
    (Φ : P.FullSubcategory) :
    Σ Ψ : Point.{w} J, u.sheafPullback (Type w) J K ⋙ Φ.obj.sheafFiber ≅ Ψ.sheafFiber := by
  classical
  let Ψ := Classical.choose (hpoint Φ)
  let hΨ : Ψ.fiber = u ⋙ Φ.obj.fiber := Classical.choose_spec (hpoint Φ)
  let _ : HasColimitsOfShape (u ⋙ Φ.obj.fiber).Elementsᵒᵖ (Type w) := by
    exact hΨ.symm ▸ (inferInstance : HasColimitsOfShape Ψ.fiber.Elementsᵒᵖ (Type w))
  refine ⟨Ψ, ?_⟩
  -- Replace the abstract pullback with the explicit left-Kan/sheafification model.
  let e₁ := Functor.isoWhiskerRight
    (Functor.sheafPullbackConstruction.sheafPullbackIso u (Type w) J K) Φ.obj.sheafFiber
  -- Convert the final sheafification step on `(D, K)` into the presheaf fiber of `Φ`.
  let e₂ := Functor.isoWhiskerLeft
    (sheafToPresheaf J (Type w) ⋙ (u.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w))
    (Φ.obj.presheafToSheafCompSheafFiberIso (Type w))
  -- Compare that presheaf fiber with the chosen point `Ψ` on `(C, J)`.
  let e₃ := Functor.isoWhiskerLeft (sheafToPresheaf J (Type w))
    (pointwise_composite_presheafFiberIso u Φ.obj Ψ hΨ)
  -- Finally identify the resulting functor on sheaves with the stalk functor of `Ψ`.
  let e₄ : sheafToPresheaf J (Type w) ⋙ Ψ.presheafFiber ≅ Ψ.sheafFiber :=
    Ψ.sheafToPresheafCompPresheafFiberIso
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- Helper for Lemma 7.38.6: the composite of `u.sheafPullback` with the stalk functor of each
point in the conservative family preserves finite limits. -/
theorem pointwise_composite_preservesFiniteLimits
    (u : C ⥤ D) [u.IsContinuous J K]
    [LocallySmall.{w} C]
    [HasWeakSheafify K (Type w)]
    [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension F]
    (P : ObjectProperty (Point.{w} K))
    (hpoint : ∀ Φ : P.FullSubcategory, ∃ Ψ : Point.{w} J, Ψ.fiber = u ⋙ Φ.obj.fiber)
    (Φ : P.FullSubcategory) :
    PreservesFiniteLimits (u.sheafPullback (Type w) J K ⋙ Φ.obj.sheafFiber) := by
  rcases pointwise_composite_sheafFiberIso u P hpoint Φ with ⟨Ψ, e⟩
  -- Transport the canonical finite-limit preservation of the stalk of an actual point of `(C, J)`.
  let _ : PreservesFiniteLimits (Ψ.sheafFiber : Sheaf J (Type w) ⥤ Type w) := by
    infer_instance
  exact preservesFiniteLimits_of_natIso (F := Ψ.sheafFiber)
    (G := u.sheafPullback (Type w) J K ⋙ Φ.obj.sheafFiber) e.symm

/-- Helper for Lemma 7.38.6: if the composite with each point in a conservative family is the
stalk functor of a point of `(C, J)`, then `u.sheafPullback` is exact on set-valued sheaves. -/
theorem sheafPullback_exact_of_conservative_family_pointwiseComposite
    (u : C ⥤ D) [u.IsContinuous J K]
    [LocallySmall.{w} C]
    [LocallySmall.{w} D]
    [HasWeakSheafify K (Type w)]
    [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension F]
    (P : ObjectProperty (Point.{w} K))
    (hP : P.IsConservativeFamilyOfPoints)
    (hpoint : ∀ Φ : P.FullSubcategory, ∃ Ψ : Point.{w} J, Ψ.fiber = u ⋙ Φ.obj.fiber) :
    exactFunctor (Sheaf J (Type w)) (Sheaf K (Type w)) (u.sheafPullback (Type w) J K) := by
  let _ : (u.sheafPullback (Type w) J K).IsLeftAdjoint :=
    (u.sheafAdjunctionContinuous (Type w) J K).isLeftAdjoint
  rw [CategoryTheory.exactFunctor_iff]
  refine ⟨?_, inferInstance⟩
  · -- Check finite limits after all stalk functors in the conservative family.
    apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize
    intro I _ _
    constructor
    intro F
    apply preservesLimit_of_preserves_limit_cone (limit.isLimit F)
    let h := hP.jointlyReflectIsomorphisms (Type w)
    let _ : ∀ Φ : P.FullSubcategory,
        PreservesLimit F (u.sheafPullback (Type w) J K ⋙ Φ.obj.sheafFiber) :=
      fun Φ ↦ by
        let _ : PreservesFiniteLimits (u.sheafPullback (Type w) J K ⋙ Φ.obj.sheafFiber) :=
          pointwise_composite_preservesFiniteLimits u P hpoint Φ
        infer_instance
    refine h.jointlyReflectsLimit ?_
    intro Φ
    exact isLimitOfPreserves (u.sheafPullback (Type w) J K ⋙ Φ.obj.sheafFiber) (limit.isLimit F)

/-- Helper for Lemma 7.38.6: the pointwise exactness argument already proves that
`u.sheafPullback` is left exact on set-valued sheaves. -/
theorem sheafPullback_preservesFiniteLimits_of_conservative_family_pointwiseComposite
    (u : C ⥤ D) [u.IsContinuous J K]
    [LocallySmall.{w} C]
    [LocallySmall.{w} D]
    [HasWeakSheafify K (Type w)]
    [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension F]
    (P : ObjectProperty (Point.{w} K))
    (hP : P.IsConservativeFamilyOfPoints)
    (hpoint : ∀ Φ : P.FullSubcategory, ∃ Ψ : Point.{w} J, Ψ.fiber = u ⋙ Φ.obj.fiber) :
    PreservesFiniteLimits (u.sheafPullback (Type w) J K) := by
  -- Reuse the exactness theorem proved just above and extract its left exactness component.
  have hexact :
      exactFunctor (Sheaf J (Type w)) (Sheaf K (Type w)) (u.sheafPullback (Type w) J K) :=
    sheafPullback_exact_of_conservative_family_pointwiseComposite u P hP hpoint
  rw [CategoryTheory.exactFunctor_iff] at hexact
  exact hexact.1

/- Domain-style sampling for Lemma 7.38.6:
- primary domain: points of Grothendieck sites and morphisms of sites;
- sampled owner API:
  `IsMorphismOfSites`,
  `ObjectProperty.IsConservativeFamilyOfPoints`,
  `Point.sheafFiberComapIso`,
  the instance `IsMorphismOfSites J typesGrothendieckTopology p.fiber` from Lemma 7.32.8;
- source/core/bridge triage:
  `source-facing`: the pointwise hypothesis that each composite `u ⋙ Φ.fiber` comes from a point
    of `(C, J)`, indexed canonically by `P.FullSubcategory`;
  `core/canonical`: the owner predicate `IsMorphismOfSites J K u`;
  `bridge/view`: the theorem below, which upgrades the source-facing pointwise condition along a
    conservative family of points to the canonical morphism-of-sites owner.

Primitive data are only the continuous functor `u`, the conservative family `P`, and the
pointwise realization hypothesis on `P.FullSubcategory`. Exactness of stalk functors and the
induced morphism-of-sites structure are derived owner API, so this file should remain a thin
bridge rather than introducing any parallel wrapper around `IsMorphismOfSites`.
-/
-- Proof sketch: for each point `Φ` in the conservative family, choose a point of `(C, J)` whose
-- fiber functor is `u ⋙ Φ.fiber`. Then the stalk functor at `Φ` after applying the inverse-image
-- functor `u.sheafPullback` identifies with the stalk functor of that chosen point, hence is exact.
-- Exactness of `u.sheafPullback` can be checked on a conservative family of points by
-- Lemma 7.38.2, so `u` defines a morphism of sites by Definition 7.14.1.
/-- Lemma 7.38.6, repaired owner form: if `u : C ⥤ D` is continuous, `P` is a conservative
family of points of `(D, K)`, and every composite fiber functor `u ⋙ Φ.fiber` comes from a point
of `(C, J)`, then the inverse-image functor on sheaves is exact. The source proof identifies this
with being a morphism of sites; the current Lean owner `IsMorphismOfSites` also contains the
extra field `RepresentablyFlat u`, so the dependency-closed target here is exactness of
`u.sheafPullback`. -/
theorem isMorphismOfSites_of_conservativeFamilyOfPoints_of_pointwiseComposite
    (u : C ⥤ D) [u.IsContinuous J K]
    [LocallySmall.{w} C] [LocallySmall.{w} D]
    [HasWeakSheafify K (Type w)]
    [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension F]
    (P : ObjectProperty (Point.{w} K))
    (hP : P.IsConservativeFamilyOfPoints)
    (hpoint : ∀ Φ : P.FullSubcategory, ∃ Ψ : Point.{w} J, Ψ.fiber = u ⋙ Φ.obj.fiber) :
    exactFunctor (Sheaf J (Type w)) (Sheaf K (Type w)) (u.sheafPullback (Type w) J K) := by
  exact sheafPullback_exact_of_conservative_family_pointwiseComposite u P hP hpoint

end
