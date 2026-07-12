import Mathlib
import StacksProject_2024.Chap07.Example_7_6_5
import StacksProject_2024.Chap07.Proposition_7_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Action

universe u

namespace CategoryTheory

noncomputable section

/- Domain-style sampling for Example 7.41.5:
- primary domain: continuous site pushforward on the surjective sites of `G`-sets and `H`-sets,
  together with the action-level coinduction model for `Action.res (Type u) φ` and the
  left-regular-sections owner from Proposition 7.9.1;
- sampled owner API:
  `Action.res`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafPushforwardContinuous`,
  `(Action.jointlySurjectiveTopology G).yonedaEquiv`,
  `sheafSectionsOnLeftRegularFunctor`,
  `Representation.coind'`;
- source/core/bridge triage:
  `source-facing`: the counit `f⁻¹ f_* ℱ ⟶ ℱ` for the continuous morphism of sites induced by
    `Action.res (Type u) φ`, together with its evaluation-at-`1` description on the `Map_G(H, S)`
    model;
  `core/canonical`: the adjunction `sheafAdjunctionContinuous` and the owner predicate
    `Sheaf.IsLocallySurjective` on its counit;
  `bridge/view`: the explicit `H →[G] S` action-level model.

The public refinement below exposes the source-facing positive statement directly on the canonical
sheaf counit, and keeps the explicit evaluation-at-`1` map only as a companion view. The formal
bridge is evaluation of the pushforward on the left regular `H`-set, which canonically recovers
the explicit `H →[G] S` model.
-/

/- The source-facing explicit `Map_G(H, S)` model used internally below: equivariant maps from the
left `G`-set on `H` induced by `φ : G →* H` to the `G`-set `S`. Public statements use the direct
canonical type expression `H →[G] S` rather than a file-local wrapper. -/
private abbrev restrictedEquivariantMaps
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (S : Type u) [MulAction G S] :=
  letI : MulAction G H := MulAction.compHom H φ
  H →[G] S

private theorem actionRes_preservesFiniteLimits
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    PreservesFiniteLimits (Action.res (Type u) φ) := by
  let _ : PreservesFiniteLimits ((Action.res (Type u) φ) ⋙ Action.forget (Type u) G) := by
    change PreservesFiniteLimits (Action.forget (Type u) H)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves
    (Action.res (Type u) φ) (Action.forget (Type u) G)

private instance actionRes_representablyFlat
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    RepresentablyFlat (Action.res (Type u) φ) := by
  let _ : PreservesFiniteLimits (Action.res (Type u) φ) :=
    actionRes_preservesFiniteLimits φ
  exact flat_of_preservesFiniteLimits (Action.res (Type u) φ)

private instance actionRes_coverPreserving
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    CoverPreserving (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) (Action.res (Type u) φ) where
  cover_preserve {U} {S} hS := by
    rw [Action.mem_jointlySurjectiveTopology_iff] at hS ⊢
    intro x
    rcases hS x with ⟨Y, f, hf, hx⟩
    exact
      ⟨(Action.res (Type u) φ).obj Y, (Action.res (Type u) φ).map f,
        Sieve.image_mem_functorPushforward (Action.res (Type u) φ) S hf, hx⟩

@[instance 10000] instance actionRes_isContinuous
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    (Action.res (Type u) φ).IsContinuous (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat (Action.jointlySurjectiveTopology G) (Action.res (Type u) φ))
    (actionRes_coverPreserving φ)

@[reducible] private def equivariantMapRightTranslation
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (S : Type u) [MulAction G S] :
    MulAction H (restrictedEquivariantMaps φ S) := by
  letI : MulAction G H := MulAction.compHom H φ
  exact
    { smul := fun h a ↦
        { toFun := fun x ↦ a (x * h)
          map_smul' := fun g x ↦ by
            change a ((φ g * x) * h) = g • a (x * h)
            rw [mul_assoc]
            exact a.map_smul g (x * h) }
      one_smul := fun a ↦ by
        apply MulActionHom.ext
        intro x
        change a (x * 1) = a x
        simp
      mul_smul := fun h₁ h₂ a ↦ by
        apply MulActionHom.ext
        intro x
        change a (x * (h₁ * h₂)) = a ((x * h₁) * h₂)
        rw [mul_assoc] }

/- The explicit `H`-action on `Map_G(H, S)` used internally below, given by right translation on
the source `H`. The corresponding left-regular-sections comparison is kept private; the public
companion statement uses the direct canonical type expression `H →[G] S`. -/
@[reducible] private def equivariantMapAction
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (S : Type u) [MulAction G S] :
    Action (Type u) H :=
  letI : MulAction G H := MulAction.compHom H φ
  letI : MulAction H (restrictedEquivariantMaps φ S) := equivariantMapRightTranslation φ S
  Action.ofMulAction H (restrictedEquivariantMaps φ S)

private abbrev equivariantMapObj
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (S : Action (Type u) G) :
    Action (Type u) H :=
  letI : MulAction G S.V := instMulAction S
  equivariantMapAction φ S.V

private def equivariantMapMap
    {G H : Type u} [Group G] [Group H] (φ : G →* H)
    {X Y : Action (Type u) G} (f : X ⟶ Y) :
    equivariantMapObj φ X ⟶ equivariantMapObj φ Y :=
  letI : MulAction G X.V := instMulAction X
  letI : MulAction G Y.V := instMulAction Y
  letI : MulAction G H := MulAction.compHom H φ
  letI : MulAction H (restrictedEquivariantMaps φ X.V) := equivariantMapRightTranslation φ X.V
  letI : MulAction H (restrictedEquivariantMaps φ Y.V) := equivariantMapRightTranslation φ Y.V
  { hom := fun a : restrictedEquivariantMaps φ X.V ↦
      { toFun := fun h ↦ f.hom (a h)
        map_smul' := fun g h ↦ by
          simpa using congrArg (fun k ↦ k (a h)) (f.comm g) }
    comm := fun h ↦ by
      funext (a : restrictedEquivariantMaps φ X.V)
      apply MulActionHom.ext
      intro x
      rfl }

private theorem equivariantMapMap_id
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (X : Action (Type u) G) :
    equivariantMapMap φ (𝟙 X) = 𝟙 (equivariantMapObj φ X) := by
  letI : MulAction G X.V := instMulAction X
  letI : MulAction G H := MulAction.compHom H φ
  letI : MulAction H (restrictedEquivariantMaps φ X.V) := equivariantMapRightTranslation φ X.V
  apply Action.hom_ext
  funext (a : restrictedEquivariantMaps φ X.V)
  apply MulActionHom.ext
  intro x
  change a x = a x
  rfl

private theorem equivariantMapMap_comp
    {G H : Type u} [Group G] [Group H] (φ : G →* H)
    {X Y Z : Action (Type u) G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    equivariantMapMap φ (f ≫ g) = equivariantMapMap φ f ≫ equivariantMapMap φ g := by
  letI : MulAction G X.V := instMulAction X
  letI : MulAction G Y.V := instMulAction Y
  letI : MulAction G Z.V := instMulAction Z
  letI : MulAction G H := MulAction.compHom H φ
  letI : MulAction H (restrictedEquivariantMaps φ X.V) := equivariantMapRightTranslation φ X.V
  letI : MulAction H (restrictedEquivariantMaps φ Y.V) := equivariantMapRightTranslation φ Y.V
  letI : MulAction H (restrictedEquivariantMaps φ Z.V) := equivariantMapRightTranslation φ Z.V
  apply Action.hom_ext
  funext (a : restrictedEquivariantMaps φ X.V)
  apply MulActionHom.ext
  intro x
  change g.hom (f.hom (a x)) = g.hom (f.hom (a x))
  rfl

/-- An explicit action-level model for the pushforward attached to a group homomorphism
`φ : G → H`: it sends a `G`-set `S` to the `H`-set of `G`-equivariant maps `H → S`, where `G`
acts on `H` through `φ` and `H` acts by right translation on the source. The canonical
characterization is the continuous pushforward on sheaves along `Action.res (Type u) φ`; this
private explicit model is kept only to support the concrete `H →[G] S` companion statements
below. -/
private def equivariantMapPushforward
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    Action (Type u) G ⥤ Action (Type u) H where
  obj := equivariantMapObj φ
  map := equivariantMapMap φ
  map_id := equivariantMapMap_id φ
  map_comp := equivariantMapMap_comp φ

private def equivariantMapPushforwardHomEquiv
    {G H : Type u} [Group G] [Group H] (φ : G →* H)
    (X : Action (Type u) H) (Y : Action (Type u) G) :
    (((Action.res (Type u) φ).obj X) ⟶ Y) ≃ (X ⟶ equivariantMapObj φ Y) := by
  letI : MulAction H X.V := instMulAction X
  letI : MulAction G Y.V := instMulAction Y
  letI : MulAction G H := MulAction.compHom H φ
  letI : MulAction H (restrictedEquivariantMaps φ Y.V) := equivariantMapRightTranslation φ Y.V
  refine
    { toFun := fun f ↦
        { hom := fun x ↦
            { toFun := fun h ↦ f.hom (h • x)
              map_smul' := fun g h ↦ by
                change f.hom ((φ g * h) • x) = g • f.hom (h • x)
                simpa [mul_smul] using congrArg (fun k ↦ k (h • x)) (f.comm g) }
          comm := fun h ↦ by
            funext x
            apply MulActionHom.ext
            intro h'
            change f.hom (h' • (h • x)) = f.hom ((h' * h) • x)
            rw [mul_smul] }
      invFun := fun a ↦
        { hom := fun x ↦ (show restrictedEquivariantMaps φ Y.V from a.hom x) 1
          comm := fun g ↦ by
            funext (x : X.V)
            have hx := congrArg
              (fun k ↦ (show restrictedEquivariantMaps φ Y.V from k x) 1) (a.comm (φ g))
            have hx' :
                (show restrictedEquivariantMaps φ Y.V from a.hom ((φ g) • x)) 1 =
                  (show restrictedEquivariantMaps φ Y.V from
                    ((equivariantMapObj φ Y).ρ (φ g)) (a.hom x)) 1 := by
              simpa using hx
            have hy :
                (show restrictedEquivariantMaps φ Y.V from
                  ((equivariantMapObj φ Y).ρ (φ g)) (a.hom x)) 1 =
                    g • ((show restrictedEquivariantMaps φ Y.V from a.hom x) 1) := by
              change (show restrictedEquivariantMaps φ Y.V from a.hom x) (1 * φ g) =
                  g • ((show restrictedEquivariantMaps φ Y.V from a.hom x) 1)
              have hy := (show restrictedEquivariantMaps φ Y.V from a.hom x).map_smul g 1
              change (show restrictedEquivariantMaps φ Y.V from a.hom x) (φ g * 1) =
                  g • ((show restrictedEquivariantMaps φ Y.V from a.hom x) 1) at hy
              simpa using hy
            exact hx'.trans (by simpa using hy) }
      left_inv := fun f ↦ by
        apply Action.hom_ext
        funext (x : X.V)
        change f.hom ((1 : H) • x) = f.hom x
        simp
      right_inv := fun a ↦ by
        apply Action.hom_ext
        funext (x : X.V)
        apply MulActionHom.ext
        intro h
        have hx := congrArg
          (fun k ↦ (show restrictedEquivariantMaps φ Y.V from k x) 1) (a.comm h)
        change (show restrictedEquivariantMaps φ Y.V from a.hom (h • x)) 1 =
            (show restrictedEquivariantMaps φ Y.V from
              ((equivariantMapObj φ Y).ρ h) (a.hom x)) 1 at hx
        change (show restrictedEquivariantMaps φ Y.V from a.hom (h • x)) 1 =
            (show restrictedEquivariantMaps φ Y.V from a.hom x) (1 * h) at hx
        simpa using hx }

/-- Restriction along `φ` is left adjoint to the explicit equivariant-map pushforward model. -/
private noncomputable def equivariantMapPushforwardAdjunction
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    Action.res (Type u) φ ⊣ equivariantMapPushforward φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := equivariantMapPushforwardHomEquiv φ
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply Action.hom_ext
        funext x
        rfl
      homEquiv_naturality_right := by
        intro X Y Y' f g
        letI : MulAction G Y'.V := instMulAction Y'
        letI : MulAction G H := MulAction.compHom H φ
        letI : MulAction H (restrictedEquivariantMaps φ Y'.V) := equivariantMapRightTranslation φ Y'.V
        apply Action.hom_ext
        funext x
        apply MulActionHom.ext
        intro h
        rfl }

/-- The explicit functor `equivariantMapPushforward φ` is the right adjoint in the adjunction
`Action.res (Type u) φ ⊣ equivariantMapPushforward φ`. -/
@[instance 10000] instance
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    (equivariantMapPushforward φ).IsRightAdjoint :=
  (equivariantMapPushforwardAdjunction φ).isRightAdjoint

private noncomputable def yonedaCompSheafPushforwardContinuousIso
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    (Action.jointlySurjectiveTopology G).yoneda ⋙
        (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
          (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) ≅
      equivariantMapPushforward φ ⋙ (Action.jointlySurjectiveTopology H).yoneda := by
  let eLeft :
      ((Action.jointlySurjectiveTopology G).yoneda ⋙
          (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
            (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G)) ⋙
        sheafToPresheaf (Action.jointlySurjectiveTopology H) (Type u) ≅
      CategoryTheory.yoneda ⋙
        (Functor.whiskeringLeft (Action (Type u) H)ᵒᵖ (Action (Type u) G)ᵒᵖ (Type u)).obj
          (Action.res (Type u) φ).op :=
    (Functor.isoWhiskerLeft (Action.jointlySurjectiveTopology G).yoneda
      ((Action.res (Type u) φ).sheafPushforwardContinuousCompSheafToPresheafIso (Type u)
        (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G))) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((Action.jointlySurjectiveTopology G).yonedaCompSheafToPresheaf) _
  let eRight :
      (equivariantMapPushforward φ ⋙ (Action.jointlySurjectiveTopology H).yoneda) ⋙
        sheafToPresheaf (Action.jointlySurjectiveTopology H) (Type u) ≅
      CategoryTheory.yoneda ⋙
        (Functor.whiskeringLeft (Action (Type u) H)ᵒᵖ (Action (Type u) G)ᵒᵖ (Type u)).obj
          (Action.res (Type u) φ).op :=
    Functor.associator _ _ _ ≪≫
      (Functor.isoWhiskerLeft (equivariantMapPushforward φ)
      ((Action.jointlySurjectiveTopology H).yonedaCompSheafToPresheaf)) ≪≫
      Adjunction.compYonedaIso (equivariantMapPushforwardAdjunction φ)
  exact
    ((fullyFaithfulSheafToPresheaf (Action.jointlySurjectiveTopology H) (Type u)).whiskeringRight
      (Action (Type u) G)).preimageIso
      (eLeft ≪≫ eRight.symm)

private instance actionRes_sheafPushforwardContinuous_isRightAdjoint
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    ((Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
      (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G)).IsRightAdjoint := by
  let eG :
      Action (Type u) G ≌ Sheaf (Action.jointlySurjectiveTopology G) (Type u) :=
    ((Action.jointlySurjectiveTopology G).yoneda).asEquivalence
  letI : (equivariantMapPushforward φ ⋙ (Action.jointlySurjectiveTopology H).yoneda).IsRightAdjoint :=
    inferInstance
  letI :
      ((Action.jointlySurjectiveTopology G).yoneda ⋙
        (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
          (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G)).IsRightAdjoint :=
    Functor.isRightAdjoint_of_iso (yonedaCompSheafPushforwardContinuousIso φ).symm
  exact
    (((Adjunction.ofIsRightAdjoint
        ((Action.jointlySurjectiveTopology G).yoneda ⋙
          (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
            (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G))).comp
        eG.toAdjunction).ofNatIsoRight
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eG.counitIso
          ((Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
            (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G)) ≪≫
        Functor.leftUnitor _)).isRightAdjoint

-- Internal action-level counit computation used below to identify the canonical sheaf counit with
-- evaluation at `1` through Proposition 7.9.1 and the left-regular-sections comparison.
private theorem equivariantMapPushforward_counit_eq_eval_one
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H) :
    letI : MulAction G H := MulAction.compHom H φ
    ((equivariantMapPushforwardAdjunction φ).counit.app (Action.ofMulAction G S)).hom =
      fun a : H →[G] S ↦ a 1 := sorry

-- Proof sketch: choose one value in `S` on each left coset of `φ(G)` in `H`, prescribing the
-- value `s` on the coset of `1`; injectivity of `φ` makes the equivariance condition consistent.
private theorem equivariantMapPushforward_counit_surjective_of_injective
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (hφ : Function.Injective φ)
    (S : Action (Type u) G) :
    Function.Surjective ((equivariantMapPushforwardAdjunction φ).counit.app S).hom := sorry

/- The left-regular-sections view of the continuous pushforward along `Action.res (Type u) φ`.
This is the canonical sheaf-level object whose action-level comparison with `H →[G] S` is used
below. -/
private abbrev continuousPushforwardLeftRegularSections
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (S : Action (Type u) G) :
    Action (Type u) H :=
  (sheafSectionsOnLeftRegularFunctor H).obj
    (((Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
      (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G)).obj
      ((Action.jointlySurjectiveTopology G).yoneda.obj S))

/-- The `H`-action obtained by evaluating the canonical continuous pushforward along
`Action.res (Type u) φ` on the left regular `H`-set. -/
private noncomputable abbrev actionRes_pushforwardLeftRegularAction
    {G H : Type u} [Group G] [Group H] (S : Type u) [MulAction G S] (φ : G →* H) :
    Action (Type u) H :=
  continuousPushforwardLeftRegularSections φ (Action.ofMulAction G S)

private noncomputable def actionRes_pushforwardLeftRegularEquiv
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (S : Action (Type u) G) :
    (continuousPushforwardLeftRegularSections φ S).V ≃
      (((Action.res (Type u) φ).obj (Action.leftRegular H)) ⟶ S) := by
  let hFF : ((Action.jointlySurjectiveTopology G).yoneda).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful ((Action.jointlySurjectiveTopology G).yoneda)
  change (((Action.jointlySurjectiveTopology G).yoneda.obj S).obj.obj
      (Opposite.op ((Action.res (Type u) φ).obj (Action.leftRegular H)))) ≃
    (((Action.res (Type u) φ).obj (Action.leftRegular H)) ⟶ S)
  exact
    ((Action.jointlySurjectiveTopology G).yonedaEquiv :
      ((Action.jointlySurjectiveTopology G).yoneda.obj ((Action.res (Type u) φ).obj (Action.leftRegular H)) ⟶
        (Action.jointlySurjectiveTopology G).yoneda.obj S) ≃
        (((Action.jointlySurjectiveTopology G).yoneda.obj S).obj.obj
          (Opposite.op ((Action.res (Type u) φ).obj (Action.leftRegular H))))).symm.trans
      hFF.homEquiv.symm

private def equivariantMapsToActionHom
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H) :
    restrictedEquivariantMaps φ S →
      ((Action.res (Type u) φ).obj (Action.leftRegular H) ⟶ Action.ofMulAction G S)
  | a => by
      letI : MulAction G H := MulAction.compHom H φ
      exact
        { hom := a.toFun
          comm := fun g ↦ by
            ext h
            change a (φ g * (show H from h)) = g • a (show H from h)
            exact a.map_smul g (show H from h) }

private noncomputable def continuousPushforwardLeftRegularEquivariantMapsEquivAux
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H) :
    (continuousPushforwardLeftRegularSections φ (Action.ofMulAction G S)).V ≃
      restrictedEquivariantMaps φ S := by
  let e := actionRes_pushforwardLeftRegularEquiv φ (Action.ofMulAction G S)
  letI : MulAction G H := MulAction.compHom H φ
  refine Equiv.ofBijective
    (fun a ↦
      { toFun := (e a).hom
        map_smul' := fun g h ↦ by
          simpa using congrArg (fun k ↦ k h) ((e a).comm g) }) ?_
  constructor
  · intro a b hab
    apply e.injective
    ext h
    exact congrArg (fun k : restrictedEquivariantMaps φ S ↦ k h) hab
  · intro a
    refine ⟨e.symm (equivariantMapsToActionHom φ a), ?_⟩
    ext h
    exact congrArg
      (fun k :
        ((Action.res (Type u) φ).obj (Action.leftRegular H) ⟶ Action.ofMulAction G S) ↦
          k.hom h)
      (e.apply_symm_apply (equivariantMapsToActionHom φ a))

private theorem continuousPushforwardLeftRegularEquivariantMaps_comm
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H) :
    ∀ h : H,
      (continuousPushforwardLeftRegularSections φ (Action.ofMulAction G S)).ρ h ≫
      (continuousPushforwardLeftRegularEquivariantMapsEquivAux φ).toIso.hom =
      (continuousPushforwardLeftRegularEquivariantMapsEquivAux φ).toIso.hom ≫
        (equivariantMapAction φ S).ρ h := by
  letI : MulAction G H := MulAction.compHom H φ
  letI : MulAction H (restrictedEquivariantMaps φ S) := equivariantMapRightTranslation φ S
  sorry

/-- The left-regular-sections comparison identifying the canonical continuous pushforward along
`Action.res (Type u) φ` with the explicit right-translation action on `H →[G] S`. -/
private noncomputable def actionRes_pushforwardLeftRegularEquivariantMapsIso
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H) :
    letI : MulAction G H := MulAction.compHom H φ
    letI : MulAction H (H →[G] S) := equivariantMapRightTranslation φ S
    actionRes_pushforwardLeftRegularAction S φ ≅ Action.ofMulAction H (H →[G] S) := by
  letI : MulAction G H := MulAction.compHom H φ
  letI : MulAction H (H →[G] S) := equivariantMapRightTranslation φ S
  exact Action.mkIso
    (continuousPushforwardLeftRegularEquivariantMapsEquivAux φ).toIso
    (continuousPushforwardLeftRegularEquivariantMaps_comm φ)

private noncomputable def actionRes_sheafAdjunctionViaYoneda
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    (((Action.jointlySurjectiveTopology H).yoneda).asEquivalence.inverse ⋙
        Action.res (Type u) φ ⋙
          (Action.jointlySurjectiveTopology G).yoneda) ⊣
      (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
        (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) := by
  let eG : Action (Type u) G ≌ Sheaf (Action.jointlySurjectiveTopology G) (Type u) :=
    ((Action.jointlySurjectiveTopology G).yoneda).asEquivalence
  let eH : Action (Type u) H ≌ Sheaf (Action.jointlySurjectiveTopology H) (Type u) :=
    ((Action.jointlySurjectiveTopology H).yoneda).asEquivalence
  let adjH : eH.inverse ⊣ eH.functor := eH.symm.toAdjunction
  let adjMaps : Action.res (Type u) φ ⊣ equivariantMapPushforward φ :=
    equivariantMapPushforwardAdjunction φ
  let adjG : eG.functor ⊣ eG.inverse := eG.toAdjunction
  let adj :
      (eH.inverse ⋙ Action.res (Type u) φ ⋙ eG.functor) ⊣
        (eG.inverse ⋙ equivariantMapPushforward φ ⋙ eH.functor) :=
    (adjH.comp adjMaps).comp adjG
  let i :
      (eG.inverse ⋙ equivariantMapPushforward φ ⋙ eH.functor) ≅
        (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
          (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) := by
    calc
      eG.inverse ⋙ equivariantMapPushforward φ ⋙ eH.functor
          ≅ eG.inverse ⋙ (equivariantMapPushforward φ ⋙ eH.functor) :=
        (Functor.associator _ _ _).symm
      _ ≅ eG.inverse ⋙
            ((Action.jointlySurjectiveTopology G).yoneda ⋙
              (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
                (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G)) :=
        Functor.isoWhiskerLeft eG.inverse (yonedaCompSheafPushforwardContinuousIso φ).symm
      _ ≅
            (eG.inverse ⋙ (Action.jointlySurjectiveTopology G).yoneda) ⋙
              (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
                (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) :=
        (Functor.associator _ _ _).symm
      _ ≅
            𝟭 (Sheaf (Action.jointlySurjectiveTopology G) (Type u)) ⋙
              (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
                (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) :=
        Functor.isoWhiskerRight eG.counitIso _
      _ ≅
            (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
              (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) :=
        Functor.leftUnitor _
  exact adj.ofNatIsoRight i

private noncomputable def actionRes_sheafPullbackIso
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    (((Action.jointlySurjectiveTopology H).yoneda).asEquivalence.inverse ⋙
        Action.res (Type u) φ ⋙
          (Action.jointlySurjectiveTopology G).yoneda) ≅
      (Action.res (Type u) φ).sheafPullback (Type u)
        (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) :=
  Adjunction.leftAdjointUniq
    (actionRes_sheafAdjunctionViaYoneda φ)
    ((Action.res (Type u) φ).sheafAdjunctionContinuous (Type u)
      (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G))

/-- The action-level map on `H →[G] S` induced by the counit of the canonical continuous sheaf
adjunction along `Action.res (Type u) φ`, viewed through Proposition 7.9.1 and the
left-regular-sections comparison. -/
private noncomputable def actionRes_pushforwardCounitMap
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H) :
    letI : MulAction G H := MulAction.compHom H φ
    (H →[G] S) → S := by
  letI : MulAction G H := MulAction.compHom H φ
  letI : MulAction H (H →[G] S) := equivariantMapRightTranslation φ S
  let JG := Action.jointlySurjectiveTopology G
  let JH := Action.jointlySurjectiveTopology H
  let eG : Action (Type u) G ≌ Sheaf JG (Type u) := (JG.yoneda).asEquivalence
  let eH : Action (Type u) H ≌ Sheaf JH (Type u) := (JH.yoneda).asEquivalence
  let Y : Sheaf JG (Type u) := JG.yoneda.obj (Action.ofMulAction G S)
  let R :
      Sheaf JG (Type u) ⥤ Sheaf JH (Type u) :=
    (Action.res (Type u) φ).sheafPushforwardContinuous (Type u) JH JG
  let eVia :
      (((Action.jointlySurjectiveTopology H).yoneda).asEquivalence.inverse ⋙
          Action.res (Type u) φ ⋙ (Action.jointlySurjectiveTopology G).yoneda).obj (R.obj Y) ≅
        eG.functor.obj ((Action.res (Type u) φ).obj (eH.inverse.obj (R.obj Y))) :=
    Iso.refl _
  let ePull :
      eG.inverse.obj
          (((Action.res (Type u) φ).sheafPullback (Type u) JH JG).obj (R.obj Y)) ≅
        (Action.res (Type u) φ).obj (eH.inverse.obj (R.obj Y)) :=
    (eG.inverse.mapIso
      (((actionRes_sheafPullbackIso φ).symm.app (R.obj Y)) ≪≫ eVia)) ≪≫
      (eG.unitIso.app ((Action.res (Type u) φ).obj (eH.inverse.obj (R.obj Y)))).symm
  let eRight :
      eH.inverse.obj (R.obj Y) ≅ actionRes_pushforwardLeftRegularAction S φ := by
    exact eqToIso (by
      simpa [actionRes_pushforwardLeftRegularAction, continuousPushforwardLeftRegularSections, R, Y]
        using
          congrArg
            (fun F : Sheaf JH (Type u) ⥤ Action (Type u) H ↦ F.obj (R.obj Y))
            (jointlySurjectiveTopology_yoneda_inv_eq_sheafSectionsOnLeftRegularFunctor H))
  let eMaps :
      (Action.res (Type u) φ).obj (eH.inverse.obj (R.obj Y)) ≅
        (Action.res (Type u) φ).obj (Action.ofMulAction H (H →[G] S)) := by
    exact ((Action.res (Type u) φ).mapIso eRight) ≪≫ by
      simpa using
        (Action.res (Type u) φ).mapIso (actionRes_pushforwardLeftRegularEquivariantMapsIso φ)
  let eSource :
      eG.inverse.obj
          (((Action.res (Type u) φ).sheafPullback (Type u) JH JG).obj (R.obj Y)) ≅
        (Action.res (Type u) φ).obj (Action.ofMulAction H (H →[G] S)) := by
    exact ePull ≪≫ eMaps
  let η :
      eG.inverse.obj
          (((Action.res (Type u) φ).sheafPullback (Type u) JH JG).obj (R.obj Y)) ⟶
        eG.inverse.obj Y :=
    eG.inverse.map
      (((Action.res (Type u) φ).sheafAdjunctionContinuous (Type u) JH JG).counit.app Y)
  let eCod :
      eG.inverse.obj Y ≅ Action.ofMulAction G S :=
    ((eG.unitIso.app (Action.ofMulAction G S)).symm)
  exact (eSource.inv ≫ η ≫ eCod.hom).hom

/-- Example 7.41.5 (1): source-facing bridge. Under Proposition 7.9.1 and the left-regular-sections
comparison for the canonical continuous pushforward along `Action.res (Type u) φ`, the counit at
the sheaf corresponding to the `G`-set `S` is the explicit evaluation map `(H →[G] S) → S`,
`a ↦ a(1)`. -/
private theorem equivariant_map_pushforward_counit_eq_eval_one
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H) :
    letI : MulAction G H := MulAction.compHom H φ
    actionRes_pushforwardCounitMap φ = fun a : H →[G] S ↦ a 1 := sorry

/-- Example 7.41.5 (2): canonical sheaf form. If `φ : G → H` is injective, then for the sheaf
attached to a `G`-set `S`, the counit `f⁻¹ f_* ℱ ⟶ ℱ` of the chapter's chosen adjunction
`(Action.res (Type u) φ).sheafAdjunctionContinuous ...` is locally surjective. The continuity
instance for `Action.res (Type u) φ` together with the canonical `Type`-valued sheaf pullback
construction supplies the needed right-adjoint structure internally. -/
theorem continuous_pushforward_counit_isLocallySurjective_of_injective
    {G H S : Type u} [Group G] [Group H] [MulAction G S]
    (φ : G →* H)
    (hφ : Function.Injective φ) :
    Sheaf.IsLocallySurjective
      (((Action.res (Type u) φ).sheafAdjunctionContinuous (Type u)
          (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G)).counit.app
        ((Action.jointlySurjectiveTopology G).yoneda.obj (Action.ofMulAction G S))) := by
  sorry

/-- Example 7.41.5 (3): explicit companion. If `φ : G → H` is injective, then the concrete map
`(H →[G] S) → S`, `a ↦ a(1)`, is surjective, where `G` acts on `H` via `φ`. This is the
left-regular-sections view of `continuous_pushforward_counit_isLocallySurjective_of_injective`. -/
theorem equivariant_map_eval_one_surjective_of_injective
    {G H S : Type u} [Group G] [Group H] [MulAction G S]
    (φ : G →* H) (hφ : Function.Injective φ) :
    letI : MulAction G H := MulAction.compHom H φ
    Function.Surjective (fun a : H →[G] S ↦ a 1) := by
  letI : MulAction G H := MulAction.compHom H φ
  simpa [equivariantMapPushforward_counit_eq_eval_one] using
    equivariantMapPushforward_counit_surjective_of_injective φ hφ (Action.ofMulAction G S)

-- Proof sketch: with `G = {1}`, every function `H → Bool` is automatically `G`-equivariant,
-- so two distinct functions agreeing at `1` give distinct preimages of the same value.
attribute [-instance] PUnit.instVAdd_mathlib

/-- In the two-point example from the text, evaluation at `1` need not be injective. -/
theorem equivariant_map_eval_one_not_injective_example :
    letI : MulAction PUnit (Multiplicative (ZMod 2)) :=
      MulAction.compHom (Multiplicative (ZMod 2)) (1 : PUnit →* Multiplicative (ZMod 2))
    ¬ Function.Injective (fun a : Multiplicative (ZMod 2) →[PUnit] Bool ↦ a 1) := sorry

-- Proof sketch: the two-point example above shows that the counit of the canonical continuous
-- pushforward along `Action.res (Type 0) (1 : PUnit →* Multiplicative (ZMod 2))` is not
-- injective on left-regular sections, and the Stacks argument then concludes that this `f_*`
-- cannot commute with coequalizers.
/-- Example 7.41.5 (4): for `G = {1}` and `H = {1, σ}`, the canonical continuous pushforward on
sheaves along `Action.res (Type 0) (1 : PUnit →* Multiplicative (ZMod 2))` does not preserve
coequalizers. Via Proposition 7.9.1 and the left-regular-sections bridge above, this is the
concrete `Map_{PUnit}(H, -)` example from the text. -/
theorem continuous_pushforward_not_preserves_coequalizers_example :
    ¬ PreservesColimitsOfShape WalkingParallelPair
      ((Action.res (Type 0) (1 : PUnit →* Multiplicative (ZMod 2))).sheafPushforwardContinuous
        (Type 0) (Action.jointlySurjectiveTopology (Multiplicative (ZMod 2))) (Action.jointlySurjectiveTopology PUnit)) := sorry

-- Proof sketch: the same `G = {1}`, `H = {1, σ}` example from the text gives a pushout diagram
-- whose image under the pushforward functor fails to remain a pushout.
/-- Example 7.41.5 (5): for `G = {1}` and `H = {1, σ}`, the canonical continuous pushforward on
sheaves along `Action.res (Type 0) (1 : PUnit →* Multiplicative (ZMod 2))` does not preserve
pushouts. Via Proposition 7.9.1 and the left-regular-sections bridge above, this is the concrete
`Map_{PUnit}(H, -)` example from the text. -/
theorem continuous_pushforward_not_preserves_pushouts_example :
    ¬ PreservesColimitsOfShape WalkingSpan
      ((Action.res (Type 0) (1 : PUnit →* Multiplicative (ZMod 2))).sheafPushforwardContinuous
        (Type 0) (Action.jointlySurjectiveTopology (Multiplicative (ZMod 2))) (Action.jointlySurjectiveTopology PUnit)) := sorry

attribute [instance] PUnit.instVAdd_mathlib

end

end CategoryTheory
