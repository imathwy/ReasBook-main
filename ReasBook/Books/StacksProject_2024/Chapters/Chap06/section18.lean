import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_6_18_1 (from Chap06) -/
open CategoryTheory Opposite TopCat TopCat.Presheaf TopCat.Presheaf.Sheafify TopologicalSpace

noncomputable section

universe v

section

variable {X : TopCat.{v}} (F : Presheaf (Type v) X)

/-
Domain-style sampling for Lemma 6.18.1:
- primary domain: sheafification of `Type`-valued presheaves and stalkwise local-germ criteria;
- sampled owner API:
  `TopCat.Presheaf.sheafify`,
  `TopCat.Presheaf.sheafifyStalkIso`,
  `TopCat.Presheaf.toSheafify`,
  `TopCat.Presheaf.Sheafify.isLocallyGerm`;
- best owner abstraction: the bundled sheafification `F.sheafify`, with stalk comparison given by
  `F.sheafifyStalkIso`;
- primitive data: the presheaf `F` and the open set `U`;
- derived API: the concrete subtype realization of `F.sheafify` inside the presheaf of functions
  into stalks, and the induced map on stalks from `F.toSheafify`.

Source/core/bridge triage:
- `source-facing`: the pullback description of sections of `F^#(U)`;
- `core/canonical`: `F.sheafify` together with `F.sheafifyStalkIso`;
- `bridge/view`: the subtype inclusion
  `(subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U)`.
-/

-- Proof sketch: use the canonical owner `F.sheafify` for sections of `F^#(U)`, map a section to
-- its family of germs in the stalks of `F^#`, pass to the original stalks via the primitive owner
-- map `F.stalkToFiber` (equivalently the hom of `F.sheafifyStalkIso`), and compare with the local-
-- germ realization inside the product presheaf of stalks.
/-- Helper for Lemma 6.18.1: the stalk-family map `σ` is exactly the underlying dependent function
of a sheafification section. -/
lemma sheafify_section_stalk_family_eq (U : Opens X) (s : F.sheafify.presheaf.obj (op U)) :
    (fun x : U ↦ F.stalkToFiber x.1 (F.sheafify.presheaf.germ U x.1 x.2 s)) =
      ((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U) s) := by
  -- Evaluate the germ of the sheafification section at each point.
  ext x
  exact TopCat.stalkToFiber_germ (isLocallyGerm F) U x.1 x.2 s

/-- Helper for Lemma 6.18.1: each component map `F_x → Π(F)_x` induced by `F.toSheafify` is
injective. -/
lemma to_stalk_sections_stalk_injective (x : X) :
    Function.Injective (((stalkFunctor (Type v) x).map
      (F.toSheafify ≫
        subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate))) := by
  have h_unit : Function.Injective ((stalkFunctor (Type v) x).map F.toSheafify) := by
    intro a b hab
    obtain ⟨U, hxU, s, rfl⟩ := F.germ_exist x a
    obtain ⟨V, hxV, t, rfl⟩ := F.germ_exist x b
    have hU :
        ((stalkFunctor (Type v) x).map F.toSheafify) (F.germ U x hxU s) =
          F.sheafify.presheaf.germ U x hxU (F.toSheafify.app (op U) s) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU F.toSheafify s
    have hV :
        ((stalkFunctor (Type v) x).map F.toSheafify) (F.germ V x hxV t) =
          F.sheafify.presheaf.germ V x hxV (F.toSheafify.app (op V) t) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV F.toSheafify t
    have hab' :
        F.sheafify.presheaf.germ U x hxU (F.toSheafify.app (op U) s) =
          F.sheafify.presheaf.germ V x hxV (F.toSheafify.app (op V) t) := by
      exact hU.symm.trans (hab.trans hV)
    have hUfiber :
        F.stalkToFiber x (F.sheafify.presheaf.germ U x hxU (F.toSheafify.app (op U) s)) =
          F.germ U x hxU s := by
      simpa [TopCat.Presheaf.toSheafify] using
        (TopCat.stalkToFiber_germ (isLocallyGerm F) U x hxU (F.toSheafify.app (op U) s))
    have hVfiber :
        F.stalkToFiber x (F.sheafify.presheaf.germ V x hxV (F.toSheafify.app (op V) t)) =
          F.germ V x hxV t := by
      simpa [TopCat.Presheaf.toSheafify] using
        (TopCat.stalkToFiber_germ (isLocallyGerm F) V x hxV (F.toSheafify.app (op V) t))
    -- Push equality in the sheafification stalk through `stalkToFiber` to recover equality in `F_x`.
    calc
      F.germ U x hxU s =
        F.stalkToFiber x (F.sheafify.presheaf.germ U x hxU (F.toSheafify.app (op U) s)) := by
          symm
          exact hUfiber
      _ =
        F.stalkToFiber x (F.sheafify.presheaf.germ V x hxV (F.toSheafify.app (op V) t)) := by
          exact congrArg (F.stalkToFiber x) hab'
      _ = F.germ V x hxV t := hVfiber
  have h_subtype :
      Function.Injective ((stalkFunctor (Type v) x).map
        (subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate)) := by
    -- The subtype inclusion is injective on each open set, so its stalk maps are injective.
    simpa using
      (stalkFunctor_map_injective_of_app_injective
        (C := Type v)
        (f := subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate)
        (x := x)
        (fun U s t hst ↦ Subtype.ext hst))
  intro a b hab
  -- Apply injectivity first on the stalk map of the subtype inclusion, then on the unit map.
  have hab' :
      ((stalkFunctor (Type v) x).map F.toSheafify) a =
        ((stalkFunctor (Type v) x).map F.toSheafify) b := by
    exact h_subtype <| by simpa using hab
  exact h_unit hab'

/-- Helper for Lemma 6.18.1: a stalk family is locally a germ exactly when each stalk value comes
from the image of the component map `F_x → Π(F)_x`. -/
lemma isLocallyGerm_pred_iff_stalkwise_lift
    (U : Opens X) (s : (X.presheafToTypes (fun x ↦ F.stalk x)).obj (op U)) :
    ((isLocallyGerm F).toPrelocalPredicate).pred s ↔
      ∀ x : U, ∃ t : F.stalk x.1,
        (X.presheafToTypes (fun y ↦ F.stalk y)).germ U x.1 x.2 s =
          ((stalkFunctor (Type v) x.1).map
            (F.toSheafify ≫
              subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate)) t := by
  constructor
  · intro hs x
    rcases hs x with ⟨V, hxV, iV, g, hg⟩
    refine ⟨F.germ V x.1 hxV g, ?_⟩
    -- Rewrite the stalk image through the actual local germ witness `g`.
    calc
      (X.presheafToTypes (fun y ↦ F.stalk y)).germ U x.1 x.2 s =
          (X.presheafToTypes (fun y ↦ F.stalk y)).germ V x.1 hxV
            (((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op V))
              (F.toSheafify.app (op V) g)) := by
                apply (X.presheafToTypes (fun y ↦ F.stalk y)).germ_ext V hxV iV (𝟙 _)
                exact funext fun y ↦ hg y
      _ =
          ((stalkFunctor (Type v) x.1).map
            (F.toSheafify ≫
              subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate))
            (F.germ V x.1 hxV g) := by
              symm
              exact TopCat.Presheaf.stalkFunctor_map_germ_apply V x.1 hxV
                (F.toSheafify ≫
                  subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate) g
  · intro hs
    intro x
    rcases hs x with ⟨t, ht⟩
    rcases F.germ_exist x.1 t with ⟨V, hxV, g, rfl⟩
    have h_germs :
        (X.presheafToTypes (fun y ↦ F.stalk y)).germ U x.1 x.2 s =
          (X.presheafToTypes (fun y ↦ F.stalk y)).germ V x.1 hxV
            (((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op V))
              (F.toSheafify.app (op V) g)) := by
      -- Rewrite the stalkwise image condition using the explicit representative of `t`.
      exact ht.trans <|
        TopCat.Presheaf.stalkFunctor_map_germ_apply V x.1 hxV
          (F.toSheafify ≫
            subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate) g
    obtain ⟨W, hxW, iWU, iWV, hW⟩ :=
      (X.presheafToTypes (fun y ↦ F.stalk y)).germ_eq x.1 x.2 hxV _ _ h_germs
    refine ⟨W, hxW, iWU, ?_⟩
    refine ⟨F.map iWV.op g, ?_⟩
    -- Shrink to a neighborhood where the family is literally given by the germs of `g`.
    intro y
    have hy := congrFun hW y
    calc
      s (iWU y) =
        (((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op V))
          (F.toSheafify.app (op V) g)) (iWV y) := by
            simpa [TopCat.presheafToTypes_map] using hy
      _ = F.germ V (iWV y).1 (iWV y).2 g := rfl
      _ = F.germ W y.1 y.2 (F.map iWV.op g) := by
        symm
        exact F.germ_res_apply iWV y.1 y.2 g

/-- Helper for Lemma 6.18.1: the four canonical maps form a commutative square. -/
lemma sheafify_square_commutes (U : Opens X) :
    let Fsharp := F.sheafify.presheaf
    let stalkSections := X.presheafToTypes (fun x ↦ F.stalk x)
    let sectionStalks : Type v := ∀ x : U, F.stalk x.1
    let stalkSectionStalks : Type v := ∀ x : U, stalkSections.stalk x.1
    let ι :
        Fsharp.obj (op U) ⟶ stalkSections.obj (op U) :=
      (subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U)
    let σ : Fsharp.obj (op U) ⟶ sectionStalks :=
      fun s x ↦ F.stalkToFiber x.1 (Fsharp.germ U x.1 x.2 s)
    let γ : stalkSections.obj (op U) ⟶ stalkSectionStalks :=
      fun s x ↦ stalkSections.germ U x.1 x.2 s
    let τ : sectionStalks ⟶ stalkSectionStalks :=
      fun s x ↦
        ((stalkFunctor (Type v) x.1).map
          (F.toSheafify ≫
            subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate)) (s x)
    ι ≫ γ = σ ≫ τ := by
  dsimp
  ext s x
  rcases s.2 x with ⟨V, hxV, iV, g, hg⟩
  have hsx :
      F.stalkToFiber x.1 (F.sheafify.presheaf.germ U x.1 x.2 s) = F.germ V x.1 hxV g := by
    calc
      F.stalkToFiber x.1 (F.sheafify.presheaf.germ U x.1 x.2 s) =
          (((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U)) s) x := by
            exact congrFun (sheafify_section_stalk_family_eq F U s) x
      _ = F.germ V x.1 hxV g := hg ⟨x.1, hxV⟩
  -- Compare both sides through the same local germ witness `g`.
  change
    (X.presheafToTypes (fun y ↦ F.stalk y)).germ U x.1 x.2
        (((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U)) s) =
      ((stalkFunctor (Type v) x.1).map
        (F.toSheafify ≫
          subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate))
        (F.stalkToFiber x.1 (F.sheafify.presheaf.germ U x.1 x.2 s))
  calc
    (X.presheafToTypes (fun y ↦ F.stalk y)).germ U x.1 x.2
        (((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U)) s) =
      (X.presheafToTypes (fun y ↦ F.stalk y)).germ V x.1 hxV
        (((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op V))
          (F.toSheafify.app (op V) g)) := by
            apply (X.presheafToTypes (fun y ↦ F.stalk y)).germ_ext V hxV iV (𝟙 _)
            exact funext fun y ↦ hg y
    _ =
      ((stalkFunctor (Type v) x.1).map
        (F.toSheafify ≫
          subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate))
        (F.germ V x.1 hxV g) := by
          symm
          exact TopCat.Presheaf.stalkFunctor_map_germ_apply V x.1 hxV
            (F.toSheafify ≫
              subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate) g
    _ =
      ((stalkFunctor (Type v) x.1).map
        (F.toSheafify ≫
          subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate))
        (F.stalkToFiber x.1 (F.sheafify.presheaf.germ U x.1 x.2 s)) := by
          rw [hsx]

/-- Lemma 6.18.1: for an open set `U`, sections of the sheafification `F^#(U)` form the pullback of
the canonical inclusion `F^#(U) ↪ Π(F)(U)`, the family of germ maps
`F^#(U) → ∏_{x ∈ U} F_x` obtained from `F.sheafifyStalkIso`, the inclusion
`Π(F)(U) → ∏_{x ∈ U} Π(F)_x`, and the product of the canonical stalk maps
`∏_{x ∈ U} F_x → ∏_{x ∈ U} Π(F)_x`. -/
lemma sheafify_section_pullback_diagram (U : Opens X) :
    let Fsharp := F.sheafify.presheaf
    let stalkSections := X.presheafToTypes (fun x ↦ F.stalk x)
    let sectionStalks : Type v := ∀ x : U, F.stalk x.1
    let stalkSectionStalks : Type v := ∀ x : U, stalkSections.stalk x.1
    let ι :
        Fsharp.obj (op U) ⟶ stalkSections.obj (op U) :=
      (subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U)
    let σ : Fsharp.obj (op U) ⟶ sectionStalks :=
      fun s x ↦ F.stalkToFiber x.1 (Fsharp.germ U x.1 x.2 s)
    let γ : stalkSections.obj (op U) ⟶ stalkSectionStalks :=
      fun s x ↦ stalkSections.germ U x.1 x.2 s
    let τ : sectionStalks ⟶ stalkSectionStalks :=
      fun s x ↦
        ((stalkFunctor (Type v) x.1).map
          (F.toSheafify ≫
            subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate)) (s x)
    IsPullback ι σ γ τ := by
  dsimp
  rw [CategoryTheory.Limits.Types.isPullback_iff]
  refine ⟨sheafify_square_commutes F U, ?_, ?_⟩
  · intro a b hab
    -- The top arrow is a subtype inclusion, so equality upstairs follows from equality downstairs.
    apply Subtype.ext
    exact hab.1
  · intro s t hst
    have hs :
        ((isLocallyGerm F).toPrelocalPredicate).pred s := by
      -- The source proof identifies local-germ sections by stalkwise liftability.
      rw [isLocallyGerm_pred_iff_stalkwise_lift F U s]
      intro x
      exact ⟨t x, congrFun hst x⟩
    refine ⟨⟨s, hs⟩, rfl, ?_⟩
    ext x
    apply to_stalk_sections_stalk_injective F x.1
    -- Compare both candidates after mapping to the lower-right corner.
    have hcomm :=
      congrFun (congrFun (sheafify_square_commutes F U) ⟨s, hs⟩) x
    have hx := congrFun hst x
    simpa using hcomm.symm.trans hx

end

/-! ### Lemma_6_18_2 (from Chap06) -/
open CategoryTheory TopCat TopCat.Presheaf
open TopologicalSpace
open scoped TopCat

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable (ℱ : PAb(X))
variable {𝒢 : Ab(X)}

local notation "J" => Opens.grothendieckTopology X

/- Domain-style sampling for Lemma 6.18.2:
- primary domain: sheafification of abelian presheaves and abelian sheaves on a topological space,
  written `PAb(X)` and `Ab(X)`;
- sampled owner API:
  `TopCat.Presheaf.sheafify`,
  `TopCat.Presheaf.toSheafify`,
  `CategoryTheory.sheafificationAdjunction`,
  `CategoryTheory.sheafComposeNatIso`,
  `CategoryTheory.sheafifyComposeIso`,
  `CompatibleAddCommGroupStructure.toPAb`,
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp`;
- best owner abstraction: the fixed set-valued sheafification should stay on the canonical owner
  `((ℱ ⋙ forget AddCommGrpCat.{u}).sheafify : X.Sheaf (Type u))`, equivalently
  `(presheafToSheaf J (Type u)).obj (ℱ ⋙ forget AddCommGrpCat.{u})`; the canonical abelian
  sheafification `(presheafToSheaf J AddCommGrpCat.{u}).obj ℱ` is then the bridge/view comparison
  object, related by `sheafifyComposeIso`;
- primitive data: the fixed set-valued sheafification `ℱ^#`, the canonical abelian sheafification,
  and the units `toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})` and `toSheafify J ℱ`;
- derived API: the transported compatible additive structure on `ℱ^#`, the bundled abelian sheaf
  `setSheafificationAb ℱ : Ab(X)`, the bridge isomorphism to the canonical abelian sheafification,
  and the resulting universal property.

Source/core/bridge triage:
- `source-facing`: the actual fixed set-valued sheafification `ℱ^#`, together with its transported
  compatible abelian-group structure;
- `core/canonical`: the sheafification adjunctions in `Type u` and in `AddCommGrpCat.{u}`;
- `bridge/view`: `sheafifyComposeIso`, which compares `ℱ^#` with the underlying set-valued
  sheafification of the canonical abelian sheafification. -/

/- Lemma 6.18.2: the source-facing `ℱ^#` is the actual set-valued sheafification of the
underlying presheaf of `ℱ`, while the canonical `AddCommGrpCat` sheafification provides the
additive structure and universal property through the standard comparison isomorphisms. -/
recall CategoryTheory.sheafificationAdjunction
recall CategoryTheory.sheafComposeNatIso
recall CategoryTheory.sheafifyComposeIso
recall CategoryTheory.sheafComposeIso_hom_fac

/- The owner equivalence for the canonical adjunction `PAb(X) ⇄ Ab(X)`. -/
#check (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv ℱ 𝒢) :
  ((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ ⟶ 𝒢) ≃ (ℱ ⟶ 𝒢.obj))

/- The sheaf-level comparison with the canonical abelian sheafification. -/
#check ((sheafComposeNatIso J (forget AddCommGrpCat.{u})
  (sheafificationAdjunction J AddCommGrpCat.{u})
  (sheafificationAdjunction J (Type u))).app ℱ)

namespace SetSheafification

/- Textbook notation for the fixed set sheafification `ℱ^#`, attached directly to the canonical
owner expression `(presheafToSheaf J (Type u)).obj (ℱ ⋙ forget AddCommGrpCat)` rather than to any
local alias. We spell that owner through `Functor.obj` so the notation expands without projection
syntax. Since the ambient space `X` is recoverable from `ℱ : PAb(X)`, the postfix notation is
inference-stable here. -/
set_option quotPrecheck false in
scoped notation:max F "^#" =>
  Functor.obj (presheafToSheaf J (Type _)) (F ⋙ forget AddCommGrpCat)

end SetSheafification

open scoped SetSheafification

/- The source-facing owner `ℱ^#`. -/
#check (ℱ^# : X.Sheaf (Type u))

/- On underlying presheaves, the bridge/view part of Lemma 6.18.2 is the canonical comparison
`sheafifyComposeIso` specialized to abelian presheaves. -/
#check (sheafifyComposeIso J (forget AddCommGrpCat.{u}) ℱ :
  (ℱ^#).obj ≅ ((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj ⋙ forget AddCommGrpCat.{u})

private abbrev setSheafificationComponentEquiv (U : (Opens X)ᵒᵖ) :
    ((ℱ^#).obj).obj U ≃
      (((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj ⋙ forget AddCommGrpCat.{u}).obj U :=
  Iso.toEquiv ((sheafifyComposeIso J (forget AddCommGrpCat.{u}) ℱ).app U)

/-- Lemma 6.18.2, source-facing structure: the exact fixed set-valued sheafification `ℱ^#`
carries a compatible sectionwise abelian-group structure, transported from the canonical
`AddCommGrpCat` sheafification along `sheafifyComposeIso`. -/
noncomputable def setSheafificationCompatibleAddCommGroupStructure :
    CompatibleAddCommGroupStructure
      (ℱ^#).obj :=
  { addCommGroup := fun U ↦
      Equiv.addCommGroup (setSheafificationComponentEquiv ℱ U)
    map_add := by
      intro U V i s t
      let eU := setSheafificationComponentEquiv ℱ U
      let eV := setSheafificationComponentEquiv ℱ V
      let _ : AddCommGroup (((ℱ^#).obj).obj U) := Equiv.addCommGroup eU
      let _ : AddCommGroup (((ℱ^#).obj).obj V) := Equiv.addCommGroup eV
      apply eV.injective
      rw [show eV (((ℱ^#).obj).map i (s + t)) =
          ((((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj ⋙
            forget AddCommGrpCat.{u}).map i) (eU (s + t)) by
            simpa using
              congrFun ((sheafifyComposeIso J (forget AddCommGrpCat.{u}) ℱ).hom.naturality i)
                (s + t)]
      rw [Equiv.add_def eU]
      simp only [Equiv.apply_symm_apply]
      rw [Equiv.add_def eV]
      simp only [Equiv.apply_symm_apply]
      rw [show eV (((ℱ^#).obj).map i s) =
          ((((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj ⋙
            forget AddCommGrpCat.{u}).map i) (eU s) by
            simpa using
              congrFun ((sheafifyComposeIso J (forget AddCommGrpCat.{u}) ℱ).hom.naturality i) s]
      rw [show eV (((ℱ^#).obj).map i t) =
          ((((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj ⋙
            forget AddCommGrpCat.{u}).map i) (eU t) by
            simpa using
              congrFun ((sheafifyComposeIso J (forget AddCommGrpCat.{u}) ℱ).hom.naturality i) t]
      exact (((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj.map i).hom.map_add (eU s) (eU t) }

/-- Lemma 6.18.2, source-facing owner: the fixed sheafification `ℱ^#` bundled as a sheaf of
abelian groups on `X`. -/
noncomputable def setSheafificationAb : Ab(X) where
  obj := (setSheafificationCompatibleAddCommGroupStructure ℱ).toPAb
  property := by
    refine (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2 ?_
    simpa [(setSheafificationCompatibleAddCommGroupStructure ℱ).toPAb_forget] using
      (ℱ^#).property

/-- Forgetting the abelian-group structure on `setSheafificationAb ℱ` recovers the fixed
set-valued sheafification `ℱ^#`. -/
theorem setSheafificationAb_forget :
    (setSheafificationAb ℱ).obj ⋙ forget AddCommGrpCat.{u} = (ℱ^#).obj :=
  (setSheafificationCompatibleAddCommGroupStructure ℱ).toPAb_forget

private noncomputable def setSheafificationAbComponentAddEquiv (U : (Opens X)ᵒᵖ) :
    ((setSheafificationAb ℱ).obj.obj U) ≃+
      ((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj.obj U where
  toEquiv := setSheafificationComponentEquiv ℱ U
  map_add' := by
    intro s t
    let e := setSheafificationComponentEquiv ℱ U
    change e (e.symm (e s + e t)) = e s + e t
    exact e.apply_symm_apply (e s + e t)

private noncomputable def setSheafificationAbPresheafIso :
    (setSheafificationAb ℱ).obj ≅ ((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj :=
  NatIso.ofComponents
    (fun U ↦ (setSheafificationAbComponentAddEquiv ℱ U).toAddCommGrpIso)
    (by
      intro U V i
      apply AddCommGrpCat.ext
      intro s
      simpa using congrFun ((sheafifyComposeIso J (forget AddCommGrpCat.{u}) ℱ).hom.naturality i) s)

/-- The bridge/view between the source-facing abelian sheafification `setSheafificationAb ℱ` and
the canonical abelian sheafification `(presheafToSheaf J AddCommGrpCat).obj ℱ`. -/
noncomputable def setSheafificationAbIsoCanonical :
    setSheafificationAb ℱ ≅ (presheafToSheaf J AddCommGrpCat.{u}).obj ℱ where
  hom := ⟨(setSheafificationAbPresheafIso ℱ).hom⟩
  inv := ⟨(setSheafificationAbPresheafIso ℱ).inv⟩
  hom_inv_id := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (setSheafificationAbPresheafIso ℱ).hom_inv_id
  inv_hom_id := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (setSheafificationAbPresheafIso ℱ).inv_hom_id

/-- The unit `ℱ ⟶ ℱ^#` as a morphism of abelian presheaves for the exact compatible structure on
`ℱ^#`. -/
noncomputable def toSetSheafificationAb :
    ℱ ⟶ (setSheafificationAb ℱ).obj :=
  toSheafify J ℱ ≫ (setSheafificationAbIsoCanonical ℱ).inv.hom

/-- Composing the source-facing unit with the bridge to the canonical abelian sheafification
recovers the canonical adjunction unit `toSheafify J ℱ`. -/
theorem toSetSheafificationAb_comp_setSheafificationAbIsoCanonical_hom :
    toSetSheafificationAb ℱ ≫ (setSheafificationAbIsoCanonical ℱ).hom.hom = toSheafify J ℱ := by
  exact congrArg
    (fun k ↦ toSheafify J ℱ ≫ k.hom)
    (Iso.inv_hom_id (setSheafificationAbIsoCanonical ℱ))

/-- Forgetting the additive structure on `toSetSheafificationAb ℱ` recovers the actual set-valued
sheafification unit `ℱ ⟶ ℱ^#`. -/
theorem toSetSheafificationAb_forget :
    Functor.whiskerRight (toSetSheafificationAb ℱ) (forget AddCommGrpCat.{u}) ≫
      eqToHom (setSheafificationAb_forget ℱ) =
        toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u}) := by
  convert (sheafComposeIso_inv_fac J (forget AddCommGrpCat.{u}) ℱ) using 1

/-- Lemma 6.18.2, source-facing map statement: the actual set-valued sheafification unit
`ℱ ⟶ ℱ^#` is additive for the exact compatible abelian-group structure on `ℱ^#`. -/
theorem toSheafify_map_add (U : (Opens X)ᵒᵖ) (s t : ℱ.obj U) :
    by
      let _ := (setSheafificationCompatibleAddCommGroupStructure ℱ).addCommGroup U
      exact
        (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U (s + t) =
          (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U s +
            (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U t := by
  let _ := (setSheafificationCompatibleAddCommGroupStructure ℱ).addCommGroup U
  have hforget := toSetSheafificationAb_forget ℱ
  have hmap := ((toSetSheafificationAb ℱ).app U).hom.map_add s t
  have hs :
      ((toSetSheafificationAb ℱ).app U).hom s =
        (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U s := by
    simpa using congrFun (congrArg (fun k ↦ k.app U) hforget) s
  have ht :
      ((toSetSheafificationAb ℱ).app U).hom t =
        (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U t := by
    simpa using congrFun (congrArg (fun k ↦ k.app U) hforget) t
  have hst :
      ((toSetSheafificationAb ℱ).app U).hom (s + t) =
        (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U (s + t) := by
    simpa using congrFun (congrArg (fun k ↦ k.app U) hforget) (s + t)
  simpa [hs, ht, hst] using hmap

private theorem setSheafification_hom_ext {γ δ : (ℱ^#).obj ⟶ (ℱ^#).obj}
    (h :
      toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u}) ≫ γ =
        toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u}) ≫ δ) :
    γ = δ := by
  simpa using (sheafify_hom_ext J γ δ (ℱ^#).property h)

/-- Lemma 6.18.2, universal property on the canonical abelian sheafification: every additive
morphism `η : ℱ ⟶ 𝒢.obj` factors uniquely through the adjunction unit `toSheafify J ℱ`. -/
theorem existsUnique_canonicalSetSheafificationLift {ℱ : PAb(X)} {𝒢 : Ab(X)} (η : ℱ ⟶ 𝒢.obj) :
    ∃! γ : (presheafToSheaf J AddCommGrpCat.{u}).obj ℱ ⟶ 𝒢, toSheafify J ℱ ≫ γ.hom = η := by
  let e := (sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv ℱ 𝒢
  refine ⟨e.symm η, ?_, ?_⟩
  · change e (e.symm η) = η
    exact Equiv.apply_symm_apply e η
  · intro γ hγ
    apply e.injective
    have hγη : e γ = η := by
      simpa [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] using hγ
    rw [hγη]
    exact (Equiv.apply_symm_apply e η).symm

/-- Lemma 6.18.2, source-facing universal property: every additive morphism
`η : ℱ ⟶ 𝒢.obj` factors uniquely through `toSetSheafificationAb ℱ`. -/
theorem existsUnique_setSheafificationLift {ℱ : PAb(X)} {𝒢 : Ab(X)} (η : ℱ ⟶ 𝒢.obj) :
    ∃! γ : setSheafificationAb ℱ ⟶ 𝒢, toSetSheafificationAb ℱ ≫ γ.hom = η := by
  obtain ⟨δ, hδ, hδuniq⟩ := existsUnique_canonicalSetSheafificationLift η
  refine ⟨(setSheafificationAbIsoCanonical ℱ).hom ≫ δ, ?_, ?_⟩
  · change toSetSheafificationAb ℱ ≫ (setSheafificationAbIsoCanonical ℱ).hom.hom ≫ δ.hom = η
    rw [← Category.assoc, toSetSheafificationAb_comp_setSheafificationAbIsoCanonical_hom]
    exact hδ
  · intro γ hγ
    have hγ' : toSheafify J ℱ ≫ ((setSheafificationAbIsoCanonical ℱ).inv ≫ γ).hom = η := by
      change toSheafify J ℱ ≫ (setSheafificationAbIsoCanonical ℱ).inv.hom ≫ γ.hom = η
      simpa [toSetSheafificationAb, Category.assoc] using hγ
    have hcomp : (setSheafificationAbIsoCanonical ℱ).inv ≫ γ = δ := hδuniq _ hγ'
    calc
      γ = (setSheafificationAbIsoCanonical ℱ).hom ≫ ((setSheafificationAbIsoCanonical ℱ).inv ≫ γ) := by
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = (setSheafificationAbIsoCanonical ℱ).hom ≫ δ := by rw [hcomp]

private theorem compatibleAddCommGroupStructure_ext_of_add
    {F : X.Presheaf (Type u)} {h₁ h₂ : CompatibleAddCommGroupStructure F}
    (hadd : ∀ (U : (Opens X)ᵒᵖ) (s t : F.obj U),
      (h₁.toCompatibleAdditionMapStructure.add).app U (FunctorToTypes.prodMk s t) =
        (h₂.toCompatibleAdditionMapStructure.add).app U (FunctorToTypes.prodMk s t)) :
    h₁ = h₂ := by
  cases h₁
  cases h₂
  simp only [CompatibleAddCommGroupStructure.mk.injEq] at ⊢
  funext U
  apply AddCommGroup.ext
  funext s t
  simpa [CompatibleAddCommGroupStructure.toCompatibleAdditionMapStructure] using hadd U s t

private noncomputable def compatibleAddCommGroupStructureSheaf
    (h : CompatibleAddCommGroupStructure (ℱ^#).obj) : Ab(X) where
  obj := h.toPAb
  property := by
    refine (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2 ?_
    simpa [h.toPAb_forget] using (ℱ^#).property

private theorem compatibleAddCommGroupStructureSheaf_forget
    (h : CompatibleAddCommGroupStructure (ℱ^#).obj) :
    (compatibleAddCommGroupStructureSheaf ℱ h).obj ⋙ forget AddCommGrpCat.{u} = (ℱ^#).obj :=
  h.toPAb_forget

private noncomputable def toCompatibleSetSheafification
    (h : CompatibleAddCommGroupStructure (ℱ^#).obj)
    (hadd : ∀ (U : (Opens X)ᵒᵖ) (s t : ℱ.obj U),
      by
        let _ := h.addCommGroup U
        exact
          (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U (s + t) =
            (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U s +
              (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U t) :
    ℱ ⟶ h.toPAb where
  app U := by
    let _ := h.addCommGroup U
    exact AddCommGrpCat.ofHom <|
      AddMonoidHom.mk' ((toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U) (hadd U)
  naturality := by
    intro U V i
    apply AddCommGrpCat.ext
    intro s
    simpa using congrFun ((toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).naturality i) s

private theorem toCompatibleSetSheafification_forget
    (h : CompatibleAddCommGroupStructure (ℱ^#).obj)
    (hadd : ∀ (U : (Opens X)ᵒᵖ) (s t : ℱ.obj U),
      by
        let _ := h.addCommGroup U
        exact
          (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U (s + t) =
            (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U s +
              (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U t) :
    Functor.whiskerRight (toCompatibleSetSheafification ℱ h hadd) (forget AddCommGrpCat.{u}) ≫
      eqToHom h.toPAb_forget =
        toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u}) := by
  ext U s
  rfl

private theorem setSheafificationAb_iso_of_toSheafify_map_add
    (h : CompatibleAddCommGroupStructure (ℱ^#).obj)
    (hadd : ∀ (U : (Opens X)ᵒᵖ) (s t : ℱ.obj U),
      by
        let _ := h.addCommGroup U
        exact
          (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U (s + t) =
            (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U s +
              (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U t) :
    ∃! γ : setSheafificationAb ℱ ⟶ compatibleAddCommGroupStructureSheaf ℱ h,
      toSetSheafificationAb ℱ ≫ γ.hom = toCompatibleSetSheafification ℱ h hadd ∧
        Functor.whiskerRight γ.hom (forget AddCommGrpCat.{u}) =
          eqToHom (setSheafificationAb_forget ℱ) ≫
            eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h).symm := by
  obtain ⟨γ, hγ, hγuniq⟩ :=
    existsUnique_setSheafificationLift
      (show ℱ ⟶ (compatibleAddCommGroupStructureSheaf ℱ h).obj from
        toCompatibleSetSheafification ℱ h hadd)
  have hunderlying_id :
      eqToHom (setSheafificationAb_forget ℱ).symm ≫
          Functor.whiskerRight γ.hom (forget AddCommGrpCat.{u}) ≫
            eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h) =
        𝟙 (ℱ^#).obj := by
    apply setSheafification_hom_ext ℱ
    calc
      toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u}) ≫
          eqToHom (setSheafificationAb_forget ℱ).symm ≫
            Functor.whiskerRight γ.hom (forget AddCommGrpCat.{u}) ≫
              eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h) =
        Functor.whiskerRight (toSetSheafificationAb ℱ) (forget AddCommGrpCat.{u}) ≫
            Functor.whiskerRight γ.hom (forget AddCommGrpCat.{u}) ≫
              eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h) := by
          rw [← toSetSheafificationAb_forget ℱ]
          simp [Category.assoc]
      _ = Functor.whiskerRight (toSetSheafificationAb ℱ ≫ γ.hom) (forget AddCommGrpCat.{u}) ≫
            eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h) := by
          simp [Category.assoc]
      _ = Functor.whiskerRight (toCompatibleSetSheafification ℱ h hadd)
            (forget AddCommGrpCat.{u}) ≫
            eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h) := by
          simpa using congrArg
            (fun k ↦
              Functor.whiskerRight k (forget AddCommGrpCat.{u}) ≫
                eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h))
            hγ
      _ = toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u}) := by
          exact toCompatibleSetSheafification_forget ℱ h hadd
      _ = toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u}) ≫ 𝟙 (ℱ^#).obj := by simp
  have hunderlying :
      Functor.whiskerRight γ.hom (forget AddCommGrpCat.{u}) =
        eqToHom (setSheafificationAb_forget ℱ) ≫
          eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h).symm := by
    have h' := congrArg
      (fun k ↦
        eqToHom (setSheafificationAb_forget ℱ) ≫ k ≫
          eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h).symm)
      hunderlying_id
    simpa [Category.assoc] using h'
  refine ⟨γ, ⟨hγ, hunderlying⟩, ?_⟩
  intro γ' hγ'
  exact hγuniq γ' hγ'.1

/-- Lemma 6.18.2, exact-structure uniqueness: if a compatible additive structure on the fixed
set-valued sheafification `ℱ^#` makes the actual sheafification unit additive on every open, then
that structure is exactly the transported structure
`setSheafificationCompatibleAddCommGroupStructure ℱ`. -/
theorem setSheafificationCompatibleAddCommGroupStructure_unique
    (h : CompatibleAddCommGroupStructure (ℱ^#).obj)
    (hadd : ∀ (U : (Opens X)ᵒᵖ) (s t : ℱ.obj U),
      by
        let _ := h.addCommGroup U
        exact
          (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U (s + t) =
            (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U s +
              (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U t) :
    h = setSheafificationCompatibleAddCommGroupStructure ℱ := by
  obtain ⟨γ, hγ, _⟩ :=
    setSheafificationAb_iso_of_toSheafify_map_add ℱ h hadd
  apply compatibleAddCommGroupStructure_ext_of_add
  intro U s t
  let _ := h.addCommGroup U
  let _ := (setSheafificationCompatibleAddCommGroupStructure ℱ).addCommGroup U
  letI : (forget AddCommGrpCat.{u}).ReflectsIsomorphisms := by
    infer_instance
  haveI :
      IsIso
        (((Functor.whiskeringRight (Opens X)ᵒᵖ AddCommGrpCat.{u} (Type u)).obj
          (forget AddCommGrpCat.{u})).map γ.hom) := by
    change IsIso (Functor.whiskerRight γ.hom (forget AddCommGrpCat.{u}))
    rw [hγ.2]
    infer_instance
  haveI : IsIso (γ.hom) :=
    isIso_of_reflects_iso γ.hom
      ((Functor.whiskeringRight (Opens X)ᵒᵖ AddCommGrpCat.{u} (Type u)).obj
        (forget AddCommGrpCat.{u}))
  let hU := γ.hom.app U
  letI : IsIso hU := NatIso.isIso_app_of_isIso γ.hom U
  let iU := inv hU
  have hU_id (x : ((setSheafificationAb ℱ).obj).obj U) : hU.hom x = x := by
    simpa using congrFun (congrArg (fun k ↦ k.app U) hγ.2) x
  have iU_id (x : ((compatibleAddCommGroupStructureSheaf ℱ h).obj).obj U) : iU.hom x = x := by
    have h₁ : hU.hom (iU.hom x) = iU.hom x := hU_id (iU.hom x)
    have h₂ : hU.hom (iU.hom x) = x := by
      simpa [iU] using IsIso.inv_hom_id_apply hU x
    exact h₁.symm.trans h₂
  have hs : iU.hom s = s := iU_id s
  have ht : iU.hom t = t := iU_id t
  have hsource :
      (iU.hom
        ((h.toCompatibleAdditionMapStructure.add).app U (FunctorToTypes.prodMk s t))) =
      (h.toCompatibleAdditionMapStructure.add).app U (FunctorToTypes.prodMk s t) := by
    exact iU_id ((h.toCompatibleAdditionMapStructure.add).app U (FunctorToTypes.prodMk s t))
  have hadd :
      (iU.hom
        ((h.toCompatibleAdditionMapStructure.add).app U (FunctorToTypes.prodMk s t))) =
      ((setSheafificationCompatibleAddCommGroupStructure ℱ).toCompatibleAdditionMapStructure.add).app U
        (FunctorToTypes.prodMk (iU.hom s) (iU.hom t)) := by
    rw [CompatibleAdditionMapStructure.add_app_eq_add
        (h.toCompatibleAdditionMapStructure) U s t]
    rw [CompatibleAdditionMapStructure.add_app_eq_add
        ((setSheafificationCompatibleAddCommGroupStructure ℱ).toCompatibleAdditionMapStructure)
        U (iU.hom s) (iU.hom t)]
    exact iU.hom.map_add s t
  have htarget :
      ((setSheafificationCompatibleAddCommGroupStructure ℱ).toCompatibleAdditionMapStructure.add).app U
        (FunctorToTypes.prodMk (iU.hom s) (iU.hom t)) =
      ((setSheafificationCompatibleAddCommGroupStructure ℱ).toCompatibleAdditionMapStructure.add).app U
        (FunctorToTypes.prodMk s t) := by
    simp [hs, ht]
  exact hsource.symm.trans (hadd.trans htarget)

end
