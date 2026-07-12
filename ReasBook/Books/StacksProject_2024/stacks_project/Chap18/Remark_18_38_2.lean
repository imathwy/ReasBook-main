import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Example_7_33_8
import StacksProject_2024.Chap07.Lemma_7_27_2
import StacksProject_2024.Chap07.Remark_7_35_4
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Lemma_18_36_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u

/- Domain-style sampling:
- primary domain: localized direct image of sheaves of modules on a ringed site and the induced
  stalk functors at points;
- sampled owner declarations:
  `ringSheaf`,
  `ringedSiteModuleCategory`,
  `SheafOfModules.pushforwardOver`,
  `SheafOfModules.toSheaf`,
  `GrothendieckTopology.Point.sheafFiber`;
- best owner abstraction: the canonical localized direct-image functor
  `SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)` between
  `ringedSiteModuleCategory (J.over U) (𝒪.over U)` and `ringedSiteModuleCategory J 𝒪`;
- primitive data: the structure sheaf `𝒪`, the object `U`, the point `p`, and the localized
  module `𝒢`;
- derived API: the source-facing universal stalk formula obtained by replacing `j_{U!}` with
  `j_{U,*}` in Lemma `18.38.1`, and the global counterexample theorem negating that universal
  statement;
- source/core/bridge triage:
  `source-facing`: the remark that the shriek-style stalk coproduct formula fails for `j_{U,*}`;
  `core/canonical`: `ringSheaf`, `ringedSiteModuleCategory`,
    `SheafOfModules.pushforwardOver`, `SheafOfModules.pushforward`, and
    `SheafOfModules.toSheaf` together with `GrothendieckTopology.Point.sheafFiber`;
  `bridge/view`: the universal formula appearing directly under the outer negation in the theorem
    below.

The previous local aliases for the underlying `RingCat`-valued sheaf, the module category, and
the localized direct image were duplicate wheels of these chapter/mathlib owners, so the public
surface below now uses the canonical declarations directly. -/

/-- Helper for Remark 18.38.2: a universal module-valued stalk formula for `j_{U,*}` would
allow one to recover an equivalence of the underlying generators from an additive isomorphism
between free abelian groups. -/
private theorem freeAbelianIsoInducesEquiv {A B : Type u}
    (h : IsIsomorphic (AddCommGrpCat.free.obj A) (AddCommGrpCat.free.obj B)) :
    Nonempty (A ≃ B) := by
  classical
  let e := Classical.choice h
  let eAdd : FreeAbelianGroup A ≃+ FreeAbelianGroup B :=
    { toFun := e.hom.hom
      invFun := e.inv.hom
      left_inv := fun x ↦ by
        -- The inverse identity of the categorical isomorphism gives the additive left inverse.
        simpa using AddGrpCat.inv_hom_apply e x
      right_inv := fun x ↦ by
        -- The other triangle identity gives the additive right inverse.
        simpa using AddGrpCat.hom_inv_apply e x
      map_add' := fun x y ↦ by
        -- The forward map is an additive-group morphism, so it preserves addition.
        simpa using e.hom.hom.map_add x y }
  -- The standard generator-recovery lemma for free abelian groups turns this additive
  -- equivalence into an equivalence of the generator types.
  exact ⟨Equiv.ofFreeAbelianGroupEquiv eAdd⟩

/-- Helper for Remark 18.38.2: once the witness-side stalk formula has been normalized to a free
abelian-group isomorphism, the original site-level counterexample is contradicted immediately. -/
private theorem freeAbelianIsoContradictsWitness {A B : Type u}
    (hbad : ¬ IsIsomorphic A B)
    (hfree : IsIsomorphic (AddCommGrpCat.free.obj A) (AddCommGrpCat.free.obj B)) :
    False := by
  classical
  obtain ⟨e⟩ := freeAbelianIsoInducesEquiv hfree
  -- The recovered equivalence of generators is exactly the forbidden site-level isomorphism.
  exact hbad ⟨Equiv.toIso e⟩

/-- Helper for Remark 18.38.2: on the chaotic `Bool` site, the fiber of `pointBot U` over `X` is
the ordinary hom-set `U ⟶ X`. -/
private noncomputable abbrev pointBotFiberEquivHom (U X : Bool) :
    (GrothendieckTopology.pointBot (J := (⊥ : GrothendieckTopology Bool)) U).fiber.obj X ≃
      (U ⟶ X) :=
  CategoryTheory.shrinkYonedaObjObjEquiv (X := X) (Y := op U)

/-- Helper for Remark 18.38.2: the chaotic `Bool` site with `U = false`, the point `pointBot true`,
and the terminal sheaf on `Bool/false` already violate the site-level localization-pushforward
stalk formula from Remark `7.35.4`. -/
private theorem binaryProductsLocalizationPushforwardCounterexample :
    ¬ IsIsomorphic
      ((GrothendieckTopology.pointBot (J := (⊥ : GrothendieckTopology Bool)) true).sheafFiber.obj
        (((((Over.forget false).morphismOfTopoiInOfCocontinuous
            ((⊥ : GrothendieckTopology Bool).over false) (⊥ : GrothendieckTopology Bool)) _*).obj
          (⊤_ Sheaf ((⊥ : GrothendieckTopology Bool).over false) (Type u)))))
      (Σ x :
          (GrothendieckTopology.pointBot (J := (⊥ : GrothendieckTopology Bool)) true).fiber.obj
            false,
        ((GrothendieckTopology.pointBot (J := (⊥ : GrothendieckTopology Bool)) true).over x)
          .sheafFiber.obj (⊤_ Sheaf ((⊥ : GrothendieckTopology Bool).over false) (Type u))) := by
  classical
  let J : GrothendieckTopology Bool := ⊥
  let p : GrothendieckTopology.Point J := GrothendieckTopology.pointBot (J := J) true
  let G : Sheaf (J.over false) (Type u) := ⊤_
  -- On the chaotic site, the point `pointBot true` has no lift above `false`, so the sigma-side is
  -- empty.
  have hright :
      IsEmpty (Σ x : p.fiber.obj false, (p.over x).sheafFiber.obj G) := by
    refine ⟨fun y ↦ ?_⟩
    have hHom : IsEmpty (true ⟶ false) := by
      infer_instance
    exact hHom.false ((pointBotFiberEquivHom true false) y.1)
  -- The direct-image side is nevertheless inhabited: evaluate the pushed-forward terminal sheaf at
  -- `true` and take its germ at the canonical element of the fiber over `true`.
  let xTrue : p.fiber.obj true := (pointBotFiberEquivHom true true).symm (𝟙 true)
  let s :
      (((((Over.forget false).morphismOfTopoiInOfCocontinuous (J.over false) J) _*).obj G).obj.obj
        (op true)) :=
    (localization_directImage_objIso_sections_over_star (J := J) (U := false) G true).inv
      PUnit.unit
  have hleft :
      Nonempty
        (p.sheafFiber.obj
          (((((Over.forget false).morphismOfTopoiInOfCocontinuous (J.over false) J) _*).obj G))) := by
    refine ⟨p.toPresheafFiber true xTrue
      (((((Over.forget false).morphismOfTopoiInOfCocontinuous (J.over false) J) _*).obj G).obj) s⟩
  intro h
  let e := Classical.choice h
  exact hright.false (e.hom (Classical.choice hleft))

/-- Helper for Remark 18.38.2: a universal module-valued stalk formula for `j_{U,*}` contradicts
the forbidden site-level witness from Remark `7.35.4`. -/
private theorem moduleUniversalFormulaContradictsSiteWitness
    (hall : ∀ {C : Type u} [Category.{u} C] [HasBinaryProducts C] (J : GrothendieckTopology C)
        [LocallySmall.{u} C]
        [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
        (𝒪 : Sheaf J CommRingCat.{u}) (U : C) (p : GrothendieckTopology.Point.{u} J)
        (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)),
        IsIsomorphic
          (((SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber).obj
            ((SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)).obj 𝒢)))
          (∐ fun x : p.fiber.obj U ↦
            ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
                (p.over x).sheafFiber).obj 𝒢))) :
    False := by
  -- Route correction: the old helper tried to prove a new universal site-level theorem. For the
  -- outer negation it is enough to extract one counterexample witness from Remark `7.35.4`,
  -- bridge that single witness through free abelian groups, and contradict the witness.
  -- Route correction: the witness search is now closed by the explicit chaotic-`Bool`
  -- counterexample above, so the only remaining work is the module-level normalization.
  -- TODO: instantiate `hall` on the constant-`ℤ` free-module sheaf built from the terminal-sheaf
  -- witness on `Bool/false`, rewrite both stalk sides to free abelian groups by the module-stalk
  -- sheafification comparison, and close with
  -- `freeAbelianIsoContradictsWitness binaryProductsLocalizationPushforwardCounterexample`.
  sorry

/-- Remark 18.38.2: the coproduct decomposition of stalks proved in Lemma `18.38.1` for
`j_{U!}` does not extend to the localization direct-image functor `j_{U,*}`. Equivalently, the
naive statement obtained by replacing `j_{U!}` with `j_{U,*}` in Lemma `18.38.1` is not valid in
general. -/
theorem ringedSiteLocalizedDirectImage_not_hasShriekStyleStalkFormula
    : ¬ ∀ {C : Type u} [Category.{u} C] [HasBinaryProducts C] (J : GrothendieckTopology C)
        [LocallySmall.{u} C]
        [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
        (𝒪 : Sheaf J CommRingCat.{u}) (U : C) (p : GrothendieckTopology.Point.{u} J)
        (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)),
        IsIsomorphic
          (((SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber).obj
            ((SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)).obj 𝒢)))
          (∐ fun x : p.fiber.obj U ↦
            ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
                (p.over x).sheafFiber).obj 𝒢)) := by
  -- Proof comment: after the route correction above, it is enough to derive a contradiction from
  -- one witness of the site-level failure supplied by Remark `7.35.4`.
  intro hall
  exact moduleUniversalFormulaContradictsSiteWitness hall
