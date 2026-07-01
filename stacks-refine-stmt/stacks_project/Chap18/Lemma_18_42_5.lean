import Mathlib
import stacks_project.Chap07.Definition_7_42_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The constant `RingCat`-valued presheaf with value `Λ` on a site. -/
abbrev constantRingPresheaf (Λ : Type w) [Ring Λ] : Cᵒᵖ ⥤ RingCat.{w} :=
  (Functor.const Cᵒᵖ).obj (RingCat.of Λ)

/-- The constant sheaf of rings `\underline{\Lambda}` on a site. -/
abbrev constantRingSheaf (J : GrothendieckTopology C) (Λ : Type w) [Ring Λ]
    [HasWeakSheafify J RingCat.{w}] : Sheaf J RingCat.{w} :=
  (presheafToSheaf J RingCat.{w}).obj (constantRingPresheaf Λ)

/-- The constant presheaf of `\Lambda`-modules with value `M`, viewed as a presheaf of modules
over the constant ring presheaf `\Lambda`. -/
abbrev constantModulePresheaf (Λ : Type w) [Ring Λ] (M : ModuleCat.{w} Λ) :
    PresheafOfModules ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) := by
  let F : Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
    ((Functor.const Cᵒᵖ).obj M) ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}
  letI (X : Cᵒᵖ) : Module ↑(((Functor.const Cᵒᵖ).obj (RingCat.of Λ)).obj X) ↑(F.obj X) := by
    change Module Λ ↑M
    infer_instance
  exact PresheafOfModules.ofPresheaf F
    (fun {X Y} f r m ↦ by
      rfl)

/-- The constant sheaf of `\underline{\Lambda}`-modules associated with a `\Lambda`-module `M`. -/
abbrev constantModuleSheaf (J : GrothendieckTopology C) (Λ : Type w) [Ring Λ]
    (M : ModuleCat.{w} Λ)
    [HasWeakSheafify J RingCat.{w}]
    [J.WEqualsLocallyBijective RingCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    SheafOfModules (constantRingSheaf J Λ) :=
  let hW : J.W (toSheafify J (constantRingPresheaf Λ)) :=
    J.W_toSheafify (constantRingPresheaf Λ)
  let hι : Presheaf.IsLocallyInjective J
      (toSheafify J (constantRingPresheaf Λ)) :=
    hW.isLocallyInjective
  let hs : Presheaf.IsLocallySurjective J
      (toSheafify J (constantRingPresheaf Λ)) :=
    hW.isLocallySurjective
  (@PresheafOfModules.sheafification _ _ _ _ _ (toSheafify J (constantRingPresheaf Λ))
      hι hs _ _).obj
    (constantModulePresheaf Λ M)

variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J RingCat.{w}]
variable [J.WEqualsLocallyBijective RingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

-- Proof sketch: if `M` is finitely generated, its generators define global sections of the
-- constant sheaf that generate it locally, so `\underline M` is of finite type. Conversely,
-- choose an object of the site that is not sheaf theoretically empty; local finite generation on
-- that object comes from finitely many elements of `M`, and injectivity of restriction to a
-- nonempty object shows those elements already generate `M`.
/-- Lemma 18.42.5 (1): the constant sheaf `\underline M` of `\underline{\Lambda}`-modules is of
finite type if and only if the `\Lambda`-module `M` is finite, assuming the sheaf topos of the
site is not empty. -/
theorem isFiniteType_constantModuleSheaf_iff_module_finite
    (M : ModuleCat.{w} Λ)
    (hne : ∃ U : C, ¬ J.IsSheafTheoreticallyEmpty U) :
    (constantModuleSheaf J Λ M).IsFiniteType ↔ Module.Finite Λ M := sorry

-- Proof sketch: finite presentation of `\underline M` implies finite type by the first clause.
-- Choose a finite generating set of `M`, use the induced short exact sequence
-- `0 → K → Λ^{\oplus r} → M → 0`, pass to constant sheaves using exactness of the constant sheaf
-- functor, and apply the finite-presentation kernel criterion to conclude that `K` is finite.
-- The converse follows by sheafifying a finite presentation of `M`.
/-- Lemma 18.42.5 (2): the constant sheaf `\underline M` of `\underline{\Lambda}`-modules is
finitely presented if and only if the `\Lambda`-module `M` is finitely presented, assuming the
sheaf topos of the site is not empty. -/
theorem isFinitePresentation_constantModuleSheaf_iff_module_finitePresentation
    (M : ModuleCat.{w} Λ)
    (hne : ∃ U : C, ¬ J.IsSheafTheoreticallyEmpty U) :
    (constantModuleSheaf J Λ M).IsFinitePresentation ↔
      Module.FinitePresentation Λ M := sorry

end CategoryTheory
