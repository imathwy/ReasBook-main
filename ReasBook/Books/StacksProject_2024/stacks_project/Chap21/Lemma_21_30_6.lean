import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import StacksProject_2024.stacks_project.Chap21.Situation_21_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.GrothendieckTopology

noncomputable section

universe u

attribute [local instance] CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C]
variable {τ τ' : GrothendieckTopology C}
variable (P : MorphismProperty C)
variable (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{u}))

variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{u})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (τ'.over X) (τ'.over Y))]
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasExt (Sheaf (τ'.over X) AddCommGrpCat.{u})]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{u})]

/- Domain-style sampling for Lemma 21.30.6:
- primary domain: localized cohomology of abelian sheaves on slice sites, together with the
  higher-direct-image descent picture for a singleton `τ`-cover `X ⟶ Y` in Situation `21.30.1`;
- sampled owner declarations:
  `CohomologyComparisonSituation`,
  `CohomologyComparisonSituation.LocalVanishing`,
  `Sheaf.H'`,
  `Sheaf.cohomologyPresheaf`,
  `(τ'.over Y).Cover`;
- best owner abstraction:
  `source-facing`: the equalizer-vanishing statement for classes on `Over.mk f`;
  `core/canonical`: the slice-site sheaf categories `Sheaf (τ'.over X) AddCommGrpCat`,
    objectwise cohomology `H'`, the cohomology presheaf, the situation owner
    `CohomologyComparisonSituation.LocalVanishing`, and the canonical cover owner on `τ'.over Y`;
  `bridge/view`: the product object `Over.mk f ⨯ U` in `Over Y`, which is the canonical slice-site
    realization of the pullback object `U ×_Y X`.

Primitive data versus derived API:
- primitive data: the comparison situation `h`, a sheaf `ℱ' ∈ A' Y`, an object `U : Over Y`, and a
  localized cohomology class on `U`;
- derived API: the equalizer-vanishing theorem below, which reuses the source-facing support owner
  `(V_n)` from `Situation_21_30_1`. The deleted placeholder parameters `coeff`, `cohomology`, and
  `map` duplicated these canonical owners without preserving the chapter's semantics.
-/

section Equalizer

variable [HasPullbacks C]

-- Proof sketch: view `θ` as a section of the higher direct image of the pullback of `ℱ'` along
-- `f` on the slice site `(C_{τ'}/Y)`. The equalizer condition is exactly the descent datum for the
-- singleton `τ`-cover `X ⟶ Y`, and the comparison situation makes that higher direct image into an
-- object of `A'_Y`. Applying `(V_n)` to that descended class yields a `τ'`-cover of `Y` on which
-- all pullbacks to the canonical slice pullbacks `Yᵢ ×_Y X` vanish.
/-- Lemma 21.30.6: in Situation `21.30.1`, if `f : X ⟶ Y` is a singleton `τ`-cover in `P` and a
degree `n + 1` cohomology class `θ` of the coarser `τ`-sheaf underlying `ℱ' ∈ A' Y` over
`Over.mk f` has equal pullbacks to `Over.mk f ⨯ Over.mk f`, then after a `τ'`-cover of `Y` its
pullback to each `Yᵢ ×_Y X` vanishes. The pullback objects are expressed canonically in `Over Y`
by binary products with `Over.mk f`. -/
@[stacks 0EZD]
theorem equalizer_class_vanishes_after_tauPrime_cover
    (h : CohomologyComparisonSituation τ τ' P A')
    (n : ℕ)
    (hVn : h.LocalVanishing n)
    {X Y : C} (f : X ⟶ Y)
    (hf : P f)
    (hcover : (τ.over Y).CoversTop (fun _ : PUnit ↦ Over.mk f))
    (ℱ' : Sheaf (τ'.over Y) AddCommGrpCat.{u})
    (hℱ' : A' Y ℱ')
    (θ : (h.coarserSheaf hℱ').H' (n + 1) (Over.mk f))
    (hθ :
      let F : Sheaf (τ.over Y) AddCommGrpCat.{u} := h.coarserSheaf hℱ'
      ((F.cohomologyPresheaf (n + 1)).map
        (prod.fst : Over.mk f ⨯ Over.mk f ⟶ Over.mk f).op) θ =
          ((F.cohomologyPresheaf (n + 1)).map
            (prod.snd : Over.mk f ⨯ Over.mk f ⟶ Over.mk f).op) θ) :
    ∃ T : (τ'.over Y).Cover (Over.mk (𝟙 Y)), ∀ I : T.Arrow,
      let F : Sheaf (τ.over Y) AddCommGrpCat.{u} := h.coarserSheaf hℱ'
      ((F.cohomologyPresheaf (n + 1)).map
        (prod.fst : Over.mk f ⨯ I.Y ⟶ Over.mk f).op) θ = 0 := by
  sorry

end Equalizer

end CategoryTheory.GrothendieckTopology
