import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_proof.stacks_project.Chap07.Lemma_7_26_4.Index
import stacks_proof.stacks_project.Chap07.Lemma_7_26_6
import stacks_proof.stacks_project.Chap08.Lemma_8_3_7
import stacks_proof.stacks_project.Chap08.Definition_8_5_5
import stacks_proof.stacks_project.Chap08.Definition_8_11_1
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part15

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Lemma 8.11.8 Part16: forgetting an `AddCommGrpCat`-valued sheaf gives a
`Type`-valued sheaf on the same localized site. -/
theorem forgetAddCommSheaf_isSheaf {U : C}
    (A : Sheaf (J.over U) AddCommGrpCat.{max u v}) :
    Presheaf.IsSheaf (J.over U) (A.1 ⋙ forget AddCommGrpCat.{max u v}) := by
  -- Convert the sheaf condition along the faithful forgetful functor to `Type`.
  exact (Presheaf.isSheaf_iff_isSheaf_forget (J.over U) A.1
    (forget AddCommGrpCat.{max u v})).mp A.2

/-- Helper for Lemma 8.11.8 Part16: the forgotten `Type`-valued sheaf underlying an
`AddCommGrpCat`-valued sheaf. -/
def forgetAddCommSheaf {U : C}
    (A : Sheaf (J.over U) AddCommGrpCat.{max u v}) :
    Sheaf (J.over U) (Type (max u v)) where
  obj := A.1 ⋙ forget AddCommGrpCat.{max u v}
  property := forgetAddCommSheaf_isSheaf (J := J) A

/-- Helper for Lemma 8.11.8 Part16: pullback over a map commutes definitionally with forgetting
an `AddCommGrpCat`-valued sheaf to its underlying `Type`-valued sheaf. -/
def overMapPullback_forget_iso {U V : C} (f : V ⟶ U)
    (A : Sheaf (J.over U) AddCommGrpCat.{max u v}) :
    (((J.overMapPullback AddCommGrpCat.{max u v} f).obj A).1 ⋙
      forget AddCommGrpCat.{max u v}) ≅
      ((J.overMapPullback (Type (max u v)) f).obj (forgetAddCommSheaf (J := J) A)).1 :=
  Iso.refl _

/-- Helper for Lemma 8.11.8 Part16: the slicewise common-owner comparison for a lifted
absolute-glueing family is the additive conjugation comparison transported through the two local
lift comparisons. -/
noncomputable def slice_addcomm_lifted_common_owner_iso
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (liftedComparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    lifted x ≅ lifted y :=
  -- Keep the local definition in this support module; the analogous helper in Part15 is private.
  liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ ≪≫ (liftedComparison y).symm

/-- Helper for Lemma 8.11.8: the common-owner comparison between two slicewise additive lifts
forgets to the canonical owner-change map between their identifications with `F.obj U`. This
packages the additive family into one fixed underlying owner before the global reconstruction
step. -/
theorem slice_addcomm_lifted_common_owner_iso_forget_hom
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hcomparison : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ = comparison y)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    (liftedComparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (liftedCompatibility : ∀ {U : C} (x : 𝒮.p.Fiber U),
      Functor.whiskerRight (liftedComparison x).hom.1
          (forget AddCommGrpCat.{max u v}) =
        (forgetIso x).hom ≫ (comparison x).hom.1)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    Functor.whiskerRight
        ((slice_addcomm_lifted_common_owner_iso
          hAbelian F comparison lifted liftedComparison φ).hom.1)
        (forget AddCommGrpCat.{max u v}) ≫
      (forgetIso y).hom =
        (forgetIso x).hom := by
  -- Specialize the fixed-owner uniqueness lemma to the absolute-glueing owner `F.obj U`.
  exact
    slice_addcomm_common_owner_iso_forget_hom
      (𝒮 := 𝒮) hAbelian
      (comparison x) (comparison y)
      (lifted x) (lifted y)
      (forgetIso x) (forgetIso y)
      (liftedComparison x) (liftedComparison y)
      (liftedCompatibility x) (liftedCompatibility y)
      φ (hcomparison φ)

/-- Helper for Lemma 8.11.8: after composing the common-owner comparison between two slicewise
additive lifts with the underlying comparison to `y`, the forgetful map collapses to the same
underlying owner comparison obtained directly from `x`. This is the transport-stable
normalization needed when the final global additive reconstruction compares different local lifts
through one fixed absolute-glueing owner. -/
theorem slice_addcomm_lifted_common_owner_iso_forget_to_comparison
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hcomparison : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ = comparison y)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    (liftedComparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (liftedCompatibility : ∀ {U : C} (x : 𝒮.p.Fiber U),
      Functor.whiskerRight (liftedComparison x).hom.1
          (forget AddCommGrpCat.{max u v}) =
        (forgetIso x).hom ≫ (comparison x).hom.1)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    Functor.whiskerRight
        ((slice_addcomm_lifted_common_owner_iso
          hAbelian F comparison lifted liftedComparison φ).hom.1)
        (forget AddCommGrpCat.{max u v}) ≫
      (forgetIso y).hom ≫ (comparison y).hom.1 =
        (forgetIso x).hom ≫ (comparison y).hom.1 := by
  -- First collapse the fixed-owner comparison on the additive side, then append the comparison to
  -- the target automorphism sheaf on the common owner.
  simpa [Category.assoc] using
    congrArg
      (fun η ↦ η ≫ (comparison y).hom.1)
      (slice_addcomm_lifted_common_owner_iso_forget_hom
        (𝒮 := 𝒮) hAbelian F comparison hcomparison
        lifted forgetIso liftedComparison liftedCompatibility φ)

/-- Helper for Lemma 8.11.8: evaluating the fixed-owner comparison collapse at the terminal
object of `C / U` produces the exact section-level identity needed by the remaining reconstructed
map-additivity check. This keeps the final blocker at the terminal-component level instead of
reopening sheaf-level transports. -/
theorem slice_addcomm_lifted_common_owner_iso_terminal_app_forget_to_comparison
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hcomparison : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ = comparison y)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    (liftedComparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (liftedCompatibility : ∀ {U : C} (x : 𝒮.p.Fiber U),
      Functor.whiskerRight (liftedComparison x).hom.1
          (forget AddCommGrpCat.{max u v}) =
        (forgetIso x).hom ≫ (comparison x).hom.1)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    (Functor.whiskerRight
        ((slice_addcomm_lifted_common_owner_iso
          hAbelian F comparison lifted liftedComparison φ).hom.1)
        (forget AddCommGrpCat.{max u v})).app
        (Opposite.op (Over.mk (𝟙 U))) ≫
      (forgetIso y).hom.app (Opposite.op (Over.mk (𝟙 U))) ≫
      (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 U))) =
        (forgetIso x).hom.app (Opposite.op (Over.mk (𝟙 U))) ≫
          (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 U))) := by
  -- Evaluate the fixed-owner comparison collapse at the terminal object of `C / U`.
  simpa [NatTrans.comp_app, Category.assoc] using
    congrArg
      (fun η ↦ η.app (Opposite.op (Over.mk (𝟙 U))))
      (slice_addcomm_lifted_common_owner_iso_forget_to_comparison
        (𝒮 := 𝒮) hAbelian F comparison hcomparison
        lifted forgetIso liftedComparison liftedCompatibility φ)

end CategoryTheory
