import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_project.Chap07.Lemma_7_26_5
import stacks_project.Chap07.Lemma_7_26_6
import stacks_project.Chap08.Lemma_8_3_7
import stacks_project.Chap08.Definition_8_5_5
import stacks_project.Chap08.Definition_8_11_1
import stacks_project.Chap08.Lemma_8_11_8.Part15

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
/-- Helper for Lemma 8.11.8: the common-owner comparison between two slicewise additive lifts
forgets to the canonical owner-change map between their identifications with `F.obj U`. This
packages the additive family into one fixed underlying owner before the global reconstruction
step. -/
private theorem slice_addcomm_lifted_common_owner_iso_forget_hom
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
          (𝒮 := 𝒮) hAbelian F comparison lifted liftedComparison φ).hom.1)
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
private theorem slice_addcomm_lifted_common_owner_iso_forget_to_comparison
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
          (𝒮 := 𝒮) hAbelian F comparison lifted liftedComparison φ).hom.1)
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
private theorem slice_addcomm_lifted_common_owner_iso_terminal_app_forget_to_comparison
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
          (𝒮 := 𝒮) hAbelian F comparison lifted liftedComparison φ).hom.1)
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

/-- Helper for Lemma 8.11.8: once the underlying absolute glueing is fixed, the remaining work is
to reconstruct a global `AddCommGrpCat`-valued sheaf whose localized restrictions are the local
abelian automorphism sheaves. -/
private theorem reconstructed_slice_addcomm_sheaf
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} :
    ∃ comparison : ∀ (x : 𝒮.p.Fiber U),
        chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U ≅
          automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
      (∀ {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y) ∧
        ∃ lifted : ∀ (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v},
          ∃ forgetIso : ∀ (x : 𝒮.p.Fiber U),
              ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅
                (chosen_cover_underlying_automorphism_sheaf
                  (𝒮 := 𝒮) hGerbe hAbelian U).1,
            ∃ liftedComparison : ∀ (x : 𝒮.p.Fiber U),
                lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
              ∀ (x : 𝒮.p.Fiber U),
                Functor.whiskerRight (liftedComparison x).hom.1
                    (forget AddCommGrpCat.{max u v}) =
                  (forgetIso x).hom ≫ (comparison x).hom.1 := by
  obtain ⟨comparison, hcomparison⟩ :=
    chosen_cover_slice_comparison
      (𝒮 := 𝒮) hGerbe hAbelian (U := U)
  let liftData :
      ∀ (x : 𝒮.p.Fiber U),
        ∃ A' : Sheaf (J.over U) AddCommGrpCat.{max u v},
          ∃ forgetIso : (A'.1 ⋙ forget AddCommGrpCat.{max u v}) ≅
              (chosen_cover_underlying_automorphism_sheaf
                (𝒮 := 𝒮) hGerbe hAbelian U).1,
            ∃ liftedComparison : A' ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
              Functor.whiskerRight liftedComparison.hom.1
                  (forget AddCommGrpCat.{max u v}) =
                forgetIso.hom ≫ (comparison x).hom.1 :=
    fun x ↦
      -- The chosen-cover slice comparison already identifies the fixed slice sheaf with
      -- `automorphismUnderlyingSheaf x`; transport the additive structure back along that map.
      slice_addcomm_sheaf_of_underlying_comparison
        (𝒮 := 𝒮) hAbelian
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U) x (comparison x)
  refine ⟨comparison, hcomparison, ?_⟩
  refine ⟨fun x ↦ Classical.choose (liftData x), ?_⟩
  refine ⟨fun x ↦ Classical.choose (Classical.choose_spec (liftData x)), ?_⟩
  refine ⟨fun x ↦ Classical.choose (Classical.choose_spec (Classical.choose_spec (liftData x))), ?_⟩
  intro x
  -- Read the forgetful compatibility from the chosen slice lift for `x`.
  exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (liftData x)))

/-- Helper for Lemma 8.11.8: on one localized site `C / U`, the Chapter 7 reconstruction
comparison identifies the reconstructed slice sheaf with the underlying `Type`-valued sheaf of
the chosen additive lift `lifted x`. This isolates the source-facing owner change before the
remaining global additivity descent. -/
private theorem reconstructed_over_to_lifted_underlying_hom_inv_id
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    {U : C} (x : 𝒮.p.Fiber U) :
    ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1 ≫ (forgetIso x).inv) ≫
        ((forgetIso x).hom ≫ (absolute_glueing_reconstruction_over_iso (J := J) F U).inv.1) =
      𝟙 _ := by
  ext T α
  -- Both comparison isomorphisms cancel pointwise on the underlying presheaf.
  simp [Category.assoc]

/-- Helper for Lemma 8.11.8: the inverse composite for the reconstructed-to-lifted underlying
comparison is the identity on the forgotten additive lift. -/
private theorem reconstructed_over_to_lifted_underlying_inv_hom_id
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    {U : C} (x : 𝒮.p.Fiber U) :
    ((forgetIso x).hom ≫ (absolute_glueing_reconstruction_over_iso (J := J) F U).inv.1) ≫
        ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1 ≫ (forgetIso x).inv) =
      𝟙 _ := by
  ext T α
  -- The reverse composite collapses by the same pointwise cancellation.
  simp [Category.assoc]

/-- Helper for Lemma 8.11.8: on one localized site `C / U`, the Chapter 7 reconstruction
comparison identifies the reconstructed slice sheaf with the underlying `Type`-valued sheaf of
the chosen additive lift `lifted x`. This isolates the source-facing owner change before the
remaining global additivity descent. -/
private noncomputable def reconstructed_over_to_lifted_underlying_iso
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    {U : C} (x : 𝒮.p.Fiber U) :
    ((absolute_glueing_reconstruction (J := J) F).over U).1 ≅
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) :=
  { hom := (absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1 ≫ (forgetIso x).inv
    inv := (forgetIso x).hom ≫ (absolute_glueing_reconstruction_over_iso (J := J) F U).inv.1
    hom_inv_id :=
      reconstructed_over_to_lifted_underlying_hom_inv_id
        (J := J) F lifted forgetIso x
    inv_hom_id :=
      reconstructed_over_to_lifted_underlying_inv_hom_id
        (J := J) F lifted forgetIso x }

/-- Helper for Lemma 8.11.8: after passing from the reconstructed slice sheaf to the forgotten
underlying sheaf of `lifted x`, the lifted comparison recovers the original fixed-owner
comparison `comparison x`. -/
private theorem reconstructed_over_to_lifted_then_comparison
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    (liftedComparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (liftedCompatibility : ∀ {U : C} (x : 𝒮.p.Fiber U),
      Functor.whiskerRight (liftedComparison x).hom.1
          (forget AddCommGrpCat.{max u v}) =
        (forgetIso x).hom ≫ (comparison x).hom.1)
    {U : C} (x : 𝒮.p.Fiber U) :
    (reconstructed_over_to_lifted_underlying_iso
        (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom ≫
      Functor.whiskerRight (liftedComparison x).hom.1
        (forget AddCommGrpCat.{max u v}) =
        (absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1 ≫
          (comparison x).hom.1 := by
  -- Expand the reconstructed-to-lifted comparison and collapse the fixed owner `F.obj U`.
  rw [liftedCompatibility x]
  simp [reconstructed_over_to_lifted_underlying_iso, Category.assoc]

/-- Helper for Lemma 8.11.8: evaluating the reconstructed-to-lifted comparison at the terminal
object of `C / U` gives the explicit section-level owner comparison needed in the remaining
restriction-map additivity descent. -/
private theorem reconstructed_over_to_lifted_terminal_app_then_comparison
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    (liftedComparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (liftedCompatibility : ∀ {U : C} (x : 𝒮.p.Fiber U),
      Functor.whiskerRight (liftedComparison x).hom.1
          (forget AddCommGrpCat.{max u v}) =
        (forgetIso x).hom ≫ (comparison x).hom.1)
    {U : C} (x : 𝒮.p.Fiber U) :
    ((reconstructed_over_to_lifted_underlying_iso
        (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom.app
        (Opposite.op (Over.mk (𝟙 U)))) ≫
      (Functor.whiskerRight (liftedComparison x).hom.1
        (forget AddCommGrpCat.{max u v})).app
          (Opposite.op (Over.mk (𝟙 U))) =
        ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
          (Opposite.op (Over.mk (𝟙 U)))) ≫
          (comparison x).hom.1.app (Opposite.op (Over.mk (𝟙 U))) := by
  -- Evaluate the sheaf-level comparison at the terminal slice object of `C / U`.
  simpa [NatTrans.comp_app, Category.assoc] using
    congrArg
      (fun η ↦ η.app (Opposite.op (Over.mk (𝟙 U))))
      (reconstructed_over_to_lifted_then_comparison
        (𝒮 := 𝒮) hAbelian F comparison
        lifted forgetIso liftedComparison liftedCompatibility x)

/-- Helper for Lemma 8.11.8: after passing from the reconstructed slice sheaf to the forgotten
underlying sheaf of `lifted x`, the lifted comparison followed by conjugation along `φ` lands on
the fixed-owner comparison to `y`. This packages the comparison half of the final band
compatibility before the remaining additivity descent. -/
private theorem reconstructed_over_to_lifted_then_conj
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    (liftedComparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (hforgetConj :
      ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
        Functor.whiskerRight
            ((liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
            (forget AddCommGrpCat.{max u v}) =
          (forgetIso x).hom ≫ (comparison y).hom.1)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    (reconstructed_over_to_lifted_underlying_iso
        (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom ≫
      Functor.whiskerRight
        ((liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
        (forget AddCommGrpCat.{max u v}) =
        (absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1 ≫
          (comparison y).hom.1 := by
  -- Expand the reconstructed-to-lifted comparison and collapse the fixed owner `F.obj U`.
  rw [hforgetConj φ]
  simp [reconstructed_over_to_lifted_underlying_iso, Category.assoc]

/-- Helper for Lemma 8.11.8: evaluating the reconstructed-to-lifted comparison followed by
conjugation at the terminal object of `C / U` exposes the exact section-level owner comparison
to the target automorphism sheaf. -/
private theorem reconstructed_over_to_lifted_terminal_app_then_conj
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    (liftedComparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (hforgetConj :
      ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
        Functor.whiskerRight
            ((liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
            (forget AddCommGrpCat.{max u v}) =
          (forgetIso x).hom ≫ (comparison y).hom.1)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    ((reconstructed_over_to_lifted_underlying_iso
        (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom.app
        (Opposite.op (Over.mk (𝟙 U)))) ≫
      (Functor.whiskerRight
        ((liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
        (forget AddCommGrpCat.{max u v})).app
          (Opposite.op (Over.mk (𝟙 U))) =
        ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
          (Opposite.op (Over.mk (𝟙 U)))) ≫
          (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 U))) := by
  -- Evaluate the sheaf-level transported conjugation comparison at the terminal slice object.
  simpa [NatTrans.comp_app, Category.assoc] using
    congrArg
      (fun η ↦ η.app (Opposite.op (Over.mk (𝟙 U))))
      (reconstructed_over_to_lifted_then_conj
        (𝒮 := 𝒮) hAbelian F comparison
        lifted forgetIso liftedComparison hforgetConj φ)

/-- Helper for Lemma 8.11.8: after the Chapter 7 reconstruction transport is normalized on the
source slice `C / V`, postcomposing with the terminal component of the lifted comparison recovers
the fixed-owner comparison needed for the final additivity argument. -/
private theorem absolute_glueing_reconstruction_restriction_map_after_lifted_terminal_comparison
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    (liftedComparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (liftedCompatibility : ∀ {U : C} (x : 𝒮.p.Fiber U),
      Functor.whiskerRight (liftedComparison x).hom.1
          (forget AddCommGrpCat.{max u v}) =
        (forgetIso x).hom ≫ (comparison x).hom.1)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber V) :
    (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
      ((reconstructed_over_to_lifted_underlying_iso
        (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom.app
        (Opposite.op (Over.mk (𝟙 V)))) ≫
      (Functor.whiskerRight (liftedComparison x).hom.1
        (forget AddCommGrpCat.{max u v})).app
          (Opposite.op (Over.mk (𝟙 V))) =
        ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
          (Opposite.op (Over.mk (𝟙 U)))) ≫
          GrothendieckTopology.absoluteGlueingToPresheafMap J F f ≫
          (comparison x).hom.1.app (Opposite.op (Over.mk (𝟙 V))) := by
  -- First replace the lifted terminal comparison by the fixed-owner terminal comparison.
  calc
    (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
        ((reconstructed_over_to_lifted_underlying_iso
          (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom.app
          (Opposite.op (Over.mk (𝟙 V)))) ≫
        (Functor.whiskerRight (liftedComparison x).hom.1
          (forget AddCommGrpCat.{max u v})).app
            (Opposite.op (Over.mk (𝟙 V))) =
      (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
        ((absolute_glueing_reconstruction_over_iso (J := J) F V).hom.1.app
          (Opposite.op (Over.mk (𝟙 V)))) ≫
        (comparison x).hom.1.app (Opposite.op (Over.mk (𝟙 V))) := by
          simpa [Category.assoc] using
            congrArg
              (fun η ↦ (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫ η)
              (reconstructed_over_to_lifted_terminal_app_then_comparison
                (𝒮 := 𝒮) hAbelian F comparison
                lifted forgetIso liftedComparison liftedCompatibility x)
    _ =
      ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
        (Opposite.op (Over.mk (𝟙 U)))) ≫
        GrothendieckTopology.absoluteGlueingToPresheafMap J F f ≫
        (comparison x).hom.1.app (Opposite.op (Over.mk (𝟙 V))) := by
          exact
            absolute_glueing_reconstruction_restriction_map_after_local_comparison
              (𝒮 := 𝒮) (J := J) hAbelian F comparison (f := f) x

/-- Helper for Lemma 8.11.8: after the Chapter 7 reconstruction transport is normalized on the
source slice `C / V`, postcomposing with the terminal component of the lifted comparison followed
by conjugation lands on the fixed-owner target comparison. -/
private theorem absolute_glueing_reconstruction_restriction_map_after_lifted_terminal_conj
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    (liftedComparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (hforgetConj :
      ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
        Functor.whiskerRight
            ((liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
            (forget AddCommGrpCat.{max u v}) =
          (forgetIso x).hom ≫ (comparison y).hom.1)
    {U V : C} (f : V ⟶ U) {x y : 𝒮.p.Fiber V} (φ : x ⟶ y) :
    (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
      ((reconstructed_over_to_lifted_underlying_iso
        (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom.app
        (Opposite.op (Over.mk (𝟙 V)))) ≫
      (Functor.whiskerRight
        ((liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
        (forget AddCommGrpCat.{max u v})).app
          (Opposite.op (Over.mk (𝟙 V))) =
        ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
          (Opposite.op (Over.mk (𝟙 U)))) ≫
          GrothendieckTopology.absoluteGlueingToPresheafMap J F f ≫
          (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 V))) := by
  -- First replace the transported conjugation comparison by the fixed-owner terminal comparison.
  calc
    (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
        ((reconstructed_over_to_lifted_underlying_iso
          (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom.app
          (Opposite.op (Over.mk (𝟙 V)))) ≫
        (Functor.whiskerRight
          ((liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
          (forget AddCommGrpCat.{max u v})).app
            (Opposite.op (Over.mk (𝟙 V))) =
      (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
        ((absolute_glueing_reconstruction_over_iso (J := J) F V).hom.1.app
          (Opposite.op (Over.mk (𝟙 V)))) ≫
        (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 V))) := by
          simpa [Category.assoc] using
            congrArg
              (fun η ↦ (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫ η)
              (reconstructed_over_to_lifted_terminal_app_then_conj
                (𝒮 := 𝒮) hAbelian F comparison
                lifted forgetIso liftedComparison hforgetConj φ)
    _ =
      ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
        (Opposite.op (Over.mk (𝟙 U)))) ≫
        GrothendieckTopology.absoluteGlueingToPresheafMap J F f ≫
        (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 V))) := by
          exact
            absolute_glueing_reconstruction_restriction_map_after_local_comparison
              (𝒮 := 𝒮) (J := J) hAbelian F comparison (f := f) y

/-- Helper for Lemma 8.11.8: after replacing the target-side lifted comparison by the fixed-owner
common-owner comparison on `lifted x`, the reconstructed restriction map still lands on the same
owner-level terminal composite. This pins the remaining blocker to the chosen-cover descent step
instead of the already-solved transport corridor. -/
private theorem absolute_glueing_reconstruction_restriction_map_after_lifted_terminal_common_owner
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
    {U V : C} (f : V ⟶ U) {x y : 𝒮.p.Fiber V} (φ : x ⟶ y) :
    (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
      ((reconstructed_over_to_lifted_underlying_iso
        (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom.app
        (Opposite.op (Over.mk (𝟙 V)))) ≫
      (Functor.whiskerRight
        ((slice_addcomm_lifted_common_owner_iso
          (𝒮 := 𝒮) hAbelian F comparison lifted liftedComparison φ).hom.1)
        (forget AddCommGrpCat.{max u v})).app
          (Opposite.op (Over.mk (𝟙 V))) ≫
      (forgetIso y).hom.app (Opposite.op (Over.mk (𝟙 V))) ≫
      (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 V))) =
        ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
          (Opposite.op (Over.mk (𝟙 U)))) ≫
          GrothendieckTopology.absoluteGlueingToPresheafMap J F f ≫
          (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 V))) := by
  -- First collapse the fixed-owner common-owner comparison at the terminal object of `C / V`.
  calc
    (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
        ((reconstructed_over_to_lifted_underlying_iso
          (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom.app
          (Opposite.op (Over.mk (𝟙 V)))) ≫
        (Functor.whiskerRight
          ((slice_addcomm_lifted_common_owner_iso
            (𝒮 := 𝒮) hAbelian F comparison lifted liftedComparison φ).hom.1)
          (forget AddCommGrpCat.{max u v})).app
            (Opposite.op (Over.mk (𝟙 V))) ≫
        (forgetIso y).hom.app (Opposite.op (Over.mk (𝟙 V))) ≫
        (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 V))) =
      (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
        ((reconstructed_over_to_lifted_underlying_iso
          (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom.app
          (Opposite.op (Over.mk (𝟙 V)))) ≫
        (forgetIso x).hom.app (Opposite.op (Over.mk (𝟙 V))) ≫
        (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 V))) := by
          simpa [Category.assoc] using
            congrArg
              (fun η ↦ (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
                ((reconstructed_over_to_lifted_underlying_iso
                  (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom.app
                  (Opposite.op (Over.mk (𝟙 V)))) ≫ η)
              (slice_addcomm_lifted_common_owner_iso_terminal_app_forget_to_comparison
                (𝒮 := 𝒮) hAbelian F comparison hcomparison
                lifted forgetIso liftedComparison liftedCompatibility φ)
    _ =
      (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
        ((absolute_glueing_reconstruction_over_iso (J := J) F V).hom.1.app
          (Opposite.op (Over.mk (𝟙 V)))) ≫
        (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 V))) := by
          simp [reconstructed_over_to_lifted_underlying_iso, Category.assoc]
    _ =
      ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
        (Opposite.op (Over.mk (𝟙 U)))) ≫
        GrothendieckTopology.absoluteGlueingToPresheafMap J F f ≫
        (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 V))) := by
          exact
            absolute_glueing_reconstruction_restriction_map_after_local_comparison
              (𝒮 := 𝒮) (J := J) hAbelian F comparison (f := f) y

/-- Helper for Lemma 8.11.8: on the terminal slice object of `C / V`, the transported conjugation
branch and the fixed-owner common-owner branch already agree after the Chapter 7 reconstruction
transport is normalized. This isolates the last unresolved work to descending this pointwise
normalization across the chosen target-side common refinement cover. -/
private theorem absolute_glueing_reconstruction_restriction_map_lifted_terminal_conj_eq_common_owner
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
    (hforgetConj :
      ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
        Functor.whiskerRight
            ((liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
            (forget AddCommGrpCat.{max u v}) =
          (forgetIso x).hom ≫ (comparison y).hom.1)
    {U V : C} (f : V ⟶ U) {x y : 𝒮.p.Fiber V} (φ : x ⟶ y) :
    (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
      ((reconstructed_over_to_lifted_underlying_iso
        (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom.app
        (Opposite.op (Over.mk (𝟙 V)))) ≫
      (Functor.whiskerRight
        ((liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
        (forget AddCommGrpCat.{max u v})).app
          (Opposite.op (Over.mk (𝟙 V))) =
      (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
        ((reconstructed_over_to_lifted_underlying_iso
          (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom.app
          (Opposite.op (Over.mk (𝟙 V)))) ≫
        (Functor.whiskerRight
          ((slice_addcomm_lifted_common_owner_iso
            (𝒮 := 𝒮) hAbelian F comparison lifted liftedComparison φ).hom.1)
          (forget AddCommGrpCat.{max u v})).app
            (Opposite.op (Over.mk (𝟙 V))) ≫
        (forgetIso y).hom.app (Opposite.op (Over.mk (𝟙 V))) ≫
        (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 V))) := by
  -- Both transported branches reduce to the same owner-level composite on `F.obj U`.
  calc
    (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
        ((reconstructed_over_to_lifted_underlying_iso
          (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom.app
          (Opposite.op (Over.mk (𝟙 V)))) ≫
        (Functor.whiskerRight
          ((liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
          (forget AddCommGrpCat.{max u v})).app
            (Opposite.op (Over.mk (𝟙 V))) =
      ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
        (Opposite.op (Over.mk (𝟙 U)))) ≫
        GrothendieckTopology.absoluteGlueingToPresheafMap J F f ≫
        (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 V))) := by
          exact
            absolute_glueing_reconstruction_restriction_map_after_lifted_terminal_conj
              (𝒮 := 𝒮) hAbelian F comparison
              lifted forgetIso liftedComparison hforgetConj f φ
    _ =
      (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
        ((reconstructed_over_to_lifted_underlying_iso
          (𝒮 := 𝒮) (J := J) F lifted forgetIso x).hom.app
          (Opposite.op (Over.mk (𝟙 V)))) ≫
        (Functor.whiskerRight
          ((slice_addcomm_lifted_common_owner_iso
            (𝒮 := 𝒮) hAbelian F comparison lifted liftedComparison φ).hom.1)
          (forget AddCommGrpCat.{max u v})).app
            (Opposite.op (Over.mk (𝟙 V))) ≫
        (forgetIso y).hom.app (Opposite.op (Over.mk (𝟙 V))) ≫
        (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 V))) := by
          symm
          exact
            absolute_glueing_reconstruction_restriction_map_after_lifted_terminal_common_owner
              (𝒮 := 𝒮) hAbelian F comparison hcomparison
              lifted forgetIso liftedComparison liftedCompatibility f φ

/-- Helper for Lemma 8.11.8: after freezing the terminal object `V / V`, equality of two
candidate reconstructed sections can be descended from any cover of that terminal object in the
slice site `C / V`. This is the source-faithful fixed-section descent step that should be used
before extracting an equality of restriction maps. -/
private theorem reconstructed_terminal_section_eq_of_cover
    {V : C} (ℱ : Sheaf (J.over V) (Type (max u v)))
    (R : (J.over V).Cover (Over.mk (𝟙 V)))
    (s s' : ℱ.1.obj (op (Over.mk (𝟙 V))))
    (hss : ∀ I : R.Arrow, ℱ.1.map I.f.op s = ℱ.1.map I.f.op s') :
    s = s' := by
  -- Freeze the terminal section and descend equality from the chosen slice cover of `V / V`.
  exact
    sections_eq_of_cover_on_slice (J := J) ℱ (Over.mk (𝟙 V)) R s s' hss

/-- Helper for Lemma 8.11.8: once the input section on `V / V` is fixed, equality of two
candidate restriction maps can be descended from a cover of that terminal object. This is the
map-level wrapper around `reconstructed_terminal_section_eq_of_cover` used by the final additive
restriction-map check. -/
private theorem reconstructed_terminal_map_eq_of_cover
    {V : C} {ℱ 𝒢 : Sheaf (J.over V) (Type (max u v))}
    (R : (J.over V).Cover (Over.mk (𝟙 V)))
    (f g : ℱ.1.obj (op (Over.mk (𝟙 V))) → 𝒢.1.obj (op (Over.mk (𝟙 V))))
    (hfg : ∀ I : R.Arrow, ∀ α : ℱ.1.obj (op (Over.mk (𝟙 V))),
      𝒢.1.map I.f.op (f α) = 𝒢.1.map I.f.op (g α)) :
    f = g := by
  -- Freeze the input section first, then descend the resulting section equality from the cover.
  exact
    section_map_eq_of_cover_on_slice (J := J)
      (T := op (Over.mk (𝟙 V))) R f g hfg

/-- Helper for Lemma 8.11.8: once a restriction map on terminal sections is known to preserve
addition, package it as the corresponding morphism in `AddCommGrpCat`. This keeps the final
reconstruction record free of inline proof terms. -/
private noncomputable def terminal_section_add_hom_of_map_add
    {A B : AddCommGrpCat.{max u v}} (f : A → B)
    (hf : ∀ a b, f (a + b) = f a + f b) :
    A ⟶ B :=
  AddCommGrpCat.ofHom <| AddMonoidHom.mk' f hf

/-- Helper for Lemma 8.11.8: once the chosen-cover slice comparisons and their slicewise additive
lifts are fixed, the only remaining work is to transport that data through the Chapter 7
absolute-glueing reconstruction and prove the global restriction maps preserve addition. -/
private theorem reconstructed_addcomm_sheaf_from_absolute_glueing_data
    (hGerbe : IsGerbe J 𝒮.p)
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
    (hforgetConj :
      ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
        Functor.whiskerRight
            ((liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
            (forget AddCommGrpCat.{max u v}) =
          (forgetIso x).hom ≫ (comparison y).hom.1) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison' : ∀ {U : C} (x : 𝒮.p.Fiber U),
          G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison' x ≪≫ automorphismAddCommSheafConj hAbelian φ = comparison' y := by
  let _ := hcomparison
  let _ := lifted
  let _ := forgetIso
  let _ := liftedComparison
  let _ := liftedCompatibility
  let _ := hforgetConj
  -- Route correction: the additive reconstruction must stay on the source gerbe route. The
  -- previous fully general helper shape hid the need for the chosen-cover local objects provided
  -- by `hGerbe`, so the remaining transport proof is now explicitly localized to that setting.
  -- TODO: the comparison side is now normalized by
  -- `reconstructed_over_to_lifted_terminal_app_then_comparison`,
  -- `reconstructed_over_to_lifted_terminal_app_then_conj`,
  -- `absolute_glueing_reconstruction_restriction_map_after_lifted_terminal_comparison`, and
  -- `absolute_glueing_reconstruction_restriction_map_after_lifted_terminal_conj`. The new
  -- theorem
  -- `absolute_glueing_reconstruction_restriction_map_lifted_terminal_conj_eq_common_owner`
  -- also collapses the transported conjugation branch to the fixed-owner common-owner branch
  -- before any cover descent. The remaining source-faithful blocker is now only the chosen-cover
  -- descent step: prove equality on each member of the target-side common refinement cover via
  -- `slice_addcomm_lifted_common_owner_iso_terminal_app_forget_to_comparison`, then descend that
  -- terminal-component equality to an equality of section maps with
  -- `reconstructed_terminal_map_eq_of_cover`, and finally package the additive restriction map
  -- by `terminal_section_add_hom_of_map_add`.
  sorry

/-- Helper for Lemma 8.11.8: once the chosen-cover slice comparisons and their slicewise additive
lifts are fixed, the only remaining work is to transport that data through the Chapter 7
absolute-glueing reconstruction and prove the global restriction maps preserve addition. -/
private theorem reconstruct_addcomm_sheaf_from_chosen_cover_slices
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison' : ∀ {U : C} (x : 𝒮.p.Fiber U),
          G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison' x ≪≫ automorphismAddCommSheafConj hAbelian φ = comparison' y := by
  obtain ⟨F, comparison, hcomparison⟩ :=
    exists_underlying_automorphism_absolute_glueing
      (𝒮 := 𝒮) hGerbe hAbelian
  obtain ⟨lifted, forgetIso, liftedComparison, liftedCompatibility⟩ :=
    -- The local additive lifts should be built from the actual absolute-glueing owner `F.obj U`,
    -- not from an auxiliary chosen-cover family. This matches the Chapter 7 reconstruction route.
    slice_addcomm_lifts_of_absolute_glueing_comparison
      (𝒮 := 𝒮) hAbelian F comparison
  have hforgetConj :
      ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
        Functor.whiskerRight
            ((liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
            (forget AddCommGrpCat.{max u v}) =
          (forgetIso x).hom ≫ (comparison y).hom.1 := by
    intro U x y φ
    -- Forgetting the lifted comparison composite lands exactly on the underlying absolute-glueing
    -- comparison prescribed by `hcomparison`.
    exact
      slice_addcomm_lifted_comparison_forget_conj
        (𝒮 := 𝒮) hAbelian F comparison hcomparison
        lifted forgetIso liftedComparison liftedCompatibility φ
  let _ := F
  let _ := comparison
  let _ := hcomparison
  let _ := lifted
  let _ := forgetIso
  let _ := liftedComparison
  let _ := liftedCompatibility
  let _ := hforgetConj
  -- The remaining absolute-glueing reconstruction step is now isolated in one helper whose
  -- hypotheses are exactly the fixed underlying owner `F` and the slicewise additive lifts above.
  exact
    reconstructed_addcomm_sheaf_from_absolute_glueing_data
      (𝒮 := 𝒮) hGerbe hAbelian F comparison hcomparison
      lifted forgetIso liftedComparison liftedCompatibility hforgetConj

/-- Helper for Lemma 8.11.8: once the underlying absolute glueing is fixed, the remaining work is
to reconstruct a global `AddCommGrpCat`-valued sheaf whose localized restrictions are the local
abelian automorphism sheaves. -/
private theorem absolute_glueing_reconstruction_has_addcomm_structure
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hcomparison : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ = comparison y) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison' : ∀ {U : C} (x : 𝒮.p.Fiber U),
          G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison' x ≪≫ automorphismAddCommSheafConj hAbelian φ = comparison' y := by
  -- Route correction: abandon the arbitrary-`F` additive packaging route. The remaining blocker
  -- is the chosen-cover-specific global reconstruction isolated in
  -- `reconstruct_addcomm_sheaf_from_chosen_cover_slices`.
  let _ := F
  let _ := comparison
  let _ := hcomparison
  exact
    reconstruct_addcomm_sheaf_from_chosen_cover_slices
      (𝒮 := 𝒮) hGerbe hAbelian

/-- Helper for Lemma 8.11.8: once the underlying absolute glueing is fixed, the remaining work is
to reconstruct a global `AddCommGrpCat`-valued sheaf whose localized restrictions are the local
abelian automorphism sheaves. -/
private theorem reconstruct_addcomm_sheaf_from_underlying_band
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hcomparison : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ = comparison y) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison' : ∀ {U : C} (x : 𝒮.p.Fiber U),
          G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison' x ≪≫ automorphismAddCommSheafConj hAbelian φ = comparison' y := by
  -- Route correction: the old statement omitted any local-inhabited hypothesis, but transporting
  -- the additive structure from automorphism sheaves needs local objects on a cover of each `U`.
  -- The gerbe hypothesis supplies exactly that source-faithful local input.
  exact
    absolute_glueing_reconstruction_has_addcomm_structure
      (𝒮 := 𝒮) hGerbe hAbelian F comparison hcomparison

/-- Helper for Lemma 8.11.8: once the absolute glueing of underlying automorphism sheaves exists,
transport the slice-wise additive structures through reconstruction to obtain the final abelian
band. -/
private theorem underlying_absolute_glueing_to_addcomm_band
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hcomparison : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ = comparison y) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G := by
  -- First reconstruct the `AddCommGrpCat`-valued sheaf together with its local comparisons; the
  -- remaining goal is then only the definitional packaging into `IsGerbeBand`.
  obtain ⟨G, comparison', hcomparison'⟩ :=
    reconstruct_addcomm_sheaf_from_underlying_band
      (𝒮 := 𝒮) hGerbe hAbelian F comparison hcomparison
  exact ⟨G, ⟨comparison', hcomparison'⟩⟩

-- Proof sketch: first use that in a gerbe any two local objects become locally isomorphic; since
-- the automorphism sheaves are abelian, conjugation is independent of the chosen local
-- isomorphism, so these local automorphism sheaves glue canonically on overlaps. Then use the
-- gluing lemmas for sheaves on the site and on its localizations to descend the resulting local
-- systems to a single global sheaf of abelian groups whose restriction to each `C/U` identifies
-- with the corresponding automorphism sheaf.
/-- Lemma 8.11.8: if `𝒮` is a gerbe over the site `(C, J)` and every automorphism sheaf
`Aut[𝒮](x)` is canonically abelian for its native composition law, then there exists a sheaf `𝒢`
of abelian groups on `C` whose restriction to each localized site `C/U` is identified with
the canonical abelian-group automorphism sheaf attached to `x`, compatibly with conjugation by
morphisms in the fiber over `U`. -/
theorem exists_gerbe_band_of_abelian_automorphism_sheaves
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G := by
  -- Route correction: the main theorem now delegates to the two remaining source-faithful
  -- structural steps. First construct the absolute glueing of descended slice automorphism
  -- sheaves; then transport their additive structures back to a global abelian band.
  obtain ⟨F, comparison, hcomparison⟩ :=
    exists_underlying_automorphism_absolute_glueing
      (𝒮 := 𝒮) hGerbe hAbelian
  exact
    underlying_absolute_glueing_to_addcomm_band
      (𝒮 := 𝒮) hGerbe hAbelian F comparison hcomparison

end CategoryTheory
