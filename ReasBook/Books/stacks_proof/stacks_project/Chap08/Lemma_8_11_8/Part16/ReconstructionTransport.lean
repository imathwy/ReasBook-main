import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part16.CommonOwnerForget
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part16.UnderlyingAbsoluteGlueingBand

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Lemma 8.11.8 Part16: snake-case compatibility alias for the public Chapter 7
absolute-glueing reconstruction API used by earlier extracted support code. -/
noncomputable abbrev absolute_glueing_reconstruction
    (F : GrothendieckTopology.AbsoluteGlueing J) :
    Sheaf J (Type (max u v)) :=
  absoluteGlueingReconstruction (J := J) F

/-- Helper for Lemma 8.11.8 Part16: snake-case compatibility alias for the local reconstruction
comparison on a slice. -/
noncomputable abbrev absolute_glueing_reconstruction_over_iso
    (F : GrothendieckTopology.AbsoluteGlueing J) (U : C) :
    (absolute_glueing_reconstruction (J := J) F).over U ≅ F.obj U :=
  absoluteGlueingReconstructionOverIso (J := J) F U

/-- Helper for Lemma 8.11.8: once the underlying absolute glueing is fixed, the remaining work is
to reconstruct a global `AddCommGrpCat`-valued sheaf whose localized restrictions are the local
abelian automorphism sheaves. -/
theorem reconstructed_slice_addcomm_sheaf
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
theorem reconstructed_over_to_lifted_underlying_hom_inv_id
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
theorem reconstructed_over_to_lifted_underlying_inv_hom_id
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
noncomputable def reconstructed_over_to_lifted_underlying_iso
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
theorem reconstructed_over_to_lifted_then_comparison
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
  rfl

/-- Helper for Lemma 8.11.8: evaluating the reconstructed-to-lifted comparison at the terminal
object of `C / U` gives the explicit section-level owner comparison needed in the remaining
restriction-map additivity descent. -/
theorem reconstructed_over_to_lifted_terminal_app_then_comparison
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
theorem reconstructed_over_to_lifted_then_conj
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
  rfl

/-- Helper for Lemma 8.11.8: evaluating the reconstructed-to-lifted comparison followed by
conjugation at the terminal object of `C / U` exposes the exact section-level owner comparison
to the target automorphism sheaf. -/
theorem reconstructed_over_to_lifted_terminal_app_then_conj
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
theorem absolute_glueing_reconstruction_restriction_map_after_lifted_terminal_comparison
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
  have hstep :
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
  have hlocal :
      (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
        ((absolute_glueing_reconstruction_over_iso (J := J) F V).hom.1.app
          (Opposite.op (Over.mk (𝟙 V)))) ≫
        (comparison x).hom.1.app (Opposite.op (Over.mk (𝟙 V))) =
      ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
        (Opposite.op (Over.mk (𝟙 U)))) ≫
        GrothendieckTopology.absoluteGlueingToPresheafMap J F f ≫
        (comparison x).hom.1.app (Opposite.op (Over.mk (𝟙 V))) := by
    simpa [absolute_glueing_reconstruction, absolute_glueing_reconstruction_over_iso,
      absoluteGlueingReconstruction, absoluteGlueingReconstructionOverIso,
      Category.assoc] using
      absolute_glueing_reconstruction_restriction_map_after_local_comparison
        (𝒮 := 𝒮) (J := J) hAbelian F comparison (f := f) x
  exact hstep.trans hlocal

/-- Helper for Lemma 8.11.8: after the Chapter 7 reconstruction transport is normalized on the
source slice `C / V`, postcomposing with the terminal component of the lifted comparison followed
by conjugation lands on the fixed-owner target comparison. -/
theorem absolute_glueing_reconstruction_restriction_map_after_lifted_terminal_conj
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
  have hstep :
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
  have hlocal :
      (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
        ((absolute_glueing_reconstruction_over_iso (J := J) F V).hom.1.app
          (Opposite.op (Over.mk (𝟙 V)))) ≫
        (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 V))) =
      ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
        (Opposite.op (Over.mk (𝟙 U)))) ≫
        GrothendieckTopology.absoluteGlueingToPresheafMap J F f ≫
        (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 V))) := by
    simpa [absolute_glueing_reconstruction, absolute_glueing_reconstruction_over_iso,
      absoluteGlueingReconstruction, absoluteGlueingReconstructionOverIso,
      Category.assoc] using
      absolute_glueing_reconstruction_restriction_map_after_local_comparison
        (𝒮 := 𝒮) (J := J) hAbelian F comparison (f := f) y
  exact hstep.trans hlocal

/-- Helper for Lemma 8.11.8: after replacing the target-side lifted comparison by the fixed-owner
common-owner comparison on `lifted x`, the reconstructed restriction map still lands on the same
owner-level terminal composite. This pins the remaining blocker to the chosen-cover descent step
instead of the already-solved transport corridor. -/
theorem absolute_glueing_reconstruction_restriction_map_after_lifted_terminal_common_owner
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
          let TV : (Over V)ᵒᵖ := Opposite.op (Over.mk (𝟙 V))
          have hcancel :
              (forgetIso x).inv.app TV ≫ (forgetIso x).hom.app TV =
                𝟙 ((F.obj V).1.obj TV) := by
            exact Iso.inv_hom_id_app (forgetIso x) TV
          change
            (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
                ((absolute_glueing_reconstruction_over_iso (J := J) F V).hom.1.app TV) ≫
                (forgetIso x).inv.app TV ≫
                (forgetIso x).hom.app TV ≫
                (comparison y).hom.1.app TV =
              (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
                ((absolute_glueing_reconstruction_over_iso (J := J) F V).hom.1.app TV) ≫
                (comparison y).hom.1.app TV
          rw [← Category.assoc ((forgetIso x).inv.app TV) ((forgetIso x).hom.app TV)
            ((comparison y).hom.1.app TV), hcancel]
          simp
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
theorem absolute_glueing_reconstruction_restriction_map_lifted_terminal_conj_eq_common_owner
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
  have hleft :
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
  have hright :
      ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
        (Opposite.op (Over.mk (𝟙 U)))) ≫
        GrothendieckTopology.absoluteGlueingToPresheafMap J F f ≫
        (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 V))) =
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
    simpa [absolute_glueing_reconstruction, absolute_glueing_reconstruction_over_iso,
      absoluteGlueingReconstruction, absoluteGlueingReconstructionOverIso,
      reconstructed_over_to_lifted_underlying_iso, Category.assoc] using
      absolute_glueing_reconstruction_restriction_map_after_lifted_terminal_common_owner
        (𝒮 := 𝒮) hAbelian F comparison hcomparison
        lifted forgetIso liftedComparison liftedCompatibility f φ
  exact hleft.trans hright

end CategoryTheory
