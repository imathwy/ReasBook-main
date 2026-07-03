import Mathlib
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall
import «StacksProject_2024».«Chap04».«4_27_7_1»
import «StacksProject_2024».«Chap04».«Lemma_4_19_2»

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_4_27_10 (from Chap04) -/
universe v u

namespace CategoryTheory

open MorphismProperty
open LeftFraction
open LeftFraction.Localization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
variable {D : Type*} [Category D]
variable {X X' Y Y' : C}

local notation "Q" => LeftFraction.Localization.Q

/- Domain-style sampling for Lemma 4.27.10:
- primary domain: left-fraction localizations and commutative-square lifting;
- inspected owner declarations:
  `Functor.IsLocalization`,
  `MorphismProperty.LeftFraction.map_comp_map_eq_map`,
  `Localization.exists_leftFraction`,
  `MorphismProperty.map_eq_iff_postcomp`;
- best owner abstraction: an ambient localization functor `L` with `[L.IsLocalization W]`,
  together with `W.LeftFraction` for the primitive roof data representing the vertical localization
  morphisms; `homMk` is only the canonical-model bridge for `Q W`.

Primitive data: the two roof representatives `aFrac : W.LeftFraction X X'` and
`bFrac : W.LeftFraction Y Y'`.
Derived API: their represented morphisms `aFrac.map L (Localization.inverts L W)` and
  `bFrac.map L (Localization.inverts L W)` in an arbitrary localization; for `L = Q W` these
  become `homMk aFrac` and `homMk bFrac`.

Source/core/bridge triage:
- `source-facing`: `commutative_square_lifts_to_left_fraction_square`;
- `core/canonical`: `localization_commutative_square_has_left_fraction_lift`,
  `Functor.IsLocalization`, `W.LeftFraction`, and `LeftFraction.map`;
- `bridge/view`: specialization from `LeftFraction.map` to `homMk` for `Q W`, and the
  equation-form companion `commutative_square_lifts_to_left_fraction_square_eq`. -/

private theorem leftFraction_map_postcomp_eq (L : C ⥤ D) [L.IsLocalization W]
    {X Y : C} (φ : W.LeftFraction X Y)
    {Z : C} (t : φ.Y' ⟶ Z) (ht : W (φ.s ≫ t)) :
    φ.map L (Localization.inverts L W) =
      (LeftFraction.mk (φ.f ≫ t) (φ.s ≫ t) ht).map L (Localization.inverts L W) := by
  exact (MorphismProperty.LeftFraction.map_eq_iff L W φ
    (LeftFraction.mk (φ.f ≫ t) (φ.s ≫ t) ht)).2 ⟨Z, t, 𝟙 _, by simp, by simp, ht⟩

-- Proof sketch: represent `a` by a left fraction with denominator in `W`; use the
-- left-calculus square-completion axiom to compare it with `f'`; refine the target of `f''` so
-- that `b` is also represented by such a fraction; then compare the two composites in the
-- localization, cancel the common denominator, and apply `map_eq_iff_postcomp` to force the left
-- square to commute after one more refinement.
/-- A commutative square in a localization can be represented by a commutative diagram in `C`
whose vertical arrows are denominators in `W`. -/
theorem localization_commutative_square_has_left_fraction_lift
    (L : C ⥤ D) [L.IsLocalization W]
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : L.obj X ⟶ L.obj X')
    (b : L.obj Y ⟶ L.obj Y')
    (hcomm : CommSq (L.map f) a b (L.map f')) :
    ∃ (aFrac : {φ : W.LeftFraction X X' //
          a = φ.map L (Localization.inverts L W)})
      (bFrac : {φ : W.LeftFraction Y Y' //
          b = φ.map L (Localization.inverts L W)})
      (f'' : aFrac.val.Y' ⟶ bFrac.val.Y'),
        CommSq f aFrac.val.f bFrac.val.f f'' ∧
          CommSq f' aFrac.val.s bFrac.val.s f'' := by
  obtain ⟨aFrac, ha⟩ := Localization.exists_leftFraction L W a
  obtain ⟨b₀, hb₀⟩ := Localization.exists_leftFraction L W b
  let cFrac : W.LeftFraction aFrac.Y' Y' :=
    RightFraction.leftFraction (RightFraction.mk aFrac.s aFrac.hs f')
  have hc : f' ≫ cFrac.s = aFrac.s ≫ cFrac.f := by
    simpa [cFrac] using
      (RightFraction.leftFraction_fac (RightFraction.mk aFrac.s aFrac.hs f'))
  let dFrac : W.LeftFraction cFrac.Y' b₀.Y' :=
    RightFraction.leftFraction (RightFraction.mk cFrac.s cFrac.hs b₀.s)
  have hd : b₀.s ≫ dFrac.s = cFrac.s ≫ dFrac.f := by
    simpa [dFrac] using
      (RightFraction.leftFraction_fac (RightFraction.mk cFrac.s cFrac.hs b₀.s))
  have hcommon : W (cFrac.s ≫ dFrac.f) := by
    simpa [hd] using W.comp_mem _ _ b₀.hs dFrac.hs
  let bRef : W.LeftFraction Y Y' :=
    LeftFraction.mk (b₀.f ≫ dFrac.s) (cFrac.s ≫ dFrac.f) hcommon
  let aRef : W.LeftFraction X Y' :=
    LeftFraction.mk (aFrac.f ≫ cFrac.f ≫ dFrac.f) (cFrac.s ≫ dFrac.f) hcommon
  have hbRef : b = bRef.map L (Localization.inverts L W) := by
    calc
      b = b₀.map L (Localization.inverts L W) := hb₀
      _ = bRef.map L (Localization.inverts L W) := by
        exact (MorphismProperty.LeftFraction.map_eq_iff L W b₀ bRef).2
          ⟨dFrac.Y', dFrac.s, 𝟙 _, by simpa [bRef, Category.assoc] using hd, by simp [bRef],
            by simpa using W.comp_mem _ _ b₀.hs dFrac.hs⟩
  have haRef : a ≫ L.map f' = aRef.map L (Localization.inverts L W) := by
    calc
      a ≫ L.map f' = aFrac.map L (Localization.inverts L W) ≫ L.map f' := by
        simpa using congrArg (fun k ↦ k ≫ L.map f') ha
      _ = (LeftFraction.mk (aFrac.f ≫ cFrac.f) cFrac.s cFrac.hs).map L
          (Localization.inverts L W) := by
        simpa [cFrac, LeftFraction.comp₀, MorphismProperty.LeftFraction.map_ofHom] using
          MorphismProperty.LeftFraction.map_comp_map_eq_map aFrac (ofHom W f') cFrac hc L
      _ = aRef.map L (Localization.inverts L W) := by
        simpa [aRef, Category.assoc] using leftFraction_map_postcomp_eq W L
          (LeftFraction.mk (aFrac.f ≫ cFrac.f) cFrac.s cFrac.hs) dFrac.f hcommon
  have hEq :
      (LeftFraction.mk (f ≫ bRef.f) bRef.s bRef.hs).map L (Localization.inverts L W) =
        aRef.map L (Localization.inverts L W) := by
    calc
      (LeftFraction.mk (f ≫ bRef.f) bRef.s bRef.hs).map L (Localization.inverts L W) =
          L.map f ≫ bRef.map L (Localization.inverts L W) := by
        symm
        simpa [LeftFraction.comp₀, MorphismProperty.LeftFraction.map_ofHom] using
          (MorphismProperty.LeftFraction.map_comp_map_eq_map (ofHom W f) bRef
            (ofHom W bRef.f) (by simp) L)
      _ = a ≫ L.map f' := by simpa [hbRef] using hcomm.w
      _ = aRef.map L (Localization.inverts L W) := haRef
  have hEq' :
      (LeftFraction.mk (f ≫ bRef.f) aRef.s aRef.hs).map L (Localization.inverts L W) =
        (LeftFraction.mk aRef.f aRef.s aRef.hs).map L (Localization.inverts L W) := by
    simpa [aRef, bRef] using hEq
  have hmap : L.map (f ≫ bRef.f) = L.map aRef.f := by
    simpa using congrArg (fun k ↦ k ≫ L.map aRef.s) hEq'
  obtain ⟨Z, u, hu, hnum⟩ := (map_eq_iff_postcomp L W (f ≫ bRef.f) aRef.f).mp hmap
  let bFrac : W.LeftFraction Y Y' :=
    LeftFraction.mk (bRef.f ≫ u) (bRef.s ≫ u) (W.comp_mem _ _ bRef.hs hu)
  let f'' : aFrac.Y' ⟶ bFrac.Y' := cFrac.f ≫ dFrac.f ≫ u
  refine ⟨⟨aFrac, ha⟩, ⟨bFrac, ?_⟩, f'', ?_, ?_⟩
  · calc
      b = bRef.map L (Localization.inverts L W) := hbRef
      _ = bFrac.map L (Localization.inverts L W) := by
        dsimp [bFrac]
        simpa [Category.assoc] using leftFraction_map_postcomp_eq W L bRef u
          (W.comp_mem _ _ bRef.hs hu)
  · refine ⟨?_⟩
    dsimp [bFrac, bRef, aRef, f''] at hnum ⊢
    simpa [Category.assoc] using hnum
  · refine ⟨?_⟩
    dsimp [bFrac, bRef, f'']
    calc
      f' ≫ ((cFrac.s ≫ dFrac.f) ≫ u) = (f' ≫ cFrac.s) ≫ dFrac.f ≫ u := by
        simp [Category.assoc]
      _ = (aFrac.s ≫ cFrac.f) ≫ dFrac.f ≫ u := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ dFrac.f ≫ u) hc
      _ = aFrac.s ≫ (cFrac.f ≫ dFrac.f ≫ u) := by simp [Category.assoc]

/-- Lemma 4.27.10: a commutative square in the left-fraction localization can be represented by a
commutative diagram in `C` whose vertical arrows are denominators in `W`. -/
theorem commutative_square_lifts_to_left_fraction_square
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : (Q W).obj X ⟶ (Q W).obj X')
    (b : (Q W).obj Y ⟶ (Q W).obj Y')
    (hcomm :
      CommSq ((Q W).map f) a b
        ((Q W).map f')) :
    ∃ (aFrac : {φ : W.LeftFraction X X' // a = homMk φ})
      (bFrac : {φ : W.LeftFraction Y Y' // b = homMk φ})
      (f'' : aFrac.val.Y' ⟶ bFrac.val.Y'),
        CommSq f aFrac.val.f bFrac.val.f f'' ∧
          CommSq f' aFrac.val.s bFrac.val.s f'' := by
  obtain ⟨aFrac, bFrac, f'', hleft, hright⟩ :=
    localization_commutative_square_has_left_fraction_lift W (Q W) f f' a b hcomm
  refine ⟨⟨aFrac.val, ?_⟩, ⟨bFrac.val, ?_⟩, f'', hleft, hright⟩
  · simpa [LeftFraction.Localization.homMk_eq] using aFrac.property
  · simpa [LeftFraction.Localization.homMk_eq] using bFrac.property

/-- Companion to Lemma 4.27.10 in equation form. -/
theorem commutative_square_lifts_to_left_fraction_square_eq
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : (Q W).obj X ⟶ (Q W).obj X')
    (b : (Q W).obj Y ⟶ (Q W).obj Y')
    (hcomm :
      (Q W).map f ≫ b =
        a ≫ (Q W).map f') :
    ∃ (aFrac : {φ : W.LeftFraction X X' // a = homMk φ})
      (bFrac : {φ : W.LeftFraction Y Y' // b = homMk φ})
      (f'' : aFrac.val.Y' ⟶ bFrac.val.Y'),
        f ≫ bFrac.val.f = aFrac.val.f ≫ f'' ∧
          aFrac.val.s ≫ f'' = f' ≫ bFrac.val.s := by
  obtain ⟨aFrac, bFrac, f'', hleft, hright⟩ :=
    commutative_square_lifts_to_left_fraction_square W f f' a b ⟨hcomm⟩
  exact ⟨aFrac, bFrac, f'', hleft.w, hright.w.symm⟩

end CategoryTheory

/-! ### Lemma_4_27_11 (from Chap04) -/
universe v u

namespace CategoryTheory

open MorphismProperty
open MorphismProperty.RightFraction

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
variable {X Y Z : C}

/- Domain-style sampling for Lemma 4.27.11:
- source-facing content: the equivalence relation on right fractions and the fact that composition
  of represented morphisms depends only on equivalence classes
- core/canonical owner abstraction: `MorphismProperty.RightFractionRel` together with the induced
  morphism `RightFraction.map : W.RightFraction X Y → W.Q.obj X ⟶ W.Q.obj Y`
- upstream owner facts inspected before refining:
  `MorphismProperty.equivalenceRightFractionRel`,
  `RightFraction.map_eq_iff`,
  `Category.assoc`

Primitive data: a pair of right fractions and proofs that they are related by
`RightFractionRel`.
Derived API: the induced localization morphism `RightFraction.map` and equality of such morphisms
coming from `RightFraction.map_eq_iff`. Unlike the concrete left-fraction model, the right-fraction
side has no separate localization owner like `homMk`, so the source-facing well-definedness
statement should use `RightFraction.map` itself directly, without introducing a parallel local
wrapper.

Source/core/bridge triage:
- `source-facing`: `rightFractionComp_wellDefined`;
- `core/canonical`: `RightFractionRel`, `equivalenceRightFractionRel`, and `RightFraction.map`;
- `bridge/view`: the passage from equivalence-class representatives to equality after composition.
-/

/- Lemma 4.27.11(1): the canonical relation `RightFractionRel` on right fractions is the mathlib
relation `CategoryTheory.MorphismProperty.RightFractionRel`, and its equivalence-relation
statement is exactly `CategoryTheory.MorphismProperty.equivalenceRightFractionRel`. -/
recall MorphismProperty.equivalenceRightFractionRel

-- Proof sketch: rewrite both hypotheses with the canonical theorem
-- `MorphismProperty.RightFraction.map_eq_iff`, replace the two pairs of maps by equal morphisms
-- in `W.Localization`, and then use congruence of composition.
/-- Lemma 4.27.11, well-definedness clause: composition of represented right fractions depends only
on their equivalence classes. -/
theorem rightFractionComp_wellDefined
    (φ φ' : W.RightFraction X Y) (ψ ψ' : W.RightFraction Y Z)
    (hφ : RightFractionRel φ φ') (hψ : RightFractionRel ψ ψ') :
    φ.map W.Q (Localization.inverts _ _) ≫ ψ.map W.Q (Localization.inverts _ _) =
      φ'.map W.Q (Localization.inverts _ _) ≫ ψ'.map W.Q (Localization.inverts _ _) := by
  simpa using congrArg₂ (· ≫ ·) (map_eq_iff W.Q W φ φ' |>.2 hφ) (map_eq_iff W.Q W ψ ψ' |>.2 hψ)

/- Lemma 4.27.11(3): composition in the right-fraction localization is associative; this is the
canonical associativity axiom `CategoryTheory.Category.assoc` in `W.Localization`. -/
recall Category.assoc

/- Lemma 4.27.11(3): the identity morphism is a left unit for composition in
`W.Localization`; this is the canonical axiom `CategoryTheory.Category.id_comp`. -/
recall Category.id_comp

/- Lemma 4.27.11(3): the identity morphism is a right unit for composition in
`W.Localization`; this is the canonical axiom `CategoryTheory.Category.comp_id`. -/
recall Category.comp_id

end CategoryTheory

/-! ### Definition_4_27_12 (from Chap04) -/
universe v u

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]
variable (S : MorphismProperty C)

/- Domain-style sampling for Definition 4.27.12:
- primary domain: right calculus of fractions and the morphism in the localization represented by
  a roof;
- inspected owner declarations:
  `MorphismProperty.RightFraction`,
  `RightFraction.map`,
  `RightFraction.map_eq_iff`,
  `Localization.exists_rightFraction`;
- best owner abstraction: the represented morphism already lives at the canonical owner
  `RightFraction.map`.

Primitive-vs-derived split:
- primitive data: a right fraction `φ : S.RightFraction X Y`;
- derived API: the induced localization morphism `φ.map S.Q (Localization.inverts _ _)`, with
  equality controlled by `RightFraction.map_eq_iff`.

Source/core/bridge triage:
- `source-facing`: the roof `φ : S.RightFraction X Y`;
- `core/canonical`: `RightFraction.map`;
- `bridge/view`: the textbook description of the represented morphism as the composite `f s⁻¹`.

Definition 4.27.12 is therefore a `core/canonical` recall item, so this file reuses
`RightFraction.map` directly and keeps no parallel local wrapper theorem.
-/
/- Definition 4.27.12: for a morphism `f : X' ⟶ Y` and a denominator `s : X' ⟶ X` in `S`, the
roof `(f, s)` represents the canonical localization morphism from `X` to `Y`. Specialized to the
localization functor `S.Q`, this is exactly the morphism of `S⁻¹ C` denoted in the text by
`f s⁻¹`. -/
recall RightFraction.map

end MorphismProperty
end CategoryTheory

/-! ### Lemma_4_27_13 (from Chap04) -/
open CategoryTheory
open MorphismProperty
open MorphismProperty.RightFraction
open Opposite
open Localization

universe u v w w'

namespace CategoryTheory
namespace Localization

variable {C : Type u} {D : Type w'} [Category.{v} C] [Category D]
variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
variable [W.HasRightCalculusOfFractions]

/- Domain-style sampling for Lemma 4.27.13:
- primary domain: localization by a right calculus of fractions;
- inspected owner declarations:
  `RightFraction.map`,
  `Localization.exists_leftFraction_finite`,
  `LeftFraction.unop`,
  `RightFraction.op_map`;
- best owner abstraction: `MorphismProperty.RightFraction` together with the canonical map
  `RightFraction.map`, which is the owner-level realization of a roof in the localization;
- primitive data: a common denominator `s : X' ⟶ X` in `W` and numerators `f i : X' ⟶ Y i`;
- derived API: the represented morphisms in the localization, obtained here by transporting the
  finite left-fraction theorem across the opposite-category bridge `LeftFraction.unop`.

Source/core/bridge triage:
- `source-facing`: `exists_rightFraction_finite`;
- `core/canonical`: the owner-level right-fraction localization API above;
- `bridge/view`: passage to the opposite category, followed by the canonical owner bridge
  `LeftFraction.unop`, where the finite common-denominator statement is already canonical as
  `exists_leftFraction_finite`. -/

-- Proof sketch: apply the finite left-fraction theorem in the opposite category, then unop the
-- resulting common denominator and numerators.
omit [W.HasRightCalculusOfFractions] in
/-- Helper for Lemma 4.27.13: mapping the `unop` of an opposite-category left fraction is
compatible with taking opposites of the original left-fraction map. -/
lemma right_fraction_map_opposite_bridge {X Y : Cᵒᵖ} (φ : W.op.LeftFraction X Y) :
    (φ.unop.map L (inverts L W)).op = φ.map L.op (inverts L.op W.op) := by
  -- This is the canonical `op`/`unop` transport for fraction representatives.
  simpa using φ.unop.op_map L (inverts L W)

/-- Lemma 4.27.13: a finite family of morphisms in a localization with common source admits
representatives by right fractions with a single common denominator in `W`. -/
theorem exists_rightFraction_finite {ι : Type w} [Finite ι] {X : C} {Y : ι → C}
    (g : ∀ i, L.obj X ⟶ L.obj (Y i)) :
    ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : ∀ i, X' ⟶ Y i),
      ∀ i, g i = (RightFraction.mk s hs (f i)).map L (inverts L W) := by
  -- Move to the opposite category, where the statement is exactly the finite left-fraction lemma.
  obtain ⟨X'op, s, hs, f, hf⟩ := exists_leftFraction_finite L.op W.op fun i ↦ (g i).op
  refine ⟨unop X'op, s.unop, hs, fun i ↦ (f i).unop, ?_⟩
  intro i
  -- Compare the transported right fraction with the left fraction found on the opposite side.
  have hφ :
      ((RightFraction.mk s.unop hs (f i).unop).map L (inverts L W)).op =
        (LeftFraction.mk (f i) s hs).map L.op (inverts L.op W.op) :=
    right_fraction_map_opposite_bridge (L := L) (W := W) (LeftFraction.mk (f i) s hs)
  -- Injectivity of `op` transfers the opposite-side equality back to the original localization.
  exact Quiver.Hom.op_inj <| (hf i).trans hφ.symm

end Localization
end CategoryTheory

/-! ### Lemma_4_27_14 (from Chap04) -/
universe v u

namespace CategoryTheory

open MorphismProperty
open MorphismProperty.RightFraction
open Localization

variable {C : Type u} [Category.{v} C]
variable (S : MorphismProperty C) [S.HasRightCalculusOfFractions]
variable {X X' Y : C}

/- Domain-style sampling for Lemma 4.27.14:
- primary domain: localization by a right calculus of fractions, with right fractions as the
  concrete presentation of morphisms;
- core/canonical owner APIs sampled upstream:
  `RightFraction.map`,
  `RightFraction.map_eq_iff`,
  `MorphismProperty.map_eq_iff_precomp`,
  `RightFraction.map_ofHom`;
- source-facing content here: the fixed-denominator comparison criterion for two right fractions,
  together with its `TFAE` companion;
- primitive data: a morphism property `S`, a common denominator `s : X' ⟶ X` with `hs : S s`, and
  numerators `f g : X' ⟶ Y`;
- derived API: the represented morphisms in `S.Localization` and the two equivalent
  precomposition criteria.

The owner abstraction is the localization morphism represented by `RightFraction.map`, together
with the canonical equality criteria `RightFraction.map_eq_iff` and `map_eq_iff_precomp`. The
source-facing fixed-denominator criterion should therefore be public, while the auxiliary variant
with composite denominator in `S` is best derived first at the primitive owner relation
`RightFractionRel`, and only then passed to the localization-equality layer and the companion
`TFAE`.
-/
private theorem same_denominator_rightFractionRel_iff_exists_precomp_composite_in_S
    (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : S s) :
    RightFractionRel (RightFraction.mk s hs f) (RightFraction.mk s hs g) ↔
      ∃ (X'' : C) (a : X'' ⟶ X'), a ≫ f = a ≫ g ∧ S (a ≫ s) := by
  constructor
  · rintro ⟨Z, t₁, t₂, hst, hfg, ht⟩
    let hS : S.HasRightCalculusOfFractions := inferInstance
    obtain ⟨X'', a, ha, hta⟩ := hS.ext t₁ t₂ s hs hst
    refine ⟨X'', a ≫ t₁, ?_, ?_⟩
    · calc
        (a ≫ t₁) ≫ f = a ≫ (t₁ ≫ f) := by simp [Category.assoc]
        _ = a ≫ (t₂ ≫ g) := by
              simpa [Category.assoc] using congrArg (fun k ↦ a ≫ k) hfg
        _ = (a ≫ t₂) ≫ g := by simp [Category.assoc]
        _ = (a ≫ t₁) ≫ g := by
              simpa [Category.assoc] using congrArg (fun k ↦ k ≫ g) hta.symm
    · simpa [Category.assoc] using S.comp_mem _ _ ha ht

  · rintro ⟨X'', a, hag, has⟩
    exact ⟨X'', a, a, rfl, hag, has⟩

-- Proof sketch: cancel the common inverted denominator `(S.Q).map s` and apply the canonical
-- localization criterion `MorphismProperty.map_eq_iff_precomp` to the equality
-- `(S.Q).map f = (S.Q).map g`.
/-- Lemma 4.27.14 (1): for two right fractions with common denominator `s`, equality of the
induced morphisms in the localization is equivalent to the existence of a further denominator in
`S` equalizing the numerators. -/
theorem right_fraction_hom_eq_iff_exists_precomp
    (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : S s) :
    (RightFraction.mk s hs f).map S.Q (inverts _ _) =
        (RightFraction.mk s hs g).map S.Q (inverts _ _) ↔
      ∃ (X'' : C) (t : X'' ⟶ X'), S t ∧ t ≫ f = t ≫ g := by
  constructor
  · intro h
    have hfg : S.Q.map f = S.Q.map g := by
      simpa [RightFraction.map] using congrArg ((S.Q.map s) ≫ ·) h
    simpa using (map_eq_iff_precomp S.Q S f g).mp hfg
  · rintro ⟨X'', t, ht, htg⟩
    rw [map_eq_iff S.Q S]
    exact (same_denominator_rightFractionRel_iff_exists_precomp_composite_in_S S f g s hs).2
      ⟨X'', t, htg, S.comp_mem _ _ ht hs⟩

/-- Lemma 4.27.14 (2): for two right fractions with common denominator `s`, equality of the
induced morphisms in the localization is equivalent to the existence of a morphism whose
precomposition equalizes the numerators and whose composite with `s` lies in `S`. -/
theorem right_fraction_hom_eq_iff_exists_precomp_composite_in_S
    (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : S s) :
    (RightFraction.mk s hs f).map S.Q (inverts _ _) =
        (RightFraction.mk s hs g).map S.Q (inverts _ _) ↔
      ∃ (X'' : C) (a : X'' ⟶ X'), a ≫ f = a ≫ g ∧ S (a ≫ s) := by
  rw [map_eq_iff S.Q S]
  exact same_denominator_rightFractionRel_iff_exists_precomp_composite_in_S S f g s hs

end CategoryTheory

/-! ### Remark_4_27_15 (from Chap04) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.Types
open MorphismProperty
open MorphismProperty.RightFraction
open Localization
open Opposite

universe v u

namespace CategoryTheory
namespace MorphismProperty

scoped[MorphismPropertyOver] notation:80 S " / " X => MorphismProperty.Over S ⊤ X

open scoped MorphismPropertyOver

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Remark 4.27.15:
- primary domain: right calculus of fractions and localized Hom-sets;
- inspected owner-level declarations:
  `localizationTargetArrows_isFiltered`,
  `MorphismProperty.Over.forget`,
  `uliftYoneda.obj`,
  `Localization.exists_rightFraction`,
  `RightFraction.map_eq_iff`;
- best owner abstraction: the denominator category is already the canonical owner `S / X`,
  i.e. `MorphismProperty.Over S ⊤ X`; its cofilteredness is the opposite-category transport of
  `localizationTargetArrows_isFiltered`, and the Hom-diagram is obtained by pulling back
  `uliftYoneda.obj Y` along `(MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X).op`.

Primitive-vs-derived split:
- primitive data: the diagram on `(S / X)ᵒᵖ` and its canonical cocone into
  `Hom_{S^{-1}\mathcal C}(X, Y)`;
- derived API: cofilteredness of `S / X`, the `Type`-colimit witness, and the resulting colimit
  comparison isomorphism.

Source/core/bridge triage:
- `source-facing`: `right_localization_hom_colimit`;
- `core/canonical`: `uliftYoneda.obj Y`, `RightFraction.map`, and the `Type`-colimit owner map
  `F.descColimitType c`;
- `bridge/view`: the opposite-category equivalence identifying `S / X` with the left denominator
  category for `S.op`, together with the cocone from the denominator diagram to the localized
  Hom-set. -/

private def sourceArrowsOpEquivUnderOp (S : MorphismProperty C) (X : C) :
    MorphismProperty.Under S.op ⊤ (Opposite.op X) ≌ (S / X)ᵒᵖ where
  functor :=
    { obj := fun U ↦ Opposite.op <| Over.mk (⊤ : MorphismProperty C) U.hom.unop U.prop
      map := fun f ↦
        (Over.homMk f.right.unop
          (by simpa using congrArg Quiver.Hom.unop (Under.w f))).op }
  inverse :=
    { obj := fun U ↦
        let U' := U.unop
        Under.mk (⊤ : MorphismProperty Cᵒᵖ) U'.hom.op U'.prop
      map := fun f ↦
        let f' := f.unop
        Under.homMk f'.left.op
          (by simpa using congrArg Quiver.Hom.op (Over.w f')) }
  unitIso := NatIso.ofComponents
    (fun U ↦ Under.isoMk (Iso.refl _) (by
      change U.hom ≫ 𝟙 U.right = U.hom
      exact Category.comp_id U.hom))
    (by
      intro U V f
      ext
      change f.right ≫ 𝟙 V.right = 𝟙 U.right ≫ f.right
      calc
        f.right ≫ 𝟙 V.right = f.right := Category.comp_id f.right
        _ = 𝟙 U.right ≫ f.right := (Category.id_comp f.right).symm)
  counitIso := NatIso.ofComponents
    (fun U ↦ (Over.isoMk (Iso.refl _) (by
      change 𝟙 (Opposite.unop U).left ≫ (Opposite.unop U).hom = (Opposite.unop U).hom
      exact Category.id_comp (Opposite.unop U).hom)).op)
    (by
      intro U V f
      apply Quiver.Hom.unop_inj
      ext
      change 𝟙 (Opposite.unop V).left ≫ f.unop.left = f.unop.left ≫ 𝟙 (Opposite.unop U).left
      calc
        𝟙 (Opposite.unop V).left ≫ f.unop.left = f.unop.left := Category.id_comp f.unop.left
        _ = f.unop.left ≫ 𝟙 (Opposite.unop U).left := (Category.comp_id f.unop.left).symm)
  functor_unitIso_comp := by
    intro U
    apply Quiver.Hom.unop_inj
    ext
    change 𝟙 (Opposite.unop U.right) ≫ 𝟙 (Opposite.unop U.right) = 𝟙 (Opposite.unop U.right)
    simp

/-- The right-fraction over-category `S/X`, realized as the canonical comma category
`MorphismProperty.Over S ⊤ X`, is cofiltered. -/
-- Proof sketch: this is the right-handed dual of `localizationTargetArrows_isFiltered`. Use the
-- identity denominator for nonemptiness, the right Ore condition to produce a common predecessor
-- of two denominators into `X`, and the right-cancellation axiom to equalize parallel triangles.
instance localizationSourceArrows_isCofiltered
    (S : MorphismProperty C) [S.HasRightCalculusOfFractions] (X : C) :
    IsCofiltered (S / X) := by
  let e := sourceArrowsOpEquivUnderOp S X
  letI : IsFiltered ((S / X)ᵒᵖ) := IsFiltered.of_equivalence e
  letI : IsCofiltered (((S / X)ᵒᵖ)ᵒᵖ) := inferInstance
  exact IsCofiltered.of_equivalence (opOpEquivalence (S / X))

variable (S : MorphismProperty C) [S.HasRightCalculusOfFractions] (X Y : C)

/-- The diagram on `(S / X)ᵒᵖ` whose value at `s : X' ⟶ X` is the Hom-set `Hom_C(X', Y)`. -/
abbrev rightLocalizationHomDiagram :
    (S / X)ᵒᵖ ⥤ Type (max u v) :=
  (Over.forget S ⊤ X ⋙ CategoryTheory.Over.forget X).op ⋙ uliftYoneda.{u}.obj Y

/-- The canonical map from the Hom-set indexed by `s : X' ⟶ X` to the localized Hom-set
`Hom_{S^{-1}\mathcal C}(X, Y)`. -/
private noncomputable def rightLocalizationHomCoconeApp (U : (S / X)ᵒᵖ) :
    (rightLocalizationHomDiagram S X Y).obj U → (S.Q.obj X ⟶ S.Q.obj Y) :=
  fun f ↦
    (RightFraction.mk U.unop.hom U.unop.prop f.down).map S.Q (Localization.inverts S.Q S)

/-- Naturality of the canonical maps from the indexed Hom-sets into the localized Hom-set. -/
-- Proof sketch: an arrow in `(S / X)ᵒᵖ` is a commutative triangle refining one denominator by
-- another, and the diagram map is precomposition on numerators. The two resulting right fractions
-- in the localization represent the same morphism by functoriality of `RightFraction.map`.
private theorem rightLocalizationHomCocone_naturality {U V : (S / X)ᵒᵖ} (g : U ⟶ V) :
    (rightLocalizationHomDiagram S X Y).map g ≫
        rightLocalizationHomCoconeApp S X Y V =
      rightLocalizationHomCoconeApp S X Y U :=
  by
    funext f
    let φ : S.RightFraction X Y :=
      RightFraction.mk V.unop.hom V.unop.prop (g.unop.left ≫ f.down)
    let ψ : S.RightFraction X Y :=
      RightFraction.mk U.unop.hom U.unop.prop f.down
    change
      φ.map S.Q (Localization.inverts S.Q S) = ψ.map S.Q (Localization.inverts S.Q S)
    exact (RightFraction.map_eq_iff S.Q S φ ψ).2 <| by
      refine ⟨V.unop.left, 𝟙 _, g.unop.left, ?_, ?_, ?_⟩
      · simpa [φ, ψ] using (Over.w g.unop).symm
      · simp [φ, ψ]
      · simpa [φ] using V.unop.prop

-- The cocone on the right-localization Hom-diagram with point `Hom_{S^{-1}\mathcal C}(X, Y)`.
private noncomputable def rightLocalizationHomCocone :
    Cocone (rightLocalizationHomDiagram S X Y) where
  pt := S.Q.obj X ⟶ S.Q.obj Y
  ι :=
    { app := rightLocalizationHomCoconeApp S X Y
      naturality := by
        intro U V g
        simpa using rightLocalizationHomCocone_naturality S X Y g }

-- Proof sketch: surjectivity is Lemma 4.27.13 in the form `Localization.exists_rightFraction`,
-- which writes any morphism in `S⁻¹ C` as a roof over some object of `S / X`. Injectivity is
-- Lemma 4.27.14 encoded by `RightFraction.map_eq_iff`: two roofs become equal in the localization
-- exactly when they agree after refining to a common predecessor in the denominator category.
private theorem rightLocalizationHomCoconeTypes_isColimit :
    let F : (S / X)ᵒᵖ ⥤ Type (max u v) :=
      rightLocalizationHomDiagram S X Y
    let c : F.CoconeTypes := F.coconeTypesEquiv.symm (rightLocalizationHomCocone S X Y)
    c.IsColimit := by
  let F : (S / X)ᵒᵖ ⥤ Type (max u v) := rightLocalizationHomDiagram S X Y
  let c : F.CoconeTypes := F.coconeTypesEquiv.symm (rightLocalizationHomCocone S X Y)
  refine ⟨?_⟩
  constructor
  · rw [Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered]
    intro U V f g hfg
    let φ : S.RightFraction X Y :=
      RightFraction.mk U.unop.hom U.unop.prop f.down
    let ψ : S.RightFraction X Y :=
      RightFraction.mk V.unop.hom V.unop.prop g.down
    have hφψ : φ.map S.Q (Localization.inverts S.Q S) = ψ.map S.Q (Localization.inverts S.Q S) := by
      simpa [F, c, φ, ψ, rightLocalizationHomCocone, rightLocalizationHomCoconeApp,
        RightFraction.map] using hfg
    obtain ⟨Z, a, b, hab, hfg', hS⟩ :=
      (RightFraction.map_eq_iff S.Q S φ ψ).mp hφψ
    let W : S / X := Over.mk (⊤ : MorphismProperty C) (a ≫ U.unop.hom) hS
    refine ⟨Opposite.op W, (Over.homMk a rfl).op, (Over.homMk b hab.symm).op, ?_⟩
    change ULift.up (a ≫ f.down) = ULift.up (b ≫ g.down)
    simpa using hfg'
  · rw [Functor.CoconeTypes.descColimitType_surjective_iff]
    intro z
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction S.Q S z
    let U : S / X := Over.mk (⊤ : MorphismProperty C) φ.s φ.hs
    have hφ' : S.Q.map φ.f = S.Q.map φ.s ≫ z := by
      simpa [RightFraction.map, Category.assoc] using
        congrArg (fun k ↦ S.Q.map φ.s ≫ k) hφ.symm
    refine ⟨Opposite.op U, ULift.up φ.f, ?_⟩
    letI := Localization.inverts S.Q S _ φ.hs
    apply (cancel_epi (S.Q.map φ.s)).1
    simpa [F, c, U, rightLocalizationHomCocone, rightLocalizationHomCoconeApp, RightFraction.map,
      Category.assoc] using hφ'

/-- Internal colimit witness for the canonical cocone used to construct
`right_localization_hom_colimit`. -/
private noncomputable def rightLocalizationHomCocone_isColimit :
    IsColimit (rightLocalizationHomCocone S X Y) := by
  let F : (S / X)ᵒᵖ ⥤ Type (max u v) := rightLocalizationHomDiagram S X Y
  let c : F.CoconeTypes := F.coconeTypesEquiv.symm (rightLocalizationHomCocone S X Y)
  have hc : c.IsColimit := by
    simpa [F, c] using rightLocalizationHomCoconeTypes_isColimit S X Y
  simpa [c] using ((Functor.CoconeTypes.isColimit_iff c).mp hc).some

/-- Remark 4.27.15: the morphisms in the right-fraction localization `S^{-1}\mathcal C` from
`X` to `Y` are canonically the colimit over `(S / X)ᵒᵖ` of the Hom-sets
`\mathrm{Mor}_{\mathcal C}(X', Y)`, where `s : X' ⟶ X` ranges over arrows of `S`. -/
noncomputable def right_localization_hom_colimit
    (S : MorphismProperty C) [S.HasRightCalculusOfFractions] (X Y : C) :
    let F : (S / X)ᵒᵖ ⥤ Type (max u v) :=
      (Over.forget S ⊤ X ⋙ CategoryTheory.Over.forget X).op ⋙
        uliftYoneda.{u}.obj Y
    colimit F ≅ (S.Q.obj X ⟶ S.Q.obj Y) := by
  let F : (S / X)ᵒᵖ ⥤ Type (max u v) := rightLocalizationHomDiagram S X Y
  let c : ColimitCocone F :=
    ⟨rightLocalizationHomCocone S X Y, rightLocalizationHomCocone_isColimit S X Y⟩
  let _ : HasColimit F := HasColimit.mk c
  simpa [F, rightLocalizationHomDiagram] using colimit.isoColimitCocone c

/-- The colimit comparison sends the coprojection indexed by a denominator `s : X' ⟶ X` and a
numerator `f : X' ⟶ Y` to the corresponding right fraction in the localization. -/
-- Proof sketch: unfold `right_localization_hom_colimit` as the canonical isomorphism from
-- `colimit.isoColimitCocone` for `rightLocalizationHomCocone`, then evaluate its `hom` on the
-- coprojection `colimit.ι`.
theorem right_localization_hom_colimit_hom_ι
    (S : MorphismProperty C) [S.HasRightCalculusOfFractions] (X Y : C)
    (U : (S / X)ᵒᵖ)
    (f : (rightLocalizationHomDiagram S X Y).obj U) :
    (right_localization_hom_colimit S X Y).hom
        (colimit.ι (rightLocalizationHomDiagram S X Y) U f) =
      (RightFraction.mk U.unop.hom U.unop.prop f.down).map S.Q (Localization.inverts S.Q S) :=
  by
    let F : (S / X)ᵒᵖ ⥤ Type (max u v) := rightLocalizationHomDiagram S X Y
    let c : ColimitCocone F :=
      ⟨rightLocalizationHomCocone S X Y, rightLocalizationHomCocone_isColimit S X Y⟩
    let _ : HasColimit F := HasColimit.mk c
    -- Evaluate the standard colimit comparison on the summand indexed by `U`.
    have hι : ((colimit.ι F U) ≫ (colimit.isoColimitCocone c).hom) f =
        (c.cocone.ι.app U) f := by
      exact congrFun (colimit.isoColimitCocone_ι_hom c U) f
    -- Unfold the cocone leg to identify the resulting localized morphism with the roof `(f, U)`.
    simpa [F, c, right_localization_hom_colimit, rightLocalizationHomDiagram,
      rightLocalizationHomCocone, rightLocalizationHomCoconeApp] using hι

end MorphismProperty
end CategoryTheory

/-! ### Lemma_4_27_16 (from Chap04) -/
universe v u

namespace CategoryTheory

open MorphismProperty Localization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C)

/-
Companion recall: the canonical functor from `C` to the localization of `W` is `W.Q`.
-/
recall Q

/-
Companion recall: if `s : X ⟶ Y` lies in `W`, then its image under `W.Q` is canonically an
isomorphism, namely `Localization.isoOfHom W.Q W s hs`.
-/
recall isoOfHom

/-
Companion recall: the strict universal property of the canonical localization functor is packaged
by `Localization.strictUniversalPropertyFixedTargetQ`.
-/
recall strictUniversalPropertyFixedTargetQ

/- Domain-style sampling in the localization owner API:
- inspected owner predicate: `Functor.IsLocalization`
- inspected canonical localization functor: `MorphismProperty.Q`
- inspected owner instance for `W.Q`: `Functor.q_isLocalization`
- inspected bridge package: `Localization.strictUniversalPropertyFixedTargetQ`

Primitive data: the morphism property `W`.
Derived API: the localization functor `W.Q`, the strict universal property, the inverted
isomorphisms `Localization.isoOfHom`, and the owner-level instance `Functor.q_isLocalization`.

Source/core/bridge triage:
- `source-facing`: the chapter’s canonical localization functor attached to the chosen
  multiplicative system;
- `core/canonical`: the owner predicate `Functor.IsLocalization`;
- `bridge/view`: the strict universal property
  `Localization.strictUniversalPropertyFixedTargetQ`, from which the owner instance is built.

Lemma 4.27.16 is a `core/canonical` recall item: the source statement is the owner fact that the
canonical localization functor `W.Q` localizes `C` at `W`. The chapter’s surrounding
right-fraction hypotheses are redundant for this owner fact, so the main entry stays at the
assumption-free canonical recall rather than reintroducing a source-local wrapper theorem.
-/
/- Lemma 4.27.16: the canonical localization functor `W.Q` is a localization of `C` at the
morphism property `W`. -/
recall Functor.q_isLocalization : W.Q.IsLocalization W

end CategoryTheory

/-! ### Lemma_4_27_17 (from Chap04) -/
open CategoryTheory.Limits

universe w v v' u

namespace CategoryTheory

open MorphismProperty

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasRightCalculusOfFractions]

/- Domain-style sampling for Lemma 4.27.17:
- primary domain: localization of morphism properties and finite-limit preservation;
- inspected owner declarations:
  `Functor.IsLocalization`,
  `Functor.q_isLocalization`,
  `Functor.IsLocalization.preservesFiniteColimits`,
  `preservesFiniteLimits_of_op`;
- best owner abstraction: `PreservesFiniteLimits L` for a localization functor `L`, obtained by
  transporting the colimit-preservation theorem for `L.op` across opposites.

Primitive-vs-derived split:
- primitive data: the morphism property `W`;
- derived API: the source-facing instance `PreservesFiniteLimits W.Q`, together with the companion
  bridge theorem `Functor.IsLocalization.preservesFiniteLimits` for any chosen localization
  functor `L`. -/

/- Source/core/bridge triage for Lemma 4.27.17:
- source-facing: the Stacks lemma for the canonical localization functor `W.Q`.
- core/canonical: the owner property is `PreservesFiniteLimits`.
- bridge/view: `Functor.IsLocalization.preservesFiniteLimits` transports the canonical
  finite-colimit preservation theorem for `W.op` across opposites, and the instance that follows
  is the derived owner property for the canonical localization functor `W.Q`. -/

namespace Functor.IsLocalization

-- Proof sketch: apply Lemma 4.27.9 to the opposite morphism property `W.op`, obtaining that
-- `L.op` preserves finite colimits, and then transport back across opposites via
-- `preservesFiniteLimits_of_op`.
/-- Lemma 4.27.17: any localization functor of a right multiplicative system preserves finite
limits. -/
theorem preservesFiniteLimits {D : Type w} [Category.{v'} D] (L : C ⥤ D) [L.IsLocalization W] :
    PreservesFiniteLimits L := by
  -- Apply Lemma 4.27.9 to the opposite localization model and transport it to `L.op`.
  let e := Localization.equivalenceFromModel L.op W.op
  letI : PreservesFiniteColimits W.op.Q := localization_Q_preservesFiniteColimits (W := W.op)
  letI : PreservesFiniteColimits e.functor := by infer_instance
  letI : PreservesFiniteColimits (W.op.Q ⋙ e.functor) :=
    Limits.comp_preservesFiniteColimits W.op.Q e.functor
  letI : PreservesFiniteColimits L.op :=
    preservesFiniteColimits_of_natIso (Localization.qCompEquivalenceFromModelFunctorIso L.op W.op)
  -- Opposite finite-colimit preservation is equivalent to finite-limit preservation on `L`.
  exact preservesFiniteLimits_of_op L

end Functor.IsLocalization

/-- The canonical localization functor of a right multiplicative system preserves finite limits. -/
instance : PreservesFiniteLimits W.Q :=
  Functor.IsLocalization.preservesFiniteLimits W W.Q

end CategoryTheory

/-! ### Lemma_4_27_18 (from Chap04) -/
open CategoryTheory

universe v u

namespace CategoryTheory

open MorphismProperty
open MorphismProperty.RightFraction
open Localization

variable {C : Type u} [Category.{v} C]

variable (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
variable {D : Type*} [Category D]
variable {X Y X' Y' : C}

/- Domain-style sampling for Lemma 4.27.18:
- primary domain: commutative squares in a localization with right-fraction representatives;
- inspected owner declarations:
  `Functor.IsLocalization`,
  `MorphismProperty.RightFraction`,
  `Localization.exists_rightFraction`,
  `MorphismProperty.RightFraction.map_eq_iff`,
  `MorphismProperty.map_eq_iff_precomp`;
- best owner abstraction: `Functor.IsLocalization W` for the ambient localization functor, with
  `W.RightFraction` as the primitive roof data representing the vertical localization morphisms.

Primitive data: the two right-fraction representatives `aFrac : W.RightFraction X X'` and
`bFrac : W.RightFraction Y Y'`.
Derived API: the represented localization morphisms
  `aFrac.map L (Localization.inverts L W)` and
  `bFrac.map L (Localization.inverts L W)` for an arbitrary localization functor `L`; for the
  canonical localization functor `W.Q`, these are exactly the source-facing vertical morphisms.

Source/core/bridge triage:
- `source-facing`: `commutative_square_lifts_to_right_fraction_square`;
- `core/canonical`: `localization_commutative_square_has_right_fraction_lift`, together with
  `Functor.IsLocalization`, `W.RightFraction`, and the owner-level equality criteria for
  represented localization morphisms;
- `bridge/view`: the equation-form companion
  `commutative_square_lifts_to_right_fraction_square_eq`. -/

private theorem rightFraction_map_precomp_eq
    (L : C ⥤ D) [L.IsLocalization W] {X Y : C} (φ : W.RightFraction X Y)
    {X'' : C} (t : X'' ⟶ φ.X') (ht : W (t ≫ φ.s)) :
    φ.map L (inverts L W) =
      (RightFraction.mk (t ≫ φ.s) ht (t ≫ φ.f)).map L (inverts L W) := by
  exact (MorphismProperty.RightFraction.map_eq_iff L W φ
    (RightFraction.mk (t ≫ φ.s) ht (t ≫ φ.f))).2
      ⟨X'', t, 𝟙 _, by simp, by simp, by simpa using ht⟩

/-- Core companion: a commutative square in any localization functor for `W` can be represented
by a commutative diagram in `C` after replacing the source and target by arrows in `W`. -/
theorem localization_commutative_square_has_right_fraction_lift
    (L : C ⥤ D) [L.IsLocalization W] (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : L.obj X ⟶ L.obj X') (b : L.obj Y ⟶ L.obj Y')
    (hcomm : CommSq a (L.map f) (L.map f') b) :
    ∃ (aFrac : W.RightFraction X X') (bFrac : W.RightFraction Y Y')
      (f'' : aFrac.X' ⟶ bFrac.X'),
      CommSq f'' aFrac.s bFrac.s f ∧
        CommSq aFrac.f f'' f' bFrac.f ∧
        a = aFrac.map L (inverts L W) ∧
        b = bFrac.map L (inverts L W) := by
  obtain ⟨a₀, ha₀⟩ := exists_rightFraction L W a
  obtain ⟨bFrac, hb⟩ := exists_rightFraction L W b
  let cFrac : W.RightFraction X bFrac.X' :=
    (LeftFraction.mk f bFrac.s bFrac.hs).rightFraction
  have hc : cFrac.s ≫ f = cFrac.f ≫ bFrac.s := by
    simpa [cFrac] using
      (LeftFraction.rightFraction_fac (LeftFraction.mk f bFrac.s bFrac.hs))
  let dFrac : W.RightFraction cFrac.X' a₀.X' :=
    (LeftFraction.mk cFrac.s a₀.s a₀.hs).rightFraction
  have hd : dFrac.s ≫ cFrac.s = dFrac.f ≫ a₀.s := by
    simpa [dFrac] using
      (LeftFraction.rightFraction_fac (LeftFraction.mk cFrac.s a₀.s a₀.hs))
  have hleft :
      L.map dFrac.s ≫ L.map cFrac.s ≫ a = L.map (dFrac.f ≫ a₀.f) := by
    calc
      L.map dFrac.s ≫ L.map cFrac.s ≫ a =
          L.map dFrac.f ≫ L.map a₀.s ≫ a := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ a) (congrArg L.map hd)
      _ = L.map dFrac.f ≫ L.map a₀.s ≫ a₀.map L (inverts L W) := by
            rw [ha₀]
      _ = L.map dFrac.f ≫ L.map a₀.f := by
            simp
      _ = L.map (dFrac.f ≫ a₀.f) := by
            simp [Functor.map_comp]
  have hright :
      L.map cFrac.s ≫ L.map f ≫ b = L.map (cFrac.f ≫ bFrac.f) := by
    calc
      L.map cFrac.s ≫ L.map f ≫ b =
          L.map cFrac.f ≫ L.map bFrac.s ≫ b := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ b) (congrArg L.map hc)
      _ = L.map cFrac.f ≫ L.map bFrac.s ≫ bFrac.map L (inverts L W) := by
            rw [hb]
      _ = L.map cFrac.f ≫ L.map bFrac.f := by
            simp
      _ = L.map (cFrac.f ≫ bFrac.f) := by
            simp [Functor.map_comp]
  have hEq :
      L.map (dFrac.f ≫ a₀.f ≫ f') = L.map (dFrac.s ≫ cFrac.f ≫ bFrac.f) := by
    calc
      L.map (dFrac.f ≫ a₀.f ≫ f') =
          L.map (dFrac.f ≫ a₀.f) ≫ L.map f' := by
            simp [Functor.map_comp, Category.assoc]
      _ = (L.map dFrac.s ≫ L.map cFrac.s ≫ a) ≫ L.map f' := by
            rw [hleft]
      _ = L.map dFrac.s ≫ L.map cFrac.s ≫ (a ≫ L.map f') := by
            simp [Category.assoc]
      _ = L.map dFrac.s ≫ L.map cFrac.s ≫ (L.map f ≫ b) := by
            rw [hcomm.w]
      _ = L.map dFrac.s ≫ (L.map cFrac.s ≫ L.map f ≫ b) := by
            simp
      _ = L.map dFrac.s ≫ L.map (cFrac.f ≫ bFrac.f) := by
            rw [hright]
      _ = L.map (dFrac.s ≫ cFrac.f ≫ bFrac.f) := by
            simp [Functor.map_comp]
  obtain ⟨Z, u, hu, hnum⟩ :=
    (map_eq_iff_precomp L W (dFrac.f ≫ a₀.f ≫ f') (dFrac.s ≫ cFrac.f ≫ bFrac.f)).mp hEq
  have haFrac : W (u ≫ dFrac.f ≫ a₀.s) := by
    simpa [Category.assoc, hd] using
      W.comp_mem _ _ hu (W.comp_mem _ _ dFrac.hs cFrac.hs)
  let aFrac : W.RightFraction X X' :=
    RightFraction.mk (u ≫ dFrac.f ≫ a₀.s) haFrac (u ≫ dFrac.f ≫ a₀.f)
  let f'' : aFrac.X' ⟶ bFrac.X' := u ≫ dFrac.s ≫ cFrac.f
  refine ⟨aFrac, bFrac, f'', ?_, ?_, ?_, hb⟩
  · refine ⟨?_⟩
    dsimp [aFrac, f'']
    calc
      (u ≫ dFrac.s ≫ cFrac.f) ≫ bFrac.s = u ≫ dFrac.s ≫ (cFrac.f ≫ bFrac.s) := by
        simp [Category.assoc]
      _ = u ≫ dFrac.s ≫ (cFrac.s ≫ f) := by
        simpa [Category.assoc] using congrArg (fun k ↦ u ≫ dFrac.s ≫ k) hc.symm
      _ = u ≫ (dFrac.s ≫ cFrac.s) ≫ f := by
        simp [Category.assoc]
      _ = (u ≫ dFrac.f ≫ a₀.s) ≫ f := by
        simpa [Category.assoc] using congrArg (fun k ↦ u ≫ k ≫ f) hd
      _ = aFrac.s ≫ f := by
        simp [aFrac, Category.assoc]
  · refine ⟨?_⟩
    dsimp [aFrac, f'']
    simpa [Category.assoc] using hnum
  · calc
      a = a₀.map L (inverts L W) := ha₀
      _ = aFrac.map L (inverts L W) := by
        have haPrecomp : W ((u ≫ dFrac.f) ≫ a₀.s) := by
          simpa [Category.assoc] using haFrac
        dsimp [aFrac]
        simpa [Category.assoc] using
          rightFraction_map_precomp_eq W L a₀ (u ≫ dFrac.f) haPrecomp

/-- Equation-form companion for an arbitrary localization functor of `W`. -/
theorem localization_commutative_square_has_right_fraction_lift_eq
    (L : C ⥤ D) [L.IsLocalization W] (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : L.obj X ⟶ L.obj X') (b : L.obj Y ⟶ L.obj Y')
    (hcomm : L.map f ≫ b = a ≫ L.map f') :
    ∃ (aFrac : W.RightFraction X X') (bFrac : W.RightFraction Y Y')
      (f'' : aFrac.X' ⟶ bFrac.X'),
      aFrac.s ≫ f = f'' ≫ bFrac.s ∧
        aFrac.f ≫ f' = f'' ≫ bFrac.f ∧
        a = aFrac.map L (inverts L W) ∧
        b = bFrac.map L (inverts L W) := by
  obtain ⟨aFrac, bFrac, f'', hleft, hright, ha, hb⟩ :=
    localization_commutative_square_has_right_fraction_lift W L f f' a b ⟨hcomm.symm⟩
  exact ⟨aFrac, bFrac, f'', hleft.w.symm, hright.w, ha, hb⟩

/-- Lemma 4.27.18: a commutative square in the canonical localization `W.Q` can be represented
by a commutative diagram in `C` whose vertical arrows are right-fraction denominators in `W`. -/
theorem commutative_square_lifts_to_right_fraction_square
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : W.Q.obj X ⟶ W.Q.obj X') (b : W.Q.obj Y ⟶ W.Q.obj Y')
    (hcomm : CommSq a (W.Q.map f) (W.Q.map f') b) :
    ∃ (aFrac : {φ : W.RightFraction X X' // a = φ.map W.Q (inverts _ _)})
      (bFrac : {φ : W.RightFraction Y Y' // b = φ.map W.Q (inverts _ _)})
      (f'' : aFrac.val.X' ⟶ bFrac.val.X'),
      CommSq f'' aFrac.val.s bFrac.val.s f ∧
        CommSq aFrac.val.f f'' f' bFrac.val.f := by
  obtain ⟨aFrac, bFrac, f'', hleft, hright, ha, hb⟩ :=
    localization_commutative_square_has_right_fraction_lift W W.Q f f' a b hcomm
  exact ⟨⟨aFrac, ha⟩, ⟨bFrac, hb⟩, f'', hleft, hright⟩

/-- Equation-form companion for the canonical right-fraction lift statement. -/
theorem commutative_square_lifts_to_right_fraction_square_eq
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : W.Q.obj X ⟶ W.Q.obj X') (b : W.Q.obj Y ⟶ W.Q.obj Y')
    (hcomm : W.Q.map f ≫ b = a ≫ W.Q.map f') :
    ∃ (aFrac : {φ : W.RightFraction X X' // a = φ.map W.Q (inverts _ _)})
      (bFrac : {φ : W.RightFraction Y Y' // b = φ.map W.Q (inverts _ _)})
      (f'' : aFrac.val.X' ⟶ bFrac.val.X'),
      aFrac.val.s ≫ f = f'' ≫ bFrac.val.s ∧
        aFrac.val.f ≫ f' = f'' ≫ bFrac.val.f := by
  obtain ⟨aFrac, bFrac, f'', hleft, hright⟩ :=
    commutative_square_lifts_to_right_fraction_square W f f' a b ⟨hcomm.symm⟩
  exact ⟨aFrac, bFrac, f'', hleft.w.symm, hright.w⟩

end CategoryTheory

/-! ### Lemma_4_27_19 (from Chap04) -/
universe v u

namespace CategoryTheory

open MorphismProperty
open Localization
open Functor.IsLocalization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions]

local notation "Q" => LeftFraction.Localization.Q

/-
Companion recall: the left-fraction model localizes `C` at `W` via the canonical functor
`LeftFraction.Localization.Q W`.
-/
recall LeftFraction.Localization.Q

/-
Companion recall: replacing the target of a localization functor by an equivalent category
preserves the localization property via `Functor.IsLocalization.of_equivalence_target`.
-/
recall Functor.IsLocalization.of_equivalence_target

/-
Companion recall: transporting a localization functor across opposites is controlled by
`Functor.IsLocalization.op_iff`.
-/
recall Functor.IsLocalization.op_iff

/- Domain-style sampling in the localization owner API:
- source-facing model: `LeftFraction.Localization W`
- source-facing right-fraction model: `(LeftFraction.Localization W.op)ᵒᵖ`, presented by the
  functor `(LeftFraction.Localization.Q W.op).rightOp`
- core/canonical owner predicate: `Functor.IsLocalization`
- core/canonical uniqueness equivalence: `Localization.uniq`

Primitive data: the morphism property `W`.
Derived API: the two source-model localization functors and the canonical equivalence between
their targets. The right-fraction-model localization proof for `(Q W.op).rightOp` is auxiliary
infrastructure, so it should stay local rather than becoming a named bridge declaration.

Lemma 4.27.19 is a `bridge/view` item: it specializes the canonical owner equivalence to the
left-fraction model `LeftFraction.Localization W` and the textbook right-fraction model
`(LeftFraction.Localization W.op)ᵒᵖ`. The main item should therefore be a direct specialization
of `Localization.uniq`, not a renamed shell around it.
-/
section

omit [W.HasLeftCalculusOfFractions] in
local instance : (Q W.op).rightOp.IsLocalization W := by
  let G := (Q W.op).rightOp
  have hGop : G.op.IsLocalization W.op :=
    of_equivalence_target (Q W.op) W.op _
      (opOpEquivalence (LeftFraction.Localization W.op)).symm (Iso.refl _)
  exact (op_iff G W).1 hGop

/- Lemma 4.27.19: the left-fraction localization of `C` at `W` is canonically equivalent to the
opposite of the left-fraction localization of `Cᵒᵖ` at `W.op`, i.e. to the textbook
right-fraction model. This is exactly the owner equivalence `Localization.uniq`, specialized to
`Q W` and `(Q W.op).rightOp`. -/
#check (uniq (Q W) (Q W.op).rightOp W :
  LeftFraction.Localization W ≌ (LeftFraction.Localization W.op)ᵒᵖ)

end

end CategoryTheory

/-! ### Definition_4_27_20 (from Chap04) -/
universe v u

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling:
- source-facing owner: `IsSaturatedMultiplicativeSystem`
- core/canonical owners already present upstream: `W.HasLeftCalculusOfFractions`,
  `W.HasRightCalculusOfFractions`, `W.IsMultiplicative`, and `W.RespectsIso`
- best owner abstraction: a saturated multiplicative system is a source-facing extension of the
  left and right calculus-of-fractions owners by the Stacks saturation axiom

Primitive data are exactly the left and right calculus-of-fractions owner instances together with
the Stacks saturation axiom. Derived API such as closure under isomorphisms should be exposed
through the canonical mathlib morphism-property owners rather than by parallel local wrappers.
-/

/- Source/core/bridge triage:
- `source-facing`: `IsSaturatedMultiplicativeSystem`
- `core/canonical`: `HasLeftCalculusOfFractions`, `HasRightCalculusOfFractions`,
  `IsMultiplicative`, `RespectsIso`
- `bridge/view`: the derived inclusion `isomorphisms C ≤ W`
-/

/-- Definition 4.27.20: a multiplicative system `W` is saturated if whenever `f`, `g`, and `h`
are composable and both composites `f ≫ g` and `g ≫ h` lie in `W`, then `g` itself lies in
`W`. -/
class IsSaturatedMultiplicativeSystem (W : MorphismProperty C) : Prop where
  toHasLeftCalculusOfFractions : W.HasLeftCalculusOfFractions
  toHasRightCalculusOfFractions : W.HasRightCalculusOfFractions
  saturation {X0 X1 X2 X3 : C} (f : X0 ⟶ X1) (g : X1 ⟶ X2) (h : X2 ⟶ X3)
      (_ : W (f ≫ g)) (_ : W (g ≫ h)) : W g

attribute [instance] IsSaturatedMultiplicativeSystem.toHasLeftCalculusOfFractions
attribute [instance] IsSaturatedMultiplicativeSystem.toHasRightCalculusOfFractions

namespace IsSaturatedMultiplicativeSystem

lemma isomorphisms_le (W : MorphismProperty C) [IsSaturatedMultiplicativeSystem W] :
    isomorphisms C ≤ W := by
  intro X Y f hf
  let e : X ≅ Y := asIso f
  have h₁ : W (e.inv ≫ e.hom) := by simpa using W.id_mem Y
  have h₂ : W (e.hom ≫ e.inv) := by simpa using W.id_mem X
  simpa using saturation e.inv e.hom e.inv h₁ h₂

instance respectsIso (W : MorphismProperty C) [IsSaturatedMultiplicativeSystem W] :
    W.RespectsIso :=
  respectsIso_of_isStableUnderComposition <| isomorphisms_le W

end IsSaturatedMultiplicativeSystem

/-- The class of isomorphisms is a saturated multiplicative system. -/
instance : IsSaturatedMultiplicativeSystem (isomorphisms C) where
  toHasLeftCalculusOfFractions := inferInstance
  toHasRightCalculusOfFractions := inferInstance
  saturation := by
    intro X0 X1 X2 X3 f g h hfg hgh
    rw [isomorphisms.iff] at hfg hgh ⊢
    letI : IsSplitEpi g :=
      IsSplitEpi.mk'
        { section_ := inv (f ≫ g) ≫ f
          id := by simp [Category.assoc] }
    letI : Mono g := mono_of_mono g h
    exact isIso_of_mono_of_isSplitEpi g

end MorphismProperty
end CategoryTheory

/-! ### Lemma_4_27_21 (from Chap04) -/
universe v u

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]
variable (S : MorphismProperty C) [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]

/- Domain-style sampling for Lemma 4.27.21:
- source-facing content: the Stacks description of the saturated closure
  `S' = { f | ∃ g h, S (f ≫ g) ∧ S (h ≫ f) }`
- core/canonical owner abstraction: the localization functor `S.Q` and the induced morphism
  property `S.saturatedClosure` of morphisms inverted by `S.Q`
- upstream owner facts inspected before refining:
  `MorphismProperty.Q_inverts`,
  `MorphismProperty.IsInvertedBy.iff_le_inverseImage_isomorphisms`,
  `Functor.q_isLocalization`,
  `Adjunction.isLocalization`

Primitive data: the two calculus-of-fractions owner instances on `S`.
Derived API: the owner `S.saturatedClosure`, its saturation, and the comparison with the textbook
source-facing description. In particular, the inclusion `S ≤ S.saturatedClosure` is already the
canonical owner fact `S.Q_inverts`, so no parallel inclusion wrapper is kept.

Source/core/bridge triage:
- `source-facing`: the textbook characterization of `S.saturatedClosure`
- `core/canonical`: the owner `S.saturatedClosure`
- `bridge/view`: the minimality theorem `saturatedClosure_le_iff`
-/

/-- The saturated closure of `S`, i.e. the morphisms inverted by the canonical localization
functor `S.Q`. -/
abbrev saturatedClosure : MorphismProperty C :=
  (isomorphisms S.Localization).inverseImage S.Q

/-- Helper for Lemma 4.27.21: every morphism of `S` already lies in the saturated closure. -/
lemma mem_saturatedClosure_of_mem {X Y : C} {f : X ⟶ Y} (hf : S f) :
    S.saturatedClosure f := by
  -- The localization functor inverts each morphism of `S`.
  change IsIso (S.Q.map f)
  exact Localization.inverts S.Q S _ hf

/-- Helper for Lemma 4.27.21: by definition the localization functor `S.Q` inverts the saturated
closure of `S`. -/
lemma saturatedClosure_inverts : S.saturatedClosure.IsInvertedBy S.Q := by
  intro X Y f hf
  -- Unfolding the inverse-image definition turns membership into invertibility of `S.Q.map f`.
  change IsIso (S.Q.map f) at hf
  exact hf

/-- Helper for Lemma 4.27.21: two-sided composites in `S` force the middle morphism to become an
isomorphism after localization. -/
lemma mem_saturatedClosure_of_two_sided_S_composites {X Y Z₁ Z₂ : C} {f : X ⟶ Y}
    {g : Y ⟶ Z₁} {h : Z₂ ⟶ X} (hfg : S (f ≫ g)) (hhf : S (h ≫ f)) :
    S.saturatedClosure f := by
  -- We build explicit right and left inverses for `S.Q.map f` from the two composite witnesses.
  change IsIso (S.Q.map f)
  let invRight : S.Q.obj Y ⟶ S.Q.obj X :=
    S.Q.map g ≫ (Localization.isoOfHom S.Q S (f ≫ g) hfg).inv
  let invLeft : S.Q.obj Y ⟶ S.Q.obj X :=
    (Localization.isoOfHom S.Q S (h ≫ f) hhf).inv ≫ S.Q.map h
  have h_right : S.Q.map f ≫ invRight = 𝟙 _ := by
    -- The right inverse comes from the inverse of `S.Q.map (f ≫ g)`.
    dsimp [invRight]
    simpa [Functor.map_comp, Category.assoc] using
      (Localization.isoOfHom_hom_inv_id S.Q S (f ≫ g) hfg)
  have h_left_aux : invLeft ≫ S.Q.map f = 𝟙 _ := by
    -- The left inverse comes from the inverse of `S.Q.map (h ≫ f)`.
    dsimp [invLeft]
    simpa [Functor.map_comp, Category.assoc] using
      (Localization.isoOfHom_inv_hom_id S.Q S (h ≫ f) hhf)
  have h_inv_eq : invLeft = invRight := by
    -- Any left inverse and right inverse of the same morphism agree.
    calc
      invLeft = invLeft ≫ 𝟙 _ := by simp
      _ = invLeft ≫ (S.Q.map f ≫ invRight) := by rw [h_right]
      _ = (invLeft ≫ S.Q.map f) ≫ invRight := by simp [Category.assoc]
      _ = invRight := by rw [h_left_aux, Category.id_comp]
  have h_left : invRight ≫ S.Q.map f = 𝟙 _ := by
    rw [← h_inv_eq, h_left_aux]
  exact ⟨invRight, h_right, h_left⟩

/-- Helper for Lemma 4.27.21: a morphism in the saturated closure admits a postcomposition that
lies in `S`. -/
lemma exists_postcomp_mem_of_mem_saturatedClosure {X Y : C} {f : X ⟶ Y}
    (hf : S.saturatedClosure f) :
    ∃ (Z : C) (g : Y ⟶ Z), S (f ≫ g) := by
  -- Route correction: represent the inverse of `S.Q.map f` by a left fraction, then clear the
  -- denominator to turn localization invertibility into an `S`-postcomposition witness.
  change IsIso (S.Q.map f) at hf
  letI : IsIso (S.Q.map f) := hf
  obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction S.Q S (inv (S.Q.map f))
  have hcomp : S.Q.map f ≫ φ.map S.Q (Localization.inverts S.Q S) = 𝟙 _ := by
    rw [← hφ]
    exact IsIso.hom_inv_id (S.Q.map f)
  have hmap : S.Q.map (f ≫ φ.f) = S.Q.map φ.s := by
    -- Multiplying by the denominator of the left fraction removes the inverse.
    calc
      S.Q.map (f ≫ φ.f) = S.Q.map f ≫ S.Q.map φ.f := by
        rw [Functor.map_comp]
      _ = S.Q.map f ≫ (φ.map S.Q (Localization.inverts S.Q S) ≫ S.Q.map φ.s) := by
        rw [MorphismProperty.LeftFraction.map_comp_map_s]
      _ = (S.Q.map f ≫ φ.map S.Q (Localization.inverts S.Q S)) ≫ S.Q.map φ.s := by
        simp [Category.assoc]
      _ = 𝟙 _ ≫ S.Q.map φ.s := by rw [hcomp]
      _ = S.Q.map φ.s := by simp
  obtain ⟨Z, t, ht, hpost⟩ :=
    (MorphismProperty.map_eq_iff_postcomp S.Q S (f ≫ φ.f) φ.s).mp hmap
  refine ⟨Z, φ.f ≫ t, ?_⟩
  -- The required composite is identified with the `S`-morphism `φ.s ≫ t`.
  have hs : S (φ.s ≫ t) := S.comp_mem _ _ φ.hs ht
  have hpost' : f ≫ φ.f ≫ t = φ.s ≫ t := by
    simpa [Category.assoc] using hpost
  rw [hpost']
  exact hs

/-- Helper for Lemma 4.27.21: a morphism in the saturated closure admits a precomposition that
lies in `S`. -/
lemma exists_precomp_mem_of_mem_saturatedClosure {X Y : C} {f : X ⟶ Y}
    (hf : S.saturatedClosure f) :
    ∃ (Z : C) (h : Z ⟶ X), S (h ≫ f) := by
  -- Route correction: use a right-fraction presentation of the inverse to recover an
  -- `S`-precomposition witness.
  change IsIso (S.Q.map f) at hf
  letI : IsIso (S.Q.map f) := hf
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction S.Q S (inv (S.Q.map f))
  have hcomp : φ.map S.Q (Localization.inverts S.Q S) ≫ S.Q.map f = 𝟙 _ := by
    rw [← hφ]
    exact IsIso.inv_hom_id (S.Q.map f)
  have hmap : S.Q.map (φ.f ≫ f) = S.Q.map φ.s := by
    -- Multiplying by the denominator of the right fraction removes the inverse.
    calc
      S.Q.map (φ.f ≫ f) = S.Q.map φ.f ≫ S.Q.map f := by
        rw [Functor.map_comp]
      _ = (S.Q.map φ.s ≫ φ.map S.Q (Localization.inverts S.Q S)) ≫ S.Q.map f := by
        rw [MorphismProperty.RightFraction.map_s_comp_map]
      _ = S.Q.map φ.s ≫ (φ.map S.Q (Localization.inverts S.Q S) ≫ S.Q.map f) := by
        simp
      _ = S.Q.map φ.s ≫ 𝟙 _ := by rw [hcomp]
      _ = S.Q.map φ.s := by simp
  obtain ⟨Z, t, ht, hpre⟩ :=
    (MorphismProperty.map_eq_iff_precomp S.Q S (φ.f ≫ f) φ.s).mp hmap
  refine ⟨Z, t ≫ φ.f, ?_⟩
  -- The required composite is identified with the `S`-morphism `t ≫ φ.s`.
  have hs : S (t ≫ φ.s) := S.comp_mem _ _ ht φ.hs
  simpa [Category.assoc, hpre] using hs

/-- Lemma 4.27.21: for a multiplicative system `S`, the morphisms whose image under the canonical
localization functor `S.Q : C ⥤ S.Localization` is an isomorphism are exactly the textbook set
`S'` of morphisms `f` for which there exist arrows `g` and `h` with `f ≫ g ∈ S` and
`h ≫ f ∈ S`. -/
theorem saturatedClosure_eq :
    S.saturatedClosure =
      fun X Y f ↦
        ∃ (Z₁ Z₂ : C) (g : Y ⟶ Z₁) (h : Z₂ ⟶ X), S (f ≫ g) ∧ S (h ≫ f) := by
  ext X Y f
  constructor
  · intro hf
    -- Extract one witness on each side from the inverse of `S.Q.map f`.
    obtain ⟨Z₁, g, hfg⟩ := exists_postcomp_mem_of_mem_saturatedClosure S hf
    obtain ⟨Z₂, h, hhf⟩ := exists_precomp_mem_of_mem_saturatedClosure S hf
    exact ⟨Z₁, Z₂, g, h, hfg, hhf⟩
  · rintro ⟨Z₁, Z₂, g, h, hfg, hhf⟩
    -- Two-sided composite witnesses already force invertibility in the localization.
    exact mem_saturatedClosure_of_two_sided_S_composites S hfg hhf

/-- The morphisms inverted by `S.Q` form a saturated multiplicative system. -/
instance saturatedClosure_isSaturatedMultiplicativeSystem :
    IsSaturatedMultiplicativeSystem S.saturatedClosure := by
  refine
    { toHasLeftCalculusOfFractions := ?_
      toHasRightCalculusOfFractions := ?_
      saturation := ?_ }
  · refine
      { exists_leftFraction := ?_
        ext := ?_ }
    · intro X Y φ
      -- Represent the localized morphism of the right fraction by a left fraction over `S`, then
      -- refine the denominator until the equality holds on the nose.
      obtain ⟨ψ₀, hψ₀⟩ :=
        Localization.exists_leftFraction S.Q S (φ.map S.Q (saturatedClosure_inverts S))
      have hψ₀_assoc :
          ψ₀.map S.Q (Localization.inverts S.Q S) ≫ S.Q.map ψ₀.s = S.Q.map ψ₀.f :=
        MorphismProperty.LeftFraction.map_comp_map_s ψ₀ S.Q (Localization.inverts S.Q S)
      have hmap : S.Q.map (φ.s ≫ ψ₀.f) = S.Q.map (φ.f ≫ ψ₀.s) := by
        calc
          S.Q.map (φ.s ≫ ψ₀.f) = S.Q.map φ.s ≫ S.Q.map ψ₀.f := by
            rw [Functor.map_comp]
          _ =
              S.Q.map φ.s ≫ ψ₀.map S.Q (Localization.inverts S.Q S) ≫ S.Q.map ψ₀.s := by
            rw [← hψ₀_assoc]
          _ =
              (S.Q.map φ.s ≫ ψ₀.map S.Q (Localization.inverts S.Q S)) ≫ S.Q.map ψ₀.s := by
            simp [Category.assoc]
          _ =
              (S.Q.map φ.s ≫ φ.map S.Q (saturatedClosure_inverts S)) ≫ S.Q.map ψ₀.s := by
            rw [hψ₀]
          _ = S.Q.map φ.f ≫ S.Q.map ψ₀.s := by
            rw [MorphismProperty.RightFraction.map_s_comp_map]
          _ = S.Q.map (φ.f ≫ ψ₀.s) := by
            rw [Functor.map_comp]
      obtain ⟨Z, t, ht, hpost⟩ :=
        (MorphismProperty.map_eq_iff_postcomp S.Q S (φ.s ≫ ψ₀.f) (φ.f ≫ ψ₀.s)).mp hmap
      have hs : S.saturatedClosure (ψ₀.s ≫ t) :=
        mem_saturatedClosure_of_mem S (S.comp_mem _ _ ψ₀.hs ht)
      refine ⟨{ f := ψ₀.f ≫ t, s := ψ₀.s ≫ t, hs := hs }, ?_⟩
      -- The refined denominator clears the localization ambiguity.
      simpa [Category.assoc] using hpost.symm
    · intro X' X Y f₁ f₂ s hs hEq
      -- A precomposition witness in `S` for `s` reduces the equalization problem to the left
      -- calculus axiom already available for `S`.
      obtain ⟨Z, a, ha⟩ := exists_precomp_mem_of_mem_saturatedClosure S hs
      obtain ⟨Y', t, ht, hfac⟩ :=
        MorphismProperty.HasLeftCalculusOfFractions.ext (W := S) f₁ f₂ (a ≫ s) ha
          (by simpa [Category.assoc] using congrArg (fun k ↦ a ≫ k) hEq)
      exact ⟨Y', t, mem_saturatedClosure_of_mem S ht, hfac⟩
  · refine
      { exists_rightFraction := ?_
        ext := ?_ }
    · intro X Y φ
      -- Represent the localized morphism of the left fraction by a right fraction over `S`, then
      -- refine the numerator until the equality holds on the nose.
      obtain ⟨ψ₀, hψ₀⟩ :=
        Localization.exists_rightFraction S.Q S (φ.map S.Q (saturatedClosure_inverts S))
      have hmap : S.Q.map (ψ₀.s ≫ φ.f) = S.Q.map (ψ₀.f ≫ φ.s) := by
        calc
          S.Q.map (ψ₀.s ≫ φ.f) = S.Q.map ψ₀.s ≫ S.Q.map φ.f := by
            rw [Functor.map_comp]
          _ =
              S.Q.map ψ₀.s ≫
                (φ.map S.Q (saturatedClosure_inverts S) ≫ S.Q.map φ.s) := by
            rw [MorphismProperty.LeftFraction.map_comp_map_s]
          _ =
              (S.Q.map ψ₀.s ≫ φ.map S.Q (saturatedClosure_inverts S)) ≫ S.Q.map φ.s := by
            simp [Category.assoc]
          _ =
              (S.Q.map ψ₀.s ≫ ψ₀.map S.Q (Localization.inverts S.Q S)) ≫ S.Q.map φ.s := by
            rw [hψ₀]
          _ = S.Q.map ψ₀.f ≫ S.Q.map φ.s := by
            rw [MorphismProperty.RightFraction.map_s_comp_map]
          _ = S.Q.map (ψ₀.f ≫ φ.s) := by
            rw [Functor.map_comp]
      obtain ⟨Z, t, ht, hpre⟩ :=
        (MorphismProperty.map_eq_iff_precomp S.Q S (ψ₀.s ≫ φ.f) (ψ₀.f ≫ φ.s)).mp hmap
      have hs : S.saturatedClosure (t ≫ ψ₀.s) :=
        mem_saturatedClosure_of_mem S (S.comp_mem _ _ ht ψ₀.hs)
      refine ⟨{ s := t ≫ ψ₀.s, hs := hs, f := t ≫ ψ₀.f }, ?_⟩
      -- The refined numerator clears the localization ambiguity.
      simpa [Category.assoc] using hpre
    · intro X Y Y' f₁ f₂ s hs hEq
      -- A postcomposition witness in `S` for `s` reduces the equalization problem to the right
      -- calculus axiom already available for `S`.
      obtain ⟨Z, b, hb⟩ := exists_postcomp_mem_of_mem_saturatedClosure S hs
      obtain ⟨X', t, ht, hfac⟩ :=
        MorphismProperty.HasRightCalculusOfFractions.ext (W := S) f₁ f₂ (s ≫ b) hb
          (by simpa [Category.assoc] using congrArg (fun k ↦ k ≫ b) hEq)
      exact ⟨X', t, mem_saturatedClosure_of_mem S ht, hfac⟩
  · intro X0 X1 X2 X3 f g h hfg hgh
    -- A left witness from `f ≫ g` and a right witness from `g ≫ h` are exactly the data needed
    -- to show that `g` lies in the textbook characterization of the saturated closure.
    obtain ⟨Zl, a, ha⟩ := exists_precomp_mem_of_mem_saturatedClosure S hfg
    obtain ⟨Zr, b, hb⟩ := exists_postcomp_mem_of_mem_saturatedClosure S hgh
    rw [saturatedClosure_eq S]
    refine ⟨Zr, Zl, h ≫ b, a ≫ f, ?_, ?_⟩
    · simpa [Category.assoc] using hb
    · simpa [Category.assoc] using ha

/- The owner `S.saturatedClosure` is the smallest saturated multiplicative system containing `S`.
-/
theorem saturatedClosure_le_iff
    {T : MorphismProperty C} [IsSaturatedMultiplicativeSystem T] :
    S.saturatedClosure ≤ T ↔ S ≤ T := by
  constructor
  · intro h
    exact
      ((IsInvertedBy.iff_le_inverseImage_isomorphisms S S.Q).1 S.Q_inverts).trans h
  · intro hST
    rw [saturatedClosure_eq S]
    intro X Y f hf
    rcases hf with ⟨Z₁, Z₂, g, h, hfg, hhf⟩
    exact IsSaturatedMultiplicativeSystem.saturation h f g (hST _ hhf) (hST _ hfg)

/- The owner `S.saturatedClosure` lies in every saturated multiplicative system containing `S`. -/
theorem saturatedClosure_le
    {T : MorphismProperty C} [IsSaturatedMultiplicativeSystem T] (hST : S ≤ T) :
    S.saturatedClosure ≤ T :=
  (saturatedClosure_le_iff S).2 hST

end MorphismProperty
end CategoryTheory
