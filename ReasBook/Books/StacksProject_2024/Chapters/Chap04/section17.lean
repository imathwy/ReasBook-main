import Mathlib
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Final.Connected
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_17_1 (from Chap04) -/
universe vI vJ uI uJ

namespace CategoryTheory
namespace Functor

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]

/- Domain-style sampling for Definition 4.17.1:
- primary domain: final/cofinal functors and connected structured-arrow categories.
- inspected owner declarations:
  `CategoryTheory.Functor.Final`,
  `CategoryTheory.IsConnected`,
  `CategoryTheory.isConnected_iff_nonempty_and_zigzag`.
- owner abstraction: the mathlib class `Functor.Final`.
- primitive data: for each `y : J`, the connectedness witness `IsConnected (StructuredArrow y H)`.
- derived API: the source-facing nonemptiness-and-zigzag characterization of each
  `StructuredArrow y H`.

Source/core/bridge triage:
- `source-facing`: the textbook description by existence of an object over `y` and zigzag
  connectivity between any two such objects;
- `core/canonical`: `Functor.Final`;
- `bridge/view`: `final_iff_nonempty_structuredArrow_and_zigzag`.

This item should therefore keep `Functor.Final` as the main owner entry and expose the textbook
zigzag formulation only as a companion theorem. -/

/- Definition 4.17.1: a functor `H : I ⥤ J` is cofinal when for every object `y : J`, the
category of pairs `(x, y ⟶ H.obj x)` is connected; this is the canonical mathlib class
`CategoryTheory.Functor.Final`. -/
recall Final

/-- Bridge/view companion to Definition 4.17.1: the textbook zigzag description of a cofinal
functor says that for each `y : J`, there is at least one morphism `y ⟶ H.obj x`, and any two
such pairs `(x, y ⟶ H.obj x)` are connected by a zigzag of morphisms in `StructuredArrow y H`. -/
-- Proof sketch: unwind `Functor.Final` as connectedness of each `StructuredArrow y H`, then use
-- the standard zigzag characterization of connected categories from Definition `4.16.1`.
theorem final_iff_nonempty_structuredArrow_and_zigzag (H : I ⥤ J) :
    H.Final ↔
      ∀ y : J,
        Nonempty (StructuredArrow y H) ∧
          ∀ a b : StructuredArrow y H, Zigzag a b := by
  constructor
  · intro h y
    simpa using isConnected_iff_nonempty_and_zigzag.mp (h.out y)
  · intro h
    exact ⟨fun y ↦ isConnected_iff_nonempty_and_zigzag.mpr (h y)⟩

end Functor
end CategoryTheory

/-! ### Lemma_4_17_2 (from Chap04) -/
open CategoryTheory

/- Domain-style sampling for Lemma 4.17.2:
- primary domain: final functors and colimit comparison along whiskering.
- sampled owner declarations:
  `Functor.Final.colimit_pre_isIso`,
  `Functor.Final.hasColimit_comp_iff`,
  `Functor.Final.colimitIso`,
  `Functor.Final.hasColimit_of_comp`.
- best owner abstraction: `Functor.Final`.
- primitive-vs-derived split:
  primitive source data: finality of `H : I ⥤ J`;
  derived API: the comparison morphism `colimit.pre M H`, its `IsIso` instance, and the induced
    colimit-existence equivalence for `H ⋙ M`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement about the canonical comparison morphism and colimit
  existence along a final functor;
- `core/canonical`: `Functor.Final`;
- `bridge/view`: the two direct owner recalls below. -/

/- Lemma 4.17.2: if `H : I ⥤ J` is final and `M : J ⥤ C` has a colimit, then the canonical
comparison morphism `colimit.pre M H : colimit (H ⋙ M) ⟶ colimit M` is an isomorphism. This is
exactly the canonical instance `Functor.Final.colimit_pre_isIso`. -/
recall Functor.Final.colimit_pre_isIso

/- Companion to Lemma 4.17.2: for a final functor `H : I ⥤ J`, the composite diagram `H ⋙ M`
has a colimit if and only if `M` does. This is exactly the canonical theorem
`Functor.Final.hasColimit_comp_iff`. -/
recall Functor.Final.hasColimit_comp_iff

/-! ### Definition_4_17_3 (from Chap04) -/
universe vI vJ uI uJ

namespace CategoryTheory
namespace Functor

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]

/- Domain-style sampling for Definition 4.17.3:
- primary domain: initial functors and connected costructured-arrow categories.
- inspected owner/bridge declarations:
  `CategoryTheory.Functor.Initial`,
  `CategoryTheory.IsConnected`,
  `CategoryTheory.isConnected_iff_nonempty_and_zigzag`,
  `final_iff_nonempty_structuredArrow_and_zigzag`.
- best owner abstraction: `Functor.Initial`.
- primitive-vs-derived split:
  primitive data: for each `y : J`, the connectedness witness
    `IsConnected (CostructuredArrow H y)` stored by the owner `Functor.Initial`;
  derived API: the source-facing nonemptiness-and-zigzag criterion for
    `CostructuredArrow H y`.
- layer triage:
  - `source-facing`: the objectwise nonempty-and-zigzag criterion for `CostructuredArrow H y`;
  - `core/canonical`: `Functor.Initial`;
  - `bridge/view`: `initial_iff_nonempty_costructuredArrow_and_zigzag`.

This item should therefore keep `Functor.Initial` as the main owner entry and expose the
textbook zigzag formulation only as a companion theorem. -/

/- Definition 4.17.3: a functor `H : I ⥤ J` is initial when for every object `y : J`, the
category of arrows `H.obj x ⟶ y` is connected. This is the canonical mathlib class
`Functor.Initial`. -/
recall Initial

/-- Bridge/view companion to Definition 4.17.3: the textbook zigzag description of an initial
functor says that for each `y : J`, there is at least one morphism `H.obj x ⟶ y`, and any two
such pairs `(x, H.obj x ⟶ y)` are connected by a zigzag of morphisms in
`CostructuredArrow H y`. -/
-- Proof sketch: unwind `Functor.Initial` as connectedness of each `CostructuredArrow H y`, then
-- use the standard zigzag characterization of connected categories from Definition `4.16.1`.
theorem initial_iff_nonempty_costructuredArrow_and_zigzag (H : I ⥤ J) :
    H.Initial ↔
      ∀ y : J,
        Nonempty (CostructuredArrow H y) ∧ ∀ a b : CostructuredArrow H y, Zigzag a b := by
  constructor
  · intro h y
    simpa using isConnected_iff_nonempty_and_zigzag.mp (h.out y)
  · intro h
    exact ⟨fun y ↦ isConnected_iff_nonempty_and_zigzag.mpr (h y)⟩

end Functor
end CategoryTheory

/-! ### Lemma_4_17_4 (from Chap04) -/
universe vI vJ vC uI uJ uC

namespace CategoryTheory
namespace Functor

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

/- Domain-style sampling for Lemma 4.17.4:
- primary domain: limit comparison along initial functors in `CategoryTheory.Limits`;
- sampled owner API:
  `Functor.Initial.limitIso`,
  `Functor.Initial.hasLimit_comp_iff`,
  `Functor.Initial.hasLimit_of_comp`,
  `Functor.Final.colimitIso`;
- best owner abstraction: `Functor.Initial`;
- primitive-vs-derived split:
  primitive data: a functor `H : I ⥤ J` equipped with `H.Initial`;
  derived API: transfer of limit existence along `H` and the canonical comparison isomorphism on
    limits;
- layer triage:
  - `core/canonical`: `Functor.Initial`;
  - derived owner API: `Functor.Initial.hasLimit_of_comp`,
    `Functor.Initial.hasLimit_comp_iff`, and `Functor.Initial.limitIso`;
  - this item needs no separate `source-facing` wrapper, because Lemma 4.17.4 is exactly the
    canonical owner theorem. -/

/- Lemma 4.17.4: if `H : I ⥤ J` is initial and `M : J ⥤ C` has a limit, then the induced map
on limits is a canonical isomorphism. This is exactly the owner theorem
`Functor.Initial.limitIso`. -/
recall Initial.limitIso

end Functor
end CategoryTheory

/-! ### Lemma_4_17_5 (from Chap04) -/
open CategoryTheory
open CategoryTheory.Limits

universe vI vJ vC uI uJ uC

namespace CategoryTheory
namespace Functor

open Fiber IsHomLift

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

variable (F : I ⥤ J)

private def fiberToStructuredArrow {X Y : J} (f : X ⟶ Y) : F.Fiber Y ⥤ StructuredArrow X F where
  obj a := StructuredArrow.mk (f ≫ eqToHom a.2.symm)
  map {a b} φ := StructuredArrow.homMk φ.1 <| by
    let _ : F.IsHomLift (𝟙 Y) φ.1 := by
      simpa using (show F.IsHomLift (𝟙 Y) (Fiber.fiberInclusion.map φ) from inferInstance)
    have hfac : F.map φ.1 = eqToHom a.2 ≫ 𝟙 Y ≫ eqToHom b.2.symm :=
      @IsHomLift.fac' _ _ _ _ F _ _ _ _ (𝟙 Y) φ.1 inferInstance
    simpa [Category.assoc] using
      congrArg (fun k ↦ (StructuredArrow.mk (f ≫ eqToHom a.2.symm)).hom ≫ k) hfac

private def homLiftToStructuredArrow {X Y : J} {a b : I} (f : X ⟶ Y) (g : a ⟶ b)
    [F.IsHomLift f g] :
    (fiberToStructuredArrow F (𝟙 X)).obj (Fiber.mk (IsHomLift.domain_eq F f g)) ⟶
      (fiberToStructuredArrow F f).obj (Fiber.mk (IsHomLift.codomain_eq F f g)) :=
  StructuredArrow.homMk g <| by
    simpa [fiberToStructuredArrow, Category.assoc] using
      congrArg (fun k ↦ eqToHom (IsHomLift.domain_eq F f g).symm ≫ k) (IsHomLift.fac' F f g)

/-
Source/core/bridge triage for Lemma 4.17.5:
- `source-facing`: the Stacks criterion that connected fibers together with arrow-lifting imply
  that `F` is final.
- `core/canonical`: `Functor.Final`, with owner API `Functor.Final.hasColimit_comp_iff` and
  `Functor.Final.colimitIso`.
- `bridge/view`: the anonymous owner-specializations below, which expose the colimit
  consequences directly through the owner API after installing the finality instance.

Primary domain-style sampling:
- project owner recall: `Functor.Final.hasColimit_comp_iff` in `Lemma_4_17_2`;
- project specialization of the same owner API: `Prod.snd` in `Lemma_4_17_6`;
- mathlib owner abstraction: `Functor.Final` in
  `Mathlib/CategoryTheory/Limits/Final.lean`;
- mathlib connected bridge example: `final_snd` in
  `Mathlib/CategoryTheory/Limits/Final/Connected.lean`.

Primitive data are exactly the hypotheses `hfiber` and `hlift`; the colimit-comparison facts
below are derived API once `F.Final` is available. -/
variable
    (hfiber : ∀ j : J, IsConnected (F.Fiber j))
    (hlift : ∀ ⦃X Y : J⦄ (f : X ⟶ Y), ∃ (a b : I) (g : a ⟶ b), F.IsHomLift f g)

include hfiber hlift

/-- Companion bridge for Lemma 4.17.5: the fibre-connectedness and morphism-lifting hypotheses
imply that `F` is final.

Proof sketch: show that each structured-arrow category `StructuredArrow y F` is connected. Use the
connected fibre over `y` to compare objects lying above `y`, and use the hypothesis that every
arrow in `J` lifts through `F` to connect an arbitrary object of `StructuredArrow y F` to one in
the fibre over `y`. -/
theorem final_of_connected_fibers_and_hom_lifts : F.Final := by
  constructor
  intro j
  letI : IsConnected (F.Fiber j) := hfiber j
  letI : Nonempty (StructuredArrow j F) :=
    ⟨(fiberToStructuredArrow F (𝟙 j)).obj (Classical.arbitrary (F.Fiber j))⟩
  apply zigzag_isConnected
  intro A B
  obtain ⟨aA, bA, gA, hgA⟩ := hlift A.hom
  obtain ⟨aB, bB, gB, hgB⟩ := hlift B.hom
  have hdomA : F.obj aA = j :=
    @IsHomLift.domain_eq _ _ _ _ F _ _ _ _ A.hom gA hgA
  have hcodA : F.obj bA = F.obj A.right :=
    @IsHomLift.codomain_eq _ _ _ _ F _ _ _ _ A.hom gA hgA
  have hdomB : F.obj aB = j :=
    @IsHomLift.domain_eq _ _ _ _ F _ _ _ _ B.hom gB hgB
  have hcodB : F.obj bB = F.obj B.right :=
    @IsHomLift.codomain_eq _ _ _ _ F _ _ _ _ B.hom gB hgB
  have hsource :
      Zigzag
        ((fiberToStructuredArrow F (𝟙 j)).obj (Fiber.mk hdomA))
        ((fiberToStructuredArrow F (𝟙 j)).obj (Fiber.mk hdomB)) := by
    simpa [fiberToStructuredArrow] using
      zigzag_obj_of_zigzag (fiberToStructuredArrow F (𝟙 j))
        (isPreconnected_zigzag (Fiber.mk hdomA) (Fiber.mk hdomB))
  have hA :
      Zigzag
        ((fiberToStructuredArrow F (𝟙 j)).obj (Fiber.mk hdomA))
        A := by
    letI : IsConnected (F.Fiber (F.obj A.right)) := hfiber (F.obj A.right)
    let _ : F.IsHomLift A.hom gA := hgA
    let A₁ : F.Fiber (F.obj A.right) := Fiber.mk rfl
    have hA' :
        Zigzag
          ((fiberToStructuredArrow F (𝟙 j)).obj (Fiber.mk hdomA))
          ((fiberToStructuredArrow F A.hom).obj A₁) := by
      refine (Zigzag.of_hom (homLiftToStructuredArrow F A.hom gA)).trans ?_
      simpa [fiberToStructuredArrow] using
        zigzag_obj_of_zigzag (fiberToStructuredArrow F A.hom)
          (isPreconnected_zigzag (Fiber.mk hcodA) A₁)
    have hAend :
        ((fiberToStructuredArrow F A.hom).obj A₁) ⟶
          StructuredArrow.mk A.hom := by
      refine StructuredArrow.homMk (𝟙 A.right) ?_
      dsimp [fiberToStructuredArrow]
      have hp : A₁.2 = rfl :=
        Subsingleton.elim _ _
      have hEq :
          eqToHom A₁.2.symm = 𝟙 (F.obj A.right) := by
        cases hp
        rfl
      have hmap : F.map (𝟙 A.right) = 𝟙 (F.obj A.right) := by
        simpa using F.map_id A.right
      rw [hEq]
      have hmap' :
          A.hom ≫ 𝟙 (F.obj A.right) ≫ F.map (𝟙 A.right) =
            A.hom ≫ 𝟙 (F.obj A.right) ≫ 𝟙 (F.obj A.right) := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ A.hom ≫ 𝟙 (F.obj A.right) ≫ k) hmap
      have hmap'' :
          (A.hom ≫ 𝟙 (F.obj A.right)) ≫ F.map (𝟙 A.right) =
            (A.hom ≫ 𝟙 (F.obj A.right)) ≫ 𝟙 (F.obj A.right) := by
        simpa [Category.assoc] using hmap'
      exact hmap''.trans (by simp)
    rw [StructuredArrow.eq_mk A]
    exact hA'.trans (Zigzag.of_hom hAend)
  have hB :
      Zigzag
        ((fiberToStructuredArrow F (𝟙 j)).obj (Fiber.mk hdomB))
        B := by
    letI : IsConnected (F.Fiber (F.obj B.right)) := hfiber (F.obj B.right)
    let _ : F.IsHomLift B.hom gB := hgB
    let B₁ : F.Fiber (F.obj B.right) := Fiber.mk rfl
    have hB' :
        Zigzag
          ((fiberToStructuredArrow F (𝟙 j)).obj (Fiber.mk hdomB))
          ((fiberToStructuredArrow F B.hom).obj B₁) := by
      refine (Zigzag.of_hom (homLiftToStructuredArrow F B.hom gB)).trans ?_
      simpa [fiberToStructuredArrow] using
        zigzag_obj_of_zigzag (fiberToStructuredArrow F B.hom)
          (isPreconnected_zigzag (Fiber.mk hcodB) B₁)
    have hBend :
        ((fiberToStructuredArrow F B.hom).obj B₁) ⟶
          StructuredArrow.mk B.hom := by
      refine StructuredArrow.homMk (𝟙 B.right) ?_
      dsimp [fiberToStructuredArrow]
      have hp : B₁.2 = rfl :=
        Subsingleton.elim _ _
      have hEq :
          eqToHom B₁.2.symm = 𝟙 (F.obj B.right) := by
        cases hp
        rfl
      have hmap : F.map (𝟙 B.right) = 𝟙 (F.obj B.right) := by
        simpa using F.map_id B.right
      rw [hEq]
      have hmap' :
          B.hom ≫ 𝟙 (F.obj B.right) ≫ F.map (𝟙 B.right) =
            B.hom ≫ 𝟙 (F.obj B.right) ≫ 𝟙 (F.obj B.right) := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ B.hom ≫ 𝟙 (F.obj B.right) ≫ k) hmap
      have hmap'' :
          (B.hom ≫ 𝟙 (F.obj B.right)) ≫ F.map (𝟙 B.right) =
            (B.hom ≫ 𝟙 (F.obj B.right)) ≫ 𝟙 (F.obj B.right) := by
        simpa [Category.assoc] using hmap'
      exact hmap''.trans (by simp)
    rw [StructuredArrow.eq_mk B]
    exact hB'.trans (Zigzag.of_hom hBend)
  exact (hA.symm.trans hsource).trans hB

/-
Under the hypotheses of Lemma 4.17.5, the colimit comparison statements are not new local owners:
they are the direct owner-level consequences of `Functor.Final`.
-/
section

variable (M : J ⥤ C)

/- Lemma 4.17.5 also yields the standard colimit-existence comparison along `F`; this is the
specialization of `Functor.Final.hasColimit_comp_iff` after installing the finality instance from
the source-facing criterion above. -/
#check
  (by
    let _ : F.Final := final_of_connected_fibers_and_hom_lifts F hfiber hlift
    exact (Functor.Final.hasColimit_comp_iff F : HasColimit (F ⋙ M) ↔ HasColimit M))

variable [HasColimit M]

/- Under the same hypotheses, the induced comparison of colimits is exactly the owner isomorphism
`Functor.Final.colimitIso`. -/
#check
  (by
    let _ : F.Final := final_of_connected_fibers_and_hom_lifts F hfiber hlift
    exact (Functor.Final.colimitIso F M : colimit (F ⋙ M) ≅ colimit M))

end

omit hfiber hlift

end Functor
end CategoryTheory

/-! ### Lemma_4_17_6 (from Chap04) -/
open CategoryTheory.Limits

universe uI uJ uC vI vJ vC

namespace CategoryTheory

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable [IsConnected I]

/-
Source/core/bridge triage for Lemma 4.17.6:
- `source-facing`: the colimit-existence comparison, together with the resulting canonical
  colimit comparison isomorphism, for pulling a diagram back along `Prod.snd I J`.
- `core/canonical`: `Functor.Final.hasColimit_comp_iff` and `Functor.Final.colimitIso`.
- `bridge/view`: the instance `CategoryTheory.final_snd`, obtained from `[IsConnected I]`.

Primary domain-style sampling:
- project owner recall: `Functor.Final.hasColimit_comp_iff` in `Lemma_4_17_2`;
- project source-facing bridge from explicit finality criteria:
  `Functor.final_of_connected_fibers_and_hom_lifts` in `Lemma_4_17_5`;
- mathlib owner theorem: `Functor.Final.hasColimit_comp_iff` in
  `Mathlib/CategoryTheory/Limits/Final.lean`;
- mathlib bridge/view instance: `final_snd` in
  `Mathlib/CategoryTheory/Limits/Final/Connected.lean`.
-/

/- Companion recall: if `I` is connected, then the second projection `Prod.snd I J : I × J ⥤ J`
is final. -/
recall final_snd

section

variable (M : J ⥤ C)

/- Lemma 4.17.6: if `I` is connected, then for a diagram `M : J ⥤ C` the colimit of `M` exists
if and only if the colimit of its pullback along the second projection `Prod.snd I J : I × J ⥤ J`
exists. This is exactly the specialized owner theorem `Functor.Final.hasColimit_comp_iff` for the
final functor `Prod.snd I J`; the companion entry below records the resulting canonical colimit
comparison isomorphism. -/
#check (Functor.Final.hasColimit_comp_iff (Prod.snd I J) :
  HasColimit (Prod.snd I J ⋙ M) ↔ HasColimit M)

/- The corresponding colimit comparison isomorphism is exactly the specialized owner declaration
`Functor.Final.colimitIso` for `Prod.snd I J`. -/
variable [HasColimit M]

#check (Functor.Final.colimitIso (Prod.snd I J) M :
  colimit (Prod.snd I J ⋙ M) ≅ colimit M)

end

end CategoryTheory
