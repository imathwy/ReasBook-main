import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_14_26_9 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Augmented
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

open Arrow.AugmentedCechNerve

variable {C : Type u} [Category.{v} C]
variable {X Y : C} (f : Y ⟶ X)
variable [∀ n : ℕ, HasWidePullback (Arrow.mk f).right
  (fun _ : Fin (n + 1) ↦ (Arrow.mk f).left) (fun _ ↦ (Arrow.mk f).hom)]
variable (s : X ⟶ Y) (hs : s ≫ f = 𝟙 X)

/- Domain-style sampling for Lemma 14.26.9:
- primary domain: Čech nerves of split epimorphisms, viewed through the augmented simplicial
  object owner and its extra degeneracy;
- sampled owner declarations:
  `Arrow.cechNerve`,
  `Arrow.augmentedCechNerve`,
  `Arrow.mapCechNerve`,
  `Arrow.AugmentedCechNerve.extraDegeneracy`,
  `SimplicialObject.Augmented.ExtraDegeneracy.section_comp_hom`;
- best owner abstraction: the source-facing endomorphism is the canonical
  `Arrow.mapCechNerve` map induced by the arrow endomorphism `(f ≫ s, 𝟙_X)`, while the
  augmentation-section composite on `(Arrow.mk f).augmentedCechNerve` is owner-level bridge data
  coming from the extra degeneracy;
- primitive data: the arrow `f : Y ⟶ X` together with the concrete split-epimorphism witness
  `s : X ⟶ Y`, `hs : s ≫ f = 𝟙 X`;
- derived API: the augmentation `(Arrow.mk f).augmentedCechNerve.hom`, the simplicial section from
  `ExtraDegeneracy.section_`, the companion identification with `Arrow.mapCechNerve`, and the
  resulting simplicial homotopy to the identity.

Source/core/bridge triage:
- `source-facing`: the Čech-nerve endomorphism induced by the idempotent `f ≫ s` and its
  simplicial homotopy to the identity;
- `core/canonical`: the augmented Čech-nerve owner `(Arrow.mk f).augmentedCechNerve`, its
  augmentation morphism, and the canonical extra degeneracy
  `Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk f)` built from the chosen split-epimorphism
  data;
- `bridge/view`: the owner-derived simplicial section of the augmentation together with its
  identification with the textbook `Arrow.mapCechNerve` endomorphism.
-/

private def cechNerveSectionEndomorphismArrowHom (hs : s ≫ f = 𝟙 X) :
    Arrow.mk f ⟶ Arrow.mk f :=
  Arrow.homMk (f ≫ s) (𝟙 X)
    (by simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) hs)

private theorem homCompSection_eq_mapCechNerve_sectionEndomorphism (hs : s ≫ f = 𝟙 X) :
    let S : SplitEpi f := { section_ := s, id := hs }
    let ed : ExtraDegeneracy ((Arrow.mk f).augmentedCechNerve) :=
      extraDegeneracy (Arrow.mk f) S
    (Arrow.mk f).augmentedCechNerve.hom ≫ ed.section_ =
      Arrow.mapCechNerve (cechNerveSectionEndomorphismArrowHom f s hs) := by
  let S : SplitEpi f := { section_ := s, id := hs }
  let ed : ExtraDegeneracy ((Arrow.mk f).augmentedCechNerve) :=
    extraDegeneracy (Arrow.mk f) S
  change (Arrow.mk f).augmentedCechNerve.hom ≫ ed.section_ =
      Arrow.mapCechNerve (cechNerveSectionEndomorphismArrowHom f s hs)
  ext n : 2
  have hfrom :
      SimplexCategory.isTerminalZero.from (Opposite.unop n) =
        SimplexCategory.const _ _ 0 :=
    SimplexCategory.eq_const_to_zero _
  apply WidePullback.hom_ext
  · intro i
    simp [ed, S, cechNerveSectionEndomorphismArrowHom, extraDegeneracy,
      ExtraDegeneracy.section_, hfrom,
      WidePullback.lift_π, Category.assoc]
  · simp [ed, S, cechNerveSectionEndomorphismArrowHom, extraDegeneracy,
      ExtraDegeneracy.section_, hfrom,
      WidePullback.lift_base, Category.assoc, hs]

/-- Helper for Lemma 14.26.9: the degree-`n` Čech-nerve base map. -/
private noncomputable def cechNerveBase (n : ℕ) :
    (Arrow.mk f).cechNerve.obj (Opposite.op (SimplexCategory.mk n)) ⟶ X :=
  WidePullback.base (B := (Arrow.mk f).right)
    (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left) (arrows := fun _ ↦ (Arrow.mk f).hom)

/-- Helper for Lemma 14.26.9: the named Čech-nerve base map is the canonical
`WidePullback.base`. -/
private theorem cechNerveBase_eq_widePullback_base (n : ℕ) :
    cechNerveBase f n =
      WidePullback.base (B := (Arrow.mk f).right)
        (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left)
        (arrows := fun _ ↦ (Arrow.mk f).hom) :=
  rfl

/-- Helper for Lemma 14.26.9: the `k`-th projection from the degree-`n` Čech nerve. -/
private noncomputable def cechNerveProjection (n : ℕ) (k : Fin (n + 1)) :
    (Arrow.mk f).cechNerve.obj (Opposite.op (SimplexCategory.mk n)) ⟶ Y :=
  WidePullback.π (B := (Arrow.mk f).right)
    (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left) (arrows := fun _ ↦ (Arrow.mk f).hom) k

/-- Helper for Lemma 14.26.9: the named Čech-nerve projection is the canonical
`WidePullback.π`. -/
private theorem cechNerveProjection_eq_widePullback_pi (n : ℕ) (k : Fin (n + 1)) :
    cechNerveProjection f n k =
      WidePullback.π (B := (Arrow.mk f).right)
        (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left)
        (arrows := fun _ ↦ (Arrow.mk f).hom) k :=
  rfl

/-- Helper for Lemma 14.26.9: the `k`-th projection used in the explicit split Čech-nerve
homotopy component. -/
private noncomputable def cechNerveSectionHomotopyProjection
    (n : ℕ) (j : Fin (n + 1)) (k : Fin (n + 2)) :
    (Arrow.mk f).cechNerve.obj (Opposite.op (SimplexCategory.mk n)) ⟶ Y :=
  if _hk : k ≤ j.castSucc then
    cechNerveBase f n ≫ s
  else
    cechNerveProjection f n (j.predAbove k)

/-- Helper for Lemma 14.26.9: every coordinate of the duplicated-component family lies over the
same base point of the Čech nerve. -/
private theorem cechNerveSectionHomotopyProjection_condition
    (hs : s ≫ f = 𝟙 X) (n : ℕ) (j : Fin (n + 1)) (k : Fin (n + 2)) :
    cechNerveSectionHomotopyProjection f s n j k ≫ f =
      cechNerveBase f n := by
  -- The duplicated coordinate either comes from the common base point or from an existing
  -- Čech projection, and both lie over the same base.
  dsimp [cechNerveSectionHomotopyProjection]
  split_ifs with hk
  · simp [cechNerveBase, Category.assoc, hs]
  · simpa [cechNerveBase, cechNerveProjection] using
      (WidePullback.π_arrow (B := (Arrow.mk f).right)
        (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left)
        (arrows := fun _ ↦ (Arrow.mk f).hom) (j := j.predAbove k))

/-- Helper for Lemma 14.26.9: the degree-`n` homotopy component inserts a duplicated coordinate at
the position indexed by `j`. -/
private noncomputable def cechNerveSectionHomotopyComponent
    (hs : s ≫ f = 𝟙 X) (n : ℕ) (j : Fin (n + 1)) :
    (Arrow.mk f).cechNerve.obj (Opposite.op (SimplexCategory.mk n)) ⟶
      (Arrow.mk f).cechNerve.obj (Opposite.op (SimplexCategory.mk (n + 1))) :=
  WidePullback.lift (cechNerveBase f n)
    (fun k => cechNerveSectionHomotopyProjection f s n j k)
    (fun k => cechNerveSectionHomotopyProjection_condition f s hs n j k)

/-- Helper for Lemma 14.26.9: the explicit homotopy component has the expected projection
formula. -/
@[reassoc]
private theorem cechNerveSectionHomotopyComponent_proj
    (hs : s ≫ f = 𝟙 X) (n : ℕ) (j : Fin (n + 1)) (k : Fin (n + 2)) :
    cechNerveSectionHomotopyComponent f s hs n j ≫ cechNerveProjection f (n + 1) k =
      cechNerveSectionHomotopyProjection f s n j k := by
  -- The explicit component was defined as a `WidePullback.lift`, so each projection is immediate.
  simpa [cechNerveSectionHomotopyComponent, cechNerveProjection] using
    (WidePullback.lift_π
      (B := (Arrow.mk f).right)
      (objs := fun _ : Fin (n + 2) ↦ (Arrow.mk f).left)
      (arrows := fun _ ↦ (Arrow.mk f).hom)
      (f := cechNerveBase f n)
      (fs := fun k => cechNerveSectionHomotopyProjection f s n j k)
      (w := fun k => cechNerveSectionHomotopyProjection_condition f s hs n j k)
      (j := k))

/-- Helper for Lemma 14.26.9: the duplicated-coordinate component preserves the Čech-nerve base
map. -/
@[reassoc]
private theorem cechNerveSectionHomotopyComponent_base
    (hs : s ≫ f = 𝟙 X) (n : ℕ) (j : Fin (n + 1)) :
    cechNerveSectionHomotopyComponent f s hs n j ≫ cechNerveBase f (n + 1) =
      cechNerveBase f n := by
  -- The base map of a `WidePullback.lift` is the map used to define the lift.
  simpa [cechNerveSectionHomotopyComponent, cechNerveBase] using
    (WidePullback.lift_base
      (B := (Arrow.mk f).right)
      (objs := fun _ : Fin (n + 2) ↦ (Arrow.mk f).left)
      (arrows := fun _ ↦ (Arrow.mk f).hom)
      (f := cechNerveBase f n)
      (fs := fun k => cechNerveSectionHomotopyProjection f s n j k)
      (w := fun k => cechNerveSectionHomotopyProjection_condition f s hs n j k))

/-- Helper for Lemma 14.26.9: on any chosen Čech coordinate, the common base followed by the
section agrees with the coordinatewise endomorphism induced by `f ≫ s`. -/
@[reassoc]
private theorem cechNerveSectionHomotopyProjection_left_block
    (n : ℕ) (k : Fin (n + 1)) :
    cechNerveBase f n ≫ s = cechNerveProjection f n k ≫ f ≫ s := by
  -- Rewrite the common base as the `k`-th projection followed by `f`, then postcompose by `s`.
  calc
    cechNerveBase f n ≫ s = (cechNerveProjection f n k ≫ f) ≫ s := by
      simp only [Category.assoc]
      simpa [cechNerveBase, cechNerveProjection] using
        (WidePullback.π_arrow (B := (Arrow.mk f).right)
          (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left)
          (arrows := fun _ ↦ (Arrow.mk f).hom) (j := k)).symm
    _ = cechNerveProjection f n k ≫ f ≫ s := by
      simp [Category.assoc]

/-- Helper for Lemma 14.26.9: every face map of the Čech nerve preserves the common base map. -/
@[reassoc]
private theorem cechNerveBase_comp_delta (n : ℕ) (i : Fin (n + 2)) :
    ((Arrow.mk f).cechNerve).δ i ≫ cechNerveBase f n =
      cechNerveBase f (n + 1) := by
  -- Unfold the Čech-nerve face map once and read off its base component.
  simpa [SimplicialObject.δ, Arrow.cechNerve, cechNerveBase, SimplexCategory.δ] using
    (WidePullback.lift_base
      (B := (Arrow.mk f).right)
      (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left)
      (arrows := fun _ ↦ (Arrow.mk f).hom)
      (f := WidePullback.base
        (B := (Arrow.mk f).right)
        (objs := fun _ : Fin (n + 2) ↦ (Arrow.mk f).left)
        (arrows := fun _ ↦ (Arrow.mk f).hom))
      (fs := fun k =>
        WidePullback.π (B := (Arrow.mk f).right)
          (objs := fun _ : Fin (n + 2) ↦ (Arrow.mk f).left)
          (arrows := fun _ ↦ (Arrow.mk f).hom) (i.succAbove k))
      (w := by
        intro k
        simpa [SimplexCategory.δ] using
          (WidePullback.π_arrow (B := (Arrow.mk f).right)
            (objs := fun _ : Fin (n + 2) ↦ (Arrow.mk f).left)
            (arrows := fun _ ↦ (Arrow.mk f).hom) (j := i.succAbove k))))

/-- Helper for Lemma 14.26.9: every degeneracy map of the Čech nerve preserves the common base
map. -/
@[reassoc]
private theorem cechNerveBase_comp_sigma (n : ℕ) (i : Fin (n + 1)) :
    ((Arrow.mk f).cechNerve).σ i ≫ cechNerveBase f (n + 1) =
      cechNerveBase f n := by
  -- Unfold the Čech-nerve degeneracy map once and read off its base component.
  simpa [SimplicialObject.σ, Arrow.cechNerve, cechNerveBase, SimplexCategory.σ] using
    (WidePullback.lift_base
      (B := (Arrow.mk f).right)
      (objs := fun _ : Fin (n + 2) ↦ (Arrow.mk f).left)
      (arrows := fun _ ↦ (Arrow.mk f).hom)
      (f := WidePullback.base
        (B := (Arrow.mk f).right)
        (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left)
        (arrows := fun _ ↦ (Arrow.mk f).hom))
      (fs := fun k =>
        WidePullback.π (B := (Arrow.mk f).right)
          (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left)
          (arrows := fun _ ↦ (Arrow.mk f).hom) (i.predAbove k))
      (w := by
        intro k
        simpa [SimplexCategory.σ] using
          (WidePullback.π_arrow (B := (Arrow.mk f).right)
            (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left)
            (arrows := fun _ ↦ (Arrow.mk f).hom) (j := i.predAbove k))))

/-- Helper for Lemma 14.26.9: composing a Čech face map with a named projection shifts the
projection index by `succAbove`. -/
@[reassoc]
private theorem cechNerveProjection_comp_delta
    (n : ℕ) (i : Fin (n + 2)) (k : Fin (n + 1)) :
    ((Arrow.mk f).cechNerve).δ i ≫ cechNerveProjection f n k =
      cechNerveProjection f (n + 1) (i.succAbove k) := by
  -- The face map of the Čech nerve is the `WidePullback.lift` induced by `succAbove`.
  simpa [SimplicialObject.δ, Arrow.cechNerve, cechNerveProjection, SimplexCategory.δ] using
    (WidePullback.lift_π
      (B := (Arrow.mk f).right)
      (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left)
      (arrows := fun _ ↦ (Arrow.mk f).hom)
      (f := WidePullback.base
        (B := (Arrow.mk f).right)
        (objs := fun _ : Fin (n + 2) ↦ (Arrow.mk f).left)
        (arrows := fun _ ↦ (Arrow.mk f).hom))
      (fs := fun t =>
        WidePullback.π (B := (Arrow.mk f).right)
          (objs := fun _ : Fin (n + 2) ↦ (Arrow.mk f).left)
          (arrows := fun _ ↦ (Arrow.mk f).hom) (i.succAbove t))
      (w := by
        intro t
        simpa [SimplexCategory.δ] using
          (WidePullback.π_arrow (B := (Arrow.mk f).right)
            (objs := fun _ : Fin (n + 2) ↦ (Arrow.mk f).left)
            (arrows := fun _ ↦ (Arrow.mk f).hom) (j := i.succAbove t)))
      (j := k))

/-- Helper for Lemma 14.26.9: composing a Čech degeneracy map with a named projection lowers the
projection index by `predAbove`. -/
@[reassoc]
private theorem cechNerveProjection_comp_sigma
    (n : ℕ) (i : Fin (n + 1)) (k : Fin (n + 2)) :
    ((Arrow.mk f).cechNerve).σ i ≫ cechNerveProjection f (n + 1) k =
      cechNerveProjection f n (i.predAbove k) := by
  -- The degeneracy map of the Čech nerve is the `WidePullback.lift` induced by `predAbove`.
  simpa [SimplicialObject.σ, Arrow.cechNerve, cechNerveProjection, SimplexCategory.σ] using
    (WidePullback.lift_π
      (B := (Arrow.mk f).right)
      (objs := fun _ : Fin (n + 2) ↦ (Arrow.mk f).left)
      (arrows := fun _ ↦ (Arrow.mk f).hom)
      (f := WidePullback.base
        (B := (Arrow.mk f).right)
        (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left)
        (arrows := fun _ ↦ (Arrow.mk f).hom))
      (fs := fun t =>
        WidePullback.π (B := (Arrow.mk f).right)
          (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left)
          (arrows := fun _ ↦ (Arrow.mk f).hom) (i.predAbove t))
      (w := by
        intro t
        simpa [SimplexCategory.σ] using
          (WidePullback.π_arrow (B := (Arrow.mk f).right)
            (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left)
            (arrows := fun _ ↦ (Arrow.mk f).hom) (j := i.predAbove t)))
      (j := k))

/-- Helper for Lemma 14.26.9: the coordinatewise endomorphism induced by `f ≫ s` acts on each
Čech projection by postcomposition with `f ≫ s`. -/
@[reassoc]
private theorem cechNerveSectionEndomorphism_app_proj
    (hs : s ≫ f = 𝟙 X) (n : ℕ) (k : Fin (n + 1)) :
    (Arrow.mapCechNerve (cechNerveSectionEndomorphismArrowHom f s hs)).app
        (Opposite.op (SimplexCategory.mk n)) ≫ cechNerveProjection f n k =
      cechNerveProjection f n k ≫ f ≫ s := by
  -- Each projection of `Arrow.mapCechNerve` is the corresponding source projection followed by
  -- the left component of the arrow morphism.
  simpa [Arrow.mapCechNerve, cechNerveProjection, cechNerveSectionEndomorphismArrowHom,
    Category.assoc] using
    (WidePullback.lift_π
      (B := (Arrow.mk f).right)
      (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left)
      (arrows := fun _ ↦ (Arrow.mk f).hom)
      (f := cechNerveBase f n ≫ 𝟙 (Arrow.mk f).right)
      (fs := fun t => cechNerveProjection f n t ≫ (Arrow.mk f).hom ≫ s)
      (w := by
        intro t
        simpa [cechNerveBase, cechNerveProjection, Category.assoc, hs] using
          congrArg (fun g => g ≫ s ≫ (Arrow.mk f).hom)
            (WidePullback.π_arrow (B := (Arrow.mk f).right)
              (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left)
              (arrows := fun _ ↦ (Arrow.mk f).hom) (j := t)))
      (j := k))

/-- Helper for Lemma 14.26.9: the coordinatewise endomorphism induced by `f ≫ s` preserves the
Čech-nerve base map. -/
@[reassoc]
private theorem cechNerveSectionEndomorphism_app_base
    (hs : s ≫ f = 𝟙 X) (n : ℕ) :
    (Arrow.mapCechNerve (cechNerveSectionEndomorphismArrowHom f s hs)).app
        (Opposite.op (SimplexCategory.mk n)) ≫ cechNerveBase f n =
      cechNerveBase f n := by
  -- The right component of the arrow endomorphism is `𝟙 X`, so the induced Čech map fixes base.
  simpa [Arrow.mapCechNerve, cechNerveBase, cechNerveProjection,
    cechNerveSectionEndomorphismArrowHom, Category.assoc, hs] using
    (WidePullback.lift_base
      (B := (Arrow.mk f).right)
      (objs := fun _ : Fin (n + 1) ↦ (Arrow.mk f).left)
      (arrows := fun _ ↦ (Arrow.mk f).hom)
      (f := cechNerveBase f n ≫ 𝟙 (Arrow.mk f).right)
      (fs := fun _ => cechNerveBase f n ≫ s)
      (w := by
        intro t
        simp [cechNerveBase, Category.assoc, hs]))

/-- Helper for Lemma 14.26.9: deleting the first duplicated coordinate recovers the identity
endomorphism of the Čech nerve. -/
private theorem cechNerveSectionHomotopy_h_zero_comp_δ_zero
    (hs : s ≫ f = 𝟙 X) (n : ℕ) :
    cechNerveSectionHomotopyComponent f s hs n 0 ≫ ((Arrow.mk f).cechNerve).δ 0 =
      𝟙 _ := by
  -- Route correction: after normalizing the Čech faces and projections, the endpoint identity
  -- is checked projectionwise on the target wide pullback.
  apply WidePullback.hom_ext
  · intro k
    calc
      (cechNerveSectionHomotopyComponent f s hs n 0 ≫ ((Arrow.mk f).cechNerve).δ 0) ≫
          cechNerveProjection f n k =
        cechNerveSectionHomotopyComponent f s hs n 0 ≫
          (((Arrow.mk f).cechNerve).δ 0 ≫ cechNerveProjection f n k) := by
            simp [Category.assoc]
      _ = cechNerveSectionHomotopyComponent f s hs n 0 ≫
          cechNerveProjection f (n + 1) ((0 : Fin (n + 2)).succAbove k) := by
            rw [cechNerveProjection_comp_delta]
      _ = cechNerveSectionHomotopyProjection f s n 0 ((0 : Fin (n + 2)).succAbove k) := by
            rw [cechNerveSectionHomotopyComponent_proj]
      _ = cechNerveProjection f n k := by
            simp [cechNerveSectionHomotopyProjection, cechNerveProjection, cechNerveBase]
      _ = 𝟙 _ ≫ cechNerveProjection f n k := by
            simp
  · calc
      (cechNerveSectionHomotopyComponent f s hs n 0 ≫ ((Arrow.mk f).cechNerve).δ 0) ≫
          cechNerveBase f n =
        cechNerveSectionHomotopyComponent f s hs n 0 ≫
          (((Arrow.mk f).cechNerve).δ 0 ≫ cechNerveBase f n) := by
            simp [Category.assoc]
      _ = cechNerveSectionHomotopyComponent f s hs n 0 ≫ cechNerveBase f (n + 1) := by
            rw [cechNerveBase_comp_delta]
      _ = cechNerveBase f n := by
            rw [cechNerveSectionHomotopyComponent_base]
      _ = 𝟙 _ ≫ cechNerveBase f n := by
            simp

/-- Helper for Lemma 14.26.9: deleting the last duplicated coordinate recovers the coordinatewise
endomorphism induced by `f ≫ s`. -/
private theorem cechNerveSectionHomotopy_h_last_comp_δ_last
    (hs : s ≫ f = 𝟙 X) (n : ℕ) :
    cechNerveSectionHomotopyComponent f s hs n (Fin.last n) ≫
        ((Arrow.mk f).cechNerve).δ (Fin.last (n + 1)) =
      (Arrow.mapCechNerve (cechNerveSectionEndomorphismArrowHom f s hs)).app
        (Opposite.op (SimplexCategory.mk n)) := by
  -- After deleting the last inserted slot, every projection lands in the left block and becomes
  -- the common base followed by the section.
  apply WidePullback.hom_ext
  · intro k
    calc
      (cechNerveSectionHomotopyComponent f s hs n (Fin.last n) ≫
          ((Arrow.mk f).cechNerve).δ (Fin.last (n + 1))) ≫ cechNerveProjection f n k =
        cechNerveSectionHomotopyComponent f s hs n (Fin.last n) ≫
          (((Arrow.mk f).cechNerve).δ (Fin.last (n + 1)) ≫ cechNerveProjection f n k) := by
            simp [Category.assoc]
      _ = cechNerveSectionHomotopyComponent f s hs n (Fin.last n) ≫
          cechNerveProjection f (n + 1) ((Fin.last (n + 1)).succAbove k) := by
            rw [cechNerveProjection_comp_delta]
      _ = cechNerveSectionHomotopyProjection f s n (Fin.last n) ((Fin.last (n + 1)).succAbove k) := by
            rw [cechNerveSectionHomotopyComponent_proj]
      _ = cechNerveBase f n ≫ s := by
            have hnot : ¬ Fin.last n < k := Fin.not_lt.mpr (Fin.le_last k)
            simpa [cechNerveSectionHomotopyProjection, Fin.succAbove_last, hnot]
      _ = cechNerveProjection f n k ≫ f ≫ s := by
            exact cechNerveSectionHomotopyProjection_left_block f s n k
      _ = (Arrow.mapCechNerve (cechNerveSectionEndomorphismArrowHom f s hs)).app
            (Opposite.op (SimplexCategory.mk n)) ≫ cechNerveProjection f n k := by
            symm
            rw [cechNerveSectionEndomorphism_app_proj]
  · calc
      (cechNerveSectionHomotopyComponent f s hs n (Fin.last n) ≫
          ((Arrow.mk f).cechNerve).δ (Fin.last (n + 1))) ≫ cechNerveBase f n =
        cechNerveSectionHomotopyComponent f s hs n (Fin.last n) ≫
          (((Arrow.mk f).cechNerve).δ (Fin.last (n + 1)) ≫ cechNerveBase f n) := by
            simp [Category.assoc]
      _ = cechNerveSectionHomotopyComponent f s hs n (Fin.last n) ≫ cechNerveBase f (n + 1) := by
            rw [cechNerveBase_comp_delta]
      _ = cechNerveBase f n := by
            rw [cechNerveSectionHomotopyComponent_base]
      _ = (Arrow.mapCechNerve (cechNerveSectionEndomorphismArrowHom f s hs)).app
            (Opposite.op (SimplexCategory.mk n)) ≫ cechNerveBase f n := by
            symm
            rw [cechNerveSectionEndomorphism_app_base]

/-- Helper for Lemma 14.26.9: under `i ≤ j.castSucc`, deleting the face at `i.castSucc`
preserves the left duplicated block exactly on the indices that were already in that block. -/
private theorem fin_face_left_duplication_mem_left_iff
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) (k : Fin (n + 2)) :
    i.castSucc.succAbove k ≤ j.succ.castSucc ↔ k ≤ j.castSucc := by
  -- Both inequalities are arithmetic once `succAbove` is expanded into its two branches.
  apply Iff.intro
  · intro hk
    by_cases hik : i ≤ k
    · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hik)] at hk
      rw [Fin.succ_le_castSucc_iff] at hk
      exact Fin.le_castSucc_iff.mpr hk
    · rw [Fin.not_le] at hik
      rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hik)] at hk
      exact le_trans (Fin.le_of_lt hik) hij
  · intro hk
    by_cases hik : i ≤ k
    · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hik)]
      rw [Fin.succ_le_castSucc_iff]
      exact Fin.succ_le_castSucc_iff.mpr (Fin.le_castSucc_iff.mp hk)
    · rw [Fin.not_le] at hik
      rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hik)]
      exact Fin.castSucc_le_castSucc_iff.mpr (le_trans hk j.castSucc_le_succ)

/-- Helper for Lemma 14.26.9: under `i ≤ j.castSucc`, deleting the face at `i.castSucc`
commutes with removing the duplicated coordinate outside the left block. -/
private theorem fin_face_left_duplication_normalization
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) (k : Fin (n + 2))
    (hk : ¬ k ≤ j.castSucc) :
    j.succ.predAbove (i.castSucc.succAbove k) = i.succAbove (j.predAbove k) := by
  -- This is a pure `Fin` identity, so we reduce it to arithmetic on values.
  apply Fin.ext
  have hij' : i.1 ≤ j.1 := hij
  have hkj : j.1 < k.1 := by
    simpa [Fin.lt_def] using (lt_of_not_ge hk : j.castSucc < k)
  simp only [Fin.predAbove, Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.val_castSucc,
    apply_dite Fin.val, dite_eq_ite, apply_ite Fin.val, Fin.val_pred, Fin.coe_castPred,
    Fin.val_succ]
  split_ifs <;> omega

/-- Helper for Lemma 14.26.9: when the removed face lies before the duplicated coordinate, the
explicit Čech-nerve components satisfy the left simplicial-homotopy face identity. -/
private theorem cechNerveSectionHomotopy_h_succ_comp_δ_castSucc_of_lt
    (hs : s ≫ f = 𝟙 X) {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) :
    cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
        ((Arrow.mk f).cechNerve).δ i.castSucc =
      ((Arrow.mk f).cechNerve).δ i ≫ cechNerveSectionHomotopyComponent f s hs n j := by
  -- Route correction: the remaining work is purely branchwise, so we rewrite projections and
  -- bases explicitly and discharge each branch with the local `Fin` normalizers above.
  apply WidePullback.hom_ext
  · intro k
    by_cases hk : k ≤ j.castSucc
    · calc
        (cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
            ((Arrow.mk f).cechNerve).δ i.castSucc) ≫
            cechNerveProjection f (n + 1) k =
          cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
            cechNerveProjection f (n + 2) (i.castSucc.succAbove k) := by
              rw [Category.assoc, cechNerveProjection_comp_delta]
        _ = cechNerveSectionHomotopyProjection f s (n + 1) j.succ (i.castSucc.succAbove k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = cechNerveBase f (n + 1) ≫ s := by
              rw [cechNerveSectionHomotopyProjection]
              exact if_pos ((fin_face_left_duplication_mem_left_iff i j hij k).mpr hk)
        _ = ((Arrow.mk f).cechNerve).δ i ≫ (cechNerveBase f n ≫ s) := by
              simpa [Category.assoc] using
                congrArg (fun g ↦ g ≫ s) (cechNerveBase_comp_delta (f := f) (n := n) (i := i)).symm
        _ = ((Arrow.mk f).cechNerve).δ i ≫ cechNerveSectionHomotopyProjection f s n j k := by
              simp [cechNerveSectionHomotopyProjection, hk]
        _ = ((Arrow.mk f).cechNerve).δ i ≫
            (cechNerveSectionHomotopyComponent f s hs n j ≫ cechNerveProjection f (n + 1) k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = (((Arrow.mk f).cechNerve).δ i ≫ cechNerveSectionHomotopyComponent f s hs n j) ≫
            cechNerveProjection f (n + 1) k := by
              simp [Category.assoc]
    · calc
        (cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
            ((Arrow.mk f).cechNerve).δ i.castSucc) ≫
            cechNerveProjection f (n + 1) k =
          cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
            cechNerveProjection f (n + 2) (i.castSucc.succAbove k) := by
              rw [Category.assoc, cechNerveProjection_comp_delta]
        _ = cechNerveSectionHomotopyProjection f s (n + 1) j.succ (i.castSucc.succAbove k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = cechNerveProjection f (n + 1)
            (j.succ.predAbove (i.castSucc.succAbove k)) := by
              rw [cechNerveSectionHomotopyProjection]
              exact if_neg (fun hmem ↦ hk ((fin_face_left_duplication_mem_left_iff i j hij k).mp hmem))
        _ = cechNerveProjection f (n + 1) (i.succAbove (j.predAbove k)) := by
              rw [fin_face_left_duplication_normalization i j hij k hk]
        _ = ((Arrow.mk f).cechNerve).δ i ≫ cechNerveProjection f n (j.predAbove k) := by
              rw [cechNerveProjection_comp_delta]
        _ = ((Arrow.mk f).cechNerve).δ i ≫ cechNerveSectionHomotopyProjection f s n j k := by
              simp [cechNerveSectionHomotopyProjection, hk]
        _ = ((Arrow.mk f).cechNerve).δ i ≫
            (cechNerveSectionHomotopyComponent f s hs n j ≫ cechNerveProjection f (n + 1) k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = (((Arrow.mk f).cechNerve).δ i ≫ cechNerveSectionHomotopyComponent f s hs n j) ≫
            cechNerveProjection f (n + 1) k := by
              simp [Category.assoc]
  · calc
      (cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
          ((Arrow.mk f).cechNerve).δ i.castSucc) ≫
          cechNerveBase f (n + 1) =
        cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫ cechNerveBase f (n + 2) := by
          rw [Category.assoc, cechNerveBase_comp_delta]
      _ = cechNerveBase f (n + 1) := by
          rw [cechNerveSectionHomotopyComponent_base]
      _ = ((Arrow.mk f).cechNerve).δ i ≫ cechNerveBase f n := by
          rw [cechNerveBase_comp_delta]
      _ = ((Arrow.mk f).cechNerve).δ i ≫
          (cechNerveSectionHomotopyComponent f s hs n j ≫ cechNerveBase f (n + 1)) := by
          rw [cechNerveSectionHomotopyComponent_base]
      _ = (((Arrow.mk f).cechNerve).δ i ≫ cechNerveSectionHomotopyComponent f s hs n j) ≫
          cechNerveBase f (n + 1) := by
          simp [Category.assoc]

/-- Helper for Lemma 14.26.9: deleting the right-hand adjacent face after inserting two
neighboring duplicated slots lands on the same surviving coordinate. -/
private theorem fin_adjacent_face_right_duplication_normalization
    {n : ℕ} (j : Fin (n + 1)) (k : Fin (n + 2)) :
    j.succ.predAbove (j.castSucc.succ.succAbove k) =
      j.castSucc.predAbove (j.castSucc.succ.succAbove k) := by
  -- Both adjacent simplicial identities collapse the surviving coordinate to `k`.
  calc
    j.succ.predAbove (j.castSucc.succ.succAbove k) = k := by
      simpa [SimplexCategory.δ, SimplexCategory.σ] using
        congr_fun (congrArg DFunLike.coe
          (congrArg SimplexCategory.Hom.toOrderHom
            (SimplexCategory.δ_comp_σ_self (i := j.succ)))) k
    _ = j.castSucc.predAbove (j.castSucc.succ.succAbove k) := by
      symm
      simpa [SimplexCategory.δ, SimplexCategory.σ] using
        congr_fun (congrArg DFunLike.coe
          (congrArg SimplexCategory.Hom.toOrderHom
            (SimplexCategory.δ_comp_σ_succ (i := j.castSucc)))) k

/-- Helper for Lemma 14.26.9: the adjacent face terms of the duplicated-coordinate family agree
exactly at the duplicated slot. -/
private theorem cechNerveSectionHomotopy_h_succ_comp_δ_castSucc_succ
    (hs : s ≫ f = 𝟙 X) {n : ℕ} (j : Fin (n + 1)) :
    cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
        ((Arrow.mk f).cechNerve).δ j.castSucc.succ =
      cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
        ((Arrow.mk f).cechNerve).δ j.castSucc.succ := by
  -- The two adjacent face deletions agree because they both delete one of the duplicated slots.
  apply WidePullback.hom_ext
  · intro k
    by_cases hk : k ≤ j.castSucc
    · calc
        (cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
            ((Arrow.mk f).cechNerve).δ j.castSucc.succ) ≫
            cechNerveProjection f (n + 1) k =
          cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
            cechNerveProjection f (n + 2) (j.castSucc.succ.succAbove k) := by
              rw [Category.assoc, cechNerveProjection_comp_delta]
        _ = cechNerveSectionHomotopyProjection f s (n + 1) j.succ (j.castSucc.succ.succAbove k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = cechNerveBase f (n + 1) ≫ s := by
              rw [cechNerveSectionHomotopyProjection]
              have hk' : j.castSucc.succ.succAbove k ≤ j.succ.castSucc := by
                rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr hk)]
                exact Fin.castSucc_le_castSucc_iff.mpr (le_trans hk j.castSucc_le_succ)
              exact if_pos hk'
        _ = cechNerveSectionHomotopyProjection f s (n + 1) j.castSucc (j.castSucc.succ.succAbove k) := by
              rw [cechNerveSectionHomotopyProjection]
              have hk' : j.castSucc.succ.succAbove k ≤ j.castSucc.castSucc := by
                rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr hk)]
                exact Fin.castSucc_le_castSucc_iff.mpr hk
              exact (if_pos hk').symm
        _ = cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
            cechNerveProjection f (n + 2) (j.castSucc.succ.succAbove k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = (cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
            ((Arrow.mk f).cechNerve).δ j.castSucc.succ) ≫
            cechNerveProjection f (n + 1) k := by
              rw [Category.assoc, cechNerveProjection_comp_delta]
    · by_cases hkj : k = j.succ
      · subst hkj
        calc
          (cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
              ((Arrow.mk f).cechNerve).δ j.castSucc.succ) ≫
              cechNerveProjection f (n + 1) j.succ =
            cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
              cechNerveProjection f (n + 2) (j.castSucc.succ.succAbove j.succ) := by
                rw [Category.assoc, cechNerveProjection_comp_delta]
          _ = cechNerveSectionHomotopyProjection f s (n + 1) j.succ
                (j.castSucc.succ.succAbove j.succ) := by
                rw [cechNerveSectionHomotopyComponent_proj]
          _ = cechNerveProjection f (n + 1)
                (j.succ.predAbove (j.castSucc.succ.succAbove j.succ)) := by
                rw [cechNerveSectionHomotopyProjection]
                have hk' : ¬ j.castSucc.succ.succAbove j.succ ≤ j.succ.castSucc := by
                  have hsucc : j.castSucc.succ.succAbove j.succ = j.succ.succ := by
                    simpa using (Fin.succAbove_succ_self j.castSucc)
                  rw [hsucc]
                  simpa using (show ¬ j.succ.succ ≤ j.succ.castSucc from by simp)
                exact if_neg hk'
          _ = cechNerveProjection f (n + 1)
                (j.castSucc.predAbove (j.castSucc.succ.succAbove j.succ)) := by
                rw [fin_adjacent_face_right_duplication_normalization]
          _ = cechNerveSectionHomotopyProjection f s (n + 1) j.castSucc
                (j.castSucc.succ.succAbove j.succ) := by
                rw [cechNerveSectionHomotopyProjection]
                have hk' : ¬ j.castSucc.succ.succAbove j.succ ≤ j.castSucc.castSucc := by
                  have hsucc : j.castSucc.succ.succAbove j.succ = j.succ.succ := by
                    simpa using (Fin.succAbove_succ_self j.castSucc)
                  rw [hsucc]
                  intro hle
                  have hlt : j.succ < j.castSucc := by
                    simpa [Fin.succ_le_castSucc_iff] using hle
                  exact hk hlt.le
                exact (if_neg hk').symm
          _ = cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
              cechNerveProjection f (n + 2) (j.castSucc.succ.succAbove j.succ) := by
                rw [cechNerveSectionHomotopyComponent_proj]
          _ = (cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
              ((Arrow.mk f).cechNerve).δ j.castSucc.succ) ≫
              cechNerveProjection f (n + 1) j.succ := by
                rw [Category.assoc, cechNerveProjection_comp_delta]
      · have hk' : j.succ < k := by
          exact lt_of_le_of_ne (Nat.succ_le_of_lt (show (j.castSucc : ℕ) < k by
            simpa using (lt_of_not_ge hk))) (Ne.symm hkj)
        calc
          (cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
              ((Arrow.mk f).cechNerve).δ j.castSucc.succ) ≫
              cechNerveProjection f (n + 1) k =
            cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
              cechNerveProjection f (n + 2) (j.castSucc.succ.succAbove k) := by
                rw [Category.assoc, cechNerveProjection_comp_delta]
          _ = cechNerveSectionHomotopyProjection f s (n + 1) j.succ
                (j.castSucc.succ.succAbove k) := by
                rw [cechNerveSectionHomotopyComponent_proj]
          _ = cechNerveProjection f (n + 1)
                (j.succ.predAbove (j.castSucc.succ.succAbove k)) := by
                rw [cechNerveSectionHomotopyProjection]
                have hmem : ¬ j.castSucc.succ.succAbove k ≤ j.succ.castSucc := by
                  have hsucc : j.castSucc.succ.succAbove k = k.succ := by
                    apply Fin.ext
                    have hnot : ¬ (k : ℕ) < j.1 + 1 := by
                      exact not_lt_of_ge hk'.le
                    simp [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, hnot]
                  rw [hsucc]
                  intro hle
                  exact hk (by simpa [Fin.succ_le_castSucc_iff] using hle)
                exact if_neg hmem
          _ = cechNerveProjection f (n + 1)
                (j.castSucc.predAbove (j.castSucc.succ.succAbove k)) := by
                rw [fin_adjacent_face_right_duplication_normalization]
          _ = cechNerveSectionHomotopyProjection f s (n + 1) j.castSucc
                (j.castSucc.succ.succAbove k) := by
                rw [cechNerveSectionHomotopyProjection]
                have hmem : ¬ j.castSucc.succ.succAbove k ≤ j.castSucc.castSucc := by
                  have hsucc : j.castSucc.succ.succAbove k = k.succ := by
                    apply Fin.ext
                    have hnot : ¬ (k : ℕ) < j.1 + 1 := by
                      exact not_lt_of_ge hk'.le
                    simp [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, hnot]
                  rw [hsucc]
                  intro hle
                  have hlt : k < j.castSucc := by
                    simpa [Fin.succ_le_castSucc_iff] using hle
                  exact hk hlt.le
                exact (if_neg hmem).symm
          _ = cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
              cechNerveProjection f (n + 2) (j.castSucc.succ.succAbove k) := by
                rw [cechNerveSectionHomotopyComponent_proj]
          _ = (cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
              ((Arrow.mk f).cechNerve).δ j.castSucc.succ) ≫
              cechNerveProjection f (n + 1) k := by
                rw [Category.assoc, cechNerveProjection_comp_delta]
  · calc
      (cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
          ((Arrow.mk f).cechNerve).δ j.castSucc.succ) ≫
          cechNerveBase f (n + 1) =
        cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫ cechNerveBase f (n + 2) := by
          rw [Category.assoc, cechNerveBase_comp_delta]
      _ = cechNerveBase f (n + 1) := by
          rw [cechNerveSectionHomotopyComponent_base]
      _ = cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫ cechNerveBase f (n + 2) := by
          rw [cechNerveSectionHomotopyComponent_base]
      _ = (cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
          ((Arrow.mk f).cechNerve).δ j.castSucc.succ) ≫
          cechNerveBase f (n + 1) := by
          rw [Category.assoc, cechNerveBase_comp_delta]

/-- Helper for Lemma 14.26.9: deleting a face strictly to the right of the duplicated coordinate
commutes with deleting that coordinate. -/
private theorem fin_face_right_duplication_normalization
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) (k : Fin (n + 2)) :
    j.castSucc.predAbove (i.succ.succAbove k) = i.succAbove (j.predAbove k) := by
  -- This is exactly the pointwise form of `δ_comp_σ_of_gt`.
  simpa [SimplexCategory.δ, SimplexCategory.σ] using
    congr_fun (congrArg DFunLike.coe
      (congrArg SimplexCategory.Hom.toOrderHom
        (SimplexCategory.δ_comp_σ_of_gt (i := i) (j := j) hji))) k

/-- Helper for Lemma 14.26.9: when the removed face lies after the duplicated coordinate, the
explicit Čech-nerve components satisfy the complementary face identity. -/
private theorem cechNerveSectionHomotopy_h_castSucc_comp_δ_succ_of_lt
    (hs : s ≫ f = 𝟙 X) {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) :
    cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
        ((Arrow.mk f).cechNerve).δ i.succ =
      ((Arrow.mk f).cechNerve).δ i ≫ cechNerveSectionHomotopyComponent f s hs n j := by
  -- The complementary face identity is the same projectionwise bookkeeping as `δ_comp_σ_of_gt`.
  apply WidePullback.hom_ext
  · intro k
    by_cases hk : k ≤ j.castSucc
    · calc
        (cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
            ((Arrow.mk f).cechNerve).δ i.succ) ≫
            cechNerveProjection f (n + 1) k =
          cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
            cechNerveProjection f (n + 2) (i.succ.succAbove k) := by
              rw [Category.assoc, cechNerveProjection_comp_delta]
        _ = cechNerveSectionHomotopyProjection f s (n + 1) j.castSucc (i.succ.succAbove k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = cechNerveBase f (n + 1) ≫ s := by
              rw [cechNerveSectionHomotopyProjection]
              have hik : k < i := lt_of_le_of_lt hk hji
              have hmem : i.succ.succAbove k ≤ j.castSucc.castSucc := by
                rw [Fin.succAbove_of_castSucc_lt _ _
                  (Fin.castSucc_lt_succ_iff.mpr hik.le)]
                exact Fin.castSucc_le_castSucc_iff.mpr hk
              exact if_pos hmem
        _ = ((Arrow.mk f).cechNerve).δ i ≫ (cechNerveBase f n ≫ s) := by
              simpa [Category.assoc] using
                congrArg (fun g ↦ g ≫ s) (cechNerveBase_comp_delta (f := f) (n := n) (i := i)).symm
        _ = ((Arrow.mk f).cechNerve).δ i ≫ cechNerveSectionHomotopyProjection f s n j k := by
              simp [cechNerveSectionHomotopyProjection, hk]
        _ = ((Arrow.mk f).cechNerve).δ i ≫
            (cechNerveSectionHomotopyComponent f s hs n j ≫ cechNerveProjection f (n + 1) k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = (((Arrow.mk f).cechNerve).δ i ≫ cechNerveSectionHomotopyComponent f s hs n j) ≫
            cechNerveProjection f (n + 1) k := by
              simp [Category.assoc]
    · calc
        (cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
            ((Arrow.mk f).cechNerve).δ i.succ) ≫
            cechNerveProjection f (n + 1) k =
          cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
            cechNerveProjection f (n + 2) (i.succ.succAbove k) := by
              rw [Category.assoc, cechNerveProjection_comp_delta]
        _ = cechNerveSectionHomotopyProjection f s (n + 1) j.castSucc (i.succ.succAbove k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = cechNerveProjection f (n + 1) (j.castSucc.predAbove (i.succ.succAbove k)) := by
              rw [cechNerveSectionHomotopyProjection]
              rcases le_or_gt k i with hik | hik
              · have hmem : ¬ i.succ.succAbove k ≤ j.castSucc.castSucc := by
                  rw [Fin.succAbove_of_castSucc_lt _ _
                    (Fin.castSucc_lt_succ_iff.mpr hik)]
                  exact fun hle ↦ hk (Fin.castSucc_le_castSucc_iff.mp hle)
                exact if_neg hmem
              · have hmem : ¬ i.succ.succAbove k ≤ j.castSucc.castSucc := by
                  rw [Fin.succAbove_of_le_castSucc _ _ (Fin.succ_le_castSucc_iff.mpr hik)]
                  intro hle
                  have hlt : k < j.castSucc := by
                    simpa [Fin.succ_le_castSucc_iff] using hle
                  exact hk hlt.le
                exact if_neg hmem
        _ = cechNerveProjection f (n + 1) (i.succAbove (j.predAbove k)) := by
              rw [fin_face_right_duplication_normalization i j hji]
        _ = ((Arrow.mk f).cechNerve).δ i ≫ cechNerveProjection f n (j.predAbove k) := by
              rw [cechNerveProjection_comp_delta]
        _ = ((Arrow.mk f).cechNerve).δ i ≫ cechNerveSectionHomotopyProjection f s n j k := by
              simp [cechNerveSectionHomotopyProjection, hk]
        _ = ((Arrow.mk f).cechNerve).δ i ≫
            (cechNerveSectionHomotopyComponent f s hs n j ≫ cechNerveProjection f (n + 1) k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = (((Arrow.mk f).cechNerve).δ i ≫ cechNerveSectionHomotopyComponent f s hs n j) ≫
            cechNerveProjection f (n + 1) k := by
              simp [Category.assoc]
  · calc
      (cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
          ((Arrow.mk f).cechNerve).δ i.succ) ≫
          cechNerveBase f (n + 1) =
        cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫ cechNerveBase f (n + 2) := by
          rw [Category.assoc, cechNerveBase_comp_delta]
      _ = cechNerveBase f (n + 1) := by
          rw [cechNerveSectionHomotopyComponent_base]
      _ = ((Arrow.mk f).cechNerve).δ i ≫ cechNerveBase f n := by
          rw [cechNerveBase_comp_delta]
      _ = ((Arrow.mk f).cechNerve).δ i ≫
          (cechNerveSectionHomotopyComponent f s hs n j ≫ cechNerveBase f (n + 1)) := by
          rw [cechNerveSectionHomotopyComponent_base]
      _ = (((Arrow.mk f).cechNerve).δ i ≫ cechNerveSectionHomotopyComponent f s hs n j) ≫
          cechNerveBase f (n + 1) := by
          simp [Category.assoc]

/-- Helper for Lemma 14.26.9: deleting the degeneracy index before deleting the duplicated
coordinate matches deleting the duplicated coordinate one slot later. -/
private theorem fin_degeneracy_left_duplication_normalization
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) (k : Fin (n + 3)) :
    j.predAbove (i.castSucc.predAbove k) = i.predAbove (j.succ.predAbove k) := by
  -- This is the pointwise form of `σ_comp_σ`.
  simpa [SimplexCategory.σ] using
    congr_fun (congrArg DFunLike.coe
      (congrArg SimplexCategory.Hom.toOrderHom
        (SimplexCategory.σ_comp_σ (i := i) (j := j) hij))) k

/-- Helper for Lemma 14.26.9: on the left degeneracy side, the nested `predAbove` branch test
for staying in the duplicated block is equivalent to the original index lying in that block. -/
private theorem fin_degeneracy_left_mem_left_iff
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) (k : Fin (n + 3)) :
    i.castSucc.predAbove k ≤ j.castSucc ↔ k ≤ j.succ.castSucc := by
  -- After expanding `predAbove`, this becomes a direct arithmetic check on `Fin` values.
  have hij' : i.1 ≤ j.1 := hij
  simp only [Fin.predAbove, Fin.lt_def, Fin.le_def, Fin.val_castSucc, Fin.val_succ,
    apply_dite Fin.val, dite_eq_ite, apply_ite Fin.val, Fin.val_pred, Fin.coe_castPred]
  split_ifs <;> omega

/-- Helper for Lemma 14.26.9: when the duplicated coordinate lies weakly to the right of the
degeneracy index, the explicit family satisfies the first degeneracy identity. -/
private theorem cechNerveSectionHomotopy_h_comp_σ_castSucc_of_le
    (hs : s ≫ f = 𝟙 X) {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    cechNerveSectionHomotopyComponent f s hs n j ≫ ((Arrow.mk f).cechNerve).σ i.castSucc =
      ((Arrow.mk f).cechNerve).σ i ≫ cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ := by
  -- Route correction: the only remaining issue is translating the left-block test through the
  -- nested `predAbove`; after that, the existing `σ_comp_σ` normalization closes each branch.
  apply WidePullback.hom_ext
  · intro k
    by_cases hk : k ≤ j.succ.castSucc
    · calc
        (cechNerveSectionHomotopyComponent f s hs n j ≫ ((Arrow.mk f).cechNerve).σ i.castSucc) ≫
            cechNerveProjection f (n + 2) k =
          cechNerveSectionHomotopyComponent f s hs n j ≫
            (((Arrow.mk f).cechNerve).σ i.castSucc ≫ cechNerveProjection f (n + 2) k) := by
              simp [Category.assoc]
        _ = cechNerveSectionHomotopyComponent f s hs n j ≫
            cechNerveProjection f (n + 1) (i.castSucc.predAbove k) := by
              rw [cechNerveProjection_comp_sigma]
        _ = cechNerveSectionHomotopyProjection f s n j (i.castSucc.predAbove k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = cechNerveBase f n ≫ s := by
              have hk' : k ≤ j.castSucc.succ := by
                simpa using hk
              rw [cechNerveSectionHomotopyProjection]
              exact if_pos ((fin_degeneracy_left_mem_left_iff i j hij k).mpr hk')
        _ = (((Arrow.mk f).cechNerve).σ i ≫ cechNerveBase f (n + 1)) ≫ s := by
              rw [cechNerveBase_comp_sigma]
        _ = ((Arrow.mk f).cechNerve).σ i ≫ (cechNerveBase f (n + 1) ≫ s) := by
              simp [Category.assoc]
        _ = ((Arrow.mk f).cechNerve).σ i ≫ cechNerveSectionHomotopyProjection f s (n + 1) j.succ k := by
              have hk' : k ≤ j.castSucc.succ := by
                simpa using hk
              rw [cechNerveSectionHomotopyProjection]
              exact congrArg (((Arrow.mk f).cechNerve).σ i ≫ ·) (if_pos hk').symm
        _ = ((Arrow.mk f).cechNerve).σ i ≫
            (cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
              cechNerveProjection f (n + 2) k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = (((Arrow.mk f).cechNerve).σ i ≫ cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ) ≫
            cechNerveProjection f (n + 2) k := by
              simp [Category.assoc]
    · calc
        (cechNerveSectionHomotopyComponent f s hs n j ≫ ((Arrow.mk f).cechNerve).σ i.castSucc) ≫
            cechNerveProjection f (n + 2) k =
          cechNerveSectionHomotopyComponent f s hs n j ≫
            (((Arrow.mk f).cechNerve).σ i.castSucc ≫ cechNerveProjection f (n + 2) k) := by
              simp [Category.assoc]
        _ = cechNerveSectionHomotopyComponent f s hs n j ≫
            cechNerveProjection f (n + 1) (i.castSucc.predAbove k) := by
              rw [cechNerveProjection_comp_sigma]
        _ = cechNerveSectionHomotopyProjection f s n j (i.castSucc.predAbove k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = cechNerveProjection f n (j.predAbove (i.castSucc.predAbove k)) := by
              have hk' : ¬ k ≤ j.castSucc.succ := by
                simpa using hk
              rw [cechNerveSectionHomotopyProjection]
              exact if_neg (fun hmem ↦ hk' ((fin_degeneracy_left_mem_left_iff i j hij k).mp hmem))
        _ = cechNerveProjection f n (i.predAbove (j.succ.predAbove k)) := by
              rw [fin_degeneracy_left_duplication_normalization i j hij]
        _ = ((Arrow.mk f).cechNerve).σ i ≫ cechNerveProjection f (n + 1) (j.succ.predAbove k) := by
              rw [cechNerveProjection_comp_sigma]
        _ = ((Arrow.mk f).cechNerve).σ i ≫ cechNerveSectionHomotopyProjection f s (n + 1) j.succ k := by
              have hk' : ¬ k ≤ j.castSucc.succ := by
                simpa using hk
              rw [cechNerveSectionHomotopyProjection]
              exact congrArg (((Arrow.mk f).cechNerve).σ i ≫ ·) (if_neg hk').symm
        _ = ((Arrow.mk f).cechNerve).σ i ≫
            (cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫
              cechNerveProjection f (n + 2) k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = (((Arrow.mk f).cechNerve).σ i ≫ cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ) ≫
            cechNerveProjection f (n + 2) k := by
              simp [Category.assoc]
  · calc
      (cechNerveSectionHomotopyComponent f s hs n j ≫ ((Arrow.mk f).cechNerve).σ i.castSucc) ≫
          cechNerveBase f (n + 2) =
        cechNerveSectionHomotopyComponent f s hs n j ≫ cechNerveBase f (n + 1) := by
          rw [Category.assoc, cechNerveBase_comp_sigma]
      _ = cechNerveBase f n := by
          rw [cechNerveSectionHomotopyComponent_base]
      _ = ((Arrow.mk f).cechNerve).σ i ≫ cechNerveBase f (n + 1) := by
          symm
          rw [cechNerveBase_comp_sigma]
      _ = ((Arrow.mk f).cechNerve).σ i ≫
          (cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ ≫ cechNerveBase f (n + 2)) := by
          rw [cechNerveSectionHomotopyComponent_base]
      _ = (((Arrow.mk f).cechNerve).σ i ≫ cechNerveSectionHomotopyComponent f s hs (n + 1) j.succ) ≫
          cechNerveBase f (n + 2) := by
          simp [Category.assoc]

/-- Helper for Lemma 14.26.9: deleting the degeneracy index after the duplicated coordinate
matches deleting the duplicated coordinate without the extra shift. -/
private theorem fin_degeneracy_right_duplication_normalization
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) (k : Fin (n + 3)) :
    j.predAbove (i.succ.predAbove k) = i.predAbove (j.castSucc.predAbove k) := by
  -- This is the symmetric pointwise form of `σ_comp_σ`.
  symm
  simpa [SimplexCategory.σ] using
    congr_fun (congrArg DFunLike.coe
      (congrArg SimplexCategory.Hom.toOrderHom
        (SimplexCategory.σ_comp_σ (i := j) (j := i) hji))) k

/-- Helper for Lemma 14.26.9: on the right degeneracy side, the nested `predAbove` branch test
for staying in the duplicated block is equivalent to the original index lying before that block. -/
private theorem fin_degeneracy_right_mem_left_iff
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) (k : Fin (n + 3)) :
    i.succ.predAbove k ≤ j.castSucc ↔ k ≤ j.castSucc.castSucc := by
  -- Expanding `predAbove` again reduces the statement to a linear arithmetic comparison.
  have hji' : j.1 ≤ i.1 := hji
  simp only [Fin.predAbove, Fin.lt_def, Fin.le_def, Fin.val_castSucc, Fin.val_succ,
    apply_dite Fin.val, dite_eq_ite, apply_ite Fin.val, Fin.val_pred, Fin.coe_castPred]
  split_ifs <;> omega

/-- Helper for Lemma 14.26.9: when the duplicated coordinate lies weakly to the left of the
degeneracy index, the explicit family satisfies the complementary degeneracy identity. -/
private theorem cechNerveSectionHomotopy_h_comp_σ_succ_of_lt
    (hs : s ≫ f = 𝟙 X) {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    cechNerveSectionHomotopyComponent f s hs n j ≫ ((Arrow.mk f).cechNerve).σ i.succ =
      ((Arrow.mk f).cechNerve).σ i ≫ cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc := by
  -- Route correction: the mirrored `σ`-identity now differs only by the right-hand branch test,
  -- so we translate that test and reuse the existing `σ_comp_σ` normalization.
  apply WidePullback.hom_ext
  · intro k
    by_cases hk : k ≤ j.castSucc.castSucc
    · calc
        (cechNerveSectionHomotopyComponent f s hs n j ≫ ((Arrow.mk f).cechNerve).σ i.succ) ≫
            cechNerveProjection f (n + 2) k =
          cechNerveSectionHomotopyComponent f s hs n j ≫
            (((Arrow.mk f).cechNerve).σ i.succ ≫ cechNerveProjection f (n + 2) k) := by
              simp [Category.assoc]
        _ = cechNerveSectionHomotopyComponent f s hs n j ≫
            cechNerveProjection f (n + 1) (i.succ.predAbove k) := by
              rw [cechNerveProjection_comp_sigma]
        _ = cechNerveSectionHomotopyProjection f s n j (i.succ.predAbove k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = cechNerveBase f n ≫ s := by
              rw [cechNerveSectionHomotopyProjection]
              exact if_pos ((fin_degeneracy_right_mem_left_iff i j hji k).mpr hk)
        _ = (((Arrow.mk f).cechNerve).σ i ≫ cechNerveBase f (n + 1)) ≫ s := by
              rw [cechNerveBase_comp_sigma]
        _ = ((Arrow.mk f).cechNerve).σ i ≫ (cechNerveBase f (n + 1) ≫ s) := by
              simp [Category.assoc]
        _ = ((Arrow.mk f).cechNerve).σ i ≫ cechNerveSectionHomotopyProjection f s (n + 1) j.castSucc k := by
              rw [cechNerveSectionHomotopyProjection]
              exact congrArg (((Arrow.mk f).cechNerve).σ i ≫ ·) (if_pos hk).symm
        _ = ((Arrow.mk f).cechNerve).σ i ≫
            (cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
              cechNerveProjection f (n + 2) k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = (((Arrow.mk f).cechNerve).σ i ≫ cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc) ≫
            cechNerveProjection f (n + 2) k := by
              simp [Category.assoc]
    · calc
        (cechNerveSectionHomotopyComponent f s hs n j ≫ ((Arrow.mk f).cechNerve).σ i.succ) ≫
            cechNerveProjection f (n + 2) k =
          cechNerveSectionHomotopyComponent f s hs n j ≫
            (((Arrow.mk f).cechNerve).σ i.succ ≫ cechNerveProjection f (n + 2) k) := by
              simp [Category.assoc]
        _ = cechNerveSectionHomotopyComponent f s hs n j ≫
            cechNerveProjection f (n + 1) (i.succ.predAbove k) := by
              rw [cechNerveProjection_comp_sigma]
        _ = cechNerveSectionHomotopyProjection f s n j (i.succ.predAbove k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = cechNerveProjection f n (j.predAbove (i.succ.predAbove k)) := by
              rw [cechNerveSectionHomotopyProjection]
              exact if_neg (fun hmem ↦ hk ((fin_degeneracy_right_mem_left_iff i j hji k).mp hmem))
        _ = cechNerveProjection f n (i.predAbove (j.castSucc.predAbove k)) := by
              rw [fin_degeneracy_right_duplication_normalization i j hji]
        _ = ((Arrow.mk f).cechNerve).σ i ≫ cechNerveProjection f (n + 1) (j.castSucc.predAbove k) := by
              rw [cechNerveProjection_comp_sigma]
        _ = ((Arrow.mk f).cechNerve).σ i ≫ cechNerveSectionHomotopyProjection f s (n + 1) j.castSucc k := by
              rw [cechNerveSectionHomotopyProjection]
              exact congrArg (((Arrow.mk f).cechNerve).σ i ≫ ·) (if_neg hk).symm
        _ = ((Arrow.mk f).cechNerve).σ i ≫
            (cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫
              cechNerveProjection f (n + 2) k) := by
              rw [cechNerveSectionHomotopyComponent_proj]
        _ = (((Arrow.mk f).cechNerve).σ i ≫ cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc) ≫
            cechNerveProjection f (n + 2) k := by
              simp [Category.assoc]
  · calc
      (cechNerveSectionHomotopyComponent f s hs n j ≫ ((Arrow.mk f).cechNerve).σ i.succ) ≫
          cechNerveBase f (n + 2) =
        cechNerveSectionHomotopyComponent f s hs n j ≫ cechNerveBase f (n + 1) := by
          rw [Category.assoc, cechNerveBase_comp_sigma]
      _ = cechNerveBase f n := by
          rw [cechNerveSectionHomotopyComponent_base]
      _ = ((Arrow.mk f).cechNerve).σ i ≫ cechNerveBase f (n + 1) := by
          symm
          rw [cechNerveBase_comp_sigma]
      _ = ((Arrow.mk f).cechNerve).σ i ≫
          (cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc ≫ cechNerveBase f (n + 2)) := by
          rw [cechNerveSectionHomotopyComponent_base]
      _ = (((Arrow.mk f).cechNerve).σ i ≫ cechNerveSectionHomotopyComponent f s hs (n + 1) j.castSucc) ≫
          cechNerveBase f (n + 2) := by
          simp [Category.assoc]

/-- Helper for Lemma 14.26.9: the explicit duplicated-coordinate family forms the simplicial
homotopy from the coordinatewise `f ≫ s` endomorphism of the Čech nerve to the identity. -/
private noncomputable def cechNerveSectionEndomorphism_homotopy
    (hs : s ≫ f = 𝟙 X) :
    Homotopy
      (Arrow.mapCechNerve (cechNerveSectionEndomorphismArrowHom f s hs))
      (𝟙 ((Arrow.mk f).cechNerve)) where
  h {n} j := cechNerveSectionHomotopyComponent f s hs n j
  h_zero_comp_δ_zero n := cechNerveSectionHomotopy_h_zero_comp_δ_zero f s hs n
  h_last_comp_δ_last n := cechNerveSectionHomotopy_h_last_comp_δ_last f s hs n
  h_succ_comp_δ_castSucc_of_lt i j hij :=
    cechNerveSectionHomotopy_h_succ_comp_δ_castSucc_of_lt f s hs i j hij
  h_succ_comp_δ_castSucc_succ j :=
    cechNerveSectionHomotopy_h_succ_comp_δ_castSucc_succ f s hs j
  h_castSucc_comp_δ_succ_of_lt i j hji :=
    cechNerveSectionHomotopy_h_castSucc_comp_δ_succ_of_lt f s hs i j hji
  h_comp_σ_castSucc_of_le i j hij :=
    cechNerveSectionHomotopy_h_comp_σ_castSucc_of_le f s hs i j hij
  h_comp_σ_succ_of_lt i j hji :=
    cechNerveSectionHomotopy_h_comp_σ_succ_of_lt f s hs i j hji

-- Proof sketch: use the textbook maps `h_{n,i}` built from the extra degeneracy on the augmented
-- Čech nerve of the split epimorphism `f`; Lemma 14.26.2 packages these maps into a simplicial
-- homotopy from the endomorphism induced by `f ≫ s` to the identity.
/-- Lemma 14.26.9: if `f : Y ⟶ X` has a section `s`, then the endomorphism of the Čech nerve of
`f` induced by the idempotent `f ≫ s` is simplicially homotopic to the identity. -/
def cechNerveSectionEndomorphism_homotopic_id (hs : s ≫ f = 𝟙 X) :
    Homotopy
      (Arrow.mapCechNerve
        (Arrow.homMk (f ≫ s) (𝟙 X)
          (by simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) hs)))
      (𝟙 ((Arrow.mk f).cechNerve)) :=
  cechNerveSectionEndomorphism_homotopy f s hs

end CategoryTheory

/-! ### Lemma_14_26_10 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open SimplexCategory Simplicial Opposite

universe w u v

noncomputable section

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable {T : Type w}

/- Domain-style sampling for Lemma 14.26.10:
- primary domain: closure of simplicial homotopy and simplicial homotopy equivalence under
  categorical products of simplicial objects;
- inspected same-kind declarations:
  `CategoryTheory.SimplicialObject.Homotopy`,
  `CategoryTheory.SimplicialObject.Homotopic`,
  `CategoryTheory.SimplicialObject.HomotopyEquiv`,
  `CategoryTheory.Limits.Pi.map`;
- best owner abstractions: the primitive directed data live in `Homotopy`, the zigzag relation
  lives in `Homotopic`, the equivalence data live in `HomotopyEquiv`, and the product maps are the
  canonical `Pi.map`s;
- primitive-vs-derived split:
  primitive input data are a family `H : ∀ t, Homotopy (a t) (b t)` or a family
  `e : ∀ t, HomotopyEquiv (X t) (Y t)`;
  derived API consists of the owner construction `Homotopy.piMap`, the induced zigzag theorem
  `Homotopic.piMap`, and the induced product homotopy equivalence `HomotopyEquiv.piObj` for finite
  index families.

Source/core/bridge triage:
- `source-facing`: the three product-closure assertions stated in Lemma 14.26.10;
- `core/canonical`: the owner-level APIs `Homotopy.piMap`, `Homotopic.piMap`, and
  `HomotopyEquiv.piObj` for finite index families;
- `bridge/view`: none introduced here, since the owner-level constructions already match the source
  mathematics directly.
-/

namespace Homotopy

variable {X Y : T → SimplicialObject C}
variable [HasProductsOfShape T C]
variable {a b : ∀ t, X t ⟶ Y t}

/-- Lemma 14.26.10 (2): a family of simplicial homotopies `a t ⟶ b t` induces a simplicial
homotopy from the product map `∏ a t` to the product map `∏ b t`. -/
def piMap (H : ∀ t, Homotopy (a t) (b t)) :
    Homotopy (Limits.Pi.map a) (Limits.Pi.map b) where
  h {n} i :=
    (piObjIso X (op ⦋n⦌)).hom ≫
      Limits.Pi.map (fun t ↦ (H t).h i) ≫
      (piObjIso Y (op ⦋n + 1⦌)).inv
  h_zero_comp_δ_zero n := by
    apply (cancel_mono (piObjIso Y (op ⦋n⦌)).hom).1
    refine Pi.hom_ext _ _ fun t ↦ ?_
    simpa only [Category.assoc, piObjIso_hom_comp_π, δ_naturality, piObjIso_inv_comp_π_assoc,
      Pi.map_π_assoc, Homotopy.h_zero_comp_δ_zero, piObjIso_hom_comp_π_assoc] using
      congr_app (Pi.map_π b t).symm (op ⦋n⦌)
  h_last_comp_δ_last n := by
    apply (cancel_mono (piObjIso Y (op ⦋n⦌)).hom).1
    refine Pi.hom_ext _ _ fun t ↦ ?_
    simpa only [Category.assoc, piObjIso_hom_comp_π, δ_naturality, piObjIso_inv_comp_π_assoc,
      Pi.map_π_assoc, Homotopy.h_last_comp_δ_last, piObjIso_hom_comp_π_assoc] using
      congr_app (Pi.map_π a t).symm (op ⦋n⦌)
  h_succ_comp_δ_castSucc_of_lt {n} i j hij := by
    apply (cancel_mono (piObjIso Y (op ⦋n + 1⦌)).hom).1
    refine Pi.hom_ext _ _ fun t ↦ ?_
    simp [Category.assoc, (H t).h_succ_comp_δ_castSucc_of_lt i j hij]
  h_succ_comp_δ_castSucc_succ {n} j := by
    apply (cancel_mono (piObjIso Y (op ⦋n + 1⦌)).hom).1
    refine Pi.hom_ext _ _ fun t ↦ ?_
    simp [Category.assoc, (H t).h_succ_comp_δ_castSucc_succ j]
  h_castSucc_comp_δ_succ_of_lt {n} i j hji := by
    apply (cancel_mono (piObjIso Y (op ⦋n + 1⦌)).hom).1
    refine Pi.hom_ext _ _ fun t ↦ ?_
    simp [Category.assoc, (H t).h_castSucc_comp_δ_succ_of_lt i j hji]
  h_comp_σ_castSucc_of_le {n} i j hij := by
    apply (cancel_mono (piObjIso Y (op ⦋n + 2⦌)).hom).1
    refine Pi.hom_ext _ _ fun t ↦ ?_
    simp [Category.assoc, (H t).h_comp_σ_castSucc_of_le i j hij]
  h_comp_σ_succ_of_lt {n} i j hji := by
    apply (cancel_mono (piObjIso Y (op ⦋n + 2⦌)).hom).1
    refine Pi.hom_ext _ _ fun t ↦ ?_
    simp [Category.assoc, (H t).h_comp_σ_succ_of_lt i j hji]

end Homotopy

namespace Homotopic

variable [Finite T]
variable {X Y : T → SimplicialObject C}
variable [HasProductsOfShape T C]
variable {a b : ∀ t, X t ⟶ Y t}

-- Proof sketch: expand each component zigzag `Homotopic (a t) (b t)` into finitely many directed
-- homotopies, promote each single-coordinate change to a product zigzag via the owner-level
-- construction `Homotopy.piMap`, and concatenate the finitely many coordinatewise zigzags.
/-- Lemma 14.26.10 (3): if each pair of component maps `a t`, `b t` are homotopic in the zigzag
sense, then the induced product maps are homotopic. -/
theorem piMap
    (hab : ∀ t, Homotopic (a t) (b t)) :
    Homotopic (Limits.Pi.map a) (Limits.Pi.map b) := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  let c : Finset T → ∀ t, X t ⟶ Y t := fun s t ↦ if t ∈ s then b t else a t
  have hs : ∀ s : Finset T, Homotopic (Limits.Pi.map a) (Limits.Pi.map (c s)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa [c] using Homotopic.refl (Limits.Pi.map a)
    | @insert t s ht ih =>
        have hcs : Function.update (c s) t (a t) = c s := by
          funext x
          by_cases hx : x = t
          · subst hx
            simp [c, ht]
          · simp [c, Function.update, hx]
        have hct : Function.update (c s) t (b t) = c (insert t s) := by
          funext x
          by_cases hx : x = t
          · subst hx
            simp [c]
          · simp [c, Function.update, hx, Finset.mem_insert]
        have hst :
            Homotopic (Limits.Pi.map (c s)) (Limits.Pi.map (c (insert t s))) := by
          simpa [hcs, hct] using
            (hab t).map
              (fun u : X t ⟶ Y t ↦ Limits.Pi.map (Function.update (c s) t u))
              (fun {u v} huv ↦
                Homotopic.of_homotopy <|
                  Homotopy.piMap fun x ↦ by
                    by_cases hx : x = t
                    · subst hx
                      simpa using huv
                    · simpa [Function.update, hx] using Homotopy.refl ((c s) x))
        exact ih.trans hst
  simpa [c] using hs Finset.univ

end Homotopic

namespace HomotopyEquiv

variable {X Y : T → SimplicialObject C}
variable [HasProductsOfShape T C]

/-- Lemma 14.26.10 (1): if each `X t` is homotopy equivalent to `Y t` and the index type is
finite, then the categorical products of the families of simplicial objects are homotopy
equivalent. -/
def piObj [Finite T] (e : ∀ t, HomotopyEquiv (X t) (Y t)) :
    HomotopyEquiv (∏ᶜ X) (∏ᶜ Y) where
  hom := Limits.Pi.map fun t ↦ (e t).hom
  inv := Limits.Pi.map fun t ↦ (e t).inv
  homotopyHomInvId := by
    let a : ∀ t, X t ⟶ X t := fun t ↦ (e t).hom ≫ (e t).inv
    let b : ∀ t, X t ⟶ X t := fun t ↦ 𝟙 (X t)
    simpa [a, b, Limits.Pi.map_comp_map, Limits.Pi.map_id] using
      Homotopic.piMap (fun t ↦ (e t).homotopyHomInvId)
  homotopyInvHomId := by
    let a : ∀ t, Y t ⟶ Y t := fun t ↦ (e t).inv ≫ (e t).hom
    let b : ∀ t, Y t ⟶ Y t := fun t ↦ 𝟙 (Y t)
    simpa [a, b, Limits.Pi.map_comp_map, Limits.Pi.map_id] using
      Homotopic.piMap (fun t ↦ (e t).homotopyInvHomId)

end HomotopyEquiv

end CategoryTheory.SimplicialObject
