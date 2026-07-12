import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Retract

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.MonoidalCategory

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsIdempotentComplete C]
variable {X Y : C}

/-
Domain-style sampling for Lemma 12.17.3:
- primary domain: rigid monoidal category theory with retracts in an idempotent complete category
- core/canonical declarations inspected:
  - `HasLeftDual`
  - `ExactPairing`
  - `Retract`
  - `IsIdempotentComplete.idempotents_split`
- best owner abstraction: `HasLeftDual`
- primitive data: a retract `r : Retract X Y` and a chosen left dual on `Y`
- derived API: the induced `HasLeftDual X`
- source/core/bridge triage:
  - `source-facing`: retracts of left-dualizable objects are again left-dualizable
  - `core/canonical`: `HasLeftDual`
  - `bridge/view`: split the induced idempotent on `ᘁY` to obtain the chosen left dual of `X`
-/

namespace Retract

private def idempotent (r : Retract X Y) : Y ⟶ Y :=
  r.r ≫ r.i

omit [MonoidalCategory C] [IsIdempotentComplete C] in
private theorem idempotent_idem (r : Retract X Y) :
    r.idempotent ≫ r.idempotent = r.idempotent := by
  dsimp [idempotent]
  simp [Category.assoc]

private def dualIdempotent [HasLeftDual Y] (r : Retract X Y) : (ᘁY : C) ⟶ ᘁY :=
  ᘁ(r.idempotent)

omit [IsIdempotentComplete C] in
private theorem dualIdempotent_idem [HasLeftDual Y] (r : Retract X Y) :
    r.dualIdempotent ≫ r.dualIdempotent = r.dualIdempotent := by
  simpa [dualIdempotent, comp_leftAdjointMate] using
    congrArg (fun f : Y ⟶ Y ↦ leftAdjointMate f) r.idempotent_idem

section

variable [HasLeftDual Y] (r : Retract X Y)

private theorem exists_dualSplit :
    ∃ split : Σ Y' : C, Retract Y' (ᘁY : C), split.2.r ≫ split.2.i = r.dualIdempotent := by
  rcases IsIdempotentComplete.idempotents_split (ᘁY : C) r.dualIdempotent r.dualIdempotent_idem with
    ⟨Y', i, e, hi, he⟩
  exact ⟨⟨Y', ⟨i, e, hi⟩⟩, he⟩

private noncomputable def dualSplit :
    Σ Y' : C, Retract Y' (ᘁY : C) :=
  Classical.choose r.exists_dualSplit

private noncomputable def leftDual : C :=
  r.dualSplit.1

private noncomputable def leftDualRetract :
    Retract r.leftDual (ᘁY : C) :=
  r.dualSplit.2

private theorem dualSplit_comp :
    (r.leftDualRetract).r ≫ (r.leftDualRetract).i = r.dualIdempotent :=
  Classical.choose_spec r.exists_dualSplit

/-- Helper for Lemma 12.17.3: the chosen split retract on the candidate left dual has the
expected retraction identity. -/
private theorem leftDualRetract_id :
    (r.leftDualRetract).i ≫ (r.leftDualRetract).r = 𝟙 r.leftDual := by
  -- This is the retract identity coming from the idempotent splitting on `ᘁY`.
  exact (r.leftDualRetract).retract

/-- Helper for Lemma 12.17.3: whiskering the split identity on the chosen left dual stays an
identity. -/
private theorem whiskerRight_leftDualRetract_id (Z : C) :
    ((r.leftDualRetract).i ≫ (r.leftDualRetract).r) ▷ Z = 𝟙 (r.leftDual ⊗ Z) := by
  -- Collapse the split identity before applying the right whiskering functor.
  simpa [r.leftDualRetract_id] using congrArg (fun f : r.leftDual ⟶ r.leftDual ↦ f ▷ Z)
    r.leftDualRetract_id

/-- Helper for Lemma 12.17.3: left whiskering the split identity on the chosen left dual stays an
identity. -/
private theorem whiskerLeft_leftDualRetract_id (Z : C) :
    Z ◁ ((r.leftDualRetract).i ≫ (r.leftDualRetract).r) = 𝟙 (Z ⊗ r.leftDual) := by
  -- Collapse the split identity before applying the left whiskering functor.
  simpa [r.leftDualRetract_id] using congrArg (fun f : r.leftDual ⟶ r.leftDual ↦ Z ◁ f)
    r.leftDualRetract_id

private noncomputable def coevaluation :
    𝟙_ C ⟶ r.leftDual ⊗ X :=
  η_ (ᘁY) Y ≫ (r.leftDualRetract).r ▷ Y ≫ r.leftDual ◁ r.r

private noncomputable def evaluation :
    X ⊗ r.leftDual ⟶ 𝟙_ C :=
  r.i ▷ r.leftDual ≫ Y ◁ (r.leftDualRetract).i ≫ ε_ (ᘁY) Y

/-- Helper for Lemma 12.17.3: after expanding the retract-side first triangle composite, the split
maps combine into the dual idempotent and the outer retract maps move to the boundary. -/
private theorem first_triangle_associator_normalization :
    X ◁ r.coevaluation ≫
        (α_ X r.leftDual X).inv ≫
        r.evaluation ▷ X =
      (r.i ▷ (𝟙_ C)) ≫
        (Y ◁ η_ (ᘁY : C) Y ≫
          Y ◁ r.dualIdempotent ▷ Y ≫
          (α_ Y (ᘁY : C) Y).inv ≫
          ε_ (ᘁY : C) Y ▷ Y) ≫
        ((𝟙_ C) ◁ r.r) := by
  -- Route correction: first isolate the split dual idempotent inside the ambient triangle-shaped
  -- composite, and only afterwards rewrite that idempotent through the ambient duality.
  have hsplit :
      Y ◁ r.leftDualRetract.r ▷ Y ≫ Y ◁ r.leftDualRetract.i ▷ Y =
        Y ◁ r.dualIdempotent ▷ Y := by
    -- The chosen split on `ᘁY` realizes the dual idempotent after whiskering by `Y` on both sides.
    simpa [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight, dualIdempotent]
      using congrArg (fun f : (ᘁY : C) ⟶ (ᘁY : C) ↦ Y ◁ f ▷ Y) r.dualSplit_comp
  have hsplit_assoc :
      Y ◁ r.leftDualRetract.r ▷ Y ≫
          Y ◁ r.leftDualRetract.i ▷ Y ≫
          (α_ Y (ᘁY : C) Y).inv ≫
          (Y ⊗ (ᘁY : C)) ◁ r.r ≫
          ε_ (ᘁY : C) Y ▷ X =
        Y ◁ r.dualIdempotent ▷ Y ≫
          (α_ Y (ᘁY : C) Y).inv ≫
          (Y ⊗ (ᘁY : C)) ◁ r.r ≫
          ε_ (ᘁY : C) Y ▷ X := by
    -- Reassociate the split-idempotent equality so it can be rewritten under the final suffix.
    simpa [Category.assoc] using congrArg
      (fun k ↦ k ≫ (α_ Y (ᘁY : C) Y).inv ≫ (Y ⊗ (ᘁY : C)) ◁ r.r ≫ ε_ (ᘁY : C) Y ▷ X)
      hsplit
  simp only [coevaluation, evaluation, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [associator_inv_naturality_right_assoc X r.leftDual r.r
    ((r.i ▷ r.leftDual) ▷ X ≫ (Y ◁ r.leftDualRetract.i) ▷ X ≫ ε_ (ᘁY) Y ▷ X)]
  rw [whisker_exchange_assoc (r.i ▷ r.leftDual) r.r
    ((Y ◁ r.leftDualRetract.i) ▷ X ≫ ε_ (ᘁY) Y ▷ X)]
  rw [← associator_inv_naturality_left_assoc r.i r.leftDual Y
    ((Y ⊗ r.leftDual) ◁ r.r ≫ (Y ◁ r.leftDualRetract.i) ▷ X ≫ ε_ (ᘁY) Y ▷ X)]
  rw [whisker_exchange_assoc r.i (r.leftDualRetract.r ▷ Y)
    ((α_ Y r.leftDual Y).inv ≫
      (Y ⊗ r.leftDual) ◁ r.r ≫
      (Y ◁ r.leftDualRetract.i) ▷ X ≫
      ε_ (ᘁY) Y ▷ X)]
  rw [whisker_exchange_assoc r.i (η_ (ᘁY) Y)
    (Y ◁ r.leftDualRetract.r ▷ Y ≫
      (α_ Y r.leftDual Y).inv ≫
      (Y ⊗ r.leftDual) ◁ r.r ≫
      (Y ◁ r.leftDualRetract.i) ▷ X ≫
      ε_ (ᘁY) Y ▷ X)]
  rw [whisker_exchange_assoc (Y ◁ r.leftDualRetract.i) r.r (ε_ (ᘁY) Y ▷ X)]
  rw [← associator_inv_naturality_middle_assoc Y r.leftDualRetract.i Y
    ((Y ⊗ (ᘁY : C)) ◁ r.r ≫ ε_ (ᘁY) Y ▷ X)]
  rw [hsplit_assoc]
  rw [← whisker_exchange]

omit [IsIdempotentComplete C] in
/-- Helper for Lemma 12.17.3: normalize the first retract-side triangle composite into the
ambient triangle for `(ᘁY, Y)` whiskered by the retract maps. -/
private theorem ambient_dual_idempotent_transport :
    (r.i ▷ (𝟙_ C)) ≫
        (Y ◁ η_ (ᘁY : C) Y ≫
          Y ◁ r.dualIdempotent ▷ Y ≫
          (α_ Y (ᘁY : C) Y).inv ≫
          ε_ (ᘁY : C) Y ▷ Y) ≫
        ((𝟙_ C) ◁ r.r) =
      (r.i ▷ (𝟙_ C)) ≫
        (Y ◁ η_ (ᘁY : C) Y ≫
          (α_ Y (ᘁY : C) Y).inv ≫
          ε_ (ᘁY : C) Y ▷ Y) ≫
        ((𝟙_ C) ◁ r.r) := by
  -- Move the inserted dual projector across the ambient first triangle by the mate identity.
  have hmate :
      Y ◁ η_ (ᘁY : C) Y ≫
          Y ◁ r.dualIdempotent ▷ Y ≫
          (α_ Y (ᘁY : C) Y).inv ≫
          ε_ (ᘁY : C) Y ▷ Y =
        Y ◁ η_ (ᘁY : C) Y ≫
          Y ◁ ((ᘁY : C) ◁ r.idempotent) ≫
          (α_ Y (ᘁY : C) Y).inv ≫
          ε_ (ᘁY : C) Y ▷ Y := by
    -- Whisker the ambient mate formula by `Y` and compose with the fixed suffix.
    simpa [MonoidalCategory.whiskerLeft_comp, Category.assoc, dualIdempotent] using
      congrArg
        (fun k : 𝟙_ C ⟶ (ᘁY : C) ⊗ Y ↦
          Y ◁ k ≫ (α_ Y (ᘁY : C) Y).inv ≫ ε_ (ᘁY : C) Y ▷ Y)
        (coevaluation_comp_leftAdjointMate (f := r.idempotent))
  -- After exposing the ambient `r.idempotent`, push it to the boundary and collapse it there.
  calc
    (r.i ▷ (𝟙_ C)) ≫
        (Y ◁ η_ (ᘁY : C) Y ≫
          Y ◁ r.dualIdempotent ▷ Y ≫
          (α_ Y (ᘁY : C) Y).inv ≫
          ε_ (ᘁY : C) Y ▷ Y) ≫
        ((𝟙_ C) ◁ r.r) =
      (r.i ▷ (𝟙_ C)) ≫
        (Y ◁ η_ (ᘁY : C) Y ≫
          Y ◁ ((ᘁY : C) ◁ r.idempotent) ≫
          (α_ Y (ᘁY : C) Y).inv ≫
          ε_ (ᘁY : C) Y ▷ Y) ≫
        ((𝟙_ C) ◁ r.r) := by
      rw [hmate]
    _ =
      (r.i ▷ (𝟙_ C)) ≫
        (Y ◁ η_ (ᘁY : C) Y ≫
          (α_ Y (ᘁY : C) Y).inv ≫
          ε_ (ᘁY : C) Y ▷ Y ≫
          ((𝟙_ C) ◁ r.idempotent)) ≫
        ((𝟙_ C) ◁ r.r) := by
      rw [Category.assoc, Category.assoc, Category.assoc, associator_inv_naturality_right_assoc,
        whisker_exchange_assoc]
      simp [Category.assoc]
    _ =
      (r.i ▷ (𝟙_ C)) ≫
        (Y ◁ η_ (ᘁY : C) Y ≫
          (α_ Y (ᘁY : C) Y).inv ≫
          ε_ (ᘁY : C) Y ▷ Y) ≫
        ((𝟙_ C) ◁ r.r) := by
      simp only [idempotent, MonoidalCategory.whiskerLeft_comp, Category.assoc]
      rw [← MonoidalCategory.whiskerLeft_comp, r.retract]
      simp

private theorem ambient_coevaluation_evaluation_whiskered :
    X ◁ r.coevaluation ≫
        (α_ X r.leftDual X).inv ≫
        r.evaluation ▷ X =
      (r.i ▷ (𝟙_ C)) ≫
        (Y ◁ η_ (ᘁY : C) Y ≫
          (α_ Y (ᘁY : C) Y).inv ≫
          ε_ (ᘁY : C) Y ▷ Y) ≫
        ((𝟙_ C) ◁ r.r) := by
  -- Reduce to the ambient triangle with the inserted projector, then transport that projector
  -- across the ambient duality computation.
  calc
    X ◁ r.coevaluation ≫
        (α_ X r.leftDual X).inv ≫
        r.evaluation ▷ X =
      (r.i ▷ (𝟙_ C)) ≫
        (Y ◁ η_ (ᘁY : C) Y ≫
          Y ◁ r.dualIdempotent ▷ Y ≫
          (α_ Y (ᘁY : C) Y).inv ≫
          ε_ (ᘁY : C) Y ▷ Y) ≫
        ((𝟙_ C) ◁ r.r) := r.first_triangle_associator_normalization
    _ =
      (r.i ▷ (𝟙_ C)) ≫
        (Y ◁ η_ (ᘁY : C) Y ≫
          (α_ Y (ᘁY : C) Y).inv ≫
          ε_ (ᘁY : C) Y ▷ Y) ≫
        ((𝟙_ C) ◁ r.r) := r.ambient_dual_idempotent_transport

private theorem coevaluation_evaluation :
    X ◁ r.coevaluation ≫
        (α_ X r.leftDual X).inv ≫
        r.evaluation ▷ X =
      (ρ_ X).hom ≫ (λ_ X).inv := by
  -- Apply the whiskered ambient triangle after isolating the retract-side normalization.
  calc
    X ◁ r.coevaluation ≫
        (α_ X r.leftDual X).inv ≫
        r.evaluation ▷ X =
      r.i ▷ (𝟙_ C) ≫
        (Y ◁ η_ (ᘁY : C) Y ≫
          (α_ Y (ᘁY : C) Y).inv ≫
          ε_ (ᘁY : C) Y ▷ Y) ≫
        ((𝟙_ C) ◁ r.r) := r.ambient_coevaluation_evaluation_whiskered
    _ = r.i ▷ (𝟙_ C) ≫ ((ρ_ Y).hom ≫ (λ_ Y).inv) ≫ (𝟙_ C) ◁ r.r := by
      rw [ExactPairing.coevaluation_evaluation (X := (ᘁY : C)) (Y := Y)]
    _ = (ρ_ X).hom ≫ (λ_ X).inv := by
      simp [Category.assoc]

/-- Helper for Lemma 12.17.3: one `simp only` pass freezes the second triangle composite into
its literal expanded retract form. -/
private theorem second_triangle_postsimp_normalization :
    r.coevaluation ▷ r.leftDual ≫
        (α_ r.leftDual X r.leftDual).hom ≫
        r.leftDual ◁ r.evaluation =
      η_ (ᘁY) Y ▷ r.leftDual ≫
        r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
        (r.leftDual ◁ r.r) ▷ r.leftDual ≫
        (α_ r.leftDual X r.leftDual).hom ≫
        r.leftDual ◁ r.i ▷ r.leftDual ≫
        r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
        r.leftDual ◁ ε_ (ᘁY) Y := by
  -- Freeze the exact post-`simp` shape so later rewrites can target a stable term.
  simp only [coevaluation, evaluation, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.comp_whiskerRight, Category.assoc]

/-- Helper for Lemma 12.17.3: the two summand maps around the hom-side associator compress to the
single projector `r.idempotent` on the ambient `Y`-factor. -/
private theorem second_triangle_projector_normalization :
    (r.leftDual ◁ r.r) ▷ r.leftDual ≫
        (α_ r.leftDual X r.leftDual).hom ≫
        r.leftDual ◁ r.i ▷ r.leftDual =
      (α_ r.leftDual Y r.leftDual).hom ≫
        r.leftDual ◁ r.idempotent ▷ r.leftDual := by
  -- Rewrite the `r.r` leg across the associator, then collapse `r.r ≫ r.i` to `r.idempotent`.
  have hα :
      (r.leftDual ◁ r.r) ▷ r.leftDual ≫
          (α_ r.leftDual X r.leftDual).hom =
        (α_ r.leftDual Y r.leftDual).hom ≫
          r.leftDual ◁ r.r ▷ r.leftDual := by
    simpa using MonoidalCategory.associator_naturality (𝟙 r.leftDual) r.r (𝟙 r.leftDual)
  calc
    (r.leftDual ◁ r.r) ▷ r.leftDual ≫
        (α_ r.leftDual X r.leftDual).hom ≫
        r.leftDual ◁ r.i ▷ r.leftDual =
      (α_ r.leftDual Y r.leftDual).hom ≫
        r.leftDual ◁ r.r ▷ r.leftDual ≫
        r.leftDual ◁ r.i ▷ r.leftDual := by
      simpa [Category.assoc] using congrArg
        (fun k ↦ k ≫ r.leftDual ◁ r.i ▷ r.leftDual) hα
    _ =
      (α_ r.leftDual Y r.leftDual).hom ≫
        r.leftDual ◁ r.idempotent ▷ r.leftDual := by
      simp [idempotent]

/-- Helper for Lemma 12.17.3: the inserted projector on the `Y`-factor can be moved across the
evaluation by the ambient mate identity, turning it into the dual projector on `ᘁY`. -/
private theorem second_triangle_mate_rewrite :
    (α_ r.leftDual Y r.leftDual).hom ≫
        r.leftDual ◁ r.idempotent ▷ r.leftDual ≫
        r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
        r.leftDual ◁ ε_ (ᘁY) Y =
      (α_ r.leftDual Y r.leftDual).hom ≫
        r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
        r.leftDual ◁ Y ◁ r.dualIdempotent ≫
        r.leftDual ◁ ε_ (ᘁY) Y := by
  -- First rewrite the projector next to the evaluation in the ambient duality.
  have hmate :
      r.idempotent ▷ r.leftDual ≫
          Y ◁ r.leftDualRetract.i ≫
          ε_ (ᘁY) Y =
        Y ◁ r.leftDualRetract.i ≫
          Y ◁ r.dualIdempotent ≫
          ε_ (ᘁY) Y := by
    calc
      r.idempotent ▷ r.leftDual ≫
          Y ◁ r.leftDualRetract.i ≫
          ε_ (ᘁY) Y =
        Y ◁ r.leftDualRetract.i ≫
          r.idempotent ▷ (ᘁY : C) ≫
          ε_ (ᘁY) Y := by
        simpa [Category.assoc] using
          (whisker_exchange_assoc r.idempotent r.leftDualRetract.i (ε_ (ᘁY) Y)).symm
      _ =
        Y ◁ r.leftDualRetract.i ≫
          Y ◁ r.dualIdempotent ≫
          ε_ (ᘁY) Y := by
        simpa [Category.assoc, dualIdempotent] using congrArg
          (fun k : Y ⊗ (ᘁY : C) ⟶ 𝟙_ C ↦ Y ◁ r.leftDualRetract.i ≫ k)
          ((leftAdjointMate_comp_evaluation (f := r.idempotent)).symm)
  -- Then whisker that rewrite by `r.leftDual` and compose with the fixed associator prefix.
  have hwhisker :
      r.leftDual ◁
          (r.idempotent ▷ r.leftDual ≫
            Y ◁ r.leftDualRetract.i ≫
            ε_ (ᘁY) Y) =
        r.leftDual ◁
          (Y ◁ r.leftDualRetract.i ≫
            Y ◁ r.dualIdempotent ≫
            ε_ (ᘁY) Y) := by
    exact congrArg (fun k : Y ⊗ r.leftDual ⟶ 𝟙_ C ↦ r.leftDual ◁ k) hmate
  have hprefix :
      (α_ r.leftDual Y r.leftDual).hom ≫
          r.leftDual ◁
            (r.idempotent ▷ r.leftDual ≫
              Y ◁ r.leftDualRetract.i ≫
              ε_ (ᘁY) Y) =
        (α_ r.leftDual Y r.leftDual).hom ≫
          r.leftDual ◁
            (Y ◁ r.leftDualRetract.i ≫
              Y ◁ r.dualIdempotent ≫
              ε_ (ᘁY) Y) := by
    exact congrArg
      (fun k : r.leftDual ⊗ (Y ⊗ r.leftDual) ⟶ r.leftDual ⊗ (𝟙_ C) ↦
        (α_ r.leftDual Y r.leftDual).hom ≫ k)
      hwhisker
  simpa [MonoidalCategory.whiskerLeft_comp, Category.assoc] using hprefix

/-- Helper for Lemma 12.17.3: after rewriting the inserted projector as the split dual
idempotent, the split maps can be pushed to the boundary so that the ambient second triangle
appears literally in the middle. -/
private theorem collapsed_second_triangle_boundary_transport :
    η_ (ᘁY) Y ▷ r.leftDual ≫
        r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
        (α_ r.leftDual Y r.leftDual).hom ≫
        r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
        r.leftDual ◁ ε_ (ᘁY) Y =
      ((𝟙_ C) ◁ r.leftDualRetract.i) ≫
        (η_ (ᘁY) Y ▷ (ᘁY : C) ≫
          (α_ (ᘁY : C) Y (ᘁY : C)).hom ≫
          (ᘁY : C) ◁ ε_ (ᘁY) Y) ≫
        (r.leftDualRetract.r ▷ (𝟙_ C)) := by
  -- Route correction: isolate the projector-free coherence statement before reintroducing the
  -- split idempotent, so the ambient transport is only associator and whisker bookkeeping.
  have htransport :
      ((𝟙_ C) ◁ r.leftDualRetract.i) ≫
          (η_ (ᘁY) Y ▷ (ᘁY : C) ≫
            (α_ (ᘁY : C) Y (ᘁY : C)).hom ≫
            (ᘁY : C) ◁ ε_ (ᘁY) Y) ≫
          (r.leftDualRetract.r ▷ (𝟙_ C)) =
        η_ (ᘁY) Y ▷ r.leftDual ≫
          r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
          (α_ r.leftDual Y r.leftDual).hom ≫
          r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
          r.leftDual ◁ ε_ (ᘁY : C) Y := by
    calc
      ((𝟙_ C) ◁ r.leftDualRetract.i) ≫
          (η_ (ᘁY) Y ▷ (ᘁY : C) ≫
            (α_ (ᘁY : C) Y (ᘁY : C)).hom ≫
            (ᘁY : C) ◁ ε_ (ᘁY) Y) ≫
          (r.leftDualRetract.r ▷ (𝟙_ C)) =
        η_ (ᘁY) Y ▷ r.leftDual ≫
          ((ᘁY : C) ⊗ Y) ◁ r.leftDualRetract.i ≫
          (α_ (ᘁY : C) Y (ᘁY : C)).hom ≫
          (ᘁY : C) ◁ ε_ (ᘁY : C) Y ≫
          (r.leftDualRetract.r ▷ (𝟙_ C)) := by
        simpa [Category.assoc] using
          (whisker_exchange_assoc (η_ (ᘁY) Y) r.leftDualRetract.i
            ((α_ (ᘁY : C) Y (ᘁY : C)).hom ≫
              (ᘁY : C) ◁ ε_ (ᘁY : C) Y ≫
              (r.leftDualRetract.r ▷ (𝟙_ C))))
      _ =
        η_ (ᘁY) Y ▷ r.leftDual ≫
          (α_ (ᘁY : C) Y r.leftDual).hom ≫
          (ᘁY : C) ◁ Y ◁ r.leftDualRetract.i ≫
          (ᘁY : C) ◁ ε_ (ᘁY : C) Y ≫
          (r.leftDualRetract.r ▷ (𝟙_ C)) := by
        simpa [Category.assoc] using
          (MonoidalCategory.associator_naturality_assoc (𝟙 (ᘁY : C)) (𝟙 Y) r.leftDualRetract.i
            ((ᘁY : C) ◁ ε_ (ᘁY : C) Y ≫ (r.leftDualRetract.r ▷ (𝟙_ C))))
      _ =
        η_ (ᘁY) Y ▷ r.leftDual ≫
          (α_ (ᘁY : C) Y r.leftDual).hom ≫
          (ᘁY : C) ◁ Y ◁ r.leftDualRetract.i ≫
          (r.leftDualRetract.r ▷ (Y ⊗ (ᘁY : C))) ≫
          r.leftDual ◁ ε_ (ᘁY : C) Y := by
        simpa [Category.assoc] using congrArg
          (fun k : (ᘁY : C) ⊗ (Y ⊗ (ᘁY : C)) ⟶ r.leftDual ⊗ (𝟙_ C) ↦
            η_ (ᘁY) Y ▷ r.leftDual ≫
              (α_ (ᘁY : C) Y r.leftDual).hom ≫
              (ᘁY : C) ◁ Y ◁ r.leftDualRetract.i ≫
              k)
          (whisker_exchange r.leftDualRetract.r (ε_ (ᘁY : C) Y))
      _ =
        η_ (ᘁY) Y ▷ r.leftDual ≫
          r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
          (α_ r.leftDual Y r.leftDual).hom ≫
          r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
          r.leftDual ◁ ε_ (ᘁY : C) Y := by
        have hboundary :
            (α_ (ᘁY : C) Y r.leftDual).hom ≫
                (ᘁY : C) ◁ Y ◁ r.leftDualRetract.i ≫
                (r.leftDualRetract.r ▷ (Y ⊗ (ᘁY : C))) ≫
                r.leftDual ◁ ε_ (ᘁY : C) Y =
              r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
                (α_ r.leftDual Y r.leftDual).hom ≫
                r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
                r.leftDual ◁ ε_ (ᘁY : C) Y := by
          have hexchange :
              (ᘁY : C) ◁ Y ◁ r.leftDualRetract.i ≫
                  (r.leftDualRetract.r ▷ (Y ⊗ (ᘁY : C))) ≫
                  r.leftDual ◁ ε_ (ᘁY : C) Y =
                (α_ (ᘁY : C) Y r.leftDual).inv ≫
                  r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
                  (α_ r.leftDual Y r.leftDual).hom ≫
                  r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
                  r.leftDual ◁ ε_ (ᘁY : C) Y := by
            simpa [Category.assoc] using
              (whisker_exchange_assoc r.leftDualRetract.r (Y ◁ r.leftDualRetract.i)
                (r.leftDual ◁ ε_ (ᘁY : C) Y))
          calc
            (α_ (ᘁY : C) Y r.leftDual).hom ≫
                (ᘁY : C) ◁ Y ◁ r.leftDualRetract.i ≫
                (r.leftDualRetract.r ▷ (Y ⊗ (ᘁY : C))) ≫
                r.leftDual ◁ ε_ (ᘁY : C) Y =
              (α_ (ᘁY : C) Y r.leftDual).hom ≫
                ((α_ (ᘁY : C) Y r.leftDual).inv ≫
                  r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
                  (α_ r.leftDual Y r.leftDual).hom ≫
                  r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
                  r.leftDual ◁ ε_ (ᘁY : C) Y) := by
              rw [hexchange]
            _ =
              r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
                (α_ r.leftDual Y r.leftDual).hom ≫
                r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
                r.leftDual ◁ ε_ (ᘁY : C) Y := by
              simp
        simpa [Category.assoc] using congrArg
          (fun k ↦ η_ (ᘁY) Y ▷ r.leftDual ≫ k)
          hboundary
  exact htransport.symm

/-- Helper for Lemma 12.17.3: after rewriting the inserted projector as the split dual
idempotent, the split maps can be pushed to the boundary so that the ambient second triangle
appears literally in the middle. -/
private theorem ambient_second_triangle_projector_transport :
    η_ (ᘁY) Y ▷ r.leftDual ≫
        r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
        (α_ r.leftDual Y r.leftDual).hom ≫
        r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
        r.leftDual ◁ Y ◁ r.dualIdempotent ≫
        r.leftDual ◁ ε_ (ᘁY) Y =
      ((𝟙_ C) ◁ r.leftDualRetract.i) ≫
        (η_ (ᘁY) Y ▷ (ᘁY : C) ≫
          (α_ (ᘁY : C) Y (ᘁY : C)).hom ≫
          (ᘁY : C) ◁ ε_ (ᘁY) Y) ≫
        (r.leftDualRetract.r ▷ (𝟙_ C)) := by
  -- Rewrite the inserted projector through the chosen split and collapse the resulting
  -- `i ≫ r = 𝟙` before invoking the projector-free boundary transport lemma.
  calc
    η_ (ᘁY) Y ▷ r.leftDual ≫
        r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
        (α_ r.leftDual Y r.leftDual).hom ≫
        r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
        r.leftDual ◁ Y ◁ r.dualIdempotent ≫
        r.leftDual ◁ ε_ (ᘁY) Y =
      η_ (ᘁY) Y ▷ r.leftDual ≫
        r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
        (α_ r.leftDual Y r.leftDual).hom ≫
        r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
        r.leftDual ◁ Y ◁ r.leftDualRetract.r ≫
        r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
        r.leftDual ◁ ε_ (ᘁY) Y := by
      simpa [MonoidalCategory.whiskerLeft_comp, Category.assoc] using congrArg
        (fun k : (ᘁY : C) ⟶ (ᘁY : C) ↦
          η_ (ᘁY) Y ▷ r.leftDual ≫
            r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
            (α_ r.leftDual Y r.leftDual).hom ≫
            r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
            r.leftDual ◁ Y ◁ k ≫
            r.leftDual ◁ ε_ (ᘁY) Y)
        r.dualSplit_comp.symm
    _ =
      η_ (ᘁY) Y ▷ r.leftDual ≫
        r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
        (α_ r.leftDual Y r.leftDual).hom ≫
        r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
        r.leftDual ◁ ε_ (ᘁY) Y := by
      have hid :
          r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
              r.leftDual ◁ Y ◁ r.leftDualRetract.r =
            𝟙 (r.leftDual ⊗ (Y ⊗ r.leftDual)) := by
        have hinnercomp :
            Y ◁ r.leftDualRetract.i ≫ Y ◁ r.leftDualRetract.r =
              Y ◁ (r.leftDualRetract.i ≫ r.leftDualRetract.r) := by
          simpa using
            (MonoidalCategory.whiskerLeft_comp Y r.leftDualRetract.i r.leftDualRetract.r).symm
        have houter :
            r.leftDual ◁ (Y ◁ (r.leftDualRetract.i ≫ r.leftDualRetract.r)) =
              𝟙 (r.leftDual ⊗ (Y ⊗ r.leftDual)) := by
          simpa using congrArg
            (fun f : Y ⊗ r.leftDual ⟶ Y ⊗ r.leftDual ↦ r.leftDual ◁ f)
            (r.whiskerLeft_leftDualRetract_id Y)
        calc
          r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
              r.leftDual ◁ Y ◁ r.leftDualRetract.r =
            r.leftDual ◁ Y ◁ (r.leftDualRetract.i ≫ r.leftDualRetract.r) := by
            simpa [Category.assoc] using congrArg
              (fun f : Y ⊗ r.leftDual ⟶ Y ⊗ r.leftDual ↦ r.leftDual ◁ f)
              hinnercomp
          _ = 𝟙 (r.leftDual ⊗ (Y ⊗ r.leftDual)) := houter
      have hcollapse :
          r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
              r.leftDual ◁ Y ◁ r.leftDualRetract.r ≫
              r.leftDual ◁ Y ◁ r.leftDualRetract.i =
            r.leftDual ◁ Y ◁ r.leftDualRetract.i := by
        simpa [Category.assoc] using congrArg
          (fun k : r.leftDual ⊗ (Y ⊗ r.leftDual) ⟶ r.leftDual ⊗ (Y ⊗ r.leftDual) ↦
            k ≫ r.leftDual ◁ Y ◁ r.leftDualRetract.i)
          hid
      simpa [Category.assoc] using congrArg
        (fun k ↦
          η_ (ᘁY) Y ▷ r.leftDual ≫
            r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
            (α_ r.leftDual Y r.leftDual).hom ≫
            k ≫
            r.leftDual ◁ ε_ (ᘁY) Y)
        hcollapse
    _ =
      ((𝟙_ C) ◁ r.leftDualRetract.i) ≫
        (η_ (ᘁY) Y ▷ (ᘁY : C) ≫
          (α_ (ᘁY : C) Y (ᘁY : C)).hom ≫
          (ᘁY : C) ◁ ε_ (ᘁY) Y) ≫
        (r.leftDualRetract.r ▷ (𝟙_ C)) := r.collapsed_second_triangle_boundary_transport

private theorem evaluation_coevaluation :
    r.coevaluation ▷ r.leftDual ≫
        (α_ r.leftDual X r.leftDual).hom ≫
        r.leftDual ◁ r.evaluation =
      (λ_ r.leftDual).hom ≫ (ρ_ r.leftDual).inv := by
  -- Route correction: the remaining blocker is transporting the literal post-`simp` projector term
  -- through the ambient second triangle before collapsing the split retract on `ᘁY`.
  calc
    r.coevaluation ▷ r.leftDual ≫
        (α_ r.leftDual X r.leftDual).hom ≫
        r.leftDual ◁ r.evaluation =
      η_ (ᘁY) Y ▷ r.leftDual ≫
        r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
        (r.leftDual ◁ r.r) ▷ r.leftDual ≫
        (α_ r.leftDual X r.leftDual).hom ≫
        r.leftDual ◁ r.i ▷ r.leftDual ≫
        r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
        r.leftDual ◁ ε_ (ᘁY) Y := r.second_triangle_postsimp_normalization
    _ =
      η_ (ᘁY) Y ▷ r.leftDual ≫
        r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
        (α_ r.leftDual Y r.leftDual).hom ≫
        r.leftDual ◁ r.idempotent ▷ r.leftDual ≫
        r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
        r.leftDual ◁ ε_ (ᘁY) Y := by
      simpa [Category.assoc] using congrArg
        (fun k ↦
          η_ (ᘁY) Y ▷ r.leftDual ≫
            r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
            k ≫
            r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
            r.leftDual ◁ ε_ (ᘁY) Y)
        r.second_triangle_projector_normalization
    _ =
      η_ (ᘁY) Y ▷ r.leftDual ≫
        r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
        (α_ r.leftDual Y r.leftDual).hom ≫
        r.leftDual ◁ Y ◁ r.leftDualRetract.i ≫
        r.leftDual ◁ Y ◁ r.dualIdempotent ≫
        r.leftDual ◁ ε_ (ᘁY) Y := by
      simpa [Category.assoc] using congrArg
        (fun k ↦
          η_ (ᘁY) Y ▷ r.leftDual ≫
            r.leftDualRetract.r ▷ Y ▷ r.leftDual ≫
            k)
        r.second_triangle_mate_rewrite
    _ =
      ((𝟙_ C) ◁ r.leftDualRetract.i) ≫
        (η_ (ᘁY) Y ▷ (ᘁY : C) ≫
          (α_ (ᘁY : C) Y (ᘁY : C)).hom ≫
          (ᘁY : C) ◁ ε_ (ᘁY) Y) ≫
        (r.leftDualRetract.r ▷ (𝟙_ C)) := r.ambient_second_triangle_projector_transport
    _ = ((𝟙_ C) ◁ r.leftDualRetract.i) ≫
        ((λ_ (ᘁY : C)).hom ≫ (ρ_ (ᘁY : C)).inv) ≫
        (r.leftDualRetract.r ▷ (𝟙_ C)) := by
      rw [ExactPairing.evaluation_coevaluation (X := (ᘁY : C)) (Y := Y)]
    _ = (λ_ r.leftDual).hom ≫ (ρ_ r.leftDual).inv := by
      simp [Category.assoc]

@[implicit_reducible] private noncomputable instance exactPairing :
    ExactPairing r.leftDual X where
  coevaluation' := r.coevaluation
  evaluation' := r.evaluation
  coevaluation_evaluation' := r.coevaluation_evaluation
  evaluation_coevaluation' := r.evaluation_coevaluation

end

/-- Helper for Lemma 12.17.3: a retract of an object with a chosen left dual inherits a chosen
left dual by splitting the induced idempotent on the dual object. -/
@[implicit_reducible] noncomputable def hasLeftDual [HasLeftDual Y] (r : Retract X Y) :
    HasLeftDual X where
  leftDual := r.leftDual
  exact := inferInstance

end Retract

/-- Lemma 12.17.3: in an idempotent complete monoidal category, every retract, hence every
summand, of an object admitting a left dual again admits a left dual. -/
noncomputable abbrev hasLeftDual_of_retract [HasLeftDual Y] (r : Retract X Y) : HasLeftDual X :=
  Retract.hasLeftDual r

end CategoryTheory
