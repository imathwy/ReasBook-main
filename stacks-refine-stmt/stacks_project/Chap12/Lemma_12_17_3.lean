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

private noncomputable def coevaluation :
    𝟙_ C ⟶ r.leftDual ⊗ X :=
  η_ (ᘁY) Y ≫ (r.leftDualRetract).r ▷ Y ≫ r.leftDual ◁ r.r

private noncomputable def evaluation :
    X ⊗ r.leftDual ⟶ 𝟙_ C :=
  r.i ▷ r.leftDual ≫ Y ◁ (r.leftDualRetract).i ≫ ε_ (ᘁY) Y

private theorem coevaluation_evaluation :
    X ◁ r.coevaluation ≫
        (α_ X r.leftDual X).inv ≫
        r.evaluation ▷ X =
      (ρ_ X).hom ≫ (λ_ X).inv := sorry

private theorem evaluation_coevaluation :
    r.coevaluation ▷ r.leftDual ≫
        (α_ r.leftDual X r.leftDual).hom ≫
        r.leftDual ◁ r.evaluation =
      (λ_ r.leftDual).hom ≫ (ρ_ r.leftDual).inv := sorry

@[implicit_reducible] private noncomputable instance exactPairing :
    ExactPairing r.leftDual X where
  coevaluation' := r.coevaluation
  evaluation' := r.evaluation
  coevaluation_evaluation' := r.coevaluation_evaluation
  evaluation_coevaluation' := r.evaluation_coevaluation

end

/-- Lemma 12.17.3: in an idempotent complete monoidal category, every retract, hence every
summand, of an object admitting a left dual again admits a left dual. -/
@[implicit_reducible] noncomputable def hasLeftDual [HasLeftDual Y] (r : Retract X Y) :
    HasLeftDual X where
  leftDual := r.leftDual
  exact := inferInstance

end Retract

end CategoryTheory
