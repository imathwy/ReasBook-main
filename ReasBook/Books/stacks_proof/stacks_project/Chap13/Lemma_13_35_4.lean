import StacksProject_2024.Chap13.Lemma_13_35_3
import StacksProject_2024.Chap13.Remark_13_35_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [(n : ℤ) → (shiftFunctor C n).Additive] [Pretriangulated C]

/- Domain-style sampling for Lemma 13.35.4:
- primary domain: object properties/full subcategories in a pretriangulated category, with the
  Section `13.35` owners `CategoryTheory.additiveClosure`, `extensionProductIter`,
  `extensionProduct`, and `retractClosure`; the final addition theorem then upgrades to the
  triangulated layer through `extensionProductIter_add`;
- inspected owner declarations:
  `CategoryTheory.additiveClosure`,
  `CategoryTheory.additiveClosure_isClosedUnderFiniteCoproducts`,
  `CategoryTheory.ObjectProperty.extensionProductIter_add`,
  `CategoryTheory.ObjectProperty.retractClosure_extensionProduct_retractClosure_retractClosure`,
  `CategoryTheory.ObjectProperty.extensionProduct_isClosedUnderBinaryCoproducts`;
- best owner abstraction: keep the source-facing stage `additiveExtensionStage`, but define it
  directly from the existing chapter owner `CategoryTheory.additiveClosure` rather than duplicating
  a local additive-hull wrapper;
- primitive-vs-derived split:
  primitive data are the chapter owner `additiveClosure` and the core operations
  `extensionProductIter`, `extensionProduct`, and `retractClosure`;
  derived API is the stage wrapper `additiveExtensionStage` together with its coproduct-closure
  and addition lemmas.

Source/core/bridge triage:
- `source-facing`: the stage `C_n = smd(add(\mathcal A)^{\star n})`;
- `core/canonical`: `CategoryTheory.additiveClosure` and the mathlib
  `ObjectProperty` extension/retract owners;
- `bridge/view`: `additiveExtensionStage` as the thin textbook wrapper around those owners. -/

/-- The stage `C_n = smd(add(\mathcal A)^{\star n})` attached to a positive integer `n`. -/
abbrev additiveExtensionStage (P : ObjectProperty C) (n : ℕ+) : ObjectProperty C :=
  (P.additiveClosure.extensionProductIter n.natPred).retractClosure

/-- `additiveExtensionStage` is monotone in the underlying object property. -/
theorem additiveExtensionStage_monotone {P Q : ObjectProperty C} (hPQ : P ≤ Q) (n : ℕ+) :
    additiveExtensionStage P n ≤ additiveExtensionStage Q n := by
  dsimp [additiveExtensionStage]
  exact monotone_retractClosure <|
    monotone_extensionProductIter
      (colimitsClosure_monotone (fun n : ℕ ↦ Discrete (Fin n)) hPQ)
      n.natPred

private instance retractClosure_isStableUnderShift (P : ObjectProperty C)
    [P.IsStableUnderShift ℤ] :
    P.retractClosure.IsStableUnderShift ℤ where
  isStableUnderShiftBy a := by
    refine ⟨?_⟩
    rintro X ⟨Y, hY, ⟨r⟩⟩
    exact ⟨Y⟦a⟧, P.le_shift a _ hY, ⟨r.map (shiftFunctor C a)⟩⟩

private instance additiveClosure_isStableUnderShift (P : ObjectProperty C)
    [P.IsStableUnderShift ℤ] :
    P.additiveClosure.IsStableUnderShift ℤ where
  isStableUnderShiftBy a := by
    refine ⟨?_⟩
    intro X hX
    change (P.colimitsClosure fun n : ℕ ↦ Discrete (Fin n)) (X⟦a⟧)
    induction hX with
    | of_mem X hX =>
        exact (P.le_colimitsClosure _) _ (P.le_shift a _ hX)
    | of_isoClosure e hX ih =>
        exact .of_isoClosure ((shiftFunctor C a).mapIso e) ih
    | of_colimitPresentation pres h ih =>
        exact .of_colimitPresentation (pres.map (shiftFunctor C a)) ih

/-- Shift-stability propagates from `P` to every additive extension stage `C_n`. -/
instance additiveExtensionStage_isStableUnderShift (P : ObjectProperty C)
    [P.IsStableUnderShift ℤ] (n : ℕ+) :
    (additiveExtensionStage P n).IsStableUnderShift ℤ := by
  dsimp [additiveExtensionStage]
  infer_instance

-- Proof sketch: first show `additiveClosure P` is closed under binary coproducts; then use
-- Lemma `13.35.3 (1)` to propagate binary-coproduct closure through `extensionProductIter`, and
-- finally Lemma `13.35.3 (2)` to pass to the outer retract closure.
/-- The stage `C_n` is closed under direct sums. -/
instance additiveExtensionStage_isClosedUnderBinaryCoproducts
    (P : ObjectProperty C) (n : ℕ+) :
    (additiveExtensionStage P n).IsClosedUnderBinaryCoproducts := by
  dsimp [additiveExtensionStage]
  letI : (P.additiveClosure.extensionProductIter n.natPred).IsClosedUnderBinaryCoproducts := by
    induction n.natPred with
    | zero =>
        simpa [extensionProductIter_zero] using
          (inferInstance : P.additiveClosure.IsClosedUnderBinaryCoproducts)
    | succ k hk =>
        rw [extensionProductIter_succ]
        letI := hk
        infer_instance
  infer_instance

end

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [(n : ℤ) → (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

-- Proof sketch: rewrite both sides using the definition of `additiveExtensionStage`; then apply
-- `retractClosure_extensionProduct_retractClosure_retractClosure` to remove the inner retract
-- closures and `extensionProductIter_add` with the positive-index offsets `n - 1` and `m - 1`.
/-- Lemma 13.35.4: for a full subcategory `\mathcal A` of a triangulated category and positive
integers `n` and `m`, the stage `C_{n + m} = smd(add(\mathcal A)^{\star (n + m)})` is the
retract/direct-summand closure of `C_n \star C_m`. -/
@[stacks 0FX4]
theorem additiveExtensionStage_add
    (P : ObjectProperty C) (n m : ℕ+) :
    additiveExtensionStage P (n + m) =
      ((additiveExtensionStage P n) ⋆ additiveExtensionStage P m).retractClosure := by
  dsimp [additiveExtensionStage]
  rw [retractClosure_extensionProduct_retractClosure_retractClosure]
  have hnm : (n + m).natPred = n.natPred + (m : ℕ) := by
    rcases n with ⟨n, hn⟩
    rcases m with ⟨m, hm⟩
    simp [PNat.natPred]
    rw [Nat.add_comm n m, Nat.add_sub_assoc hn, Nat.add_comm m (n - 1)]
  have hm : (m : ℕ) = m.natPred + 1 := by
    simpa [PNat.natPred] using (Nat.sub_add_cancel m.2).symm
  rw [hnm, P.additiveClosure.extensionProductIter_add' hm]

end

end CategoryTheory.ObjectProperty
