import stacks_proof.stacks_project.Chap13.Lemma_13_35_1
import stacks_proof.stacks_project.Chap13.Remark_13_35_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {C : Type u} [Category.{v} C]

private theorem iSup_isClosedUnderColimitsOfShape_of_monotone
    {J : Type*} [Category J] [Finite J] (A : ℕ → ObjectProperty C) (hA : Monotone A)
    [∀ i, (A i).IsClosedUnderIsomorphisms] [∀ i, (A i).IsClosedUnderColimitsOfShape J] :
    (⨆ i, A i).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    classical
    rintro X ⟨p⟩
    let _ : Fintype J := Fintype.ofFinite J
    choose i hi using fun j : J ↦ (prop_iSup_iff A _).mp (p.prop_diag_obj j)
    let n : ℕ := Finset.univ.sup i
    have hn (j : J) : A n (p.diag.obj j) := by
      exact hA (Finset.le_sup (by simp)) _ (hi j)
    let q : (A n).ColimitOfShape J X :=
      { toColimitPresentation := p.toColimitPresentation
        prop_diag_obj := hn }
    exact (le_iSup A n) _ (ColimitOfShape.prop q)

private theorem colimitsClosure_iSup_of_monotone {α : Type*} (J : α → Type*)
    [∀ a, Category (J a)] [∀ a, Finite (J a)] (A : ℕ → ObjectProperty C) (hA : Monotone A) :
    (⨆ i, A i).colimitsClosure J = ⨆ i, (A i).colimitsClosure J := by
  let B : ℕ → ObjectProperty C := fun i ↦ (A i).colimitsClosure J
  have hB : Monotone B := by
    intro i j hij
    simpa [B] using
      (colimitsClosure_monotone J (hA hij) : (A i).colimitsClosure J ≤ (A j).colimitsClosure J)
  refine le_antisymm ?_ ?_
  · let Q : ObjectProperty C := ⨆ i, B i
    have hAQ : (⨆ i, A i) ≤ Q := by
      refine iSup_le fun i ↦ ?_
      exact ((A i).le_colimitsClosure J).trans <| le_iSup B i
    have hQ (a : α) : Q.IsClosedUnderColimitsOfShape (J a) := by
      simpa [Q, B] using
        (iSup_isClosedUnderColimitsOfShape_of_monotone B hB : Q.IsClosedUnderColimitsOfShape (J a))
    let _ : ∀ a : α, Q.IsClosedUnderColimitsOfShape (J a) := hQ
    intro X hX
    induction hX with
    | of_mem X hX => exact hAQ _ hX
    | of_isoClosure e hX hX' => exact Q.prop_of_iso e hX'
    | of_colimitPresentation pres h h' => exact Q.prop_of_isColimit pres.isColimit h'
  · refine iSup_le fun i ↦ ?_
    simpa [B] using
      (colimitsClosure_monotone J (le_iSup A i) :
        (A i).colimitsClosure J ≤ (⨆ i, A i).colimitsClosure J)

-- Proof sketch: finite coproduct presentations only use finitely many stages of the chain, so
-- monotonicity lets one dominate all of them by a single index; then retract closures commute with
-- that `iSup`.
/-- Remark 13.35.6 (3): for an increasing family `A_i`, the additive closure `add` of the union is
the union of the additive closures. -/
@[stacks 0FX6]
theorem additiveClosure_iSup_of_monotone (A : ℕ → ObjectProperty C) (hA : Monotone A) :
    additiveClosure (⨆ i, A i) = ⨆ i, additiveClosure (A i) := by
  simpa [additiveClosure] using
    (colimitsClosure_iSup_of_monotone (fun n : ℕ ↦ Discrete (Fin n)) A hA)

end

section

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {ι : Sort*}

/- Domain-style sampling for Remark 13.35.6:
- primary domain: `ObjectProperty` closure operations in a pretriangulated category, especially the
  interval-of-shifts owner from Remark `13.35.5` and the triangulated extension/retract owners
  from mathlib;
- sampled owner declarations:
  `CategoryTheory.shiftInterval`,
  `CategoryTheory.additiveClosure`,
  `CategoryTheory.ObjectProperty.retractClosure`,
  `CategoryTheory.ObjectProperty.extensionProduct`;
- best owner abstraction: the interval construction should use the chapter owner `P[a, b]` rather
  than a second local interval wrapper; the new content of this file is the interaction of `iSup`
  with that owner and with the closure operations `retractClosure`, `additiveClosure`, `⋆`, and
  `extensionProductIter`;
- primitive-vs-derived split:
  primitive data are the existing owners `P[a, b]`, `P.retractClosure`, `additiveClosure P`,
  `P ⋆ Q`, and `P.extensionProductIter n`;
  derived API is the six `iSup`-commutation lemmas recorded below.

Source/core/bridge triage:
- `source-facing`: the Stacks formulas saying that unions commute with bounded shifts, direct
  summands, additive closure, extension products `⋆`, and iterated extension products;
- `core/canonical`: `shiftInterval`, `retractClosure`, `additiveClosure`, `extensionProduct`, and
  `extensionProductIter`;
- `bridge/view`: none beyond using the established notation `P[a, b]` for the interval owner. -/

-- Proof sketch: `P[a, b]` is an `iSup` of shifted-and-iso-closed object properties over the
-- finite interval `Set.Icc a b`; `shift_iSup`, `isoClosure_iSup`, and `iSup_comm` commute the two
-- suprema.
/-- Remark 13.35.6 (1): shifting the union of a family through the interval `[a,b]`
equals the union of the interval shifts. -/
@[stacks 0FX6]
theorem shiftInterval_iSup (A : ι → ObjectProperty C) (a b : ℤ) :
    (⨆ i, A i)[a, b] = ⨆ i, (A i)[a, b] := by
  simp_rw [shiftInterval, shift_iSup, isoClosure_iSup]
  rw [iSup_comm]

end

section

variable {C : Type u} [Category.{v} C]
variable {ι : Sort*}

-- Proof sketch: an object is a direct summand of an object in `⨆ i, A i` exactly when it is a
-- direct summand of an object in some single stage `A i`; this rewrites the retract closure of the
-- supremum as the supremum of the retract closures.
/-- Remark 13.35.6 (2): the direct-summand closure `smd` commutes with the union of a family
`A_i`. -/
@[stacks 0FX6]
theorem retractClosure_iSup (A : ι → ObjectProperty C) :
    (⨆ i, A i).retractClosure = ⨆ i, (A i).retractClosure := by
  ext X
  constructor
  · rintro ⟨Y, hY, ⟨r⟩⟩
    rcases (prop_iSup_iff A Y).mp hY with ⟨i, hi⟩
    exact (prop_iSup_iff (fun i ↦ (A i).retractClosure) X).mpr ⟨i, prop_retractClosure hi r⟩
  · intro hX
    rcases (prop_iSup_iff (fun i ↦ (A i).retractClosure) X).mp hX with ⟨i, hX⟩
    exact monotone_retractClosure (le_iSup A i) _ hX

end

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [(n : ℤ) → (shiftFunctor C n).Additive] [Pretriangulated C]
variable {ι : Sort*}

-- Proof sketch: membership in an extension product with left factor `⨆ i, A i` already chooses a
-- single left object `Y`, so that object lies in some definite stage `A i`; conversely, every
-- stage maps into the supremum.
/-- Remark 13.35.6 (4): the extension product of `\bigcup A_i` with a fixed full subcategory
`\mathcal B` is the union of the extension products `A_i \star \mathcal B`. -/
@[stacks 0FX6]
theorem extensionProduct_iSup_left (A : ι → ObjectProperty C) (B : ObjectProperty C) :
    (⨆ i, A i) ⋆ B = ⨆ i, A i ⋆ B := by
  ext X
  constructor
  · intro hX
    rw [extensionProduct_iff] at hX
    rcases hX with ⟨Y, Z, f, g, h, hT, hY, hZ⟩
    rcases (prop_iSup_iff A Y).mp hY with ⟨i, hY⟩
    exact (prop_iSup_iff (fun i ↦ A i ⋆ B) X).mpr
      ⟨i, by
        rw [extensionProduct_iff]
        exact ⟨Y, Z, f, g, h, hT, hY, hZ⟩⟩
  · exact (iSup_le fun i ↦ monotone_extensionProduct_left B (le_iSup A i)) X

-- Proof sketch: the same argument as in the left-variable case, now reading the distinguished
-- triangle that defines `extensionProduct` on the right factor.
/-- Remark 13.35.6 (5): the extension product of a fixed full subcategory `\mathcal B` with
`\bigcup A_i` is the union of the extension products `\mathcal B \star A_i`. -/
@[stacks 0FX6]
theorem extensionProduct_iSup_right (B : ObjectProperty C) (A : ι → ObjectProperty C) :
    B ⋆ (⨆ i, A i) = ⨆ i, B ⋆ A i := by
  ext X
  constructor
  · intro hX
    rw [extensionProduct_iff] at hX
    rcases hX with ⟨Y, Z, f, g, h, hT, hY, hZ⟩
    rcases (prop_iSup_iff A Z).mp hZ with ⟨i, hZ⟩
    exact (prop_iSup_iff (fun i ↦ B ⋆ A i) X).mpr
      ⟨i, by
        rw [extensionProduct_iff]
        exact ⟨Y, Z, f, g, h, hT, hY, hZ⟩⟩
  · exact (iSup_le fun i ↦ monotone_extensionProduct_right B (le_iSup A i)) X

private theorem extensionProduct_iSup_of_monotone
    (A B : ℕ → ObjectProperty C) (hA : Monotone A) (hB : Monotone B) :
    (⨆ i, A i) ⋆ (⨆ i, B i) = ⨆ i, A i ⋆ B i := by
  calc
    (⨆ i, A i) ⋆ (⨆ i, B i)
        = ⨆ i, A i ⋆ (⨆ j, B j) :=
      extensionProduct_iSup_left A _
    _ = ⨆ i, ⨆ j, A i ⋆ B j := by
      simp_rw [extensionProduct_iSup_right]
    _ = ⨆ i, A i ⋆ B i := by
      apply le_antisymm
      · refine iSup_le fun i ↦ ?_
        refine iSup_le fun j ↦ ?_
        exact
          (monotone_extensionProduct_left (B j) (hA (Nat.le_max_left i j))).trans <|
            (monotone_extensionProduct_right (A (max i j))
              (hB (Nat.le_max_right i j))).trans <|
              le_iSup (fun k ↦ A k ⋆ B k) (max i j)
      · refine iSup_le fun i ↦ ?_
        exact
          (le_iSup (fun j ↦ A i ⋆ B j) i).trans <|
            le_iSup (fun j ↦ ⨆ k, A j ⋆ B k) i

-- Proof sketch: prove the statement by induction on `n`. Each `⋆`-step involves only finitely
-- many stages of the chain, and monotonicity replaces those finitely many indices by one larger
-- index.
/-- Remark 13.35.6 (6): for an increasing family `A_i`, the `n`-fold extension product of the
union, written source-faithfully as `(\bigcup A_i)^{\star n}`, equals the union of the
`n`-fold extension products `A_i^{\star n}`. -/
@[stacks 0FX6]
theorem extensionProductIter_iSup_of_monotone (A : ℕ → ObjectProperty C) (hA : Monotone A)
    (n : ℕ) :
    (⨆ i, A i).extensionProductIter n = ⨆ i, (A i).extensionProductIter n := by
  induction n with
  | zero =>
      simp
  | succ n hn =>
      let B : ℕ → ObjectProperty C := fun i ↦ (A i).extensionProductIter n
      have hB : Monotone B := by
        intro i j hij
        exact monotone_extensionProductIter (hA hij) n
      rw [extensionProductIter_succ, hn]
      simpa [B, extensionProductIter_succ] using extensionProduct_iSup_of_monotone A B hA hB

end

end CategoryTheory.ObjectProperty
