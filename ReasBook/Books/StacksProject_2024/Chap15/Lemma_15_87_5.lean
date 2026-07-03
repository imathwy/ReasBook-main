import Mathlib
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap15.Lemma_15_87_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.SequentialInverseSystem
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Domain-style sampling for Lemma 15.87.5:
- primary domain: the Milnor short exact sequence obtained by applying the represented Hom functor
  `Hom_D(L, -)` to a chosen Milnor triangle for a derived inverse limit in a triangulated
  category;
- sampled owner declarations:
  `CategoryTheory.HasMilnorTriangle.WithMap`,
  `preadditiveCoyonedaObj`,
  `CategoryTheory.derivedLimitDifferenceMap`,
  `CategoryTheory.IsDerivedLimit`,
  `SequentialInverseSystem.firstDerivedLimit`;
- best owner abstraction: the primitive source-facing data are the chosen Milnor triangle
  `K ⟶ ∏ K_n ⟶ ∏ K_n ⟶ K[1]`, while the intrinsic derived API is the Hom tower
  `n ↦ Hom_D(L, K_n)` and its shifted variant `n ↦ Hom_D(L, K_n[-1])`, together with their
  canonical Milnor owners `limit (Ksys ⋙ preadditiveCoyonedaObj L)` and
  `firstDerivedLimit ((Ksys ⋙ shiftFunctor D (-1 : ℤ)) ⋙ preadditiveCoyonedaObj L)`;
  the theorem surface should therefore expose those owners directly, with only the represented Hom
  functor itself appearing explicitly where no shorter ambient owner already exists;
- primitive-vs-derived split:
  primitive data are the chosen Milnor triangle and its relation `ι ≫ (1 - shift) = 0`;
  derived API are the owner-level `firstDerivedLimit` model for the shifted Hom tower
  `n ↦ Hom_D(L, K_n[-1])` and the
  comparison morphism from `Hom_D(L, K)` to `\varprojlim_n Hom_D(L, K_n)`.

Source/core/bridge triage:
- `source-facing`: the Milnor short exact sequence for `Hom_D(L, -)` attached to a chosen Milnor
  triangle;
- `core/canonical`: `derivedLimitDifferenceMap`, `IsDerivedLimit`, `preadditiveCoyonedaObj`,
  and `firstDerivedLimit`;
- `bridge/view`: the comparison morphism
  `Hom_D(L, K) ⟶ \varprojlim_n Hom_D(L, K_n)` induced by the first map of the chosen Milnor
  triangle. -/

/-- The sequential inverse system `n ↦ Hom_D(L, K_n)`. -/
private abbrev representedHomTower
    (Ksys : SequentialInverseSystem D) (L : D) :
    SequentialInverseSystem (ModuleCat (End L)ᵐᵒᵖ) :=
  Ksys ⋙ preadditiveCoyonedaObj L

/-- The sequential inverse system `n ↦ Hom_D(L, K_n[-1])`. -/
private abbrev shiftedRepresentedHomTower
    (Ksys : SequentialInverseSystem D) (L : D) :
    SequentialInverseSystem (ModuleCat (End L)ᵐᵒᵖ) :=
  (Ksys ⋙ shiftFunctor D (-1 : ℤ)) ⋙ preadditiveCoyonedaObj L

private theorem homToDerivedLimit_comp_zero
    {Ksys : SequentialInverseSystem D} {K : D}
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    ι ≫ derivedLimitDifferenceMap Ksys = 0 := by
  rcases hι with ⟨δ, hδ⟩
  exact comp_distTriang_mor_zero₁₂ (Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ) hδ

private theorem homToDerivedLimitCone_naturality
    {Ksys : SequentialInverseSystem D} {K : D} (L : D)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι)
    (n : ℕ) :
    (preadditiveCoyonedaObj L).map (ι ≫ Pi.π (inverseSystemFamily Ksys) n) =
      (preadditiveCoyonedaObj L).map
          (ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1)) ≫
        (Ksys ⋙ preadditiveCoyonedaObj L).map (homOfLE (Nat.le_succ n)).op := by
  let F := preadditiveCoyonedaObj L
  have hdiff : ι ≫ derivedLimitDifferenceMap Ksys = 0 :=
    homToDerivedLimit_comp_zero hι
  have hcomp : ι ≫ Pi.π (inverseSystemFamily Ksys) n =
      ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
        Ksys.map (homOfLE (Nat.le_succ n)).op := by
    have hπ :
        ι ≫ Pi.π (inverseSystemFamily Ksys) n -
            ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
              Ksys.map (homOfLE (Nat.le_succ n)).op = 0 := by
      have hπ'' :
          ι ≫ derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n =
            ι ≫
              (Pi.π (inverseSystemFamily Ksys) n -
                Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
                  Ksys.map (homOfLE (Nat.le_succ n)).op) := by
        exact congrArg (fun f ↦ ι ≫ f) (derivedLimitDifferenceMap_comp_π Ksys n)
      have hπ' :
          0 =
            ι ≫ Pi.π (inverseSystemFamily Ksys) n -
              ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
                Ksys.map (homOfLE (Nat.le_succ n)).op := by
        rw [← Category.assoc] at hπ''
        rw [hdiff, zero_comp] at hπ''
        simpa [Preadditive.comp_sub] using hπ''
      exact hπ'.symm
    exact sub_eq_zero.mp hπ
  calc
    F.map (ι ≫ Pi.π (inverseSystemFamily Ksys) n) =
        F.map
          (ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
            Ksys.map (homOfLE (Nat.le_succ n)).op) := by
        exact congrArg F.map hcomp
    _ =
        F.map (ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1)) ≫
          (Ksys ⋙ F).map (homOfLE (Nat.le_succ n)).op := by
        simpa using
          (Functor.map_comp F
            (ι ≫ Pi.π (inverseSystemFamily Ksys) (n + 1))
            (Ksys.map (homOfLE (Nat.le_succ n)).op))

private def homToDerivedLimitCone
    {Ksys : SequentialInverseSystem D} {K : D} (L : D)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    Cone (representedHomTower Ksys L) where
  pt := (preadditiveCoyonedaObj L).obj K
  π := NatTrans.ofOpSequence
    (fun n ↦ (preadditiveCoyonedaObj L).map (ι ≫ Pi.π (inverseSystemFamily Ksys) n))
    (fun n ↦ homToDerivedLimitCone_naturality L hι n)

private def homToDerivedLimitComparison
    {Ksys : SequentialInverseSystem D} {K : D} (L : D)
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι) :
    (preadditiveCoyonedaObj L).obj K ⟶
      limit (representedHomTower Ksys L) :=
  limit.lift _ (homToDerivedLimitCone L hι)

-- Proof sketch: apply the homological functor `Hom_D(L, -)` to the chosen Milnor triangle
-- `K ⟶ ∏ K_n ⟶ ∏ K_n ⟶ K[1]`. The first map gives the comparison morphism from `Hom_D(L, K)` to
-- the inverse limit of the Hom tower, while the left term is the standard cokernel model for
-- `R^1 \!\varprojlim_n Hom_D(L, K_n[-1])`, canonically exposed as
-- `(shiftedRepresentedHomTower Ksys L).firstDerivedLimit`.
private theorem homToDerivedLimit_shortExact_of_triangle
    {Ksys : SequentialInverseSystem D} {K : D}
    [HasProduct (inverseSystemFamily Ksys)]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    (hι : HasMilnorTriangle.WithMap Ksys ι)
    (L : D) :
    ∃ (ι' :
        (shiftedRepresentedHomTower Ksys L).firstDerivedLimit ⟶
          (preadditiveCoyonedaObj L).obj K)
      (h :
        ι' ≫ homToDerivedLimitComparison L hι = 0),
      (ShortComplex.mk ι' (homToDerivedLimitComparison L hι) h).ShortExact := by
  rcases hι with ⟨δ, hδ⟩
  sorry

-- Proof sketch: unpack the chosen Milnor triangle from `hK` and apply the previous bridge-level
-- result. The public surface keeps only the canonical owner hypothesis `IsDerivedLimit Ksys K`,
-- while the specific Milnor presentation remains internal.
/-- Lemma 15.87.5: if `K` is a derived limit of a sequential inverse system `(K_n)_n`, then for
every object `L` there is a short exact sequence
`0 ⟶ R^1 \!\varprojlim \operatorname{Hom}_D(L, K_n[-1]) ⟶ \operatorname{Hom}_D(L, K) ⟶
\varprojlim_n \operatorname{Hom}_D(L, K_n) ⟶ 0`. -/
theorem homToDerivedLimit_hasMilnorShortExactSequence
    (Ksys : SequentialInverseSystem D) {K : D}
    (hK : IsDerivedLimit Ksys K) (L : D) :
    ∃ (ι :
        (shiftedRepresentedHomTower Ksys L).firstDerivedLimit ⟶
          (preadditiveCoyonedaObj L).obj K)
      (π :
        (preadditiveCoyonedaObj L).obj K ⟶
          limit (representedHomTower Ksys L))
      (h :
        ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  rcases hK with ⟨_, ⟨ι, δ, hδ⟩⟩
  let hι : HasMilnorTriangle.WithMap Ksys ι := ⟨δ, hδ⟩
  rcases homToDerivedLimit_shortExact_of_triangle hι L with ⟨ι', h, hshort⟩
  exact ⟨ι', homToDerivedLimitComparison L hι, h, hshort⟩

end

end CategoryTheory
