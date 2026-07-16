import StacksProject_2024.stacks_project.Chap10.«10_69_0_1»
import StacksProject_2024.stacks_project.Chap10.Definition_10_86_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_22_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.SequentialInverseSystem
open CategoryTheory.ShortComplex
open Opposite
open scoped DirectSum

noncomputable section

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]
variable [HasWeakSheafify J (ModuleCat.{max u v w} A)]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})]

local notation "ModSheaf" => Sheaf J (ModuleCat A)

/- Domain-style sampling for Lemma 21.22.2:
- primary domain: site cohomology of sequential inverse systems of `A`-module sheaves, with the
  stabilization condition expressed by the chapter owner
  `CategoryTheory.SequentialInverseSystem.IsMittagLeffler`, and with the source ACC input
  recorded as Noetherianity over `idealAssociatedGradedRing I`;
- sampled owner declarations:
  * `CategoryTheory.SequentialInverseSystem`;
  * `CategoryTheory.SequentialInverseSystem.transitionMap`;
  * `CategoryTheory.SequentialInverseSystem.IsMittagLeffler`;
  * `CategoryTheory.IsIdealPowerRowFamily`;
  * `CategoryTheory.ShortComplex`;
  * `CategoryTheory.Functor.eventualRange`;
  * `CategoryTheory.Functor.eventualRangeAddSubgroup`;
  * `idealAssociatedGradedRing`;
  * `CategoryTheory.siteModuleCohomologyTower`.
- owner choice:
  * `source-facing`: the source theorem about the ideal-power eventual ranges forcing the
    Mittag-Leffler condition for the cohomology tower;
  * `core/canonical`: `SequentialInverseSystem`, `.transitionMap`, `.IsMittagLeffler`,
    `IsIdealPowerRowFamily`, `ShortComplex`, `Functor.eventualRange`,
    `Functor.eventualRangeAddSubgroup`, `siteModuleCohomologyTower`, and
    `idealAssociatedGradedRing`;
  * `bridge/view`: the fixed-right ideal-power rows
    `0 → I^n ℱ_{m+1} → ℱ_{m+1} → ℱ_n → 0`, together with the named
    eventual-range terms `N_n`.
- primitive data: the ideal `I`, the towers `ℱ` and `powSheaf`, the canonical left maps
  `I^n ℱ_{m+1} → ℱ_{m+1}`, bundled into the source row-family owner
  `IsIdealPowerRowFamily ℱ powSheaf idealPowerι`;
- derived API: the ideal-power cohomology towers `siteModuleCohomologyTower (powSheaf n) (p + 1)`
  and the graded direct sum of their eventual-range additive subgroups at each stage `n`.
-/

/-- For fixed `n`, this is the source term `N_n`, expressed as the canonical additive subgroup
carried by the eventual range of the cohomology tower
`m ↦ H^{p+1}(𝒞, I^n ℱ_{m+1})`. -/
abbrev siteModuleCohomologyIdealPowerEventualRange
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf) (p n : ℕ) :
    AddSubgroup (((siteModuleCohomologyTower (powSheaf n) (p + 1)).obj (op n)) :
      AddCommGrpCat.{max u v w}) :=
  (siteModuleCohomologyTower (powSheaf n) (p + 1)).eventualRangeAddSubgroup (op n)

/-- The source graded object `⨁ n, N_n` built from the eventual-range pieces of the ideal-power
cohomology towers. -/
abbrev siteModuleCohomologyIdealPowerEventualRangeDirectSum
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf) (p : ℕ) :
    Type (max u v w) :=
  ⨁ n : ℕ, siteModuleCohomologyIdealPowerEventualRange powSheaf p n

/-- The degree-`n` homogeneous subgroup of the source direct sum `⨁ n, N_n`. -/
abbrev siteModuleCohomologyIdealPowerEventualRangeGrading
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf) (p n : ℕ) :
    AddSubgroup (siteModuleCohomologyIdealPowerEventualRangeDirectSum powSheaf p) :=
  AddMonoidHom.range
    (DirectSum.of (fun n ↦ siteModuleCohomologyIdealPowerEventualRange powSheaf p n) n)

omit [HasWeakSheafify J (ModuleCat.{max u v w} A)] in
/-- Helper for Lemma 21.22.2: membership in the eventual-range subgroup `N_n` means belonging to
the image of every later transition morphism in the tower
`m ↦ H^{p+1}(𝒞, I^n ℱ_{m+1})`. -/
theorem mem_siteModuleCohomologyIdealPowerEventualRange_iff
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf) (p n : ℕ)
    {x : (((siteModuleCohomologyTower (powSheaf n) (p + 1)).obj (op n)) :
      AddCommGrpCat.{max u v w})} :
    x ∈ siteModuleCohomologyIdealPowerEventualRange powSheaf p n ↔
      ∀ m : ℕ, ∀ hnm : n ≤ m,
        x ∈ Set.range (((siteModuleCohomologyTower (powSheaf n) (p + 1)).transitionMap hnm).hom) := by
  -- Rewrite the additive subgroup back to the owner eventual range in `Type`.
  change
    x ∈ ((siteModuleCohomologyTower (powSheaf n) (p + 1) ⋙ forget AddCommGrpCat).eventualRange
      (op n)) ↔
      ∀ m : ℕ, ∀ hnm : n ≤ m,
        x ∈ Set.range (((siteModuleCohomologyTower (powSheaf n) (p + 1)).transitionMap hnm).hom)
  constructor
  · intro hx m hnm
    have hx' :
        ∀ ⦃i : ℕᵒᵖ⦄ (f : i ⟶ op n),
          x ∈ Set.range
            (((siteModuleCohomologyTower (powSheaf n) (p + 1) ⋙ forget AddCommGrpCat).map f)) :=
      (show
          x ∈ ((siteModuleCohomologyTower (powSheaf n) (p + 1) ⋙
            forget AddCommGrpCat).eventualRange (op n)) ↔
            ∀ ⦃i : ℕᵒᵖ⦄ (f : i ⟶ op n),
              x ∈ Set.range
                (((siteModuleCohomologyTower (powSheaf n) (p + 1) ⋙
                  forget AddCommGrpCat).map f))
        from Functor.mem_eventualRange_iff
          (siteModuleCohomologyTower (powSheaf n) (p + 1) ⋙ forget AddCommGrpCat)).1 hx
    simpa [SequentialInverseSystem.transitionMap] using hx' ((homOfLE hnm).op)
  · intro hx
    refine (show
        x ∈ ((siteModuleCohomologyTower (powSheaf n) (p + 1) ⋙
          forget AddCommGrpCat).eventualRange (op n)) ↔
          ∀ ⦃i : ℕᵒᵖ⦄ (f : i ⟶ op n),
            x ∈ Set.range
              (((siteModuleCohomologyTower (powSheaf n) (p + 1) ⋙
                forget AddCommGrpCat).map f))
      from Functor.mem_eventualRange_iff
        (siteModuleCohomologyTower (powSheaf n) (p + 1) ⋙ forget AddCommGrpCat)).2 ?_
    intro j g
    have hnj : n ≤ unop j := leOfHom g.unop
    simpa [SequentialInverseSystem.transitionMap] using hx (unop j) hnj

/-- The source fixed-right ideal-power rows
`0 → I^n ℱ_{m+1} → ℱ_{m+1} → ℱ_n → 0`
are exact and compatible with the transition maps of `powSheaf n` and `ℱ`. -/
class IsIdealPowerRowFamily
    (ℱ : SequentialInverseSystem ModSheaf)
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf)
    (idealPowerι : ∀ n m : ℕ, ∀ _ : n ≤ m, (powSheaf n).obj (op m) ⟶ ℱ.obj (op (m + 1))) :
    Prop where
  comp_zero (n m : ℕ) (hnm : n ≤ m) :
    idealPowerι n m hnm ≫ ℱ.transitionMap (Nat.le_trans hnm (Nat.le_succ m)) = 0
  shortExact (n m : ℕ) (hnm : n ≤ m) :
    (ShortComplex.mk
      (idealPowerι n m hnm)
      (ℱ.transitionMap (Nat.le_trans hnm (Nat.le_succ m)))
      (comp_zero n m hnm)).ShortExact
  naturality {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) :
    CommSq
      ((powSheaf n).transitionMap hml)
      (idealPowerι n l (Nat.le_trans hnm hml))
      (idealPowerι n m hnm)
      (ℱ.transitionMap (Nat.succ_le_succ hml))

omit [HasWeakSheafify J (ModuleCat.{max u v w} A)] [HasSheafify J AddCommGrpCat.{max u v w}]
  [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})] in
/-- The diagonal ideal-power sheaf `I^n ℱ_{n + 1}` attached to a source row family. -/
abbrev idealPowerDiagonalSheaf
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf) : ℕ → ModSheaf :=
  fun n ↦ (powSheaf n).obj (op n)

omit [HasWeakSheafify J (ModuleCat.{max u v w} A)] [HasSheafify J AddCommGrpCat.{max u v w}]
  [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})] in
/-- The diagonal left map `I^n ℱ_{n + 1} → ℱ_{n + 1}` extracted from a source row family. -/
abbrev idealPowerDiagonalι
    (ℱ : SequentialInverseSystem ModSheaf)
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf)
    (idealPowerι : ∀ n m : ℕ, ∀ _ : n ≤ m, (powSheaf n).obj (op m) ⟶ ℱ.obj (op (m + 1))) :
    ∀ n : ℕ, idealPowerDiagonalSheaf powSheaf n ⟶ ℱ.obj (op (n + 1)) :=
  fun n ↦ idealPowerι n n le_rfl

omit [HasWeakSheafify J (ModuleCat.{max u v w} A)] [HasSheafify J AddCommGrpCat.{max u v w}]
  [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})] in
/-- The diagonal left maps compose to zero with the canonical transition maps. -/
theorem idealPowerDiagonalCompZero
    (ℱ : SequentialInverseSystem ModSheaf)
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf)
    (idealPowerι : ∀ n m : ℕ, ∀ _ : n ≤ m, (powSheaf n).obj (op m) ⟶ ℱ.obj (op (m + 1)))
    (hpow : IsIdealPowerRowFamily ℱ powSheaf idealPowerι)
    (n : ℕ) :
    idealPowerDiagonalι ℱ powSheaf idealPowerι n ≫ ℱ.stepMap n = 0 := by
  simpa [idealPowerDiagonalι] using hpow.comp_zero n n le_rfl

omit [HasWeakSheafify J (ModuleCat.{max u v w} A)] [HasSheafify J AddCommGrpCat.{max u v w}]
  [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})] in
/-- The diagonal short exact row `0 → I^n ℱ_{n + 1} → ℱ_{n + 1} → ℱ_n → 0`. -/
abbrev idealPowerDiagonalRow
    (ℱ : SequentialInverseSystem ModSheaf)
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf)
    (idealPowerι : ∀ n m : ℕ, ∀ _ : n ≤ m, (powSheaf n).obj (op m) ⟶ ℱ.obj (op (m + 1)))
    (hpow : IsIdealPowerRowFamily ℱ powSheaf idealPowerι)
    (n : ℕ) :
    ShortComplex ModSheaf :=
  idealPowerRow
    ℱ
    (idealPowerDiagonalSheaf powSheaf)
    (idealPowerDiagonalι ℱ powSheaf idealPowerι)
    (idealPowerDiagonalCompZero ℱ powSheaf idealPowerι hpow)
    n

omit [HasWeakSheafify J (ModuleCat.{max u v w} A)] [HasSheafify J AddCommGrpCat.{max u v w}]
  [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})] in
/-- The diagonal row of a source ideal-power row family is short exact. -/
theorem IsIdealPowerRowFamily.shortExactDiagonal
    {ℱ : SequentialInverseSystem ModSheaf}
    {powSheaf : ℕ → SequentialInverseSystem ModSheaf}
    {idealPowerι : ∀ n m : ℕ, ∀ _ : n ≤ m, (powSheaf n).obj (op m) ⟶ ℱ.obj (op (m + 1))}
    (hpow : IsIdealPowerRowFamily ℱ powSheaf idealPowerι)
    (n : ℕ) :
    (idealPowerDiagonalRow ℱ powSheaf idealPowerι hpow n).ShortExact := by
  simpa [idealPowerDiagonalRow, idealPowerDiagonalι, idealPowerDiagonalCompZero] using
    hpow.shortExact n n le_rfl

/-- Helper for Lemma 21.22.2: the fixed-right-term row
`0 → I^n ℱ_{m+1} → ℱ_{m+1} → ℱ_n → 0`
attached to a source ideal-power row family. -/
private abbrev idealPowerRowAt
    (ℱ : SequentialInverseSystem ModSheaf)
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf)
    (idealPowerι : ∀ n m : ℕ, ∀ _ : n ≤ m, (powSheaf n).obj (op m) ⟶ ℱ.obj (op (m + 1)))
    (hpow : IsIdealPowerRowFamily ℱ powSheaf idealPowerι)
    (n m : ℕ) (hnm : n ≤ m) :
    ShortComplex ModSheaf :=
  ShortComplex.mk
    (idealPowerι n m hnm)
    (ℱ.transitionMap (Nat.le_trans hnm (Nat.le_succ m)))
    (hpow.comp_zero n m hnm)

omit [HasWeakSheafify J (ModuleCat.{max u v w} A)] [HasSheafify J AddCommGrpCat.{max u v w}]
  [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})] in
/-- Helper for Lemma 21.22.2: the left square comparing the fixed-right-term row at stage `m`
to the diagonal row at stage `n` is exactly the source naturality square. -/
private theorem idealPowerRowAtToDiagonal_comm_left
    (ℱ : SequentialInverseSystem ModSheaf)
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf)
    (idealPowerι : ∀ n m : ℕ, ∀ _ : n ≤ m, (powSheaf n).obj (op m) ⟶ ℱ.obj (op (m + 1)))
    (hpow : IsIdealPowerRowFamily ℱ powSheaf idealPowerι)
    (n m : ℕ) (hnm : n ≤ m) :
    (powSheaf n).transitionMap hnm ≫ idealPowerι n n le_rfl =
      idealPowerι n m hnm ≫ ℱ.transitionMap (Nat.succ_le_succ hnm) := by
  -- Specialize the source compatibility square to the diagonal target row.
  simpa using (hpow.naturality le_rfl hnm).w

omit [HasWeakSheafify J (ModuleCat.{max u v w} A)] [HasSheafify J AddCommGrpCat.{max u v w}]
  [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})] in
/-- Helper for Lemma 21.22.2: the middle-to-right square of the row comparison is the defining
composition law of the sequential inverse system `ℱ`. -/
private theorem idealPowerRowAtToDiagonal_comm_right
    (ℱ : SequentialInverseSystem ModSheaf)
    (n m : ℕ) (hnm : n ≤ m) :
    ℱ.transitionMap (Nat.succ_le_succ hnm) ≫ ℱ.stepMap n =
      ℱ.transitionMap (Nat.le_trans hnm (Nat.le_succ m)) := by
  -- The transition maps compose exactly as the source rows require.
  rw [SequentialInverseSystem.transitionMap, SequentialInverseSystem.transitionMap,
    ← Functor.map_comp]
  exact congrArg ℱ.map (Subsingleton.elim _ _)

/-- Helper for Lemma 21.22.2: the canonical morphism from the stage-`m` row
`0 → I^n ℱ_{m+1} → ℱ_{m+1} → ℱ_n → 0`
to the diagonal row
`0 → I^n ℱ_{n+1} → ℱ_{n+1} → ℱ_n → 0`. -/
private abbrev idealPowerRowAtToDiagonal
    (ℱ : SequentialInverseSystem ModSheaf)
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf)
    (idealPowerι : ∀ n m : ℕ, ∀ _ : n ≤ m, (powSheaf n).obj (op m) ⟶ ℱ.obj (op (m + 1)))
    (hpow : IsIdealPowerRowFamily ℱ powSheaf idealPowerι)
    (n m : ℕ) (hnm : n ≤ m) :
    idealPowerRowAt ℱ powSheaf idealPowerι hpow n m hnm ⟶
      idealPowerDiagonalRow ℱ powSheaf idealPowerι hpow n :=
  ShortComplex.homMk
    ((powSheaf n).transitionMap hnm)
    (ℱ.transitionMap (Nat.succ_le_succ hnm))
    (𝟙 (ℱ.obj (op n)))
    (idealPowerRowAtToDiagonal_comm_left
      ℱ powSheaf idealPowerι hpow n m hnm)
    (idealPowerRowAtToDiagonal_comm_right
      ℱ n m hnm)

omit [HasWeakSheafify J (ModuleCat.{max u v w} A)] [HasSheafify J AddCommGrpCat.{max u v w}]
  [HasExt (Sheaf J AddCommGrpCat.{max u v w})] in
/-- Helper for Lemma 21.22.2: after applying the forgetful sheaf-composition functor, the left
square of `idealPowerRowAtToDiagonal` still commutes. -/
private theorem idealPowerRowAtToDiagonal_comm_left_map
    (ℱ : SequentialInverseSystem ModSheaf)
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf)
    (idealPowerι : ∀ n m : ℕ, ∀ _ : n ≤ m, (powSheaf n).obj (op m) ⟶ ℱ.obj (op (m + 1)))
    (hpow : IsIdealPowerRowFamily ℱ powSheaf idealPowerι)
    (n m : ℕ) (hnm : n ≤ m) :
    (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map ((powSheaf n).transitionMap hnm) ≫
        ((idealPowerDiagonalRow ℱ powSheaf idealPowerι hpow n).map
            (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat))).f =
      ((idealPowerRowAt ℱ powSheaf idealPowerι hpow n m hnm).map
          (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat))).f ≫
        (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map
          (ℱ.transitionMap (Nat.succ_le_succ hnm)) := by
  -- Unfold the mapped row morphisms and reduce to the source square.
  change
    (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map ((powSheaf n).transitionMap hnm) ≫
        (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map (idealPowerι n n le_rfl) =
      (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map (idealPowerι n m hnm) ≫
        (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map
          (ℱ.transitionMap (Nat.succ_le_succ hnm))
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg
    ((sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map)
    (idealPowerRowAtToDiagonal_comm_left
      ℱ powSheaf idealPowerι hpow n m hnm)

omit [HasWeakSheafify J (ModuleCat.{max u v w} A)] [HasSheafify J AddCommGrpCat.{max u v w}]
  [HasExt (Sheaf J AddCommGrpCat.{max u v w})] in
/-- Helper for Lemma 21.22.2: after applying the forgetful sheaf-composition functor, the right
square of `idealPowerRowAtToDiagonal` still commutes. -/
private theorem idealPowerRowAtToDiagonal_comm_right_map
    (ℱ : SequentialInverseSystem ModSheaf)
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf)
    (idealPowerι : ∀ n m : ℕ, ∀ _ : n ≤ m, (powSheaf n).obj (op m) ⟶ ℱ.obj (op (m + 1)))
    (hpow : IsIdealPowerRowFamily ℱ powSheaf idealPowerι)
    (n m : ℕ) (hnm : n ≤ m) :
    (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map
        (ℱ.transitionMap (Nat.succ_le_succ hnm)) ≫
        ((idealPowerDiagonalRow ℱ powSheaf idealPowerι hpow n).map
            (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat))).g =
      ((idealPowerRowAt ℱ powSheaf idealPowerι hpow n m hnm).map
          (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat))).g ≫
        (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map (𝟙 (ℱ.obj (op n))) := by
  -- Unfold the mapped row morphisms and reduce to the transition-map composition law.
  change
    (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map
        (ℱ.transitionMap (Nat.succ_le_succ hnm)) ≫
        (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map (ℱ.stepMap n) =
      (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map
          (ℱ.transitionMap (Nat.le_trans hnm (Nat.le_succ m))) ≫
        (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map (𝟙 (ℱ.obj (op n)))
  rw [Functor.map_id, Category.comp_id, ← Functor.map_comp]
  exact congrArg
    ((sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map)
    (idealPowerRowAtToDiagonal_comm_right ℱ n m hnm)

/-- Helper for Lemma 21.22.2: after applying the forgetful sheaf-composition functor, each
stage-`m` row `0 → I^n ℱ_{m+1} → ℱ_{m+1} → ℱ_n → 0` remains short
exact. This is the exact-functor bridge needed to apply
`ShortComplex.ShortExact.extClass_naturality` to the source row-comparison square. -/
private theorem idealPowerRowAt_map_shortExact
    (ℱ : SequentialInverseSystem ModSheaf)
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf)
    (idealPowerι : ∀ n m : ℕ, ∀ _ : n ≤ m, (powSheaf n).obj (op m) ⟶ ℱ.obj (op (m + 1)))
    (hpow : IsIdealPowerRowFamily ℱ powSheaf idealPowerι)
    (n m : ℕ) (hnm : n ≤ m) :
    ((idealPowerRowAt ℱ powSheaf idealPowerι hpow n m hnm).map
      (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat))).ShortExact := by
  sorry

/-- Helper for Lemma 21.22.2: after mapping the source row-comparison square to additive sheaves,
the owner theorem `ShortComplex.ShortExact.extClass_naturality` rewrites the stage-`m`
extension class into the diagonal extension class. -/
private theorem idealPowerRowAt_extClass_naturality
    (ℱ : SequentialInverseSystem ModSheaf)
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf)
    (idealPowerι : ∀ n m : ℕ, ∀ _ : n ≤ m, (powSheaf n).obj (op m) ⟶ ℱ.obj (op (m + 1)))
    (hpow : IsIdealPowerRowFamily ℱ powSheaf idealPowerι)
    (n m : ℕ) (hnm : n ≤ m) :
    (idealPowerRowAt_map_shortExact
        ℱ powSheaf idealPowerι hpow n m hnm).extClass.comp
        (Ext.mk₀
          ((sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map
            ((powSheaf n).transitionMap hnm)))
        (zero_add 1) =
      (idealPowerRowAt_map_shortExact
        ℱ powSheaf idealPowerι hpow n n
        le_rfl).extClass := by
  -- The mapped row morphism is exactly the source comparison square between the stage-`m`
  -- row and the diagonal row.
  let mappedRowHom :
      ((idealPowerRowAt ℱ powSheaf idealPowerι hpow n m hnm).map
          (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat))) ⟶
        ((idealPowerDiagonalRow ℱ powSheaf idealPowerι hpow n).map
          (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat))) :=
    ShortComplex.homMk
      ((sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map ((powSheaf n).transitionMap hnm))
      ((sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map
        (ℱ.transitionMap (Nat.succ_le_succ hnm)))
      ((sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).map (𝟙 (ℱ.obj (op n))))
      (idealPowerRowAtToDiagonal_comm_left_map
        ℱ powSheaf idealPowerι hpow n m hnm)
      (idealPowerRowAtToDiagonal_comm_right_map
        ℱ powSheaf idealPowerι hpow n m hnm)
  -- Apply the owner naturality theorem before unfolding the boundary maps themselves.
  simpa [mappedRowHom, Functor.map_id] using
      (ShortExact.extClass_naturality
        (idealPowerRowAt_map_shortExact
          ℱ powSheaf idealPowerι hpow n m hnm)
        (idealPowerRowAt_map_shortExact
          ℱ powSheaf idealPowerι hpow n n le_rfl)
        mappedRowHom)

/-- Helper for Lemma 21.22.2: the connecting morphism of the stage-`m` row becomes the
diagonal connecting morphism after the cohomology transition map
`H^{p + 1}(𝒞, I^n ℱ_{m + 1}) → H^{p + 1}(𝒞, I^n ℱ_{n + 1})`.
This is the source second diagram rewritten at the level of actual boundary maps. -/
private theorem idealPowerRowAt_connecting_naturality
    (ℱ : SequentialInverseSystem ModSheaf)
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf)
    (idealPowerι : ∀ n m : ℕ, ∀ _ : n ≤ m, (powSheaf n).obj (op m) ⟶ ℱ.obj (op (m + 1)))
    (hpow : IsIdealPowerRowFamily ℱ powSheaf idealPowerι)
    (p : ℕ)
    (δ : ∀ i : ℕ, ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op i))) ⟶
      ((siteModuleCohomologyFunctor (p + 1)).obj (idealPowerDiagonalSheaf powSheaf i)))
    (hδ : IsIdealPowerConnectingFamily
      ℱ
      (idealPowerDiagonalSheaf powSheaf)
      (idealPowerDiagonalι ℱ powSheaf idealPowerι)
      (idealPowerDiagonalCompZero ℱ powSheaf idealPowerι hpow)
      p
      δ)
    (n m : ℕ) (hnm : n ≤ m) :
    let δnm :
      ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op n))) ⟶
      ((siteModuleCohomologyTower (powSheaf n) (p + 1)).obj (op m)) :=
      AddCommGrpCat.ofHom
        ((idealPowerRowAt_map_shortExact
          ℱ powSheaf idealPowerι hpow
          n m hnm).extClass.postcomp
            ((constantSheaf J AddCommGrpCat.{max u v w}).obj (AddCommGrpCat.of (ULift ℤ))) rfl)
    δnm ≫ (siteModuleCohomologyTower (powSheaf n) (p + 1)).transitionMap hnm =
      δ n := by
  sorry

/-- Helper for Lemma 21.22.2: the image of the diagonal boundary map
`H^p(𝒞, ℱ_n) → H^{p + 1}(𝒞, I^n ℱ_{n + 1})`
lands in the eventual-range subgroup `N_n`. This is the source claim
`im(δ_n) ≤ N_n`, reduced to the concrete boundary-map naturality for the stage-`m`
rows. -/
private theorem idealPowerConnectingRange_le_siteModuleCohomologyIdealPowerEventualRange
    (ℱ : SequentialInverseSystem ModSheaf)
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf)
    (idealPowerι : ∀ n m : ℕ, ∀ _ : n ≤ m, (powSheaf n).obj (op m) ⟶ ℱ.obj (op (m + 1)))
    (hpow : IsIdealPowerRowFamily ℱ powSheaf idealPowerι)
    (p : ℕ)
    (δ : ∀ i : ℕ, ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op i))) ⟶
      ((siteModuleCohomologyFunctor (p + 1)).obj (idealPowerDiagonalSheaf powSheaf i)))
    (hδ : IsIdealPowerConnectingFamily
      ℱ
      (idealPowerDiagonalSheaf powSheaf)
      (idealPowerDiagonalι ℱ powSheaf idealPowerι)
      (idealPowerDiagonalCompZero ℱ powSheaf idealPowerι hpow)
      p
      δ)
    (n : ℕ) :
    idealPowerConnectingRange
        ℱ
        (idealPowerDiagonalSheaf powSheaf)
        p
        δ
        n ≤
      siteModuleCohomologyIdealPowerEventualRange powSheaf p n := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  -- Unpack the eventual-range subgroup degreewise and use the same source class `y` upstairs.
  refine
    (mem_siteModuleCohomologyIdealPowerEventualRange_iff
      powSheaf p n).2 ?_
  intro m hnm
  let δnm :
      ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op n))) ⟶
        ((siteModuleCohomologyTower (powSheaf n) (p + 1)).obj (op m)) :=
    AddCommGrpCat.ofHom
      ((idealPowerRowAt_map_shortExact
        ℱ powSheaf idealPowerι hpow
        n m hnm).extClass.postcomp
          ((constantSheaf J AddCommGrpCat.{max u v w}).obj (AddCommGrpCat.of (ULift ℤ))) rfl)
  refine ⟨δnm.hom y, ?_⟩
  -- Apply the source second diagram after evaluating it on `y`.
  have hδ :=
    idealPowerRowAt_connecting_naturality
      ℱ powSheaf idealPowerι hpow
      p δ hδ n m hnm
  simpa [δnm] using congrArg (fun f ↦ f.hom y) hδ

/-- The eventual-range direct sum inherits its scalar action from any ambient
`idealAssociatedGradedRing I`-module structure. This explicit projection instance keeps the
source-facing theorem below inferable without reintroducing an expensive derived `SMul`
search on `⨁ n, N_n`. -/
instance siteModuleCohomologyIdealPowerEventualRangeDirectSum_smul
    (I : Ideal A)
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf) (p : ℕ)
    [hModule : Module (idealAssociatedGradedRing I)
      (siteModuleCohomologyIdealPowerEventualRangeDirectSum powSheaf p)] :
    SMul (idealAssociatedGradedRing I)
      (siteModuleCohomologyIdealPowerEventualRangeDirectSum powSheaf p) :=
  hModule.toSMul

-- Proof sketch: for each `n ≤ m`, the canonical short exact row
-- `0 → I^n ℱ_{m+1} → ℱ_{m+1} → ℱ_n → 0` yields connecting maps
-- landing in the eventual range `siteModuleCohomologyIdealPowerEventualRange powSheaf p n`.
-- Compatibility of the left maps with the transition maps of `powSheaf n` and `ℱ` forces the
-- image of each connecting map to lie in that eventual range. The source ACC hypothesis is then
-- imposed on the graded family `⊕ N_n`, and Lemma `21.22.1` gives stabilization of the images in
-- the inverse system `n ↦ H^p(𝒞, ℱ_n)`.
/-- Lemma 21.22.2: let `ℱ` be a sequential inverse system of sheaves of `A`-modules on the site
`(C, J)`, let `I` be an ideal of `A`, and let `powSheaf n` model the inverse system
`m ↦ I^n ℱ_{m+1}`. Assume that for every `n ≤ m` the canonical row
`0 → I^n ℱ_{m+1} → ℱ_{m+1} → ℱ_n → 0`, with right map the transition
map `ℱ_{m+1} → ℱ_n`, define a source row family
`IsIdealPowerRowFamily ℱ powSheaf idealPowerι`. Write
`N_n = siteModuleCohomologyIdealPowerEventualRange powSheaf p n` for the eventual range at stage
`n` of the tower `m ↦ H^{p+1}(𝒞, I^n ℱ_{m+1})`.
If the graded family `⨁ n, N_n` is Noetherian over the associated graded ring
`⨁ n, I^n / I^(n + 1)`, then the inverse system `n ↦ H^p(𝒞, ℱ_n)` satisfies the
Mittag-Leffler condition `2`, expressed by the chapter owner
`SequentialInverseSystem.IsMittagLeffler`. -/
@[stacks 0GYR]
theorem site_module_cohomology_tower_isMittagLeffler_of_idealPower_eventualRange_ascending_chain_condition
    (I : Ideal A)
    (ℱ : SequentialInverseSystem ModSheaf)
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf)
    (idealPowerι : ∀ n m : ℕ, ∀ _ : n ≤ m, (powSheaf n).obj (op m) ⟶ ℱ.obj (op (m + 1)))
    (hpow : IsIdealPowerRowFamily ℱ powSheaf idealPowerι)
    (p : ℕ)
    [Module (idealAssociatedGradedRing I)
      (siteModuleCohomologyIdealPowerEventualRangeDirectSum powSheaf p)]
    [SetLike.GradedSMul (idealAssociatedGradedRingGrade I)
      (siteModuleCohomologyIdealPowerEventualRangeGrading powSheaf p)]
    [IsNoetherian (idealAssociatedGradedRing I)
      (siteModuleCohomologyIdealPowerEventualRangeDirectSum powSheaf p)] :
    SequentialInverseSystem.IsMittagLeffler (siteModuleCohomologyTower ℱ p) := by
  -- The remaining proof uses the internal degreewise containment
  -- `idealPowerConnectingRange_le_siteModuleCohomologyIdealPowerEventualRange`, the source
  -- Noetherian hypothesis on `⊕ n, N_n`, and Lemma `21.22.1` together with
  -- `idealPowerRowAt_connecting_naturality`.
  sorry

end

end CategoryTheory
