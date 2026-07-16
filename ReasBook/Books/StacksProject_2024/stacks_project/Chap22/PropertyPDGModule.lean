import StacksProject_2024.stacks_project.Chap22.Definition_22_7_1
import StacksProject_2024.stacks_project.Chap22.Lemma_22_7_3
import StacksProject_2024.stacks_project.Chap22.Lemma_22_20_1
import StacksProject_2024.stacks_project.Chap22.ShiftedFreeDGModule

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace CochainComplex

section

variable {A : Type u} [Ring A]

/-- A chosen filtration exhibiting property `(P)` for a differential graded `A`-module in the
canonical cochain-complex model. -/
structure PropertyPFiltration (P : CochainComplex (ModuleCat.{u, u} A) ℤ) where
  /-- The filtration stages, indexed so that `stage 0` is the source's `F_{-1}P = 0`. -/
  stage : ℕ → CochainComplex (ModuleCat.{u, u} A) ℤ
  /-- The initial stage is zero. -/
  stageZero : IsZero (stage 0)
  /-- The admissible filtration inclusions `F_iP ⟶ F_{i + 1}P`. -/
  inclusion : ∀ n : ℕ, stage n ⟶ stage (n + 1)
  /-- The filtration inclusions are monomorphisms in the differential graded module category. -/
  mono : ∀ n : ℕ, Mono (inclusion n)
  /-- The filtration inclusions are admissible, i.e. split after forgetting the differential. -/
  admissible : ∀ n : ℕ, IsAdmissibleMono dgModuleUnderlyingGradedHomSystem (inclusion n)
  /-- The sequential filtration admits its colimit. -/
  hasColimit : HasColimit (Functor.ofSequence inclusion)
  /-- The module is the union, encoded as the colimit, of its filtration stages. -/
  colimitIso : let _ := hasColimit; P ≅ colimit (Functor.ofSequence inclusion)
  /-- The summand index type for the direct sum describing each successive quotient. -/
  pieceIndex : ℕ → Type u
  /-- The shift degree of each free summand in a successive quotient. -/
  pieceDegree : ∀ n : ℕ, pieceIndex n → ℤ
  /-- The coproduct of shifted free modules appearing in each successive quotient exists. -/
  pieceHasCoproduct :
    ∀ n : ℕ,
      HasCoproduct (fun i : pieceIndex n ↦ shiftedFreeDGModule A (pieceDegree n i))
  /-- Each successive quotient is identified with a direct sum of shifts of `A`. -/
  pieceIso :
    ∀ n : ℕ,
      let _ := pieceHasCoproduct n
      cokernel (inclusion n) ≅
        ∐ fun i : pieceIndex n ↦ shiftedFreeDGModule A (pieceDegree n i)

namespace PropertyPFiltration

/-- A chosen property `(P)` filtration supplies the colimit of its stage diagram. -/
instance instHasColimit {P : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (F : PropertyPFiltration P) :
    HasColimit (Functor.ofSequence F.inclusion) :=
  F.hasColimit

/-- The differential graded module filtration from Chapter 22, viewed as the generic filtration
owner used elsewhere in the chapter. -/
abbrev toFiltration {P : CochainComplex (ModuleCat.{u, u} A) ℤ} (F : PropertyPFiltration P) :
    _root_.PropertyPFiltration P where
  stage := F.stage
  step := F.inclusion
  toCocone :=
    (colimit.cocone (Functor.ofSequence F.inclusion)).ι ≫
      (Functor.const ℕ).map F.colimitIso.inv
  isColimit := by
    refine (colimit.isColimit (Functor.ofSequence F.inclusion)).ofIsoColimit ?_
    refine Cocone.ext F.colimitIso.symm ?_
    intro n
    simp

/-- The canonical map from the `n`-th filtration stage to the ambient differential graded module.
-/
abbrev coconeApp {P : CochainComplex (ModuleCat.{u, u} A) ℤ} (F : PropertyPFiltration P)
    (n : ℕ) : F.stage n ⟶ P :=
  F.toFiltration.toCocone.app n

end PropertyPFiltration

/-- A differential graded `A`-module has property `(P)` if it admits a filtration by admissible
monomorphisms whose union is the module and whose successive quotients are direct sums of shifts
of `A`. -/
def HasPropertyP (P : CochainComplex (ModuleCat.{u, u} A) ℤ) : Prop :=
  Nonempty (PropertyPFiltration P)

/-- A chosen property `(P)` filtration exhibits property `(P)` on the underlying differential
graded module. -/
theorem PropertyPFiltration.hasPropertyP {P : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (F : PropertyPFiltration P) :
    HasPropertyP P :=
  ⟨F⟩

end

end CochainComplex
