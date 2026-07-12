import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import StacksProject_2024.Chap12.Lemma_12_14_12
import StacksProject_2024.Chap22.Definition_22_7_1
import StacksProject_2024.Chap22.Lemma_22_7_3

open CategoryTheory
open CategoryTheory.CochainComplex
open HomologicalComplex

universe u

namespace CochainComplex

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ

/-- In the canonical cochain-complex model for differential graded `A`-modules, the Chapter 22
admissibility predicate for a short exact sequence is exactly the existence of degreewise
splittings of the underlying short complex. -/
theorem isAdmissibleShortExact_iff_nonempty_degreewiseSplitting
    (S : ShortComplex DGMod) :
    IsAdmissibleShortExact dgModuleUnderlyingGradedHomSystem S ↔
      Nonempty (∀ n : ℤ, (degreewiseShortComplex S n).Splitting) := by
  constructor
  · rintro ⟨hS, hf, hg⟩
    refine ⟨fun n ↦ ?_⟩
    let T := degreewiseShortComplex S n
    have hT : T.ShortExact := by
      simpa [T] using hS.map_of_exact (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)
    letI : IsSplitEpi (dgModuleUnderlyingGradedHomSystem.map S.g) := hg
    exact ShortComplex.Splitting.ofExactOfSection T hT.exact
      (section_ (dgModuleUnderlyingGradedHomSystem.map S.g) n)
      (by
        simpa [T, dgModuleUnderlyingGradedHomSystem] using
          congrArg (fun k ↦ k n) (IsSplitEpi.id (dgModuleUnderlyingGradedHomSystem.map S.g)))
      hT.mono_f
  · rintro ⟨σ⟩
    let hS : S.ShortExact := by
      refine HomologicalComplex.shortExact_of_degreewise_shortExact S ?_
      intro n
      simpa [degreewiseShortComplex] using (σ n).shortExact
    refine ⟨hS, IsSplitMono.mk' ⟨fun n ↦ (σ n).r, ?_⟩, IsSplitEpi.mk' ⟨fun n ↦ (σ n).s, ?_⟩⟩
    · funext n
      simpa [dgModuleUnderlyingGradedHomSystem] using (σ n).f_r
    · funext n
      simpa [dgModuleUnderlyingGradedHomSystem] using (σ n).s_g

end

end CochainComplex
