import StacksProject_2024.Chap22.AdmissibleShortExact
import StacksProject_2024.Chap22.PropertyI

open CategoryTheory

universe u

namespace CochainComplex

noncomputable section

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ

/-- A differential graded `A`-module is the middle term of an admissible short exact sequence
whose outer terms are products of shifts of the fixed dual object `Aᵛ`. This keeps the
source-facing short exact witness in the canonical `ShortComplex` owner, while giving later files
a reusable predicate for the middle-term condition from Lemma 22.21.3. -/
def IsMiddleOfAdmissibleShortExactWithDualShiftEnds (Avee I : DGMod) : Prop :=
  ∃ S : ShortComplex DGMod,
    I = S.X₂ ∧
      IsAdmissibleShortExact dgModuleUnderlyingGradedHomSystem S ∧
      IsProductOfDualShifts Avee S.X₁ ∧
      IsProductOfDualShifts Avee S.X₃

/-- The middle-term owner from Lemma 22.21.3 exposes its canonical short-complex witness without
requiring downstream files to unfold the definition. -/
theorem IsMiddleOfAdmissibleShortExactWithDualShiftEnds.exists_shortComplex
    {Avee I : DGMod} (hI : IsMiddleOfAdmissibleShortExactWithDualShiftEnds Avee I) :
    ∃ S : ShortComplex DGMod,
      I = S.X₂ ∧
        IsAdmissibleShortExact dgModuleUnderlyingGradedHomSystem S ∧
        IsProductOfDualShifts Avee S.X₁ ∧
        IsProductOfDualShifts Avee S.X₃ :=
  hI

/-- Lemma 22.21.3: for a differential graded `A`-module `M` and a fixed dual object `Aᵛ`,
there exists a morphism `M ⟶ I` into the middle term `I = S.X₂` of an admissible short exact
sequence `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` such that the map is injective on the underlying graded
module, the induced maps `Coker(d_M) ⟶ Coker(d_I)` are injective in every degree, and the end
terms are products of shifts `Aᵛ⟦k⟧`. The admissible short exact structure is expressed by the
canonical Chapter 22 owner `IsAdmissibleShortExact`. -/
@[stacks 09KT]
theorem exists_forgetMono_monoOnDifferentialCokernels_admissibleShortExact
    (Avee M : DGMod) :
    ∃ (S : ShortComplex DGMod) (ι : M ⟶ S.X₂),
      Mono (dgModuleUnderlyingGradedHomSystem.map ι) ∧
        MonoOnDifferentialCokernels ι ∧
        IsAdmissibleShortExact dgModuleUnderlyingGradedHomSystem S ∧
        IsProductOfDualShifts Avee S.X₁ ∧
        IsProductOfDualShifts Avee S.X₃ := by
  sorry

/-- Companion bridge for Lemma 22.21.3: the target object can be used directly through the
middle-term owner `IsMiddleOfAdmissibleShortExactWithDualShiftEnds`, instead of repeatedly
reconstructing the ambient short complex. -/
theorem exists_forgetMono_monoOnDifferentialCokernels_middleOfAdmissibleShortExactWithDualShiftEnds
    (Avee M : DGMod) :
    ∃ (I : DGMod) (ι : M ⟶ I),
      Mono (dgModuleUnderlyingGradedHomSystem.map ι) ∧
        MonoOnDifferentialCokernels ι ∧
        IsMiddleOfAdmissibleShortExactWithDualShiftEnds Avee I := by
  rcases exists_forgetMono_monoOnDifferentialCokernels_admissibleShortExact Avee M with
    ⟨S, ι, hι, hcoker, hS, hX₁, hX₃⟩
  exact ⟨S.X₂, ι, hι, hcoker, S, rfl, hS, hX₁, hX₃⟩

end

end

end CochainComplex
