import StacksProject_2024.stacks_project.Chap15.«15_96_5_1»
import StacksProject_2024.stacks_project.Chap15.Remark_15_96_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CochainComplex

universe u

section

variable {A : Type u} [CommRing A]

namespace ModFSquared
namespace Nat

/-- Helper for 15.96.5.2: after comparing reduction with extension degreewise, the owner homology
in degree `i` identifies canonically with the bounded-below reduced homology. -/
noncomputable abbrev reduceModIdealAHomologyIso
    (I : Ideal A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).homology (i : ℤ) ≅
      (reduceModIdealA I M).homology i :=
  sorry

/-- Helper for 15.96.5.2: the bounded-below Berthelot-Ogus Bockstein morphism on
`H^i(M^\bullet / fM^\bullet)`. -/
noncomputable abbrev bockstein
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ)
    (hM : IsTermwiseFTorsionFree f M) :
    (reduceModIdealA (principalIdeal f) M).homology i ⟶
      (reduceModIdealA (principalIdeal f) M).homology (i + 1) :=
  sorry

end Nat
end ModFSquared

open ModFSquared.Nat

/-- Helper for 15.96.5.2: two successive bounded-below Berthelot-Ogus Bockstein morphisms
compose to zero. -/
theorem berthelotOgusBockstein_sq
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M) (i : ℕ) :
    bockstein f M i hM ≫ bockstein f M (i + 1) hM = 0 := by
  sorry

/-- Helper for 15.96.5.2: the Berthelot-Ogus square-zero theorem packaged in the exact
function-valued form expected by `CochainComplex.of`. -/
theorem berthelotOgusBockstein_sq_for_of
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M) :
    ∀ i, (fun j ↦ bockstein f M j hM) i ≫ (fun j ↦ bockstein f M j hM) (i + 1) = 0 := by
  intro i
  simpa using berthelotOgusBockstein_sq f M hM i

/-- Helper for 15.96.5.2: the square-zero witness for the Bockstein differential in the exact
pointwise form used by the canonical `CochainComplex.of` constructor. -/
theorem berthelotOgusBockstein_sq_for_complex
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M) :
    ∀ i, bockstein f M i hM ≫ bockstein f M (i + 1) hM = 0 := by
  intro i
  simpa using berthelotOgusBockstein_sq f M hM i

/-- 15.96.5.2: the canonical cohomology complex `H^\bullet(M^\bullet / f)` is the nonnegative
cochain complex whose degree-`i` term is `H^i(M^\bullet / fM^\bullet)` and whose differential is
the Berthelot-Ogus Bockstein morphism on the scalar-restricted `A`-linear bridge
`reduceModIdealA (principalIdeal f) M`. This keeps the source-facing cohomological grading and uses the
bounded-below owner declaration `ModFSquared.Nat.bockstein` for the differential. -/
abbrev modfCohomologyBocksteinComplex
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M) :
    NatModuleCochainComplex A :=
  CochainComplex.of
    (fun i ↦ (reduceModIdealA (principalIdeal f) M).homology i)
    (fun i ↦ bockstein f M i hM)
    (berthelotOgusBockstein_sq_for_complex f M hM)

/-- The degree-`i` term of the canonical Bockstein complex is
`H^i((M^\bullet / fM^\bullet)_A)`. -/
@[simp] theorem modfCohomologyBocksteinComplex_X
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M) (i : ℕ) :
    (modfCohomologyBocksteinComplex f M hM).X i =
      (reduceModIdealA (principalIdeal f) M).homology i :=
  rfl

/-- The differential of the canonical Bockstein complex is the Berthelot-Ogus Bockstein map. -/
@[simp] theorem modfCohomologyBocksteinComplex_d
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M) (i : ℕ) :
    (modfCohomologyBocksteinComplex f M hM).d i (i + 1) =
      bockstein f M i hM := by
  simpa only [modfCohomologyBocksteinComplex] using
    (CochainComplex.of_d
      (fun j ↦ (reduceModIdealA (principalIdeal f) M).homology j)
      (fun j ↦ bockstein f M j hM)
      (berthelotOgusBockstein_sq_for_complex f M hM)
      i)

end
