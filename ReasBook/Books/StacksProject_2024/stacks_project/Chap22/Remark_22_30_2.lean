import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap22.Lemma_22_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

noncomputable section

universe u v w

section

variable {R : Type u} [CommRing R]
variable {DGModB : Type v} {DGModA : Type w}
variable [DifferentialGradedCategory R DGModB] [DifferentialGradedCategory R DGModA]
variable [HasShift (Comp R DGModB) ℤ] [HasShift (Comp R DGModA) ℤ]
variable (homOverBFromN : DgFunctor R DGModB DGModA)
variable [homOverBFromN.mapComp.CommShift ℤ]
variable (N' : Comp R DGModB) (k : ℤ)

/- Source/core/bridge triage for Remark `22.30.2`.
- `source-facing`: the internal-Hom functor on differential graded modules from
  `Lemma_22_30_1`, namely `homOverBFromN.mapComp : Comp R DGModB ⥤ Comp R DGModA`,
  together with the shifted comparison
  `Hom_{Mod^gr_B}(N, N')[k] ⟶ Hom_{Mod^gr_B}(N, N'[k])`;
- `core/canonical`: `Functor.CommShift.commShiftIso`;
- `bridge/view`: none beyond the direct specialization of `Functor.commShiftIso` to
  `homOverBFromN.mapComp`. -/

/- Remark 22.30.2: let `R` be a ring, let `(A, d)` and `(B, d)` be differential graded algebras
over `R`, let `N` be a differential graded `(A, B)`-bimodule, and let `N'` be a right
differential graded `B`-module. For every `k : ℤ`, the source gives an isomorphism
`Hom_{Mod^gr_B}(N, N')[k] ⟶ Hom_{Mod^gr_B}(N, N'[k])` of right differential graded `A`-modules,
defined without introducing extra signs.

Lemma `22.30.1` already records the represented internal-Hom construction attached to `N` on the
underlying category of differential graded modules as the canonical owner
`homOverBFromN.mapComp`. Accordingly, this remark is recalled directly at that
source-facing owner: the displayed sign-free isomorphism is the inverse component of the
shift-commutation comparison `((homOverBFromN.mapComp).commShiftIso k).app N'`. -/
recall Functor.commShiftIso
set_option linter.hashCommand false in
#check (((homOverBFromN.mapComp).commShiftIso k).app N').symm

end
