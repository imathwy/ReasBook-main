import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap22.Lemma_22_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open DifferentialGradedCategory
open HomologicalComplex

noncomputable section

universe u v w

section

/- Source/core/bridge triage:
- `source-facing`: the tensor-by-bimodule DG functor `tensorWithN : DgFunctor R DGModA DGModB`
  from Lemma `22.29.1`, together with the source isomorphism
  `(M ⊗_A N)[k] ⟶ M[k] ⊗_A N` on the underlying category of differential graded modules;
- `core/canonical`: `Functor.CommShift.commShiftIso`;
- `bridge/view`: the induced ordinary functor `tensorWithN.mapComp : Comp R DGModA ⥤
  Comp R DGModB`, whose shift comparison is the displayed sign-free tensor isomorphism. -/

variable {R : Type u} [CommRing R]
variable {DGModA : Type v} {DGModB : Type w}
variable [DifferentialGradedCategory R DGModA] [DifferentialGradedCategory R DGModB]
variable [HasShift (Comp R DGModA) ℤ] [HasShift (Comp R DGModB) ℤ]
variable (tensorWithN : DgFunctor R DGModA DGModB) [tensorWithN.mapComp.CommShift ℤ]
variable (M : Comp R DGModA) (k : ℤ)

/- Remark 22.29.2: let `R` be a ring, let `(A, d)` and `(B, d)` be differential graded algebras
over `R`, let `N` be a differential graded `(A, B)`-bimodule, and let `M` be a right
differential graded `A`-module. For every `k : ℤ`, the source gives an isomorphism
`(M ⊗_A N)[k] ⟶ M[k] ⊗_A N` of right differential graded `B`-modules, defined without
introducing extra signs.

Lemma `22.29.1` already records the tensor-by-bimodule construction at the canonical Chapter 22
owner `tensorWithN.mapComp` on the underlying category of differential graded modules. We
therefore keep this remark at that source-facing owner: once the induced functor
`tensorWithN.mapComp : Comp R DGModA ⥤ Comp R DGModB` carries its canonical `CommShift` witness,
the displayed sign-free source isomorphism is the inverse component of
`(tensorWithN.mapComp).commShiftIso k` at `M`. -/
recall Functor.commShiftIso
set_option linter.hashCommand false in
#check (((tensorWithN.mapComp).commShiftIso k).app M).symm

end

section

variable {R : Type w} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

variable (M N : Cpx) (k : ℤ)

/- Bridge companion: for the canonical fixed-right tensor functor on cochain complexes, the same
source-facing shift comparison is the inverse component of the `CommShift` isomorphism below. Its
objectwise type is the underlying cochain-complex tensor isomorphism `(M ⊗ N)[k] ≅ M[k] ⊗ N`. -/
set_option linter.hashCommand false in
#check ((((tensorRight N).mapHomologicalComplex (up ℤ)).commShiftIso k).app M).symm

end
