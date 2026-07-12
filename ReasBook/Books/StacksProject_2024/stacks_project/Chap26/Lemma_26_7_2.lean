import Mathlib
import Mathlib.CategoryTheory.Sites.Monoidal
import StacksProject_2024.Chap17.TensorPowerSheaf
import StacksProject_2024.Chap26.Lemma_26_7_1
import StacksProject_2024.LinearAlgebra.PowerOperations

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry
open scoped TensorProduct

noncomputable section

universe u

-- Semantic recall: `lean_leansearch` surfaced the canonical affine owner `ModuleCat.tilde`; the
-- sheaf-side tensor and internal-Hom owners are the ambient monoidal/closed structures on
-- `(Spec R).Modules`. The compiling Chapter 17 tensor-power owner is `T^[n]`; the symmetric and
-- exterior clauses below use the affine specialization represented by the associated sheaf of the
-- corresponding algebraic power.

section

variable (R : CommRingCat.{u})
variable (M N : ModuleCat R)
variable (n : ℕ)

/-- Lemma 26.7.2 (1): on the affine scheme `X = Spec(R)`, the associated module sheaf of the
tensor product `M ⊗_R N` is canonically isomorphic to the tensor product of the associated module
sheaves `\widetilde M ⊗_{\mathcal O_X} \widetilde N`; equivalently, the canonical affine counit
for this tensor-product sheaf is an isomorphism. -/
@[stacks 01I8]
theorem tildeTensorIso [MonoidalCategory (Spec R).Modules] :
    IsIso (@Scheme.Modules.fromTildeΓ R
      (tensorObj (tilde M) (tilde N) : (Spec R).Modules)) := sorry

/-- Lemma 26.7.2 (2): on `X = Spec(R)`, the associated module sheaf of the `n`th tensor power of
`M` is canonically isomorphic to the `n`th tensor-power sheaf of `\widetilde M`; equivalently,
the canonical affine counit for that tensor-power sheaf is an isomorphism. -/
@[stacks 01I8]
theorem tildeTensorPowerIso
    [MonoidalCategory (SheafOfModules (RingedSpace.ringCatSheaf (Spec R).toSheafedSpace))] :
    IsIso (@Scheme.Modules.fromTildeΓ R (T^[n] (tilde M) : (Spec R).Modules)) := sorry

/-- Lemma 26.7.2 (3): on `X = Spec(R)`, the associated module sheaf of the `n`th symmetric power
of `M` is canonically isomorphic to the `n`th symmetric-power sheaf of `\widetilde M`; in the
affine specialization this is recorded through the canonical affine counit for the associated
sheaf of the algebraic symmetric power. -/
@[stacks 01I8]
theorem tildeSymmetricPowerIso :
    IsIso (@Scheme.Modules.fromTildeΓ R
      (tilde (ModuleCat.of R (Sym[R] (SymmetricPower.UFin n) M)))) := sorry

/-- Lemma 26.7.2 (4): on `X = Spec(R)`, the associated module sheaf of the `n`th exterior power
of `M` is canonically isomorphic to the `n`th exterior-power sheaf of `\widetilde M`; in the
affine specialization this is recorded through the canonical affine counit for the associated
sheaf of the algebraic exterior power. -/
@[stacks 01I8]
theorem tildeExteriorPowerIso :
    IsIso (@Scheme.Modules.fromTildeΓ R (tilde (M.exteriorPower n))) := sorry

/-- Lemma 26.7.2 (5): if `M` is a finitely presented `R`-module, then on `X = Spec(R)` the
internal-Hom sheaf `\mathcal H\!\mathit{om}_{\mathcal O_X}(\widetilde M, \widetilde N)` is
canonically isomorphic to the associated module sheaf of `\operatorname{Hom}_R(M, N)`;
equivalently, the canonical affine counit for the internal-Hom sheaf is an isomorphism. -/
@[stacks 01I8]
theorem tildeInternalHomIso
    [MonoidalCategory (Spec R).Modules]
    [MonoidalClosed (Spec R).Modules]
    [MonoidalCategory (SheafOfModules (RingedSpace.ringCatSheaf (Spec R).toSheafedSpace))]
    [MonoidalClosed (SheafOfModules (RingedSpace.ringCatSheaf (Spec R).toSheafedSpace))]
    [Module.FinitePresentation R M] :
    IsIso (@Scheme.Modules.fromTildeΓ R
      (((ihom (tilde M)).obj (tilde N)) : (Spec R).Modules)) := sorry

end
