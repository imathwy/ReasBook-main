import Mathlib
import StacksProject_2024.Chap15.Lemma_15_23_5
import StacksProject_2024.Chap31.Lemma_31_11_3
import StacksProject_2024.Chap31.Lemma_31_12_2
import StacksProject_2024.Chap31.Lemma_31_12_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]
variable {S : ShortComplex X.Modules}
variable [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]

-- Semantic recall: `lean_leansearch` surfaced the module-level kernel-closure theorem
-- `isReflexive_of_exact_of_isReflexive_of_isTorsionFree`; locally, Chapter 31 already uses the
-- `ShortComplex X.Modules` owner for exact sequences and the predicates `IsReflexive` and
-- `IsTorsionFree` on coherent/quasi-coherent `\mathcal O_X`-modules.

/-- Affine-open sections of the kernel term in a short exact sequence of coherent
`\mathcal O_X`-modules are reflexive when the middle term is reflexive and the quotient is
torsion free. -/
theorem isReflexive_affineOpen_of_shortExact_of_isReflexive_of_isTorsionFree
    (hS : S.ShortExact) [IsReflexive S.X₂] [IsTorsionFree S.X₃]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Module.IsReflexive (Γ(X, U)) (Γ(S.X₁, U)) := by
  let TU : ShortComplex <| ModuleCat (Γ(X, U)) :=
    S.map ((Scheme.Γ(X, U)).obj (Functor.id _))
  have hTU : TU.ShortExact := by
    simpa [TU] using hS.map ((Scheme.Γ(X, U)).obj (Functor.id _))
  letI : Module.IsReflexive (Γ(X, U)) (Γ(S.X₂, U)) :=
    (isReflexive_iff_affineOpen S.X₂).1 inferInstance U hU
  letI : Module.IsTorsionFree (Γ(X, U)) (Γ(S.X₃, U)) :=
    (isTorsionFree_iff_affineOpen S.X₃).1 inferInstance U hU
  simpa [TU] using
    (isReflexive_of_exact_of_isReflexive_of_isTorsionFree
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact TU).1 hTU.exact)
      hTU.moduleCat_injective_f :
      Module.IsReflexive (Γ(X, U)) TU.X₁)

/-- The affine-open form of the short-exact reflexivity criterion, packaged over
`X.affineOpens`. -/
theorem isReflexive_affineOpens_of_shortExact_of_isReflexive_of_isTorsionFree
    (hS : S.ShortExact) [IsReflexive S.X₂] [IsTorsionFree S.X₃]
    (U : X.affineOpens) :
    Module.IsReflexive (Γ(X, U)) (Γ(S.X₁, U)) := by
  simpa using
    isReflexive_affineOpen_of_shortExact_of_isReflexive_of_isTorsionFree hS U.1 U.2

/-- Lemma 31.12.7: let `X` be an integral locally Noetherian scheme. Let
`0 → \mathcal{F} → \mathcal{F}' → \mathcal{F}''` be a short exact sequence of coherent
`\mathcal O_X`-modules. If `\mathcal{F}'` is reflexive and `\mathcal{F}''` is torsion free, then
`\mathcal{F}` is reflexive. -/
@[stacks 0EBG]
theorem isReflexive_of_shortExact_of_isReflexive_of_isTorsionFree
    (hS : S.ShortExact) [IsReflexive S.X₂] [IsTorsionFree S.X₃] :
    IsReflexive S.X₁ := by
  exact (isReflexive_iff_affineOpen S.X₁).2 <|
    isReflexive_affineOpen_of_shortExact_of_isReflexive_of_isTorsionFree hS

end AlgebraicGeometry.Scheme.Modules
