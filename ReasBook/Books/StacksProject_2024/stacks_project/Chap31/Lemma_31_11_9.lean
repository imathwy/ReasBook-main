import StacksProject_2024.stacks_project.Chap31.Lemma_31_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]
variable {S : ShortComplex X.Modules}
variable [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]

-- Semantic recall: the source-facing Chapter 31 statement is proved affine-openwise using the
-- chapter-owned exactness bridge `ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`
-- together with the canonical scalar-regularity theorem
-- `isSMulRegular_of_range_eq_ker`.

/-- Affine-open sections of the middle term in a short exact sequence of quasi-coherent
`\mathcal O_X`-modules on an integral scheme are torsion free when the outer affine-open sections
are torsion free. -/
theorem isTorsionFree_affineOpen_of_shortExact_of_outer
    (hS : S.ShortExact) [IsTorsionFree S.X₁] [IsTorsionFree S.X₃]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Module.IsTorsionFree (Γ(X, U)) (Γ(S.X₂, U)) := by
  let TU : ShortComplex <| ModuleCat (Γ(X, U)) :=
    S.map ((Scheme.Γ(X, U)).obj (Functor.id _))
  have hTU : TU.ShortExact := by
    simpa [TU] using hS.map ((Scheme.Γ(X, U)).obj (Functor.id _))
  letI : Module.IsTorsionFree (Γ(X, U)) (Γ(S.X₁, U)) :=
    (inferInstance : IsTorsionFree S.X₁).torsionFree_sections U hU
  letI : Module.IsTorsionFree (Γ(X, U)) (Γ(S.X₃, U)) :=
    (inferInstance : IsTorsionFree S.X₃).torsionFree_sections U hU
  have hExact : Function.Exact TU.f TU.g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact TU).1 hTU.exact
  have hTorsionFree : Module.IsTorsionFree (Γ(X, U)) TU.X₂ where
    isSMulRegular _r hr :=
      Module.isSMulRegular_of_range_eq_ker
        hTU.moduleCat_injective_f hExact.linearMap_ker_eq.symm
        hr.isSMulRegular hr.isSMulRegular
  simpa [TU] using hTorsionFree

/-- The affine-open form of the short-exact torsion-freeness criterion, packaged over
`X.affineOpens`. -/
theorem isTorsionFree_affineOpens_of_shortExact_of_outer
    (hS : S.ShortExact) [IsTorsionFree S.X₁] [IsTorsionFree S.X₃]
    (U : X.affineOpens) :
    Module.IsTorsionFree (Γ(X, U)) (Γ(S.X₂, U)) := by
  simpa using isTorsionFree_affineOpen_of_shortExact_of_outer hS U.1 U.2

/-- Lemma 31.11.9: let `X` be an integral scheme. For a short exact sequence of quasi-coherent
`\mathcal O_X`-modules on `X`, if the outer terms are torsion free, then the middle term is
torsion free. -/
@[stacks 0AXX]
theorem isTorsionFree_of_shortExact_of_outer
    (hS : S.ShortExact) [IsTorsionFree S.X₁] [IsTorsionFree S.X₃] :
    IsTorsionFree S.X₂ := by
  exact isTorsionFree_of_affineOpens S.X₂ <|
    isTorsionFree_affineOpens_of_shortExact_of_outer hS

end AlgebraicGeometry.Scheme.Modules
