import StacksProject_2024.stacks_project.Chap30.«30_23_3_1»

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open Scheme.IdealSheafData

noncomputable section

universe u v

-- Semantic recall: `lean_leansearch` surfaced `Functor.essImage` as the canonical owner for
-- "in the essential image"; local Chapter 30 precedent supplies `CoherentCompletionFunctor` for
-- the completion functor (30.23.3.1) and `Scheme.IdealSheafData` for closed thickenings.

/-- Lemma 30.25.2: let `X` be a Noetherian scheme with quasi-coherent ideal sheaves `I` and
`K`. For each positive `e`, let `X_e` be the closed subscheme cut out by `K^e` and let
`I_e = I O_{X_e}`. If the completion functor
`Coh(O_{X_e}) ⥤ Coh(X_e, I_e)` is an equivalence for every `e ≥ 1`, and an object
`E` of `Coh(X, I)` admits a map to the completion of a coherent sheaf whose kernel and
cokernel are annihilated by a power of `K`, then `E` lies in the essential image of the
completion functor (30.23.3.1). The target-side torsion condition is kept as an explicit
predicate on the canonical target category `Scheme.CoherentFormalModules X I`. -/
@[stacks 088A]
theorem coherentFormalModule_mem_essImage_of_thickenings_equiv_and_kPowerTorsionApprox
    {X : Scheme.{u}} [IsNoetherian X] {I K : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (ctxThickening : (e : ℕ+) →
      CoherentCompletionFunctor
        ((ofIdeals fun U : X.affineOpens ↦ K.ideal U ^ (e : ℕ)).subscheme)
        (I.comap ((ofIdeals fun U : X.affineOpens ↦ K.ideal U ^ (e : ℕ)).subschemeι)))
    (hThickeningEquiv : ∀ e : ℕ+, (ctxThickening e).IsEquivalence)
    (targetKPowerTorsion :
      {E₁ E₂ : Scheme.CoherentFormalModules X I} → (E₁ ⟶ E₂) → Prop)
    (E : Scheme.CoherentFormalModules X I)
    (hApprox : ∃ H : RingedSpace.Coh X.toRingedSpace,
      ∃ alpha : E ⟶ ctx.obj H,
        targetKPowerTorsion alpha) :
    ctx.essImage E := sorry
