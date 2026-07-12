import Mathlib.CategoryTheory.Adjunction.Basic

-- Core owner declarations extracted from Remark 21.19.3 for downstream files that only need the
-- canonical derived base-change mate and its defining predicate.

open CategoryTheory

noncomputable section

universe uDX uDX' uDY uDY' vDX vDX' vDY vDY'

namespace CategoryTheory

section

variable {DX : Type uDX} {DX' : Type uDX'} {DY : Type uDY} {DY' : Type uDY'}
variable [Category.{vDX} DX] [Category.{vDX'} DX'] [Category.{vDY} DY] [Category.{vDY'} DY']

variable
  (Lf : DY ⥤ DX)
  (Lf' : DY' ⥤ DX')
  (Lg : DY ⥤ DY')
  (Lg' : DX ⥤ DX')
  (Rf : DX ⥤ DY)
  (Rf' : DX' ⥤ DY')
  (adj_f : Lf ⊣ Rf)
  (adj_f' : Lf' ⊣ Rf')
  (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg')

/- Core owner abstraction:
- `core/canonical`: `CategoryTheory.IsDerivedBaseChangeMap` and
  `CategoryTheory.derivedBaseChangeMap`;
- `bridge/view`: specialized source-facing files, such as the ringed-site incarnation in
  Remark `21.19.3`.

This file keeps only the ambient categorical owner declarations, so later chapter files can reuse
them directly without importing a more specialized ringed-site wrapper layer.
-/

/-- A morphism `Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K)` is a derived base-change map if,
after transposing across `Lf' ⊣ Rf'`, it is the pullback of the counit for `adj_f`
transported through the square comparison `Lg ⋙ Lf' ≅ Lf ⋙ Lg'`. -/
def IsDerivedBaseChangeMap
    (K : DX)
    (η : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K)) : Prop :=
  ((adj_f'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)).symm η) =
    (squareIso.hom.app (Rf.obj K) ≫ Lg'.map (adj_f.counit.app K))

/-- The canonical derived base-change morphism, defined as the mate of the pullback of the counit
through `Lf' ⊣ Rf'`. -/
noncomputable def derivedBaseChangeMap
    (K : DX) :
    Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K) :=
  adj_f'.homEquiv
    (Lg.obj (Rf.obj K))
    (Lg'.obj K)
    (squareIso.hom.app (Rf.obj K) ≫ Lg'.map (adj_f.counit.app K))

/-- Applying `Adjunction.homEquiv.symm` to `derivedBaseChangeMap` recovers the pullback of the
counit prescribed by `squareIso`. -/
theorem derivedBaseChangeMap_spec
    (K : DX) :
    ((adj_f'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)).symm
        (derivedBaseChangeMap Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso K)) =
      (squareIso.hom.app (Rf.obj K) ≫ Lg'.map (adj_f.counit.app K)) := by
  simp [derivedBaseChangeMap]

/-- Any morphism satisfying `IsDerivedBaseChangeMap` is equal to the canonical derived
base-change map. -/
theorem IsDerivedBaseChangeMap.eq_derivedBaseChangeMap
    {K : DX}
    {η : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K)}
    (hη : IsDerivedBaseChangeMap Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso K η) :
    η = derivedBaseChangeMap Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso K := by
  simpa [IsDerivedBaseChangeMap] using
    hη.trans (derivedBaseChangeMap_spec Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso K).symm

end

end CategoryTheory
