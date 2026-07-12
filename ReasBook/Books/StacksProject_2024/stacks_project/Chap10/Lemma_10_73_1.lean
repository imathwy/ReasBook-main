import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits Abelian

universe u

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R')

private abbrev extScalars :=
  ModuleCat.extendScalars (algebraMap R R')

private abbrev resScalars :=
  ModuleCat.restrictScalars (algebraMap R R')

private abbrev baseChangeAdj :=
  ModuleCat.extendRestrictScalarsAdj (algebraMap R R')

/-
Domain triage:
- `source-facing`: `moduleCatExtFlatBaseChangeComparison` is the textbook flat base-change map on
  `Ext`.
- `core/canonical`: the owner abstractions are `Functor.mapExtAddHom` for `extScalars` and
  `resScalars`, together with the unit/counit of `ModuleCat.extendRestrictScalarsAdj`.
- `bridge/view`: `moduleCatExtFlatBaseChangeAdjointComparison` is the adjoint transpose of the
  source-facing map, expressed directly from the owner API rather than from a parallel wrapper.

Primitive data are only the ring map and the two modules. The comparison maps are derived from the
change-of-rings adjunction and `Ext` functoriality, so no extra packaged data is introduced.
-/

/- The textbook base-change comparison
`Ext^i_{R'}(R' ⊗[R] M, N') → Ext^i_R(M, N'|_R)`, which is the canonical owner-object form of the
source-facing textbook map `Ext^i_{R'}(M ⊗[R] R', N') → Ext^i_R(M, N'|_R)` via tensor symmetry. -/
def moduleCatExtFlatBaseChangeComparison (i : ℕ) :
    Ext (extScalars.obj M) N' i →+ Ext M (resScalars.obj N') i :=
  AddMonoidHom.comp
    ((Ext.mk₀ (baseChangeAdj.unit.app M)).precomp (resScalars.obj N') (zero_add i))
    (resScalars.mapExtAddHom (extScalars.obj M) N' i)

/-- The adjoint-transposed comparison from `Ext_R(M, N'|_R)` to
`Ext_{R'}(R' ⊗[R] M, N')`, obtained by applying `Ext` to extension of scalars and then
postcomposing with the adjunction counit. This is a `bridge/view` companion to the source-facing
map of Lemma `10.73.1`. -/
abbrev moduleCatExtFlatBaseChangeAdjointComparison
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    Ext M (resScalars.obj N') i →+ Ext (extScalars.obj M) N' i :=
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap R R')
  letI : PreservesFiniteLimits extScalars :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  letI : extScalars.Additive := adj.left_adjoint_additive
  AddMonoidHom.comp
    ((Ext.mk₀ (adj.counit.app N')).postcomp (extScalars.obj M) (add_zero i))
    (extScalars.mapExtAddHom M (resScalars.obj N') i)

-- Proof sketch: choose a projective resolution `P• → M`; flatness makes `R' ⊗[R] P•` a
-- projective resolution of `R' ⊗[R] M`, and Lemma `10.14.3` identifies the two Hom complexes
-- `Hom_{R'}(R' ⊗[R] P•, N')` and `Hom_R(P•, N')`, so the induced comparison on homology is
-- bijective in every degree.
/-- Lemma 10.73.1: for a flat ring map `R → R'`, an `R`-module `M`, and an `R'`-module `N'`,
the textbook natural map
`Ext^i_{R'}(M ⊗[R] R', N') → Ext^i_R(M, N'|_R)`
is an isomorphism for every `i`; equivalently, the canonical owner-object comparison
`Ext^i_{R'}(R' ⊗[R] M, N') → Ext^i_R(M, N'|_R)` is an isomorphism. -/
theorem moduleCat_ext_flat_baseChange_isIso
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    IsIso (AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeComparison M N' i)) := sorry

/-- Companion reformulation of Lemma 10.73.1 as bijectivity of the source-facing textbook map. -/
theorem moduleCat_ext_flat_baseChange_bijective
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    Function.Bijective (moduleCatExtFlatBaseChangeComparison M N' i) := by
  let f := AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeComparison M N' i)
  letI : IsIso f := moduleCat_ext_flat_baseChange_isIso M N' hf i
  exact ⟨(AddCommGrpCat.mono_iff_injective f).mp inferInstance,
    (AddCommGrpCat.epi_iff_surjective f).mp inferInstance⟩

/-- The adjoint-transposed comparison is likewise an isomorphism under the flatness hypothesis. -/
theorem moduleCat_ext_flat_baseChange_adjoint_isIso
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    IsIso (AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i)) := sorry

/-- Companion reformulation of the adjoint-transposed comparison as a bijection. -/
theorem moduleCat_ext_flat_baseChange_adjoint_bijective
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    Function.Bijective (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i) := by
  let f := AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i)
  letI : IsIso f := moduleCat_ext_flat_baseChange_adjoint_isIso M N' hf i
  exact ⟨(AddCommGrpCat.mono_iff_injective f).mp inferInstance,
    (AddCommGrpCat.epi_iff_surjective f).mp inferInstance⟩

end
