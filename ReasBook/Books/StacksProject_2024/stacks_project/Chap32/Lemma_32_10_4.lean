import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism flatness owner
-- `AlgebraicGeometry.Flat`; the module-side source surface is the stalkwise `Module.Flat`
-- condition on the pulled-back module, with base change written using `Scheme.Modules.pullback`.
-- Finite presentation of scheme morphisms is kept in mathlib's canonical component form:
-- `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated`.

/-- The pullback of a module on `X_i` to the source of the base change of
`φ_i : X_i ⟶ Y_i` along `T ⟶ S_i`. -/
noncomputable abbrev stageBaseChangeModule {S T Xi Yi : Scheme}
    (yi : Yi ⟶ S) (φi : Xi ⟶ Yi) (g : T ⟶ S) (ℱi : Xi.Modules) :
    (pullback φi (pullback.fst yi g)).Modules :=
  (Scheme.Modules.pullback (pullback.fst φi (pullback.fst yi g))).obj ℱi

/-- The base change of `φ_i : X_i ⟶ Y_i` along `T ⟶ S_i`, viewed as a morphism from the
base-changed source to the base-changed target. -/
noncomputable abbrev stageBaseChangeMorphism {S T Xi Yi : Scheme}
    (yi : Yi ⟶ S) (φi : Xi ⟶ Yi) (g : T ⟶ S) :
    pullback φi (pullback.fst yi g) ⟶ pullback yi g :=
  pullback.snd φi (pullback.fst yi g)

/-- The source-facing flatness condition for the pullback of an `𝒪_{X_i}`-module after base
change along `T ⟶ S_i`. -/
noncomputable abbrev stageBaseChangeRelativeModuleIsFlat {S T Xi Yi : Scheme}
    (yi : Yi ⟶ S) (φi : Xi ⟶ Yi) (g : T ⟶ S) (ℱi : Xi.Modules) : Prop :=
  ∀ x,
    let f := stageBaseChangeMorphism yi φi g
    let M := RingedSpace.stalkModuleCat (stageBaseChangeModule yi φi g ℱi) x
    letI : Module ((pullback yi g).presheaf.stalk (f.base x)) M :=
      Module.compHom M (f.stalkMap x).hom
    Module.Flat ((pullback yi g).presheaf.stalk (f.base x)) M

/-- Lemma 32.10.4: in the directed inverse-limit setup of Lemma 32.10.1, let
`φᵢ : Xᵢ ⟶ Yᵢ` be a morphism over `Sᵢ` between schemes of finite presentation over `Sᵢ`, and
let `ℱᵢ` be a quasi-coherent finite-presentation `𝒪_{Xᵢ}`-module. If the pullback of `ℱᵢ` to
the limit base change of `Xᵢ` is flat over the corresponding limit base change of `Yᵢ`, then,
after passing to some stage `i' ≥ i`, the pullback of `ℱᵢ` to the `Sᵢ'`-base change of `Xᵢ` is
flat over the `Sᵢ'`-base change of `Yᵢ`. -/
@[stacks 05LY]
theorem exists_ge_relativeModule_isFlat_stageBaseChange_of_isFlat_limitBaseChange
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i : I)
    {Xi Yi : Scheme} (xi : Xi ⟶ D.obj i) (yi : Yi ⟶ D.obj i) (φi : Xi ⟶ Yi)
    (hφi : φi ≫ yi = xi)
    [LocallyOfFinitePresentation xi] [QuasiCompact xi] [QuasiSeparated xi]
    [LocallyOfFinitePresentation yi] [QuasiCompact yi] [QuasiSeparated yi]
    (ℱi : Xi.Modules) [ℱi.IsQuasicoherent] [ℱi.IsFinitePresentation]
    (hflat : stageBaseChangeRelativeModuleIsFlat yi φi (c.π.app i) ℱi) :
    ∃ (i' : I) (hii' : i ≤ i'),
      stageBaseChangeRelativeModuleIsFlat yi φi (D.map (homOfLE hii')) ℱi := sorry

end AlgebraicGeometry
