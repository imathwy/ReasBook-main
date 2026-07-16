import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_32_15

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

variable {Z X S : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]

-- Semantic recall: `lean_leansearch` surfaced the ring-level cotangent exactness owner
-- `Algebra.Extension.exact_cotangentComplex_toKaehler`; local Chapter 29 precedent fixes the
-- scheme-level sequence through `immersionConormalSheaf`, `Ω[f.toShHom]`, and the comparison-map
-- formula from Lemma 29.32.15.

/-- Helper for Lemma 29.34.17: the right map in the conormal-relative-differentials sequence is
the comparison morphism supplied by Lemma 29.32.8 for the square `Z ⟶ X` over `S`. -/
private def conormalRelativeDifferentialsRightMapSpec
    (i : Z ⟶ X) (f : X ⟶ S)
    (ψ : (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom] ⟶
      Ω[(i ≫ f).toShHom]) : Prop :=
  ∀ {U : (Opens X)ᵒᵖ} (t : X.presheaf.obj U),
    let U' := (Opens.map i.base).op.obj U
    let φi := i.toRingCatSheafHom
    let iSharpU := φi.hom.app U
    ((((SheafOfModules.pullbackPushforwardAdjunction
          φi).homEquiv _ _)
        ψ).val.app U)
      (((d[f.toShHom]).app U).d t) =
      ((d[(i ≫ f).toShHom]).app U').d (iSharpU t)

/-- Lemma 29.34.17: let `i : Z ⟶ X` be an immersion of schemes over `S`. If `Z` is smooth over
`S`, then the canonical conormal sequence
`0 ⟶ \mathcal C_{Z/X} ⟶ i^* \Omega_{X/S} ⟶ \Omega_{Z/S} ⟶ 0`
from Lemma 29.32.15 is short exact. -/
@[stacks 06AA]
theorem exists_shortExact_conormalRelativeDifferentialsSequence_of_smooth
    (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S) (hZ : Smooth (i ≫ f)) :
    ∃ δ : immersionConormalSheaf i ⟶
        (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom],
      ∃ ψ : (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom] ⟶
          Ω[(i ≫ f).toShHom],
        conormalRelativeDifferentialsRightMapSpec i f ψ ∧
          ∃ hδψ : δ ≫ ψ = 0, (ShortComplex.mk δ ψ hδψ).ShortExact := sorry

end AlgebraicGeometry
