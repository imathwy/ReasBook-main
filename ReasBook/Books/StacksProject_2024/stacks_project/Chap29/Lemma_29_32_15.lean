import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_31_3
import StacksProject_2024.stacks_project.Chap29.Lemma_29_32_8

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

-- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.IsImmersion` and the
-- ring-level owner `Algebra.Extension.exact_cotangentComplex_toKaehler`; local Chapter 29
-- precedent fixes the scheme-level surfaces as `immersionConormalSheaf i`, `Ω[f.toShHom]`, and
-- comparison maps characterized by Lemma 29.32.8.

/-- Helper for Lemma 29.32.15: the right map in the conormal-relative-differentials sequence is
the comparison morphism supplied by Lemma 29.32.8 for the square
`Z ⟶ X` over `S`. -/
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

/-- Helper for Lemma 29.32.15: the displayed conormal-relative-differentials sequence is exact
and continues to `0`; exactness makes the left map the conormal map into the kernel of the
right comparison map. -/
private def conormalRelativeDifferentialsExactToZero
    (i : Z ⟶ X) (f : X ⟶ S)
    (δ : immersionConormalSheaf i ⟶
      (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom])
    (ψ : (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom] ⟶
      Ω[(i ≫ f).toShHom]) : Prop :=
  ∃ hδψ : δ ≫ ψ = 0, (ShortComplex.mk δ ψ hδψ).Exact ∧ Epi ψ

/-- Lemma 29.32.15: for an immersion of schemes `i : Z ⟶ X` over `S`, there is a canonical exact
sequence
`\mathcal C_{Z/X} ⟶ i^* \Omega_{X/S} ⟶ \Omega_{Z/S} ⟶ 0`. The right map is the comparison map
from Lemma 29.32.8, and the left map is the conormal map induced locally by `d_{X/S}`. -/
@[stacks 01UZ]
theorem exists_exact_conormalRelativeDifferentialsSequence
    (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S) :
    ∃ δ : immersionConormalSheaf i ⟶
        (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom],
      ∃ ψ : (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom] ⟶
          Ω[(i ≫ f).toShHom],
        conormalRelativeDifferentialsRightMapSpec i f ψ ∧
          conormalRelativeDifferentialsExactToZero i f δ ψ := sorry

end AlgebraicGeometry
