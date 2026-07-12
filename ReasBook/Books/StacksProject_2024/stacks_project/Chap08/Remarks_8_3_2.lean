import Mathlib
import StacksProject_2024.Chap04.Lemma_4_33_7
import StacksProject_2024.Chap08.Definition_8_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C} [p.IsFibered]
variable {hc : PullbackChoice p}
variable {U : C} {𝒰 : SemiRepresentableFamily.Over U} [HasDescentPullbacks 𝒰]

/- Domain-style sampling for Remark 8.3.2:
- primary domain: descent data for a fixed-target family in a fibred category, specialized to the
  canonical diagonal and switching maps of pairwise overlaps.
- inspected owner-level declarations:
  `DescentDatum.iso`,
  `Pseudofunctor.DescentData.iso`,
  `SemiRepresentableFamily.Over.diagonal`,
  `SemiRepresentableFamily.Over.switch`.
- best owner abstraction: the chapter owner remains `DescentDatum p hc 𝒰`, while the generic
  pullback comparison `D.descentData.iso` is the canonical owner-level way to pull the overlap
  comparison isomorphisms back along arbitrary maps such as the diagonal and switch.
- primitive data: the fixed-target family `𝒰`, the chosen pullback system `hc`, and the descent
  datum fields `D.obj` and `D.iso`.
- derived API: the diagonal self-comparison and the switched overlap comparison from the remark.

Source/core/bridge triage:
- `source-facing`: the remark's diagonal and switching comparison isomorphisms.
- `core/canonical`: `DescentDatum.iso`, `Pseudofunctor.DescentData.iso`, and the overlap maps
  `𝒰.diagonal` and `𝒰.switch`.
- `bridge/view`: the identification of the generic diagonal self-comparison with an automorphism
  of `D.obj i` through `hc.pullbackIdComponentIso`. -/

namespace DescentDatum

variable (D : DescentDatum p hc 𝒰)

/-- The pullback of `φᵢᵢ` along the canonical diagonal
`Uᵢ ⟶ Uᵢ ×[U] Uᵢ`, identified as an automorphism of `Xᵢ` itself via the
identity-pullback comparison. -/
noncomputable def diagonalSelfComparisonIso
    (i : 𝒰.index) :
    D.obj i ≅ D.obj i :=
  hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i) ≪≫
    D.descentData.iso ((𝒰.obj i).hom) (𝟙 ((𝒰.obj i).left)) (𝟙 ((𝒰.obj i).left)) ≪≫
      (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).symm

/-- The pullback of `φⱼᵢ` along the canonical switching morphism
`Uᵢ ×[U] Uⱼ ⟶ Uⱼ ×[U] Uᵢ`, identified as an isomorphism from `pr₁^* Xⱼ`
back to `pr₀^* Xᵢ`. -/
noncomputable def switchedOverlapComparisonIso
    (i j : 𝒰.index) :
    hc.obj (𝒰.pr1 i j) (D.obj j) ≅ hc.obj (𝒰.pr0 i j) (D.obj i) :=
  D.descentData.iso
    (𝒰.pr0 i j ≫ (𝒰.obj i).hom)
    (𝒰.pr1 i j)
    (𝒰.pr0 i j)
    ((𝒰.pr0_map_eq_pr1_map i j).symm)
    rfl

-- Proof sketch: the middle factor is the generic self-comparison isomorphism
-- `D.descentData.iso (𝒰.obj i).hom (𝟙 _) (𝟙 _)`, whose morphism is `𝟙` by
-- `D.descentData.hom_self`; conjugate by the identity-pullback comparison.
/-- Remarks 8.3.2 (1): pulling back `φ_{ii}` along the canonical diagonal
`Uᵢ ⟶ Uᵢ ×[U] Uᵢ` gives the identity automorphism of `Xᵢ`. -/
theorem diagonalSelfComparisonIso_eq_refl
    (i : 𝒰.index) :
    D.diagonalSelfComparisonIso i = Iso.refl _ := sorry

-- Proof sketch: on the overlap `Uᵢ ×[U] Uⱼ`, pull back the cocycle identity for the triple
-- `(i, j, i)` along `𝒰.delta13 i j`; the first factor becomes `D.iso i j`, the second becomes the
-- switched pullback of `φ_{ji}`, and the third factor becomes the diagonal self-comparison from
-- part `(1)`, hence the identity.
/-- Remarks 8.3.2 (2): after pulling back `φ_{ji}` along the canonical switching morphism
`Uᵢ ×[U] Uⱼ ⟶ Uⱼ ×[U] Uᵢ`, its composition with `φ_{ij}` is the identity on
`pr₀^* Xᵢ`. -/
theorem overlapComparison_comp_switchedOverlapComparison_eq_refl
    (i j : 𝒰.index) :
    D.iso i j ≪≫ D.switchedOverlapComparisonIso i j = Iso.refl _ := sorry

end DescentDatum

end CategoryTheory
