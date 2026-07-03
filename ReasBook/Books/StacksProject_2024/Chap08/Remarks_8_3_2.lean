import Mathlib
import stacks_project.Chap04.Lemma_4_33_7
import stacks_project.Chap08.Definition_8_3_1

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
    D.diagonalSelfComparisonIso i = Iso.refl _ := by
  -- Compare the diagonal self-comparison with the identity after forgetting to the total category.
  apply Iso.ext
  apply Functor.Fiber.hom_ext
  -- Unfold the diagonal comparison and rewrite its middle factor via the prime-level pullback API.
  simp only [diagonalSelfComparisonIso, Iso.trans_hom, Functor.id_obj,
    Pseudofunctor.DescentData.iso_hom, Pseudofunctor.DescentData'.descentData_hom]
  -- The middle self-comparison is the identity pullback morphism, so the conjugation collapses.
  have hself :
      (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).hom ≫
          Pseudofunctor.DescentData'.pullHom' D.hom (𝒰.obj i).hom
            (𝟙 ((𝒰.obj i).left)) (𝟙 ((𝒰.obj i).left)) (by simp) (by simp) ≫
          (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).symm.hom =
        𝟙 (D.obj i) := by
    apply Functor.Fiber.hom_ext
    rw [D.pullHom'_self ((𝒰.obj i).hom) (𝟙 ((𝒰.obj i).left))]
    simp [Functor.map_comp]
    have hinv :
        Functor.Fiber.fiberInclusion.map
            (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).inv =
          hc.map (𝟙 ((𝒰.obj i).left)) (D.obj i) := by
      simpa [PullbackChoice.pullbackIdIso, Functor.Fiber.fiberInclusion] using
        hc.pullbackIdComponentIso_inv_eq ((𝒰.obj i).left) (D.obj i)
    have hfac :
        Functor.Fiber.fiberInclusion.map
            (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).hom ≫
            hc.map (𝟙 ((𝒰.obj i).left)) (D.obj i) =
          Functor.Fiber.fiberInclusion.map (𝟙 (D.obj i)) := by
      simpa [Functor.Fiber.fiberInclusion] using
        hc.pullbackIdComponentIso_fac ((𝒰.obj i).left) (D.obj i)
    have hmid :
        Functor.Fiber.fiberInclusion.map
            (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).hom ≫
            Functor.Fiber.fiberInclusion.map
              (𝟙 ((hc.fiberPseudofunctor.map (𝟙 (𝒰.obj i).left).op.toLoc).toFunctor.obj (D.obj i))) ≫
            Functor.Fiber.fiberInclusion.map
              (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).inv =
          Functor.Fiber.fiberInclusion.map
            (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).hom ≫
            Functor.Fiber.fiberInclusion.map
              (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).inv := by
      have hidmap :
          Functor.Fiber.fiberInclusion.map
              (𝟙 ((hc.fiberPseudofunctor.map (𝟙 (𝒰.obj i).left).op.toLoc).toFunctor.obj (D.obj i))) ≫
            Functor.Fiber.fiberInclusion.map
              (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).inv =
          Functor.Fiber.fiberInclusion.map
            (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).inv := by
        change 𝟙 _ ≫
            Functor.Fiber.fiberInclusion.map
              (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).inv =
          Functor.Fiber.fiberInclusion.map
            (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).inv
        exact Category.id_comp _
      simpa [Category.assoc] using
        congrArg
          (fun f ↦
            Functor.Fiber.fiberInclusion.map
              (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).hom ≫ f)
          hidmap
    have hpost :
        Functor.Fiber.fiberInclusion.map
            (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).hom ≫
            Functor.Fiber.fiberInclusion.map
              (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).inv =
          Functor.Fiber.fiberInclusion.map
            (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).hom ≫
            hc.map (𝟙 ((𝒰.obj i).left)) (D.obj i) := by
      exact congrArg
        (fun f ↦
          Functor.Fiber.fiberInclusion.map
            (hc.pullbackIdComponentIso ((𝒰.obj i).left) (D.obj i)).hom ≫ f)
        hinv
    simpa using hmid.trans (hpost.trans hfac)
  simpa using congrArg Functor.Fiber.fiberInclusion.map hself

-- Proof sketch: on the overlap `Uᵢ ×[U] Uⱼ`, pull back the cocycle identity for the triple
-- `(i, j, i)` along `𝒰.delta13 i j`; the first factor becomes `D.iso i j`, the second becomes the
-- switched pullback of `φ_{ji}`, and the third factor becomes the diagonal self-comparison from
-- part `(1)`, hence the identity.
/-- Remarks 8.3.2 (2): after pulling back `φ_{ji}` along the canonical switching morphism
`Uᵢ ×[U] Uⱼ ⟶ Uⱼ ×[U] Uᵢ`, its composition with `φ_{ij}` is the identity on
`pr₀^* Xᵢ`. -/
theorem overlapComparison_comp_switchedOverlapComparison_eq_refl
    (i j : 𝒰.index) :
    D.iso i j ≪≫ D.switchedOverlapComparisonIso i j = Iso.refl _ := by
  -- Compare the two overlap isomorphisms on their underlying morphisms in the ambient category.
  apply Iso.ext
  apply Functor.Fiber.hom_ext
  -- Normalize both factors to the prime-level pullback morphisms on the pairwise overlap.
  simp only [Iso.trans_hom, D.iso_hom, switchedOverlapComparisonIso, Functor.id_obj,
    Pseudofunctor.DescentData.iso_hom, Pseudofunctor.DescentData'.descentData_hom]
  -- Pulling back the cocycle relation for `(i,j,i)` gives the desired composite formula.
  have hcomp :
      Functor.Fiber.fiberInclusion.map (D.hom i j) ≫
          Functor.Fiber.fiberInclusion.map
            (Pseudofunctor.DescentData'.pullHom' D.hom ((𝒰.pairwisePullback i j).p)
              (𝒰.pr1 i j) (𝒰.pr0 i j) (𝒰.pr1_map i j) (𝒰.pr0_map i j)) =
        Functor.Fiber.fiberInclusion.map
          (Pseudofunctor.DescentData'.pullHom' D.hom ((𝒰.pairwisePullback i j).p)
            (𝒰.pr0 i j) (𝒰.pr0 i j) (𝒰.pr0_map i j) (𝒰.pr0_map i j)) := by
    rw [← D.pullHom'_eq_hom i j]
    simpa [𝒰.pr1_map i j, Functor.map_comp] using
      congrArg Functor.Fiber.fiberInclusion.map <|
        D.comp_pullHom'
          (𝒰.pairwisePullback i j).p
          (𝒰.pr0 i j)
          (𝒰.pr1 i j)
          (𝒰.pr0 i j)
          (𝒰.pr0_map i j)
          (𝒰.pr1_map i j)
          (𝒰.pr0_map i j)
  -- The remaining self-comparison on `pr₀` is the identity.
  refine hcomp.trans ?_
  simpa using congrArg Functor.Fiber.fiberInclusion.map <|
    D.pullHom'_self ((𝒰.pairwisePullback i j).p) (𝒰.pr0 i j)

end DescentDatum

end CategoryTheory
