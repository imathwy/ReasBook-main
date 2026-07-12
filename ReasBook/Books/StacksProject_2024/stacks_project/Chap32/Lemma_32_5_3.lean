import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced mathlib's affine-transition limit API,
-- especially `AlgebraicGeometry.opensCone`; local Chapter 32 precedent represents Stacks
-- inverse systems as `OrderDual I ⥤ Scheme` or, for absolute finite-type data, as diagrams in
-- `Over (Spec (CommRingCat.of ℤ))`.

/-- A structured witness for the approximation of `S` by absolute finite type stages, together
with the open subschemes matching a prescribed compact open inverse limit. -/
structure CompactOpenAbsoluteNoetherianApproximation
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : Scheme) [CompactSpace S] [QuasiSeparatedSpace S]
    (V : S.Opens)
    (D : OrderDual I ⥤ Over (Spec (CommRingCat.of ℤ)))
    (cV : Cone (D ⋙ Over.forget (Spec (CommRingCat.of ℤ))))
    (eV : V.toScheme ≅ cV.pt) where
  J : Type
  [preorderJ : Preorder J]
  [nonemptyJ : Nonempty J]
  [directedJ : IsDirected J (· ≤ ·)]
  E : OrderDual J ⥤ Over (Spec (CommRingCat.of ℤ))
  cS : Cone (E ⋙ Over.forget (Spec (CommRingCat.of ℤ)))
  eS : S ≅ cS.pt
  isLimitS : IsLimit cS
  indexMap : J → I
  monotoneIndexMap : Monotone indexMap
  transitionAffine :
    ∀ ⦃j j' : J⦄ (hjj' : j ≤ j'), IsAffineHom (E.map (homOfLE hjj')).left
  stageFinite : ∀ j : J, QuasiCompact (E.obj j).hom ∧ LocallyOfFiniteType (E.obj j).hom
  V' : ∀ j : J, ((E.obj j).left).Opens
  stageIso : ∀ j : J, (V' j).toScheme ≅ (D.obj (indexMap j)).left
  toV' : ∀ j : J, V.toScheme ⟶ (V' j).toScheme
  Vtransition : ∀ {j j' : J}, (hjj' : j ≤ j') → (V' j').toScheme ⟶ (V' j).toScheme
  openLimit :
    ∀ j : J, IsLimit (opensCone (E ⋙ Over.forget (Spec (CommRingCat.of ℤ))) cS j (V' j))
  openPullback :
    ∀ j : J, (Opens.map ((eS.hom ≫ cS.π.app j).base)).obj (V' j) = V
  transitionPullback :
    ∀ ⦃j j' : J⦄ (hjj' : j ≤ j'),
      (Opens.map ((E.map (homOfLE hjj')).left).base).obj (V' j) = V' j'
  toOpen :
    ∀ j : J, toV' j ≫ (V' j).ι = V.ι ≫ eS.hom ≫ cS.π.app j
  toStage :
    ∀ j : J, toV' j ≫ (stageIso j).hom = eV.hom ≫ cV.π.app (indexMap j)
  transitionOpen :
    ∀ ⦃j j' : J⦄ (hjj' : j ≤ j'),
      Vtransition hjj' ≫ (V' j).ι = (V' j').ι ≫ (E.map (homOfLE hjj')).left
  transitionStage :
    ∀ ⦃j j' : J⦄ (hjj' : j ≤ j'),
      Vtransition hjj' ≫ (stageIso j).hom =
        (stageIso j').hom ≫ (D.map (homOfLE (monotoneIndexMap hjj'))).left

/-- Lemma 32.5.3: a quasi-compact quasi-separated scheme containing a quasi-compact open which
is an absolute Noetherian inverse limit admits a compatible absolute Noetherian approximation. -/
@[stacks 07RN]
theorem exists_absoluteNoetherianApproximation_of_compactOpen_inverseLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : Scheme) [CompactSpace S] [QuasiSeparatedSpace S]
    (V : S.Opens) (hV : IsCompact (V : Set S))
    (D : OrderDual I ⥤ Over (Spec (CommRingCat.of ℤ)))
    (cV : Cone (D ⋙ Over.forget (Spec (CommRingCat.of ℤ)))) (hcV : IsLimit cV)
    (eV : V.toScheme ≅ cV.pt)
    (hDaffine :
      ∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii')).left)
    (hDfinite :
      ∀ i : I, QuasiCompact (D.obj i).hom ∧ LocallyOfFiniteType (D.obj i).hom) :
    Nonempty (CompactOpenAbsoluteNoetherianApproximation S V D cV eV) := sorry

end AlgebraicGeometry
