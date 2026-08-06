import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Lemma_2_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_2

open CategoryTheory
open scoped BasedSpace

noncomputable section

/-- A pair in the wedge locus of `X ∧ Y` is sent to a pair in the wedge locus of `X' ∧ Y'`. -/
theorem smashWedge_map
    {X X' Y Y' : BasedSpace} (f : X ⟶ X') (g : Y ⟶ Y')
    {p : smashProductPair X Y} (hp : smashWedge X Y p) :
    smashWedge X' Y' (f.right.hom p.1, g.right.hom p.2) := by
  rcases hp with hp | hp
  · left
    simp [hp, fundamentalGroupFunctorMap_basepoint]
  · right
    simp [hp, fundamentalGroupFunctorMap_basepoint]

/-- The product map induced by based maps respects the smash-product quotient relation. -/
theorem smashProductRel_map
    {X X' Y Y' : BasedSpace} (f : X ⟶ X') (g : Y ⟶ Y')
    {p q : smashProductPair X Y} (hpq : smashProductRel X Y p q) :
    smashProductRel X' Y'
      (Prod.map (f.right.hom : X.right → X'.right) (g.right.hom : Y.right → Y'.right) p)
      (Prod.map (f.right.hom : X.right → X'.right) (g.right.hom : Y.right → Y'.right) q) := by
  rcases hpq with rfl | ⟨hp, hq⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨by simpa using smashWedge_map f g hp, by simpa using smashWedge_map f g hq⟩

/-- The product map induced by based maps descends to the smash-product quotient setoid. -/
theorem smashProductSetoid_map
    {X X' Y Y' : BasedSpace} (f : X ⟶ X') (g : Y ⟶ Y') :
    ∀ a b, (smashProductSetoid X Y).r a b →
      (smashProductSetoid X' Y').r
        (Prod.map (f.right.hom : X.right → X'.right) (g.right.hom : Y.right → Y'.right) a)
        (Prod.map (f.right.hom : X.right → X'.right) (g.right.hom : Y.right → Y'.right) b)
  | _, _, hpq => smashProductRel_map f g hpq

/-- A based map in each variable induces the corresponding map of smash products. -/
def smashProductMap
    {X X' Y Y' : BasedSpace} (f : X ⟶ X') (g : Y ⟶ Y') :
    X ∧ Y ⟶ X' ∧ Y' :=
  let sourceMap : C(X.right, X'.right) := f.right.hom
  let targetMap : C(Y.right, Y'.right) := g.right.hom
  let mapProd : X.right × Y.right → X'.right × Y'.right := Prod.map sourceMap targetMap
  have mapProd_rel :
      ∀ a b, (smashProductSetoid X Y).r a b →
        (smashProductSetoid X' Y').r (mapProd a) (mapProd b) :=
    by
      simpa [mapProd, sourceMap, targetMap] using smashProductSetoid_map f g
  have hF : Continuous sourceMap := sourceMap.continuous
  have hG : Continuous targetMap := targetMap.continuous
  have mapProd_continuous : Continuous mapProd := by
    change Continuous (Prod.map sourceMap targetMap)
    exact hF.prodMap hG
  Under.homMk
    (TopCat.ofHom
      { toFun :=
          Quotient.map' mapProd mapProd_rel
        continuous_toFun := by
          simpa [smashProductType] using
            mapProd_continuous.quotient_map' mapProd_rel })
    (by
      ext x
      simp [mapProd, sourceMap, targetMap, smashProductBasepointPair, Quotient.map'_mk'',
        fundamentalGroupFunctorMap_basepoint]
    )

@[simp] theorem smashProductMap_apply_mk
    {X X' Y Y' : BasedSpace} (f : X ⟶ X') (g : Y ⟶ Y')
    (p : X.right × Y.right) :
    (smashProductMap f g).right.hom (smashProductMk X Y p) =
      smashProductMk X' Y' (f.right.hom p.1, g.right.hom p.2) := by
  change Quotient.map'
      (Prod.map (f.right.hom : X.right → X'.right) (g.right.hom : Y.right → Y'.right))
      (smashProductSetoid_map f g)
      (Quotient.mk'' p) =
    Quotient.mk''
      (Prod.map (f.right.hom : X.right → X'.right) (g.right.hom : Y.right → Y'.right) p)
  exact Quotient.map'_mk''
    (Prod.map (f.right.hom : X.right → X'.right) (g.right.hom : Y.right → Y'.right))
    (smashProductSetoid_map f g)
    p
