import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1

open CategoryTheory Limits

noncomputable section

universe u v

/-- The product carrier underlying the smash-product quotient. -/
abbrev smashProductPair (X : BasedSpace.{u}) (Y : BasedSpace.{v}) :
    Type (max u v) :=
  X.right × Y.right

instance smashProductPairTopologicalSpace
    (X : BasedSpace.{u}) (Y : BasedSpace.{v}) :
    TopologicalSpace (smashProductPair X Y) :=
  inferInstance

-- Semantic recall: the repository already fixes `BasedSpace` as the canonical owner for based
-- spaces. The smash product is therefore introduced directly on that owner as the quotient of
-- `X.right × Y.right` collapsing the wedge locus.

/-- The wedge subset `X ∨ Y` inside `X × Y`, i.e. the pairs with at least one coordinate equal to
the chosen basepoint. -/
def smashWedge (X : BasedSpace.{u}) (Y : BasedSpace.{v}) :
    smashProductPair X Y → Prop
  | p => p.1 = underTopBasepoint X ∨ p.2 = underTopBasepoint Y

/-- Membership in `smashWedge X Y` means that one coordinate is the corresponding basepoint. -/
theorem smashWedge_iff (X : BasedSpace.{u}) (Y : BasedSpace.{v})
    (p : smashProductPair X Y) :
    smashWedge X Y p ↔ p.1 = underTopBasepoint X ∨ p.2 = underTopBasepoint Y := by
  rfl

/-- The quotient relation presenting the smash product: points are identified exactly when they
agree, or when both lie in the wedge `X ∨ Y`. -/
def smashProductRel
    (X : BasedSpace.{u}) (Y : BasedSpace.{v}) :
    smashProductPair X Y → smashProductPair X Y → Prop :=
  fun p q ↦ p = q ∨ (smashWedge X Y p ∧ smashWedge X Y q)

/-- `smashProductRel X Y` identifies equal points and collapses the wedge `X ∨ Y` to one class. -/
theorem smashProductRel_iff
    (X : BasedSpace.{u}) (Y : BasedSpace.{v})
    (p q : smashProductPair X Y) :
    smashProductRel X Y p q ↔ p = q ∨ (smashWedge X Y p ∧ smashWedge X Y q) := by
  rfl

/-- Reflexivity of `smashProductRel`. -/
theorem smashProductRel_refl
    (X : BasedSpace.{u}) (Y : BasedSpace.{v}) (p : smashProductPair X Y) :
    smashProductRel X Y p p := by
  exact Or.inl rfl

/-- Symmetry of `smashProductRel`. -/
theorem smashProductRel_symm
    (X : BasedSpace.{u}) (Y : BasedSpace.{v})
    {p q : smashProductPair X Y} (h : smashProductRel X Y p q) :
    smashProductRel X Y q p := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr ⟨h.2, h.1⟩

/-- Transitivity of `smashProductRel`. -/
theorem smashProductRel_trans
    (X : BasedSpace.{u}) (Y : BasedSpace.{v})
    {p q r : smashProductPair X Y}
    (hpq : smashProductRel X Y p q) (hqr : smashProductRel X Y q r) :
    smashProductRel X Y p r := by
  rcases hpq with rfl | ⟨hp, hq⟩
  · exact hqr
  rcases hqr with rfl | ⟨_, hr⟩
  · exact Or.inr ⟨hp, hq⟩
  · exact Or.inr ⟨hp, hr⟩

/-- The setoid presenting the quotient model of the smash product. -/
def smashProductSetoid
    (X : BasedSpace.{u}) (Y : BasedSpace.{v}) :
    Setoid (smashProductPair X Y) where
  r := smashProductRel X Y
  iseqv := ⟨
    smashProductRel_refl X Y,
    fun {_ _} ↦ smashProductRel_symm X Y,
    fun {_ _ _} ↦ smashProductRel_trans X Y⟩

/-- The quotient carrier underlying the smash product `X ∧ Y`. -/
abbrev smashProductType (X : BasedSpace.{u}) (Y : BasedSpace.{v}) :=
  Quotient (smashProductSetoid X Y)

/-- The quotient map from `X × Y` to the smash-product carrier. -/
abbrev smashProductMk
    (X : BasedSpace.{u}) (Y : BasedSpace.{v}) (p : smashProductPair X Y) :
    smashProductType X Y :=
  Quotient.mk'' p

/-- The pair of chosen basepoints of `X` and `Y`. -/
abbrev smashProductBasepointPair
    (X : BasedSpace.{u}) (Y : BasedSpace.{v}) :
    smashProductPair X Y :=
  (underTopBasepoint X, underTopBasepoint Y)

instance smashProductTypeTopologicalSpace
    (X : BasedSpace.{u}) (Y : BasedSpace.{v}) :
    TopologicalSpace (smashProductType X Y) :=
  inferInstance

/-- The distinguished pair of basepoints lies in the wedge `X ∨ Y`. -/
theorem smashWedge_basepointPair
    (X : BasedSpace.{u}) (Y : BasedSpace.{v}) :
    smashWedge X Y (smashProductBasepointPair X Y) := by
  left
  rfl

/-- The quotient map identifies any two points related by `smashProductRel X Y`. -/
theorem smashProductMk_eq_of_rel
    (X : BasedSpace.{u}) (Y : BasedSpace.{v})
    {p q : smashProductPair X Y} (hpq : smashProductRel X Y p q) :
    smashProductMk X Y p = smashProductMk X Y q :=
  Quotient.sound hpq

/-- Definition 8.1.2: the based smash product `X ∧ Y` is the quotient of `X × Y` obtained by
collapsing the wedge `X ∨ Y`, where `X ∨ Y` consists of the pairs with at least one coordinate
equal to the corresponding basepoint. -/
abbrev smashProduct
    (X : BasedSpace.{u}) (Y : BasedSpace.{v}) :
    BasedSpace.{max u v} :=
  Under.mk
    (show (⊤_ TopCat.{max u v}) ⟶ TopCat.of (smashProductType X Y) from
      TopCat.terminalIsoPUnit.hom ≫
        TopCat.ofHom
          (ContinuousMap.const PUnit
            (smashProductMk X Y (smashProductBasepointPair X Y))))

scoped[BasedSpace] infixr:70 " ∧ " => smashProduct

open scoped BasedSpace

/-- The chosen basepoint of `X ∧ Y` is the class of
`(underTopBasepoint X, underTopBasepoint Y)`. -/
@[simp] theorem underTopBasepoint_smashProduct
    (X : BasedSpace.{u}) (Y : BasedSpace.{v}) :
    underTopBasepoint (X ∧ Y) =
      smashProductMk X Y (smashProductBasepointPair X Y) := by
  rfl

/-- Any point of the wedge `X ∨ Y` represents the basepoint of `X ∧ Y`. -/
theorem smashProduct_mk_eq_basepoint_of_mem_smashWedge
    (X : BasedSpace.{u}) (Y : BasedSpace.{v})
    {p : smashProductPair X Y} (hp : smashWedge X Y p) :
    smashProductMk X Y p =
      underTopBasepoint (X ∧ Y) := by
  calc
    smashProductMk X Y p = smashProductMk X Y (smashProductBasepointPair X Y) :=
      smashProductMk_eq_of_rel X Y (Or.inr ⟨hp, smashWedge_basepointPair X Y⟩)
    _ = underTopBasepoint (X ∧ Y) := by
      exact (underTopBasepoint_smashProduct X Y).symm
