import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Lemma_2_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_2

open CategoryTheory Limits

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch`: no verified existing owner for this `Y₊`-smash
-- identification was surfaced in the current project. This chapter uses based spaces as
-- `Under (⊤_ TopCat)`, `Definition_8_1_2` already introduces the canonical smash-product owner
-- `smashProduct`, and this file records the source-facing strip-collapse relation on `X.right × Y`
-- together with the based-space quotient model used to realize the collapsed basepoint.

/-- Definition 8.3.5 (1): for an unbased space `Y`, `adjoinBasepoint Y` is `Y₊`, namely `Y` with
a disjoint basepoint adjoined. -/
abbrev adjoinBasepoint (Y : TopCat) : BasedSpace :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit (Sum.inl PUnit.unit : PUnit ⊕ Y)))

/- Source notation for adjoining a disjoint basepoint to an unbased space. -/
notation:max Y "₊" => adjoinBasepoint Y

/-- The structure map of `Y₊` picks out the adjoined summand. -/
theorem adjoinBasepoint_hom (Y : TopCat) :
    (Y₊).hom =
      TopCat.terminalIsoPUnit.hom ≫
        TopCat.ofHom (ContinuousMap.const PUnit (Sum.inl PUnit.unit : PUnit ⊕ Y)) := by
  rfl

/-- The chosen basepoint of `Y₊` is the adjoined summand. -/
@[simp] theorem underTopBasepoint_adjoinBasepoint (Y : TopCat) :
    underTopBasepoint Y₊ = Sum.inl PUnit.unit := by
  rfl

/-- The strip `{underTopBasepoint X} × Y` collapsed in the source-facing quotient description of
`X ∧ Y₊`. -/
def smashProductAdjoinBasepointStrip
    (X : BasedSpace) (Y : TopCat) :
    X.right × Y → Prop
  | p => p.1 = underTopBasepoint X

/-- The quotient relation on `X.right × Y` identifying equal points and collapsing the strip
`{underTopBasepoint X} × Y` to one class. -/
def smashProductAdjoinBasepointRel
    (X : BasedSpace) (Y : TopCat) :
    (X.right × Y) → (X.right × Y) → Prop :=
  fun p q ↦ p = q ∨
    (smashProductAdjoinBasepointStrip X Y p ∧ smashProductAdjoinBasepointStrip X Y q)

/-- `smashProductAdjoinBasepointRel X Y` identifies equal points and collapses the strip
`{underTopBasepoint X} × Y` to one class. -/
theorem smashProductAdjoinBasepointRel_iff
    (X : BasedSpace) (Y : TopCat) (p q : X.right × Y) :
    smashProductAdjoinBasepointRel X Y p q ↔
      p = q ∨
        (smashProductAdjoinBasepointStrip X Y p ∧ smashProductAdjoinBasepointStrip X Y q) := by
  rfl

/-- Reflexivity of `smashProductAdjoinBasepointRel`. -/
theorem smashProductAdjoinBasepointRel_refl
    (X : BasedSpace) (Y : TopCat) (p : X.right × Y) :
    smashProductAdjoinBasepointRel X Y p p := by
  exact Or.inl rfl

/-- Symmetry of `smashProductAdjoinBasepointRel`. -/
theorem smashProductAdjoinBasepointRel_symm
    (X : BasedSpace) (Y : TopCat) {p q : X.right × Y}
    (h : smashProductAdjoinBasepointRel X Y p q) :
    smashProductAdjoinBasepointRel X Y q p := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr ⟨h.2, h.1⟩

/-- Transitivity of `smashProductAdjoinBasepointRel`. -/
theorem smashProductAdjoinBasepointRel_trans
    (X : BasedSpace) (Y : TopCat) {p q r : X.right × Y}
    (hpq : smashProductAdjoinBasepointRel X Y p q)
    (hqr : smashProductAdjoinBasepointRel X Y q r) :
    smashProductAdjoinBasepointRel X Y p r := by
  rcases hpq with rfl | ⟨hp, hq⟩
  · exact hqr
  rcases hqr with rfl | ⟨_, hr⟩
  · exact Or.inr ⟨hp, hq⟩
  · exact Or.inr ⟨hp, hr⟩

/-- The source-facing quotient setoid on `X.right × Y` collapsing
`{underTopBasepoint X} × Y`. -/
def smashProductAdjoinBasepointSetoid
    (X : BasedSpace) (Y : TopCat) :
    Setoid (X.right × Y) where
  r := smashProductAdjoinBasepointRel X Y
  iseqv := ⟨
    smashProductAdjoinBasepointRel_refl X Y,
    fun {_ _} ↦ smashProductAdjoinBasepointRel_symm X Y,
    fun {_ _ _} ↦ smashProductAdjoinBasepointRel_trans X Y⟩

/-- The quotient map from `X.right × Y` to the source-facing strip-collapse quotient carrier. -/
abbrev smashProductAdjoinBasepointMk
    (X : BasedSpace) (Y : TopCat) (p : X.right × Y) :
    Quotient (smashProductAdjoinBasepointSetoid X Y) :=
  Quotient.mk'' p

/-- The subset collapsed to the basepoint in the quotient model for `X ∧ Y₊`. -/
private def smashWithAdjoinedBasepointBasepointLocus
    (X : BasedSpace) (Y : TopCat) :
    PUnit ⊕ (X.right × Y) → Prop
  | Sum.inl _ => True
  | Sum.inr p => p.1 = underTopBasepoint X

/-- The equivalence relation identifying the adjoined basepoint with the strip
`{underTopBasepoint X} × Y`. -/
private def smashWithAdjoinedBasepointRel
    (X : BasedSpace) (Y : TopCat) :
    PUnit ⊕ (X.right × Y) → PUnit ⊕ (X.right × Y) → Prop :=
  fun a b ↦ a = b ∨
    (smashWithAdjoinedBasepointBasepointLocus X Y a ∧
      smashWithAdjoinedBasepointBasepointLocus X Y b)

/-- On the `X.right × Y` summand, the auxiliary relation agrees with the source-facing quotient
relation collapsing `{underTopBasepoint X} × Y`. -/
private theorem smashWithAdjoinedBasepointRel_inr_iff
    (X : BasedSpace) (Y : TopCat) (p q : X.right × Y) :
    smashWithAdjoinedBasepointRel X Y (Sum.inr p) (Sum.inr q) ↔
      smashProductAdjoinBasepointRel X Y p q := by
  simp [smashWithAdjoinedBasepointRel, smashProductAdjoinBasepointRel,
    smashWithAdjoinedBasepointBasepointLocus, smashProductAdjoinBasepointStrip]

/-- Reflexivity of `smashWithAdjoinedBasepointRel`. -/
private theorem smashWithAdjoinedBasepointRel_refl
    (X : BasedSpace) (Y : TopCat) (p : PUnit ⊕ (X.right × Y)) :
    smashWithAdjoinedBasepointRel X Y p p := by
  exact Or.inl rfl

/-- Symmetry of `smashWithAdjoinedBasepointRel`. -/
private theorem smashWithAdjoinedBasepointRel_symm
    (X : BasedSpace) (Y : TopCat) {p q : PUnit ⊕ (X.right × Y)}
    (h : smashWithAdjoinedBasepointRel X Y p q) :
    smashWithAdjoinedBasepointRel X Y q p := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr ⟨h.2, h.1⟩

/-- Transitivity of `smashWithAdjoinedBasepointRel`. -/
private theorem smashWithAdjoinedBasepointRel_trans
    (X : BasedSpace) (Y : TopCat) {p q r : PUnit ⊕ (X.right × Y)}
    (hpq : smashWithAdjoinedBasepointRel X Y p q)
    (hqr : smashWithAdjoinedBasepointRel X Y q r) :
    smashWithAdjoinedBasepointRel X Y p r := by
  rcases hpq with rfl | ⟨hp, hq⟩
  · exact hqr
  rcases hqr with rfl | ⟨_, hr⟩
  · exact Or.inr ⟨hp, hq⟩
  · exact Or.inr ⟨hp, hr⟩

/-- The setoid presenting the quotient model for `X ∧ Y₊`. -/
private def smashWithAdjoinedBasepointSetoid
    (X : BasedSpace) (Y : TopCat) :
    Setoid (PUnit ⊕ (X.right × Y)) where
  r := smashWithAdjoinedBasepointRel X Y
  iseqv := ⟨
    smashWithAdjoinedBasepointRel_refl X Y,
    fun {_ _} h ↦ smashWithAdjoinedBasepointRel_symm X Y h,
    fun {_ _ _} hpq hqr ↦ smashWithAdjoinedBasepointRel_trans X Y hpq hqr⟩

/-- The quotient class of the adjoined basepoint in the model for `X ∧ Y₊`. -/
private def smashWithAdjoinedBasepointBasepoint
    (X : BasedSpace) (Y : TopCat) :
    Quotient (smashWithAdjoinedBasepointSetoid X Y) :=
  Quotient.mk'' (Sum.inl PUnit.unit : PUnit ⊕ (X.right × Y))

/-- The quotient model of `X ∧ Y₊`, obtained from `X × Y` with an adjoined basepoint by
collapsing `{underTopBasepoint X} × Y` to that basepoint. -/
abbrev smashWithAdjoinedBasepoint
    (X : BasedSpace) (Y : TopCat) : BasedSpace :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom
        (ContinuousMap.const PUnit
          (smashWithAdjoinedBasepointBasepoint X Y)))

/-- The quotient map from `PUnit ⊕ (X.right × Y)` to the carrier of
`smashWithAdjoinedBasepoint X Y`. -/
abbrev smashWithAdjoinedBasepointMk
    (X : BasedSpace) (Y : TopCat) (p : PUnit ⊕ (X.right × Y)) :
    (smashWithAdjoinedBasepoint X Y).right :=
  Quotient.mk'' p

/-- The chosen basepoint of `smashWithAdjoinedBasepoint X Y` is the class of the adjoined
basepoint. -/
@[simp] theorem underTopBasepoint_smashWithAdjoinedBasepoint
    (X : BasedSpace) (Y : TopCat) :
    underTopBasepoint (smashWithAdjoinedBasepoint X Y) =
      smashWithAdjoinedBasepointMk X Y (Sum.inl PUnit.unit) := by
  rfl

/-- In `smashWithAdjoinedBasepoint X Y`, every point of the strip
`{underTopBasepoint X} × Y` is identified with the distinguished basepoint class. -/
theorem smashWithAdjoinedBasepoint_mk_eq_basepoint_of_mem_strip
    (X : BasedSpace) (Y : TopCat) {p : X.right × Y}
    (hp : smashProductAdjoinBasepointStrip X Y p) :
    Quotient.mk'' (Sum.inr p : PUnit ⊕ (X.right × Y)) =
      underTopBasepoint (smashWithAdjoinedBasepoint X Y) := by
  calc
    Quotient.mk'' (Sum.inr p : PUnit ⊕ (X.right × Y)) =
        Quotient.mk'' (Sum.inl PUnit.unit : PUnit ⊕ (X.right × Y)) :=
      Quotient.sound <| Or.inr ⟨hp, trivial⟩
    _ = underTopBasepoint (smashWithAdjoinedBasepoint X Y) := by
      exact (underTopBasepoint_smashWithAdjoinedBasepoint X Y).symm

/-- The quotient map from `X × Y₊` to the quotient model collapsing the adjoined basepoint
summand and the strip `{underTopBasepoint X} × Y`. -/
private def smashProductAdjoinBasepointToModelRaw
    (X : BasedSpace) (Y : TopCat) :
    X.right × (Y₊).right → PUnit ⊕ (X.right × Y)
  | (_, Sum.inl _) => Sum.inl PUnit.unit
  | (x, Sum.inr y) => Sum.inr (x, y)

/-- The quotient model map respects the smash-product relation on `X × Y₊`. -/
private theorem smashProductAdjoinBasepointToModelRaw_mem_basepointLocus
    (X : BasedSpace) (Y : TopCat) {p : X.right × (Y₊).right}
    (hp : smashWedge X Y₊ p) :
    smashWithAdjoinedBasepointBasepointLocus X Y
      (smashProductAdjoinBasepointToModelRaw X Y p) := by
  rcases p with ⟨x, y⟩
  rcases y with _ | y
  · trivial
  · simpa [smashWedge, smashWithAdjoinedBasepointBasepointLocus,
      smashProductAdjoinBasepointToModelRaw, underTopBasepoint_adjoinBasepoint] using hp

/-- The quotient model map respects the smash-product relation on `X × Y₊`. -/
private theorem smashProductAdjoinBasepointToModelRaw_respects
    (X : BasedSpace) (Y : TopCat) :
    ∀ ⦃p q : X.right × (Y₊).right⦄,
      smashProductRel X Y₊ p q →
        smashWithAdjoinedBasepointRel X Y
          (smashProductAdjoinBasepointToModelRaw X Y p)
          (smashProductAdjoinBasepointToModelRaw X Y q) := by
  intro p q hpq
  rcases hpq with rfl | ⟨hp, hq⟩
  · exact Or.inl rfl
  · exact Or.inr
      ⟨smashProductAdjoinBasepointToModelRaw_mem_basepointLocus X Y hp,
        smashProductAdjoinBasepointToModelRaw_mem_basepointLocus X Y hq⟩

/-- A representative in the quotient model determines a representative in `X ∧ Y₊`. -/
private def smashWithAdjoinedBasepointToSmashProductRaw
    (X : BasedSpace) (Y : TopCat) :
    PUnit ⊕ (X.right × Y) → X.right × (Y₊).right
  | Sum.inl _ => (underTopBasepoint X, Sum.inl PUnit.unit)
  | Sum.inr p => (p.1, Sum.inr p.2)

/-- The map back to `X ∧ Y₊` respects the quotient-model relation. -/
private theorem smashWithAdjoinedBasepointToSmashProductRaw_mem_smashWedge
    (X : BasedSpace) (Y : TopCat) {p : PUnit ⊕ (X.right × Y)}
    (hp : smashWithAdjoinedBasepointBasepointLocus X Y p) :
    smashWedge X Y₊ (smashWithAdjoinedBasepointToSmashProductRaw X Y p) := by
  rcases p with _ | p
  · simp [smashWedge,
      smashWithAdjoinedBasepointToSmashProductRaw, underTopBasepoint_adjoinBasepoint]
  · simpa [smashWedge, smashWithAdjoinedBasepointBasepointLocus,
      smashWithAdjoinedBasepointToSmashProductRaw, underTopBasepoint_adjoinBasepoint] using hp

/-- The map back to `X ∧ Y₊` respects the quotient-model relation. -/
private theorem smashWithAdjoinedBasepointToSmashProductRaw_respects
    (X : BasedSpace) (Y : TopCat) :
    ∀ ⦃p q : PUnit ⊕ (X.right × Y)⦄,
      smashWithAdjoinedBasepointRel X Y p q →
        smashProductRel X Y₊
          (smashWithAdjoinedBasepointToSmashProductRaw X Y p)
          (smashWithAdjoinedBasepointToSmashProductRaw X Y q) := by
  intro p q hpq
  rcases hpq with rfl | ⟨hp, hq⟩
  · exact Or.inl rfl
  · exact Or.inr
      ⟨smashWithAdjoinedBasepointToSmashProductRaw_mem_smashWedge X Y hp,
        smashWithAdjoinedBasepointToSmashProductRaw_mem_smashWedge X Y hq⟩

/-- Helper for Definition 8.3.5: on raw representatives of `X × Y₊`, the forward map to the
auxiliary quotient model and the raw map back to `X ∧ Y₊` land in the same smash-product class. -/
private theorem smashProductAdjoinBasepointSourceRoundTripRel
    (X : BasedSpace) (Y : TopCat) (p : X.right × (Y₊).right) :
    smashProductRel X Y₊ p
      (smashWithAdjoinedBasepointToSmashProductRaw X Y
        (smashProductAdjoinBasepointToModelRaw X Y p)) := by
  rcases p with ⟨x, y⟩
  rcases y with _ | y
  · -- Both representatives lie in the smash wedge because the `Y₊`-coordinate is the basepoint.
    exact Or.inr <| by
      constructor <;>
        simp [smashWedge, smashWithAdjoinedBasepointToSmashProductRaw,
          smashProductAdjoinBasepointToModelRaw, underTopBasepoint_adjoinBasepoint]
  · -- Away from the adjoined basepoint, the raw roundtrip is literally the identity.
    exact Or.inl rfl

/-- Helper for Definition 8.3.5: on the auxiliary quotient-model carrier, the raw map to
`X ∧ Y₊` and back is definitionally the identity. -/
private theorem smashProductAdjoinBasepointModelRoundTrip
    (X : BasedSpace) (Y : TopCat) (q : PUnit ⊕ (X.right × Y)) :
    smashProductAdjoinBasepointToModelRaw X Y
      (smashWithAdjoinedBasepointToSmashProductRaw X Y q) = q := by
  -- Each sum branch reduces directly to the original representative.
  rcases q with _ | q <;> rfl

/-- Helper for Definition 8.3.5: the raw map from `X × Y₊` to the auxiliary quotient model is
continuous before descending to the quotient. -/
private theorem smashProductAdjoinBasepointToModelRawContinuous
    (X : BasedSpace) (Y : TopCat) :
    Continuous (smashProductAdjoinBasepointToModelRaw X Y) := by
  let collapseLeft : (X.right × PUnit) ⊕ (X.right × Y) → PUnit ⊕ (X.right × Y) :=
    Sum.elim (fun _ ↦ Sum.inl PUnit.unit) Sum.inr
  have hcollapse : Continuous collapseLeft := by
    -- The left summand collapses to the adjoined basepoint, while the right summand is included.
    exact Continuous.sumElim continuous_const continuous_inr
  have hfactor :
      smashProductAdjoinBasepointToModelRaw X Y =
        fun p : X.right × (Y₊).right ↦
          collapseLeft ((Homeomorph.prodSumDistrib (X := X.right) (Y := PUnit) (Z := Y)) p) := by
    -- The product-with-sum distributivity homeomorphism exposes the two defining branches.
    funext p
    rcases p with ⟨x, y⟩
    rcases y with _ | y <;> rfl
  rw [hfactor]
  exact hcollapse.comp
    (Homeomorph.prodSumDistrib (X := X.right) (Y := PUnit) (Z := Y)).continuous_toFun

/-- Helper for Definition 8.3.5: the raw map from the auxiliary quotient model back to `X ∧ Y₊`
is continuous before descending to the quotient. -/
private theorem smashWithAdjoinedBasepointToSmashProductRawContinuous
    (X : BasedSpace) (Y : TopCat) :
    Continuous (smashWithAdjoinedBasepointToSmashProductRaw X Y) := by
  let leftBranch : PUnit → X.right × (Y₊).right :=
    fun _ ↦ (underTopBasepoint X, Sum.inl PUnit.unit)
  let rightBranch : X.right × Y → X.right × (Y₊).right :=
    fun p ↦ (p.1, Sum.inr p.2)
  have hleft : Continuous leftBranch := by
    -- The adjoined-basepoint summand is sent to a constant representative.
    exact continuous_const
  have hright : Continuous rightBranch := by
    -- The visible summand keeps the `X`-coordinate and inserts `Y` into `Y₊`.
    change Continuous
      (fun p : X.right × Y ↦
        ((p.1, (Sum.inr p.2 : (Y₊).right)) : X.right × (Y₊).right))
    continuity
  have hfactor :
      smashWithAdjoinedBasepointToSmashProductRaw X Y = Sum.elim leftBranch rightBranch := by
    -- The raw inverse map is exactly the sum-eliminator built from the two branches above.
    funext q
    rcases q with _ | q <;> rfl
  rw [hfactor]
  -- Assemble the two continuous branches over the sum carrier.
  exact Continuous.sumElim hleft hright

/-- The underlying homeomorphism of based spaces identifying `X ∧ Y₊` with the auxiliary quotient
model that collapses `{underTopBasepoint X} × Y` to the distinguished class. -/
noncomputable def smashProductAdjoinBasepointHomeomorph
    (X : BasedSpace) (Y : TopCat) :
    (smashProduct X Y₊).right ≃ₜ (smashWithAdjoinedBasepoint X Y).right where
  toEquiv :=
    { toFun :=
        Quotient.map'
          (smashProductAdjoinBasepointToModelRaw X Y)
          (smashProductAdjoinBasepointToModelRaw_respects X Y)
      invFun :=
        Quotient.map'
          (smashWithAdjoinedBasepointToSmashProductRaw X Y)
          (smashWithAdjoinedBasepointToSmashProductRaw_respects X Y)
      left_inv := by
        intro z
        -- Reduce the quotient inverse law to a relation between raw representatives.
        refine Quotient.inductionOn' z ?_
        intro p
        simp_rw [Quotient.map'_mk'']
        exact Quotient.sound <|
          smashProductRel_symm X Y₊
            (smashProductAdjoinBasepointSourceRoundTripRel X Y p)
      right_inv := by
        intro z
        -- On the quotient-model side, the raw roundtrip is literally the identity.
        refine Quotient.inductionOn' z ?_
        intro q
        simp_rw [Quotient.map'_mk'']
        exact congrArg Quotient.mk'' (smashProductAdjoinBasepointModelRoundTrip X Y q) }
  continuous_toFun := by
    -- Descend the raw continuous map through the smash-product quotient.
    have hrel :
        ∀ a b, (smashProductSetoid X Y₊).r a b →
          (smashWithAdjoinedBasepointSetoid X Y).r
            (smashProductAdjoinBasepointToModelRaw X Y a)
            (smashProductAdjoinBasepointToModelRaw X Y b) := by
      intro a b h
      exact smashProductAdjoinBasepointToModelRaw_respects X Y h
    simpa using
      (smashProductAdjoinBasepointToModelRawContinuous X Y).quotient_map'
        hrel
  continuous_invFun := by
    -- Descend the raw inverse map through the quotient-model quotient.
    have hrel :
        ∀ a b, (smashWithAdjoinedBasepointSetoid X Y).r a b →
          (smashProductSetoid X Y₊).r
            (smashWithAdjoinedBasepointToSmashProductRaw X Y a)
            (smashWithAdjoinedBasepointToSmashProductRaw X Y b) := by
      intro a b h
      exact smashWithAdjoinedBasepointToSmashProductRaw_respects X Y h
    simpa using
      (smashWithAdjoinedBasepointToSmashProductRawContinuous X Y).quotient_map'
        hrel

/- The auxiliary `PUnit ⊕ (X.right × Y)` carrier is only an implementation of the quotient model;
the public statement is the `Under (⊤_ TopCat)`-isomorphism below. -/

/-- The homeomorphism `smashProductAdjoinBasepointHomeomorph` sends a quotient class in
`smashProduct X Y₊` represented by `(x, y)` to the corresponding quotient class in the
adjoined-basepoint model. -/
@[simp] theorem smashProductAdjoinBasepointHomeomorph_apply_mk
    (X : BasedSpace) (Y : TopCat) (x : X.right) (y : Y) :
    smashProductAdjoinBasepointHomeomorph X Y
        (smashProductMk X Y₊ (x, Sum.inr y)) =
      smashWithAdjoinedBasepointMk X Y (Sum.inr (x, y)) := by
  rfl

/-- The homeomorphism `smashProductAdjoinBasepointHomeomorph` sends any representative with the
adjoined basepoint in the `Y₊` coordinate to the distinguished class in the quotient model. -/
@[simp] theorem smashProductAdjoinBasepointHomeomorph_apply_mk_basepoint
    (X : BasedSpace) (Y : TopCat) (x : X.right) :
    smashProductAdjoinBasepointHomeomorph X Y
        (smashProductMk X Y₊ (x, Sum.inl PUnit.unit)) =
      underTopBasepoint (smashWithAdjoinedBasepoint X Y) := by
  rw [underTopBasepoint_smashWithAdjoinedBasepoint]
  rfl

/-- The identification `smashProductAdjoinBasepointHomeomorph` preserves the distinguished
basepoint. -/
@[simp] theorem smashProductAdjoinBasepointHomeomorph_basepoint
    (X : BasedSpace) (Y : TopCat) :
    smashProductAdjoinBasepointHomeomorph X Y
        (underTopBasepoint (smashProduct X Y₊)) =
      underTopBasepoint (smashWithAdjoinedBasepoint X Y) := by
  simpa [underTopBasepoint_smashProduct, smashProductBasepointPair,
    underTopBasepoint_adjoinBasepoint] using
      smashProductAdjoinBasepointHomeomorph_apply_mk_basepoint X Y (underTopBasepoint X)

/-- The underlying topological isomorphism of the based-space identification preserves the
structure maps from `⊤_ TopCat`. -/
theorem smashProductAdjoinBasepointIso_w
    (X : BasedSpace) (Y : TopCat) :
    (smashProduct X Y₊).hom ≫
        (TopCat.isoOfHomeo (smashProductAdjoinBasepointHomeomorph X Y)).hom =
      (smashWithAdjoinedBasepoint X Y).hom := by
  -- Both structure maps from `⊤_ TopCat` are constant at the distinguished basepoint classes.
  ext x
  simpa using smashProductAdjoinBasepointHomeomorph_basepoint X Y

/-- Definition 8.3.5 (2): the based space `smashProduct X Y₊`, representing
`X ∧ Y₊`, is canonically identified with a based quotient model whose public relation on
`X.right × Y` is `smashProductAdjoinBasepointRel X Y`, collapsing `{underTopBasepoint X} × Y` to
the distinguished basepoint class. -/
noncomputable def smashProductAdjoinBasepointIso
    (X : BasedSpace) (Y : TopCat) :
    smashProduct X Y₊ ≅ smashWithAdjoinedBasepoint X Y :=
  Under.isoMk
    (TopCat.isoOfHomeo (smashProductAdjoinBasepointHomeomorph X Y))
    (smashProductAdjoinBasepointIso_w X Y)

/-- The forward morphism of `smashProductAdjoinBasepointIso` is induced by
`smashProductAdjoinBasepointHomeomorph`. -/
theorem smashProductAdjoinBasepointIso_hom_right
    (X : BasedSpace) (Y : TopCat) :
    (smashProductAdjoinBasepointIso X Y).hom.right =
      (TopCat.isoOfHomeo (smashProductAdjoinBasepointHomeomorph X Y)).hom := by
  rfl
