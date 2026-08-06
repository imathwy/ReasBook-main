import Mathlib.CategoryTheory.CommSq
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Definition_18_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.ExpandingUnion
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Lemma_19_4_2

open CategoryTheory

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` only surfaced unrelated direct-limit and homological
-- infrastructure. The shared owner `ExpandingUnion` and its basic stage API now live in
-- `Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.ExpandingUnion`; this file builds the Milnor continuity API on top of
-- that support owner and the Chapter 19 owner `InverseSequence.limOne`.

namespace ExpandingUnion

variable {X Y : TopCat.{u}}

/-- The inverse sequence `... ⟶ E^q(X_(n + 1)) ⟶ E^q(X_n) ⟶ ...` induced by restriction
along an expanding union `U`. -/
def cohomologyInverseSequence (U : ExpandingUnion X)
    (E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}) (q : ℤ) : InverseSequence where
  A n := (E q).obj (Opposite.op (U.stageSpace n))
  d n := (E q).map (U.stageStep n).op

/-- The family of restriction maps from `E^q(X)` to the stages of an expanding union. -/
def restrictionSectionsHom (U : ExpandingUnion X)
    (E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}) (q : ℤ) :
    (E q).obj (Opposite.op X) →+
      ((n : ℕ) → (E q).obj (Opposite.op (U.stageSpace n))) :=
  AddMonoidHom.mk'
    (fun x n ↦ (E q).map (U.stageInclusion n).op x)
    (by
      intro x y
      ext n
      simp)

/-- Restricting a global class to each stage yields a compatible family and hence lands in
`lim E^q(X_n)`. -/
theorem restrictionSections_mem_lim (U : ExpandingUnion X)
    (E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}) (q : ℤ) (x : (E q).obj (Opposite.op X)) :
    U.restrictionSectionsHom E q x ∈
      AddMonoidHom.ker (U.cohomologyInverseSequence E q).productDifferenceHom := sorry

/-- The canonical restriction map `E^q(X) ⟶ lim E^q(X_n)` for an expanding union `U`. -/
def restrictionToLimit (U : ExpandingUnion X)
    (E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}) (q : ℤ) :
    (E q).obj (Opposite.op X) ⟶ (U.cohomologyInverseSequence E q).lim :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun x ↦ ⟨U.restrictionSectionsHom E q x, U.restrictionSections_mem_lim E q x⟩)
      (by
        intro x y
        ext n
        change (U.restrictionSectionsHom E q (x + y)) n =
          (U.restrictionSectionsHom E q x + U.restrictionSectionsHom E q y) n
        simp [restrictionSectionsHom])

/-- The underlying map of the stagewise morphism induced by a stage-preserving map is continuous. -/
theorem stageMapContinuous (U : ExpandingUnion X) (V : ExpandingUnion Y) (f : X ⟶ Y)
    (hmap : ∀ n : ℕ, Set.MapsTo f (U.stage n) (V.stage n)) (n : ℕ) :
    Continuous fun x : U.stage n ↦ (⟨f x.1, hmap n x.2⟩ : V.stage n) := sorry

/-- A map `f : X ⟶ Y` preserving the stages of two expanding unions induces a stagewise map
`U_n ⟶ V_n`. -/
abbrev stageMap (U : ExpandingUnion X) (V : ExpandingUnion Y) (f : X ⟶ Y)
    (hmap : ∀ n : ℕ, Set.MapsTo f (U.stage n) (V.stage n)) (n : ℕ) :
    U.stageSpace n ⟶ V.stageSpace n :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨f x.1, hmap n x.2⟩,
      U.stageMapContinuous V f hmap n⟩

/-- The induced map on the stagewise products of cohomology groups. -/
def sectionsMapHom (U : ExpandingUnion X) (V : ExpandingUnion Y)
    (E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}) (q : ℤ) (f : X ⟶ Y)
    (hmap : ∀ n : ℕ, Set.MapsTo f (U.stage n) (V.stage n)) :
    ((n : ℕ) → (E q).obj (Opposite.op (V.stageSpace n))) →+
      ((n : ℕ) → (E q).obj (Opposite.op (U.stageSpace n))) :=
  AddMonoidHom.mk'
    (fun x n ↦ (E q).map (U.stageMap V f hmap n).op (x n))
    (by
      intro x y
      ext n
      simp)

/-- The stagewise map induced by `f` sends compatible families on `V` to compatible families on
`U`, hence descends to inverse limits. -/
theorem sectionsMap_mem_lim (U : ExpandingUnion X) (V : ExpandingUnion Y)
    (E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}) (q : ℤ) (f : X ⟶ Y)
    (hmap : ∀ n : ℕ, Set.MapsTo f (U.stage n) (V.stage n))
    (x : (V.cohomologyInverseSequence E q).lim) :
    U.sectionsMapHom V E q f hmap x.1 ∈
      AddMonoidHom.ker (U.cohomologyInverseSequence E q).productDifferenceHom := sorry

/-- The induced morphism `lim E^q(V_n) ⟶ lim E^q(U_n)` coming from a map
`f : X ⟶ Y` that preserves stages. -/
def limMap (U : ExpandingUnion X) (V : ExpandingUnion Y)
    (E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}) (q : ℤ) (f : X ⟶ Y)
    (hmap : ∀ n : ℕ, Set.MapsTo f (U.stage n) (V.stage n)) :
    (V.cohomologyInverseSequence E q).lim ⟶ (U.cohomologyInverseSequence E q).lim :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun x ↦ ⟨U.sectionsMapHom V E q f hmap x.1, U.sectionsMap_mem_lim V E q f hmap x⟩)
      (by
        intro x y
        ext n
        change (U.sectionsMapHom V E q f hmap (x.1 + y.1)) n =
          (U.sectionsMapHom V E q f hmap x.1 + U.sectionsMapHom V E q f hmap y.1) n
        exact
          (ConcreteCategory.hom ((E q).map (U.stageMap V f hmap n).op)).map_add (x.1 n) (y.1 n))

/-- The stagewise map induced by `f` sends the range of the product-difference map on `V` into the
corresponding range on `U`, hence descends to `lim¹`. -/
theorem sectionsMap_range_le (U : ExpandingUnion X) (V : ExpandingUnion Y)
    (E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}) (q : ℤ) (f : X ⟶ Y)
    (hmap : ∀ n : ℕ, Set.MapsTo f (U.stage n) (V.stage n)) :
    AddMonoidHom.range (V.cohomologyInverseSequence E q).productDifferenceHom ≤
      AddSubgroup.comap (U.sectionsMapHom V E q f hmap)
        (AddMonoidHom.range (U.cohomologyInverseSequence E q).productDifferenceHom) := sorry

/-- The induced morphism `lim¹ E^q(V_n) ⟶ lim¹ E^q(U_n)` coming from a map
`f : X ⟶ Y` that preserves stages. -/
def limOneMap (U : ExpandingUnion X) (V : ExpandingUnion Y)
    (E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}) (q : ℤ) (f : X ⟶ Y)
    (hmap : ∀ n : ℕ, Set.MapsTo f (U.stage n) (V.stage n)) :
    (V.cohomologyInverseSequence E q).limOne ⟶ (U.cohomologyInverseSequence E q).limOne :=
  AddCommGrpCat.ofHom <|
    QuotientAddGroup.map
      (AddMonoidHom.range (V.cohomologyInverseSequence E q).productDifferenceHom)
      (AddMonoidHom.range (U.cohomologyInverseSequence E q).productDifferenceHom)
      (U.sectionsMapHom V E q f hmap)
      (U.sectionsMap_range_le V E q f hmap)

/-- The canonical restriction morphisms `E^q(Y) ⟶ lim E^q(V_n)` and `E^q(X) ⟶ lim E^q(U_n)` are
natural with respect to stage-preserving maps `f : X ⟶ Y`. -/
theorem restrictionToLimit_natural (U : ExpandingUnion X) (V : ExpandingUnion Y)
    (E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}) (q : ℤ) (f : X ⟶ Y)
    (hmap : ∀ n : ℕ, Set.MapsTo f (U.stage n) (V.stage n)) :
    CommSq ((E q).map f.op) (V.restrictionToLimit E q)
      (U.restrictionToLimit E q) (U.limMap V E q f hmap) := by
  sorry

/-- `restrictionToLimit_natural` as an equality of composites. -/
theorem restrictionToLimit_natural_w (U : ExpandingUnion X) (V : ExpandingUnion Y)
    (E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}) (q : ℤ) (f : X ⟶ Y)
    (hmap : ∀ n : ℕ, Set.MapsTo f (U.stage n) (V.stage n)) :
    (E q).map f.op ≫ U.restrictionToLimit E q =
      V.restrictionToLimit E q ≫ U.limMap V E q f hmap :=
  (restrictionToLimit_natural U V E q f hmap).w

/-- A morphism `δ : lim¹ E^(q - 1)(X_n) ⟶ E^q(X)` exhibits the Milnor short exact sequence when
it gives a short exact sequence with the canonical restriction map. -/
def HasMilnorShortExactSequence (U : ExpandingUnion X)
    (E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}) (q : ℤ)
    (δ : (U.cohomologyInverseSequence E (q - 1)).limOne ⟶ (E q).obj (Opposite.op X)) : Prop :=
  ∃ hzero : δ ≫ U.restrictionToLimit E q = 0,
    (ShortComplex.mk δ (U.restrictionToLimit E q) hzero).ShortExact

/-- A Milnor short exact sequence has zero composite. -/
theorem HasMilnorShortExactSequence.zero
    {U : ExpandingUnion X} {E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}} {q : ℤ}
    {δ : (U.cohomologyInverseSequence E (q - 1)).limOne ⟶ (E q).obj (Opposite.op X)}
    (hδ : U.HasMilnorShortExactSequence E q δ) :
    δ ≫ U.restrictionToLimit E q = 0 :=
  hδ.choose

/-- A Milnor short exact sequence yields the short exact complex with the canonical restriction
map as its second differential. -/
theorem HasMilnorShortExactSequence.shortExact
    {U : ExpandingUnion X} {E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}} {q : ℤ}
    {δ : (U.cohomologyInverseSequence E (q - 1)).limOne ⟶ (E q).obj (Opposite.op X)}
    (hδ : U.HasMilnorShortExactSequence E q δ) :
    (ShortComplex.mk δ (U.restrictionToLimit E q) hδ.zero).ShortExact := by
  simpa [HasMilnorShortExactSequence.zero] using hδ.choose_spec

/-- A pair of connecting morphisms exhibits the Milnor short exact sequences for `U` and `V`
and is natural with respect to a stage-preserving map `f : X ⟶ Y`. -/
class NaturalMilnorShortExactSequence (U : ExpandingUnion X) (V : ExpandingUnion Y)
    (E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}) (q : ℤ) (f : X ⟶ Y)
    (hmap : ∀ n : ℕ, Set.MapsTo f (U.stage n) (V.stage n))
    (δU : (U.cohomologyInverseSequence E (q - 1)).limOne ⟶ (E q).obj (Opposite.op X))
    (δV : (V.cohomologyInverseSequence E (q - 1)).limOne ⟶ (E q).obj (Opposite.op Y)) :
    Prop where
  /-- The connecting morphism for `U` yields the Milnor short exact sequence. -/
  source_exact : U.HasMilnorShortExactSequence E q δU
  /-- The connecting morphism for `V` yields the Milnor short exact sequence. -/
  target_exact : V.HasMilnorShortExactSequence E q δV
  /-- The connecting morphisms commute with the map induced by `f`. -/
  comm :
    CommSq (U.limOneMap V E (q - 1) f hmap) δV δU ((E q).map f.op)

namespace NaturalMilnorShortExactSequence

/-- `NaturalMilnorShortExactSequence.comm` as an equality of composites. -/
theorem comm_w
    {U : ExpandingUnion X} {V : ExpandingUnion Y}
    {E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}} {q : ℤ}
    {f : X ⟶ Y} {hmap : ∀ n : ℕ, Set.MapsTo f (U.stage n) (V.stage n)}
    {δU : (U.cohomologyInverseSequence E (q - 1)).limOne ⟶ (E q).obj (Opposite.op X)}
    {δV : (V.cohomologyInverseSequence E (q - 1)).limOne ⟶ (E q).obj (Opposite.op Y)}
    (hΔ : ExpandingUnion.NaturalMilnorShortExactSequence U V E q f hmap δU δV) :
    U.limOneMap V E (q - 1) f hmap ≫ δU = δV ≫ (E q).map f.op :=
  hΔ.comm.w

end NaturalMilnorShortExactSequence

/-- A coherent family of Milnor connecting morphisms gives a Milnor short exact sequence for every
expanding union and is natural for every stage-preserving map. -/
class NaturalMilnorConnectingFamily (E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}) (q : ℤ)
    (Δ : ∀ {Z : TopCat.{u}} (W : ExpandingUnion Z),
      (W.cohomologyInverseSequence E (q - 1)).limOne ⟶ (E q).obj (Opposite.op Z)) : Prop where
  /-- Each `Δ W` yields the Milnor short exact sequence for the expanding union `W`. -/
  exact {Z : TopCat.{u}} (W : ExpandingUnion Z) : W.HasMilnorShortExactSequence E q (Δ W)
  /-- The family `Δ` is natural for stage-preserving maps. -/
  comm {Z Z' : TopCat.{u}} (W : ExpandingUnion Z) (W' : ExpandingUnion Z') (g : Z ⟶ Z')
      (hg : ∀ n : ℕ, Set.MapsTo g (W.stage n) (W'.stage n)) :
      CommSq (W.limOneMap W' E (q - 1) g hg) (Δ W') (Δ W) ((E q).map g.op)

namespace NaturalMilnorConnectingFamily

/-- `NaturalMilnorConnectingFamily.comm` as an equality of composites. -/
theorem comm_w
    {E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}} {q : ℤ}
    {Δ : ∀ {Z : TopCat.{u}} (W : ExpandingUnion Z),
      (W.cohomologyInverseSequence E (q - 1)).limOne ⟶ (E q).obj (Opposite.op Z)}
    (hΔ : ExpandingUnion.NaturalMilnorConnectingFamily E q Δ)
    {Z Z' : TopCat.{u}} (W : ExpandingUnion Z) (W' : ExpandingUnion Z') (g : Z ⟶ Z')
    (hg : ∀ n : ℕ, Set.MapsTo g (W.stage n) (W'.stage n)) :
    W.limOneMap W' E (q - 1) g hg ≫ Δ W = Δ W' ≫ (E q).map g.op :=
  (hΔ.comm W W' g hg).w

end NaturalMilnorConnectingFamily

namespace NaturalMilnorShortExactSequence

/-- A coherent family of connecting morphisms specializes to the fixed-map naturality
predicate `NaturalMilnorShortExactSequence`. -/
instance ofFamily
    {U : ExpandingUnion X} {V : ExpandingUnion Y}
    {E : ℤ → TopCat.{u}ᵒᵖ ⥤ Ab.{u}} {q : ℤ}
    {f : X ⟶ Y} {hmap : ∀ n : ℕ, Set.MapsTo f (U.stage n) (V.stage n)}
    {Δ : ∀ {Z : TopCat.{u}} (W : ExpandingUnion Z),
      (W.cohomologyInverseSequence E (q - 1)).limOne ⟶ (E q).obj (Opposite.op Z)}
    [hΔ : ExpandingUnion.NaturalMilnorConnectingFamily E q Δ] :
    ExpandingUnion.NaturalMilnorShortExactSequence U V E q f hmap (Δ U) (Δ V) where
  source_exact := hΔ.exact U
  target_exact := hΔ.exact V
  comm := hΔ.comm U V f hmap

end NaturalMilnorShortExactSequence

/-- Theorem 19.4.3 (1): if `X` is the union of an expanding sequence `U_n` and `E` is a pair
cohomology theory, then there exists a connecting morphism yielding the short exact sequence
`0 ⟶ lim¹ E^(q - 1)(U_n, ∅) ⟶ E^q(X, ∅) ⟶ lim E^q(U_n, ∅) ⟶ 0`,
with the right-hand map given by restriction to the stages; the companion theorem
`HasMilnorShortExactSequence.shortExact` recovers the short exact complex from that witness. -/
theorem milnorShortExactSequence (U : ExpandingUnion X)
    {π : Type u} [AddCommGroup π] (E : PairCohomologyTheory π) (q : ℤ) :
    ∃ δ :
        (U.cohomologyInverseSequence (PairCohomologyTheory.absoluteCohomology E) (q - 1)).limOne ⟶
          (PairCohomologyTheory.absoluteCohomology E q).obj (Opposite.op X),
      U.HasMilnorShortExactSequence (PairCohomologyTheory.absoluteCohomology E) q δ := sorry

/-- Theorem 19.4.3 (2): there exists a coherent choice of connecting morphisms for all expanding
unions, each yielding the Milnor short exact sequence of part (1), and this choice is natural for
stage-preserving maps; the companion APIs `NaturalMilnorConnectingFamily.exact`,
`NaturalMilnorConnectingFamily.comm`, and `NaturalMilnorShortExactSequence.ofFamily` recover the
fixed-union short exact sequence and the fixed-map naturality package from that family. -/
theorem milnorShortExactSequence_natural
    {π : Type u} [AddCommGroup π] (E : PairCohomologyTheory π) (q : ℤ) :
    ∃ Δ :
        ∀ {Z : TopCat.{u}} (W : ExpandingUnion Z),
          (W.cohomologyInverseSequence
            (PairCohomologyTheory.absoluteCohomology E) (q - 1)).limOne ⟶
            (PairCohomologyTheory.absoluteCohomology E q).obj (Opposite.op Z),
      ExpandingUnion.NaturalMilnorConnectingFamily
        (PairCohomologyTheory.absoluteCohomology E) q Δ := sorry

end ExpandingUnion
