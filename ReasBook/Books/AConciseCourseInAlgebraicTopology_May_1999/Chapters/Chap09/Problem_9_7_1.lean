import Mathlib.Algebra.Exact
import Mathlib.CategoryTheory.WithTerminal.Cone
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Lemma_2_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Theorem_9_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped TopCat Topology Topology.Homotopy unitInterval

noncomputable section

universe u

-- Semantic recall via `lean_leansearch`: no current mathlib owner for relative homotopy groups was
-- found in this environment, but local Chapter 9 precedent provides `relativeHomotopyGroup` for
-- pair-relative groups, while Chapter 2 already treats wedges of based spaces as coproducts in
-- `Under (⊤_ TopCat)`. The source-facing wedge owner therefore reuses the canonical coproduct
-- surface.

/-- The binary wedge `X ∨ Y`, realized as the coproduct of the two based spaces in
`Under (⊤_ TopCat)`. -/
abbrev binaryWedge (X Y : BasedSpace) : BasedSpace :=
  ∐ fun b : Bool ↦ cond b X Y

/-- Expanding `binaryWedge X Y` recovers the canonical coproduct presentation of the wedge. -/
@[simp] theorem binaryWedge_eq_coprod (X Y : BasedSpace) :
    binaryWedge X Y = ∐ fun b : Bool ↦ cond b X Y :=
  rfl

/-- The based homotopy group of a based space, obtained from the canonical `π_` owner by using the
chosen basepoint of `X`. -/
abbrev basedHomotopyGroup (n : ℕ) (X : BasedSpace) :=
  π_ n X.right (underTopBasepoint X)

/-- Expanding `basedHomotopyGroup n X` recovers the underlying-pointed `π_` owner. -/
@[simp] theorem basedHomotopyGroup_eq_pi (n : ℕ) (X : BasedSpace) :
    basedHomotopyGroup n X = π_ n X.right (underTopBasepoint X) :=
  rfl

/-- The distinguished basepoint of the pair `(X.right × Y.right, smashWedge X Y)`. -/
abbrev smashWedgeRelativeBasepoint
    (X Y : BasedSpace) :
    {p : smashProductPair X Y // smashWedge X Y p} :=
  ⟨smashProductBasepointPair X Y, smashWedge_basepointPair X Y⟩

/-- The relative homotopy group `π_(n+1)(X × Y, smashWedge X Y)` based at the wedge basepoint,
formalized through the Chapter 9 owner `relativeHomotopyGroup` for pair-relative homotopy
groups. -/
abbrev smashWedgeRelativeHomotopyGroup
    (n : ℕ) (X Y : BasedSpace) :=
  relativeHomotopyGroup n.succPNat
    ({p : smashProductPair X Y | smashWedge X Y p} : Set (smashProductPair X Y))
    (smashWedgeRelativeBasepoint X Y)

/-- The shifted relative term over the canonical wedge subset carries its inherited group
structure in positive degree. -/
noncomputable instance smashWedgeRelativeHomotopyGroupGroup
    (n : ℕ) (X Y : BasedSpace) :
    Group (smashWedgeRelativeHomotopyGroup (n + 1) X Y) :=
  relativeHomotopyGroupGroup n
    ({p : smashProductPair X Y | smashWedge X Y p} : Set (smashProductPair X Y))
    (smashWedgeRelativeBasepoint X Y)

-- Pin the `PathToSet` topology instance to the chosen wedge-basepoint spelling used below.
local instance smashWedgeRelativePathToSetTopologicalSpace
    (X Y : BasedSpace) :
    TopologicalSpace
      (PathToSet
        ({p : smashProductPair X Y | smashWedge X Y p} : Set (smashProductPair X Y))
        (smashWedgeRelativeBasepoint X Y).1) :=
  PathToSet.instTopologicalSpace
    ({p : smashProductPair X Y | smashWedge X Y p} : Set (smashProductPair X Y))
    (smashWedgeRelativeBasepoint X Y)

/-- Applying `relativeHomotopyGroup_succ` to `smashWedgeRelativeHomotopyGroup` recovers the
path-space model for `π_(n+1)(X × Y, smashWedge X Y)`. -/
@[simp] theorem smashWedgeRelativeHomotopyGroup_eq_pi
    (n : ℕ) (X Y : BasedSpace) :
    smashWedgeRelativeHomotopyGroup n X Y =
      π_ n
        (PathToSet
          ({p : smashProductPair X Y | smashWedge X Y p} : Set (smashProductPair X Y))
          (smashWedgeRelativeBasepoint X Y).1)
        (PathToSet.refl (smashWedgeRelativeBasepoint X Y)) := by
  exact
    relativeHomotopyGroup_succ n
      ({p : smashProductPair X Y | smashWedge X Y p} : Set (smashProductPair X Y))
      (smashWedgeRelativeBasepoint X Y)

/-- For Problem 9.7.1, writing the source hypothesis `n ≥ 2` as `n + 2`, the multiplicative
homotopy group `π_ (n + 2) (binaryWedge X Y)` decomposes as the product of `π_ (n + 2) X`,
`π_ (n + 2) Y`, and the relative term `π_ (n + 3) (X × Y, smashWedge X Y)`. In the
multiplicative `π_` API, this product is the source-facing `⊕` decomposition surface. -/
abbrev wedgeHomotopyGroup_mulEquiv_prod_prod_relative
    (n : ℕ) (X Y : BasedSpace) :
    Type _ :=
  basedHomotopyGroup (n + 2) (binaryWedge X Y) ≃*
    ((basedHomotopyGroup (n + 2) X ×
        basedHomotopyGroup (n + 2) Y) ×
      smashWedgeRelativeHomotopyGroup (n + 2) X Y)

/-- Helper for Problem 9.7.1: `X.right × Y.right` pointed at
`(underTopBasepoint X, underTopBasepoint Y)`. -/
abbrev productPairBasedSpace (X Y : BasedSpace) : BasedSpace :=
  underTopOfPoint (smashProductPair X Y) (smashProductBasepointPair X Y)

/-- Helper for Problem 9.7.1: the left coproduct leg `X ⟶ X ∨ Y`. -/
abbrev binaryWedgeLeftInclusion (X Y : BasedSpace) : X ⟶ binaryWedge X Y :=
  Sigma.ι (fun b : Bool ↦ cond b X Y) true

/-- Helper for Problem 9.7.1: the right coproduct leg `Y ⟶ X ∨ Y`. -/
abbrev binaryWedgeRightInclusion (X Y : BasedSpace) : Y ⟶ binaryWedge X Y :=
  Sigma.ι (fun b : Bool ↦ cond b X Y) false

/-- Helper for Problem 9.7.1: the projection `X ∨ Y ⟶ X` that restricts to the identity on the
left summand and the constant map on the right summand. -/
def binaryWedgeLeftProjection (X Y : BasedSpace) : binaryWedge X Y ⟶ X :=
  Sigma.desc
    (fun
      | true => 𝟙 X
      | false => constantBasedMap Y X)

/-- Helper for Problem 9.7.1: the projection `X ∨ Y ⟶ Y` that restricts to the constant map on
the left summand and the identity on the right summand. -/
def binaryWedgeRightProjection (X Y : BasedSpace) : binaryWedge X Y ⟶ Y :=
  Sigma.desc
    (fun
      | true => constantBasedMap X Y
      | false => 𝟙 Y)

/-- Helper for Problem 9.7.1: the specialized map on positive homotopy groups attached to a
continuous map whose target basepoint has been identified with a chosen point. -/
def homotopyGroupMapOverEq
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (hf : f a = b) (n : ℕ) :
    π_ (n + 1) A a → π_ (n + 1) B b :=
  match hf with
  | rfl => homotopyGroupMap f (n + 1) a

/-- Helper for Problem 9.7.1: changing only the proof of the target-basepoint equality does not
change `homotopyGroupMapOverEq`. -/
theorem homotopyGroupMapOverEq_proofIrrel
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (h₁ h₂ : f a = b) (n : ℕ) :
    homotopyGroupMapOverEq f h₁ n = homotopyGroupMapOverEq f h₂ n := by
  -- The target equality proof is proposition-valued, so the match defining the specialized map is
  -- proof irrelevant.
  cases h₁
  cases h₂
  rfl

/-- Helper for Problem 9.7.1: equal continuous maps induce equal specialized maps on positive
homotopy groups. -/
theorem homotopyGroupMapOverEq_congr
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f g : C(A, B)} (hfg : f = g) {a : A} {b : B} (hf : f a = b) (hg : g a = b) (n : ℕ) :
    homotopyGroupMapOverEq f hf n = homotopyGroupMapOverEq g hg n := by
  subst hfg
  exact homotopyGroupMapOverEq_proofIrrel f hf hg n

/-- Helper for Problem 9.7.1: postcomposition on homotopy groups respects composition. -/
theorem homotopyGroupMap_comp
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C)) (q : ℕ) (a : A) :
    homotopyGroupMap (g.comp f) q a =
      (homotopyGroupMap g q (f a)) ∘ homotopyGroupMap f q a := by
  -- Reduce the equality to generalized-loop representatives, where both sides are literally the
  -- same postcomposition.
  funext x
  refine Quotient.inductionOn x ?_
  intro γ
  rfl

/-- Helper for Problem 9.7.1: the specialized positive-degree map preserves multiplication. -/
theorem homotopyGroupMapOverEq_mul
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (hf : f a = b) (n : ℕ)
    (p q : π_ (n + 1) A a) :
    homotopyGroupMapOverEq f hf n (p * q) =
      homotopyGroupMapOverEq f hf n p * homotopyGroupMapOverEq f hf n q := by
  -- After the target-point equality is discharged, this is the usual multiplicativity of
  -- `homotopyGroupMap`.
  subst hf
  exact homotopyGroupMap_mul f n a p q

/-- Helper for Problem 9.7.1: the specialized positive-degree map preserves the unit class. -/
theorem homotopyGroupMapOverEq_one
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (hf : f a = b) (n : ℕ) :
    homotopyGroupMapOverEq f hf n (1 : π_ (n + 1) A a) = 1 := by
  -- After the target-point transport is removed, this is the ordinary unit law for
  -- `homotopyGroupMap`.
  subst hf
  exact homotopyGroupMap_one f n a

/-- Helper for Problem 9.7.1: the specialized positive-degree map can be bundled as a monoid
homomorphism. -/
def homotopyGroupMapOverEqMulHom
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (hf : f a = b) (n : ℕ) :
    π_ (n + 1) A a →* π_ (n + 1) B b where
  toFun := homotopyGroupMapOverEq f hf n
  map_one' := by
    -- After the target-basepoint transport is removed, this is the ordinary unit law for
    -- `homotopyGroupMap`.
    subst hf
    exact homotopyGroupMap_one f n a
  map_mul' := by
    -- Multiplicativity is exactly the previously isolated companion theorem.
    exact homotopyGroupMapOverEq_mul f hf n

/-- Helper for Problem 9.7.1: a constant map induces the trivial map on positive homotopy groups.
-/
theorem homotopyGroupMapOverEq_const_eq_one
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (b : B) (n : ℕ) (a : A) (x : π_ (n + 1) A a) :
    homotopyGroupMapOverEq (ContinuousMap.const A b) rfl n x = 1 := by
  -- Quotient representatives map to the constant generalized loop.
  refine Quotient.inductionOn x ?_
  intro γ
  change Quotient.mk' (genLoopMap (ContinuousMap.const A b) γ) = Quotient.mk' GenLoop.const
  exact congrArg Quotient.mk' (genLoopMap_const (ContinuousMap.const A b) (q := n + 1) (y := a))

/-- Helper for Problem 9.7.1: composing specialized positive-degree maps matches specializing the
composite map. -/
theorem homotopyGroupMapOverEq_comp
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C))
    {a : A} {b : B} {c : C} (hf : f a = b) (hg : g b = c) (n : ℕ) :
    (homotopyGroupMapOverEq g hg n) ∘ (homotopyGroupMapOverEq f hf n) =
      homotopyGroupMapOverEq (g.comp f)
        (by simpa [ContinuousMap.comp_apply, hf] using hg) n := by
  -- First remove the proof transports, then apply functoriality of `homotopyGroupMap`.
  funext x
  subst hf
  subst hg
  simpa [homotopyGroupMapOverEq] using
    congrFun (homotopyGroupMap_comp f g (n + 1) a).symm x

/-- Helper for Problem 9.7.1: the specialized map of the identity is the identity. -/
theorem homotopyGroupMapOverEq_id
    {A : Type*} [TopologicalSpace A] (a : A) (n : ℕ) :
    homotopyGroupMapOverEq (ContinuousMap.id A) (a := a) (b := a) rfl n = id := by
  -- With no transport remaining, this is exactly the identity-induced map on `π_(n + 1)`.
  funext x
  simp [homotopyGroupMapOverEq, homotopyGroupMap_id]

/-- Helper for Problem 9.7.1: the left projection restricts to the identity on the left summand.
-/
@[simp] theorem binaryWedgeLeftProjection_comp_leftInclusion (X Y : BasedSpace) :
    binaryWedgeLeftInclusion X Y ≫ binaryWedgeLeftProjection X Y = 𝟙 X := by
  -- The coproduct descent agrees with its prescribed left branch.
  apply Under.UnderMorphism.ext
  simpa [binaryWedgeLeftInclusion, binaryWedgeLeftProjection] using
    congrArg (fun f ↦ f.right)
      (Sigma.ι_desc
        (f := fun b : Bool ↦ cond b X Y)
        (p := fun
          | true => (𝟙 X : X ⟶ X)
          | false => constantBasedMap Y X)
        true)

/-- Helper for Problem 9.7.1: the left projection restricts to the constant map on the right
summand. -/
@[simp] theorem binaryWedgeLeftProjection_comp_rightInclusion (X Y : BasedSpace) :
    binaryWedgeRightInclusion X Y ≫ binaryWedgeLeftProjection X Y = constantBasedMap Y X := by
  -- The coproduct descent agrees with its prescribed right branch.
  apply Under.UnderMorphism.ext
  simpa [binaryWedgeRightInclusion, binaryWedgeLeftProjection] using
    congrArg (fun f ↦ f.right)
      (Sigma.ι_desc
        (f := fun b : Bool ↦ cond b X Y)
        (p := fun
          | true => (𝟙 X : X ⟶ X)
          | false => constantBasedMap Y X)
        false)

/-- Helper for Problem 9.7.1: the right projection restricts to the constant map on the left
summand. -/
@[simp] theorem binaryWedgeRightProjection_comp_leftInclusion (X Y : BasedSpace) :
    binaryWedgeLeftInclusion X Y ≫ binaryWedgeRightProjection X Y = constantBasedMap X Y := by
  -- The coproduct descent agrees with its prescribed left branch.
  apply Under.UnderMorphism.ext
  simpa [binaryWedgeLeftInclusion, binaryWedgeRightProjection] using
    congrArg (fun f ↦ f.right)
      (Sigma.ι_desc
        (f := fun b : Bool ↦ cond b X Y)
        (p := fun
          | true => constantBasedMap X Y
          | false => (𝟙 Y : Y ⟶ Y))
        true)

/-- Helper for Problem 9.7.1: the right projection restricts to the identity on the right
summand. -/
@[simp] theorem binaryWedgeRightProjection_comp_rightInclusion (X Y : BasedSpace) :
    binaryWedgeRightInclusion X Y ≫ binaryWedgeRightProjection X Y = 𝟙 Y := by
  -- The coproduct descent agrees with its prescribed right branch.
  apply Under.UnderMorphism.ext
  simpa [binaryWedgeRightInclusion, binaryWedgeRightProjection] using
    congrArg (fun f ↦ f.right)
      (Sigma.ι_desc
        (f := fun b : Bool ↦ cond b X Y)
        (p := fun
          | true => constantBasedMap X Y
          | false => (𝟙 Y : Y ⟶ Y))
        false)

/-- Helper for Problem 9.7.1: the projection-induced map
`π_(n+1)(X ∨ Y) → π_(n+1)X × π_(n+1)Y`. -/
def binaryWedgeHomotopyGroupToFactors
    (n : ℕ) (X Y : BasedSpace) :
    basedHomotopyGroup (n + 1) (binaryWedge X Y) →
      (basedHomotopyGroup (n + 1) X × basedHomotopyGroup (n + 1) Y) :=
  fun z ↦
    ( homotopyGroupMapOverEq
        (binaryWedgeLeftProjection X Y).right.hom
        (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftProjection X Y))
        n z
    , homotopyGroupMapOverEq
        (binaryWedgeRightProjection X Y).right.hom
        (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightProjection X Y))
        n z )

/-- Helper for Problem 9.7.1: the section of
`binaryWedgeHomotopyGroupToFactors n X Y` built from the two coproduct legs. -/
def binaryWedgeHomotopyGroupFromFactors
    (n : ℕ) (X Y : BasedSpace) :
    basedHomotopyGroup (n + 1) X × basedHomotopyGroup (n + 1) Y →
      basedHomotopyGroup (n + 1) (binaryWedge X Y) :=
  fun z ↦
    homotopyGroupMapOverEq
        (binaryWedgeLeftInclusion X Y).right.hom
        (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftInclusion X Y))
        n z.1 *
      homotopyGroupMapOverEq
        (binaryWedgeRightInclusion X Y).right.hom
        (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightInclusion X Y))
        n z.2

/-- Helper for Problem 9.7.1: the projection-induced map on positive homotopy groups is split
surjective, with section given by the two coproduct legs. -/
theorem binaryWedgeHomotopyGroupToFactors_rightInverse
    (n : ℕ) (X Y : BasedSpace) :
    Function.RightInverse
      (binaryWedgeHomotopyGroupFromFactors n X Y)
      (binaryWedgeHomotopyGroupToFactors n X Y) := by
  intro z
  rcases z with ⟨x, y⟩
  apply Prod.ext
  · -- The left projection kills the right summand and recovers the left summand.
    simp only [binaryWedgeHomotopyGroupToFactors, binaryWedgeHomotopyGroupFromFactors]
    rw [homotopyGroupMapOverEq_mul]
    have hLeftLeftComp :
        homotopyGroupMapOverEq
            (binaryWedgeLeftProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftProjection X Y))
            n
            (homotopyGroupMapOverEq
              (binaryWedgeLeftInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftInclusion X Y))
              n x) =
          x := by
      -- Collapse the projection after the left inclusion to the identity map on `X`.
      have hbase :
          (binaryWedgeLeftProjection X Y).right.hom
              ((binaryWedgeLeftInclusion X Y).right.hom (underTopBasepoint X)) =
            underTopBasepoint X := by
        rw [fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftInclusion X Y)]
        exact fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftProjection X Y)
      have hcomp :
          (homotopyGroupMapOverEq
              (binaryWedgeLeftProjection X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftProjection X Y))
              n) ∘
            (homotopyGroupMapOverEq
              (binaryWedgeLeftInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftInclusion X Y))
              n) =
          homotopyGroupMapOverEq
            ((binaryWedgeLeftProjection X Y).right.hom.comp
              (binaryWedgeLeftInclusion X Y).right.hom)
            hbase
            n := by
        simpa using
          (homotopyGroupMapOverEq_comp
            (binaryWedgeLeftInclusion X Y).right.hom
            (binaryWedgeLeftProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftInclusion X Y))
            (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftProjection X Y))
            n)
      have hmap :
          (binaryWedgeLeftProjection X Y).right.hom.comp
              (binaryWedgeLeftInclusion X Y).right.hom =
            ContinuousMap.id X.right := by
        change ((binaryWedgeLeftInclusion X Y ≫ binaryWedgeLeftProjection X Y).right).hom =
          ((𝟙 X : X ⟶ X).right).hom
        exact congrArg (fun f ↦ f.right.hom)
          (binaryWedgeLeftProjection_comp_leftInclusion X Y)
      have hcongr :
          homotopyGroupMapOverEq
              ((binaryWedgeLeftProjection X Y).right.hom.comp
                (binaryWedgeLeftInclusion X Y).right.hom)
              hbase
              n =
            homotopyGroupMapOverEq (ContinuousMap.id X.right) rfl n := by
        -- Replace the composite based map by the identity using the wedge projection formula.
        exact homotopyGroupMapOverEq_congr hmap hbase rfl n
      exact
        (congrFun hcomp x).trans <|
          (congrFun hcongr x).trans <|
            by simpa using congrFun (homotopyGroupMapOverEq_id (underTopBasepoint X) n) x
    have hLeftRightComp :
        homotopyGroupMapOverEq
            (binaryWedgeLeftProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftProjection X Y))
            n
            (homotopyGroupMapOverEq
              (binaryWedgeRightInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightInclusion X Y))
              n y) =
          1 := by
      -- Collapse the projection after the right inclusion to the constant map on `Y`.
      have hbase :
          (binaryWedgeLeftProjection X Y).right.hom
              ((binaryWedgeRightInclusion X Y).right.hom (underTopBasepoint Y)) =
            underTopBasepoint X := by
        rw [fundamentalGroupFunctorMap_basepoint (binaryWedgeRightInclusion X Y)]
        exact fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftProjection X Y)
      have hcomp :
          (homotopyGroupMapOverEq
              (binaryWedgeLeftProjection X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftProjection X Y))
              n) ∘
            (homotopyGroupMapOverEq
              (binaryWedgeRightInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightInclusion X Y))
              n) =
          homotopyGroupMapOverEq
            ((binaryWedgeLeftProjection X Y).right.hom.comp
              (binaryWedgeRightInclusion X Y).right.hom)
            hbase
            n := by
        simpa using
          (homotopyGroupMapOverEq_comp
            (binaryWedgeRightInclusion X Y).right.hom
            (binaryWedgeLeftProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightInclusion X Y))
            (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftProjection X Y))
            n)
      have hmap :
          (binaryWedgeLeftProjection X Y).right.hom.comp
              (binaryWedgeRightInclusion X Y).right.hom =
            ContinuousMap.const Y.right (underTopBasepoint X) := by
        change ((binaryWedgeRightInclusion X Y ≫ binaryWedgeLeftProjection X Y).right).hom =
          (constantBasedMap Y X).right.hom
        exact congrArg (fun f ↦ f.right.hom)
          (binaryWedgeLeftProjection_comp_rightInclusion X Y)
      have hcongr :
          homotopyGroupMapOverEq
              ((binaryWedgeLeftProjection X Y).right.hom.comp
                (binaryWedgeRightInclusion X Y).right.hom)
              hbase
              n =
            homotopyGroupMapOverEq
              (ContinuousMap.const Y.right (underTopBasepoint X))
              rfl
              n := by
        -- Replace the composite based map by the constant map using the wedge projection formula.
        exact homotopyGroupMapOverEq_congr hmap hbase rfl n
      exact
        (congrFun hcomp y).trans <|
          (congrFun hcongr y).trans <|
            by
              simpa using
                (homotopyGroupMapOverEq_const_eq_one
                  (A := Y.right)
                  (underTopBasepoint X)
                  n
                  (underTopBasepoint Y)
                  y)
    rw [hLeftLeftComp, hLeftRightComp, mul_one]
  · -- The right projection kills the left summand and recovers the right summand.
    simp only [binaryWedgeHomotopyGroupToFactors, binaryWedgeHomotopyGroupFromFactors]
    rw [homotopyGroupMapOverEq_mul]
    have hRightLeftComp :
        homotopyGroupMapOverEq
            (binaryWedgeRightProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightProjection X Y))
            n
            (homotopyGroupMapOverEq
              (binaryWedgeLeftInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftInclusion X Y))
              n x) =
          1 := by
      -- Collapse the projection after the left inclusion to the constant map on `X`.
      have hbase :
          (binaryWedgeRightProjection X Y).right.hom
              ((binaryWedgeLeftInclusion X Y).right.hom (underTopBasepoint X)) =
            underTopBasepoint Y := by
        rw [fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftInclusion X Y)]
        exact fundamentalGroupFunctorMap_basepoint (binaryWedgeRightProjection X Y)
      have hcomp :
          (homotopyGroupMapOverEq
              (binaryWedgeRightProjection X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightProjection X Y))
              n) ∘
            (homotopyGroupMapOverEq
              (binaryWedgeLeftInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftInclusion X Y))
              n) =
          homotopyGroupMapOverEq
            ((binaryWedgeRightProjection X Y).right.hom.comp
              (binaryWedgeLeftInclusion X Y).right.hom)
            hbase
            n := by
        simpa using
          (homotopyGroupMapOverEq_comp
            (binaryWedgeLeftInclusion X Y).right.hom
            (binaryWedgeRightProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftInclusion X Y))
            (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightProjection X Y))
            n)
      have hmap :
          (binaryWedgeRightProjection X Y).right.hom.comp
              (binaryWedgeLeftInclusion X Y).right.hom =
            ContinuousMap.const X.right (underTopBasepoint Y) := by
        change ((binaryWedgeLeftInclusion X Y ≫ binaryWedgeRightProjection X Y).right).hom =
          (constantBasedMap X Y).right.hom
        exact congrArg (fun f ↦ f.right.hom)
          (binaryWedgeRightProjection_comp_leftInclusion X Y)
      have hcongr :
          homotopyGroupMapOverEq
              ((binaryWedgeRightProjection X Y).right.hom.comp
                (binaryWedgeLeftInclusion X Y).right.hom)
              hbase
              n =
            homotopyGroupMapOverEq
              (ContinuousMap.const X.right (underTopBasepoint Y))
              rfl
              n := by
        -- Replace the composite based map by the constant map using the wedge projection formula.
        exact homotopyGroupMapOverEq_congr hmap hbase rfl n
      exact
        (congrFun hcomp x).trans <|
          (congrFun hcongr x).trans <|
            by
              simpa using
                (homotopyGroupMapOverEq_const_eq_one
                  (A := X.right)
                  (underTopBasepoint Y)
                  n
                  (underTopBasepoint X)
                  x)
    have hRightRightComp :
        homotopyGroupMapOverEq
            (binaryWedgeRightProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightProjection X Y))
            n
            (homotopyGroupMapOverEq
              (binaryWedgeRightInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightInclusion X Y))
              n y) =
          y := by
      -- Collapse the projection after the right inclusion to the identity map on `Y`.
      have hbase :
          (binaryWedgeRightProjection X Y).right.hom
              ((binaryWedgeRightInclusion X Y).right.hom (underTopBasepoint Y)) =
            underTopBasepoint Y := by
        rw [fundamentalGroupFunctorMap_basepoint (binaryWedgeRightInclusion X Y)]
        exact fundamentalGroupFunctorMap_basepoint (binaryWedgeRightProjection X Y)
      have hcomp :
          (homotopyGroupMapOverEq
              (binaryWedgeRightProjection X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightProjection X Y))
              n) ∘
            (homotopyGroupMapOverEq
              (binaryWedgeRightInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightInclusion X Y))
              n) =
          homotopyGroupMapOverEq
            ((binaryWedgeRightProjection X Y).right.hom.comp
              (binaryWedgeRightInclusion X Y).right.hom)
            hbase
            n := by
        simpa using
          (homotopyGroupMapOverEq_comp
            (binaryWedgeRightInclusion X Y).right.hom
            (binaryWedgeRightProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightInclusion X Y))
            (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightProjection X Y))
            n)
      have hmap :
          (binaryWedgeRightProjection X Y).right.hom.comp
              (binaryWedgeRightInclusion X Y).right.hom =
            ContinuousMap.id Y.right := by
        change ((binaryWedgeRightInclusion X Y ≫ binaryWedgeRightProjection X Y).right).hom =
          ((𝟙 Y : Y ⟶ Y).right).hom
        exact congrArg (fun f ↦ f.right.hom)
          (binaryWedgeRightProjection_comp_rightInclusion X Y)
      have hcongr :
          homotopyGroupMapOverEq
              ((binaryWedgeRightProjection X Y).right.hom.comp
                (binaryWedgeRightInclusion X Y).right.hom)
              hbase
              n =
            homotopyGroupMapOverEq (ContinuousMap.id Y.right) rfl n := by
        -- Replace the composite based map by the identity using the wedge projection formula.
        exact homotopyGroupMapOverEq_congr hmap hbase rfl n
      exact
        (congrFun hcomp y).trans <|
          (congrFun hcongr y).trans <|
            by simpa using congrFun (homotopyGroupMapOverEq_id (underTopBasepoint Y) n) y
    rw [hRightLeftComp, hRightRightComp, one_mul]

/-- Helper for Problem 9.7.1: the native wedge locus
`{p : X.right × Y.right | smashWedge X Y p}` inside `X.right × Y.right`. -/
abbrev productWedgeLocus (X Y : BasedSpace) : Set (smashProductPair X Y) :=
  {p : smashProductPair X Y | smashWedge X Y p}

/-- Helper for Problem 9.7.1: the native wedge locus as a based subspace of `X.right × Y.right`.
-/
abbrev productWedgeBasedSpace (X Y : BasedSpace) : BasedSpace :=
  inclusionBasedSubspace (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y)

/-- Helper for Problem 9.7.1: evaluating the structure map of a based space at any point of its
terminal source recovers the chosen basepoint. -/
theorem basedSpaceHom_eq_basepoint (X : BasedSpace)
    (u : ↑((Functor.fromPUnit (⊤_ TopCat)).obj X.left)) :
    (ConcreteCategory.hom X.hom) u = underTopBasepoint X := by
  -- Move `u` across the terminal-space identification and then use that `PUnit` has one point.
  calc
    (ConcreteCategory.hom X.hom) u =
      (ConcreteCategory.hom X.hom)
        ((ConcreteCategory.hom TopCat.terminalIsoPUnit.inv)
          ((ConcreteCategory.hom TopCat.terminalIsoPUnit.hom) u)) := by
            simp
    _ = (ConcreteCategory.hom X.hom)
          ((ConcreteCategory.hom TopCat.terminalIsoPUnit.inv) PUnit.unit) := by
            rw [Subsingleton.elim ((ConcreteCategory.hom TopCat.terminalIsoPUnit.hom) u) PUnit.unit]
    _ = underTopBasepoint X := by
          rfl

/-- Helper for Problem 9.7.1: the left axis map `x ↦ (x, *)` landing in the native wedge locus. -/
def productWedgeLeftAxisMap (X Y : BasedSpace) :
    C(X.right, productWedgeLocus X Y) where
  toFun x := ⟨(x, underTopBasepoint Y), Or.inr rfl⟩
  continuous_toFun := by
    -- The left axis is continuous as the product of the identity and the constant basepoint map.
    exact Continuous.subtype_mk (continuous_id.prodMk continuous_const) fun x ↦ Or.inr rfl

/-- Helper for Problem 9.7.1: the right axis map `y ↦ (*, y)` landing in the native wedge locus.
-/
def productWedgeRightAxisMap (X Y : BasedSpace) :
    C(Y.right, productWedgeLocus X Y) where
  toFun y := ⟨(underTopBasepoint X, y), Or.inl rfl⟩
  continuous_toFun := by
    -- The right axis is continuous as the product of the constant basepoint map and the identity.
    exact Continuous.subtype_mk (continuous_const.prodMk continuous_id) fun y ↦ Or.inl rfl

/-- Helper for Problem 9.7.1: the left axis inclusion `X ⟶ productWedgeBasedSpace X Y`. -/
def productWedgeLeftInclusion (X Y : BasedSpace) : X ⟶ productWedgeBasedSpace X Y :=
  Under.homMk (TopCat.ofHom (productWedgeLeftAxisMap X Y)) (by
    ext u
    -- Reduce the source-point evaluation to the chosen basepoint of `X`.
    apply Subtype.ext
    change ((ConcreteCategory.hom X.hom) u, underTopBasepoint Y) =
      (smashWedgeRelativeBasepoint X Y).1
    rw [basedSpaceHom_eq_basepoint X u]
    rfl)

/-- Helper for Problem 9.7.1: the right axis inclusion `Y ⟶ productWedgeBasedSpace X Y`. -/
def productWedgeRightInclusion (X Y : BasedSpace) : Y ⟶ productWedgeBasedSpace X Y :=
  Under.homMk (TopCat.ofHom (productWedgeRightAxisMap X Y)) (by
    ext u
    -- Reduce the source-point evaluation to the chosen basepoint of `Y`.
    apply Subtype.ext
    change (underTopBasepoint X, (ConcreteCategory.hom Y.hom) u) =
      (smashWedgeRelativeBasepoint X Y).1
    rw [basedSpaceHom_eq_basepoint Y u]
    rfl)

/-- Helper for Problem 9.7.1: the projection of the native wedge locus to the `X`-coordinate. -/
def productWedgeLeftProjectionMap (X Y : BasedSpace) :
    C(productWedgeLocus X Y, X.right) :=
  ⟨fun p ↦ p.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- Helper for Problem 9.7.1: the projection of the native wedge locus to the `Y`-coordinate. -/
def productWedgeRightProjectionMap (X Y : BasedSpace) :
    C(productWedgeLocus X Y, Y.right) :=
  ⟨fun p ↦ p.1.2, continuous_snd.comp continuous_subtype_val⟩

/-- Helper for Problem 9.7.1: the projection `productWedgeBasedSpace X Y ⟶ X`. -/
def productWedgeLeftProjection (X Y : BasedSpace) : productWedgeBasedSpace X Y ⟶ X :=
  Under.homMk (TopCat.ofHom (productWedgeLeftProjectionMap X Y)) (by
    ext u
    -- Projecting the chosen wedge-locus basepoint recovers the chosen basepoint of `X`.
    change (smashWedgeRelativeBasepoint X Y).1.1 = (ConcreteCategory.hom X.hom) u
    rw [basedSpaceHom_eq_basepoint X u])

/-- Helper for Problem 9.7.1: the projection `productWedgeBasedSpace X Y ⟶ Y`. -/
def productWedgeRightProjection (X Y : BasedSpace) : productWedgeBasedSpace X Y ⟶ Y :=
  Under.homMk (TopCat.ofHom (productWedgeRightProjectionMap X Y)) (by
    ext u
    -- Projecting the chosen wedge-locus basepoint recovers the chosen basepoint of `Y`.
    change (smashWedgeRelativeBasepoint X Y).1.2 = (ConcreteCategory.hom Y.hom) u
    rw [basedSpaceHom_eq_basepoint Y u])

/-- Helper for Problem 9.7.1: the left projection restricts to the identity on the left axis. -/
@[simp] theorem productWedgeLeftProjection_comp_leftInclusion (X Y : BasedSpace) :
    productWedgeLeftInclusion X Y ≫ productWedgeLeftProjection X Y = 𝟙 X := by
  -- The first-coordinate projection recovers the source point on the left axis.
  apply Under.UnderMorphism.ext
  ext x
  rfl

/-- Helper for Problem 9.7.1: the left projection is constant on the right axis. -/
@[simp] theorem productWedgeLeftProjection_comp_rightInclusion (X Y : BasedSpace) :
    productWedgeRightInclusion X Y ≫ productWedgeLeftProjection X Y = constantBasedMap Y X := by
  -- The first-coordinate projection sends the right axis to the chosen basepoint of `X`.
  apply Under.UnderMorphism.ext
  ext y
  rfl

/-- Helper for Problem 9.7.1: the right projection is constant on the left axis. -/
@[simp] theorem productWedgeRightProjection_comp_leftInclusion (X Y : BasedSpace) :
    productWedgeLeftInclusion X Y ≫ productWedgeRightProjection X Y = constantBasedMap X Y := by
  -- The second-coordinate projection sends the left axis to the chosen basepoint of `Y`.
  apply Under.UnderMorphism.ext
  ext x
  rfl

/-- Helper for Problem 9.7.1: the right projection restricts to the identity on the right axis. -/
@[simp] theorem productWedgeRightProjection_comp_rightInclusion (X Y : BasedSpace) :
    productWedgeRightInclusion X Y ≫ productWedgeRightProjection X Y = 𝟙 Y := by
  -- The second-coordinate projection recovers the source point on the right axis.
  apply Under.UnderMorphism.ext
  ext y
  rfl

/-- Helper for Problem 9.7.1: the canonical comparison map from the coproduct wedge model to the
native subspace wedge model. -/
def binaryWedgeToProductWedge (X Y : BasedSpace) :
    binaryWedge X Y ⟶ productWedgeBasedSpace X Y :=
  Sigma.desc (fun
    | true => productWedgeLeftInclusion X Y
    | false => productWedgeRightInclusion X Y)

/-- Helper for Problem 9.7.1: the canonical comparison map restricts to the native left-axis
inclusion on the left summand. -/
@[simp] theorem binaryWedgeToProductWedge_comp_leftInclusion (X Y : BasedSpace) :
    binaryWedgeLeftInclusion X Y ≫ binaryWedgeToProductWedge X Y =
      productWedgeLeftInclusion X Y := by
  -- The descended comparison map agrees with its prescribed left branch on the coproduct.
  simpa [binaryWedgeLeftInclusion, binaryWedgeToProductWedge] using
    Sigma.ι_desc
      (f := fun b : Bool ↦ cond b X Y)
      (p := fun
        | true => productWedgeLeftInclusion X Y
        | false => productWedgeRightInclusion X Y)
      true

/-- Helper for Problem 9.7.1: the canonical comparison map restricts to the native right-axis
inclusion on the right summand. -/
@[simp] theorem binaryWedgeToProductWedge_comp_rightInclusion (X Y : BasedSpace) :
    binaryWedgeRightInclusion X Y ≫ binaryWedgeToProductWedge X Y =
      productWedgeRightInclusion X Y := by
  -- The descended comparison map agrees with its prescribed right branch on the coproduct.
  simpa [binaryWedgeRightInclusion, binaryWedgeToProductWedge] using
    Sigma.ι_desc
      (f := fun b : Bool ↦ cond b X Y)
      (p := fun
        | true => productWedgeLeftInclusion X Y
        | false => productWedgeRightInclusion X Y)
      false

/-- Helper for Problem 9.7.1: the comparison map recovers the usual left wedge projection after
projecting from the native product-wedge model. -/
@[simp] theorem binaryWedgeToProductWedge_comp_leftProjection (X Y : BasedSpace) :
    binaryWedgeToProductWedge X Y ≫ productWedgeLeftProjection X Y =
      binaryWedgeLeftProjection X Y := by
  -- It is enough to compare the two maps on the left and right coproduct branches.
  apply Sigma.hom_ext
  intro b
  cases b
  · -- On the right branch, both composites are the constant map to the left basepoint.
    calc
      binaryWedgeRightInclusion X Y ≫ binaryWedgeToProductWedge X Y ≫
          productWedgeLeftProjection X Y =
        productWedgeRightInclusion X Y ≫ productWedgeLeftProjection X Y := by
          change
            (binaryWedgeRightInclusion X Y ≫ binaryWedgeToProductWedge X Y) ≫
                productWedgeLeftProjection X Y =
              productWedgeRightInclusion X Y ≫ productWedgeLeftProjection X Y
          rw [binaryWedgeToProductWedge_comp_rightInclusion]
      _ = constantBasedMap Y X := productWedgeLeftProjection_comp_rightInclusion X Y
      _ = binaryWedgeRightInclusion X Y ≫ binaryWedgeLeftProjection X Y := by
        symm
        exact binaryWedgeLeftProjection_comp_rightInclusion X Y
  · -- On the left branch, both composites recover the identity on `X`.
    calc
      binaryWedgeLeftInclusion X Y ≫ binaryWedgeToProductWedge X Y ≫
          productWedgeLeftProjection X Y =
        productWedgeLeftInclusion X Y ≫ productWedgeLeftProjection X Y := by
          change
            (binaryWedgeLeftInclusion X Y ≫ binaryWedgeToProductWedge X Y) ≫
                productWedgeLeftProjection X Y =
              productWedgeLeftInclusion X Y ≫ productWedgeLeftProjection X Y
          rw [binaryWedgeToProductWedge_comp_leftInclusion]
      _ = 𝟙 X := productWedgeLeftProjection_comp_leftInclusion X Y
      _ = binaryWedgeLeftInclusion X Y ≫ binaryWedgeLeftProjection X Y := by
        symm
        exact binaryWedgeLeftProjection_comp_leftInclusion X Y

/-- Helper for Problem 9.7.1: the comparison map recovers the usual right wedge projection after
projecting from the native product-wedge model. -/
@[simp] theorem binaryWedgeToProductWedge_comp_rightProjection (X Y : BasedSpace) :
    binaryWedgeToProductWedge X Y ≫ productWedgeRightProjection X Y =
      binaryWedgeRightProjection X Y := by
  -- It is enough to compare the two maps on the left and right coproduct branches.
  apply Sigma.hom_ext
  intro b
  cases b
  · -- On the right branch, both composites recover the identity on `Y`.
    calc
      binaryWedgeRightInclusion X Y ≫ binaryWedgeToProductWedge X Y ≫
          productWedgeRightProjection X Y =
        productWedgeRightInclusion X Y ≫ productWedgeRightProjection X Y := by
          change
            (binaryWedgeRightInclusion X Y ≫ binaryWedgeToProductWedge X Y) ≫
                productWedgeRightProjection X Y =
              productWedgeRightInclusion X Y ≫ productWedgeRightProjection X Y
          rw [binaryWedgeToProductWedge_comp_rightInclusion]
      _ = 𝟙 Y := productWedgeRightProjection_comp_rightInclusion X Y
      _ = binaryWedgeRightInclusion X Y ≫ binaryWedgeRightProjection X Y := by
        symm
        exact binaryWedgeRightProjection_comp_rightInclusion X Y
  · -- On the left branch, both composites are the constant map to the right basepoint.
    calc
      binaryWedgeLeftInclusion X Y ≫ binaryWedgeToProductWedge X Y ≫
          productWedgeRightProjection X Y =
        productWedgeLeftInclusion X Y ≫ productWedgeRightProjection X Y := by
          change
            (binaryWedgeLeftInclusion X Y ≫ binaryWedgeToProductWedge X Y) ≫
                productWedgeRightProjection X Y =
              productWedgeLeftInclusion X Y ≫ productWedgeRightProjection X Y
          rw [binaryWedgeToProductWedge_comp_leftInclusion]
      _ = constantBasedMap X Y := productWedgeRightProjection_comp_leftInclusion X Y
      _ = binaryWedgeLeftInclusion X Y ≫ binaryWedgeRightProjection X Y := by
        symm
        exact binaryWedgeRightProjection_comp_leftInclusion X Y

/-- Helper for Problem 9.7.1: maps out of the native wedge model are determined by their
restrictions to the left and right axes. -/
theorem productWedgeHom_ext
    {X Y Z : BasedSpace} {φ ψ : productWedgeBasedSpace X Y ⟶ Z}
    (hleft : productWedgeLeftInclusion X Y ≫ φ = productWedgeLeftInclusion X Y ≫ ψ)
    (hright : productWedgeRightInclusion X Y ≫ φ = productWedgeRightInclusion X Y ≫ ψ) :
    φ = ψ := by
  -- Every point of `productWedgeLocus X Y` lies on one of the two axes, so axis agreement
  -- determines the map on the whole subtype.
  apply Under.UnderMorphism.ext
  ext p
  rcases p with ⟨⟨x, y⟩, hp⟩
  rcases hp with hx | hy
  · -- On the right axis, evaluate the right-axis compatibility at the chosen point `y`.
    have hpRight : (productWedgeRightAxisMap X Y) y = ⟨(x, y), Or.inl hx⟩ := by
      apply Subtype.ext
      exact Prod.ext hx.symm rfl
    have hEval := congrArg (fun f : Y ⟶ Z ↦ f.right.hom y) hright
    refine hpRight ▸ ?_
    simpa [productWedgeRightInclusion, productWedgeRightAxisMap] using hEval
  · -- On the left axis, evaluate the left-axis compatibility at the chosen point `x`.
    have hpLeft : (productWedgeLeftAxisMap X Y) x = ⟨(x, y), Or.inr hy⟩ := by
      apply Subtype.ext
      exact Prod.ext rfl hy.symm
    have hEval := congrArg (fun f : X ⟶ Z ↦ f.right.hom x) hleft
    refine hpLeft ▸ ?_
    simpa [productWedgeLeftInclusion, productWedgeLeftAxisMap] using hEval

/-- Helper for Problem 9.7.1: a native wedge point whose first coordinate is not the basepoint
must lie on the left axis, so its second coordinate is the chosen basepoint of `Y`. -/
theorem productWedgeLocus_snd_eq_basepoint_of_fst_ne_basepoint
    {X Y : BasedSpace} (p : productWedgeLocus X Y)
    (hx : p.1.1 ≠ underTopBasepoint X) :
    p.1.2 = underTopBasepoint Y := by
  -- Membership in the wedge locus means the point lies on one of the two axes.
  rcases p.2 with hfst | hsnd
  · exact (hx hfst).elim
  · exact hsnd

/-- Helper for Problem 9.7.1: a native wedge point whose first coordinate is the chosen basepoint
is exactly the corresponding point on the right axis. -/
theorem productWedgePoint_eq_rightAxis_of_fst_eq_basepoint
    {X Y : BasedSpace} (p : productWedgeLocus X Y)
    (hx : p.1.1 = underTopBasepoint X) :
    p = productWedgeRightAxisMap X Y p.1.2 := by
  -- Once the first coordinate is the chosen basepoint, the subtype point is literally the right
  -- axis representative with the same second coordinate.
  apply Subtype.ext
  exact Prod.ext hx rfl

/-- Helper for Problem 9.7.1: a native wedge point whose first coordinate is not the chosen
basepoint is exactly the corresponding point on the left axis. -/
theorem productWedgePoint_eq_leftAxis_of_fst_ne_basepoint
    {X Y : BasedSpace} (p : productWedgeLocus X Y)
    (hx : p.1.1 ≠ underTopBasepoint X) :
    p = productWedgeLeftAxisMap X Y p.1.1 := by
  -- The non-basepoint branch forces the second coordinate to be the chosen basepoint of `Y`, so
  -- the point is literally the left-axis representative.
  have hy : p.1.2 = underTopBasepoint Y :=
    productWedgeLocus_snd_eq_basepoint_of_fst_ne_basepoint p hx
  apply Subtype.ext
  exact Prod.ext rfl hy

/-- Helper for Problem 9.7.1: a native wedge point whose second coordinate is the chosen
basepoint is exactly the corresponding point on the left axis. -/
theorem productWedgePoint_eq_leftAxis_of_snd_eq_basepoint
    {X Y : BasedSpace} (p : productWedgeLocus X Y)
    (hy : p.1.2 = underTopBasepoint Y) :
    p = productWedgeLeftAxisMap X Y p.1.1 := by
  -- Once the second coordinate is the chosen basepoint, the subtype point is literally the left
  -- axis representative with the same first coordinate.
  apply Subtype.ext
  exact Prod.ext rfl hy

/-- Helper for Problem 9.7.1: the two axis maps agree at the shared basepoint of the native
wedge locus. -/
@[simp] theorem productWedgeAxis_basepoint
    (X Y : BasedSpace) :
    productWedgeLeftAxisMap X Y (underTopBasepoint X) =
      productWedgeRightAxisMap X Y (underTopBasepoint Y) := by
  -- Both axis maps send the chosen basepoints to the same subtype point `(*, *)`.
  apply Subtype.ext
  rfl

/-- Helper for Problem 9.7.1: the left and right axis pullbacks contain the shared basepoint
simultaneously. -/
theorem productWedgeAxisBasepoint_mem_iff
    {X Y : BasedSpace} {A : Set (productWedgeLocus X Y)} :
    underTopBasepoint X ∈ (productWedgeLeftAxisMap X Y) ⁻¹' A ↔
      underTopBasepoint Y ∈ (productWedgeRightAxisMap X Y) ⁻¹' A := by
  -- Both pullback memberships say exactly that the common wedge basepoint lies in `A`.
  change
    productWedgeLeftAxisMap X Y (underTopBasepoint X) ∈ A ↔
      productWedgeRightAxisMap X Y (underTopBasepoint Y) ∈ A
  rw [productWedgeAxis_basepoint]

/-- Helper for Problem 9.7.1: if a subset of the native wedge locus contains the shared basepoint,
then membership is equivalent to simultaneous membership in the two axis pullbacks. -/
theorem productWedgeMem_iff_of_basepoint_mem
    {X Y : BasedSpace} {A : Set (productWedgeLocus X Y)}
    (hA : smashWedgeRelativeBasepoint X Y ∈ A)
    (p : productWedgeLocus X Y) :
    p ∈ A ↔
      p.1.1 ∈ (productWedgeLeftAxisMap X Y) ⁻¹' A ∧
        p.1.2 ∈ (productWedgeRightAxisMap X Y) ⁻¹' A := by
  -- First record that both axis pullbacks contain the shared basepoint.
  have hLeftBase :
      underTopBasepoint X ∈ (productWedgeLeftAxisMap X Y) ⁻¹' A := by
    simpa [Set.mem_preimage, productWedgeLeftAxisMap, smashWedgeRelativeBasepoint] using hA
  have hRightBase :
      underTopBasepoint Y ∈ (productWedgeRightAxisMap X Y) ⁻¹' A := by
    exact (productWedgeAxisBasepoint_mem_iff (A := A)).mp hLeftBase
  -- Split on whether the point lies on the right or left axis.
  by_cases hx : p.1.1 = underTopBasepoint X
  · have hpRight :
        p = productWedgeRightAxisMap X Y p.1.2 :=
      productWedgePoint_eq_rightAxis_of_fst_eq_basepoint p hx
    constructor
    · intro hp
      refine ⟨?_, ?_⟩
      · simpa [Set.mem_preimage, hx] using hLeftBase
      · rw [Set.mem_preimage]
        exact hpRight ▸ hp
    · intro hp
      rw [Set.mem_preimage] at hp
      exact hpRight ▸ hp.2
  · have hpLeft :
        p = productWedgeLeftAxisMap X Y p.1.1 :=
      productWedgePoint_eq_leftAxis_of_fst_ne_basepoint p hx
    have hy : p.1.2 = underTopBasepoint Y :=
      productWedgeLocus_snd_eq_basepoint_of_fst_ne_basepoint p hx
    constructor
    · intro hp
      refine ⟨?_, ?_⟩
      · rw [Set.mem_preimage]
        exact hpLeft ▸ hp
      · rw [Set.mem_preimage, hy]
        exact hRightBase
    · intro hp
      rw [Set.mem_preimage] at hp
      exact hpLeft ▸ hp.1

/-- Helper for Problem 9.7.1: if a subset of the native wedge locus misses the shared basepoint,
then membership is equivalent to membership in at least one axis pullback. -/
theorem productWedgeMem_iff_of_basepoint_not_mem
    {X Y : BasedSpace} {A : Set (productWedgeLocus X Y)}
    (hA : smashWedgeRelativeBasepoint X Y ∉ A)
    (p : productWedgeLocus X Y) :
    p ∈ A ↔
      p.1.1 ∈ (productWedgeLeftAxisMap X Y) ⁻¹' A ∨
        p.1.2 ∈ (productWedgeRightAxisMap X Y) ⁻¹' A := by
  -- First record that neither axis pullback contains the shared basepoint.
  have hLeftBase :
      underTopBasepoint X ∉ (productWedgeLeftAxisMap X Y) ⁻¹' A := by
    intro hx
    exact hA (by
      simpa [Set.mem_preimage, productWedgeLeftAxisMap, smashWedgeRelativeBasepoint] using hx)
  have hRightBase :
      underTopBasepoint Y ∉ (productWedgeRightAxisMap X Y) ⁻¹' A := by
    intro hy
    exact hLeftBase ((productWedgeAxisBasepoint_mem_iff (A := A)).mpr hy)
  -- Split on whether the point lies on the right or left axis.
  by_cases hx : p.1.1 = underTopBasepoint X
  · have hpRight :
        p = productWedgeRightAxisMap X Y p.1.2 :=
      productWedgePoint_eq_rightAxis_of_fst_eq_basepoint p hx
    constructor
    · intro hp
      right
      rw [Set.mem_preimage]
      exact hpRight ▸ hp
    · intro hp
      rcases hp with hp | hp
      · exact False.elim (hLeftBase (by simpa [Set.mem_preimage, hx] using hp))
      · rw [Set.mem_preimage] at hp
        exact hpRight ▸ hp
  · have hpLeft :
        p = productWedgeLeftAxisMap X Y p.1.1 :=
      productWedgePoint_eq_leftAxis_of_fst_ne_basepoint p hx
    have hy : p.1.2 = underTopBasepoint Y :=
      productWedgeLocus_snd_eq_basepoint_of_fst_ne_basepoint p hx
    constructor
    · intro hp
      left
      rw [Set.mem_preimage]
      exact hpLeft ▸ hp
    · intro hp
      rcases hp with hp | hp
      · rw [Set.mem_preimage] at hp
        exact hpLeft ▸ hp
      · exact False.elim (hRightBase (by simpa [Set.mem_preimage, hy] using hp))

/-- Helper for Problem 9.7.1: a subset of the native wedge locus is open exactly when its pullbacks
to the left and right axes are open. -/
theorem productWedgeIsOpen_iff_of_axes
    {X Y : BasedSpace} (A : Set (productWedgeLocus X Y)) :
    IsOpen A ↔
      IsOpen ((productWedgeLeftAxisMap X Y) ⁻¹' A) ∧
        IsOpen ((productWedgeRightAxisMap X Y) ⁻¹' A) := by
  -- The forward direction is immediate from continuity of the two axis maps.
  constructor
  · intro hA
    exact ⟨hA.preimage (productWedgeLeftAxisMap X Y).continuous,
      hA.preimage (productWedgeRightAxisMap X Y).continuous⟩
  · intro hAxes
    let L : Set X.right := (productWedgeLeftAxisMap X Y) ⁻¹' A
    let R : Set Y.right := (productWedgeRightAxisMap X Y) ⁻¹' A
    have hOpenL : IsOpen L := by
      simpa [L] using hAxes.1
    have hOpenR : IsOpen R := by
      simpa [R] using hAxes.2
    -- Route correction: rewrite `A` as a subtype preimage of an ambient rectangle or strip union,
    -- depending on whether it contains the shared basepoint.
    by_cases hBase : smashWedgeRelativeBasepoint X Y ∈ A
    · let S : Set (smashProductPair X Y) := (Prod.fst ⁻¹' L) ∩ (Prod.snd ⁻¹' R)
      have hEq : A = Subtype.val ⁻¹' S := by
        ext p
        simpa [L, R, S, Set.mem_preimage] using
          (productWedgeMem_iff_of_basepoint_mem (X := X) (Y := Y) (A := A) hBase p)
      have hOpenS : IsOpen S := by
        exact (hOpenL.preimage continuous_fst).inter (hOpenR.preimage continuous_snd)
      rw [hEq]
      exact hOpenS.preimage continuous_subtype_val
    · let S : Set (smashProductPair X Y) := (Prod.fst ⁻¹' L) ∪ (Prod.snd ⁻¹' R)
      have hEq : A = Subtype.val ⁻¹' S := by
        ext p
        simpa [L, R, S, Set.mem_preimage] using
          (productWedgeMem_iff_of_basepoint_not_mem (X := X) (Y := Y) (A := A) hBase p)
      have hOpenS : IsOpen S := by
        exact (hOpenL.preimage continuous_fst).union (hOpenR.preimage continuous_snd)
      rw [hEq]
      exact hOpenS.preimage continuous_subtype_val

/-- Helper for Problem 9.7.1: a map out of the native wedge locus is continuous exactly when its
restrictions to the left and right axes are continuous. -/
theorem productWedgeContinuous_iff_of_axes
    {X Y : BasedSpace} {Z : Type*} [TopologicalSpace Z]
    (f : productWedgeLocus X Y → Z) :
    Continuous f ↔
      Continuous (fun x : X.right ↦ f (productWedgeLeftAxisMap X Y x)) ∧
        Continuous (fun y : Y.right ↦ f (productWedgeRightAxisMap X Y y)) := by
  -- Continuity on the native wedge is equivalent to openness of all preimages, and the openness
  -- criterion above reduces those preimages to the two axis pullbacks.
  rw [continuous_def, continuous_def, continuous_def]
  constructor
  · intro hf
    refine ⟨?_, ?_⟩
    · intro U hU
      simpa [Set.preimage_preimage] using
        (hf U hU).preimage (productWedgeLeftAxisMap X Y).continuous
    · intro U hU
      simpa [Set.preimage_preimage] using
        (hf U hU).preimage (productWedgeRightAxisMap X Y).continuous
  · intro h U hU
    rw [productWedgeIsOpen_iff_of_axes]
    refine ⟨?_, ?_⟩
    · simpa [Set.preimage_preimage] using h.1 U hU
    · simpa [Set.preimage_preimage] using h.2 U hU

/-- Helper for Problem 9.7.1: the pointwise native-to-binary comparison sends a locus point to
the right wedge leg when its first coordinate is the shared basepoint, and otherwise to the left
wedge leg. -/
noncomputable def productWedgeToBinaryWedgePoint
    (X Y : BasedSpace) (p : productWedgeLocus X Y) :
    (binaryWedge X Y).right :=
  let _ := Classical.decEq X.right
  if _hx : p.1.1 = underTopBasepoint X then
    (binaryWedgeRightInclusion X Y).right.hom p.1.2
  else
    (binaryWedgeLeftInclusion X Y).right.hom p.1.1

/-- Helper for Problem 9.7.1: the pointwise native-to-binary formula is continuous once the
native wedge locus is known to carry the final topology from its two axis inclusions. -/
theorem productWedgeToBinaryWedgeMap_continuous
    (X Y : BasedSpace) :
    Continuous (productWedgeToBinaryWedgePoint X Y) := by
  -- Route correction: instead of trying to prove continuity from the `if` formula directly, use
  -- the recovered two-axis openness criterion on `productWedgeLocus X Y` and check only the
  -- two axis restrictions.
  rw [productWedgeContinuous_iff_of_axes]
  refine ⟨?_, ?_⟩
  · -- On the left axis, the pointwise formula is exactly the left wedge inclusion.
    have hLeftAxis :
        (fun x : X.right ↦ productWedgeToBinaryWedgePoint X Y (productWedgeLeftAxisMap X Y x)) =
          (binaryWedgeLeftInclusion X Y).right.hom := by
      funext x
      classical
      by_cases hx : x = underTopBasepoint X
      · subst hx
        change
            (if underTopBasepoint X = underTopBasepoint X then
              (binaryWedgeRightInclusion X Y).right.hom (underTopBasepoint Y)
            else
              (binaryWedgeLeftInclusion X Y).right.hom (underTopBasepoint X)) =
              (binaryWedgeLeftInclusion X Y).right.hom (underTopBasepoint X)
        simp [fundamentalGroupFunctorMap_basepoint]
      · change
            (if x = underTopBasepoint X then
              (binaryWedgeRightInclusion X Y).right.hom (underTopBasepoint Y)
            else
              (binaryWedgeLeftInclusion X Y).right.hom x) =
              (binaryWedgeLeftInclusion X Y).right.hom x
        simp [hx]
    rw [hLeftAxis]
    exact (binaryWedgeLeftInclusion X Y).right.hom.continuous
  · -- On the right axis, the pointwise formula is exactly the right wedge inclusion.
    have hRightAxis :
        (fun y : Y.right ↦ productWedgeToBinaryWedgePoint X Y (productWedgeRightAxisMap X Y y)) =
          (binaryWedgeRightInclusion X Y).right.hom := by
      funext y
      classical
      change
          (if underTopBasepoint X = underTopBasepoint X then
            (binaryWedgeRightInclusion X Y).right.hom y
          else
            (binaryWedgeLeftInclusion X Y).right.hom (underTopBasepoint X)) =
            (binaryWedgeRightInclusion X Y).right.hom y
      simp
    rw [hRightAxis]
    exact (binaryWedgeRightInclusion X Y).right.hom.continuous

/-- Helper for Problem 9.7.1: on the right axis, the pointwise comparison formula is exactly the
right wedge leg. -/
@[simp] theorem productWedgeToBinaryWedgePoint_rightAxis
    (X Y : BasedSpace) (y : Y.right) :
    productWedgeToBinaryWedgePoint X Y (productWedgeRightAxisMap X Y y) =
      (binaryWedgeRightInclusion X Y).right.hom y := by
  -- The right axis has first coordinate equal to the chosen basepoint, so the `if` picks the
  -- right wedge leg immediately.
  classical
  change
      (if underTopBasepoint X = underTopBasepoint X then
        (binaryWedgeRightInclusion X Y).right.hom y
      else
        (binaryWedgeLeftInclusion X Y).right.hom (underTopBasepoint X)) =
        (binaryWedgeRightInclusion X Y).right.hom y
  simp

/-- Helper for Problem 9.7.1: on the left axis, the pointwise comparison formula is exactly the
left wedge leg, including at the shared basepoint. -/
@[simp] theorem productWedgeToBinaryWedgePoint_leftAxis
    (X Y : BasedSpace) (x : X.right) :
    productWedgeToBinaryWedgePoint X Y (productWedgeLeftAxisMap X Y x) =
      (binaryWedgeLeftInclusion X Y).right.hom x := by
  -- Away from the shared basepoint the formula picks the left wedge leg directly, while at the
  -- basepoint both wedge legs agree with the chosen wedge basepoint.
  classical
  by_cases hx : x = underTopBasepoint X
  · subst hx
    change
        (if underTopBasepoint X = underTopBasepoint X then
          (binaryWedgeRightInclusion X Y).right.hom (underTopBasepoint Y)
        else
          (binaryWedgeLeftInclusion X Y).right.hom (underTopBasepoint X)) =
          (binaryWedgeLeftInclusion X Y).right.hom (underTopBasepoint X)
    simp [fundamentalGroupFunctorMap_basepoint]
  · change
        (if x = underTopBasepoint X then
          (binaryWedgeRightInclusion X Y).right.hom (underTopBasepoint Y)
        else
          (binaryWedgeLeftInclusion X Y).right.hom x) =
          (binaryWedgeLeftInclusion X Y).right.hom x
    simp [hx]

/-- Helper for Problem 9.7.1: the explicit pointwise formula for the comparison map from the
native wedge locus to the coproduct wedge. -/
def productWedgeToBinaryWedgeMap
    (X Y : BasedSpace) :
    C(productWedgeLocus X Y, (binaryWedge X Y).right) :=
  { toFun := productWedgeToBinaryWedgePoint X Y
    -- The only remaining work is the continuity companion theorem isolated above.
    continuous_toFun := productWedgeToBinaryWedgeMap_continuous X Y }

/-- Helper for Problem 9.7.1: the pointwise native-to-binary formula sends the native basepoint
to the coproduct wedge basepoint. -/
theorem productWedgeToBinaryWedgeMap_basepoint (X Y : BasedSpace) :
    productWedgeToBinaryWedgeMap X Y (underTopBasepoint (productWedgeBasedSpace X Y)) =
      underTopBasepoint (binaryWedge X Y) := by
  -- At the chosen basepoint the explicit branch formula is the right wedge leg at `*`.
  simpa [productWedgeToBinaryWedgeMap, smashWedgeRelativeBasepoint, productWedgeRightAxisMap] using
    productWedgeToBinaryWedgePoint_rightAxis X Y (underTopBasepoint Y)

/-- Helper for Problem 9.7.1: the native product-wedge model maps back to the coproduct wedge by
the explicit axis formula. -/
def productWedgeToBinaryWedge (X Y : BasedSpace) :
    productWedgeBasedSpace X Y ⟶ binaryWedge X Y :=
  Under.homMk (TopCat.ofHom (productWedgeToBinaryWedgeMap X Y))
    (by
      -- The explicit comparison formula preserves the chosen wedge basepoint.
      ext u
      calc
        productWedgeToBinaryWedgeMap X Y (underTopBasepoint (productWedgeBasedSpace X Y)) =
            underTopBasepoint (binaryWedge X Y) :=
          productWedgeToBinaryWedgeMap_basepoint X Y
        _ = (ConcreteCategory.hom (binaryWedge X Y).hom) u :=
          (basedSpaceHom_eq_basepoint (binaryWedge X Y) u).symm)

/-- Helper for Problem 9.7.1: the native-to-binary comparison restricts to the left wedge leg on
the left axis. -/
@[simp] theorem productWedgeToBinaryWedge_comp_leftInclusion (X Y : BasedSpace) :
    productWedgeLeftInclusion X Y ≫ productWedgeToBinaryWedge X Y =
      binaryWedgeLeftInclusion X Y := by
  -- On the left axis, the explicit pointwise formula chooses the left coproduct branch.
  apply Under.UnderMorphism.ext
  ext x
  simpa [productWedgeToBinaryWedge, productWedgeToBinaryWedgeMap, productWedgeLeftInclusion] using
    productWedgeToBinaryWedgePoint_leftAxis X Y x

/-- Helper for Problem 9.7.1: the native-to-binary comparison restricts to the right wedge leg on
the right axis. -/
@[simp] theorem productWedgeToBinaryWedge_comp_rightInclusion (X Y : BasedSpace) :
    productWedgeRightInclusion X Y ≫ productWedgeToBinaryWedge X Y =
      binaryWedgeRightInclusion X Y := by
  -- On the right axis, the explicit pointwise formula chooses the right coproduct branch.
  apply Under.UnderMorphism.ext
  ext y
  simpa [productWedgeToBinaryWedge, productWedgeToBinaryWedgeMap, productWedgeRightInclusion] using
    productWedgeToBinaryWedgePoint_rightAxis X Y y

/-- Helper for Problem 9.7.1: the coproduct wedge comparison followed by the native-to-binary
comparison is the identity on the coproduct wedge. -/
@[simp] theorem binaryWedgeToProductWedge_comp_productWedgeToBinaryWedge (X Y : BasedSpace) :
    binaryWedgeToProductWedge X Y ≫ productWedgeToBinaryWedge X Y = 𝟙 (binaryWedge X Y) := by
  -- Compare the two maps on the left and right coproduct branches.
  apply Sigma.hom_ext
  intro b
  cases b
  · -- On the right summand, the two comparisons reduce to the right inclusion.
    simpa [Category.assoc] using
      calc
        binaryWedgeRightInclusion X Y ≫ binaryWedgeToProductWedge X Y ≫
            productWedgeToBinaryWedge X Y =
          productWedgeRightInclusion X Y ≫ productWedgeToBinaryWedge X Y := by
            change
              (binaryWedgeRightInclusion X Y ≫ binaryWedgeToProductWedge X Y) ≫
                  productWedgeToBinaryWedge X Y =
                productWedgeRightInclusion X Y ≫ productWedgeToBinaryWedge X Y
            rw [binaryWedgeToProductWedge_comp_rightInclusion]
        _ = binaryWedgeRightInclusion X Y :=
          productWedgeToBinaryWedge_comp_rightInclusion X Y
  · -- On the left summand, the two comparisons reduce to the left inclusion.
    simpa [Category.assoc] using
      calc
        binaryWedgeLeftInclusion X Y ≫ binaryWedgeToProductWedge X Y ≫
            productWedgeToBinaryWedge X Y =
          productWedgeLeftInclusion X Y ≫ productWedgeToBinaryWedge X Y := by
            change
              (binaryWedgeLeftInclusion X Y ≫ binaryWedgeToProductWedge X Y) ≫
                  productWedgeToBinaryWedge X Y =
                productWedgeLeftInclusion X Y ≫ productWedgeToBinaryWedge X Y
            rw [binaryWedgeToProductWedge_comp_leftInclusion]
        _ = binaryWedgeLeftInclusion X Y :=
          productWedgeToBinaryWedge_comp_leftInclusion X Y

/-- Helper for Problem 9.7.1: the native-to-binary comparison followed by the coproduct wedge
comparison is the identity on the native wedge model. -/
@[simp] theorem productWedgeToBinaryWedge_comp_binaryWedgeToProductWedge (X Y : BasedSpace) :
    productWedgeToBinaryWedge X Y ≫ binaryWedgeToProductWedge X Y =
      𝟙 (productWedgeBasedSpace X Y) := by
  -- Compare the two maps on the native left and right axes.
  apply productWedgeHom_ext
  · -- The left axis is fixed by the two comparison maps.
    simpa [Category.assoc] using
      calc
        productWedgeLeftInclusion X Y ≫ productWedgeToBinaryWedge X Y ≫
            binaryWedgeToProductWedge X Y =
          binaryWedgeLeftInclusion X Y ≫ binaryWedgeToProductWedge X Y := by
            change
              (productWedgeLeftInclusion X Y ≫ productWedgeToBinaryWedge X Y) ≫
                  binaryWedgeToProductWedge X Y =
                binaryWedgeLeftInclusion X Y ≫ binaryWedgeToProductWedge X Y
            rw [productWedgeToBinaryWedge_comp_leftInclusion]
        _ = productWedgeLeftInclusion X Y :=
          binaryWedgeToProductWedge_comp_leftInclusion X Y
  · -- The right axis is fixed by the two comparison maps.
    simpa [Category.assoc] using
      calc
        productWedgeRightInclusion X Y ≫ productWedgeToBinaryWedge X Y ≫
            binaryWedgeToProductWedge X Y =
          binaryWedgeRightInclusion X Y ≫ binaryWedgeToProductWedge X Y := by
            change
              (productWedgeRightInclusion X Y ≫ productWedgeToBinaryWedge X Y) ≫
                  binaryWedgeToProductWedge X Y =
                binaryWedgeRightInclusion X Y ≫ binaryWedgeToProductWedge X Y
            rw [productWedgeToBinaryWedge_comp_rightInclusion]
        _ = productWedgeRightInclusion X Y :=
          binaryWedgeToProductWedge_comp_rightInclusion X Y

/-- Helper for Problem 9.7.1: the native factor map
`π_(n+1)(productWedgeBasedSpace X Y) → π_(n+1)X × π_(n+1)Y`. -/
def productWedgeHomotopyGroupToFactors
    (n : ℕ) (X Y : BasedSpace) :
    basedHomotopyGroup (n + 1) (productWedgeBasedSpace X Y) →
      (basedHomotopyGroup (n + 1) X × basedHomotopyGroup (n + 1) Y) :=
  fun z ↦
    ( homotopyGroupMapOverEq
        (productWedgeLeftProjection X Y).right.hom
        (fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y))
        n z
    , homotopyGroupMapOverEq
        (productWedgeRightProjection X Y).right.hom
        (fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y))
        n z )

/-- Helper for Problem 9.7.1: the section of
`productWedgeHomotopyGroupToFactors n X Y` built from the two native axis inclusions. -/
def productWedgeHomotopyGroupFromFactors
    (n : ℕ) (X Y : BasedSpace) :
    basedHomotopyGroup (n + 1) X × basedHomotopyGroup (n + 1) Y →
      basedHomotopyGroup (n + 1) (productWedgeBasedSpace X Y) :=
  fun z ↦
    homotopyGroupMapOverEq
        (productWedgeLeftInclusion X Y).right.hom
        (fundamentalGroupFunctorMap_basepoint (productWedgeLeftInclusion X Y))
        n z.1 *
      homotopyGroupMapOverEq
        (productWedgeRightInclusion X Y).right.hom
        (fundamentalGroupFunctorMap_basepoint (productWedgeRightInclusion X Y))
        n z.2

/-- Helper for Problem 9.7.1: the native factor map on the wedge locus is split surjective, with
section given by the two axis inclusions. -/
theorem productWedgeHomotopyGroupToFactors_rightInverse
    (n : ℕ) (X Y : BasedSpace) :
    Function.RightInverse
      (productWedgeHomotopyGroupFromFactors n X Y)
      (productWedgeHomotopyGroupToFactors n X Y) := by
  intro z
  rcases z with ⟨x, y⟩
  apply Prod.ext
  · -- The left projection kills the right axis contribution and recovers the left one.
    simp only [productWedgeHomotopyGroupToFactors, productWedgeHomotopyGroupFromFactors]
    rw [homotopyGroupMapOverEq_mul]
    have hLeftLeftComp :
        homotopyGroupMapOverEq
            (productWedgeLeftProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y))
            n
            (homotopyGroupMapOverEq
              (productWedgeLeftInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (productWedgeLeftInclusion X Y))
              n x) =
          x := by
      -- Collapse the left projection after the left axis to the identity map on `X`.
      have hbase :
          (productWedgeLeftProjection X Y).right.hom
              ((productWedgeLeftInclusion X Y).right.hom (underTopBasepoint X)) =
            underTopBasepoint X := by
        rw [fundamentalGroupFunctorMap_basepoint (productWedgeLeftInclusion X Y)]
        exact fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y)
      have hcomp :
          (homotopyGroupMapOverEq
              (productWedgeLeftProjection X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y))
              n) ∘
            (homotopyGroupMapOverEq
              (productWedgeLeftInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (productWedgeLeftInclusion X Y))
              n) =
          homotopyGroupMapOverEq
            ((productWedgeLeftProjection X Y).right.hom.comp
              (productWedgeLeftInclusion X Y).right.hom)
            hbase
            n := by
        simpa using
          (homotopyGroupMapOverEq_comp
            (productWedgeLeftInclusion X Y).right.hom
            (productWedgeLeftProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (productWedgeLeftInclusion X Y))
            (fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y))
            n)
      have hmap :
          (productWedgeLeftProjection X Y).right.hom.comp
              (productWedgeLeftInclusion X Y).right.hom =
            ContinuousMap.id X.right := by
        change ((productWedgeLeftInclusion X Y ≫ productWedgeLeftProjection X Y).right).hom =
          ((𝟙 X : X ⟶ X).right).hom
        exact congrArg (fun f ↦ f.right.hom)
          (productWedgeLeftProjection_comp_leftInclusion X Y)
      have hcongr :
          homotopyGroupMapOverEq
              ((productWedgeLeftProjection X Y).right.hom.comp
                (productWedgeLeftInclusion X Y).right.hom)
              hbase
              n =
            homotopyGroupMapOverEq (ContinuousMap.id X.right) rfl n := by
        -- Replace the composite with the identity using the axis-projection formula.
        exact homotopyGroupMapOverEq_congr hmap hbase rfl n
      exact
        (congrFun hcomp x).trans <|
          (congrFun hcongr x).trans <|
            by simpa using congrFun (homotopyGroupMapOverEq_id (underTopBasepoint X) n) x
    have hLeftRightComp :
        homotopyGroupMapOverEq
            (productWedgeLeftProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y))
            n
            (homotopyGroupMapOverEq
              (productWedgeRightInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (productWedgeRightInclusion X Y))
              n y) =
          1 := by
      -- Collapse the left projection after the right axis to the constant map on `Y`.
      have hbase :
          (productWedgeLeftProjection X Y).right.hom
              ((productWedgeRightInclusion X Y).right.hom (underTopBasepoint Y)) =
            underTopBasepoint X := by
        rw [fundamentalGroupFunctorMap_basepoint (productWedgeRightInclusion X Y)]
        exact fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y)
      have hcomp :
          (homotopyGroupMapOverEq
              (productWedgeLeftProjection X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y))
              n) ∘
            (homotopyGroupMapOverEq
              (productWedgeRightInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (productWedgeRightInclusion X Y))
              n) =
          homotopyGroupMapOverEq
            ((productWedgeLeftProjection X Y).right.hom.comp
              (productWedgeRightInclusion X Y).right.hom)
            hbase
            n := by
        simpa using
          (homotopyGroupMapOverEq_comp
            (productWedgeRightInclusion X Y).right.hom
            (productWedgeLeftProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (productWedgeRightInclusion X Y))
            (fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y))
            n)
      have hmap :
          (productWedgeLeftProjection X Y).right.hom.comp
              (productWedgeRightInclusion X Y).right.hom =
            ContinuousMap.const Y.right (underTopBasepoint X) := by
        change ((productWedgeRightInclusion X Y ≫ productWedgeLeftProjection X Y).right).hom =
          (constantBasedMap Y X).right.hom
        exact congrArg (fun f ↦ f.right.hom)
          (productWedgeLeftProjection_comp_rightInclusion X Y)
      have hcongr :
          homotopyGroupMapOverEq
              ((productWedgeLeftProjection X Y).right.hom.comp
                (productWedgeRightInclusion X Y).right.hom)
              hbase
              n =
            homotopyGroupMapOverEq
              (ContinuousMap.const Y.right (underTopBasepoint X))
              (a := underTopBasepoint Y)
              (b := underTopBasepoint X)
              rfl
              n := by
        -- Replace the composite with the constant map using the axis-projection formula.
        exact homotopyGroupMapOverEq_congr hmap hbase rfl n
      exact
        (congrFun hcomp y).trans <|
          (congrFun hcongr y).trans <|
            by
              simpa using
                (homotopyGroupMapOverEq_const_eq_one
                  (A := Y.right)
                  (underTopBasepoint X)
                  n
                  (underTopBasepoint Y)
                  y)
    rw [hLeftLeftComp, hLeftRightComp, mul_one]
  · -- The right projection kills the left axis contribution and recovers the right one.
    simp only [productWedgeHomotopyGroupToFactors, productWedgeHomotopyGroupFromFactors]
    rw [homotopyGroupMapOverEq_mul]
    have hRightLeftComp :
        homotopyGroupMapOverEq
            (productWedgeRightProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y))
            n
            (homotopyGroupMapOverEq
              (productWedgeLeftInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (productWedgeLeftInclusion X Y))
              n x) =
          1 := by
      -- Collapse the right projection after the left axis to the constant map on `X`.
      have hbase :
          (productWedgeRightProjection X Y).right.hom
              ((productWedgeLeftInclusion X Y).right.hom (underTopBasepoint X)) =
            underTopBasepoint Y := by
        rw [fundamentalGroupFunctorMap_basepoint (productWedgeLeftInclusion X Y)]
        exact fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y)
      have hcomp :
          (homotopyGroupMapOverEq
              (productWedgeRightProjection X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y))
              n) ∘
            (homotopyGroupMapOverEq
              (productWedgeLeftInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (productWedgeLeftInclusion X Y))
              n) =
          homotopyGroupMapOverEq
            ((productWedgeRightProjection X Y).right.hom.comp
              (productWedgeLeftInclusion X Y).right.hom)
            hbase
            n := by
        simpa using
          (homotopyGroupMapOverEq_comp
            (productWedgeLeftInclusion X Y).right.hom
            (productWedgeRightProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (productWedgeLeftInclusion X Y))
            (fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y))
            n)
      have hmap :
          (productWedgeRightProjection X Y).right.hom.comp
              (productWedgeLeftInclusion X Y).right.hom =
            ContinuousMap.const X.right (underTopBasepoint Y) := by
        change ((productWedgeLeftInclusion X Y ≫ productWedgeRightProjection X Y).right).hom =
          (constantBasedMap X Y).right.hom
        exact congrArg (fun f ↦ f.right.hom)
          (productWedgeRightProjection_comp_leftInclusion X Y)
      have hcongr :
          homotopyGroupMapOverEq
              ((productWedgeRightProjection X Y).right.hom.comp
                (productWedgeLeftInclusion X Y).right.hom)
              hbase
              n =
            homotopyGroupMapOverEq
              (ContinuousMap.const X.right (underTopBasepoint Y))
              (a := underTopBasepoint X)
              (b := underTopBasepoint Y)
              rfl
              n := by
        -- Replace the composite with the constant map using the axis-projection formula.
        exact homotopyGroupMapOverEq_congr hmap hbase rfl n
      exact
        (congrFun hcomp x).trans <|
          (congrFun hcongr x).trans <|
            by
              simpa using
                (homotopyGroupMapOverEq_const_eq_one
                  (A := X.right)
                  (underTopBasepoint Y)
                  n
                  (underTopBasepoint X)
                  x)
    have hRightRightComp :
        homotopyGroupMapOverEq
            (productWedgeRightProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y))
            n
            (homotopyGroupMapOverEq
              (productWedgeRightInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (productWedgeRightInclusion X Y))
              n y) =
          y := by
      -- Collapse the right projection after the right axis to the identity map on `Y`.
      have hbase :
          (productWedgeRightProjection X Y).right.hom
              ((productWedgeRightInclusion X Y).right.hom (underTopBasepoint Y)) =
            underTopBasepoint Y := by
        rw [fundamentalGroupFunctorMap_basepoint (productWedgeRightInclusion X Y)]
        exact fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y)
      have hcomp :
          (homotopyGroupMapOverEq
              (productWedgeRightProjection X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y))
              n) ∘
            (homotopyGroupMapOverEq
              (productWedgeRightInclusion X Y).right.hom
              (fundamentalGroupFunctorMap_basepoint (productWedgeRightInclusion X Y))
              n) =
          homotopyGroupMapOverEq
            ((productWedgeRightProjection X Y).right.hom.comp
              (productWedgeRightInclusion X Y).right.hom)
            hbase
            n := by
        simpa using
          (homotopyGroupMapOverEq_comp
            (productWedgeRightInclusion X Y).right.hom
            (productWedgeRightProjection X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (productWedgeRightInclusion X Y))
            (fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y))
            n)
      have hmap :
          (productWedgeRightProjection X Y).right.hom.comp
              (productWedgeRightInclusion X Y).right.hom =
            ContinuousMap.id Y.right := by
        change ((productWedgeRightInclusion X Y ≫ productWedgeRightProjection X Y).right).hom =
          ((𝟙 Y : Y ⟶ Y).right).hom
        exact congrArg (fun f ↦ f.right.hom)
          (productWedgeRightProjection_comp_rightInclusion X Y)
      have hcongr :
          homotopyGroupMapOverEq
              ((productWedgeRightProjection X Y).right.hom.comp
                (productWedgeRightInclusion X Y).right.hom)
              hbase
              n =
            homotopyGroupMapOverEq (ContinuousMap.id Y.right) rfl n := by
        -- Replace the composite with the identity using the axis-projection formula.
        exact homotopyGroupMapOverEq_congr hmap hbase rfl n
      exact
        (congrFun hcomp y).trans <|
          (congrFun hcongr y).trans <|
            by simpa using congrFun (homotopyGroupMapOverEq_id (underTopBasepoint Y) n) y
    rw [hRightLeftComp, hRightRightComp, one_mul]

/-- Helper for Problem 9.7.1: the product equivalence on positive homotopy groups preserves the
distinguished unit. -/
@[simp] theorem homotopyGroupProdEquiv_one
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (n : ℕ) (a : A) (b : B) :
    homotopyGroupProdEquiv (n := n + 1) (x := a) (y := b)
      (1 : π_ (n + 1) (A × B) (a, b)) =
        (1 : π_ (n + 1) A a × π_ (n + 1) B b) := by
  -- Rewrite both units as classes of constant generalized-loop representatives.
  rw [HomotopyGroup.one_def, homotopyGroupProdEquiv_apply]
  change
    ((⟦(GenLoop.const : Ω^ (Fin (n + 1)) A a)⟧ : π_ (n + 1) A a),
      (⟦(GenLoop.const : Ω^ (Fin (n + 1)) B b)⟧ : π_ (n + 1) B b)) =
      (1 : π_ (n + 1) A a × π_ (n + 1) B b)
  rfl

/-- Helper for Problem 9.7.1: the inverse product equivalence on positive homotopy groups also
preserves the distinguished unit. -/
@[simp] theorem homotopyGroupProdEquiv_symm_one
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (n : ℕ) (a : A) (b : B) :
    (homotopyGroupProdEquiv (n := n + 1) (x := a) (y := b)).symm
        (1 : π_ (n + 1) A a × π_ (n + 1) B b) =
      (1 : π_ (n + 1) (A × B) (a, b)) := by
  let e := homotopyGroupProdEquiv (n := n + 1) (x := a) (y := b)
  -- Apply the forward equivalence once; both sides reduce to the same product unit.
  apply e.injective
  simp [e]

/-- Helper for Problem 9.7.1: the ambient inclusion of a generalized loop in the native wedge
locus has the expected two coordinate loops in the ambient product. -/
theorem productWedgeAmbientCoordinateBridge
    (n : ℕ) (X Y : BasedSpace)
    (γ : Ω^ (Fin (n + 2)) (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y)) :
    genLoopProdEquiv (genLoopMap (pairSubspaceInclusion (productWedgeLocus X Y)) γ) =
      (genLoopMap (productWedgeLeftProjectionMap X Y) γ,
        genLoopMap (productWedgeRightProjectionMap X Y) γ) := by
  -- Both sides are obtained by projecting the same ambient generalized loop coordinatewise.
  apply Prod.ext <;> ext t <;> rfl

/-- Helper for Problem 9.7.1: the native factor map is the pair-LES subspace inclusion followed
by the product decomposition of ambient homotopy groups. -/
theorem productWedgeHomotopyGroupToFactors_eq_prodEquiv_comp_subspaceInclusion
    (n : ℕ) (X Y : BasedSpace) :
    productWedgeHomotopyGroupToFactors (n + 1) X Y =
      (homotopyGroupProdEquiv (n := n + 2)
          (x := underTopBasepoint X) (y := underTopBasepoint Y)) ∘
        pairSubspaceInclusionHomotopyGroupMap
          (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 2) := by
  funext z
  refine Quotient.inductionOn z ?_
  intro γ
  -- Unfold only the induced maps and then normalize the ambient representative coordinatewise.
  simp only [productWedgeHomotopyGroupToFactors, pairSubspaceInclusionHomotopyGroupMap]
  cases fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y)
  cases fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y)
  change
    ((⟦genLoopMap (productWedgeLeftProjectionMap X Y) γ⟧ :
        basedHomotopyGroup (n + 2) X),
      (⟦genLoopMap (productWedgeRightProjectionMap X Y) γ⟧ :
        basedHomotopyGroup (n + 2) Y)) =
      ((⟦(genLoopProdEquiv
          (genLoopMap (pairSubspaceInclusion (productWedgeLocus X Y)) γ)).1⟧ :
          basedHomotopyGroup (n + 2) X),
        (⟦(genLoopProdEquiv
          (genLoopMap (pairSubspaceInclusion (productWedgeLocus X Y)) γ)).2⟧ :
          basedHomotopyGroup (n + 2) Y))
  -- Apply the representative-level bridge before quotienting to the two coordinate classes.
  simpa using
    congrArg
      (fun p :
        Ω^ (Fin (n + 2)) X.right (underTopBasepoint X) ×
          Ω^ (Fin (n + 2)) Y.right (underTopBasepoint Y) ↦
          ((⟦p.1⟧ : basedHomotopyGroup (n + 2) X),
            (⟦p.2⟧ : basedHomotopyGroup (n + 2) Y)))
      (productWedgeAmbientCoordinateBridge n X Y γ).symm

/-- Helper for Problem 9.7.1: exactness of the pair boundary map against the native factor map is
obtained by transporting the pair long exact sequence through the product homotopy-group
equivalence. -/
theorem productWedgeBoundary_mulExact_toFactors
    (n : ℕ) (X Y : BasedSpace) :
    Function.MulExact
      (pairHomotopyBoundaryMap (productWedgeLocus X Y)
        (smashWedgeRelativeBasepoint X Y) (n + 1))
      (productWedgeHomotopyGroupToFactors (n + 1) X Y) := by
  let e :=
    homotopyGroupProdEquiv (n := n + 2)
      (x := underTopBasepoint X) (y := underTopBasepoint Y)
  have hExact :=
    pairHomotopyLongExactSequenceBoundaryToSubspace
      (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1)
  have hTransport :
      Function.MulExact
        (pairHomotopyBoundaryMap
          (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1))
        (e ∘ pairSubspaceInclusionHomotopyGroupMap
          (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 2)) := by
    -- Exactness survives postcomposition with the injective product decomposition equivalence.
    exact Function.MulExact.comp_injective
      (f := pairHomotopyBoundaryMap
        (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1))
      (g := pairSubspaceInclusionHomotopyGroupMap
        (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 2))
      (g' := e)
      hExact e.injective
      (homotopyGroupProdEquiv_one (n + 1) (underTopBasepoint X) (underTopBasepoint Y))
  simpa [e, productWedgeHomotopyGroupToFactors_eq_prodEquiv_comp_subspaceInclusion] using
    hTransport

/-- Helper for Problem 9.7.1: the native wedge locus inclusion into `X.right × Y.right` is
surjective on positive homotopy groups because the factor map already has an explicit section. -/
theorem productWedgeSubspaceInclusion_surjective
    (n : ℕ) (X Y : BasedSpace.{0}) :
    Function.Surjective
      (pairSubspaceInclusionHomotopyGroupMap
        (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 2)) := by
  intro g
  -- Route correction: keep the witness transport pointwise under the ambient product
  -- equivalence, so Lean only normalizes the inclusion map after one application of `e`.
  let e :=
    homotopyGroupProdEquiv (n := n + 2)
      (x := underTopBasepoint X) (y := underTopBasepoint Y)
  refine
    ⟨productWedgeHomotopyGroupFromFactors (n + 1) X Y (e g), ?_⟩
  -- Apply the ambient product equivalence once so the inclusion map matches the native factor
  -- map, where the explicit section theorem closes the coordinate computation.
  apply e.injective
  calc
    e
        (pairSubspaceInclusionHomotopyGroupMap
          (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 2)
          (productWedgeHomotopyGroupFromFactors (n + 1) X Y (e g))) =
      productWedgeHomotopyGroupToFactors (n + 1) X Y
        (productWedgeHomotopyGroupFromFactors (n + 1) X Y (e g)) := by
        simpa [e] using
          (congrFun
            (productWedgeHomotopyGroupToFactors_eq_prodEquiv_comp_subspaceInclusion
              n X Y)
            (productWedgeHomotopyGroupFromFactors (n + 1) X Y (e g))).symm
    _ = e g := by
      simpa using productWedgeHomotopyGroupToFactors_rightInverse (n + 1) X Y (e g)

/-- Helper for Problem 9.7.1: generalized-loop homotopies are exactly paths in the
generalized-loop space. -/
private theorem genLoopHomotopic_iff_joined
    {N : Type*} {Y : Type*} [TopologicalSpace Y] {y : Y} {p q : Ω^ N Y y} :
    GenLoop.Homotopic p q ↔ Joined p q := by
  constructor
  · rintro ⟨H⟩
    let curriedHomotopy := H.toHomotopy.curry
    -- Curry the relative homotopy into a path through the generalized-loop space.
    refine ⟨Path.mk
      ⟨fun t ↦
          (⟨curriedHomotopy t, fun a ha ↦ (H.prop t a ha).trans (p.property a ha)⟩ :
            Ω^ N Y y),
        Continuous.subtype_mk curriedHomotopy.continuous ?_⟩
      ?_ ?_⟩
    · intro t a ha
      exact (H.prop t a ha).trans (p.property a ha)
    · ext a
      exact H.apply_zero a
    · ext a
      exact H.apply_one a
  · rintro ⟨γ⟩
    -- Uncurry a path of generalized loops into a relative homotopy.
    refine ⟨⟨⟨
      (ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ γ.toContinuousMap).uncurry,
      ?_, ?_⟩, ?_⟩⟩
    · intro a
      change γ 0 a = p a
      exact congrArg (fun r : Ω^ N Y y ↦ r a) γ.source
    · intro a
      change γ 1 a = q a
      exact congrArg (fun r : Ω^ N Y y ↦ r a) γ.target
    · intro t a ha
      exact ((γ t).property a ha).trans (p.property a ha).symm

/-- Helper for Problem 9.7.1: a homeomorphism preserves and reflects the path relation `Joined`.
-/
private theorem joined_iff_homeomorph
    {Y : Type*} {Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (h : Y ≃ₜ Z) {a b : Y} :
    Joined (h a) (h b) ↔ Joined a b := by
  constructor
  · rintro ⟨γ⟩
    -- Pull the path back along the inverse homeomorphism.
    simpa using (show Joined (h.symm (h a)) (h.symm (h b)) from ⟨γ.map h.symm.continuous⟩)
  · rintro ⟨γ⟩
    -- Push the path forward along the homeomorphism.
    exact ⟨γ.map h.continuous⟩

/-- Helper for Problem 9.7.1: a generalized-loop homeomorphism preserves and reflects generalized
loop homotopies. -/
private theorem genLoopHomotopic_iff_of_homeomorph
    {M : Type*} {N : Type*} {Y : Type*} {Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] {y : Y} {z : Z}
    (h : Ω^ M Y y ≃ₜ Ω^ N Z z) {p q : Ω^ M Y y} :
    GenLoop.Homotopic (h p) (h q) ↔ GenLoop.Homotopic p q := by
  -- Translate homotopies to paths, use the homeomorphism, then translate back.
  rw [genLoopHomotopic_iff_joined, genLoopHomotopic_iff_joined, joined_iff_homeomorph h]

/-- Helper for Problem 9.7.1: `Fin 1`-indexed generalized loops identify with the ordinary loop
space. -/
private def oneGenLoopHomeomorph
    {Y : Type*} [TopologicalSpace Y] (y : Y) : Ω^ (Fin 1) Y y ≃ₜ Ω Y y where
  toFun p :=
    Path.mk ⟨fun t ↦ p (fun _ ↦ t), by fun_prop⟩
      (p.2 (fun _ ↦ 0) ⟨0, Or.inl rfl⟩)
      (p.2 (fun _ ↦ 1) ⟨0, Or.inr rfl⟩)
  invFun γ :=
    ⟨⟨fun t ↦ γ (t 0), by fun_prop⟩, fun t ht ↦ by
      rcases ht with ⟨i, hi | hi⟩
      · have hi0 : t 0 = 0 := by
          fin_cases i
          simpa using hi
        change γ (t 0) = y
        calc
          γ (t 0) = γ 0 := by simpa using congrArg γ hi0
          _ = y := γ.source
      · have hi1 : t 0 = 1 := by
          fin_cases i
          simpa using hi
        change γ (t 0) = y
        calc
          γ (t 0) = γ 1 := by simpa using congrArg γ hi1
          _ = y := γ.target⟩
  left_inv p := by
    -- Collapse the `Fin 1` cube to its unique coordinate.
    ext t
    have ht : t = fun _ : Fin 1 ↦ t 0 := by
      funext i
      fin_cases i
      rfl
    rw [ht]
    rfl
  right_inv γ := by
    -- The forward map simply evaluates the unique coordinate.
    ext t
    rfl
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_precomp
        ⟨fun t _ ↦ t, by fun_prop⟩).comp continuous_subtype_val
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_precomp
        ⟨fun t : I^(Fin 1) ↦ t 0, by fun_prop⟩).comp continuous_induced_dom

/-- Helper for Problem 9.7.1: the inverse of `oneGenLoopHomeomorph` sends the constant loop to the
constant generalized loop. -/
@[simp] private theorem oneGenLoopHomeomorph_symm_refl
    {Y : Type*} [TopologicalSpace Y] (y : Y) :
    (oneGenLoopHomeomorph y).symm (Path.refl y) = GenLoop.const := by
  -- Both loop representatives are constant at the chosen basepoint.
  ext t
  rfl

/-- Helper for Problem 9.7.1: a homeomorphism induces a homeomorphism on generalized-loop spaces.
-/
private def genLoopHomeomorph
    {M : Type*} {Y : Type*} {Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] (h : Y ≃ₜ Z) {y : Y} {z : Z} (hy : h y = z) :
    Ω^ M Y y ≃ₜ Ω^ M Z z where
  toFun p :=
    ⟨⟨fun t ↦ h (p t), h.continuous.comp p.1.continuous⟩, fun t ht ↦ by
      simpa [hy] using congrArg h (p.2 t ht)⟩
  invFun p :=
    ⟨⟨fun t ↦ h.symm (p t), (h.symm.continuous).comp p.1.continuous⟩, fun t ht ↦ by
      have hp : p t = z := p.2 t ht
      calc
        h.symm (p t) = h.symm z := by rw [hp]
        _ = y := (h.symm_apply_eq).2 hy.symm⟩
  left_inv p := by
    -- The inverse homeomorphism cancels pointwise.
    ext t
    simp
  right_inv p := by
    -- The same pointwise cancellation proves the reverse direction.
    ext t
    simp
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact (ContinuousMap.continuous_postcomp ⟨h, h.continuous⟩).comp continuous_subtype_val
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_postcomp ⟨h.symm, h.symm.continuous⟩).comp
        continuous_subtype_val

/-- Helper for Problem 9.7.1: iterated loops on a loop space identify with the next ordinary
iterated loop space. This is the shift bridge used to compare the pair-LES loop owners with the
direct positive-degree inclusion map. -/
private def loopSpaceRepresentativeHomeomorph
    {Y : Type*} [TopologicalSpace Y] (n : ℕ) (y : Y) :
    Ω^ (Fin n) (Ω Y y) (Path.refl y) ≃ₜ Ω^ (Fin (n + 1)) Y y :=
  let e₁ : Ω^ (Fin n) (Ω Y y) (Path.refl y) ≃ₜ Ω^ (Fin n) (Ω^ (Fin 1) Y y) GenLoop.const :=
    genLoopHomeomorph (oneGenLoopHomeomorph y).symm (oneGenLoopHomeomorph_symm_refl y)
  let e₂ : Ω^ (Fin n) (Ω^ (Fin 1) Y y) GenLoop.const ≃ₜ Ω^ (Fin n ⊕ Fin 1) Y y :=
    GenLoop.genLoopGenLoopEquiv y
  let e₃ : Ω^ (Fin n ⊕ Fin 1) Y y ≃ₜ Ω^ (Fin (n + 1)) Y y :=
    GenLoop.congr y (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
  (e₁.trans e₂).trans e₃

/-- Helper for Problem 9.7.1: the standard loop-space shift descends to an equivalence on
homotopy groups. -/
private def loopSpaceHomotopyGroupEquivPiSucc
    {Y : Type*} [TopologicalSpace Y] (n : ℕ) (y : Y) :
    π_ n (Ω Y y) (Path.refl y) ≃ π_ (n + 1) Y y :=
  Quotient.congr (loopSpaceRepresentativeHomeomorph n y) fun _ _ ↦
    (genLoopHomotopic_iff_of_homeomorph (loopSpaceRepresentativeHomeomorph n y)).symm

/-- Helper for Problem 9.7.1: the loop-space shift sends a class to the class of its shifted
representative. -/
@[simp] private theorem loopSpaceHomotopyGroupEquivPiSucc_apply
    {Y : Type*} [TopologicalSpace Y] (n : ℕ) (y : Y)
    (γ : Ω^ (Fin n) (Ω Y y) (Path.refl y)) :
    loopSpaceHomotopyGroupEquivPiSucc n y ⟦γ⟧ =
      (⟦loopSpaceRepresentativeHomeomorph n y γ⟧ : π_ (n + 1) Y y) :=
  rfl

/-- Helper for Problem 9.7.1: the representative-level loop-space shift commutes with the
subspace inclusion `A ↪ X`. -/
private theorem loopSpaceRepresentativeHomeomorph_subtypeInclusion
    {X : Type*} [TopologicalSpace X]
    (A : Set X) (x : A) (n : ℕ)
    (γ : Ω^ (Fin n) (Ω A x) (Path.refl x)) :
    loopSpaceRepresentativeHomeomorph n x.1
        (genLoopMap (pairLoopSubspaceInclusionMap A x) γ) =
      genLoopMap (pairSubspaceInclusion A)
        (loopSpaceRepresentativeHomeomorph n x γ) := by
  -- Each stage of the loop-space shift is defined pointwise, so it commutes with inclusion.
  ext t
  rfl

/-- Helper for Problem 9.7.1: after the standard loop-space shift, the pair-LES loop-owner map
agrees with the ordinary positive-degree inclusion-induced map. -/
private theorem pairLoopSubspaceInclusion_commutes_withPairSubspaceInclusionPiSucc
    {X : Type*} [TopologicalSpace X]
    (A : Set X) (x : A) (q : ℕ) :
    (loopSpaceHomotopyGroupEquivPiSucc (q + 1) x.1).toFun ∘
        pairLoopSubspaceInclusionHomotopyGroupMap A x q =
      pairSubspaceInclusionHomotopyGroupMap A x (q + 2) ∘
        (loopSpaceHomotopyGroupEquivPiSucc (q + 1) x).toFun := by
  -- Compare both induced maps on iterated-loop representatives before quotienting.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  simp [pairLoopSubspaceInclusionHomotopyGroupMap, pairSubspaceInclusionHomotopyGroupMap,
    loopSpaceRepresentativeHomeomorph_subtypeInclusion]

/-- Helper for Problem 9.7.1: surjectivity of the direct inclusion on `π_(n+3)` transfers to the
loop-owner map used by the native pair long exact sequence. -/
theorem productWedgeLoopSubspaceInclusion_surjective
    (n : ℕ) (X Y : BasedSpace.{0}) :
    Function.Surjective
      (pairLoopSubspaceInclusionHomotopyGroupMap
        (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1)) := by
  intro g
  let gAmbient :=
    (loopSpaceHomotopyGroupEquivPiSucc (n + 2) (smashWedgeRelativeBasepoint X Y).1) g
  rcases productWedgeSubspaceInclusion_surjective (n + 1) X Y gAmbient with ⟨a, ha⟩
  let aLoop :=
    (loopSpaceHomotopyGroupEquivPiSucc (n + 2) (smashWedgeRelativeBasepoint X Y)).symm a
  refine ⟨aLoop, ?_⟩
  -- Move the goal across the shift equivalence, where it is exactly the direct inclusion case.
  apply (loopSpaceHomotopyGroupEquivPiSucc (n + 2) (smashWedgeRelativeBasepoint X Y).1).injective
  calc
    (loopSpaceHomotopyGroupEquivPiSucc (n + 2) (smashWedgeRelativeBasepoint X Y).1)
        (pairLoopSubspaceInclusionHomotopyGroupMap
          (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1) aLoop) =
      pairSubspaceInclusionHomotopyGroupMap
        (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 3)
        ((loopSpaceHomotopyGroupEquivPiSucc (n + 2) (smashWedgeRelativeBasepoint X Y)) aLoop) := by
          simpa using
            congrFun
              (pairLoopSubspaceInclusion_commutes_withPairSubspaceInclusionPiSucc
                (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1))
              aLoop
    _ = pairSubspaceInclusionHomotopyGroupMap
          (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 3) a := by
            simp [aLoop]
    _ = gAmbient := ha
    _ = (loopSpaceHomotopyGroupEquivPiSucc (n + 2) (smashWedgeRelativeBasepoint X Y).1) g := rfl

/-- Helper for Problem 9.7.1: the pair boundary map bundled as a multiplicative homomorphism on
the native relative owner. This exposes the kernel computation needed for injectivity. -/
def pairHomotopyBoundaryMulHom
    {X : Type*} [TopologicalSpace X] (A : Set X) (x : A) (q : ℕ) :
    relativeHomotopyGroup (q + 1).succPNat A x →* π_ (q + 1) A x :=
  match (relativeHomotopyGroup_succ (q + 1) A x).symm with
  | rfl => homotopyGroupMapOverEqMulHom
      (pairRelativeEndpointMap A x) (pairRelativeEndpointMap_refl A x) q

/-- Helper for Problem 9.7.1: the bundled boundary homomorphism has the same underlying function
as the native boundary map from Theorem 9.2.2. -/
@[simp] theorem pairHomotopyBoundaryMulHom_apply
    {X : Type*} [TopologicalSpace X] (A : Set X) (x : A) (q : ℕ)
    (u : relativeHomotopyGroup (q + 1).succPNat A x) :
    pairHomotopyBoundaryMulHom A x q u = pairHomotopyBoundaryMap A x q u := by
  -- Unfold the relative-homotopy-group cast once; both sides reduce to the same induced map.
  cases (relativeHomotopyGroup_succ (q + 1) A x).symm
  rfl

/-- Helper for Problem 9.7.1: the native pair boundary map is injective because exactness lifts a
kernel element to the loop owner, and the previous surjectivity bridge forces that lift to come
from the subspace loop owner. -/
theorem productWedgeBoundary_injective
    (n : ℕ) (X Y : BasedSpace.{0}) :
    Function.Injective
      (pairHomotopyBoundaryMap
        (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1)) := by
  intro r s hrs
  let boundary :=
    pairHomotopyBoundaryMulHom
      (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1)
  have hrs' : boundary r = boundary s := by
    simpa using hrs
  have hkernel :
      pairHomotopyBoundaryMap
        (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1)
        (r * s⁻¹) = 1 := by
    -- Translate equality of boundary values into triviality of the boundary of the quotient.
    change boundary (r * s⁻¹) = 1
    rw [boundary.map_mul, boundary.map_inv, hrs', mul_inv_cancel]
  have hrange :
      r * s⁻¹ ∈ Set.range
        (pairLoopToRelativeHomotopyGroupMap
          (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1)) :=
    ((pairHomotopyLongExactSequenceAmbientToRelative
      (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1))
      (r * s⁻¹)).mp hkernel
  rcases hrange with ⟨a, ha⟩
  rcases productWedgeLoopSubspaceInclusion_surjective n X Y a with ⟨b, hb⟩
  have hambient :
      pairLoopToRelativeHomotopyGroupMap
        (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1) a = 1 := by
    -- Exactness of the first native clause kills the chosen ambient lift.
    exact
      ((pairHomotopyLongExactSequenceSubspaceToAmbient
        (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1)) a).mpr
        ⟨b, hb⟩
  have hquotient : r * s⁻¹ = 1 := by
    -- The kernel element equals the exact ambient lift, which the previous step shows is trivial.
    calc
      r * s⁻¹ =
        pairLoopToRelativeHomotopyGroupMap
          (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1) a := by
            simp [ha]
      _ = 1 := hambient
  -- Cancel the now-trivial quotient element to recover equality of the original relative classes.
  calc
    r = r * 1 := by simp
    _ = r * (s⁻¹ * s) := by rw [inv_mul_cancel]
    _ = (r * s⁻¹) * s := by simp [mul_assoc]
    _ = 1 * s := by rw [hquotient]
    _ = s := by simp

/-- Helper for Problem 9.7.1: the native wedge-locus owner already splits as the product of the
two factor homotopy groups and the relative boundary term. -/
theorem productWedgeHomotopyGroup_mulEquiv_prod_prod_relative_exists
    (n : ℕ) (X Y : BasedSpace.{0}) :
    Nonempty
      (basedHomotopyGroup (n + 2) (productWedgeBasedSpace X Y) ≃*
        ((basedHomotopyGroup (n + 2) X × basedHomotopyGroup (n + 2) Y) ×
          smashWedgeRelativeHomotopyGroup (n + 2) X Y)) := by
  -- Route correction: rebuild the split directly from the native exact pair by bundling the
  -- factor map, the explicit section, and the boundary map as homomorphisms.
  let leftProjHom :=
    homotopyGroupMapOverEqMulHom
      (productWedgeLeftProjection X Y).right.hom
      (fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y))
      (n + 1)
  let rightProjHom :=
    homotopyGroupMapOverEqMulHom
      (productWedgeRightProjection X Y).right.hom
      (fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y))
      (n + 1)
  let leftAxisHom :=
    homotopyGroupMapOverEqMulHom
      (productWedgeLeftInclusion X Y).right.hom
      (fundamentalGroupFunctorMap_basepoint (productWedgeLeftInclusion X Y))
      (n + 1)
  let rightAxisHom :=
    homotopyGroupMapOverEqMulHom
      (productWedgeRightInclusion X Y).right.hom
      (fundamentalGroupFunctorMap_basepoint (productWedgeRightInclusion X Y))
      (n + 1)
  let toFactorsHom :
      basedHomotopyGroup (n + 2) (productWedgeBasedSpace X Y) →*
        (basedHomotopyGroup (n + 2) X × basedHomotopyGroup (n + 2) Y) :=
    leftProjHom.prod rightProjHom
  let sectionHom :
      (basedHomotopyGroup (n + 2) X × basedHomotopyGroup (n + 2) Y) →*
        basedHomotopyGroup (n + 2) (productWedgeBasedSpace X Y) :=
    { toFun := fun z ↦ leftAxisHom z.1 * rightAxisHom z.2
      map_one' := by
        -- The section sends the trivial pair to the trivial ambient class.
        change leftAxisHom 1 * rightAxisHom 1 = 1
        rw [map_one, map_one, mul_one]
      map_mul' := by
        -- Multiplicativity is coordinatewise, and the ambient homotopy group is commutative in
        -- degree `n + 2`.
        intro z w
        rcases z with ⟨zx, zy⟩
        rcases w with ⟨wx, wy⟩
        change leftAxisHom (zx * wx) * rightAxisHom (zy * wy) = _
        rw [map_mul, map_mul]
        ac_rfl }
  let boundaryHom :
      smashWedgeRelativeHomotopyGroup (n + 2) X Y →*
        basedHomotopyGroup (n + 2) (productWedgeBasedSpace X Y) :=
    pairHomotopyBoundaryMulHom
      (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1)
  have hsection : Function.RightInverse sectionHom toFactorsHom := by
    intro z
    rcases z with ⟨x, y⟩
    -- The explicit native section recovers the two product coordinates.
    change
      productWedgeHomotopyGroupToFactors (n + 1) X Y
        (productWedgeHomotopyGroupFromFactors (n + 1) X Y (x, y)) = (x, y)
    exact productWedgeHomotopyGroupToFactors_rightInverse (n + 1) X Y (x, y)
  have hboundary :
      ∀ r, toFactorsHom (boundaryHom r) = 1 := by
    intro r
    -- Exactness forces every boundary class into the kernel of the factor map.
    change
      productWedgeHomotopyGroupToFactors (n + 1) X Y
        (pairHomotopyBoundaryMap (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y)
          (n + 1) r) = 1
    simpa [toFactorsHom, leftProjHom, rightProjHom] using
      Function.MulExact.apply_apply_eq_one (productWedgeBoundary_mulExact_toFactors n X Y) r
  have hcorrection :
      ∀ g : basedHomotopyGroup (n + 2) (productWedgeBasedSpace X Y),
        ∃ r : smashWedgeRelativeHomotopyGroup (n + 2) X Y,
          boundaryHom r = g * (sectionHom (toFactorsHom g))⁻¹ := by
    intro g
    have hk :
        productWedgeHomotopyGroupToFactors (n + 1) X Y
          (g * (sectionHom (toFactorsHom g))⁻¹) = 1 := by
      -- The correction term lands in the kernel because the section already matches the factor
      -- coordinate of `g`.
      change toFactorsHom (g * (sectionHom (toFactorsHom g))⁻¹) = 1
      rw [toFactorsHom.map_mul, map_inv, hsection (toFactorsHom g), mul_inv_cancel]
    rcases
        (productWedgeBoundary_mulExact_toFactors n X Y
          (g * (sectionHom (toFactorsHom g))⁻¹)).mp hk with
      ⟨r, hr⟩
    refine ⟨r, ?_⟩
    -- Re-express the exactness witness using the bundled boundary hom.
    simpa [boundaryHom, pairHomotopyBoundaryMulHom_apply] using hr
  let reconstruct :
      ((basedHomotopyGroup (n + 2) X × basedHomotopyGroup (n + 2) Y) ×
        smashWedgeRelativeHomotopyGroup (n + 2) X Y) →*
      basedHomotopyGroup (n + 2) (productWedgeBasedSpace X Y) :=
    { toFun := fun u ↦ boundaryHom u.2 * sectionHom u.1
      map_one' := by
        -- Both the boundary term and the section term preserve the identity.
        change boundaryHom 1 * sectionHom 1 = 1
        rw [map_one, map_one, mul_one]
      map_mul' := by
        -- Commutativity in the ambient group lets the boundary and section pieces regroup.
        intro u v
        rcases u with ⟨zu, ru⟩
        rcases v with ⟨zv, rv⟩
        change boundaryHom (ru * rv) * sectionHom (zu * zv) = _
        rw [map_mul, map_mul]
        ac_rfl }
  refine ⟨(MulEquiv.ofBijective reconstruct ?_).symm⟩
  constructor
  · intro u v huv
    rcases u with ⟨zu, ru⟩
    rcases v with ⟨zv, rv⟩
    -- Applying the factor map recovers the product coordinate.
    have hz : zu = zv := by
      have hmap := congrArg toFactorsHom huv
      have hzu : toFactorsHom (reconstruct (zu, ru)) = zu := by
        change toFactorsHom (boundaryHom ru * sectionHom zu) = zu
        rw [toFactorsHom.map_mul, hboundary, hsection, one_mul]
      have hzv : toFactorsHom (reconstruct (zv, rv)) = zv := by
        change toFactorsHom (boundaryHom rv * sectionHom zv) = zv
        rw [toFactorsHom.map_mul, hboundary, hsection, one_mul]
      calc
        zu = toFactorsHom (reconstruct (zu, ru)) := hzu.symm
        _ = toFactorsHom (reconstruct (zv, rv)) := hmap
        _ = zv := hzv
    subst hz
    -- With the section terms aligned, cancel them and use injectivity of the boundary map.
    have hboundaryEq : boundaryHom ru = boundaryHom rv := by
      exact mul_right_cancel (by simpa [reconstruct] using huv)
    have hr : ru = rv := productWedgeBoundary_injective n X Y hboundaryEq
    exact Prod.ext rfl hr
  · intro g
    rcases hcorrection g with ⟨r, hr⟩
    -- The correction term and the section together reconstruct the original ambient class.
    refine ⟨(toFactorsHom g, r), ?_⟩
    change boundaryHom r * sectionHom (toFactorsHom g) = g
    rw [hr]
    rw [mul_assoc, inv_mul_cancel, mul_one]

/-- Helper for Problem 9.7.1: the canonical comparison map on `π_ (n + 2)` induced by
`binaryWedgeToProductWedge X Y`. -/
def binaryWedgeToProductWedgeHomotopyGroupHom
    (n : ℕ) (X Y : BasedSpace) :
    basedHomotopyGroup (n + 2) (binaryWedge X Y) →*
      basedHomotopyGroup (n + 2) (productWedgeBasedSpace X Y) :=
  homotopyGroupMapOverEqMulHom
    (binaryWedgeToProductWedge X Y).right.hom
    (fundamentalGroupFunctorMap_basepoint (binaryWedgeToProductWedge X Y))
    (n + 1)

/-- Helper for Problem 9.7.1: the canonical comparison map on `π_ (n + 2)` induced by
`productWedgeToBinaryWedge X Y`. -/
def productWedgeToBinaryWedgeHomotopyGroupHom
    (n : ℕ) (X Y : BasedSpace) :
    basedHomotopyGroup (n + 2) (productWedgeBasedSpace X Y) →*
      basedHomotopyGroup (n + 2) (binaryWedge X Y) :=
  homotopyGroupMapOverEqMulHom
    (productWedgeToBinaryWedge X Y).right.hom
    (fundamentalGroupFunctorMap_basepoint (productWedgeToBinaryWedge X Y))
    (n + 1)

/-- Helper for Problem 9.7.1: the induced native-to-binary map is a left inverse to the induced
binary-to-native map on positive homotopy groups. -/
theorem productWedgeToBinaryWedgeHomotopyGroupHom_comp_binaryWedgeToProductWedgeHomotopyGroupHom
    (n : ℕ) (X Y : BasedSpace) :
    (productWedgeToBinaryWedgeHomotopyGroupHom n X Y).comp
        (binaryWedgeToProductWedgeHomotopyGroupHom n X Y) =
      MonoidHom.id (basedHomotopyGroup (n + 2) (binaryWedge X Y)) := by
  -- Descend the space-level left inverse through `homotopyGroupMapOverEq_comp`.
  ext z
  let f := (binaryWedgeToProductWedge X Y).right.hom
  let g := (productWedgeToBinaryWedge X Y).right.hom
  have hbase :
      g (f (underTopBasepoint (binaryWedge X Y))) =
        underTopBasepoint (binaryWedge X Y) := by
    rw [fundamentalGroupFunctorMap_basepoint (binaryWedgeToProductWedge X Y)]
    exact fundamentalGroupFunctorMap_basepoint (productWedgeToBinaryWedge X Y)
  have hcomp :
      productWedgeToBinaryWedgeHomotopyGroupHom n X Y
          (binaryWedgeToProductWedgeHomotopyGroupHom n X Y z) =
        homotopyGroupMapOverEq (g.comp f) hbase (n + 1) z := by
    simpa [f, g, productWedgeToBinaryWedgeHomotopyGroupHom,
      binaryWedgeToProductWedgeHomotopyGroupHom] using
      congrFun
        (homotopyGroupMapOverEq_comp
          f
          g
          (fundamentalGroupFunctorMap_basepoint (binaryWedgeToProductWedge X Y))
          (fundamentalGroupFunctorMap_basepoint (productWedgeToBinaryWedge X Y))
          (n + 1))
        z
  have hmap :
      g.comp f = ContinuousMap.id (binaryWedge X Y).right := by
    change ((binaryWedgeToProductWedge X Y ≫ productWedgeToBinaryWedge X Y).right).hom =
      ContinuousMap.id (binaryWedge X Y).right
    exact congrArg (fun f ↦ f.right.hom)
      (binaryWedgeToProductWedge_comp_productWedgeToBinaryWedge X Y)
  have hcongr :
      homotopyGroupMapOverEq (g.comp f) hbase (n + 1) =
        homotopyGroupMapOverEq (ContinuousMap.id (binaryWedge X Y).right) rfl (n + 1) := by
    -- Replace the composite by the identity using the space-level inverse identity.
    exact homotopyGroupMapOverEq_congr hmap hbase rfl (n + 1)
  exact
    hcomp.trans <|
      (congrFun hcongr z).trans <|
        by
          simpa using
            congrFun (homotopyGroupMapOverEq_id (underTopBasepoint (binaryWedge X Y))
              (n + 1)) z

/-- Helper for Problem 9.7.1: the induced binary-to-native map is a left inverse to the induced
native-to-binary map on positive homotopy groups. -/
theorem binaryWedgeToProductWedgeHomotopyGroupHom_comp_productWedgeToBinaryWedgeHomotopyGroupHom
    (n : ℕ) (X Y : BasedSpace) :
    (binaryWedgeToProductWedgeHomotopyGroupHom n X Y).comp
        (productWedgeToBinaryWedgeHomotopyGroupHom n X Y) =
      MonoidHom.id (basedHomotopyGroup (n + 2) (productWedgeBasedSpace X Y)) := by
  -- Descend the space-level right inverse through `homotopyGroupMapOverEq_comp`.
  ext z
  let f := (productWedgeToBinaryWedge X Y).right.hom
  let g := (binaryWedgeToProductWedge X Y).right.hom
  have hbase :
      g (f (underTopBasepoint (productWedgeBasedSpace X Y))) =
        underTopBasepoint (productWedgeBasedSpace X Y) := by
    rw [fundamentalGroupFunctorMap_basepoint (productWedgeToBinaryWedge X Y)]
    exact fundamentalGroupFunctorMap_basepoint (binaryWedgeToProductWedge X Y)
  have hcomp :
      binaryWedgeToProductWedgeHomotopyGroupHom n X Y
          (productWedgeToBinaryWedgeHomotopyGroupHom n X Y z) =
        homotopyGroupMapOverEq (g.comp f) hbase (n + 1) z := by
    simpa [f, g, productWedgeToBinaryWedgeHomotopyGroupHom,
      binaryWedgeToProductWedgeHomotopyGroupHom] using
      congrFun
        (homotopyGroupMapOverEq_comp
          f
          g
          (fundamentalGroupFunctorMap_basepoint (productWedgeToBinaryWedge X Y))
          (fundamentalGroupFunctorMap_basepoint (binaryWedgeToProductWedge X Y))
          (n + 1))
        z
  have hmap :
      g.comp f = ContinuousMap.id (productWedgeBasedSpace X Y).right := by
    change ((productWedgeToBinaryWedge X Y ≫ binaryWedgeToProductWedge X Y).right).hom =
      ContinuousMap.id (productWedgeBasedSpace X Y).right
    exact congrArg (fun f ↦ f.right.hom)
      (productWedgeToBinaryWedge_comp_binaryWedgeToProductWedge X Y)
  have hcongr :
      homotopyGroupMapOverEq (g.comp f) hbase (n + 1) =
        homotopyGroupMapOverEq (ContinuousMap.id (productWedgeBasedSpace X Y).right) rfl
          (n + 1) := by
    -- Replace the composite by the identity using the space-level inverse identity.
    exact homotopyGroupMapOverEq_congr hmap hbase rfl (n + 1)
  exact
    hcomp.trans <|
      (congrFun hcongr z).trans <|
        by
          simpa using
            congrFun
              (homotopyGroupMapOverEq_id (underTopBasepoint (productWedgeBasedSpace X Y))
                (n + 1))
              z

/-- Helper for Problem 9.7.1: the induced binary-to-native comparison map is bijective in
positive degree because the two wedge models are inverse up to based maps. -/
theorem binaryWedgeToProductWedgeHomotopyGroupHom_bijective
    (n : ℕ) (X Y : BasedSpace) :
    Function.Bijective (binaryWedgeToProductWedgeHomotopyGroupHom n X Y) := by
  constructor
  · intro z w hzw
    have hleftEq := congrArg (productWedgeToBinaryWedgeHomotopyGroupHom n X Y) hzw
    have hz :
        productWedgeToBinaryWedgeHomotopyGroupHom n X Y
            (binaryWedgeToProductWedgeHomotopyGroupHom n X Y z) = z := by
      simpa using
        congrArg
          (fun m :
            basedHomotopyGroup (n + 2) (binaryWedge X Y) →*
              basedHomotopyGroup (n + 2) (binaryWedge X Y) ↦
            m z)
          (productWedgeToBinaryWedgeHomotopyGroupHom_comp_binaryWedgeToProductWedgeHomotopyGroupHom
            n X Y)
    have hw :
        productWedgeToBinaryWedgeHomotopyGroupHom n X Y
            (binaryWedgeToProductWedgeHomotopyGroupHom n X Y w) = w := by
      simpa using
        congrArg
          (fun m :
            basedHomotopyGroup (n + 2) (binaryWedge X Y) →*
              basedHomotopyGroup (n + 2) (binaryWedge X Y) ↦
            m w)
          (productWedgeToBinaryWedgeHomotopyGroupHom_comp_binaryWedgeToProductWedgeHomotopyGroupHom
            n X Y)
    exact hz.symm.trans (hleftEq.trans hw)
  · intro g
    refine ⟨productWedgeToBinaryWedgeHomotopyGroupHom n X Y g, ?_⟩
    simpa using
      congrArg
        (fun m :
          basedHomotopyGroup (n + 2) (productWedgeBasedSpace X Y) →*
            basedHomotopyGroup (n + 2) (productWedgeBasedSpace X Y) ↦
          m g)
        (binaryWedgeToProductWedgeHomotopyGroupHom_comp_productWedgeToBinaryWedgeHomotopyGroupHom
          n X Y)

/-- Helper for Problem 9.7.1: after the wedge-model comparison, the left projection on
`productWedgeBasedSpace X Y` induces the same positive-degree map as the left coproduct
projection on `binaryWedge X Y`. -/
theorem binaryWedgeToProductWedgeHomotopyGroupHom_comp_leftProjection
    (n : ℕ) (X Y : BasedSpace) :
    (homotopyGroupMapOverEqMulHom
        (productWedgeLeftProjection X Y).right.hom
        (fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y))
        (n + 1)).comp
      (binaryWedgeToProductWedgeHomotopyGroupHom n X Y) =
    homotopyGroupMapOverEqMulHom
      (binaryWedgeLeftProjection X Y).right.hom
      (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftProjection X Y))
      (n + 1) := by
  ext z
  -- First collapse the two induced maps to the induced map of the composite comparison.
  have hbase :
      (productWedgeLeftProjection X Y).right.hom
          ((binaryWedgeToProductWedge X Y).right.hom
            (underTopBasepoint (binaryWedge X Y))) =
        underTopBasepoint X := by
    rw [fundamentalGroupFunctorMap_basepoint (binaryWedgeToProductWedge X Y)]
    exact fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y)
  have hcomp :
      homotopyGroupMapOverEq
          (productWedgeLeftProjection X Y).right.hom
          (fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y))
          (n + 1)
          (binaryWedgeToProductWedgeHomotopyGroupHom n X Y z) =
        homotopyGroupMapOverEq
          ((productWedgeLeftProjection X Y).right.hom.comp
            (binaryWedgeToProductWedge X Y).right.hom)
          hbase
          (n + 1)
          z := by
    simpa [binaryWedgeToProductWedgeHomotopyGroupHom] using
      congrFun
        (homotopyGroupMapOverEq_comp
          (binaryWedgeToProductWedge X Y).right.hom
          (productWedgeLeftProjection X Y).right.hom
          (fundamentalGroupFunctorMap_basepoint (binaryWedgeToProductWedge X Y))
          (fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y))
          (n + 1))
        z
  have hmap :
      (productWedgeLeftProjection X Y).right.hom.comp
          (binaryWedgeToProductWedge X Y).right.hom =
        (binaryWedgeLeftProjection X Y).right.hom := by
    change ((binaryWedgeToProductWedge X Y ≫ productWedgeLeftProjection X Y).right).hom =
      (binaryWedgeLeftProjection X Y).right.hom
    exact congrArg (fun f ↦ f.right.hom)
      (binaryWedgeToProductWedge_comp_leftProjection X Y)
  have hcongr :
      homotopyGroupMapOverEq
          ((productWedgeLeftProjection X Y).right.hom.comp
            (binaryWedgeToProductWedge X Y).right.hom)
          hbase
          (n + 1) =
        homotopyGroupMapOverEq
          (binaryWedgeLeftProjection X Y).right.hom
          (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftProjection X Y))
          (n + 1) := by
    -- Replace the composite comparison by the already normalized left wedge projection.
    exact
      homotopyGroupMapOverEq_congr
        hmap
        hbase
        (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftProjection X Y))
        (n + 1)
  exact hcomp.trans (congrFun hcongr z)

/-- Helper for Problem 9.7.1: after the wedge-model comparison, the right projection on
`productWedgeBasedSpace X Y` induces the same positive-degree map as the right coproduct
projection on `binaryWedge X Y`. -/
theorem binaryWedgeToProductWedgeHomotopyGroupHom_comp_rightProjection
    (n : ℕ) (X Y : BasedSpace) :
    (homotopyGroupMapOverEqMulHom
        (productWedgeRightProjection X Y).right.hom
        (fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y))
        (n + 1)).comp
      (binaryWedgeToProductWedgeHomotopyGroupHom n X Y) =
    homotopyGroupMapOverEqMulHom
      (binaryWedgeRightProjection X Y).right.hom
      (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightProjection X Y))
      (n + 1) := by
  ext z
  -- First collapse the two induced maps to the induced map of the composite comparison.
  have hbase :
      (productWedgeRightProjection X Y).right.hom
          ((binaryWedgeToProductWedge X Y).right.hom
            (underTopBasepoint (binaryWedge X Y))) =
        underTopBasepoint Y := by
    rw [fundamentalGroupFunctorMap_basepoint (binaryWedgeToProductWedge X Y)]
    exact fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y)
  have hcomp :
      homotopyGroupMapOverEq
          (productWedgeRightProjection X Y).right.hom
          (fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y))
          (n + 1)
          (binaryWedgeToProductWedgeHomotopyGroupHom n X Y z) =
        homotopyGroupMapOverEq
          ((productWedgeRightProjection X Y).right.hom.comp
            (binaryWedgeToProductWedge X Y).right.hom)
          hbase
          (n + 1)
          z := by
    simpa [binaryWedgeToProductWedgeHomotopyGroupHom] using
      congrFun
        (homotopyGroupMapOverEq_comp
          (binaryWedgeToProductWedge X Y).right.hom
          (productWedgeRightProjection X Y).right.hom
          (fundamentalGroupFunctorMap_basepoint (binaryWedgeToProductWedge X Y))
          (fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y))
          (n + 1))
        z
  have hmap :
      (productWedgeRightProjection X Y).right.hom.comp
          (binaryWedgeToProductWedge X Y).right.hom =
        (binaryWedgeRightProjection X Y).right.hom := by
    change ((binaryWedgeToProductWedge X Y ≫ productWedgeRightProjection X Y).right).hom =
      (binaryWedgeRightProjection X Y).right.hom
    exact congrArg (fun f ↦ f.right.hom)
      (binaryWedgeToProductWedge_comp_rightProjection X Y)
  have hcongr :
      homotopyGroupMapOverEq
          ((productWedgeRightProjection X Y).right.hom.comp
            (binaryWedgeToProductWedge X Y).right.hom)
          hbase
          (n + 1) =
        homotopyGroupMapOverEq
          (binaryWedgeRightProjection X Y).right.hom
          (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightProjection X Y))
          (n + 1) := by
    -- Replace the composite comparison by the already normalized right wedge projection.
    exact
      homotopyGroupMapOverEq_congr
        hmap
        hbase
        (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightProjection X Y))
        (n + 1)
  exact hcomp.trans (congrFun hcongr z)

/-- Helper for Problem 9.7.1: the comparison map to the native wedge model preserves the factor
coordinates detected by the two wedge projections. -/
theorem productWedgeHomotopyGroupToFactors_comp_binaryWedgeToProductWedgeHomotopyGroupHom
    (n : ℕ) (X Y : BasedSpace) (z : basedHomotopyGroup (n + 2) (binaryWedge X Y)) :
    productWedgeHomotopyGroupToFactors (n + 1) X Y
      (binaryWedgeToProductWedgeHomotopyGroupHom n X Y z) =
    binaryWedgeHomotopyGroupToFactors (n + 1) X Y z := by
  -- Compare the two coordinates separately using the projection-compatibility lemmas.
  apply Prod.ext
  · simpa [productWedgeHomotopyGroupToFactors, binaryWedgeHomotopyGroupToFactors] using
      congrArg
        (fun m :
          basedHomotopyGroup (n + 2) (binaryWedge X Y) →*
            basedHomotopyGroup (n + 2) X ↦
          m z)
        (binaryWedgeToProductWedgeHomotopyGroupHom_comp_leftProjection n X Y)
  · simpa [productWedgeHomotopyGroupToFactors, binaryWedgeHomotopyGroupToFactors] using
      congrArg
        (fun m :
          basedHomotopyGroup (n + 2) (binaryWedge X Y) →*
            basedHomotopyGroup (n + 2) Y ↦
          m z)
        (binaryWedgeToProductWedgeHomotopyGroupHom_comp_rightProjection n X Y)

/-- Helper for Problem 9.7.1: the comparison map sends the standard section from the factor groups
for `binaryWedge X Y` to the corresponding section for `productWedgeBasedSpace X Y`. -/
theorem binaryWedgeToProductWedgeHomotopyGroupHom_fromFactors
    (n : ℕ) (X Y : BasedSpace)
    (z : basedHomotopyGroup (n + 2) X × basedHomotopyGroup (n + 2) Y) :
    binaryWedgeToProductWedgeHomotopyGroupHom n X Y
      (binaryWedgeHomotopyGroupFromFactors (n + 1) X Y z) =
    productWedgeHomotopyGroupFromFactors (n + 1) X Y z := by
  rcases z with ⟨x, y⟩
  -- Push the comparison through the multiplicative section and normalize each inclusion branch.
  rw [binaryWedgeHomotopyGroupFromFactors, productWedgeHomotopyGroupFromFactors, map_mul]
  have hleftBase :
      (binaryWedgeToProductWedge X Y).right.hom
          ((binaryWedgeLeftInclusion X Y).right.hom (underTopBasepoint X)) =
        underTopBasepoint (productWedgeBasedSpace X Y) := by
    rw [fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftInclusion X Y)]
    exact fundamentalGroupFunctorMap_basepoint (binaryWedgeToProductWedge X Y)
  have hleftComp :
      binaryWedgeToProductWedgeHomotopyGroupHom n X Y
          (homotopyGroupMapOverEq
            (binaryWedgeLeftInclusion X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftInclusion X Y))
            (n + 1)
            x) =
        homotopyGroupMapOverEq
          ((binaryWedgeToProductWedge X Y).right.hom.comp
            (binaryWedgeLeftInclusion X Y).right.hom)
          hleftBase
          (n + 1)
          x := by
    simpa [binaryWedgeToProductWedgeHomotopyGroupHom] using
      congrFun
        (homotopyGroupMapOverEq_comp
          (binaryWedgeLeftInclusion X Y).right.hom
          (binaryWedgeToProductWedge X Y).right.hom
          (fundamentalGroupFunctorMap_basepoint (binaryWedgeLeftInclusion X Y))
          (fundamentalGroupFunctorMap_basepoint (binaryWedgeToProductWedge X Y))
          (n + 1))
        x
  have hleftMap :
      (binaryWedgeToProductWedge X Y).right.hom.comp
          (binaryWedgeLeftInclusion X Y).right.hom =
        (productWedgeLeftInclusion X Y).right.hom := by
    change ((binaryWedgeLeftInclusion X Y ≫ binaryWedgeToProductWedge X Y).right).hom =
      (productWedgeLeftInclusion X Y).right.hom
    exact congrArg (fun f ↦ f.right.hom)
      (binaryWedgeToProductWedge_comp_leftInclusion X Y)
  have hleftConcr :
      homotopyGroupMapOverEq
          ((binaryWedgeToProductWedge X Y).right.hom.comp
            (binaryWedgeLeftInclusion X Y).right.hom)
          hleftBase
          (n + 1) =
        homotopyGroupMapOverEq
          (productWedgeLeftInclusion X Y).right.hom
          (fundamentalGroupFunctorMap_basepoint (productWedgeLeftInclusion X Y))
          (n + 1) := by
    -- Replace the left composite by the native left-axis inclusion.
    exact
      homotopyGroupMapOverEq_congr
        hleftMap
        hleftBase
        (fundamentalGroupFunctorMap_basepoint (productWedgeLeftInclusion X Y))
        (n + 1)
  have hrightBase :
      (binaryWedgeToProductWedge X Y).right.hom
          ((binaryWedgeRightInclusion X Y).right.hom (underTopBasepoint Y)) =
        underTopBasepoint (productWedgeBasedSpace X Y) := by
    rw [fundamentalGroupFunctorMap_basepoint (binaryWedgeRightInclusion X Y)]
    exact fundamentalGroupFunctorMap_basepoint (binaryWedgeToProductWedge X Y)
  have hrightComp :
      binaryWedgeToProductWedgeHomotopyGroupHom n X Y
          (homotopyGroupMapOverEq
            (binaryWedgeRightInclusion X Y).right.hom
            (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightInclusion X Y))
            (n + 1)
            y) =
        homotopyGroupMapOverEq
          ((binaryWedgeToProductWedge X Y).right.hom.comp
            (binaryWedgeRightInclusion X Y).right.hom)
          hrightBase
          (n + 1)
          y := by
    simpa [binaryWedgeToProductWedgeHomotopyGroupHom] using
      congrFun
        (homotopyGroupMapOverEq_comp
          (binaryWedgeRightInclusion X Y).right.hom
          (binaryWedgeToProductWedge X Y).right.hom
          (fundamentalGroupFunctorMap_basepoint (binaryWedgeRightInclusion X Y))
          (fundamentalGroupFunctorMap_basepoint (binaryWedgeToProductWedge X Y))
          (n + 1))
        y
  have hrightMap :
      (binaryWedgeToProductWedge X Y).right.hom.comp
          (binaryWedgeRightInclusion X Y).right.hom =
        (productWedgeRightInclusion X Y).right.hom := by
    change ((binaryWedgeRightInclusion X Y ≫ binaryWedgeToProductWedge X Y).right).hom =
      (productWedgeRightInclusion X Y).right.hom
    exact congrArg (fun f ↦ f.right.hom)
      (binaryWedgeToProductWedge_comp_rightInclusion X Y)
  have hrightConcr :
      homotopyGroupMapOverEq
          ((binaryWedgeToProductWedge X Y).right.hom.comp
            (binaryWedgeRightInclusion X Y).right.hom)
          hrightBase
          (n + 1) =
        homotopyGroupMapOverEq
          (productWedgeRightInclusion X Y).right.hom
          (fundamentalGroupFunctorMap_basepoint (productWedgeRightInclusion X Y))
          (n + 1) := by
    -- Replace the right composite by the native right-axis inclusion.
    exact
      homotopyGroupMapOverEq_congr
        hrightMap
        hrightBase
        (fundamentalGroupFunctorMap_basepoint (productWedgeRightInclusion X Y))
        (n + 1)
  rw [hleftComp, congrFun hleftConcr x, hrightComp, congrFun hrightConcr y]

/-- Helper for Problem 9.7.1: the wedge quotient carries a canonical ambient-product homotopy
class by applying the binary factor map and then using the product equivalence. -/
def binaryWedgeAmbientHomotopyGroupMap
    (n : ℕ) (X Y : BasedSpace) :
    basedHomotopyGroup (n + 2) (binaryWedge X Y) →
      π_ (n + 2) (smashProductPair X Y) (smashProductBasepointPair X Y) :=
  let e :=
    homotopyGroupProdEquiv (n := n + 2)
      (x := underTopBasepoint X) (y := underTopBasepoint Y)
  e.symm ∘ binaryWedgeHomotopyGroupToFactors (n + 1) X Y

/-- Helper for Problem 9.7.1: the ambient product comparison for `binaryWedge X Y` is already
surjective because the binary factor map has an explicit section. -/
theorem binaryWedgeAmbientHomotopyGroupMap_surjective
    (n : ℕ) (X Y : BasedSpace) :
    Function.Surjective (binaryWedgeAmbientHomotopyGroupMap n X Y) := by
  let e :=
    homotopyGroupProdEquiv (n := n + 2)
      (x := underTopBasepoint X) (y := underTopBasepoint Y)
  intro g
  refine ⟨binaryWedgeHomotopyGroupFromFactors (n + 1) X Y (e g), ?_⟩
  -- Move the witness through the product equivalence, where the binary section theorem closes the
  -- factor computation directly.
  change e.symm
      (binaryWedgeHomotopyGroupToFactors (n + 1) X Y
        (binaryWedgeHomotopyGroupFromFactors (n + 1) X Y (e g))) = g
  rw [binaryWedgeHomotopyGroupToFactors_rightInverse (n + 1) X Y (e g)]
  exact e.left_inv g

/-- Helper for Problem 9.7.1: after passing to ambient-product homotopy groups, the comparison
map `binaryWedgeToProductWedge` agrees with the native subspace inclusion. -/
theorem binaryWedgeAmbientHomotopyGroupMap_eq_subspaceInclusion_comp
    (n : ℕ) (X Y : BasedSpace) :
    binaryWedgeAmbientHomotopyGroupMap n X Y =
      pairSubspaceInclusionHomotopyGroupMap
        (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 2) ∘
          binaryWedgeToProductWedgeHomotopyGroupHom n X Y := by
  let e :=
    homotopyGroupProdEquiv (n := n + 2)
      (x := underTopBasepoint X) (y := underTopBasepoint Y)
  funext z
  -- Compare the two ambient classes after one application of the product equivalence, where both
  -- sides reduce to the already-proved factor compatibility.
  apply e.injective
  calc
    e (binaryWedgeAmbientHomotopyGroupMap n X Y z) =
      binaryWedgeHomotopyGroupToFactors (n + 1) X Y z := by
        change e (e.symm (binaryWedgeHomotopyGroupToFactors (n + 1) X Y z)) = _
        exact e.apply_symm_apply _
    _ = productWedgeHomotopyGroupToFactors (n + 1) X Y
          (binaryWedgeToProductWedgeHomotopyGroupHom n X Y z) := by
            exact
              (productWedgeHomotopyGroupToFactors_comp_binaryWedgeToProductWedgeHomotopyGroupHom
                n X Y z).symm
    _ = e
          (pairSubspaceInclusionHomotopyGroupMap
            (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 2)
            (binaryWedgeToProductWedgeHomotopyGroupHom n X Y z)) := by
              simpa [e] using
                congrFun
                  (productWedgeHomotopyGroupToFactors_eq_prodEquiv_comp_subspaceInclusion
                    n X Y)
                  (binaryWedgeToProductWedgeHomotopyGroupHom n X Y z)

/-- Helper for Problem 9.7.1: once a binary-side boundary map compares to the native boundary,
its image already lies in the kernel of the ambient binary map. -/
theorem binaryBoundary_apply_eq_one_of_compareBoundary
    (n : ℕ) (X Y : BasedSpace)
    (boundaryHom :
      smashWedgeRelativeHomotopyGroup (n + 2) X Y →*
        basedHomotopyGroup (n + 2) (binaryWedge X Y))
    (hcompareBoundary :
      (binaryWedgeToProductWedgeHomotopyGroupHom n X Y).comp boundaryHom =
        pairHomotopyBoundaryMulHom
          (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1))
    (r : smashWedgeRelativeHomotopyGroup (n + 2) X Y) :
    binaryWedgeAmbientHomotopyGroupMap n X Y (boundaryHom r) = 1 := by
  have hcompareBoundary_apply :
      binaryWedgeToProductWedgeHomotopyGroupHom n X Y (boundaryHom r) =
        pairHomotopyBoundaryMulHom
          (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1) r := by
    -- Evaluate the comparison hom equality at the chosen relative class.
    simpa using congrArg (fun m => m r) hcompareBoundary
  have hnativeBoundary :
      pairSubspaceInclusionHomotopyGroupMap
          (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 2)
          (pairHomotopyBoundaryMulHom
            (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1) r) = 1 := by
    -- The native pair exactness already kills the native boundary image.
    have hnativeExact :
        Function.MulExact
          (pairHomotopyBoundaryMulHom
            (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1))
          (pairSubspaceInclusionHomotopyGroupMap
            (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 2)) := by
      simpa [pairHomotopyBoundaryMulHom_apply] using
        pairHomotopyLongExactSequenceBoundaryToSubspace
          (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1)
    simpa using Function.MulExact.apply_apply_eq_one hnativeExact r
  -- Rewrite the binary ambient map through the already-proved native subspace comparison.
  calc
    binaryWedgeAmbientHomotopyGroupMap n X Y (boundaryHom r) =
        pairSubspaceInclusionHomotopyGroupMap
          (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 2)
          (binaryWedgeToProductWedgeHomotopyGroupHom n X Y (boundaryHom r)) := by
            simpa [Function.comp_apply] using
              congrFun
                (binaryWedgeAmbientHomotopyGroupMap_eq_subspaceInclusion_comp n X Y)
                (boundaryHom r)
    _ =
        pairSubspaceInclusionHomotopyGroupMap
          (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 2)
          (pairHomotopyBoundaryMulHom
            (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1) r) := by
              rw [hcompareBoundary_apply]
    _ = 1 := hnativeBoundary

/-- Helper for Problem 9.7.1: once the binary-side boundary bridge is available, the comparison
map to the native wedge model is forced to be a multiplicative equivalence. -/
theorem binaryWedgeHomotopyGroup_mulEquiv_productWedgeExists_of_boundaryBridge
    (n : ℕ) (X Y : BasedSpace)
    (boundaryHom :
      smashWedgeRelativeHomotopyGroup (n + 2) X Y →*
        basedHomotopyGroup (n + 2) (binaryWedge X Y))
    (hcompareBoundary :
      (binaryWedgeToProductWedgeHomotopyGroupHom n X Y).comp boundaryHom =
        pairHomotopyBoundaryMulHom
          (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1))
    (hboundaryExact :
      Function.MulExact boundaryHom (binaryWedgeAmbientHomotopyGroupMap n X Y)) :
    Nonempty
      (basedHomotopyGroup (n + 2) (binaryWedge X Y) ≃*
        basedHomotopyGroup (n + 2) (productWedgeBasedSpace X Y)) := by
  let compareHom := binaryWedgeToProductWedgeHomotopyGroupHom n X Y
  let nativeBoundary :=
    pairHomotopyBoundaryMulHom
      (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1)
  let productToFactorsHom :
      basedHomotopyGroup (n + 2) (productWedgeBasedSpace X Y) →*
        (basedHomotopyGroup (n + 2) X × basedHomotopyGroup (n + 2) Y) :=
    (homotopyGroupMapOverEqMulHom
        (productWedgeLeftProjection X Y).right.hom
        (fundamentalGroupFunctorMap_basepoint (productWedgeLeftProjection X Y))
        (n + 1)).prod
      (homotopyGroupMapOverEqMulHom
        (productWedgeRightProjection X Y).right.hom
        (fundamentalGroupFunctorMap_basepoint (productWedgeRightProjection X Y))
        (n + 1))
  have hcompareBoundary_apply :
      ∀ r, compareHom (boundaryHom r) = nativeBoundary r := by
    intro r
    -- Evaluate the boundary-compatibility hom equality at the chosen relative class.
    simpa [compareHom, nativeBoundary] using congrArg (fun m => m r) hcompareBoundary
  refine ⟨MulEquiv.ofBijective compareHom ?_⟩
  constructor
  · intro z w hzw
    have hkernel :
        compareHom (z * w⁻¹) = 1 := by
      -- Equality after `compareHom` puts the quotient element in the kernel.
      rw [map_mul, hzw, map_inv, mul_inv_cancel]
    have hkernelFactors :
        binaryWedgeHomotopyGroupToFactors (n + 1) X Y (z * w⁻¹) = 1 := by
      -- The comparison preserves factor coordinates, so a kernel element for `compareHom` has
      -- trivial factor coordinates on the binary side as well.
      calc
        binaryWedgeHomotopyGroupToFactors (n + 1) X Y (z * w⁻¹) =
            productWedgeHomotopyGroupToFactors (n + 1) X Y (compareHom (z * w⁻¹)) := by
              symm
              exact
                productWedgeHomotopyGroupToFactors_comp_binaryWedgeToProductWedgeHomotopyGroupHom
                  n X Y (z * w⁻¹)
        _ = productWedgeHomotopyGroupToFactors (n + 1) X Y 1 := by rw [hkernel]
        _ = 1 := by
          -- Switch to the bundled factor map so the unit computation is a single `map_one`.
          change productToFactorsHom 1 = 1
          exact productToFactorsHom.map_one
    have hkernelAmbient :
        binaryWedgeAmbientHomotopyGroupMap n X Y (z * w⁻¹) = 1 := by
      -- The ambient binary map is the inverse product equivalence applied to the factor map.
      change
        (homotopyGroupProdEquiv (n := n + 2)
          (x := underTopBasepoint X) (y := underTopBasepoint Y)).symm
            (binaryWedgeHomotopyGroupToFactors (n + 1) X Y (z * w⁻¹)) = 1
      rw [hkernelFactors]
      simp
    rcases (hboundaryExact (z * w⁻¹)).mp hkernelAmbient with ⟨r, hrange⟩
    have hrBoundary : nativeBoundary r = 1 := by
      -- The binary exactness witness maps to the trivial native boundary because the quotient
      -- element was already in the comparison kernel.
      calc
        nativeBoundary r = compareHom (boundaryHom r) := (hcompareBoundary_apply r).symm
        _ = compareHom (z * w⁻¹) := by rw [hrange]
        _ = 1 := hkernel
    have hboundaryEq :
        pairHomotopyBoundaryMap
            (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1) r =
          pairHomotopyBoundaryMap
            (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1) 1 := by
      -- Compare with the trivial relative class so native boundary injectivity can cancel `r`.
      have hnativeEq : nativeBoundary r = nativeBoundary 1 := by
        rw [hrBoundary, nativeBoundary.map_one]
      calc
        pairHomotopyBoundaryMap
            (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1) r =
          nativeBoundary r := by
            exact
              (pairHomotopyBoundaryMulHom_apply
                (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1) r).symm
        _ = nativeBoundary 1 := hnativeEq
        _ =
          pairHomotopyBoundaryMap
            (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1) 1 := by
              exact
                pairHomotopyBoundaryMulHom_apply
                  (productWedgeLocus X Y) (smashWedgeRelativeBasepoint X Y) (n + 1) 1
    have hr : r = 1 := productWedgeBoundary_injective n X Y hboundaryEq
    have hquotient : z * w⁻¹ = 1 := by
      -- The exactness witness was already trivial, so the quotient element is trivial as well.
      calc
        z * w⁻¹ = boundaryHom r := hrange.symm
        _ = boundaryHom 1 := by rw [hr]
        _ = 1 := boundaryHom.map_one
    -- Cancel the now-trivial quotient element to recover equality of the original classes.
    calc
      z = z * 1 := by simp
      _ = z * (w⁻¹ * w) := by rw [inv_mul_cancel]
      _ = (z * w⁻¹) * w := by simp [mul_assoc]
      _ = 1 * w := by rw [hquotient]
      _ = w := by simp
  · intro g
    let z0 :=
      binaryWedgeHomotopyGroupFromFactors (n + 1) X Y
        (productWedgeHomotopyGroupToFactors (n + 1) X Y g)
    have hz0Factors :
        productWedgeHomotopyGroupToFactors (n + 1) X Y (compareHom z0) =
          productWedgeHomotopyGroupToFactors (n + 1) X Y g := by
      -- Start from the explicit binary section so both ambient classes share the same factor data.
      calc
        productWedgeHomotopyGroupToFactors (n + 1) X Y (compareHom z0) =
          binaryWedgeHomotopyGroupToFactors (n + 1) X Y z0 := by
            exact
              productWedgeHomotopyGroupToFactors_comp_binaryWedgeToProductWedgeHomotopyGroupHom
                n X Y z0
        _ =
          productWedgeHomotopyGroupToFactors (n + 1) X Y g := by
            simpa [z0] using
              binaryWedgeHomotopyGroupToFactors_rightInverse
                (n + 1) X Y
                (productWedgeHomotopyGroupToFactors (n + 1) X Y g)
    have hz0Factors' :
        productToFactorsHom (compareHom z0) = productToFactorsHom g := by
      -- Rewrite the factor agreement through the bundled native factor map.
      apply Prod.ext
      · simpa [productToFactorsHom, productWedgeHomotopyGroupToFactors] using
          congrArg Prod.fst hz0Factors
      · simpa [productToFactorsHom, productWedgeHomotopyGroupToFactors] using
          congrArg Prod.snd hz0Factors
    have hk :
        productWedgeHomotopyGroupToFactors (n + 1) X Y
            (g * (compareHom z0)⁻¹) = 1 := by
      -- The correction term lies in the native kernel because the section already matches factors.
      change productToFactorsHom (g * (compareHom z0)⁻¹) = 1
      rw [productToFactorsHom.map_mul, productToFactorsHom.map_inv, hz0Factors', mul_inv_cancel]
    rcases
        (productWedgeBoundary_mulExact_toFactors n X Y
          (g * (compareHom z0)⁻¹)).mp hk with
      ⟨r, hr⟩
    refine ⟨boundaryHom r * z0, ?_⟩
    have hrNative :
        nativeBoundary r = g * (compareHom z0)⁻¹ := by
      -- Repackage the native exactness witness through the bundled boundary hom.
      simpa [nativeBoundary, pairHomotopyBoundaryMulHom_apply] using hr
    have hrCompare :
        compareHom (boundaryHom r) = g * (compareHom z0)⁻¹ := by
      -- Move the native correction term back across the binary comparison.
      rw [hcompareBoundary_apply r]
      exact hrNative
    -- The native correction term is already in the image of the binary boundary bridge.
    calc
      compareHom (boundaryHom r * z0) =
        compareHom (boundaryHom r) * compareHom z0 := by
          rw [map_mul]
      _ = (g * (compareHom z0)⁻¹) * compareHom z0 := by rw [hrCompare]
      _ = g := by
          rw [mul_assoc, inv_mul_cancel, mul_one]

/-- Helper for Problem 9.7.1: the coproduct wedge and the native product-wedge model induce the
same positive-degree homotopy groups. -/
theorem binaryWedgeHomotopyGroup_mulEquiv_productWedgeExists
    (n : ℕ) (X Y : BasedSpace) :
    Nonempty
      (basedHomotopyGroup (n + 2) (binaryWedge X Y) ≃*
        basedHomotopyGroup (n + 2) (productWedgeBasedSpace X Y)) := by
  -- Route correction: the remaining comparison is now proved by the explicit native-to-binary
  -- space map, not by rebuilding a binary-side boundary exactness bridge.
  refine ⟨MulEquiv.ofBijective (binaryWedgeToProductWedgeHomotopyGroupHom n X Y) ?_⟩
  -- The two space-level comparison maps are inverse, so the induced homotopy-group map is
  -- bijective as well.
  exact binaryWedgeToProductWedgeHomotopyGroupHom_bijective n X Y

/-- Problem 9.7.1 admits the source-facing decomposition equivalence of
`π_ (n + 2) (binaryWedge X Y)`. -/
theorem wedgeHomotopyGroup_mulEquiv_prod_prod_relative_exists
    (n : ℕ) (X Y : BasedSpace) :
    Nonempty (wedgeHomotopyGroup_mulEquiv_prod_prod_relative n X Y) := by
  -- Route correction: the pair-LES kernel step is now isolated on `productWedgeBasedSpace X Y`,
  -- so the source-facing theorem is just the composition of the native split with the remaining
  -- comparison theorem between the quotient wedge and the native wedge model.
  rcases binaryWedgeHomotopyGroup_mulEquiv_productWedgeExists n X Y with ⟨hCompare⟩
  rcases productWedgeHomotopyGroup_mulEquiv_prod_prod_relative_exists n X Y with ⟨hNative⟩
  exact ⟨hCompare.trans hNative⟩
