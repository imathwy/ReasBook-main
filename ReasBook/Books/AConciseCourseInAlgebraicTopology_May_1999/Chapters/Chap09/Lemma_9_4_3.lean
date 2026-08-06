import Mathlib.Topology.Covering.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Criterion_7_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Lemma_7_2_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Criterion_8_5_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Theorem_9_3_4

universe u v

open CategoryTheory
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

-- Semantic recall via `lean_leansearch`: `IsCoveringMap` is the canonical owner for coverings,
-- and local Chapter 9 precedent uses `homotopyGroupMap` for the induced map `p_*` on based
-- homotopy groups.

namespace IsCoveringMap

local notation "BasedSpace" => Under (⊤_ TopCat)

/-- Helper for Lemma 9.4.3: every point of a positive-dimensional generalized loop lies in the
path component of the basepoint. -/
private theorem genLoop_mem_pathComponent {X : Type*} [TopologicalSpace X] (m : ℕ) {x : X}
    (γ : Ω^ (Fin (m + 1)) X x) (t : I^(Fin (m + 1))) :
    γ t ∈ pathComponent x := by
  -- Join the distinguished boundary vertex to `t` by the straight-line cube path, then map it
  -- across `γ`.
  let zeroCube : I^(Fin (m + 1)) := fun _ ↦ 0
  have hzero : zeroCube ∈ Cube.boundary (Fin (m + 1)) := ⟨0, Or.inl rfl⟩
  let cubePath : Path zeroCube t :=
    Path.mk
      ⟨fun s i ↦
        ⟨s * t i, by
          exact unitInterval.mul_mem s.2 (t i).2⟩,
        by fun_prop⟩
      (by
        ext i
        simp [zeroCube])
      (by
        ext i
        simp)
  refine mem_pathComponent_iff.mpr ?_
  refine ⟨(cubePath.map γ.1.continuous).cast (γ.2 zeroCube hzero).symm rfl⟩

/-- Helper for Lemma 9.4.3: a positive-dimensional generalized loop whose values lie in a subset
`A` can be regarded as a generalized loop in the subspace `A`. -/
private def genLoopToSubspace {X : Type*} [TopologicalSpace X] (A : Set X) {x : A} (m : ℕ)
    (γ : Ω^ (Fin (m + 1)) X x.1) (hγ : ∀ t, γ t ∈ A) :
    Ω^ (Fin (m + 1)) A x :=
  ⟨⟨fun t ↦ ⟨γ t, hγ t⟩, γ.1.continuous.subtype_mk hγ⟩, fun t ht ↦ by
    apply Subtype.ext
    simpa using γ.2 t ht⟩

/-- Helper for Lemma 9.4.3: forgetting the subspace target of `genLoopToSubspace` recovers the
original generalized loop. -/
private theorem genLoopMap_subspaceInclusion_genLoopToSubspace {X : Type*} [TopologicalSpace X]
    (A : Set X) {x : A} (m : ℕ) (γ : Ω^ (Fin (m + 1)) X x.1) (hγ : ∀ t, γ t ∈ A) :
    genLoopMap (pairSubspaceInclusion A) (genLoopToSubspace A m γ hγ) = γ := by
  -- The inclusion map only forgets the subtype witness.
  ext t
  simp [genLoopMap, genLoopToSubspace, pairSubspaceInclusion]

/-- Helper for Lemma 9.4.3: every point of a positive-dimensional generalized-loop homotopy lies
in the path component of the common basepoint. -/
private theorem homotopy_mem_pathComponent {X : Type*} [TopologicalSpace X] (m : ℕ) {x : X}
    {γ δ : Ω^ (Fin (m + 1)) X x} (H : GenLoop.Homotopic γ δ) (z : I × I^(Fin (m + 1))) :
    (Classical.choice H) z ∈ pathComponent x := by
  -- Evaluate the relative homotopy at a boundary vertex and connect to `z` inside the product.
  let zeroCube : I^(Fin (m + 1)) := fun _ ↦ 0
  have hzero : zeroCube ∈ Cube.boundary (Fin (m + 1)) := ⟨0, Or.inl rfl⟩
  let squarePath : Path (0, zeroCube) z :=
    Path.mk
      ⟨fun s ↦
        (⟨s * z.1, by
            exact unitInterval.mul_mem s.2 z.1.2⟩,
          fun i ↦
            ⟨s * z.2 i, by
              exact unitInterval.mul_mem s.2 (z.2 i).2⟩),
        by fun_prop⟩
      (by
        ext
        · simp
        · simp [zeroCube])
      (by
        ext
        · simp
        · simp)
  let H' := Classical.choice H
  refine mem_pathComponent_iff.mpr ?_
  have hbase : H' (0, zeroCube) = x := by
    calc
      H' (0, zeroCube) = γ zeroCube := H'.eq_fst 0 hzero
      _ = x := by simpa [zeroCube] using γ.2 zeroCube hzero
  refine ⟨(squarePath.map H'.toHomotopy.continuous).cast hbase.symm rfl⟩

/-- Helper for Lemma 9.4.3: a positive-dimensional homotopy between loops in `X` whose image
stays in `A` lifts to a homotopy in the subspace `A`. -/
private theorem genLoopHomotopic_toSubspace {X : Type*} [TopologicalSpace X] (A : Set X) {x : A}
    (m : ℕ) {γ δ : Ω^ (Fin (m + 1)) A x}
    (H : GenLoop.Homotopic (genLoopMap (pairSubspaceInclusion A) γ)
      (genLoopMap (pairSubspaceInclusion A) δ))
    (hH : ∀ z, (Classical.choice H) z ∈ A) :
    GenLoop.Homotopic γ δ := by
  -- Lift the ambient homotopy pointwise into the subtype and reuse the relative-boundary data.
  let H' := Classical.choice H
  refine ⟨{
      toHomotopy := {
        toFun := fun z ↦ ⟨H'.toHomotopy z, hH z⟩
        continuous_toFun := H'.toHomotopy.continuous.subtype_mk hH
        map_zero_left := by
          intro t
          ext
          exact H'.toHomotopy.map_zero_left t
        map_one_left := by
          intro t
          ext
          exact H'.toHomotopy.map_one_left t }
      prop' := ?_ }⟩
  intro s t ht
  apply Subtype.ext
  simpa [genLoopMap, pairSubspaceInclusion] using H'.eq_fst s ht

/-- Helper for Lemma 9.4.3: if a subset `A ⊆ X` contains the path component of the chosen
basepoint, then inclusion `A ↪ X` induces a bijection on positive homotopy groups. -/
private theorem subspaceInclusion_bijective_of_pathComponentSubset {X : Type*}
    [TopologicalSpace X] (A : Set X) (x : A) (m : ℕ) (hA : pathComponent x.1 ⊆ A) :
    Function.Bijective ((pairSubspaceInclusion A).eStar (m + 1) x) := by
  constructor
  · intro a b hab
    -- Any ambient homotopy between images already lives in the same path component, hence in `A`.
    refine Quotient.inductionOn₂ a b ?_ hab
    intro γ δ h
    apply Quotient.sound
    exact genLoopHomotopic_toSubspace A m (Quotient.exact h)
      (fun z ↦ hA (homotopy_mem_pathComponent m (Quotient.exact h) z))
  · intro g
    -- Factor the chosen representative through `A` pointwise using path connectedness of the cube.
    refine Quotient.inductionOn g ?_
    intro γ
    refine ⟨⟦genLoopToSubspace A m γ (fun t ↦ hA (genLoop_mem_pathComponent m γ t))⟧, ?_⟩
    rw [homotopyGroupMap_mk]
    simpa [genLoopMap_subspaceInclusion_genLoopToSubspace]

/-- Helper for Lemma 9.4.3: the covering restricted to `pathComponent (p e)` is surjective. -/
private theorem pathComponentRestrictSurjective {p : C(E, B)} (hp : IsCoveringMap p) (e : E) :
    Function.Surjective ((pathComponent (p e)).restrictPreimage p) := by
  intro y
  rcases mem_pathComponent_iff.mp y.2 with ⟨γ⟩
  -- Lift a path from `p e` to `y` starting at `e`; its endpoint lies over `y`.
  let lifted := hp.liftPath γ.toContinuousMap e γ.source'
  refine ⟨⟨lifted 1, ?_⟩, ?_⟩
  · have hendpoint :=
      (congrFun (hp.liftPath_lifts γ.toContinuousMap e γ.source') 1).trans γ.target'
    have hendpoint' : p (lifted 1) = y.1 := by
      simpa [lifted, ContinuousMap.comp_apply] using hendpoint
    change p (lifted 1) ∈ pathComponent (p e)
    rw [hendpoint']
    exact y.2
  · apply Subtype.ext
    simpa [lifted] using
      (congrFun (hp.liftPath_lifts γ.toContinuousMap e γ.source') 1).trans γ.target'

/-- Helper for Lemma 9.4.3: postcomposition on homotopy groups respects composition of the
underlying continuous maps. -/
private theorem homotopyGroupMap_comp
    {A : Type*} {B : Type*} {C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C)) (q : ℕ) (a : A) :
    homotopyGroupMap (g.comp f) q a =
      homotopyGroupMap g q (f a) ∘ homotopyGroupMap f q a := by
  -- Compare both induced maps on loop representatives before quotienting.
  funext x
  refine Quotient.inductionOn x ?_
  intro γ
  rfl

/-- Helper for Lemma 9.4.3: applying `eStarMulHomOverEq` agrees with the transported positive
homotopy-group map. -/
private theorem eStarMulHomOverEq_apply
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (hf : f a = b) (n : ℕ)
    (x : π_ (n + 1) A a) :
    f.eStarMulHomOverEq n hf x =
      cast
        (congrArg (fun y ↦ π_ (n + 1) A a → π_ (n + 1) B y) hf)
        (homotopyGroupMap f (n + 1) a) x := by
  -- Once the endpoint proof becomes `rfl`, both maps are literally the same.
  cases hf
  rfl

/-- Helper for Lemma 9.4.3: the canonical map into a `ULift` copy of a space. -/
private def uliftUpContinuousMap (X : Type*) [TopologicalSpace X] : C(X, ULift X) :=
  ⟨ULift.up, continuous_uliftUp⟩

/-- Helper for Lemma 9.4.3: the canonical map back from a `ULift` copy of a space. -/
private def uliftDownContinuousMap (X : Type*) [TopologicalSpace X] : C(ULift X, X) :=
  ⟨ULift.down, continuous_uliftDown⟩

/-- Helper for Lemma 9.4.3: evaluating the `ULift`-up comparison map is definitionally `ULift.up`.
-/
@[simp] private theorem uliftUpContinuousMap_apply {X : Type*} [TopologicalSpace X] (x : X) :
    uliftUpContinuousMap X x = ULift.up x :=
  rfl

/-- Helper for Lemma 9.4.3: evaluating the `ULift`-down comparison map is definitionally
`ULift.down`. -/
@[simp] private theorem uliftDownContinuousMap_apply {X : Type*} [TopologicalSpace X]
    (x : ULift X) :
    uliftDownContinuousMap X x = x.down :=
  rfl

/-- Helper for Lemma 9.4.3: the two `ULift` comparison maps compose to the identity on the
original space. -/
@[simp] private theorem uliftDownContinuousMap_comp_uliftUpContinuousMap
    {X : Type*} [TopologicalSpace X] :
    (uliftDownContinuousMap X).comp (uliftUpContinuousMap X) = ContinuousMap.id X := by
  -- Compare the composite and the identity pointwise on the underlying space.
  ext x
  rfl

/-- Helper for Lemma 9.4.3: the two `ULift` comparison maps compose to the identity on the lifted
space. -/
@[simp] private theorem uliftUpContinuousMap_comp_uliftDownContinuousMap
    {X : Type*} [TopologicalSpace X] :
    (uliftUpContinuousMap X).comp (uliftDownContinuousMap X) = ContinuousMap.id (ULift X) := by
  -- Compare the composite and the identity pointwise on the lifted space.
  ext x
  cases x
  rfl

/-- Helper for Lemma 9.4.3: lift a continuous map to a common universe so the Chapter 9 based-map
API can be applied without mixing source and target universes in the same owner. -/
private def uliftContinuousMapAcrossUniverses {Y : Type u} {Z : Type v}
    [TopologicalSpace Y] [TopologicalSpace Z] (e : C(Y, Z)) :
    C(ULift.{v} Y, ULift.{u} Z) :=
  (uliftUpContinuousMap Z).comp (e.comp (uliftDownContinuousMap Y))

/-- Helper for Lemma 9.4.3: evaluating the lifted cross-universe map is the same as applying `e`
and then lifting the result back. -/
@[simp] private theorem uliftContinuousMapAcrossUniverses_apply {Y : Type u} {Z : Type v}
    [TopologicalSpace Y] [TopologicalSpace Z] (e : C(Y, Z)) (y : ULift.{v} Y) :
    uliftContinuousMapAcrossUniverses e y = ULift.up (e y.down) :=
  rfl

/-- Helper for Lemma 9.4.3: restate `underTopOfPointMap` after lifting source and target into a
common universe. -/
private def underTopOfPointMapAcrossUniverses {Y : Type u} {Z : Type v}
    [TopologicalSpace Y] [TopologicalSpace Z] (e : C(Y, Z)) (y₀ : Y) :
    underTopOfPoint (ULift.{v} Y) (ULift.up y₀) ⟶
      underTopOfPoint (ULift.{u} Z) (ULift.up (e y₀)) :=
  Under.homMk (TopCat.ofHom (uliftContinuousMapAcrossUniverses e)) (by
    -- The lifted map sends the chosen lifted basepoint to the chosen lifted image.
    ext u
    rfl)

/-- Helper for Lemma 9.4.3: the underlying continuous map of the lifted based-map bridge is the
lifted continuous map itself. -/
@[simp] private theorem underTopOfPointMapAcrossUniverses_hom {Y : Type u} {Z : Type v}
    [TopologicalSpace Y] [TopologicalSpace Z] (e : C(Y, Z)) (y₀ : Y) :
    (underTopOfPointMapAcrossUniverses e y₀).right.hom = uliftContinuousMapAcrossUniverses e :=
  rfl

/-- Helper for Lemma 9.4.3: the lifted based-map bridge preserves the chosen basepoints. -/
@[simp] private theorem underTopOfPointMapAcrossUniverses_basepoint {Y : Type u} {Z : Type v}
    [TopologicalSpace Y] [TopologicalSpace Z] (e : C(Y, Z)) (y₀ : Y) :
    (underTopOfPointMapAcrossUniverses e y₀).right.hom
        (underTopBasepoint (underTopOfPoint (ULift.{v} Y) (ULift.up y₀))) =
      underTopBasepoint (underTopOfPoint (ULift.{u} Z) (ULift.up (e y₀))) := by
  -- The lifted bridge was defined so that it sends the chosen lifted basepoint to the lifted
  -- image of the original basepoint.
  rfl

/-- Helper for Lemma 9.4.3: the `ULift`-up comparison induces a bijection on every homotopy
group. -/
private theorem uliftUpContinuousMap_bijective_homotopyGroupMap
    {X : Type*} [TopologicalSpace X] (q : ℕ) (x : X) :
    Function.Bijective ((uliftUpContinuousMap X).eStar q x) := by
  -- The `ULift`-up map has the `ULift`-down map as inverse on homotopy groups because the two
  -- underlying continuous maps compose to the identity in both orders.
  have hleft_raw :=
    homotopyGroupMap_comp (uliftUpContinuousMap X) (uliftDownContinuousMap X) q x
  have hleft_id :
      homotopyGroupMap ((uliftDownContinuousMap X).comp (uliftUpContinuousMap X)) q x = id := by
    funext a
    refine Quotient.inductionOn a ?_
    intro γ
    rfl
  have hleft :
      (uliftDownContinuousMap X).eStar q (ULift.up x) ∘ (uliftUpContinuousMap X).eStar q x = id :=
    hleft_raw.symm.trans hleft_id
  have hright_raw :=
    homotopyGroupMap_comp (uliftDownContinuousMap X) (uliftUpContinuousMap X) q (ULift.up x)
  have hright_id :
      homotopyGroupMap ((uliftUpContinuousMap X).comp (uliftDownContinuousMap X)) q (ULift.up x) =
        id := by
    funext a
    refine Quotient.inductionOn a ?_
    intro γ
    rfl
  have hright :
      (uliftUpContinuousMap X).eStar q x ∘ (uliftDownContinuousMap X).eStar q (ULift.up x) = id :=
    hright_raw.symm.trans hright_id
  constructor
  · intro a b hab
    have ha :
        (uliftDownContinuousMap X).eStar q (ULift.up x)
            ((uliftUpContinuousMap X).eStar q x a) = a := by
      simpa [Function.comp, homotopyGroupMap_id] using congrFun hleft a
    have hb :
        (uliftDownContinuousMap X).eStar q (ULift.up x)
            ((uliftUpContinuousMap X).eStar q x b) = b := by
      simpa [Function.comp, homotopyGroupMap_id] using congrFun hleft b
    exact ha.symm.trans <| (congrArg ((uliftDownContinuousMap X).eStar q (ULift.up x)) hab).trans hb
  · intro b
    refine ⟨(uliftDownContinuousMap X).eStar q (ULift.up x) b, ?_⟩
    simpa [Function.comp, homotopyGroupMap_id] using congrFun hright b

/-- Helper for Lemma 9.4.3: the `ULift`-down comparison induces a bijection on every homotopy
group. -/
private theorem uliftDownContinuousMap_bijective_homotopyGroupMap
    {X : Type*} [TopologicalSpace X] (q : ℕ) (x : ULift X) :
    Function.Bijective ((uliftDownContinuousMap X).eStar q x) := by
  -- The `ULift`-down map is inverse to `ULift`-up on homotopy groups by the same identity
  -- composite calculation as above.
  have hleft_raw :=
    homotopyGroupMap_comp (uliftDownContinuousMap X) (uliftUpContinuousMap X) q x
  have hleft_id :
      homotopyGroupMap ((uliftUpContinuousMap X).comp (uliftDownContinuousMap X)) q x = id := by
    funext a
    refine Quotient.inductionOn a ?_
    intro γ
    rfl
  have hleft :
      (uliftUpContinuousMap X).eStar q x.down ∘ (uliftDownContinuousMap X).eStar q x = id :=
    hleft_raw.symm.trans hleft_id
  have hright_raw :=
    homotopyGroupMap_comp (uliftUpContinuousMap X) (uliftDownContinuousMap X) q x.down
  have hright_id :
      homotopyGroupMap ((uliftDownContinuousMap X).comp (uliftUpContinuousMap X)) q x.down = id :=
    by
      funext a
      refine Quotient.inductionOn a ?_
      intro γ
      rfl
  have hright :
      (uliftDownContinuousMap X).eStar q x ∘ (uliftUpContinuousMap X).eStar q x.down = id :=
    hright_raw.symm.trans hright_id
  constructor
  · intro a b hab
    have ha :
        (uliftUpContinuousMap X).eStar q x.down
            ((uliftDownContinuousMap X).eStar q x a) = a := by
      simpa [Function.comp, homotopyGroupMap_id] using congrFun hleft a
    have hb :
        (uliftUpContinuousMap X).eStar q x.down
            ((uliftDownContinuousMap X).eStar q x b) = b := by
      simpa [Function.comp, homotopyGroupMap_id] using congrFun hleft b
    exact ha.symm.trans <| (congrArg ((uliftUpContinuousMap X).eStar q x.down) hab).trans hb
  · intro b
    refine ⟨(uliftUpContinuousMap X).eStar q x.down b, ?_⟩
    simpa [Function.comp, homotopyGroupMap_id] using congrFun hright b

/-- Helper for Lemma 9.4.3: lifting source and target into a common universe conjugates the
induced homotopy-group map by the `ULift` comparison maps. -/
private theorem ContinuousMap.eStar_uliftConjugation {Y : Type u} {Z : Type v}
    [TopologicalSpace Y] [TopologicalSpace Z] (e : C(Y, Z)) (q : ℕ) (y : Y) :
    (uliftContinuousMapAcrossUniverses e).eStar q (ULift.up y) =
      (uliftUpContinuousMap Z).eStar q (e y) ∘ e.eStar q y ∘
        (uliftDownContinuousMap Y).eStar q (ULift.up y) := by
  -- Expand the lifted map as `ULift.up ∘ e ∘ ULift.down`, then compose the two induced maps one
  -- factor at a time.
  funext a
  have houter :
      (uliftContinuousMapAcrossUniverses e).eStar q (ULift.up y) a =
        (uliftUpContinuousMap Z).eStar q (e y)
          ((e.comp (uliftDownContinuousMap Y)).eStar q (ULift.up y) a) := by
    simpa [uliftContinuousMapAcrossUniverses, Function.comp] using
      congrFun (homotopyGroupMap_comp (e.comp (uliftDownContinuousMap Y))
        (uliftUpContinuousMap Z) q (ULift.up y)) a
  have hinner :
      (e.comp (uliftDownContinuousMap Y)).eStar q (ULift.up y) a =
        e.eStar q y ((uliftDownContinuousMap Y).eStar q (ULift.up y) a) := by
    simpa [Function.comp] using
      congrFun (homotopyGroupMap_comp (uliftDownContinuousMap Y) e q (ULift.up y)) a
  calc
    (uliftContinuousMapAcrossUniverses e).eStar q (ULift.up y) a
      = (uliftUpContinuousMap Z).eStar q (e y)
          ((e.comp (uliftDownContinuousMap Y)).eStar q (ULift.up y) a) := houter
    _ = (uliftUpContinuousMap Z).eStar q (e y)
          (e.eStar q y ((uliftDownContinuousMap Y).eStar q (ULift.up y) a)) := by rw [hinner]
    _ = ((uliftUpContinuousMap Z).eStar q (e y) ∘ e.eStar q y ∘
          (uliftDownContinuousMap Y).eStar q (ULift.up y)) a := by
            rfl

/-- Helper for Lemma 9.4.3: the original and lifted homotopy-group maps are bijective
simultaneously. -/
private theorem ContinuousMap.bijective_eStar_iff_bijective_uliftAcrossUniverses
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : C(Y, Z)) (q : ℕ) (y : Y) :
    Function.Bijective ((uliftContinuousMapAcrossUniverses e).eStar q (ULift.up y)) ↔
      Function.Bijective (e.eStar q y) := by
  -- Conjugating by the two `ULift` comparison bijections shows that bijectivity is unchanged by
  -- moving to the common-universe spelling.
  constructor
  · intro hLifted
    have hdownZ := uliftDownContinuousMap_bijective_homotopyGroupMap q (ULift.up (e y))
    have hupY := uliftUpContinuousMap_bijective_homotopyGroupMap q y
    have hconj := ContinuousMap.eStar_uliftConjugation e q y
    have hdownUpZ :
        (uliftDownContinuousMap Z).eStar q (ULift.up (e y)) ∘
            (uliftUpContinuousMap Z).eStar q (e y) = id := by
      have hraw := homotopyGroupMap_comp (uliftUpContinuousMap Z) (uliftDownContinuousMap Z) q
        (e y)
      have hid :
          homotopyGroupMap ((uliftDownContinuousMap Z).comp (uliftUpContinuousMap Z)) q (e y) =
            id := by
        funext a
        refine Quotient.inductionOn a ?_
        intro γ
        rfl
      exact hraw.symm.trans hid
    have hdownUpY :
        (uliftDownContinuousMap Y).eStar q (ULift.up y) ∘
            (uliftUpContinuousMap Y).eStar q y = id := by
      have hraw := homotopyGroupMap_comp (uliftUpContinuousMap Y) (uliftDownContinuousMap Y) q y
      have hid :
          homotopyGroupMap ((uliftDownContinuousMap Y).comp (uliftUpContinuousMap Y)) q y = id := by
        funext a
        refine Quotient.inductionOn a ?_
        intro γ
        rfl
      exact hraw.symm.trans hid
    have hrewrite :
        ((uliftDownContinuousMap Z).eStar q (ULift.up (e y))) ∘
            (uliftContinuousMapAcrossUniverses e).eStar q (ULift.up y) ∘
            (uliftUpContinuousMap Y).eStar q y =
          e.eStar q y := by
      funext a
      calc
        (((uliftDownContinuousMap Z).eStar q (ULift.up (e y))) ∘
              (uliftContinuousMapAcrossUniverses e).eStar q (ULift.up y) ∘
              (uliftUpContinuousMap Y).eStar q y) a
            = (uliftDownContinuousMap Z).eStar q (ULift.up (e y))
                ((uliftContinuousMapAcrossUniverses e).eStar q (ULift.up y)
                  ((uliftUpContinuousMap Y).eStar q y a)) := by
                    rfl
        _ = (uliftDownContinuousMap Z).eStar q (ULift.up (e y))
              ((uliftUpContinuousMap Z).eStar q (e y)
                (e.eStar q y
                  ((uliftDownContinuousMap Y).eStar q (ULift.up y)
                    ((uliftUpContinuousMap Y).eStar q y a)))) := by
                  rw [hconj]
                  rfl
        _ = e.eStar q y
              ((uliftDownContinuousMap Y).eStar q (ULift.up y)
                ((uliftUpContinuousMap Y).eStar q y a)) := by
                  simpa [Function.comp] using congrFun hdownUpZ
                    (e.eStar q y
                      ((uliftDownContinuousMap Y).eStar q (ULift.up y)
                        ((uliftUpContinuousMap Y).eStar q y a)))
        _ = e.eStar q y a := by
              exact congrArg (e.eStar q y) (congrFun hdownUpY a)
    rw [← hrewrite]
    exact hdownZ.comp (hLifted.comp hupY)
  · intro h
    have hupZ := uliftUpContinuousMap_bijective_homotopyGroupMap q (e y)
    have hdownY := uliftDownContinuousMap_bijective_homotopyGroupMap q (ULift.up y)
    have hconj := ContinuousMap.eStar_uliftConjugation e q y
    simpa [hconj] using hupZ.comp (h.comp hdownY)

/-
The following obsolete adapters identified the k-ified Chapter 7 mapping-path topology with the
raw Chapter 8 based subtype topology. They are not valid after the May-category pullback fix.

/-- Helper for Lemma 9.4.3: a continuous path lift upgrades to a based path lift once it sends
the canonical mapping-path-space basepoint to the constant basepoint path. -/
private theorem basedPathLiftOfContinuousPathLift
    {E B : BasedSpace} (p : E ⟶ B)
    (s : ContinuousPathLiftingFunction p.right.hom)
    (hbase :
      s.toContinuousMap (basedMappingPathSpaceBasepoint p) =
        ContinuousMap.const I (underTopBasepoint E)) :
    Nonempty (BasedPathLiftingFunction p) := by
  -- The Chapter 7 and Chapter 8 mapping-path-space owners are definitionally the same subtype.
  refine ⟨{
    toContinuousMap := s.toContinuousMap
    source_eq := ?_
    proj_comp_eq := ?_
    map_basepoint := hbase
  }⟩
  · intro x
    exact s.source_eq x
  · intro x
    exact s.proj_comp_eq x

/-- Helper for Lemma 9.4.3: a continuous map from the interval into a discrete space is constant.
-/
private theorem continuousMap_eq_const_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (γ : C(I, X)) :
    γ = ContinuousMap.const I (γ 0) := by
  -- The unit interval is preconnected, so a continuous map into a discrete target cannot move.
  ext t
  simpa using
    (PreconnectedSpace.constant (α := I) (Y := X) inferInstance γ.continuous (x := t) (y := 0))

/-- Helper for Lemma 9.4.3: a surjective based map with a continuous path lift satisfying the
canonical basepoint condition is a based fibration. -/
private theorem isBasedFibrationOfContinuousPathLift
    {E B : BasedSpace} (p : E ⟶ B) (hsurj : Function.Surjective p.right.hom)
    (s : ContinuousPathLiftingFunction p.right.hom)
    (hbase :
      s.toContinuousMap (basedMappingPathSpaceBasepoint p) =
        ContinuousMap.const I (underTopBasepoint E)) :
    IsBasedFibration p := by
  -- Convert the unbased path-lifting witness to the Chapter 8 owner and apply the criterion.
  let _ : Nonempty (BasedPathLiftingFunction p) :=
    basedPathLiftOfContinuousPathLift p s hbase
  exact (IsBasedFibration.iff_surjective_and_nonempty_basedPathLiftingFunction p).2
    ⟨hsurj, inferInstance⟩

/-- Helper for Lemma 9.4.3: the cross-universe based map is a based fibration as soon as its
lifted underlying map is surjective and admits a normalized continuous path lift. -/
private theorem underTopOfPointMapAcrossUniverses_isBasedFibrationOfContinuousPathLift
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (r : C(Y, Z)) (y₀ : Y)
    (hsurj : Function.Surjective (underTopOfPointMapAcrossUniverses r y₀).right.hom)
    (s : ContinuousPathLiftingFunction (underTopOfPointMapAcrossUniverses r y₀).right.hom)
    (hbase :
      s.toContinuousMap (basedMappingPathSpaceBasepoint
          (underTopOfPointMapAcrossUniverses r y₀)) =
        ContinuousMap.const I (ULift.up y₀)) :
    IsBasedFibration (underTopOfPointMapAcrossUniverses r y₀) := by
  let pBased := underTopOfPointMapAcrossUniverses r y₀
  let sBased : ContinuousPathLiftingFunction pBased.right.hom := s
  -- Rewrite the endpoint condition into the exact based-owner spelling expected by the criterion.
  have hbase' :
      sBased.toContinuousMap (basedMappingPathSpaceBasepoint pBased) =
        ContinuousMap.const I
          (underTopBasepoint (underTopOfPoint (ULift.{v} Y) (ULift.up y₀))) := by
    simpa [sBased, underTopBasepoint_underTopOfPoint] using hbase
  let _ : Nonempty (BasedPathLiftingFunction pBased) := by
    refine ⟨{
      toContinuousMap := sBased.toContinuousMap
      source_eq := ?_
      proj_comp_eq := ?_
      map_basepoint := hbase'
    }⟩
    · intro x
      exact sBased.source_eq x
    · intro x
      exact sBased.proj_comp_eq x
  exact (IsBasedFibration.iff_surjective_and_nonempty_basedPathLiftingFunction pBased).2
    ⟨hsurj, inferInstance⟩
-/

/-
/-- Helper for Lemma 9.4.3: restricting a covering to the path component of the basepoint keeps
the map in the fibration class used by Lemma 7.2.4. -/

This raw path-component fibration adapter relied on compact-generation instances that an
arbitrary path component does not carry.

private theorem pathComponentRestrictIsFibration {p : C(E, B)} (hp : IsCoveringMap p) (e : E) :
    IsFibration (show C(p ⁻¹' pathComponent (p e), pathComponent (p e)) from
      p.restrictPreimage (pathComponent (p e))) := by
  -- Restrict the covering to the relevant path component and then invoke the covering-to-fibration
  -- bridge from Chapter 7.
  let r : C(p ⁻¹' pathComponent (p e), pathComponent (p e)) :=
    p.restrictPreimage (pathComponent (p e))
  have hsurj : Function.Surjective r := by
    simpa [r] using pathComponentRestrictSurjective hp e
  simpa [r] using (hp.restrictPreimage (pathComponent (p e))).isFibration hsurj

/-- Helper for Lemma 9.4.3: the path-component restriction of a covering admits a continuous path
lifting function. -/
private theorem pathComponentRestrict_nonemptyContinuousPathLiftingFunction
    {p : C(E, B)} (hp : IsCoveringMap p) (e : E) :
    Nonempty (ContinuousPathLiftingFunction
      (show C(p ⁻¹' pathComponent (p e), pathComponent (p e)) from
        p.restrictPreimage (pathComponent (p e)))) := by
  -- Unpack the criterion form of `IsFibration` for the restricted covering.
  let r : C(p ⁻¹' pathComponent (p e), pathComponent (p e)) :=
    p.restrictPreimage (pathComponent (p e))
  exact
    ((IsFibration.iff_surjective_and_nonempty_continuousPathLiftingFunction r).1
      (by simpa [r] using pathComponentRestrictIsFibration hp e)).2
-/

/-- Helper for Lemma 9.4.3: the path component of `e` maps into the path component of `p e`. -/
private theorem pathComponentSubset_preimageTargetPathComponent {p : C(E, B)} (e : E) :
    pathComponent e ⊆ p ⁻¹' pathComponent (p e) := by
  intro x hx
  rcases mem_pathComponent_iff.mp hx with ⟨γ⟩
  -- Map a path from `e` to `x` through `p` to obtain a path from `p e` to `p x`.
  exact mem_pathComponent_iff.mpr ⟨γ.map p.continuous⟩

/-- Helper for Lemma 9.4.3: after lifting both source and target to a common universe, the
path-component restriction is still a covering map. -/
private theorem pathComponentRestrict_liftedIsCoveringMap {p : C(E, B)} (hp : IsCoveringMap p)
    (e : E) :
    IsCoveringMap
      (uliftContinuousMapAcrossUniverses
        (show C(p ⁻¹' pathComponent (p e), pathComponent (p e)) from
          p.restrictPreimage (pathComponent (p e)))) := by
  let U : Set B := pathComponent (p e)
  let r : C(p ⁻¹' U, U) := p.restrictPreimage U
  have hr : IsCoveringMap r := by
    simpa [U, r] using hp.restrictPreimage U
  -- `uliftContinuousMapAcrossUniverses r` is obtained from `r` by pre- and postcomposing with
  -- the canonical `ULift` homeomorphisms.
  simpa [U, r, uliftContinuousMapAcrossUniverses, Function.comp] using
    (hr.comp_homeomorph (Homeomorph.ulift : ULift (p ⁻¹' U) ≃ₜ (p ⁻¹' U))).homeomorph_comp
      (Homeomorph.ulift.symm : U ≃ₜ ULift U)

/-- Helper for Lemma 9.4.3: the lifted path-component restriction is surjective. -/
private theorem pathComponentRestrict_liftedSurjective {p : C(E, B)} (hp : IsCoveringMap p)
    (e : E) :
    Function.Surjective
      (uliftContinuousMapAcrossUniverses
        (show C(p ⁻¹' pathComponent (p e), pathComponent (p e)) from
          p.restrictPreimage (pathComponent (p e)))) := by
  let U : Set B := pathComponent (p e)
  let r : C(p ⁻¹' U, U) := p.restrictPreimage U
  have hsurj : Function.Surjective r := by
    simpa [U, r] using pathComponentRestrictSurjective hp e
  rintro ⟨z⟩
  rcases hsurj z with ⟨y, rfl⟩
  exact ⟨ULift.up y, rfl⟩

/-
The normalized based-lift construction below depended on the obsolete topology adapter above.

/-- Helper for Lemma 9.4.3: a continuous path lift for the lifted path-component restriction sends
the canonical mapping-path-space basepoint to the constant lifted path at `e`. -/
private theorem pathComponentRestrict_basepointLift_eq_const {p : C(E, B)} (hp : IsCoveringMap p)
    (e : E)
    (s : ContinuousPathLiftingFunction
      (uliftContinuousMapAcrossUniverses
        (show C(p ⁻¹' pathComponent (p e), pathComponent (p e)) from
          p.restrictPreimage (pathComponent (p e))))) :
    s.toContinuousMap
        (basedMappingPathSpaceBasepoint
          (underTopOfPointMapAcrossUniverses
            (show C(p ⁻¹' pathComponent (p e), pathComponent (p e)) from
              p.restrictPreimage (pathComponent (p e)))
            ⟨e, mem_pathComponent_self (p e)⟩)) =
      ContinuousMap.const I (ULift.up ⟨e, mem_pathComponent_self (p e)⟩) := by
  let U : Set B := pathComponent (p e)
  let r : C(p ⁻¹' U, U) := p.restrictPreimage U
  let eU : p ⁻¹' U := ⟨e, mem_pathComponent_self (p e)⟩
  let rLift : C(ULift (p ⁻¹' U), ULift U) := uliftContinuousMapAcrossUniverses r
  let rBased := underTopOfPointMapAcrossUniverses r eU
  let γ : C(I, ULift (p ⁻¹' U)) := s.toContinuousMap (basedMappingPathSpaceBasepoint rBased)
  have hrCover : IsCoveringMap rLift := by
    simpa [U, r, rLift] using pathComponentRestrict_liftedIsCoveringMap hp e
  have hstart : γ 0 = ULift.up eU := by
    -- The lifted path starts at the chosen lifted basepoint.
    simpa [γ, rBased, basedMappingPathSpaceBasepoint] using
      s.source_eq (basedMappingPathSpaceBasepoint rBased)
  have hproj :
      rLift ∘ γ = ContinuousMap.const I (ULift.up (r eU)) := by
    -- The projected lifted path is the constant basepoint path in the target mapping path space.
    simpa [γ, rBased, basedMappingPathSpaceBasepoint] using
      s.proj_comp_eq (basedMappingPathSpaceBasepoint rBased)
  ext t
  have hconst :
      γ t = γ 0 := by
    refine hrCover.const_of_comp γ.continuous ?_ t 0
    intro t₁ t₂
    have ht₁ := congrFun hproj t₁
    have ht₂ := congrFun hproj t₂
    exact ht₁.trans ht₂.symm
  -- A path in a covering with constant projection is constant on the preconnected interval.
  simpa [γ] using congrArg (fun x : ULift (p ⁻¹' U) ↦ x.down.1) (hconst.trans hstart)

/-- Helper for Lemma 9.4.3: the lifted path-component restriction is a based fibration. -/
private theorem pathComponentRestrict_isBasedFibrationAcrossUniverses {p : C(E, B)}
    (hp : IsCoveringMap p) (e : E) :
    IsBasedFibration
      (underTopOfPointMapAcrossUniverses
        (show C(p ⁻¹' pathComponent (p e), pathComponent (p e)) from
          p.restrictPreimage (pathComponent (p e)))
        ⟨e, mem_pathComponent_self (p e)⟩) := by
  let U : Set B := pathComponent (p e)
  let r : C(p ⁻¹' U, U) := p.restrictPreimage U
  let eU : p ⁻¹' U := ⟨e, mem_pathComponent_self (p e)⟩
  let rLift : C(ULift (p ⁻¹' U), ULift U) := uliftContinuousMapAcrossUniverses r
  let rBased := underTopOfPointMapAcrossUniverses r eU
  have hsurj : Function.Surjective rLift := by
    -- The restricted covering is surjective on the chosen path component, and `ULift` preserves
    -- that surjectivity.
    simpa [U, r, rLift] using pathComponentRestrict_liftedSurjective hp e
  have hs : Nonempty (ContinuousPathLiftingFunction rLift) := by
    -- The restricted covering is already known to be an unbased fibration.
    let hFibration : IsFibration rLift := by
      have hCover : IsCoveringMap rLift := by
        simpa [U, r, rLift] using pathComponentRestrict_liftedIsCoveringMap hp e
      exact hCover.isFibration hsurj
    exact
      (IsFibration.iff_surjective_and_nonempty_continuousPathLiftingFunction rLift).1
        hFibration |>.2
  rcases hs with ⟨s⟩
  -- The owner-level adapter removes the last transport between the lifted map and the based map.
  simpa [U, r, eU, rBased, rLift] using
    underTopOfPointMapAcrossUniverses_isBasedFibrationOfContinuousPathLift
      r eU
      (by simpa [rBased, rLift] using hsurj)
      (by simpa [rBased, rLift] using s)
      (by simpa [U, r, eU, rBased] using pathComponentRestrict_basepointLift_eq_const hp e s)
-/

/-- Helper for Lemma 9.4.3: a homeomorphism preserves and reflects the path relation `Joined`. -/
private def loopSpaceMapContinuous
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (y : Y) :
    C(Ω Y y, Ω Z (f y)) :=
  ⟨fun γ ↦ γ.map f.continuous, by
    rw [continuous_induced_rng]
    change Continuous fun γ : Ω Y y ↦ (f.comp γ.toContinuousMap : C(I, Z))
    exact (ContinuousMap.continuous_postcomp f).comp continuous_induced_dom⟩

/-- Helper for Lemma 9.4.3: generalized-loop homotopies are exactly paths in the
generalized-loop space. -/
private theorem genLoopHomotopic_iff_joined
    {N : Type*} {X : Type*} [TopologicalSpace X] {x : X} {p q : Ω^ N X x} :
    GenLoop.Homotopic p q ↔ Joined p q := by
  constructor
  · rintro ⟨H⟩
    let curriedHomotopy := H.toHomotopy.curry
    -- Curry the relative homotopy into a path through the generalized-loop space.
    refine ⟨Path.mk
      ⟨fun t ↦
          (⟨curriedHomotopy t, fun a ha ↦ (H.prop t a ha).trans (p.property a ha)⟩ :
            Ω^ N X x),
        Continuous.subtype_mk curriedHomotopy.continuous ?_⟩
      ?_ ?_⟩
    · intro t a ha
      exact (H.prop t a ha).trans (p.property a ha)
    · ext a
      exact H.apply_zero a
    · ext a
      exact H.apply_one a
  · rintro ⟨γ⟩
    -- Uncurry a path in the generalized-loop space back into a relative homotopy.
    refine ⟨⟨⟨
      (ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ γ.toContinuousMap).uncurry,
      ?_, ?_⟩, ?_⟩⟩
    · intro a
      change γ 0 a = p a
      exact congrArg (fun r : Ω^ N X x ↦ r a) γ.source
    · intro a
      change γ 1 a = q a
      exact congrArg (fun r : Ω^ N X x ↦ r a) γ.target
    · intro t a ha
      exact ((γ t).property a ha).trans (p.property a ha).symm

/-- Helper for Lemma 9.4.3: a homeomorphism induces a homeomorphism on generalized-loop spaces. -/
private def genLoopHomeomorph
    {M : Type v} {Y : Type u} {Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (h : Y ≃ₜ Z) {y : Y} {z : Z} (hy : h y = z) :
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
    -- The homeomorphism and its inverse cancel pointwise.
    ext t
    simp
  right_inv p := by
    -- The inverse direction is pointwise cancellation as well.
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

/-- Helper for Lemma 9.4.3: a homeomorphism preserves and reflects the path relation `Joined`. -/
private theorem joined_iff_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) {x y : X} :
    Joined (h x) (h y) ↔ Joined x y := by
  constructor
  · rintro ⟨γ⟩
    -- Pull a path in the codomain back through the inverse homeomorphism.
    simpa using (show Joined (h.symm (h x)) (h.symm (h y)) from ⟨γ.map h.symm.continuous⟩)
  · rintro ⟨γ⟩
    -- Push a path in the domain forward through the homeomorphism.
    exact ⟨γ.map h.continuous⟩

/-- Helper for Lemma 9.4.3: a homeomorphism between generalized-loop spaces preserves and
reflects generalized-loop homotopy. -/
private theorem genLoopHomotopic_iff_of_homeomorph
    {M N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (h : Ω^ M X x ≃ₜ Ω^ N Y y) {p q : Ω^ M X x} :
    GenLoop.Homotopic (h p) (h q) ↔ GenLoop.Homotopic p q := by
  -- Translate generalized-loop homotopies to paths, compare them through the homeomorphism, and
  -- translate back.
  rw [genLoopHomotopic_iff_joined, genLoopHomotopic_iff_joined, joined_iff_homeomorph h]

/-- Helper for Lemma 9.4.3: the one-cube generalized loops are homeomorphic to ordinary loops. -/
private def oneGenLoopHomeomorph
    {X : Type u} [TopologicalSpace X] (x : X) :
    Ω^ (Fin 1) X x ≃ₜ Ω X x where
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
        change γ (t 0) = x
        calc
          γ (t 0) = γ 0 := by simpa using congrArg γ hi0
          _ = x := γ.source
      · have hi1 : t 0 = 1 := by
          fin_cases i
          simpa using hi
        change γ (t 0) = x
        calc
          γ (t 0) = γ 1 := by simpa using congrArg γ hi1
          _ = x := γ.target⟩
  left_inv p := by
    -- A `Fin 1`-indexed cube has only one coordinate.
    ext t
    have ht : t = fun _ : Fin 1 ↦ t 0 := by
      funext i
      fin_cases i
      rfl
    rw [ht]
    rfl
  right_inv γ := by
    -- The inverse simply reads the unique cube coordinate.
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

/-- Helper for Lemma 9.4.3: the inverse of `oneGenLoopHomeomorph` sends the constant loop to the
constant generalized loop. -/
@[simp] private theorem oneGenLoopHomeomorph_symm_refl
    {X : Type u} [TopologicalSpace X] (x : X) :
    (oneGenLoopHomeomorph x).symm (Path.refl x) = GenLoop.const := by
  -- Both representatives are pointwise constant at the basepoint.
  ext t
  rfl

/-- Helper for Lemma 9.4.3: the representative-level loop-space shift re-associates iterated
loops into one higher ordinary loop space. -/
private def loopSpaceRepresentativeEquivLocal
    {X : Type u} [TopologicalSpace X] (n : ℕ) (x : X) :
    Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ Ω^ (Fin (n + 1)) X x :=
  let e₁ :
      Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ₜ
        Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const :=
    genLoopHomeomorph (oneGenLoopHomeomorph x).symm (oneGenLoopHomeomorph_symm_refl x)
  let e₂ :
      Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const ≃ₜ Ω^ (Fin n ⊕ Fin 1) X x :=
    GenLoop.genLoopGenLoopEquiv x
  let e₃ : Ω^ (Fin n ⊕ Fin 1) X x ≃ₜ Ω^ (Fin (n + 1)) X x :=
    GenLoop.congr x (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
  (e₁.trans e₂).trans e₃

/-- Helper for Lemma 9.4.3: the representative-level loop-space shift preserves and reflects
generalized-loop homotopy. -/
private theorem loopSpaceRepresentativeEquivLocal_homotopic_iff
    {X : Type u} [TopologicalSpace X] (n : ℕ) (x : X)
    {p q : Ω^ (Fin n) (Ω X x) (Path.refl x)} :
    GenLoop.Homotopic (loopSpaceRepresentativeEquivLocal n x p)
        (loopSpaceRepresentativeEquivLocal n x q) ↔
      GenLoop.Homotopic p q := by
  let e :
      Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ₜ Ω^ (Fin (n + 1)) X x :=
    let e₁ :
        Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ₜ
          Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const :=
      genLoopHomeomorph (oneGenLoopHomeomorph x).symm (oneGenLoopHomeomorph_symm_refl x)
    let e₂ :
        Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const ≃ₜ Ω^ (Fin n ⊕ Fin 1) X x :=
      GenLoop.genLoopGenLoopEquiv x
    let e₃ : Ω^ (Fin n ⊕ Fin 1) X x ≃ₜ Ω^ (Fin (n + 1)) X x :=
      GenLoop.congr x (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
    (e₁.trans e₂).trans e₃
  -- Compare generalized-loop homotopies through the composite homeomorphism.
  change GenLoop.Homotopic (e p) (e q) ↔ GenLoop.Homotopic p q
  exact genLoopHomotopic_iff_of_homeomorph e

/-- Helper for Lemma 9.4.3: the standard loop-space shift identifies `π_ n(Ω X, refl)` with
`π_(n + 1)(X, x)`. -/
private def loopSpaceHomotopyGroupEquivPiSuccLocal
    {X : Type u} [TopologicalSpace X] (n : ℕ) (x : X) :
    π_ n (Ω X x) (Path.refl x) ≃ π_ (n + 1) X x :=
  -- Descend the representative-level loop-space shift to homotopy classes.
  Quotient.congr (loopSpaceRepresentativeEquivLocal n x) fun _ _ ↦
    (loopSpaceRepresentativeEquivLocal_homotopic_iff n x).symm

/-- Helper for Lemma 9.4.3: the representative-level loop-space shift commutes with
postcomposition. -/
private theorem loopSpaceRepresentativeEquivLocal_genLoopMap_eq
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (n : ℕ) {y : Y}
    (γ : Ω^ (Fin n) (Ω Y y) (Path.refl y)) :
    loopSpaceRepresentativeEquivLocal n (f y)
        (genLoopMap (loopSpaceMapContinuous f y) γ) =
      genLoopMap f (loopSpaceRepresentativeEquivLocal n y γ) := by
  -- Every component of the shift is defined pointwise, so it commutes with postcomposition.
  ext t
  rfl

/-- Helper for Lemma 9.4.3: under the loop-space shift, the induced map on higher homotopy
groups becomes the induced map on loop spaces one degree lower. -/
private theorem homotopyGroupMap_piSucc_eq_loopSpaceMapLocal
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (n : ℕ) (y : Y) :
    loopSpaceHomotopyGroupEquivPiSuccLocal n (f y) ∘
        homotopyGroupMap (loopSpaceMapContinuous f y) n (Path.refl y) =
      homotopyGroupMap f (n + 1) y ∘
        loopSpaceHomotopyGroupEquivPiSuccLocal n y := by
  -- Reduce to iterated-loop representatives, where both sides are the same postcomposition map.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  change
    Quotient.mk'
      (loopSpaceRepresentativeEquivLocal n (f y)
        (genLoopMap (loopSpaceMapContinuous f y) γ)) =
      Quotient.mk' (genLoopMap f (loopSpaceRepresentativeEquivLocal n y γ))
  exact congrArg Quotient.mk' (loopSpaceRepresentativeEquivLocal_genLoopMap_eq f n γ)

/-- Helper for Lemma 9.4.3: the lifted path component of the target basepoint is path connected.
-/
private theorem pathComponentUlift_pathConnectedSpace {p : C(E, B)} (e : E) :
    PathConnectedSpace (ULift (pathComponent (p e))) := by
  -- First use the standard path connectedness of a path component in the original universe.
  let _ : PathConnectedSpace (pathComponent (p e)) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_pathComponent (x := p e))
  -- Then transfer that structure across the canonical `ULift` surjection.
  exact ULift.up_surjective.pathConnectedSpace continuous_uliftUp

/-- Helper for Lemma 9.4.3: the raw loop-space map of the lifted path-component restriction sends
the constant loop at the lifted source basepoint to the constant loop at the lifted target
basepoint. -/
private theorem pathComponentRestrict_loopSpaceMapContinuous_refl {p : C(E, B)} (e : E) :
    let U : Set B := pathComponent (p e)
    let r : C(p ⁻¹' U, U) := p.restrictPreimage U
    let eU : p ⁻¹' U := ⟨e, mem_pathComponent_self (p e)⟩
    let rLift : C(ULift (p ⁻¹' U), ULift U) := uliftContinuousMapAcrossUniverses r
    loopSpaceMapContinuous rLift (ULift.up eU) (Path.refl (ULift.up eU)) =
      Path.refl (ULift.up (r eU)) := by
  let U : Set B := pathComponent (p e)
  let r : C(p ⁻¹' U, U) := p.restrictPreimage U
  let eU : p ⁻¹' U := ⟨e, mem_pathComponent_self (p e)⟩
  let rLift : C(ULift (p ⁻¹' U), ULift U) := uliftContinuousMapAcrossUniverses r
  -- The lifted restriction just postcomposes the constant source loop pointwise.
  ext t
  rfl

/-- Helper for Lemma 9.4.3: the actual fiber of the lifted path-component restriction is discrete.
-/
private theorem pathComponentRestrict_actualFiber_discrete {p : C(E, B)} (hp : IsCoveringMap p)
    (e : E) :
    DiscreteTopology
      (actualFiberSet
        (underTopOfPointMapAcrossUniverses
          (show C(p ⁻¹' pathComponent (p e), pathComponent (p e)) from
            p.restrictPreimage (pathComponent (p e)))
          ⟨e, mem_pathComponent_self (p e)⟩)) := by
  let U : Set B := pathComponent (p e)
  let r : C(p ⁻¹' U, U) := p.restrictPreimage U
  let eU : p ⁻¹' U := ⟨e, mem_pathComponent_self (p e)⟩
  let rLift : C(ULift (p ⁻¹' U), ULift U) := uliftContinuousMapAcrossUniverses r
  let rBased := underTopOfPointMapAcrossUniverses r eU
  have hrCover : IsCoveringMap rLift := by
    simpa [U, r, rLift] using pathComponentRestrict_liftedIsCoveringMap hp e
  -- The actual fiber is the fiber of the lifted covering over its chosen target basepoint.
  simpa [rBased, rLift, actualFiberSet, underTopBasepoint_underTopOfPoint] using
    (hrCover (ULift.up (r eU))).discreteTopology_fiber

/-- Helper for Lemma 9.4.3: exactness with a subsingleton source forces injectivity of the
middle homomorphism. -/
private theorem injective_of_mulExact_of_subsingleton_source
    {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B →* C) (hfg : Function.MulExact f g)
    [Subsingleton A] :
    Function.Injective g := by
  intro x y hxy
  have hkernel : g (x * y⁻¹) = 1 := by
    rw [g.map_mul, g.map_inv, hxy, mul_inv_cancel]
  rcases (hfg _).mp hkernel with ⟨a, ha⟩
  have ha' : f a = 1 := by
    calc
      f a = f (1 : A) := by
        congr
        exact Subsingleton.elim _ _
      _ = 1 := f.map_one
  have hquotient : x * y⁻¹ = 1 := by
    calc
      x * y⁻¹ = f a := ha.symm
      _ = 1 := ha'
  -- Cancel the trivial quotient element to recover equality of the original classes.
  calc
    x = x * 1 := by simp
    _ = x * (y⁻¹ * y) := by rw [inv_mul_cancel]
    _ = (x * y⁻¹) * y := by simp [mul_assoc]
    _ = 1 * y := by rw [hquotient]
    _ = y := by simp

/-- Helper for Lemma 9.4.3: exactness with a subsingleton target obstruction forces surjectivity
of the preceding homomorphism. -/
private theorem surjective_of_mulExact_of_subsingleton_target
    {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B → C) (hfg : Function.MulExact f g)
    [Subsingleton C] :
    Function.Surjective f := by
  intro y
  have hy : g y = 1 := by
    exact Subsingleton.elim _ _
  exact (hfg _).mp hy

/-- Helper for Lemma 9.4.3: the restriction to the basepoint path component commutes with the
ambient map on homotopy groups via the two subspace inclusions. -/
private theorem pathComponentRestrict_eStar_square {p : C(E, B)} (e : E) (q : ℕ) :
    let U : Set B := pathComponent (p e)
    let r : C(p ⁻¹' U, U) := (p.restrictPreimage U : C(p ⁻¹' U, U))
    let eU : p ⁻¹' U := ⟨e, mem_pathComponent_self (p e)⟩
    let jS : C(p ⁻¹' U, E) := pairSubspaceInclusion (p ⁻¹' U)
    let jT : C(U, B) := pairSubspaceInclusion U
    jT.eStar (q + 2) (r eU) ∘ r.eStar (q + 2) eU =
      p.eStar (q + 2) e ∘ jS.eStar (q + 2) eU := by
  -- Compare the two composites of the restriction square as continuous maps, then pass to the
  -- induced maps on homotopy groups.
  let U : Set B := pathComponent (p e)
  let r : C(p ⁻¹' U, U) := p.restrictPreimage U
  let eU : p ⁻¹' U := ⟨e, mem_pathComponent_self (p e)⟩
  let jS : C(p ⁻¹' U, E) := pairSubspaceInclusion (p ⁻¹' U)
  let jT : C(U, B) := pairSubspaceInclusion U
  change jT.eStar (q + 2) (r eU) ∘ r.eStar (q + 2) eU =
    p.eStar (q + 2) e ∘ jS.eStar (q + 2) eU
  have hsquare : jT.comp r = p.comp jS := by
    ext x
    rfl
  have hcomp_left :
      jT.eStar (q + 2) (r eU) ∘ r.eStar (q + 2) eU =
        homotopyGroupMap (jT.comp r) (q + 2) eU := by
    simpa using (homotopyGroupMap_comp r jT (q + 2) eU).symm
  have hsquare_map :
      homotopyGroupMap (jT.comp r) (q + 2) eU =
        homotopyGroupMap (p.comp jS) (q + 2) eU := by
    cases hsquare
    rfl
  have hcomp_right :
      homotopyGroupMap (p.comp jS) (q + 2) eU =
        p.eStar (q + 2) (jS eU) ∘ jS.eStar (q + 2) eU := by
    simpa using homotopyGroupMap_comp jS p (q + 2) eU
  have hbasepoint :
      p.eStar (q + 2) (jS eU) ∘ jS.eStar (q + 2) eU =
        p.eStar (q + 2) e ∘ jS.eStar (q + 2) eU := by
    rfl
  exact hcomp_left.trans (hsquare_map.trans (hcomp_right.trans hbasepoint))

/-- Lemma 9.4.3: if `p : C(E, B)` is a covering, then for every basepoint `e : E` and every
degree `n ≥ 2`, the induced map `p_* : π_ n E e → π_ n B (p e)` is bijective. This records the
source's "isomorphism" claim in the local Chapter 9 API, where the induced map `p_*` is written
as `p.eStar`. -/
theorem bijective_homotopyGroupMap {p : C(E, B)} (hp : IsCoveringMap p) (n : ℕ) (hn : 2 ≤ n)
    (e : E) :
    Function.Bijective (p.eStar n e) := by
  sorry
/-
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hn
  let U : Set B := pathComponent (p e)
  let r : C(p ⁻¹' U, U) := p.restrictPreimage U
  let eU : p ⁻¹' U := ⟨e, mem_pathComponent_self (p e)⟩
  let rLift : C(ULift (p ⁻¹' U), ULift U) := uliftContinuousMapAcrossUniverses r
  let rBased := underTopOfPointMapAcrossUniverses r eU
  -- Route correction: the path-component restriction is now packaged in the exact lifted owner
  -- needed for the LES endgame, so the remaining work is confined to exactness and transport.
  let _ : PathConnectedSpace (ULift.{u} U) := by
    simpa [U] using pathComponentUlift_pathConnectedSpace (p := p) e
  let _ : IsBasedFibration rBased := by
    simpa [U, r, eU, rBased] using
      pathComponentRestrict_isBasedFibrationAcrossUniverses (p := p) hp e
  let _ : DiscreteTopology (actualFiberSet rBased) := by
    simpa [U, r, eU, rBased] using pathComponentRestrict_actualFiber_discrete (p := p) hp e
  have hLoopRefl :
      loopSpaceMapContinuous rLift (ULift.up eU) (Path.refl (ULift.up eU)) =
        Path.refl (ULift.up (r eU)) := by
    -- This is the basepoint normalization needed to compare the raw loop map with the LES owner.
    simpa [U, r, eU, rLift] using
      pathComponentRestrict_loopSpaceMapContinuous_refl (p := p) e
  -- TODO: use `fibrationHomotopyLongExactSequence rBased` together with the discrete actual fiber
  -- to prove bijectivity of the loop-model map, then transport that bijection across
  -- `homotopyGroupMap_piSucc_eq_loopSpaceMapLocal rLift` and descend through the restriction
  -- square `pathComponentRestrict_eStar_square`.
  -- The remaining blocker is the exact owner-level bridge from the LES loop-model map
  -- `fibrationLoopTotalToBaseHomotopyGroupMap rBased q` to the raw transported loop-space map
  -- determined by `hLoopRefl`, plus the final descent from the lifted restriction back to `p.eStar`.
  sorry
-/

/-- A covering induces an injective map on each homotopy group `π_ n` in degree `n ≥ 2`. -/
theorem injective_homotopyGroupMap {p : C(E, B)} (hp : IsCoveringMap p) (n : ℕ) (hn : 2 ≤ n)
    (e : E) :
    Function.Injective (p.eStar n e) :=
  (hp.bijective_homotopyGroupMap n hn e).injective

/-- A covering induces a surjective map on each homotopy group `π_ n` in degree `n ≥ 2`. -/
theorem surjective_homotopyGroupMap {p : C(E, B)} (hp : IsCoveringMap p) (n : ℕ) (hn : 2 ≤ n)
    (e : E) :
    Function.Surjective (p.eStar n e) :=
  (hp.bijective_homotopyGroupMap n hn e).surjective

end IsCoveringMap
