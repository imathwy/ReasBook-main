import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Construction_16_4_3

open CategoryTheory Simplicial

universe u

section Algebraic

variable (G : Type u) [Group G]

-- Semantic recall via `lean_leansearch`: Definition 16.4.2 fixes simplicial spaces as
-- `CategoryTheory.SimplicialObject TopCat`, while `nerve (SingleObj G)` remains a useful
-- set-level companion for the tuple formulas.

/-- Recursively rebuild the nerve-model `n`-simplex of `BG` from its successive edge labels
in `G`. -/
def groupBarConstructionNerveSimplexOfTuple (n : ℕ) :
    (Fin n → G) → ComposableArrows (SingleObj G) n :=
  match n with
  | 0 => fun _ ↦ ComposableArrows.mk₀ (SingleObj.star G)
  | n + 1 => fun g ↦
      let tail : Fin n → G := fun i ↦ g i.succ
      let F := groupBarConstructionNerveSimplexOfTuple n tail
      F.precomp
        (show F.left ⟶ F.left from SingleObj.toEnd G (g 0))

/-- Helper for Construction 16.5.1: in the simplex reconstructed from a tuple
`g : Fin n → G`, the edge from `i` to `i + 1` is labeled by `g i`. -/
private theorem groupBarConstructionNerveSimplexOfTuple_edge
    (n : ℕ) (g : Fin n → G) (i : Fin n) :
    (groupBarConstructionNerveSimplexOfTuple G n g).map'
        i.1 (i.1 + 1) (Nat.le_succ i.1) (Nat.succ_le_of_lt i.2) =
      SingleObj.toEnd G (g i) := by
  induction n with
  | zero =>
      exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          -- The recursive construction inserts the first edge by precomposition.
          simp [groupBarConstructionNerveSimplexOfTuple]
      | succ i =>
          -- All later edges come from the recursively reconstructed tail simplex.
          simpa [groupBarConstructionNerveSimplexOfTuple] using
            ih (fun j ↦ g j.succ) i

/-- The inverse map in `groupBarConstructionNSimplicesEquiv` is a left inverse to the edge-label
map on `n`-simplices. -/
theorem groupBarConstructionNSimplicesEquiv_leftInv (n : ℕ) :
    Function.LeftInverse (groupBarConstructionNerveSimplexOfTuple G n)
      (fun x i ↦ x.map' i.1 (i.1 + 1) (Nat.le_succ i.1) (Nat.succ_le_of_lt i.2)) := by
  intro x
  let y :=
    groupBarConstructionNerveSimplexOfTuple G n
      (fun j ↦ x.map' j.1 (j.1 + 1) (Nat.le_succ j.1) (Nat.succ_le_of_lt j.2))
  let hObj : ∀ i, y.obj i = x.obj i := fun i ↦ by
    cases y.obj i
    cases x.obj i
    rfl
  -- We compare simplices by their consecutive edges, which determine simplices in a one-object
  -- category.
  refine ComposableArrows.ext hObj ?_
  intro i hi
  -- The reconstructed simplex has exactly the recorded edge labels.
  refine
    (CategoryTheory.conj_eqToHom_iff_heq
      (y.map' i (i + 1) (Nat.le_succ i) (Nat.succ_le_of_lt hi))
      (x.map' i (i + 1) (Nat.le_succ i) (Nat.succ_le_of_lt hi))
      (hObj ⟨i, Nat.lt_succ_of_lt hi⟩)
      (hObj ⟨i + 1, Nat.succ_lt_succ hi⟩)).2 ?_
  simpa [y, SingleObj.toEnd_def] using
    groupBarConstructionNerveSimplexOfTuple_edge G n
      (fun j ↦ x.map' j.1 (j.1 + 1) (Nat.le_succ j.1) (Nat.succ_le_of_lt j.2))
      ⟨i, hi⟩

/-- The inverse map in `groupBarConstructionNSimplicesEquiv` is a right inverse to the edge-label
map on `n`-simplices. -/
theorem groupBarConstructionNSimplicesEquiv_rightInv (n : ℕ) :
    Function.RightInverse (groupBarConstructionNerveSimplexOfTuple G n)
      (fun x i ↦ x.map' i.1 (i.1 + 1) (Nat.le_succ i.1) (Nat.succ_le_of_lt i.2)) := by
  intro g
  -- Each coordinate of the tuple recovered from the reconstructed simplex is the original one.
  funext i
  simpa [SingleObj.toEnd_def] using
    groupBarConstructionNerveSimplexOfTuple_edge G n g i

/-- The set-level `n`-simplex of the one-object nerve is canonically equivalent to `G^n`. -/
def groupBarConstructionNSimplicesEquiv (n : ℕ) :
    (nerve (SingleObj G)) _⦋n⦌ ≃ (Fin n → G) :=
  { toFun := fun x i ↦ x.map' i.1 (i.1 + 1) (Nat.le_succ i.1) (Nat.succ_le_of_lt i.2)
    invFun := groupBarConstructionNerveSimplexOfTuple G n
    left_inv := groupBarConstructionNSimplicesEquiv_leftInv G n
    right_inv := groupBarConstructionNSimplicesEquiv_rightInv G n }

/-- The forward map of `groupBarConstructionNSimplicesEquiv` records the successive edge labels of
an `n`-simplex in the nerve of `SingleObj G`. -/
@[simp] theorem groupBarConstructionNSimplicesEquiv_apply
    (n : ℕ) (x : (nerve (SingleObj G)) _⦋n⦌) (i : Fin n) :
    groupBarConstructionNSimplicesEquiv G n x i =
      x.map' i.1 (i.1 + 1) (Nat.le_succ i.1) (Nat.succ_le_of_lt i.2) := by
  -- The forward equivalence was defined by taking successive edge labels.
  rfl

/-- The inverse map of `groupBarConstructionNSimplicesEquiv` reconstructs a simplex from its
tuple of edge labels. -/
@[simp] theorem groupBarConstructionNSimplicesEquiv_symm_apply
    (n : ℕ) (g : Fin n → G) :
    (groupBarConstructionNSimplicesEquiv G n).symm g =
      groupBarConstructionNerveSimplexOfTuple G n g := by
  -- The inverse equivalence was defined by recursive reconstruction from the tuple.
  rfl

/-- The `0`-th face map in the bar construction deletes the first coordinate. -/
def groupBarConstructionFaceZero (n : ℕ) :
    (Fin (n + 1) → G) → (Fin n → G) :=
  fun g k ↦ g k.succ

/-- The higher face maps in the bar construction multiply adjacent coordinates. -/
def groupBarConstructionFaceSucc (n : ℕ) (i : Fin (n + 1)) :
    (Fin (n + 1) → G) → (Fin n → G) :=
  Fin.contractNth i (fun x y ↦ y * x)

/-- The degeneracy maps in the bar construction insert the identity element. -/
def groupBarConstructionDegeneracy (n : ℕ) (i : Fin (n + 1)) :
    (Fin n → G) → (Fin (n + 1) → G) :=
  fun g ↦ i.insertNth 1 g

end Algebraic

section Topological

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- The space of `n`-simplices in the bar construction of `G`. -/
abbrev groupBarConstructionObj (n : ℕ) : TopCat :=
  TopCat.of (Fin n → G)

/-- The face map deleting the first coordinate is continuous. -/
private theorem groupBarConstructionFaceZero_continuous (n : ℕ) :
    Continuous (groupBarConstructionFaceZero G n) := by
  -- Each output coordinate is just a shifted coordinate projection.
  refine continuous_pi ?_
  intro k
  simpa [groupBarConstructionFaceZero] using
    (continuous_apply k.succ : Continuous fun g : Fin (n + 1) → G ↦ g k.succ)

/-- The degeneracy maps inserting the identity are continuous. -/
private theorem groupBarConstructionDegeneracy_continuous (n : ℕ) (i : Fin (n + 1)) :
    Continuous (groupBarConstructionDegeneracy G n i) := by
  -- Each output coordinate is either the inserted identity or one of the original coordinates.
  refine continuous_pi ?_
  intro j
  induction j using i.succAboveCases with
  | x =>
      simpa [groupBarConstructionDegeneracy] using
        (continuous_const : Continuous fun _ : Fin n → G ↦ (1 : G))
  | p j =>
      simpa [groupBarConstructionDegeneracy] using
        (continuous_apply j : Continuous fun g : Fin n → G ↦ g j)

/-- The `0`-th face map of the bar construction as a morphism in `TopCat`. -/
abbrev groupBarConstructionFaceZeroHom (n : ℕ) :
    groupBarConstructionObj G (n + 1) ⟶ groupBarConstructionObj G n :=
  TopCat.ofHom ⟨groupBarConstructionFaceZero G n, groupBarConstructionFaceZero_continuous G n⟩

/-- The degeneracy maps of the bar construction as morphisms in `TopCat`. -/
abbrev groupBarConstructionDegeneracyHom (n : ℕ) (i : Fin (n + 1)) :
    groupBarConstructionObj G n ⟶ groupBarConstructionObj G (n + 1) :=
  TopCat.ofHom ⟨groupBarConstructionDegeneracy G n i,
    groupBarConstructionDegeneracy_continuous G n i⟩

section TopologicalGroup

variable [IsTopologicalGroup G]

/-- The simplicial transition map on tuple spaces, transported from the one-object nerve. -/
private def groupBarConstructionMap {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (Fin Δ.unop.len → G) → (Fin Δ'.unop.len → G) :=
  fun g ↦
    groupBarConstructionNSimplicesEquiv G Δ'.unop.len
      ((nerve (SingleObj G)).map f
        ((groupBarConstructionNSimplicesEquiv G Δ.unop.len).symm g))

/-- Helper for Construction 16.5.1: transporting along the identity simplex map acts trivially on
tuple coordinates. -/
private theorem groupBarConstructionMap_id {Δ : SimplexCategoryᵒᵖ} :
    groupBarConstructionMap G (𝟙 Δ) = id := by
  funext g
  -- The nerve action is functorial, and the tuple equivalence immediately cancels.
  simpa [groupBarConstructionMap] using
    (groupBarConstructionNSimplicesEquiv G Δ.unop.len).apply_symm_apply g

/-- Helper for Construction 16.5.1: transporting along a composite simplex map is the composite
of the transported tuple maps. -/
private theorem groupBarConstructionMap_comp
    {Δ₀ Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (f : Δ₀ ⟶ Δ₁) (g : Δ₁ ⟶ Δ₂) :
    groupBarConstructionMap G (f ≫ g) =
      groupBarConstructionMap G g ∘ groupBarConstructionMap G f := by
  funext x
  -- Functoriality of the nerve transport matches ordinary function composition on tuples.
  simp only [groupBarConstructionMap, FunctorToTypes.map_comp_apply, Function.comp_apply]
  exact congrArg (groupBarConstructionNSimplicesEquiv G Δ₂.unop.len)
    (congrArg ((nerve (SingleObj G)).map g)
      ((groupBarConstructionNSimplicesEquiv G Δ₁.unop.len).symm_apply_apply
        ((nerve (SingleObj G)).map f
          ((groupBarConstructionNSimplicesEquiv G Δ₀.unop.len).symm x))).symm)

/-- Helper for Construction 16.5.1: the transported face map `δ 0` is the tuple map that forgets
the first coordinate. -/
private theorem groupBarConstructionMap_deltaZero (n : ℕ) :
    groupBarConstructionMap G ((SimplexCategory.δ (0 : Fin (n + 2))).op) =
      groupBarConstructionFaceZero G n := by
  funext g
  funext k
  -- The `δ 0` simplex operator forgets the first edge in the nerve model.
  change groupBarConstructionNSimplicesEquiv G n
      ((nerve (SingleObj G)).δ (0 : Fin (n + 2))
        ((groupBarConstructionNSimplicesEquiv G (n + 1)).symm g)) k =
    groupBarConstructionFaceZero G n g k
  rw [CategoryTheory.nerve.δ₀_eq]
  simpa [groupBarConstructionFaceZero, groupBarConstructionNSimplicesEquiv_symm_apply,
    SingleObj.toEnd_def] using
    groupBarConstructionNerveSimplexOfTuple_edge G (n + 1) g k.succ

/-- Helper for Construction 16.5.1: in the nerve, the `k`-th consecutive edge after applying
`δ i.succ` is the original edge between the corresponding `succAbove` vertices. -/
private theorem nerveDeltaSuccConsecutiveMap
    (n : ℕ) (i : Fin (n + 1)) (x : ComposableArrows (SingleObj G) (n + 1)) (k : Fin n) :
    ((nerve (SingleObj G)).δ i.succ x).map'
        k.1 (k.1 + 1) (Nat.le_succ k.1) (Nat.succ_le_of_lt k.2) =
      x.map'
        (i.succ.succAbove k.castSucc).1
        (i.succ.succAbove k.succ).1
        (by
          change i.succ.succAbove k.castSucc ≤ i.succ.succAbove k.succ
          exact (Fin.strictMono_succAbove i.succ k.castSucc_lt_succ).le)
        (Nat.le_of_lt_succ (i.succ.succAbove k.succ).2) := by
  -- Route correction: normalize the transported consecutive edge once at the owner level.
  rfl

/-- Helper for Construction 16.5.1: before the deleted vertex in `δ i.succ`, the normalized source
vertices are the unchanged consecutive vertices. -/
private theorem deltaSuccIndices_lt
    (i : Fin (n + 1)) (k : Fin n) (h : k.castSucc < i) :
    i.succ.succAbove k.castSucc = k.castSucc.castSucc ∧
      i.succ.succAbove k.succ = k.castSucc.succ := by
  constructor
  · rw [Fin.succAbove_succ_of_le i k.castSucc h.le]
  · have hs : k.succ ≤ i := by simpa using h
    rw [Fin.succAbove_succ_of_le i k.succ hs, Fin.succ_castSucc]

/-- Helper for Construction 16.5.1: at the deleted vertex in `δ i.succ`, the normalized source
vertices are the two consecutive vertices around the composite edge. -/
private theorem deltaSuccIndices_eq (k : Fin n) :
    k.castSucc.succ.succAbove k.castSucc = k.castSucc.castSucc ∧
      k.castSucc.succ.succAbove k.succ = k.succ.succ := by
  constructor
  · simpa using (Fin.succAbove_succ_self k.castSucc)
  · simpa using (Fin.succAbove_succ_of_lt k.castSucc k.succ k.castSucc_lt_succ)

/-- Helper for Construction 16.5.1: after the deleted vertex in `δ i.succ`, the normalized source
vertices are shifted one step to the right. -/
private theorem deltaSuccIndices_gt
    (i : Fin (n + 1)) (k : Fin n) (h : i < k.castSucc) :
    i.succ.succAbove k.castSucc = k.castSucc.succ ∧
      i.succ.succAbove k.succ = k.succ.succ := by
  constructor
  · rw [Fin.succAbove_succ_of_lt i k.castSucc h, Fin.succ_castSucc]
  · rw [Fin.succAbove_succ_of_lt i k.succ (lt_of_lt_of_le h k.castSucc_le_succ)]

/-- Helper for Construction 16.5.1: in `ComposableArrows (SingleObj G)`, the map `x.map' i j`
depends only on the endpoint indices, not on the specific proof terms witnessing the bounds. -/
private theorem singleObjMap'_congr
    {m : ℕ} (x : ComposableArrows (SingleObj G) m)
    {i i' j j' : ℕ} (hi : i = i') (hj : j = j')
    {hij : i ≤ j} {hjm : j ≤ m} {hij' : i' ≤ j'} {hjm' : j' ≤ m} :
    x.map' i j hij hjm = x.map' i' j' hij' hjm' := by
  -- After identifying the endpoints, proof irrelevance removes the remaining bound witnesses.
  subst hi
  subst hj
  have h₁ : hij = hij' := Subsingleton.elim _ _
  have h₂ : hjm = hjm' := Subsingleton.elim _ _
  subst h₁
  subst h₂
  rfl

/-- Helper for Construction 16.5.1: after transporting along `δ i.succ`, the `k`-th consecutive
edge is the `k`-th coordinate of the explicit higher face map. -/
private theorem groupBarConstructionDeltaSuccEdgeFormula
    (n : ℕ) (i : Fin (n + 1)) (g : Fin (n + 1) → G) (k : Fin n) :
    ((nerve (SingleObj G)).δ i.succ ((groupBarConstructionNSimplicesEquiv G (n + 1)).symm g)).map'
        k.1 (k.1 + 1) (Nat.le_succ k.1) (Nat.succ_le_of_lt k.2) =
      SingleObj.toEnd G ((groupBarConstructionFaceSucc G n i g) k) := by
  -- Route correction: normalize the transported edge first, then split into the three tuple cases.
  rw [groupBarConstructionNSimplicesEquiv_symm_apply, nerveDeltaSuccConsecutiveMap]
  rcases lt_trichotomy (k : ℕ) i with hlt | heq | hgt
  · -- Before the deleted vertex, the consecutive edge is unchanged.
    rcases deltaSuccIndices_lt i k hlt with ⟨hsrc, htgt⟩
    have hsrc' : (i.succ.succAbove k.castSucc).1 = k.castSucc.1 := by
      simpa using congrArg Fin.val hsrc
    have htgt' : (i.succ.succAbove k.succ).1 = k.succ.1 := by
      simpa using congrArg Fin.val htgt
    calc
      (groupBarConstructionNerveSimplexOfTuple G (n + 1) g).map'
          (i.succ.succAbove k.castSucc).1
          (i.succ.succAbove k.succ).1
          (by
            change i.succ.succAbove k.castSucc ≤ i.succ.succAbove k.succ
            exact (Fin.strictMono_succAbove i.succ k.castSucc_lt_succ).le)
          (Nat.le_of_lt_succ (i.succ.succAbove k.succ).2) =
          (groupBarConstructionNerveSimplexOfTuple G (n + 1) g).map'
            k.castSucc.1 k.succ.1 (Nat.le_succ k.1) (Nat.le_of_lt k.succ.2) := by
            exact
              singleObjMap'_congr (G := G)
                (x := groupBarConstructionNerveSimplexOfTuple G (n + 1) g) hsrc' htgt'
      _ = SingleObj.toEnd G (g k.castSucc) := by
            exact groupBarConstructionNerveSimplexOfTuple_edge G (n + 1) g k.castSucc
      _ = SingleObj.toEnd G ((groupBarConstructionFaceSucc G n i g) k) := by
            simp [groupBarConstructionFaceSucc, Fin.contractNth_apply_of_lt, hlt,
              SingleObj.toEnd_def]
  · -- At the deleted vertex, the new edge is the composite of the two adjacent old edges.
    have hi : i = k.castSucc := by
      apply Fin.ext
      simpa using heq.symm
    subst hi
    rcases deltaSuccIndices_eq k with ⟨hsrc, htgt⟩
    have hsrc' : (k.castSucc.succ.succAbove k.castSucc).1 = k.castSucc.1 := by
      simpa using congrArg Fin.val hsrc
    have htgt' : (k.castSucc.succ.succAbove k.succ).1 = k.succ.1 + 1 := by
      simpa using congrArg Fin.val htgt
    calc
      (groupBarConstructionNerveSimplexOfTuple G (n + 1) g).map'
          (k.castSucc.succ.succAbove k.castSucc).1
          (k.castSucc.succ.succAbove k.succ).1
          (by
            change k.castSucc.succ.succAbove k.castSucc ≤ k.castSucc.succ.succAbove k.succ
            exact (Fin.strictMono_succAbove k.castSucc.succ k.castSucc_lt_succ).le)
          (Nat.le_of_lt_succ (k.castSucc.succ.succAbove k.succ).2) =
          (groupBarConstructionNerveSimplexOfTuple G (n + 1) g).map'
            k.castSucc.1 (k.succ.1 + 1)
            (by simpa using Nat.le_succ_of_le (Nat.le_succ k.1))
            (Nat.succ_le_of_lt k.succ.2) := by
            exact
              singleObjMap'_congr (G := G)
                (x := groupBarConstructionNerveSimplexOfTuple G (n + 1) g) hsrc' htgt'
      _ =
          (groupBarConstructionNerveSimplexOfTuple G (n + 1) g).map'
            k.castSucc.1 k.succ.1 (Nat.le_succ k.1) (Nat.le_of_lt k.succ.2) ≫
          (groupBarConstructionNerveSimplexOfTuple G (n + 1) g).map'
            k.succ.1 (k.succ.1 + 1) (Nat.le_succ k.succ.1) (Nat.succ_le_of_lt k.succ.2) := by
            simpa using
              (ComposableArrows.map'_comp
                (F := groupBarConstructionNerveSimplexOfTuple G (n + 1) g)
                (i := k.castSucc.1)
                (j := k.succ.1)
                (k := k.succ.1 + 1)
                (hij := Nat.le_succ k.1)
                (hjk := Nat.le_succ k.succ.1)
                (hk := Nat.succ_le_of_lt k.succ.2))
      _ = SingleObj.toEnd G (g k.castSucc) ≫ SingleObj.toEnd G (g k.succ) := by
            have hEdgeCast :
                (groupBarConstructionNerveSimplexOfTuple G (n + 1) g).map'
                    k.castSucc.1 k.succ.1 (Nat.le_succ k.1) (Nat.le_of_lt k.succ.2) =
                  SingleObj.toEnd G (g k.castSucc) := by
              calc
                (groupBarConstructionNerveSimplexOfTuple G (n + 1) g).map'
                    k.castSucc.1 k.succ.1 (Nat.le_succ k.1) (Nat.le_of_lt k.succ.2) =
                    (groupBarConstructionNerveSimplexOfTuple G (n + 1) g).map'
                      k.castSucc.1 (k.castSucc.1 + 1)
                      (Nat.le_succ k.castSucc.1) (Nat.succ_le_of_lt k.castSucc.2) := by
                        exact
                          singleObjMap'_congr (G := G)
                            (x := groupBarConstructionNerveSimplexOfTuple G (n + 1) g) rfl rfl
                _ = SingleObj.toEnd G (g k.castSucc) := by
                      exact groupBarConstructionNerveSimplexOfTuple_edge G (n + 1) g k.castSucc
            rw [hEdgeCast, groupBarConstructionNerveSimplexOfTuple_edge G (n + 1) g k.succ]
            rfl
      _ = SingleObj.toEnd G ((groupBarConstructionFaceSucc G n k.castSucc g) k) := by
            simp [groupBarConstructionFaceSucc, Fin.contractNth_apply_of_eq,
              CategoryTheory.SingleObj.comp_as_mul, SingleObj.toEnd_def]
  · -- After the deleted vertex, the surviving edge is shifted one step to the right.
    rcases deltaSuccIndices_gt i k hgt with ⟨hsrc, htgt⟩
    have hsrc' : (i.succ.succAbove k.castSucc).1 = k.succ.1 := by
      simpa using congrArg Fin.val hsrc
    have htgt' : (i.succ.succAbove k.succ).1 = k.succ.1 + 1 := by
      simpa using congrArg Fin.val htgt
    calc
      (groupBarConstructionNerveSimplexOfTuple G (n + 1) g).map'
          (i.succ.succAbove k.castSucc).1
          (i.succ.succAbove k.succ).1
          (by
            change i.succ.succAbove k.castSucc ≤ i.succ.succAbove k.succ
            exact (Fin.strictMono_succAbove i.succ k.castSucc_lt_succ).le)
          (Nat.le_of_lt_succ (i.succ.succAbove k.succ).2) =
          (groupBarConstructionNerveSimplexOfTuple G (n + 1) g).map'
            k.succ.1 (k.succ.1 + 1) (Nat.le_succ k.succ.1) (Nat.succ_le_of_lt k.succ.2) := by
            exact
              singleObjMap'_congr (G := G)
                (x := groupBarConstructionNerveSimplexOfTuple G (n + 1) g) hsrc' htgt'
      _ = SingleObj.toEnd G (g k.succ) := by
            exact groupBarConstructionNerveSimplexOfTuple_edge G (n + 1) g k.succ
      _ = SingleObj.toEnd G ((groupBarConstructionFaceSucc G n i g) k) := by
            simp [groupBarConstructionFaceSucc, Fin.contractNth_apply_of_gt, hgt,
              SingleObj.toEnd_def]

/-- Helper for Construction 16.5.1: transporting along `δ i.succ` agrees with the explicit higher
face map on tuples. -/
private theorem groupBarConstructionMap_deltaSucc (n : ℕ) (i : Fin (n + 1)) :
    groupBarConstructionMap G ((SimplexCategory.δ i.succ).op) =
      groupBarConstructionFaceSucc G n i := by
  funext g
  funext k
  -- Reduce tuple coordinates to consecutive edges in the transported nerve simplex.
  exact groupBarConstructionDeltaSuccEdgeFormula G n i g k

/-- Helper for Construction 16.5.1: in the nerve, the `j`-th consecutive edge after applying
`σ i` is the original edge between the corresponding `predAbove` vertices. -/
private theorem nerveSigmaConsecutiveMap
    (n : ℕ) (i : Fin (n + 1)) (x : ComposableArrows (SingleObj G) n) (j : Fin (n + 1)) :
    ((nerve (SingleObj G)).σ i x).map'
        j.1 (j.1 + 1) (Nat.le_succ j.1) (Nat.succ_le_of_lt j.2) =
      x.map'
        (i.predAbove j.castSucc).1
        (i.predAbove j.succ).1
        (Fin.predAbove_right_monotone i j.castSucc_le_succ)
        (Nat.le_of_lt_succ (i.predAbove j.succ).2) := by
  -- Route correction: normalize the transported consecutive edge once at the owner level.
  rfl

/-- Helper for Construction 16.5.1: the repeated vertex created by `σ i` becomes a constant edge. -/
private theorem sigmaPredAbove_self (i : Fin (n + 1)) :
    i.predAbove i.castSucc = i ∧ i.predAbove i.succ = i := by
  constructor
  · simpa [Fin.castPred_castSucc] using
      (Fin.predAbove_of_le_castSucc i i.castSucc le_rfl)
  · simpa [Fin.pred_succ] using
      (Fin.predAbove_of_castSucc_lt i i.succ i.castSucc_lt_succ)

/-- Helper for Construction 16.5.1: away from the repeated vertex, the normalized source vertices
for `σ i` recover the original consecutive edge indexed by `k`. -/
private theorem sigmaPredAbove_succAbove
    (i : Fin (n + 1)) (k : Fin n) :
    i.predAbove (i.succAbove k).castSucc = k.castSucc ∧
      i.predAbove (i.succAbove k).succ = k.succ := by
  rcases lt_or_ge k.castSucc i with hki | hik
  · constructor
    · rw [Fin.succAbove_of_castSucc_lt _ _ hki]
      simpa [Fin.castPred_castSucc] using
        (Fin.predAbove_of_le_castSucc i k.castSucc.castSucc (by simpa using hki.le))
    · rw [Fin.succAbove_of_castSucc_lt _ _ hki, Fin.succ_castSucc]
      simpa [Fin.castPred_castSucc] using
        (Fin.predAbove_of_le_castSucc i k.succ.castSucc (by simpa using hki))
  · constructor
    · rw [Fin.succAbove_of_le_castSucc _ _ hik, ← Fin.succ_castSucc]
      simpa [Fin.pred_succ] using
        (Fin.predAbove_of_castSucc_lt i k.castSucc.succ (by simpa using hik))
    · rw [Fin.succAbove_of_le_castSucc _ _ hik]
      simpa [Fin.pred_succ] using
        (Fin.predAbove_of_castSucc_lt i k.succ.succ
          (by simpa using le_trans hik k.castSucc_le_succ))

/-- Helper for Construction 16.5.1: after transporting along `σ i`, the `j`-th consecutive edge
is the `j`-th coordinate of the explicit degeneracy map. -/
private theorem groupBarConstructionSigmaEdgeFormula
    (n : ℕ) (i : Fin (n + 1)) (g : Fin n → G) (j : Fin (n + 1)) :
    ((nerve (SingleObj G)).σ i ((groupBarConstructionNSimplicesEquiv G n).symm g)).map'
        j.1 (j.1 + 1) (Nat.le_succ j.1) (Nat.succ_le_of_lt j.2) =
      SingleObj.toEnd G ((groupBarConstructionDegeneracy G n i g) j) := by
  -- Route correction: normalize the transported edge, then split into the repeated and off-pivot
  -- cases given by `succAboveCases`.
  rw [groupBarConstructionNSimplicesEquiv_symm_apply, nerveSigmaConsecutiveMap]
  induction j using i.succAboveCases with
  | x =>
      -- The repeated vertex contributes the identity edge.
      rcases sigmaPredAbove_self (i := i) with ⟨hsrc, htgt⟩
      have hsrc' : (i.predAbove i.castSucc).1 = i.1 := by
        simpa using congrArg Fin.val hsrc
      have htgt' : (i.predAbove i.succ).1 = i.1 := by
        simpa using congrArg Fin.val htgt
      calc
        (groupBarConstructionNerveSimplexOfTuple G n g).map'
            (i.predAbove i.castSucc).1
            (i.predAbove i.succ).1
            (Fin.predAbove_right_monotone i i.castSucc_le_succ)
            (Nat.le_of_lt_succ (i.predAbove i.succ).2) =
            (groupBarConstructionNerveSimplexOfTuple G n g).map'
              i.1 i.1 (Nat.le_refl i.1) (Nat.le_of_lt_succ i.2) := by
              exact
                singleObjMap'_congr (G := G)
                  (x := groupBarConstructionNerveSimplexOfTuple G n g) hsrc' htgt'
        _ = SingleObj.toEnd G ((groupBarConstructionDegeneracy G n i g) i) := by
              rw [ComposableArrows.map'_self
                (F := groupBarConstructionNerveSimplexOfTuple G n g)
                (i := i.1)
                (hi := Nat.le_of_lt_succ i.2)]
              simp [groupBarConstructionDegeneracy, SingleObj.toEnd_def,
                CategoryTheory.SingleObj.id_as_one]
  | p k =>
      -- Away from the repeated vertex, the consecutive edge is unchanged.
      rcases sigmaPredAbove_succAbove i k with ⟨hsrc, htgt⟩
      have hsrc' : (i.predAbove (i.succAbove k).castSucc).1 = k.1 := by
        simpa using congrArg Fin.val hsrc
      have htgt' : (i.predAbove (i.succAbove k).succ).1 = k.1 + 1 := by
        simpa using congrArg Fin.val htgt
      calc
        (groupBarConstructionNerveSimplexOfTuple G n g).map'
            (i.predAbove (i.succAbove k).castSucc).1
            (i.predAbove (i.succAbove k).succ).1
            (Fin.predAbove_right_monotone i (i.succAbove k).castSucc_le_succ)
            (Nat.le_of_lt_succ (i.predAbove (i.succAbove k).succ).2) =
            (groupBarConstructionNerveSimplexOfTuple G n g).map'
              k.1 (k.1 + 1) (Nat.le_succ k.1) (Nat.succ_le_of_lt k.2) := by
              exact
                singleObjMap'_congr (G := G)
                  (x := groupBarConstructionNerveSimplexOfTuple G n g) hsrc' htgt'
        _ = SingleObj.toEnd G ((groupBarConstructionDegeneracy G n i g) (i.succAbove k)) := by
              simpa [groupBarConstructionDegeneracy, SingleObj.toEnd_def] using
                groupBarConstructionNerveSimplexOfTuple_edge G n g k

/-- Helper for Construction 16.5.1: transporting along `σ i` agrees with the explicit degeneracy
map on tuples. -/
private theorem groupBarConstructionMap_sigma (n : ℕ) (i : Fin (n + 1)) :
    groupBarConstructionMap G ((SimplexCategory.σ i).op) =
      groupBarConstructionDegeneracy G n i := by
  funext g
  funext j
  -- Reduce tuple coordinates to consecutive edges in the transported nerve simplex.
  exact groupBarConstructionSigmaEdgeFormula G n i g j

/-- The transported simplicial transition maps in the bar construction are continuous. -/
-- TODO: Close the abstract continuity argument by combining the generator rewrites
-- `groupBarConstructionMap_deltaZero`, `groupBarConstructionMap_deltaSucc`, and
-- `groupBarConstructionMap_sigma` with `SimplexCategory.morphismProperty_eq_top`.
private theorem groupBarConstructionMap_continuous {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    Continuous (groupBarConstructionMap G f) := by
  let W : MorphismProperty SimplexCategory := fun _ _ h ↦
    Continuous (groupBarConstructionMap G h.op)
  -- Close continuity on all simplex maps from the standard generators.
  have hFaceSucc : ∀ (n : ℕ) (i : Fin (n + 1)), Continuous (groupBarConstructionFaceSucc G n i) := by
    intro n i
    refine continuous_pi ?_
    intro k
    rcases lt_trichotomy (k : ℕ) i with hlt | heq | hgt
    · simpa [groupBarConstructionFaceSucc, Fin.contractNth_apply_of_lt, hlt] using
        (continuous_apply k.castSucc : Continuous fun g : Fin (n + 1) → G ↦ g k.castSucc)
    · simpa [groupBarConstructionFaceSucc, Fin.contractNth_apply_of_eq, heq] using
        ((continuous_apply k.succ : Continuous fun g : Fin (n + 1) → G ↦ g k.succ).mul
          (continuous_apply k.castSucc : Continuous fun g : Fin (n + 1) → G ↦ g k.castSucc))
    · simpa [groupBarConstructionFaceSucc, Fin.contractNth_apply_of_gt, hgt] using
        (continuous_apply k.succ : Continuous fun g : Fin (n + 1) → G ↦ g k.succ)
  letI : W.IsMultiplicative := {
    id_mem := by
      intro Δ
      simpa [W, groupBarConstructionMap_id] using
        (continuous_id : Continuous (id : (Fin Δ.len → G) → Fin Δ.len → G))
    comp_mem := by
      intro _ _ _ h₁ h₂ hh₁ hh₂
      simpa [W, groupBarConstructionMap_comp] using hh₁.comp hh₂ }
  have hTop : W = ⊤ := by
    refine SimplexCategory.morphismProperty_eq_top W ?_ ?_
    · intro n i
      cases i using Fin.cases with
      | zero =>
          simpa [W, groupBarConstructionMap_deltaZero] using
            groupBarConstructionFaceZero_continuous G n
      | succ i =>
          simpa [W, groupBarConstructionMap_deltaSucc] using
            hFaceSucc n i
    · intro n i
      simpa [W, groupBarConstructionMap_sigma] using
        groupBarConstructionDegeneracy_continuous G n i
  have hf : W f.unop := by
    simp [hTop]
  simpa [W] using hf

/-- The simplicial transition map in the bar construction, regarded as a morphism in `TopCat`. -/
private def groupBarConstructionHom {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    groupBarConstructionObj G Δ.unop.len ⟶ groupBarConstructionObj G Δ'.unop.len :=
  TopCat.ofHom ⟨groupBarConstructionMap G f, groupBarConstructionMap_continuous G f⟩

/-- The transported simplicial transition map respects identities. -/
private theorem groupBarConstructionHom_id (Δ : SimplexCategoryᵒᵖ) :
    groupBarConstructionHom G (𝟙 Δ) = 𝟙 (groupBarConstructionObj G Δ.unop.len) := by
  -- Equality in `TopCat` reduces to equality of the underlying continuous maps.
  apply TopCat.hom_ext
  ext g
  simpa [groupBarConstructionHom, groupBarConstructionMap_id]

/-- The transported simplicial transition map respects composition. -/
private theorem groupBarConstructionHom_comp {Δ₀ Δ₁ Δ₂ : SimplexCategoryᵒᵖ}
    (f : Δ₀ ⟶ Δ₁) (g : Δ₁ ⟶ Δ₂) :
    groupBarConstructionHom G (f ≫ g) =
      groupBarConstructionHom G f ≫ groupBarConstructionHom G g := by
  -- The transported tuple maps compose exactly as the nerve action does.
  apply TopCat.hom_ext
  ext x
  simpa [groupBarConstructionHom, groupBarConstructionMap_comp]

/-- The face maps multiplying adjacent coordinates are continuous. -/
private theorem groupBarConstructionFaceSucc_continuous (n : ℕ) (i : Fin (n + 1)) :
    Continuous (groupBarConstructionFaceSucc G n i) := by
  -- Each coordinate is either copied from the input or formed by one multiplication.
  refine continuous_pi ?_
  intro k
  rcases lt_trichotomy (k : ℕ) i with hlt | heq | hgt
  · simpa [groupBarConstructionFaceSucc, Fin.contractNth_apply_of_lt, hlt] using
      (continuous_apply k.castSucc : Continuous fun g : Fin (n + 1) → G ↦ g k.castSucc)
  · simpa [groupBarConstructionFaceSucc, Fin.contractNth_apply_of_eq, heq] using
      ((continuous_apply k.succ : Continuous fun g : Fin (n + 1) → G ↦ g k.succ).mul
        (continuous_apply k.castSucc : Continuous fun g : Fin (n + 1) → G ↦ g k.castSucc))
  · simpa [groupBarConstructionFaceSucc, Fin.contractNth_apply_of_gt, hgt] using
      (continuous_apply k.succ : Continuous fun g : Fin (n + 1) → G ↦ g k.succ)

/-- The higher face maps of the bar construction as morphisms in `TopCat`. -/
abbrev groupBarConstructionFaceSuccHom (n : ℕ) (i : Fin (n + 1)) :
    groupBarConstructionObj G (n + 1) ⟶ groupBarConstructionObj G n :=
  TopCat.ofHom ⟨groupBarConstructionFaceSucc G n i, groupBarConstructionFaceSucc_continuous G n i⟩

/-- Construction 16.5.1 (1): a topological group `G` determines the simplicial space `B_*G`,
formalized as a simplicial object in `TopCat` whose `n`-simplices are `TopCat.of (Fin n → G)`. -/
def groupBarConstruction : SimplicialObject TopCat where
  obj Δ := groupBarConstructionObj G Δ.unop.len
  map f := groupBarConstructionHom G f
  map_id Δ := groupBarConstructionHom_id G Δ
  map_comp f g := groupBarConstructionHom_comp G f g

/-- The levelwise singular simplicial set attached to the simplicial space `groupBarConstruction G`,
viewed as a bisimplicial set. -/
noncomputable abbrev groupBarConstructionBisimplicialSet : SimplicialObject SSet :=
  SimplicialObject.singularBisimplicialSet (groupBarConstruction G)

/-- The diagonal simplicial set of the bisimplicial singular set attached to
`groupBarConstruction G`. -/
noncomputable abbrev groupBarConstructionDiagonalSSet : SSet :=
  SimplicialObject.diagonalSingularSet (groupBarConstruction G)

/-- Construction 16.5.1 (2): the geometric realization `BG` of `B_*G`, formalized as the
geometric realization of the diagonal simplicial set of the levelwise singular complex of
`groupBarConstruction G`. This is the classifying space of `G`. -/
noncomputable abbrev groupClassifyingSpace : TopCat :=
  SimplicialObject.geometricRealization (groupBarConstruction G)

/-- `groupClassifyingSpace G` is the geometric realization of the diagonal simplicial set
attached to `groupBarConstruction G`. -/
theorem groupClassifyingSpace_def :
    groupClassifyingSpace G =
      SSet.toTop.obj (groupBarConstructionDiagonalSSet G) := rfl

/-- The `0`-th face map of `groupBarConstruction G` deletes the first coordinate. -/
theorem groupBarConstruction_δ_zero (n : ℕ) :
    (groupBarConstruction G).δ (0 : Fin (n + 2)) =
      groupBarConstructionFaceZeroHom G n := by
  -- Rewriting `δ 0` in the nerve forgets the first edge, so the tuple model drops the first
  -- coordinate.
  apply TopCat.hom_ext
  ext g
  funext k
  change groupBarConstructionNSimplicesEquiv G n
      ((nerve (SingleObj G)).δ (0 : Fin (n + 2))
        ((groupBarConstructionNSimplicesEquiv G (n + 1)).symm g)) k =
    groupBarConstructionFaceZero G n g k
  rw [CategoryTheory.nerve.δ₀_eq]
  simpa [groupBarConstructionFaceZero, groupBarConstructionNSimplicesEquiv_symm_apply,
    SingleObj.toEnd_def] using
    groupBarConstructionNerveSimplexOfTuple_edge G (n + 1) g k.succ

/-- The higher face maps of `groupBarConstruction G` multiply adjacent coordinates. -/
-- TODO: Rewrite `(groupBarConstruction G).δ i.succ` to
-- `groupBarConstructionHom G (SimplexCategory.δ i.succ).op`, then prove the underlying transported
-- tuple map is `Fin.contractNth i (· * ·)` by splitting coordinates into `< i`, `= i`, and `> i`.
theorem groupBarConstruction_δ_succ (n : ℕ) (i : Fin (n + 1)) :
    (groupBarConstruction G).δ i.succ =
      groupBarConstructionFaceSuccHom G n i := by
  -- Route correction: after normalizing the transported map once, the public face identity is a
  -- short extensionality argument.
  rw [SimplicialObject.δ_def]
  apply TopCat.hom_ext
  ext g
  funext k
  simpa [groupBarConstruction, groupBarConstructionHom, groupBarConstructionFaceSuccHom] using
    congrFun (congrFun (groupBarConstructionMap_deltaSucc G n i) g) k

/-- The degeneracy maps of `groupBarConstruction G` insert the identity element. -/
-- TODO: Rewrite `(groupBarConstruction G).σ i` to
-- `groupBarConstructionHom G (SimplexCategory.σ i).op`, then prove the underlying transported
-- tuple map is `i.insertNth 1` using the `i.succAboveCases` split and the identity edge at the
-- repeated vertex.
theorem groupBarConstruction_σ (n : ℕ) (i : Fin (n + 1)) :
    (groupBarConstruction G).σ i =
      groupBarConstructionDegeneracyHom G n i := by
  -- Route correction: after normalizing the transported map once, the public degeneracy identity
  -- is a short extensionality argument.
  rw [SimplicialObject.σ_def]
  apply TopCat.hom_ext
  ext g
  funext j
  simpa [groupBarConstruction, groupBarConstructionHom, groupBarConstructionDegeneracyHom] using
    congrFun (congrFun (groupBarConstructionMap_sigma G n i) g) j

end TopologicalGroup

end Topological
