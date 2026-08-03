module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy

public section

open CategoryTheory

universe u v

namespace CategoryTheory.NatTrans

/-- Helper for Theorem 62.1: naturally transformed functors induce the same
map on connected components of their categorical nerves. -/
lemma nerveMap_mapπ₀_eq {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) :
    SSet.mapπ₀ (nerveMap F) = SSet.mapπ₀ (nerveMap G) := by
  -- Reduce a component to a vertex and represent that vertex by one category object.
  funext z
  induction z using SSet.π₀.rec with
  | mk x =>
      obtain ⟨c, rfl⟩ := ComposableArrows.mk₀_surjective x
      rw [SSet.mapπ₀_mk, SSet.mapπ₀_mk, nerveMap_app_mk₀,
        nerveMap_app_mk₀]
      -- The component of the natural transformation is an edge joining the images.
      exact SSet.π₀.sound (CategoryTheory.nerve.edgeMk (α.app c))

end CategoryTheory.NatTrans

namespace CategoryTheory.OrderHom

-- Route correction: a bare abstract nerve has no simplicial morphism API, so
-- use the categorical nerve of its face poset and an explicit prism homotopy.

variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- Helper for Theorem 62.1: the prism vertex records which endpoint map is
used and which vertex of the original simplex supplies its object. -/
private def prismVertexIndex {n : ℕ} (i : Fin (n + 1)) (k : Fin (n + 2)) :
    Fin 2 × Fin (n + 1) :=
  (if k ≤ i.castSucc then 0 else 1, i.predAbove k)

/-- Helper for Theorem 62.1: reindex only the original-simplex coordinate of
a prism vertex. -/
private def mapPrismVertexIndex {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1))
    (z : Fin 2 × Fin (n + 1)) : Fin 2 × Fin (m + 1) :=
  (z.1, f z.2)

/-- Helper for Theorem 62.1: deleting the first prism vertex leaves the
`G`-image of the original simplex. -/
private lemma prismVertexIndex_zero_succAbove {n : ℕ} (k : Fin (n + 1)) :
    prismVertexIndex (0 : Fin (n + 1)) ((0 : Fin (n + 2)).succAbove k) = (1, k) := by
  -- The zero face shifts every surviving vertex, so the prism lies on the `G` side.
  simp [prismVertexIndex]

/-- Helper for Theorem 62.1: deleting the last prism vertex leaves the
`F`-image of the original simplex. -/
private lemma prismVertexIndex_last_succAbove {n : ℕ} (k : Fin (n + 1)) :
    prismVertexIndex (Fin.last n) ((Fin.last (n + 1)).succAbove k) = (0, k) := by
  -- The last face preserves every earlier vertex, so the prism lies on the `F` side.
  simp [prismVertexIndex, Fin.succAbove_last_apply, Fin.le_last]

/-- Helper for Theorem 62.1: the prism index commutes with an early face map. -/
private lemma prismVertexIndex_face_of_le {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 1)) (hij : i ≤ j.castSucc) (k : Fin (n + 2)) :
    prismVertexIndex j.succ (i.castSucc.succAbove k) =
      mapPrismVertexIndex i.succAbove (prismVertexIndex j k) := by
  -- The face identity is the coordinate form of `δ_comp_σ_of_le`.
  have hside : i.castSucc.succAbove k ≤ j.succ.castSucc ↔ k ≤ j.castSucc := by
    by_cases hki : k < i
    · rw [Fin.succAbove_of_castSucc_lt _ _
        (Fin.castSucc_lt_castSucc_iff.mpr hki)]
      have hkj : k ≤ j.castSucc := hki.le.trans hij
      exact ⟨fun _ ↦ hkj, fun _ ↦
        Fin.castSucc_le_castSucc_iff.mpr (hkj.trans j.castSucc_le_succ)⟩
    · have hik : i ≤ k := Fin.not_lt.mp hki
      rw [Fin.succAbove_of_le_castSucc _ _
        (Fin.castSucc_le_castSucc_iff.mpr hik), Fin.castSucc_succ,
        Fin.succ_le_succ_iff]
  have hvertex := SimplexCategory.congr_toOrderHom_apply
    (SimplexCategory.δ_comp_σ_of_le hij) k
  apply Prod.ext
  · simp only [prismVertexIndex, mapPrismVertexIndex]
    by_cases hk : k ≤ j.castSucc
    · rw [if_pos hk, if_pos (hside.mpr hk)]
    · rw [if_neg hk, if_neg (fun hl ↦ hk (hside.mp hl))]
  · simp only [prismVertexIndex, mapPrismVertexIndex]
    simpa [SimplexCategory.δ, SimplexCategory.σ] using hvertex

/-- Helper for Theorem 62.1: the prism index commutes with a late face map. -/
private lemma prismVertexIndex_face_of_gt {n : ℕ} (i : Fin (n + 2))
    (j : Fin (n + 1)) (hji : j.castSucc < i) (k : Fin (n + 2)) :
    prismVertexIndex j.castSucc (i.succ.succAbove k) =
      mapPrismVertexIndex i.succAbove (prismVertexIndex j k) := by
  -- The face identity is the coordinate form of `δ_comp_σ_of_gt`.
  have hside : i.succ.succAbove k ≤ j.castSucc.castSucc ↔ k ≤ j.castSucc := by
    by_cases hki : k ≤ i
    · rw [Fin.succAbove_succ_of_le i k hki]
      exact Fin.castSucc_le_castSucc_iff
    · rw [Fin.succAbove_succ_of_lt i k (lt_of_not_ge hki)]
      have hjk : j.castSucc < k := hji.trans (lt_of_not_ge hki)
      constructor
      · intro h
        have hkcast : k.castSucc ≤ j.castSucc.castSucc := k.castSucc_le_succ.trans h
        exact (not_le_of_gt hjk (Fin.castSucc_le_castSucc_iff.mp hkcast)).elim
      · intro h
        exact (not_le_of_gt hjk h).elim
  have hvertex := SimplexCategory.congr_toOrderHom_apply
    (SimplexCategory.δ_comp_σ_of_gt hji) k
  apply Prod.ext
  · simp only [prismVertexIndex, mapPrismVertexIndex]
    by_cases hk : k ≤ j.castSucc
    · rw [if_pos hk, if_pos (hside.mpr hk)]
    · rw [if_neg hk, if_neg (fun hl ↦ hk (hside.mp hl))]
  · simp only [prismVertexIndex, mapPrismVertexIndex]
    simpa [SimplexCategory.δ, SimplexCategory.σ] using hvertex

/-- Helper for Theorem 62.1: the prism index commutes with an early degeneracy. -/
private lemma prismVertexIndex_degeneracy_of_le {n : ℕ} (i j : Fin (n + 1))
    (hij : i ≤ j) (k : Fin (n + 3)) :
    prismVertexIndex j (i.castSucc.predAbove k) =
      mapPrismVertexIndex i.predAbove (prismVertexIndex j.succ k) := by
  -- The degeneracy identity is the coordinate form of `σ_comp_σ`.
  have hside : i.castSucc.predAbove k ≤ j.castSucc ↔ k ≤ j.succ.castSucc := by
    by_cases hki : k ≤ i.castSucc.castSucc
    · rw [Fin.predAbove_of_le_castSucc _ _ hki]
      have hkjBase : k ≤ j.castSucc.castSucc :=
        hki.trans (Fin.castSucc_le_castSucc_iff.mpr
          (Fin.castSucc_le_castSucc_iff.mpr hij))
      have hkj : k ≤ j.succ.castSucc := by
        exact hkjBase.trans (Fin.castSucc_le_castSucc_iff.mpr j.castSucc_le_succ)
      exact ⟨fun _ ↦ hkj, fun _ ↦
        (Fin.castPred_le_iff (i := k) (j := j.castSucc) _).mpr hkjBase⟩
    · have hik : i.castSucc.castSucc < k := lt_of_not_ge hki
      rw [Fin.predAbove_of_castSucc_lt _ _ hik]
      simpa only [Fin.castSucc_succ] using
        (Fin.pred_le_iff (Fin.ne_zero_of_lt hik) (j := j.castSucc))
  have hvertex := SimplexCategory.congr_toOrderHom_apply
    (SimplexCategory.σ_comp_σ hij) k
  apply Prod.ext
  · simp only [prismVertexIndex, mapPrismVertexIndex]
    by_cases hk : k ≤ j.succ.castSucc
    · rw [if_pos hk, if_pos (hside.mpr hk)]
    · rw [if_neg hk, if_neg (fun hl ↦ hk (hside.mp hl))]
  · simp only [prismVertexIndex, mapPrismVertexIndex]
    simpa [SimplexCategory.σ] using hvertex

/-- Helper for Theorem 62.1: the prism index commutes with a late degeneracy. -/
private lemma prismVertexIndex_degeneracy_of_ge {n : ℕ} (i j : Fin (n + 1))
    (hji : j ≤ i) (k : Fin (n + 3)) :
    prismVertexIndex j (i.succ.predAbove k) =
      mapPrismVertexIndex i.predAbove (prismVertexIndex j.castSucc k) := by
  -- Apply the same simplicial identity with the two repeated positions reversed.
  have hside : i.succ.predAbove k ≤ j.castSucc ↔ k ≤ j.castSucc.castSucc := by
    by_cases hki : k ≤ i.succ.castSucc
    · rw [Fin.predAbove_of_le_castSucc _ _ hki]
      exact Fin.castPred_le_iff _
    · have hik : i.succ.castSucc < k := lt_of_not_ge hki
      rw [Fin.predAbove_of_castSucc_lt _ _ hik]
      have hjk : j.castSucc.castSucc < k :=
        (Fin.castSucc_le_castSucc_iff.mpr
          ((Fin.castSucc_le_castSucc_iff.mpr hji).trans i.castSucc_le_succ)).trans_lt hik
      have hjPivot : j.castSucc.succ ≤ i.succ.castSucc := by
        simpa only [Fin.castSucc_succ] using
          (Fin.succ_le_succ_iff.mpr (Fin.castSucc_le_castSucc_iff.mpr hji))
      have hjpred : j.castSucc < k.pred (Fin.ne_zero_of_lt hik) :=
        (Fin.lt_pred_iff (Fin.ne_zero_of_lt hik)).mpr (hjPivot.trans_lt hik)
      exact ⟨fun h ↦ (not_le_of_gt hjpred h).elim,
        fun h ↦ (not_le_of_gt hjk h).elim⟩
  have hvertex := SimplexCategory.congr_toOrderHom_apply
    (SimplexCategory.σ_comp_σ hji) k
  apply Prod.ext
  · simp only [prismVertexIndex, mapPrismVertexIndex]
    by_cases hk : k ≤ j.castSucc.castSucc
    · rw [if_pos hk, if_pos (hside.mpr hk)]
    · rw [if_neg hk, if_neg (fun hl ↦ hk (hside.mp hl))]
  · simp only [prismVertexIndex, mapPrismVertexIndex]
    symm
    simpa [SimplexCategory.σ] using hvertex

/-- Helper for Theorem 62.1: deleting the switching vertex gives the same
prism index from either adjacent switching position. -/
private lemma prismVertexIndex_middle_face {n : ℕ} (j : Fin (n + 1))
    (k : Fin (n + 2)) :
    prismVertexIndex j.succ (j.castSucc.succ.succAbove k) =
      prismVertexIndex j.castSucc (j.castSucc.succ.succAbove k) := by
  -- Both sides reduce to the original prism index at `j`.
  by_cases hkj : k ≤ j.castSucc
  · have hsucc : k.succ ≤ j.castSucc.succ := Fin.succ_le_succ_iff.mpr hkj
    rw [Fin.succAbove_of_succ_le _ _ hsucc]
    simp only [prismVertexIndex]
    rw [show j.succ.predAbove k.castSucc = k from
      Fin.predAbove_castSucc_of_le _ _ (hkj.trans j.castSucc_le_succ)]
    rw [show j.castSucc.predAbove k.castSucc = k from
      Fin.predAbove_castSucc_of_le _ _ hkj]
    have hLeft : k.castSucc ≤ j.succ.castSucc :=
      Fin.castSucc_le_castSucc_iff.mpr (hkj.trans j.castSucc_le_succ)
    have hRight : k.castSucc ≤ j.castSucc.castSucc :=
      Fin.castSucc_le_castSucc_iff.mpr hkj
    simp only [if_pos hLeft, if_pos hRight]
  · have hjk : j.castSucc < k := lt_of_not_ge hkj
    have hsucc : j.castSucc.succ ≤ k.castSucc := Fin.succ_le_castSucc_iff.mpr hjk
    rw [Fin.succAbove_of_le_castSucc _ _ hsucc]
    simp only [prismVertexIndex]
    rw [show j.succ.predAbove k.succ = k from
      Fin.predAbove_succ_of_le _ _ (Fin.castSucc_lt_iff_succ_le.mp hjk)]
    rw [show j.castSucc.predAbove k.succ = k from
      Fin.predAbove_succ_of_le _ _ hjk.le]
    have hLeft : ¬ k.succ ≤ j.succ.castSucc := by
      rw [Fin.succ_le_castSucc_iff]
      exact not_lt_of_ge (Fin.castSucc_lt_iff_succ_le.mp hjk)
    have hRight : ¬ k.succ ≤ j.castSucc.castSucc := by
      rw [Fin.succ_le_castSucc_iff]
      exact not_lt_of_ge hjk.le
    simp only [if_neg hLeft, if_neg hRight]

/-- Helper for Theorem 62.1: the vertices in the prism simplex associated to
pointwise comparable order maps. -/
private def comparableNerveHomotopyObj {n : ℕ} (F G : P →o Q)
    (x : ComposableArrows P n) (i : Fin (n + 1)) (k : Fin (n + 2)) : Q :=
  let z := prismVertexIndex i k
  if z.1 = 0 then F (x.obj z.2) else G (x.obj z.2)

/-- Helper for Theorem 62.1: the prism vertices form a monotone chain. -/
private lemma comparableNerveHomotopyObj_monotone {n : ℕ} (F G : P →o Q)
    (h : ∀ p, F p ≤ G p) (x : ComposableArrows P n) (i : Fin (n + 1)) :
    Monotone (comparableNerveHomotopyObj F G x i) := by
  -- On either side of the duplicated vertex, monotonicity comes from `x` and
  -- the corresponding order map; the crossing step uses the comparison `h`.
  intro a b hab
  by_cases ha : a ≤ i.castSucc
  · by_cases hb : b ≤ i.castSucc
    · simp only [comparableNerveHomotopyObj, prismVertexIndex, if_pos ha,
        if_pos hb]
      exact F.monotone (leOfHom (x.map (homOfLE (i.predAbove_right_monotone hab))))
    · simp only [comparableNerveHomotopyObj, prismVertexIndex, if_pos ha,
        if_neg hb]
      exact (h _).trans
        (G.monotone (leOfHom (x.map (homOfLE (i.predAbove_right_monotone hab)))))
  · have hb : ¬ b ≤ i.castSucc := fun hb ↦ ha (hab.trans hb)
    simp only [comparableNerveHomotopyObj, prismVertexIndex, if_neg ha,
      if_neg hb]
    exact G.monotone (leOfHom (x.map (homOfLE (i.predAbove_right_monotone hab))))

/-- Helper for Theorem 62.1: the prism simplex joining the images of a nerve
simplex under pointwise comparable order maps. -/
private noncomputable def comparableNerveHomotopySimplex {n : ℕ} (F G : P →o Q)
    (h : ∀ p, F p ≤ G p) (x : ComposableArrows P n) (i : Fin (n + 1)) :
    ComposableArrows Q (n + 1) :=
  ComposableArrows.mkOfObjOfMapSucc
    (comparableNerveHomotopyObj F G x i)
    (fun k ↦ homOfLE
      (comparableNerveHomotopyObj_monotone F G h x i k.castSucc_le_succ))

/-- Helper for Theorem 62.1: the objects of the prism simplex are its prescribed
piecewise `F`- and `G`-images. -/
@[simp] private lemma comparableNerveHomotopySimplex_obj {n : ℕ} (F G : P →o Q)
    (h : ∀ p, F p ≤ G p) (x : ComposableArrows P n) (i : Fin (n + 1))
    (k : Fin (n + 2)) :
    (comparableNerveHomotopySimplex F G h x i).obj k =
      comparableNerveHomotopyObj F G x i k := by
  -- `mkOfObjOfMapSucc` preserves its supplied object function definitionally.
  rfl

/-- Helper for Theorem 62.1: a face map on a category nerve deletes the
specified object from the composable chain. -/
@[simp] private lemma nerveFaceMap_obj {n : ℕ} (i : Fin (n + 2))
    (x : ComposableArrows Q (n + 1)) (k : Fin (n + 1)) :
    ((ConcreteCategory.hom ((nerve Q).δ i)) x).obj k = x.obj (i.succAbove k) := by
  -- Expose the object projection without unfolding the forgetful category tower.
  rfl

/-- Helper for Theorem 62.1: a degeneracy map on a category nerve repeats the
specified object of the composable chain. -/
@[simp] private lemma nerveDegeneracyMap_obj {n : ℕ} (i : Fin (n + 1))
    (x : ComposableArrows Q n) (k : Fin (n + 2)) :
    ((ConcreteCategory.hom ((nerve Q).σ i)) x).obj k = x.obj (i.predAbove k) := by
  -- Expose the object projection without unfolding the forgetful category tower.
  rfl

/-- Helper for Theorem 62.1: a map of category nerves applies its functor to
each object of a composable chain. -/
@[simp] private lemma nerveOrderHomMap_obj {n : ℕ} (F : P →o Q)
    (x : ComposableArrows P n) (k : Fin (n + 1)) :
    ((ConcreteCategory.hom
      ((nerveMap F.toFunctor).app (Opposite.op (SimplexCategory.mk n)))) x).obj k =
      F (x.obj k) := by
  -- The nerve-map object formula is definitionally pointwise.
  rfl

/-- Helper for Theorem 62.1: pointwise comparable order maps induce a
combinatorial homotopy between the corresponding category-nerve maps. -/
lemma nerveMapHomotopyOfPointwiseLE (F G : P →o Q)
    (hle : ∀ p, F p ≤ G p) :
    Nonempty (SimplicialObject.Homotopy
      (nerveMap F.toFunctor) (nerveMap G.toFunctor)) := by
  -- Assemble the prism simplices; thinness reduces every simplicial identity
  -- to its equality on the ordered list of objects.
  constructor
  refine SimplicialObject.Homotopy.mk
    (fun i ↦ ↾fun x ↦ comparableNerveHomotopySimplex F G hle x i)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro n
    apply ConcreteCategory.hom_ext
    intro x
    change ComposableArrows P n at x
    apply nerve.ext_of_isThin
    funext k
    change Fin (n + 1) at k
    change comparableNerveHomotopyObj F G x 0 ((0 : Fin (n + 2)).succAbove k) =
      G (x.obj k)
    unfold comparableNerveHomotopyObj
    rw [prismVertexIndex_zero_succAbove]
    rfl
  · intro n
    apply ConcreteCategory.hom_ext
    intro x
    change ComposableArrows P n at x
    apply nerve.ext_of_isThin
    funext k
    change Fin (n + 1) at k
    change comparableNerveHomotopyObj F G x (Fin.last n)
      ((Fin.last (n + 1)).succAbove k) = F (x.obj k)
    unfold comparableNerveHomotopyObj
    rw [prismVertexIndex_last_succAbove]
    rfl
  · intro n i j hij
    apply ConcreteCategory.hom_ext
    intro x
    change ComposableArrows P (n + 1) at x
    apply nerve.ext_of_isThin
    funext k
    change Fin (n + 2) at k
    change comparableNerveHomotopyObj F G x j.succ (i.castSucc.succAbove k) =
      comparableNerveHomotopyObj F G
        ((ConcreteCategory.hom ((nerve P).δ i)) x) j k
    unfold comparableNerveHomotopyObj
    rw [prismVertexIndex_face_of_le i j hij k]
    simp only [mapPrismVertexIndex, nerveFaceMap_obj]
  · intro n j
    apply ConcreteCategory.hom_ext
    intro x
    change ComposableArrows P (n + 1) at x
    apply nerve.ext_of_isThin
    funext k
    change Fin (n + 2) at k
    change comparableNerveHomotopyObj F G x j.succ
      (j.castSucc.succ.succAbove k) =
        comparableNerveHomotopyObj F G x j.castSucc
          (j.castSucc.succ.succAbove k)
    unfold comparableNerveHomotopyObj
    rw [prismVertexIndex_middle_face]
  · intro n i j hji
    apply ConcreteCategory.hom_ext
    intro x
    change ComposableArrows P (n + 1) at x
    apply nerve.ext_of_isThin
    funext k
    change Fin (n + 2) at k
    change comparableNerveHomotopyObj F G x j.castSucc (i.succ.succAbove k) =
      comparableNerveHomotopyObj F G
        ((ConcreteCategory.hom ((nerve P).δ i)) x) j k
    unfold comparableNerveHomotopyObj
    rw [prismVertexIndex_face_of_gt i j hji k]
    simp only [mapPrismVertexIndex, nerveFaceMap_obj]
  · intro n i j hij
    apply ConcreteCategory.hom_ext
    intro x
    change ComposableArrows P n at x
    apply nerve.ext_of_isThin
    funext k
    change Fin (n + 3) at k
    change comparableNerveHomotopyObj F G x j (i.castSucc.predAbove k) =
      comparableNerveHomotopyObj F G
        ((ConcreteCategory.hom ((nerve P).σ i)) x) j.succ k
    unfold comparableNerveHomotopyObj
    rw [prismVertexIndex_degeneracy_of_le i j hij k]
    simp only [mapPrismVertexIndex, nerveDegeneracyMap_obj]
  · intro n i j hji
    apply ConcreteCategory.hom_ext
    intro x
    change ComposableArrows P n at x
    apply nerve.ext_of_isThin
    funext k
    change Fin (n + 3) at k
    change comparableNerveHomotopyObj F G x j (i.succ.predAbove k) =
      comparableNerveHomotopyObj F G
        ((ConcreteCategory.hom ((nerve P).σ i)) x) j.castSucc k
    unfold comparableNerveHomotopyObj
    rw [prismVertexIndex_degeneracy_of_ge i j hji k]
    simp only [mapPrismVertexIndex, nerveDegeneracyMap_obj]


end CategoryTheory.OrderHom

end
