import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Reformulation_6_1_6

open CategoryTheory
open scoped ContinuousMap unitInterval

universe u

variable {A B X Y Z W : Type u}
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace Z] [TopologicalSpace W]

-- Semantic recall: `Arrow TopCat` is the canonical owner for commutative squares of continuous
-- maps, while `ContinuousMap.HomotopyEquiv` is the canonical owner for ordinary homotopy
-- equivalences. The pair-level homotopy notions below keep the source-facing relative data.

/-- The arrow of `TopCat` corresponding to the inclusion map of a pair `(X, A)`. -/
abbrev PairObject (i : C(A, X)) : Arrow TopCat :=
  Arrow.mk (TopCat.ofHom i)

/-- A map of pairs presented by a commutative square between the vertical maps `i : A → X` and
`j : B → Y`. -/
abbrev PairMap (i : C(A, X)) (j : C(B, Y)) :=
  PairObject i ⟶ PairObject j

namespace PairMap

/-- The induced map on the chosen subspaces. -/
abbrev subspaceMap {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j) : C(A, B) :=
  F.left.hom

/-- The induced map on the ambient spaces. -/
abbrev ambientMap {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j) : C(X, Y) :=
  F.right.hom

/-- A `PairMap` is exactly a commutative square of continuous maps. -/
theorem comm {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j) :
    F.ambientMap.comp i = j.comp F.subspaceMap := by
  ext a
  change F.right.hom (i a) = j (F.left.hom a)
  simpa using (congrFun (congrArg ContinuousMap.toFun (congrArg TopCat.Hom.hom F.w)) a).symm

end PairMap

/-- A homotopy of pair maps is a homotopy on the subspaces and a homotopy on the ambient spaces
whose stages continue to commute with the vertical maps. -/
structure PairHomotopy {i : C(A, X)} {j : C(B, Y)} (F₀ F₁ : PairMap i j) where
  subspaceHomotopy : F₀.subspaceMap.Homotopy F₁.subspaceMap
  ambientHomotopy : F₀.ambientMap.Homotopy F₁.ambientMap
  comm :
    ∀ z : I × A,
      ambientHomotopy (z.1, i z.2) = j (subspaceHomotopy (z.1, z.2))

namespace PairHomotopy

/-- A pair homotopy can be reversed by reversing both its subspace and ambient components. -/
def symm {i : C(A, X)} {j : C(B, Y)} {F₀ F₁ : PairMap i j}
    (H : PairHomotopy F₀ F₁) :
    PairHomotopy F₁ F₀ := by
  refine
    { subspaceHomotopy := H.subspaceHomotopy.symm
      ambientHomotopy := H.ambientHomotopy.symm
      comm := ?_ }
  -- Evaluate the reversed pair homotopy at the reversed time parameter.
  intro z
  rcases z with ⟨t, a⟩
  simpa [ContinuousMap.Homotopy.symm] using H.comm (σ t, a)

/-- Pair homotopies concatenate by concatenating their subspace and ambient components in lockstep.
-/
noncomputable def trans {i : C(A, X)} {j : C(B, Y)} {F₀ F₁ F₂ : PairMap i j}
    (H₀ : PairHomotopy F₀ F₁) (H₁ : PairHomotopy F₁ F₂) :
    PairHomotopy F₀ F₂ := by
  refine
    { subspaceHomotopy := H₀.subspaceHomotopy.trans H₁.subspaceHomotopy
      ambientHomotopy := H₀.ambientHomotopy.trans H₁.ambientHomotopy
      comm := ?_ }
  -- The pointwise pair-map compatibility is preserved on each half of the concatenation.
  intro z
  rcases z with ⟨t, a⟩
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · simpa using
      H₀.comm
        (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, a)
  · simpa using
      H₁.comm
        (⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, a)

end PairHomotopy

/-- Two maps of pairs are homotopic when they are connected by a `PairHomotopy`. -/
abbrev HomotopicPairMap {i : C(A, X)} {j : C(B, Y)} (F₀ F₁ : PairMap i j) : Prop :=
  Nonempty (PairHomotopy F₀ F₁)

namespace HomotopicPairMap

/-- Every pair map is homotopic to itself through pair maps. -/
theorem refl {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j) : HomotopicPairMap F F := by
  refine ⟨{
    subspaceHomotopy := .refl F.subspaceMap
    ambientHomotopy := .refl F.ambientMap
    comm := ?_
  }⟩
  intro z
  simpa using congrFun (congrArg ContinuousMap.toFun (PairMap.comm F)) z.2

end HomotopicPairMap

/-- A map of pairs is a homotopy equivalence of pairs if it admits a two-sided inverse square up to
homotopies through maps of pairs. -/
class IsPairHomotopyEquivalence {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j) : Prop where
  exists_inverse :
    ∃ G : PairMap j i,
      HomotopicPairMap (F ≫ G) (𝟙 (PairObject i)) ∧
        HomotopicPairMap (G ≫ F) (𝟙 (PairObject j))

/-- A pair map is a pair homotopy equivalence exactly when it admits a two-sided inverse up to
pair homotopy. -/
theorem isPairHomotopyEquivalence_iff {i : C(A, X)} {j : C(B, Y)} {F : PairMap i j} :
    IsPairHomotopyEquivalence F ↔
      ∃ G : PairMap j i,
        HomotopicPairMap (F ≫ G) (𝟙 (PairObject i)) ∧
          HomotopicPairMap (G ≫ F) (𝟙 (PairObject j)) :=
  ⟨fun h ↦ h.exists_inverse, fun h ↦ ⟨h⟩⟩

/-- Helper for Proposition 6.5.5: the loop `H.symm.trans H` contracts relative to the boundary
`({0, 1} : Set I) ×ˢ Set.univ`. -/
private theorem homotopySymmTransHomotopicRelRefl
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {r₀ r₁ : C(T, Z)}
    (H : r₀.Homotopy r₁) :
    (H.symm.trans H).toContinuousMap.HomotopicRel
      ((ContinuousMap.Homotopy.refl r₁).toContinuousMap)
      (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
  let loopParam : I × I → I := fun st ↦
    ⟨1 - Path.Homotopy.reflTransSymmAux (σ st.1, st.2), by
      have hmem := Path.Homotopy.reflTransSymmAux_mem_I (σ st.1, st.2)
      constructor
      · linarith [hmem.2]
      · linarith [hmem.1]⟩
  refine ⟨{
      toHomotopy :=
        { toFun := fun sx ↦ H (loopParam (sx.1, sx.2.1), sx.2.2)
          continuous_toFun := by
            fun_prop
          map_zero_left := by
            intro tx
            rcases tx with ⟨t, x⟩
            change H (loopParam (0, t), x) = (H.symm.trans H) (t, x)
            rw [ContinuousMap.Homotopy.trans_apply]
            split_ifs with ht
            · have hParam :
                loopParam (0, t) =
                  σ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩ := by
                apply Subtype.ext
                have ht' : (t : ℝ) ≤ 1 / 2 := by
                  simpa using ht
                change (↑(loopParam (0, t)) : ℝ) = 1 - 2 * (t : ℝ)
                have hAux :
                    Path.Homotopy.reflTransSymmAux (σ 0, t) =
                      (if (t : ℝ) ≤ 1 / 2 then 2 * (t : ℝ) else 2 - 2 * (t : ℝ)) := by
                  simp [Path.Homotopy.reflTransSymmAux]
                rw [show (↑(loopParam (0, t)) : ℝ) =
                    1 - Path.Homotopy.reflTransSymmAux (σ 0, t) by
                  simp [loopParam]]
                rw [hAux, if_pos ht']
              exact congrArg (fun u : I ↦ H (u, x)) hParam
            · have hParam :
                loopParam (0, t) = ⟨2 * t - 1,
                  unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ := by
                apply Subtype.ext
                have ht' : ¬ (t : ℝ) ≤ 1 / 2 := by
                  simpa using ht
                change (↑(loopParam (0, t)) : ℝ) = 2 * (t : ℝ) - 1
                have hAux :
                    Path.Homotopy.reflTransSymmAux (σ 0, t) =
                      (if (t : ℝ) ≤ 1 / 2 then 2 * (t : ℝ) else 2 - 2 * (t : ℝ)) := by
                  simp [Path.Homotopy.reflTransSymmAux]
                rw [show (↑(loopParam (0, t)) : ℝ) =
                    1 - Path.Homotopy.reflTransSymmAux (σ 0, t) by
                  simp [loopParam]]
                rw [hAux, if_neg ht']
                ring
              exact congrArg (fun u : I ↦ H (u, x)) hParam
          map_one_left := by
            intro tx
            rcases tx with ⟨t, x⟩
            simp [loopParam, Path.Homotopy.reflTransSymmAux] }
      prop' := ?_ }⟩
  intro s tx htx
  rcases tx with ⟨t, x⟩
  rcases Set.mem_insert_iff.mp htx.1 with ht | ht
  · subst ht
    norm_num [loopParam, Path.Homotopy.reflTransSymmAux]
  · have ht' : t = 1 := Set.mem_singleton_iff.mp ht
    subst ht'
    norm_num [loopParam, Path.Homotopy.reflTransSymmAux]

/-- Helper for Proposition 6.5.5: a square fixed on the time-boundary packages into a homotopy
relative to `({0, 1} : Set I) ×ˢ Set.univ`. -/
private theorem homotopyRelOfBoundaryFixedSquare
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {F₀ F₁ : C(I × T, Z)}
    (S : C((I × T) × I, Z))
    (hZero : ∀ tx : I × T, S (tx, 0) = F₀ tx)
    (hOne : ∀ tx : I × T, S (tx, 1) = F₁ tx)
    (hLeft : ∀ s : I, ∀ x : T, S ((0, x), s) = F₀ (0, x))
    (hRight : ∀ s : I, ∀ x : T, S ((1, x), s) = F₀ (1, x)) :
    F₀.HomotopicRel F₁ (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
  refine ⟨{
    toHomotopy := {
      toContinuousMap := S.comp ContinuousMap.prodSwap
      map_zero_left := hZero
      map_one_left := hOne
    }
    prop' := ?_
  }⟩
  -- The left and right time-faces of the square are frozen, so the homotopy is relative to the
  -- boundary subset.
  intro s tx htx
  rcases tx with ⟨t, x⟩
  rcases Set.mem_insert_iff.mp htx.1 with ht | ht
  · subst ht
    simpa using hLeft s x
  · have ht' : t = 1 := Set.mem_singleton_iff.mp ht
    subst ht'
    simpa using hRight s x

/-- Helper for Proposition 6.5.5: a relative homotopy can be read back as a square whose vertical
faces are fixed on the time-boundary. -/
private theorem boundaryFixedSquareOfHomotopyRel
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {F₀ F₁ : C(I × T, Z)}
    (hF :
      F₀.HomotopicRel F₁ (({0, 1} : Set I) ×ˢ (Set.univ : Set T))) :
    ∃ square : C((I × T) × I, Z),
      (∀ tx : I × T, square (tx, 0) = F₀ tx) ∧
      (∀ tx : I × T, square (tx, 1) = F₁ tx) ∧
      (∀ s : I, ∀ x : T, square ((0, x), s) = F₀ (0, x)) ∧
      (∀ s : I, ∀ x : T, square ((1, x), s) = F₀ (1, x)) := by
  rcases hF with ⟨hF⟩
  refine ⟨hF.toHomotopy.toContinuousMap.comp ContinuousMap.prodSwap, ?_, ?_, ?_, ?_⟩
  · -- Reading the square at `s = 0` recovers the source map of the relative homotopy.
    intro tx
    simpa using hF.toHomotopy.apply_zero tx
  · -- Reading the square at `s = 1` recovers the target map of the relative homotopy.
    intro tx
    simpa using hF.toHomotopy.apply_one tx
  · -- The `t = 0` face is fixed because the relative homotopy is constant on the boundary.
    intro s x
    exact hF.eq_fst s (x := (0, x)) (by simp)
  · -- The `t = 1` face is fixed for the same reason.
    intro s x
    exact hF.eq_fst s (x := (1, x)) (by simp)

/-- Helper for Proposition 6.5.5: a homotopy relative to `({0, 1} : Set I) ×ˢ Set.univ`
identifies the two endpoint time-slices of the underlying homotopies. -/
private theorem homotopyRel_eq_fst_boundary
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {F₀ F₁ : C(I × T, Z)}
    (hF :
      F₀.HomotopicRel F₁ (({0, 1} : Set I) ×ˢ (Set.univ : Set T)))
    (x : T) :
    F₀ (0, x) = F₁ (0, x) ∧ F₀ (1, x) = F₁ (1, x) := by
  -- Read the two distinguished time-slices as points of the recorded boundary subset.
  constructor
  · exact hF.fst_eq_snd (x := ⟨0, x⟩) ⟨by simp, by simp⟩
  · exact hF.fst_eq_snd (x := ⟨1, x⟩) ⟨by simp, by simp⟩

/-- Helper for Proposition 6.5.5: reading the `t = 1` boundary of a symmetrized relative homotopy
recovers the common endpoint of the right factor. -/
private theorem homotopyRelSymm_apply_one
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {r₀ r₁ : C(T, Z)} {H K : r₀.Homotopy r₁}
    (hHK :
      H.toContinuousMap.HomotopyRel K.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set T)))
    (s : I) (x : T) :
    hHK.toHomotopy.symm (s, (1, x)) = K (1, x) := by
  -- The relative homotopy is fixed on the endpoint boundary, and symmetrizing it keeps that
  -- fixed endpoint.
  simpa [ContinuousMap.Homotopy.symm] using
    hHK.eq_snd (σ s) (x := (1, x)) (by simp)

/-- Helper for Proposition 6.5.5: a relative comparison on the right factor of `H.symm.trans _`
induces a relative comparison on the corresponding normalized loop. -/
private theorem symmTransCongrRight_homotopyRel
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {r₀ r₁ : C(T, Z)}
    (H K : r₀.Homotopy r₁)
    (hHK :
      H.toContinuousMap.HomotopicRel K.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set T))) :
    (H.symm.trans K).toContinuousMap.HomotopicRel
      (H.symm.trans H).toContinuousMap
      (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
  rcases hHK with ⟨hHK⟩
  let leftBranch : C((I × T) × I, Z) :=
    { toFun := fun u ↦
        H
          (σ (Set.projIcc 0 1 zero_le_one (2 * ((u.1).1 : ℝ))), (u.1).2)
      continuous_toFun := by
        fun_prop }
  let rightBranch : C((I × T) × I, Z) :=
    { toFun := fun u ↦
        hHK.toHomotopy.symm
          (u.2, (Set.projIcc 0 1 zero_le_one (2 * ((u.1).1 : ℝ) - 1), (u.1).2))
      continuous_toFun := by
        fun_prop }
  let square : C((I × T) × I, Z) :=
    { toFun := fun u ↦
        if h : (((u.1).1 : I) : ℝ) ≤ 1 / 2 then leftBranch u else rightBranch u
      continuous_toFun := by
        refine continuous_if_le (by fun_prop) continuous_const
          leftBranch.continuous.continuousOn rightBranch.continuous.continuousOn ?_
        intro u hu
        rcases u with ⟨⟨t, x⟩, s⟩
        -- The two branches meet at the common `t = 0` endpoint of the right factor.
        have hLeftBranch :
            leftBranch ((t, x), s) = H (0, x) := by
          have ht : (t : ℝ) = 1 / 2 := hu
          simp [leftBranch, ht]
        have hRightBranch :
            rightBranch ((t, x), s) = H (0, x) := by
          have ht : (t : ℝ) = 1 / 2 := hu
          simpa [rightBranch, ht, ContinuousMap.Homotopy.symm] using
            hHK.eq_fst (σ s) (x := (0, x)) (by simp)
        rw [hLeftBranch, hRightBranch] }
  -- Package the square by reading it as a relative homotopy between the two normalized loops.
  refine homotopyRelOfBoundaryFixedSquare square ?_ ?_ ?_ ?_
  · intro tx
    rcases tx with ⟨t, x⟩
    rw [show square (⟨t, x⟩, 0) =
        if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 0) else rightBranch (⟨t, x⟩, 0) by
      rfl]
    change (if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 0) else rightBranch (⟨t, x⟩, 0)) =
      (H.symm.trans K) (t, x)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · have hmem : 2 * (t : ℝ) ∈ I := by
        constructor
        · nlinarith [t.2.1]
        · nlinarith [ht]
      have hproj :
          Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)) = (⟨2 * t, hmem⟩ : I) := by
        apply Subtype.ext
        simp [Set.projIcc_of_mem _ hmem]
      change leftBranch (⟨t, x⟩, 0) = (H.symm) (⟨2 * t, hmem⟩, x)
      change H (σ (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))), x) =
        H (σ (⟨2 * t, hmem⟩ : I), x)
      exact congrArg (fun u : I ↦ H (σ u, x)) hproj
    · have hmem : 2 * (t : ℝ) - 1 ∈ I := by
        constructor
        · nlinarith [(not_le.1 ht).le]
        · nlinarith [t.2.2]
      simpa [rightBranch, ContinuousMap.Homotopy.symm, Set.projIcc_of_mem _ hmem] using
        hHK.toHomotopy.apply_one (⟨2 * t - 1, hmem⟩, x)
  · intro tx
    rcases tx with ⟨t, x⟩
    rw [show square (⟨t, x⟩, 1) =
        if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 1) else rightBranch (⟨t, x⟩, 1) by
      rfl]
    change (if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 1) else rightBranch (⟨t, x⟩, 1)) =
      (H.symm.trans H) (t, x)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · have hmem : 2 * (t : ℝ) ∈ I := by
        constructor
        · nlinarith [t.2.1]
        · nlinarith [ht]
      have hproj :
          Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)) = (⟨2 * t, hmem⟩ : I) := by
        apply Subtype.ext
        simp [Set.projIcc_of_mem _ hmem]
      change leftBranch (⟨t, x⟩, 1) = (H.symm) (⟨2 * t, hmem⟩, x)
      change H (σ (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))), x) =
        H (σ (⟨2 * t, hmem⟩ : I), x)
      exact congrArg (fun u : I ↦ H (σ u, x)) hproj
    · have hmem : 2 * (t : ℝ) - 1 ∈ I := by
        constructor
        · nlinarith [(not_le.1 ht).le]
        · nlinarith [t.2.2]
      simpa [rightBranch, ContinuousMap.Homotopy.symm, Set.projIcc_of_mem _ hmem] using
        hHK.toHomotopy.apply_zero (⟨2 * t - 1, hmem⟩, x)
  · intro s x
    -- The `t = 0` face stays on the common midpoint of the two loops.
    simpa [square, leftBranch, ContinuousMap.Homotopy.symm] using
      (H.symm.trans K).apply_zero x
  · intro s x
    -- The `t = 1` face reads the common right endpoint of the comparison homotopy.
    have hFace :
        rightBranch ((1, x), s) = K (1, x) := by
      have hmem : 2 * ((1 : I) : ℝ) - 1 ∈ I := by
        norm_num
      have hproj :
          Set.projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1) = (1 : I) := by
        apply Subtype.ext
        norm_num
      change hHK.toHomotopy.symm (s, (Set.projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1), x)) =
        K (1, x)
      rw [hproj]
      simpa using homotopyRelSymm_apply_one hHK s x
    have hFalse : ¬ (((1 : I) : ℝ) ≤ 1 / 2) := by
      norm_num
    change
      (if h : (((1 : I) : ℝ) ≤ 1 / 2) then leftBranch ((1, x), s) else rightBranch ((1, x), s)) =
        (H.symm.trans K) (1, x)
    have hIf :
        (if h : (((1 : I) : ℝ) ≤ 1 / 2) then leftBranch ((1, x), s) else rightBranch ((1, x), s)) =
          rightBranch ((1, x), s) := by
      rw [dif_neg hFalse]
    rw [hIf]
    simpa using hFace

/-- Helper for Proposition 6.5.5: whiskering a relative comparison by a fixed left factor preserves
the time-boundary conditions. -/
private theorem symmTransCongrLeft_homotopyRel
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {f₀ f₁ f₂ : C(T, Z)}
    (L : f₀.Homotopy f₁) {M N : f₀.Homotopy f₂}
    (hMN :
      M.toContinuousMap.HomotopicRel N.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set T))) :
    (L.symm.trans M).toContinuousMap.HomotopicRel
      (L.symm.trans N).toContinuousMap
      (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
  rcases hMN with ⟨hMN⟩
  let leftBranch : C((I × T) × I, Z) :=
    { toFun := fun u ↦
        L
          (σ (Set.projIcc 0 1 zero_le_one (2 * ((u.1).1 : ℝ))), (u.1).2)
      continuous_toFun := by
        fun_prop }
  let rightBranch : C((I × T) × I, Z) :=
    { toFun := fun u ↦
        hMN.toHomotopy
          (u.2, (Set.projIcc 0 1 zero_le_one (2 * ((u.1).1 : ℝ) - 1), (u.1).2))
      continuous_toFun := by
        fun_prop }
  let square : C((I × T) × I, Z) :=
    { toFun := fun u ↦
        if h : (((u.1).1 : I) : ℝ) ≤ 1 / 2 then leftBranch u else rightBranch u
      continuous_toFun := by
        refine continuous_if_le (by fun_prop) continuous_const
          leftBranch.continuous.continuousOn rightBranch.continuous.continuousOn ?_
        intro u hu
        rcases u with ⟨⟨t, x⟩, s⟩
        -- The two branches meet at the common `t = 0` endpoint of the right factor.
        have hLeftBranch :
            leftBranch ((t, x), s) = L (0, x) := by
          have ht : (t : ℝ) = 1 / 2 := hu
          simp [leftBranch, ht]
        have hRightBranch :
            rightBranch ((t, x), s) = L (0, x) := by
          have ht : (t : ℝ) = 1 / 2 := hu
          simpa [rightBranch, ht] using
            hMN.eq_fst s (x := (0, x)) (by simp)
        rw [hLeftBranch, hRightBranch] }
  -- Package the square by reading it as a relative homotopy between the two left-whiskered loops.
  refine homotopyRelOfBoundaryFixedSquare square ?_ ?_ ?_ ?_
  · intro tx
    rcases tx with ⟨t, x⟩
    rw [show square (⟨t, x⟩, 0) =
        if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 0) else rightBranch (⟨t, x⟩, 0) by
      rfl]
    change (if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 0) else rightBranch (⟨t, x⟩, 0)) =
      (L.symm.trans M) (t, x)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · have hmem : 2 * (t : ℝ) ∈ I := by
        constructor
        · nlinarith [t.2.1]
        · nlinarith [ht]
      have hproj :
          Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)) = (⟨2 * t, hmem⟩ : I) := by
        apply Subtype.ext
        simp [Set.projIcc_of_mem _ hmem]
      change leftBranch (⟨t, x⟩, 0) = (L.symm) (⟨2 * t, hmem⟩, x)
      change L (σ (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))), x) =
        L (σ (⟨2 * t, hmem⟩ : I), x)
      exact congrArg (fun u : I ↦ L (σ u, x)) hproj
    · have hmem : 2 * (t : ℝ) - 1 ∈ I := by
        constructor
        · nlinarith [(not_le.1 ht).le]
        · nlinarith [t.2.2]
      simpa [rightBranch, Set.projIcc_of_mem _ hmem] using
        hMN.toHomotopy.apply_zero (⟨2 * t - 1, hmem⟩, x)
  · intro tx
    rcases tx with ⟨t, x⟩
    rw [show square (⟨t, x⟩, 1) =
        if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 1) else rightBranch (⟨t, x⟩, 1) by
      rfl]
    change (if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 1) else rightBranch (⟨t, x⟩, 1)) =
      (L.symm.trans N) (t, x)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · have hmem : 2 * (t : ℝ) ∈ I := by
        constructor
        · nlinarith [t.2.1]
        · nlinarith [ht]
      have hproj :
          Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)) = (⟨2 * t, hmem⟩ : I) := by
        apply Subtype.ext
        simp [Set.projIcc_of_mem _ hmem]
      change leftBranch (⟨t, x⟩, 1) = (L.symm) (⟨2 * t, hmem⟩, x)
      change L (σ (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))), x) =
        L (σ (⟨2 * t, hmem⟩ : I), x)
      exact congrArg (fun u : I ↦ L (σ u, x)) hproj
    · have hmem : 2 * (t : ℝ) - 1 ∈ I := by
        constructor
        · nlinarith [(not_le.1 ht).le]
        · nlinarith [t.2.2]
      simpa [rightBranch, Set.projIcc_of_mem _ hmem] using
        hMN.toHomotopy.apply_one (⟨2 * t - 1, hmem⟩, x)
  · intro s x
    -- The `t = 0` face is the shared start of the left-whiskered loops.
    simpa [square, leftBranch, ContinuousMap.Homotopy.symm] using
      (L.symm.trans M).apply_zero x
  · intro s x
    -- The `t = 1` face stays on the common endpoint of the compared right factors.
    have hFace :
        rightBranch ((1, x), s) = M (1, x) := by
      have hproj :
          Set.projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1) = (1 : I) := by
        apply Subtype.ext
        norm_num
      change
        hMN.toHomotopy (s, (Set.projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1), x)) =
          M (1, x)
      rw [hproj]
      simpa using hMN.eq_fst s (x := (1, x)) (by simp)
    have hFalse : ¬ (((1 : I) : ℝ) ≤ 1 / 2) := by
      norm_num
    change
      (if h : (((1 : I) : ℝ) ≤ 1 / 2) then leftBranch ((1, x), s) else rightBranch ((1, x), s)) =
        (L.symm.trans M) (1, x)
    rw [dif_neg hFalse]
    simpa using hFace

/-- Helper for Proposition 6.5.5: whiskering a relative comparison by a fixed right factor
preserves the time-boundary conditions. -/
private theorem transCongrRight_homotopyRel
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {f₀ f₁ f₂ : C(T, Z)}
    {L M : f₀.Homotopy f₁} (K : f₁.Homotopy f₂)
    (hLM :
      L.toContinuousMap.HomotopicRel M.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set T))) :
    (L.trans K).toContinuousMap.HomotopicRel
      (M.trans K).toContinuousMap
      (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
  rcases hLM with ⟨hLM⟩
  let leftBranch : C((I × T) × I, Z) :=
    { toFun := fun u ↦
        hLM.toHomotopy
          (u.2, (Set.projIcc 0 1 zero_le_one (2 * ((u.1).1 : ℝ)), (u.1).2))
      continuous_toFun := by
        fun_prop }
  let rightBranch : C((I × T) × I, Z) :=
    { toFun := fun u ↦
        K (Set.projIcc 0 1 zero_le_one (2 * ((u.1).1 : ℝ) - 1), (u.1).2)
      continuous_toFun := by
        fun_prop }
  let square : C((I × T) × I, Z) :=
    { toFun := fun u ↦
        if h : (((u.1).1 : I) : ℝ) ≤ 1 / 2 then leftBranch u else rightBranch u
      continuous_toFun := by
        refine continuous_if_le (by fun_prop) continuous_const
          leftBranch.continuous.continuousOn rightBranch.continuous.continuousOn ?_
        intro u hu
        rcases u with ⟨⟨t, x⟩, s⟩
        -- The two branches meet at the common `t = 1` endpoint of the left factor.
        have hLeftBranch :
            leftBranch ((t, x), s) = f₁ x := by
          have ht : (t : ℝ) = 1 / 2 := hu
          simpa [leftBranch, ht] using
            hLM.eq_snd s (x := (1, x)) (by simp)
        have hRightBranch :
            rightBranch ((t, x), s) = f₁ x := by
          have ht : (t : ℝ) = 1 / 2 := hu
          simp [rightBranch, ht]
        rw [hLeftBranch, hRightBranch] }
  -- Package the square by reading it as a relative homotopy between the two right-whiskered
  -- composites.
  refine homotopyRelOfBoundaryFixedSquare square ?_ ?_ ?_ ?_
  · intro tx
    rcases tx with ⟨t, x⟩
    rw [show square (⟨t, x⟩, 0) =
        if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 0) else rightBranch (⟨t, x⟩, 0) by
      rfl]
    change (if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 0) else rightBranch (⟨t, x⟩, 0)) =
      (L.trans K) (t, x)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · have hmem : 2 * (t : ℝ) ∈ I := by
        constructor
        · nlinarith [t.2.1]
        · nlinarith [ht]
      simpa [leftBranch, Set.projIcc_of_mem _ hmem] using
        hLM.toHomotopy.apply_zero (⟨2 * t, hmem⟩, x)
    · have hmem : 2 * (t : ℝ) - 1 ∈ I := by
        constructor
        · nlinarith [(not_le.1 ht).le]
        · nlinarith [t.2.2]
      simpa [rightBranch, Set.projIcc_of_mem _ hmem]
  · intro tx
    rcases tx with ⟨t, x⟩
    rw [show square (⟨t, x⟩, 1) =
        if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 1) else rightBranch (⟨t, x⟩, 1) by
      rfl]
    change (if h : (t : ℝ) ≤ 1 / 2 then leftBranch (⟨t, x⟩, 1) else rightBranch (⟨t, x⟩, 1)) =
      (M.trans K) (t, x)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · have hmem : 2 * (t : ℝ) ∈ I := by
        constructor
        · nlinarith [t.2.1]
        · nlinarith [ht]
      simpa [leftBranch, Set.projIcc_of_mem _ hmem] using
        hLM.toHomotopy.apply_one (⟨2 * t, hmem⟩, x)
    · have hmem : 2 * (t : ℝ) - 1 ∈ I := by
        constructor
        · nlinarith [(not_le.1 ht).le]
        · nlinarith [t.2.2]
      simpa [rightBranch, Set.projIcc_of_mem _ hmem]
  · intro s x
    -- The `t = 0` face stays on the common start of the compared left factors.
    simpa [square, leftBranch] using
      hLM.eq_fst s (x := (0, x)) (by simp)
  · intro s x
    -- The `t = 1` face stays on the fixed endpoint of the right factor.
    have hproj :
        Set.projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1) = (1 : I) := by
      apply Subtype.ext
      norm_num
    have hFalse : ¬ (((1 : I) : ℝ) ≤ 1 / 2) := by
      norm_num
    change
      (if h : (((1 : I) : ℝ) ≤ 1 / 2) then leftBranch ((1, x), s) else rightBranch ((1, x), s)) =
        (L.trans K) (1, x)
    rw [dif_neg hFalse]
    rw [show rightBranch ((1, x), s) =
        K (Set.projIcc 0 1 zero_le_one (2 * ((1 : I) : ℝ) - 1), x) by
      rfl]
    rw [hproj]
    simpa using K.apply_one x

/-- Helper for Proposition 6.5.5: after whiskering on the right, the standard contraction of
`L.symm.trans L` still produces a relative comparison to the corresponding reflexive whisker. -/
private theorem symmTransTransReflCongrRight_homotopyRel
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {r₀ r₁ r₂ : C(T, Z)}
    (L : r₀.Homotopy r₁) (K : r₁.Homotopy r₂) :
    ((L.symm.trans L).trans K).toContinuousMap.HomotopicRel
      (((ContinuousMap.Homotopy.refl r₁).trans K).toContinuousMap)
      (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
  -- Whisker the standard relative contraction of `L.symm.trans L` by the fixed trailing factor.
  exact transCongrRight_homotopyRel K (homotopySymmTransHomotopicRelRefl L)

/-- Helper for Proposition 6.5.5: any endpoint-preserving reparametrization of a homotopy is
relative-homotopic to the original homotopy on `({0, 1} : Set I) ×ˢ Set.univ`. -/
private theorem homotopyReparamHomotopicRel
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {r₀ r₁ : C(T, Z)}
    (H : r₀.Homotopy r₁) (f : I → I) (hf : Continuous f)
    (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    let Hreparam : r₀.Homotopy r₁ :=
      { toFun := fun tx ↦ H (f tx.1, tx.2)
        continuous_toFun := by
          have hpair : Continuous fun tx : I × T ↦ (f tx.1, tx.2) := by
            fun_prop
          simpa using H.continuous.comp hpair
        map_zero_left := by
          intro x
          simpa [hf₀] using H.apply_zero x
        map_one_left := by
          intro x
          simpa [hf₁] using H.apply_one x }
    H.toContinuousMap.HomotopicRel Hreparam.toContinuousMap
      (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
  let Hreparam : r₀.Homotopy r₁ :=
    { toFun := fun tx ↦ H (f tx.1, tx.2)
      continuous_toFun := by
        have hpair : Continuous fun tx : I × T ↦ (f tx.1, tx.2) := by
          fun_prop
        simpa using H.continuous.comp hpair
      map_zero_left := by
        intro x
        simpa [hf₀] using H.apply_zero x
      map_one_left := by
        intro x
        simpa [hf₁] using H.apply_one x }
  let squareTime : (I × T) × I → I := fun us ↦
    ⟨σ us.2 * us.1.1 + us.2 * f us.1.1,
      show (σ us.2 : ℝ) • (us.1.1 : ℝ) + (us.2 : ℝ) • (f us.1.1 : ℝ) ∈ I from
        convex_Icc _ _ us.1.1.2 (f us.1.1).2
          (by unit_interval) (by unit_interval) (by simp)⟩
  let square : C((I × T) × I, Z) :=
    { toFun := fun us ↦ H (squareTime us, us.1.2)
      continuous_toFun := by
        have hsquareTime : Continuous squareTime := by
          fun_prop
        have hpair : Continuous fun us : (I × T) × I ↦ (squareTime us, us.1.2) := by
          exact hsquareTime.prodMk continuous_fst.snd
        simpa using H.continuous.comp hpair }
  -- Interpolate linearly between the identity parameter and the chosen reparametrization.
  refine homotopyRelOfBoundaryFixedSquare square ?_ ?_ ?_ ?_
  · intro tx
    rcases tx with ⟨t, x⟩
    change H (squareTime ((t, x), 0), x) = H (t, x)
    have hTime : squareTime ((t, x), 0) = t := by
      apply Subtype.ext
      simp [squareTime]
    simpa [hTime]
  · intro tx
    rcases tx with ⟨t, x⟩
    change H (squareTime ((t, x), 1), x) = Hreparam (t, x)
    have hTime : squareTime ((t, x), 1) = f t := by
      apply Subtype.ext
      simp [squareTime]
    simpa [Hreparam] using congrArg (fun u : I ↦ H (u, x)) hTime
  · intro s x
    change H (squareTime ((0, x), s), x) = H (0, x)
    have hTime : squareTime ((0, x), s) = 0 := by
      apply Subtype.ext
      simp [squareTime, hf₀]
    simpa [hTime]
  · intro s x
    change H (squareTime ((1, x), s), x) = H (1, x)
    have hTime : squareTime ((1, x), s) = 1 := by
      apply Subtype.ext
      simp [squareTime, hf₁]
    simpa [hTime]

/-- Helper for Proposition 6.5.5: the left-associated triple composite is just an
endpoint-preserving reparametrization of the right-associated one. -/
private theorem symmTransTrans_assoc_homotopyRel
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {r₀ r₁ r₂ : C(T, Z)}
    (L : r₀.Homotopy r₁) (K : r₁.Homotopy r₂) :
    (L.symm.trans (L.trans K)).toContinuousMap.HomotopicRel
      (((L.symm.trans L).trans K).toContinuousMap)
      (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
  let assocReparam : I → I := fun t ↦
    ⟨Path.Homotopy.transAssocReparamAux t, Path.Homotopy.transAssocReparamAux_mem_I t⟩
  let Hreparam : r₁.Homotopy r₂ :=
    { toFun := fun tx ↦ (L.symm.trans (L.trans K)) (assocReparam tx.1, tx.2)
      continuous_toFun := by
        have hpair : Continuous fun tx : I × T ↦ (assocReparam tx.1, tx.2) := by
          fun_prop
        simpa using (L.symm.trans (L.trans K)).continuous.comp hpair
      map_zero_left := by
        intro x
        simpa [assocReparam, Path.Homotopy.transAssocReparamAux_zero] using
          (L.symm.trans (L.trans K)).apply_zero x
      map_one_left := by
        intro x
        simpa [assocReparam, Path.Homotopy.transAssocReparamAux_one] using
          (L.symm.trans (L.trans K)).apply_one x }
  have hEq :
      Hreparam.toContinuousMap = (((L.symm.trans L).trans K).toContinuousMap) := by
    ext tx
    rcases tx with ⟨t, x⟩
    let p : Path (r₁ x) (r₀ x) := (L.symm).evalAt x
    let q : Path (r₀ x) (r₁ x) := L.evalAt x
    let r : Path (r₁ x) (r₂ x) := K.evalAt x
    have hPath := Path.Homotopy.trans_assoc_reparam p q r
    have hAt := congrArg (fun γ : Path (r₁ x) (r₂ x) => γ t) hPath.symm
    simpa [p, q, r, Hreparam, assocReparam, ContinuousMap.Homotopy.evalAt] using hAt
  -- Compare the two bracketings by the generic reparametrization principle, then cast the target
  -- to the normalized triple composite used later.
  have hReparam :
      (L.symm.trans (L.trans K)).toContinuousMap.HomotopicRel
        Hreparam.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
    exact
      homotopyReparamHomotopicRel
        (L.symm.trans (L.trans K)) assocReparam
        (by
          fun_prop)
        (by
          apply Subtype.ext
          exact Path.Homotopy.transAssocReparamAux_zero)
        (by
          apply Subtype.ext
          exact Path.Homotopy.transAssocReparamAux_one)
  rcases hReparam with ⟨hReparam⟩
  exact ⟨hReparam.cast rfl hEq⟩

/-- Helper for Proposition 6.5.5: the reflexive left whisker of a homotopy contracts relative to
the time-boundary to the original homotopy. -/
private theorem reflTrans_homotopyRel
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {r₀ r₁ : C(T, Z)}
    (K : r₀.Homotopy r₁) :
    (((ContinuousMap.Homotopy.refl r₀).trans K).toContinuousMap).HomotopicRel
      K.toContinuousMap
      (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
  let reflTransReparamAux : I → ℝ := fun t ↦
    if (t : ℝ) ≤ 1 / 2 then 0 else 2 * t - 1
  have hReflTransReparamAux : Continuous reflTransReparamAux := by
    refine continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) ?_
    intro t ht
    have ht' : (t : ℝ) = 1 / 2 := ht
    simp [reflTransReparamAux, ht']
  have hReflTransReparamAux_mem : ∀ t : I, reflTransReparamAux t ∈ I := by
    intro t
    dsimp [reflTransReparamAux]
    split_ifs with ht
    · constructor <;> norm_num
    · constructor
      · nlinarith [(not_le.1 ht).le]
      · nlinarith [t.2.2]
  let reflTransReparam : I → I := fun t ↦
    ⟨reflTransReparamAux t, hReflTransReparamAux_mem t⟩
  have hReflTransReparam : Continuous reflTransReparam := by
    exact Continuous.subtype_mk hReflTransReparamAux hReflTransReparamAux_mem
  let Hreparam : r₀.Homotopy r₁ :=
    { toFun := fun tx ↦ K (reflTransReparam tx.1, tx.2)
      continuous_toFun := by
        have hpair : Continuous fun tx : I × T ↦ (reflTransReparam tx.1, tx.2) := by
          exact (hReflTransReparam.comp continuous_fst).prodMk continuous_snd
        simpa using K.continuous.comp hpair
      map_zero_left := by
        intro x
        simp [reflTransReparam, reflTransReparamAux]
      map_one_left := by
        intro x
        have hEq : reflTransReparam 1 = (1 : I) := by
          apply Subtype.ext
          norm_num [reflTransReparam, reflTransReparamAux]
        simpa [hEq] using K.apply_one x }
  have hEq :
      Hreparam.toContinuousMap =
        (((ContinuousMap.Homotopy.refl r₀).trans K).toContinuousMap) := by
    ext tx
    rcases tx with ⟨t, x⟩
    change Hreparam (t, x) = ((ContinuousMap.Homotopy.refl r₀).trans K) (t, x)
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · have hZero : reflTransReparam t = 0 := by
        apply Subtype.ext
        have hZeroAux : reflTransReparamAux t = 0 := by
          dsimp [reflTransReparamAux]
          rw [if_pos ht]
        simpa [reflTransReparam, hZeroAux]
      have hTarget : ((ContinuousMap.Homotopy.refl r₀).trans K) (t, x) = r₀ x := by
        rw [ContinuousMap.Homotopy.trans_apply]
        split_ifs with h
        · rfl
        · exact False.elim (h ht)
      rw [hTarget]
      calc
        Hreparam (t, x) = K (reflTransReparam t, x) := rfl
        _ = K (0, x) := by rw [hZero]
        _ = r₀ x := by simpa using K.apply_zero x
    · have hmem : 2 * (t : ℝ) - 1 ∈ I := by
        constructor
        · nlinarith [(not_le.1 ht).le]
        · nlinarith [t.2.2]
      have hReparam :
          reflTransReparam t = ⟨2 * t - 1, hmem⟩ := by
        apply Subtype.ext
        have hAux : reflTransReparamAux t = 2 * (t : ℝ) - 1 := by
          dsimp [reflTransReparamAux]
          rw [if_neg ht]
        simpa [reflTransReparam, hAux]
      have hTarget :
          ((ContinuousMap.Homotopy.refl r₀).trans K) (t, x) = K (⟨2 * t - 1, hmem⟩, x) := by
        rw [ContinuousMap.Homotopy.trans_apply]
        split_ifs with h
        · exact False.elim (ht h)
        · rfl
      rw [hTarget]
      calc
        Hreparam (t, x) = K (reflTransReparam t, x) := rfl
        _ = K (⟨2 * t - 1, hmem⟩, x) := by rw [hReparam]
  -- Collapse the idle first half by the generic endpoint-preserving reparametrization lemma.
  have hReparam :
      K.toContinuousMap.HomotopicRel Hreparam.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
    exact
      homotopyReparamHomotopicRel
        K reflTransReparam
        hReflTransReparam
        (by
          apply Subtype.ext
          simp [reflTransReparam, reflTransReparamAux])
        (by
          apply Subtype.ext
          norm_num [reflTransReparam, reflTransReparamAux])
  rcases ContinuousMap.HomotopicRel.symm hReparam with ⟨hReparam⟩
  exact ⟨hReparam.cast hEq rfl⟩

/-- Helper for Proposition 6.5.5: the exact cancellation
`L.symm.trans (L.trans K) ~ rel K` is obtained by rebracketing, contracting `L.symm.trans L`,
and then collapsing the reflexive prefix. -/
private theorem symmTransTransCancel_homotopyRel
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {r₀ r₁ r₂ : C(T, Z)}
    (L : r₀.Homotopy r₁) (K : r₁.Homotopy r₂) :
    (L.symm.trans (L.trans K)).toContinuousMap.HomotopicRel
      K.toContinuousMap
      (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
  -- Reassociate first so the existing `L.symm.trans L` contraction applies in the exact shape.
  refine ContinuousMap.HomotopicRel.trans
    (symmTransTrans_assoc_homotopyRel L K) ?_
  -- After contracting `L.symm.trans L`, only the reflexive left whisker of `K` remains.
  refine ContinuousMap.HomotopicRel.trans
    (symmTransTransReflCongrRight_homotopyRel L K) ?_
  -- Collapse the remaining reflexive prefix by reparametrizing away the idle initial segment.
  exact reflTrans_homotopyRel K

/-- Helper for Proposition 6.5.5: the left and right whiskerings of a homotopy equivalence inverse
agree on the time-boundary. -/
private theorem whiskeredInverseHomotopies_eq_boundary
    {T U : Type u} [TopologicalSpace T] [TopologicalSpace U]
    (e : T ≃ₕ U) (x : T) :
    let rightWhisker :
        (e.toFun.comp (e.symm.toFun.comp e.toFun)).Homotopy e.toFun :=
      ContinuousMap.Homotopy.comp e.right_inv.some (ContinuousMap.Homotopy.refl e.toFun)
    let leftWhisker :
        (e.toFun.comp (e.symm.toFun.comp e.toFun)).Homotopy e.toFun :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) e.left_inv.some
    rightWhisker (0, x) = leftWhisker (0, x) ∧
      rightWhisker (1, x) = leftWhisker (1, x) := by
  let rightWhisker :
      (e.toFun.comp (e.symm.toFun.comp e.toFun)).Homotopy e.toFun :=
    ContinuousMap.Homotopy.comp e.right_inv.some (ContinuousMap.Homotopy.refl e.toFun)
  let leftWhisker :
      (e.toFun.comp (e.symm.toFun.comp e.toFun)).Homotopy e.toFun :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl e.toFun) e.left_inv.some
  constructor
  · -- At time `0`, both whiskered homotopies start at the common composite `e ∘ e.symm ∘ e`.
    change e.right_inv.some (0, e.toFun x) = e.toFun (e.left_inv.some (0, x))
    rw [e.right_inv.some.apply_zero, e.left_inv.some.apply_zero]
    rfl
  · -- At time `1`, both whiskered homotopies end at the common map `e`.
    change e.right_inv.some (1, e.toFun x) = e.toFun (e.left_inv.some (1, x))
    rw [e.right_inv.some.apply_one, e.left_inv.some.apply_one]
    rfl

/-- Helper for Proposition 6.5.5: rebracketing a triple composite changes only the time
parameter, so the two bracketings are relative-homotopic on the time-boundary. -/
private theorem trans_assoc_homotopyRel
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {r₀ r₁ r₂ r₃ : C(T, Z)}
    (H₀ : r₀.Homotopy r₁) (H₁ : r₁.Homotopy r₂) (H₂ : r₂.Homotopy r₃) :
    ((H₀.trans H₁).trans H₂).toContinuousMap.HomotopicRel
      (H₀.trans (H₁.trans H₂)).toContinuousMap
      (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
  let assocReparam : I → I := fun t ↦
    ⟨Path.Homotopy.transAssocReparamAux t, Path.Homotopy.transAssocReparamAux_mem_I t⟩
  let Hreparam : r₀.Homotopy r₃ :=
    { toFun := fun tx ↦ (H₀.trans (H₁.trans H₂)) (assocReparam tx.1, tx.2)
      continuous_toFun := by
        have hpair : Continuous fun tx : I × T ↦ (assocReparam tx.1, tx.2) := by
          fun_prop
        simpa using (H₀.trans (H₁.trans H₂)).continuous.comp hpair
      map_zero_left := by
        intro x
        simpa [assocReparam, Path.Homotopy.transAssocReparamAux_zero] using
          (H₀.trans (H₁.trans H₂)).apply_zero x
      map_one_left := by
        intro x
        simpa [assocReparam, Path.Homotopy.transAssocReparamAux_one] using
          (H₀.trans (H₁.trans H₂)).apply_one x }
  have hEq :
      Hreparam.toContinuousMap = (((H₀.trans H₁).trans H₂).toContinuousMap) := by
    ext tx
    rcases tx with ⟨t, x⟩
    let p : Path (r₀ x) (r₁ x) := H₀.evalAt x
    let q : Path (r₁ x) (r₂ x) := H₁.evalAt x
    let r : Path (r₂ x) (r₃ x) := H₂.evalAt x
    have hPath := Path.Homotopy.trans_assoc_reparam p q r
    have hAt := congrArg (fun γ : Path (r₀ x) (r₃ x) => γ t) hPath.symm
    simpa [p, q, r, Hreparam, assocReparam, ContinuousMap.Homotopy.evalAt] using hAt
  -- Reassociate by reparametrizing the right-associated composite, then cast the source back to
  -- the left-associated spelling needed downstream.
  have hReparam :
      (H₀.trans (H₁.trans H₂)).toContinuousMap.HomotopicRel
        Hreparam.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
    exact
      homotopyReparamHomotopicRel
        (H₀.trans (H₁.trans H₂)) assocReparam
        (by
          fun_prop)
        (by
          apply Subtype.ext
          exact Path.Homotopy.transAssocReparamAux_zero)
        (by
          apply Subtype.ext
          exact Path.Homotopy.transAssocReparamAux_one)
  rcases ContinuousMap.HomotopicRel.symm hReparam with ⟨hReparam⟩
  exact ⟨hReparam.cast hEq rfl⟩

/-- Helper for Proposition 6.5.5: a relative comparison between the restricted ambient homotopy
and the whiskered subspace homotopy rectifies to an actual pair homotopy. -/
private theorem homotopicPairMap_of_restrictedAmbientHomotopicRel
    {i : C(A, X)} {j : C(B, Y)} (hi : IsCofibration.{u, u, u} i)
    {F₀ F₁ : PairMap i j}
    (K : F₀.subspaceMap.Homotopy F₁.subspaceMap)
    (H : F₀.ambientMap.Homotopy F₁.ambientMap)
    (hRel :
      (H.toContinuousMap.comp ((ContinuousMap.id I).prodMap i)).HomotopicRel
        ((ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl j) K).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set A))) :
    HomotopicPairMap F₀ F₁ := by
  rcases hRel with ⟨hRel⟩
  let boundaryPathFamily : C(A, C(I, Y)) :=
    (ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl j) K).toPathSpaceMap
  let rawK : C((I × A) × I, Y) :=
    { toFun := fun sat ↦ hRel.toHomotopy (sat.1.1, (sat.2, sat.1.2))
      continuous_toFun := by
        -- Repackage the relative contraction as a path-space homotopy over `A`.
        have hcoord : Continuous fun sat : (I × A) × I ↦ (sat.1.1, (sat.2, sat.1.2)) := by
          fun_prop
        simpa using hRel.toHomotopy.continuous.comp hcoord }
  let KPath : (H.toPathSpaceMap.comp i).Homotopy boundaryPathFamily :=
    { toContinuousMap := rawK.curry
      map_zero_left := by
        intro a
        -- At outer time `0`, the rebracketed homotopy is the original restricted ambient path
        -- family.
        ext t
        calc
          rawK.curry (0, a) t = hRel.toHomotopy (0, (t, a)) := rfl
          _ = (H.toContinuousMap.comp ((ContinuousMap.id I).prodMap i)) (t, a) := by
            exact hRel.toHomotopy.apply_zero (t, a)
          _ = (H.toPathSpaceMap.comp i) a t := rfl
      map_one_left := by
        intro a
        -- At outer time `1`, the same rebracketing is the desired whiskered subspace path family.
        ext t
        calc
          rawK.curry (1, a) t =
              ((ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl j) K).toContinuousMap)
                (t, a) := by
            change
              hRel.toHomotopy (1, (t, a)) =
                ((ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl j) K).toContinuousMap)
                  (t, a)
            exact hRel.toHomotopy.apply_one (t, a)
          _ = boundaryPathFamily a t := rfl }
  obtain ⟨G, L, hL⟩ := hi.exists_homotopy_extension
    (f₀ := H.toPathSpaceMap) (g := boundaryPathFamily) KPath
  have hGi : G.comp i = boundaryPathFamily := by
    -- Reading the time-`1` endpoint of the lifted path-space homotopy fixes the entire boundary
    -- path family exactly.
    ext a t
    calc
      G (i a) t = L (1, i a) t := by
        simpa using congrArg (fun γ : C(I, Y) => γ t) (L.apply_one (i a)).symm
      _ = KPath (1, a) t := by
        simpa using ContinuousMap.congr_fun (hL (1, a)) t
      _ = boundaryPathFamily a t := by
        simpa using ContinuousMap.congr_fun (KPath.apply_one a) t
  let V₀ : PairMap i j :=
    Arrow.homMk' (TopCat.ofHom F₀.subspaceMap) (TopCat.ofHom ((pathSpaceEvalAt 0 Y).comp G)) (by
      -- The `t = 0` face of the corrected path-space family is still a map of pairs with the
      -- original subspace map.
      apply congrArg TopCat.ofHom
      ext a
      change j (F₀.subspaceMap a) = ((pathSpaceEvalAt 0 Y).comp G) (i a)
      calc
        j (F₀.subspaceMap a) = j (K (0, a)) := by
          symm
          simpa using K.apply_zero a
        _ = boundaryPathFamily a 0 := by
          rfl
        _ = G (i a) 0 := by
          symm
          exact ContinuousMap.congr_fun (ContinuousMap.congr_fun hGi a) 0
        _ = ((pathSpaceEvalAt 0 Y).comp G) (i a) := rfl)
  let V₁ : PairMap i j :=
    Arrow.homMk' (TopCat.ofHom F₁.subspaceMap) (TopCat.ofHom ((pathSpaceEvalAt 1 Y).comp G)) (by
      -- The `t = 1` face similarly matches the terminal subspace map.
      apply congrArg TopCat.ofHom
      ext a
      change j (F₁.subspaceMap a) = ((pathSpaceEvalAt 1 Y).comp G) (i a)
      calc
        j (F₁.subspaceMap a) = j (K (1, a)) := by
          symm
          simpa using K.apply_one a
        _ = boundaryPathFamily a 1 := by
          rfl
        _ = G (i a) 1 := by
          symm
          exact ContinuousMap.congr_fun (ContinuousMap.congr_fun hGi a) 1
        _ = ((pathSpaceEvalAt 1 Y).comp G) (i a) := rfl)
  let sourceFaceRaw :
      ((pathSpaceEvalAt 0 Y).comp H.toPathSpaceMap).Homotopy ((pathSpaceEvalAt 0 Y).comp G) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl (pathSpaceEvalAt 0 Y)) L
  let sourceFace : F₀.ambientMap.Homotopy V₀.ambientMap :=
    sourceFaceRaw.cast H.pathSpaceEvalAtZero_comp_toPathSpaceMap rfl
  have hSourceFace : PairHomotopy F₀ V₀ := by
    refine
      { subspaceHomotopy := .refl F₀.subspaceMap
        ambientHomotopy := sourceFace
        comm := ?_ }
    intro z
    rcases z with ⟨s, a⟩
    have hBoundary0 :
        (H.toContinuousMap.comp ((ContinuousMap.id I).prodMap i)) (0, a) =
          j (F₀.subspaceMap a) := by
      calc
        (H.toContinuousMap.comp ((ContinuousMap.id I).prodMap i)) (0, a) = H (0, i a) := rfl
        _ = F₀.ambientMap (i a) := by
          simpa using H.apply_zero (i a)
        _ = j (F₀.subspaceMap a) := by
          simpa using ContinuousMap.congr_fun (PairMap.comm F₀) a
    have hRestricted0 : hRel.toHomotopy (s, (0, a)) = j (F₀.subspaceMap a) := by
      exact (hRel.eq_fst s ⟨by simp, by simp⟩).trans hBoundary0
    have hFace0 :
        (((pathSpaceEvalAt 0 Y).comp (L.curry s)).comp i) a = hRel.toHomotopy (s, (0, a)) := by
      calc
        (((pathSpaceEvalAt 0 Y).comp (L.curry s)).comp i) a =
            ((pathSpaceEvalAt 0 Y).comp (L.curry s)) (i a) := rfl
        _ = L (s, i a) 0 := rfl
        _ = KPath (s, a) 0 := by
          simpa using ContinuousMap.congr_fun (hL (s, a)) 0
        _ = hRel.toHomotopy (s, (0, a)) := rfl
    exact hFace0.trans hRestricted0
  let middleFace : V₀.ambientMap.Homotopy V₁.ambientMap :=
    ContinuousMap.Homotopy.ofPathSpaceMap G rfl rfl
  have hMiddleFace : PairHomotopy V₀ V₁ := by
    refine
      { subspaceHomotopy := K
        ambientHomotopy := middleFace
        comm := ?_ }
    intro z
    rcases z with ⟨s, a⟩
    calc
      middleFace (s, i a) = G (i a) s := rfl
      _ = boundaryPathFamily a s := by
        exact ContinuousMap.congr_fun (ContinuousMap.congr_fun hGi a) s
      _ = j (K (s, a)) := rfl
  let targetFaceRaw :
      ((pathSpaceEvalAt 1 Y).comp H.toPathSpaceMap).Homotopy ((pathSpaceEvalAt 1 Y).comp G) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl (pathSpaceEvalAt 1 Y)) L
  let targetFace : F₁.ambientMap.Homotopy V₁.ambientMap :=
    targetFaceRaw.cast ((H.pathSpaceEvalAt_comp_toPathSpaceMap 1).trans H.curry_one) rfl
  have hTargetFace : PairHomotopy F₁ V₁ := by
    refine
      { subspaceHomotopy := .refl F₁.subspaceMap
        ambientHomotopy := targetFace
        comm := ?_ }
    intro z
    rcases z with ⟨s, a⟩
    have hRestricted1 : hRel.toHomotopy (s, (1, a)) = j (F₁.subspaceMap a) := by
      calc
        hRel.toHomotopy (s, (1, a)) =
            ((ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl j) K).toContinuousMap)
              (1, a) := by
          exact hRel.eq_snd s ⟨by simp, by simp⟩
        _ = j (K (1, a)) := rfl
        _ = j (F₁.subspaceMap a) := by
          simpa using K.apply_one a
    have hFace1 :
        (((pathSpaceEvalAt 1 Y).comp (L.curry s)).comp i) a = hRel.toHomotopy (s, (1, a)) := by
      calc
        (((pathSpaceEvalAt 1 Y).comp (L.curry s)).comp i) a =
            ((pathSpaceEvalAt 1 Y).comp (L.curry s)) (i a) := rfl
        _ = L (s, i a) 1 := rfl
        _ = KPath (s, a) 1 := by
          simpa using ContinuousMap.congr_fun (hL (s, a)) 1
        _ = hRel.toHomotopy (s, (1, a)) := rfl
    exact hFace1.trans hRestricted1
  -- Compose the two endpoint faces with the corrected middle path-space family to obtain the
  -- desired pair homotopy.
  exact ⟨PairHomotopy.trans hSourceFace <|
    PairHomotopy.trans hMiddleFace hTargetFace.symm⟩

/-- Helper for Proposition 6.5.5: the chosen restricted ambient inverse homotopy from `j` to `i`
is an explicit term, so downstream normalization can rewrite through it directly. -/
private noncomputable abbrev correctedInverseRestrictionHomotopic
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap) :
    (eAmbient.symm.toFun.comp j).Homotopy (i.comp eSubspace.symm.toFun) := by
  -- Rewrite the square once so the restricted ambient inverse can be compared to the chosen
  -- subspace inverse.
  have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
    simpa [heSubspace, heAmbient] using PairMap.comm F
  let whiskeredRightInverse :
      (((eAmbient.symm.toFun.comp j).comp
          (eSubspace.toFun.comp eSubspace.symm.toFun))).Homotopy
        (eAmbient.symm.toFun.comp j) :=
    ContinuousMap.Homotopy.comp
      (ContinuousMap.Homotopy.refl (eAmbient.symm.toFun.comp j))
      eSubspace.right_inv.some
  let restrictedLeftInverse :
      (((eAmbient.symm.toFun.comp j).comp
          (eSubspace.toFun.comp eSubspace.symm.toFun))).Homotopy
        (i.comp eSubspace.symm.toFun) :=
    (eAmbient.left_inv.some.compContinuousMap (i.comp eSubspace.symm.toFun)).cast
      (by
        -- Normalize the source endpoint of the restricted ambient left inverse using the square.
        ext b
        simpa using congrArg eAmbient.symm.toFun
          (ContinuousMap.congr_fun hSquare (eSubspace.symm b)))
      (by simp)
  -- First insert the subspace self-equivalence loop, then collapse it using the ambient left
  -- inverse.
  exact whiskeredRightInverse.symm.trans restrictedLeftInverse

/-- Helper for Proposition 6.5.5: the explicit corrected inverse restriction starts at the raw
restricted ambient inverse. -/
private theorem correctedInverseRestrictionHomotopic_apply_zero
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap)
    (b : B) :
    correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient (0, b) =
      eAmbient.symm.toFun (j b) := by
  -- At time `0`, the inserted subspace loop has not yet changed the raw restricted ambient
  -- inverse.
  simp [correctedInverseRestrictionHomotopic]

/-- Helper for Proposition 6.5.5: the explicit corrected inverse restriction ends at the chosen
subspace inverse. -/
private theorem correctedInverseRestrictionHomotopic_apply_one
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap)
    (b : B) :
    correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient (1, b) =
      i (eSubspace.symm b) := by
  -- At time `1`, the correction has landed on the chosen subspace inverse.
  simp [correctedInverseRestrictionHomotopic]

/-- Helper for Proposition 6.5.5: a cofibration on `j` rectifies the ambient inverse into an
actual inverse square while retaining its restriction homotopy on `B`. -/
private theorem existsPairInverseMap_of_isCofibration
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j) (hj : IsCofibration.{u, u, u} j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap) :
    ∃ G : PairMap j i, G.subspaceMap = eSubspace.symm.toFun ∧
      ∃ hg : eAmbient.symm.toFun.Homotopy G.ambientMap,
        ∀ z : I × B,
          hg (z.1, j z.2) =
            (correctedInverseRestrictionHomotopic
              F eSubspace heSubspace eAmbient heAmbient) z :=
by
  let hBoundary :=
    correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
  -- Extend the boundary homotopy along `j`, but keep the exact restriction formula for the later
  -- pair-level compatibility check.
  obtain ⟨g, hg, hgRestrict⟩ := hj.exists_homotopy_extension
    (f₀ := eAmbient.symm.toFun) (g := i.comp eSubspace.symm.toFun) hBoundary
  have hgComm : g.comp j = i.comp eSubspace.symm.toFun := by
    -- Read the time-`1` endpoint of the extension to recover the corrected inverse square.
    ext b
    calc
      g (j b) = hg (1, j b) := by
        exact (hg.apply_one (j b)).symm
      _ = hBoundary (1, b) := by
        simpa using hgRestrict (1, b)
      _ = i (eSubspace.symm b) := by
        simpa using hBoundary.apply_one b
  let G : PairMap j i :=
    Arrow.homMk' (TopCat.ofHom eSubspace.symm.toFun) (TopCat.ofHom g) (by
      simpa using congrArg TopCat.ofHom hgComm.symm)
  refine ⟨G, rfl, ?_⟩
  refine ⟨hg, ?_⟩
  -- Package the exact boundary-control formula using the newly defined square.
  intro z
  simpa [G] using hgRestrict z

/-- Helper for Proposition 6.5.5: after rectifying the inverse square, the left composite
`F ≫ G` should contract to the identity through pair maps. -/
private theorem leftCompositeRestrictionEq
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j) (G : PairMap j i)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap)
    (hg : eAmbient.symm.toFun.Homotopy G.ambientMap)
    (hgRestrict :
      ∀ z : I × B,
        hg (z.1, j z.2) =
          (correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient) z) :
    let hBoundary :=
      correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
    let FfgRaw : (eAmbient.symm.toFun.comp eAmbient.toFun).Homotopy
        (G.ambientMap.comp eAmbient.toFun) :=
      ContinuousMap.Homotopy.comp hg (ContinuousMap.Homotopy.refl eAmbient.toFun)
    let FfgTargetEq : G.ambientMap.comp eAmbient.toFun = G.ambientMap.comp F.ambientMap := by
      ext x
      simp [heAmbient]
    let Ffg : (eAmbient.symm.toFun.comp eAmbient.toFun).Homotopy
        (G.ambientMap.comp F.ambientMap) :=
      FfgRaw.cast rfl FfgTargetEq
    let restrictedBoundaryRaw :
        ((eAmbient.symm.toFun.comp j).comp eSubspace.toFun).Homotopy
          ((i.comp eSubspace.symm.toFun).comp eSubspace.toFun) :=
      ContinuousMap.Homotopy.comp hBoundary (ContinuousMap.Homotopy.refl eSubspace.toFun)
    let restrictedBoundarySourceEq :
        (eAmbient.symm.toFun.comp j).comp eSubspace.toFun =
          (eAmbient.symm.toFun.comp eAmbient.toFun).comp i := by
      ext a
      have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
        simpa [heSubspace, heAmbient] using PairMap.comm F
      simpa using (congrArg eAmbient.symm.toFun (ContinuousMap.congr_fun hSquare a)).symm
    let restrictedBoundaryTargetEq :
        (i.comp eSubspace.symm.toFun).comp eSubspace.toFun =
          i.comp (eSubspace.symm.toFun.comp eSubspace.toFun) := by
      rfl
    let restrictedBoundary :
        ((eAmbient.symm.toFun.comp eAmbient.toFun).comp i).Homotopy
          (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)) :=
      restrictedBoundaryRaw.cast restrictedBoundarySourceEq restrictedBoundaryTargetEq
    ((Ffg.symm.trans eAmbient.left_inv.some).toContinuousMap).comp
        ((ContinuousMap.id I).prodMap i) =
      (restrictedBoundary.symm.trans
        (eAmbient.left_inv.some.compContinuousMap i)).toContinuousMap := by
  let hBoundary :=
    correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
  let FfgRaw : (eAmbient.symm.toFun.comp eAmbient.toFun).Homotopy
      (G.ambientMap.comp eAmbient.toFun) :=
    ContinuousMap.Homotopy.comp hg (ContinuousMap.Homotopy.refl eAmbient.toFun)
  have FfgTargetEq : G.ambientMap.comp eAmbient.toFun = G.ambientMap.comp F.ambientMap := by
    -- Normalize the ambient endpoint to the actual right-hand component of `F ≫ G`.
    ext x
    simp [heAmbient]
  let Ffg : (eAmbient.symm.toFun.comp eAmbient.toFun).Homotopy
      (G.ambientMap.comp F.ambientMap) :=
    FfgRaw.cast rfl FfgTargetEq
  let restrictedBoundaryRaw :
      ((eAmbient.symm.toFun.comp j).comp eSubspace.toFun).Homotopy
        ((i.comp eSubspace.symm.toFun).comp eSubspace.toFun) :=
    ContinuousMap.Homotopy.comp hBoundary (ContinuousMap.Homotopy.refl eSubspace.toFun)
  have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
    -- Rewrite the square once so the restriction can be compared on `A`.
    simpa [heSubspace, heAmbient] using PairMap.comm F
  have restrictedBoundarySourceEq :
      (eAmbient.symm.toFun.comp j).comp eSubspace.toFun =
        (eAmbient.symm.toFun.comp eAmbient.toFun).comp i := by
    -- This is the only place where the commutative square is used in the left normalization.
    ext a
    simpa using (congrArg eAmbient.symm.toFun (ContinuousMap.congr_fun hSquare a)).symm
  let restrictedBoundary :
      ((eAmbient.symm.toFun.comp eAmbient.toFun).comp i).Homotopy
        (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)) :=
    restrictedBoundaryRaw.cast restrictedBoundarySourceEq rfl
  have hFfg :
      Ffg.toContinuousMap.comp ((ContinuousMap.id I).prodMap i) =
        restrictedBoundary.toContinuousMap := by
    -- Restrict the ambient composite homotopy along `i` and rewrite it through the corrected
    -- boundary homotopy on `B`.
    ext z
    rcases z with ⟨t, a⟩
    calc
      Ffg (t, i a) = hg (t, eAmbient.toFun (i a)) := by
        rfl
      _ = hg (t, j (eSubspace a)) := by
        rw [show eAmbient.toFun (i a) = j (eSubspace a) by
          simpa using ContinuousMap.congr_fun hSquare a]
      _ = hBoundary (t, eSubspace a) := hgRestrict (t, eSubspace a)
      _ = restrictedBoundary (t, a) := by
        rfl
  -- Compare the restricted left composite pointwise with the normalized boundary loop.
  ext z
  rcases z with ⟨t, a⟩
  change (Ffg.symm.trans eAmbient.left_inv.some) (t, i a) =
    (restrictedBoundary.symm.trans (eAmbient.left_inv.some.compContinuousMap i)) (t, a)
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · simpa [ContinuousMap.Homotopy.symm] using
      ContinuousMap.congr_fun hFfg
        (σ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, a)
  · rfl

/-- Helper for Proposition 6.5.5: restricting the right ambient composite homotopy along `j`
normalizes it to the loop induced by the corrected inverse on `B`. -/
private theorem rightCompositeRestrictionEq
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j) (G : PairMap j i)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap)
    (hg : eAmbient.symm.toFun.Homotopy G.ambientMap)
    (hgRestrict :
      ∀ z : I × B,
        hg (z.1, j z.2) =
          (correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient) z) :
    let hBoundary :=
      correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
    let FgfRaw : (eAmbient.toFun.comp eAmbient.symm.toFun).Homotopy
        (eAmbient.toFun.comp G.ambientMap) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl eAmbient.toFun) hg
    let FgfTargetEq : eAmbient.toFun.comp G.ambientMap = F.ambientMap.comp G.ambientMap := by
      ext y
      simp [heAmbient]
    let Fgf : (eAmbient.toFun.comp eAmbient.symm.toFun).Homotopy
        (F.ambientMap.comp G.ambientMap) :=
      FgfRaw.cast rfl FgfTargetEq
    let restrictedBoundaryRaw :
        ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
          ((eAmbient.toFun.comp i).comp eSubspace.symm.toFun) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl eAmbient.toFun) hBoundary
    let restrictedBoundarySourceEq :
        (eAmbient.toFun.comp eAmbient.symm.toFun).comp j =
          (eAmbient.toFun.comp eAmbient.symm.toFun).comp j := by
      rfl
    let restrictedBoundaryTargetEq :
        (eAmbient.toFun.comp i).comp eSubspace.symm.toFun =
          j.comp (eSubspace.toFun.comp eSubspace.symm.toFun) := by
      ext b
      have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
        simpa [heSubspace, heAmbient] using PairMap.comm F
      simpa using ContinuousMap.congr_fun hSquare (eSubspace.symm b)
    let restrictedBoundary :
        ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
          (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)) :=
      restrictedBoundaryRaw.cast restrictedBoundarySourceEq restrictedBoundaryTargetEq
    ((Fgf.symm.trans eAmbient.right_inv.some).toContinuousMap).comp
        ((ContinuousMap.id I).prodMap j) =
      (restrictedBoundary.symm.trans
        (eAmbient.right_inv.some.compContinuousMap j)).toContinuousMap := by
  let hBoundary :=
    correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
  let FgfRaw : (eAmbient.toFun.comp eAmbient.symm.toFun).Homotopy
      (eAmbient.toFun.comp G.ambientMap) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl eAmbient.toFun) hg
  have FgfTargetEq : eAmbient.toFun.comp G.ambientMap = F.ambientMap.comp G.ambientMap := by
    -- Normalize the ambient endpoint to the actual right-hand component of `G ≫ F`.
    ext y
    simp [heAmbient]
  let Fgf : (eAmbient.toFun.comp eAmbient.symm.toFun).Homotopy
      (F.ambientMap.comp G.ambientMap) :=
    FgfRaw.cast rfl FgfTargetEq
  let restrictedBoundaryRaw :
      ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
        ((eAmbient.toFun.comp i).comp eSubspace.symm.toFun) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl eAmbient.toFun) hBoundary
  have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
    -- Rewrite the square once so the restriction can be compared on `B`.
    simpa [heSubspace, heAmbient] using PairMap.comm F
  have restrictedBoundaryTargetEq :
      (eAmbient.toFun.comp i).comp eSubspace.symm.toFun =
        j.comp (eSubspace.toFun.comp eSubspace.symm.toFun) := by
    -- The corrected boundary target is the whiskered right inverse on `B`.
    ext b
    simpa using ContinuousMap.congr_fun hSquare (eSubspace.symm b)
  let restrictedBoundary :
      ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
        (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)) :=
    restrictedBoundaryRaw.cast rfl restrictedBoundaryTargetEq
  have hFgf :
      Fgf.toContinuousMap.comp ((ContinuousMap.id I).prodMap j) =
        restrictedBoundary.toContinuousMap := by
    -- Restrict the ambient composite homotopy along `j` and rewrite it through the corrected
    -- boundary homotopy produced on `B`.
    ext z
    rcases z with ⟨t, b⟩
    calc
      Fgf (t, j b) = eAmbient.toFun (hg (t, j b)) := by
        rfl
      _ = eAmbient.toFun (hBoundary (t, b)) := by
        rw [hgRestrict (t, b)]
      _ = restrictedBoundary (t, b) := by
        rfl
  -- Compare the restricted right composite pointwise with the normalized boundary loop.
  ext z
  rcases z with ⟨t, b⟩
  change (Fgf.symm.trans eAmbient.right_inv.some) (t, j b) =
    (restrictedBoundary.symm.trans (eAmbient.right_inv.some.compContinuousMap j)) (t, b)
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · simpa [ContinuousMap.Homotopy.symm] using
      ContinuousMap.congr_fun hFgf
        (σ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, b)
  · rfl

/-- Helper for Proposition 6.5.5: the left composite subspace map is the expected
`eSubspace.symm ≫ eSubspace` composite. -/
private theorem leftCompositeSubspaceMap_eq
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j) (G : PairMap j i)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (hGsub : G.subspaceMap = eSubspace.symm.toFun) :
    eSubspace.symm.toFun.comp eSubspace.toFun = PairMap.subspaceMap (F ≫ G) := by
  -- Rewrite the left composite subspace map directly to the chosen inverse composite.
  ext a
  change eSubspace.symm.toFun (eSubspace.toFun a) = G.subspaceMap (F.subspaceMap a)
  simp [heSubspace, hGsub]

/-- Helper for Proposition 6.5.5: the right composite subspace map is the expected
`eSubspace ≫ eSubspace.symm` composite. -/
private theorem rightCompositeSubspaceMap_eq
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j) (G : PairMap j i)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (hGsub : G.subspaceMap = eSubspace.symm.toFun) :
    eSubspace.toFun.comp eSubspace.symm.toFun = PairMap.subspaceMap (G ≫ F) := by
  -- Rewrite the right composite subspace map directly to the chosen inverse composite.
  ext b
  change eSubspace.toFun (eSubspace.symm.toFun b) = F.subspaceMap (G.subspaceMap b)
  simp [heSubspace, hGsub]

/-- Helper for Proposition 6.5.5: both normalized restricted ambient loops should compare
relative to the boundary with the corresponding whiskered subspace inverse homotopies. -/
private theorem leftRestrictedBoundaryWhisker_eq_boundary
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap)
    (a : A) :
    let hBoundary :=
      correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
    let restrictedBoundaryRaw :
        ((eAmbient.symm.toFun.comp j).comp eSubspace.toFun).Homotopy
          ((i.comp eSubspace.symm.toFun).comp eSubspace.toFun) :=
      ContinuousMap.Homotopy.comp hBoundary (ContinuousMap.Homotopy.refl eSubspace.toFun)
    let restrictedBoundarySourceEq :
        (eAmbient.symm.toFun.comp j).comp eSubspace.toFun =
          (eAmbient.symm.toFun.comp eAmbient.toFun).comp i := by
      ext a
      have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
        simpa [heSubspace, heAmbient] using PairMap.comm F
      simpa using (congrArg eAmbient.symm.toFun (ContinuousMap.congr_fun hSquare a)).symm
    let restrictedBoundary :
        ((eAmbient.symm.toFun.comp eAmbient.toFun).comp i).Homotopy
          (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)) :=
      restrictedBoundaryRaw.cast restrictedBoundarySourceEq rfl
    let KleftNormalized :
        (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)).Homotopy
          (i.comp (ContinuousMap.id A)) :=
      ContinuousMap.Homotopy.comp
        (ContinuousMap.Homotopy.refl i) eSubspace.symm.right_inv.some
    ((restrictedBoundary.symm.trans
        (eAmbient.left_inv.some.compContinuousMap i)) (0, a) = KleftNormalized (0, a)) ∧
      ((restrictedBoundary.symm.trans
        (eAmbient.left_inv.some.compContinuousMap i)) (1, a) = KleftNormalized (1, a)) := by
  let hBoundary :=
    correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
  let restrictedBoundaryRaw :
      ((eAmbient.symm.toFun.comp j).comp eSubspace.toFun).Homotopy
        ((i.comp eSubspace.symm.toFun).comp eSubspace.toFun) :=
    ContinuousMap.Homotopy.comp hBoundary (ContinuousMap.Homotopy.refl eSubspace.toFun)
  have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
    -- Reuse the commutative square to normalize the source of the restricted boundary.
    simpa [heSubspace, heAmbient] using PairMap.comm F
  have restrictedBoundarySourceEq :
      (eAmbient.symm.toFun.comp j).comp eSubspace.toFun =
        (eAmbient.symm.toFun.comp eAmbient.toFun).comp i := by
    -- This is the same source rewrite used in the left branch of the main proof.
    ext a
    simpa using (congrArg eAmbient.symm.toFun (ContinuousMap.congr_fun hSquare a)).symm
  let restrictedBoundary :
      ((eAmbient.symm.toFun.comp eAmbient.toFun).comp i).Homotopy
        (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)) :=
    restrictedBoundaryRaw.cast restrictedBoundarySourceEq rfl
  let KleftNormalized :
      (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)).Homotopy
        (i.comp (ContinuousMap.id A)) :=
    ContinuousMap.Homotopy.comp
      (ContinuousMap.Homotopy.refl i) eSubspace.symm.right_inv.some
  constructor
  · -- At time `0`, both loops start at `i ∘ eSubspace.symm ∘ eSubspace`.
    simp
  · -- At time `1`, both loops end at `i`.
    simp

/-- Helper for Proposition 6.5.5: the normalized right restricted loop already matches the
whiskered subspace inverse on the two endpoint time-slices. -/
private theorem rightRestrictedBoundaryWhisker_eq_boundary
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap)
    (b : B) :
    let hBoundary :=
      correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
    let restrictedBoundaryRaw :
        ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
          ((eAmbient.toFun.comp i).comp eSubspace.symm.toFun) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl eAmbient.toFun) hBoundary
    let restrictedBoundaryTargetEq :
        (eAmbient.toFun.comp i).comp eSubspace.symm.toFun =
          j.comp (eSubspace.toFun.comp eSubspace.symm.toFun) := by
      ext b
      have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
        simpa [heSubspace, heAmbient] using PairMap.comm F
      simpa using ContinuousMap.congr_fun hSquare (eSubspace.symm b)
    let restrictedBoundary :
        ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
          (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)) :=
      restrictedBoundaryRaw.cast rfl restrictedBoundaryTargetEq
    let KrightNormalized :
        (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)).Homotopy
          (j.comp (ContinuousMap.id B)) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl j) eSubspace.right_inv.some
    ((restrictedBoundary.symm.trans
        (eAmbient.right_inv.some.compContinuousMap j)) (0, b) = KrightNormalized (0, b)) ∧
      ((restrictedBoundary.symm.trans
        (eAmbient.right_inv.some.compContinuousMap j)) (1, b) = KrightNormalized (1, b)) := by
  let hBoundary :=
    correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
  let restrictedBoundaryRaw :
      ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
        ((eAmbient.toFun.comp i).comp eSubspace.symm.toFun) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl eAmbient.toFun) hBoundary
  have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
    -- Reuse the commutative square to normalize the target of the restricted boundary.
    simpa [heSubspace, heAmbient] using PairMap.comm F
  have restrictedBoundaryTargetEq :
      (eAmbient.toFun.comp i).comp eSubspace.symm.toFun =
        j.comp (eSubspace.toFun.comp eSubspace.symm.toFun) := by
    -- This is the same target rewrite used in the right branch of the main proof.
    ext b
    simpa using ContinuousMap.congr_fun hSquare (eSubspace.symm b)
  let restrictedBoundary :
      ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
        (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)) :=
    restrictedBoundaryRaw.cast rfl restrictedBoundaryTargetEq
  let KrightNormalized :
      (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)).Homotopy
        (j.comp (ContinuousMap.id B)) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl j) eSubspace.right_inv.some
  constructor
  · -- At time `0`, both loops start at `j ∘ eSubspace ∘ eSubspace.symm`.
    simp
  · -- At time `1`, both loops end at `j`.
    simp

/-- Helper for Proposition 6.5.5: extract the `t = 0` boundary equality from the left normalized
restricted loop comparison. -/
private theorem leftRestrictedBoundaryWhisker_eq_zero
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap)
    (a : A) :
    let hBoundary :=
      correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
    let restrictedBoundaryRaw :
        ((eAmbient.symm.toFun.comp j).comp eSubspace.toFun).Homotopy
          ((i.comp eSubspace.symm.toFun).comp eSubspace.toFun) :=
      ContinuousMap.Homotopy.comp hBoundary (ContinuousMap.Homotopy.refl eSubspace.toFun)
    let restrictedBoundarySourceEq :
        (eAmbient.symm.toFun.comp j).comp eSubspace.toFun =
          (eAmbient.symm.toFun.comp eAmbient.toFun).comp i := by
      ext a
      have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
        simpa [heSubspace, heAmbient] using PairMap.comm F
      simpa using (congrArg eAmbient.symm.toFun (ContinuousMap.congr_fun hSquare a)).symm
    let restrictedBoundary :
        ((eAmbient.symm.toFun.comp eAmbient.toFun).comp i).Homotopy
          (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)) :=
      restrictedBoundaryRaw.cast restrictedBoundarySourceEq rfl
    let KleftNormalized :
        (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)).Homotopy
          (i.comp (ContinuousMap.id A)) :=
      ContinuousMap.Homotopy.comp
        (ContinuousMap.Homotopy.refl i) eSubspace.symm.right_inv.some
    ((restrictedBoundary.symm.trans
        (eAmbient.left_inv.some.compContinuousMap i)) (0, a) = KleftNormalized (0, a)) := by
  -- Read only the `t = 0` face from the already-established endpoint comparison.
  exact (leftRestrictedBoundaryWhisker_eq_boundary
    F eSubspace heSubspace eAmbient heAmbient a).1

/-- Helper for Proposition 6.5.5: extract the `t = 1` boundary equality from the right normalized
restricted loop comparison. -/
private theorem rightRestrictedBoundaryWhisker_eq_one
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap)
    (b : B) :
    let hBoundary :=
      correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
    let restrictedBoundaryRaw :
        ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
          ((eAmbient.toFun.comp i).comp eSubspace.symm.toFun) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl eAmbient.toFun) hBoundary
    let restrictedBoundaryTargetEq :
        (eAmbient.toFun.comp i).comp eSubspace.symm.toFun =
          j.comp (eSubspace.toFun.comp eSubspace.symm.toFun) := by
      ext b
      have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
        simpa [heSubspace, heAmbient] using PairMap.comm F
      simpa using ContinuousMap.congr_fun hSquare (eSubspace.symm b)
    let restrictedBoundary :
        ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
          (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)) :=
      restrictedBoundaryRaw.cast rfl restrictedBoundaryTargetEq
    let KrightNormalized :
        (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)).Homotopy
          (j.comp (ContinuousMap.id B)) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl j) eSubspace.right_inv.some
    ((restrictedBoundary.symm.trans
        (eAmbient.right_inv.some.compContinuousMap j)) (1, b) = KrightNormalized (1, b)) := by
  -- Read only the `t = 1` face from the already-established endpoint comparison.
  exact (rightRestrictedBoundaryWhisker_eq_boundary
    F eSubspace heSubspace eAmbient heAmbient b).2

/-- Helper for Proposition 6.5.5: restricting the inserted right-inverse whisker to `A` rewrites
its source to the ambient left-composite source followed by the subspace self-loop. -/
private theorem leftInsertedSourceLoopSourceEq
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap) :
    (((eAmbient.symm.toFun.comp j).comp
        (eSubspace.toFun.comp eSubspace.symm.toFun)).comp eSubspace.toFun) =
      (((eAmbient.symm.toFun.comp eAmbient.toFun).comp i).comp
        (eSubspace.symm.toFun.comp eSubspace.toFun)) := by
  have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
    -- Reuse the commutative square at the corrected subspace point.
    simpa [heSubspace, heAmbient] using PairMap.comm F
  ext a
  change
    eAmbient.symm.toFun
        (j (eSubspace.toFun (eSubspace.symm.toFun (eSubspace.toFun a)))) =
      eAmbient.symm.toFun
        (eAmbient.toFun (i (eSubspace.symm.toFun (eSubspace.toFun a))))
  simpa using
    (congrArg eAmbient.symm.toFun
      (ContinuousMap.congr_fun hSquare (eSubspace.symm.toFun (eSubspace.toFun a)))).symm

/-- Helper for Proposition 6.5.5: restricting the corrected inverse along `eSubspace.symm`
rewrites the right branch target to the explicit inserted target loop on `B`. -/
private theorem rightInsertedTargetLoopTargetEq
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap) :
    ((eAmbient.toFun.comp i).comp eSubspace.symm.toFun) =
      (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)) := by
  have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
    -- Reuse the original commutative square before evaluating at the chosen inverse point.
    simpa [heSubspace, heAmbient] using PairMap.comm F
  ext b
  -- Evaluate the square on `eSubspace.symm b` so the inserted target loop is visible on `B`.
  simpa using ContinuousMap.congr_fun hSquare (eSubspace.symm b)

/-- Helper for Proposition 6.5.5: the left normalized restricted loop needs an explicit interior
square whose vertical faces are fixed on the time-boundary. -/
private theorem leftNormalizedRestrictionComparison
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap) :
    let hBoundary :=
      correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
    let restrictedBoundaryRaw :
        ((eAmbient.symm.toFun.comp j).comp eSubspace.toFun).Homotopy
          ((i.comp eSubspace.symm.toFun).comp eSubspace.toFun) :=
      ContinuousMap.Homotopy.comp hBoundary (ContinuousMap.Homotopy.refl eSubspace.toFun)
    let restrictedBoundarySourceEq :
        (eAmbient.symm.toFun.comp j).comp eSubspace.toFun =
          (eAmbient.symm.toFun.comp eAmbient.toFun).comp i := by
      ext a
      have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
        simpa [heSubspace, heAmbient] using PairMap.comm F
      simpa using (congrArg eAmbient.symm.toFun (ContinuousMap.congr_fun hSquare a)).symm
    let restrictedBoundary :
        ((eAmbient.symm.toFun.comp eAmbient.toFun).comp i).Homotopy
          (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)) :=
      restrictedBoundaryRaw.cast restrictedBoundarySourceEq rfl
    let KleftNormalized :
        (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)).Homotopy
          (i.comp (ContinuousMap.id A)) :=
      ContinuousMap.Homotopy.comp
        (ContinuousMap.Homotopy.refl i) eSubspace.symm.right_inv.some
    ((restrictedBoundary.symm.trans
        (eAmbient.left_inv.some.compContinuousMap i)).toContinuousMap).HomotopicRel
      KleftNormalized.toContinuousMap
      (({0, 1} : Set I) ×ˢ (Set.univ : Set A)) := by
  -- Route correction: the square packaging is already solved, so the remaining work is this
  -- exact branch-local `HomotopicRel` witness in the normalized spelling used downstream.
  -- TODO: use `leftInsertedSourceLoopSourceEq` to keep the inserted source loop explicit, then
  -- prove the direct factorization comparison
  -- `eAmbient.left_inv.some.compContinuousMap i ~ rel restrictedBoundary.trans KleftNormalized`,
  -- then whisker it through `restrictedBoundary.symm` and close with
  -- `symmTransTransCancel_homotopyRel restrictedBoundary KleftNormalized`.
  sorry

/-- Helper for Proposition 6.5.5: the left normalized restricted loop needs an explicit interior
square whose vertical faces are fixed on the time-boundary. -/
private theorem leftNormalizedRestrictionInteriorSquare
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap) :
    let hBoundary :=
      correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
    let restrictedBoundaryRaw :
        ((eAmbient.symm.toFun.comp j).comp eSubspace.toFun).Homotopy
          ((i.comp eSubspace.symm.toFun).comp eSubspace.toFun) :=
      ContinuousMap.Homotopy.comp hBoundary (ContinuousMap.Homotopy.refl eSubspace.toFun)
    let restrictedBoundarySourceEq :
        (eAmbient.symm.toFun.comp j).comp eSubspace.toFun =
          (eAmbient.symm.toFun.comp eAmbient.toFun).comp i := by
      ext a
      have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
        simpa [heSubspace, heAmbient] using PairMap.comm F
      simpa using (congrArg eAmbient.symm.toFun (ContinuousMap.congr_fun hSquare a)).symm
    let restrictedBoundary :
        ((eAmbient.symm.toFun.comp eAmbient.toFun).comp i).Homotopy
          (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)) :=
      restrictedBoundaryRaw.cast restrictedBoundarySourceEq rfl
    let KleftNormalized :
        (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)).Homotopy
          (i.comp (ContinuousMap.id A)) :=
      ContinuousMap.Homotopy.comp
        (ContinuousMap.Homotopy.refl i) eSubspace.symm.right_inv.some
    ∃ square : C((I × A) × I, X),
      (∀ tx : I × A,
        square (tx, 0) =
          (restrictedBoundary.symm.trans
            (eAmbient.left_inv.some.compContinuousMap i)) tx) ∧
      (∀ tx : I × A, square (tx, 1) = KleftNormalized tx) ∧
      (∀ s : I, ∀ x : A, square ((0, x), s) =
        (restrictedBoundary.symm.trans
          (eAmbient.left_inv.some.compContinuousMap i)) (0, x)) ∧
      (∀ s : I, ∀ x : A, square ((1, x), s) =
        (restrictedBoundary.symm.trans
          (eAmbient.left_inv.some.compContinuousMap i)) (1, x)) := by
  -- Once the direct normalized comparison is available, the square is the underlying two-parameter
  -- family recorded by `boundaryFixedSquareOfHomotopyRel`.
  simpa using
    boundaryFixedSquareOfHomotopyRel
      (leftNormalizedRestrictionComparison F eSubspace heSubspace eAmbient heAmbient)

/-- Helper for Proposition 6.5.5: the right normalized restricted loop needs the symmetric
interior square whose vertical faces are fixed on the time-boundary. -/
private theorem rightNormalizedRestrictionComparison
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap) :
    let hBoundary :=
      correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
    let restrictedBoundaryRaw :
        ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
          ((eAmbient.toFun.comp i).comp eSubspace.symm.toFun) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl eAmbient.toFun) hBoundary
    let restrictedBoundaryTargetEq :
        (eAmbient.toFun.comp i).comp eSubspace.symm.toFun =
          j.comp (eSubspace.toFun.comp eSubspace.symm.toFun) := by
      ext b
      have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
        simpa [heSubspace, heAmbient] using PairMap.comm F
      simpa using ContinuousMap.congr_fun hSquare (eSubspace.symm b)
    let restrictedBoundary :
        ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
          (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)) :=
      restrictedBoundaryRaw.cast rfl restrictedBoundaryTargetEq
    let KrightNormalized :
        (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)).Homotopy
          (j.comp (ContinuousMap.id B)) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl j) eSubspace.right_inv.some
    ((restrictedBoundary.symm.trans
        (eAmbient.right_inv.some.compContinuousMap j)).toContinuousMap).HomotopicRel
      KrightNormalized.toContinuousMap
      (({0, 1} : Set I) ×ˢ (Set.univ : Set B)) := by
  -- Route correction: the symmetric branch has the same remaining frontier, so keep the blocker in
  -- the exact normalized statement consumed by the downstream pair-level rectifier.
  -- TODO: prove the direct factorization comparison
  -- `eAmbient.right_inv.some.compContinuousMap j ~ rel restrictedBoundary.trans KrightNormalized`,
  -- then whisker it through `restrictedBoundary.symm` and close with
  -- `symmTransTransCancel_homotopyRel restrictedBoundary KrightNormalized`.
  sorry

/-- Helper for Proposition 6.5.5: the right normalized restricted loop needs the symmetric
interior square whose vertical faces are fixed on the time-boundary. -/
private theorem rightNormalizedRestrictionInteriorSquare
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap) :
    let hBoundary :=
      correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
    let restrictedBoundaryRaw :
        ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
          ((eAmbient.toFun.comp i).comp eSubspace.symm.toFun) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl eAmbient.toFun) hBoundary
    let restrictedBoundaryTargetEq :
        (eAmbient.toFun.comp i).comp eSubspace.symm.toFun =
          j.comp (eSubspace.toFun.comp eSubspace.symm.toFun) := by
      ext b
      have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
        simpa [heSubspace, heAmbient] using PairMap.comm F
      simpa using ContinuousMap.congr_fun hSquare (eSubspace.symm b)
    let restrictedBoundary :
        ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
          (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)) :=
      restrictedBoundaryRaw.cast rfl restrictedBoundaryTargetEq
    let KrightNormalized :
        (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)).Homotopy
          (j.comp (ContinuousMap.id B)) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl j) eSubspace.right_inv.some
    ∃ square : C((I × B) × I, Y),
      (∀ tx : I × B,
        square (tx, 0) =
          (restrictedBoundary.symm.trans
            (eAmbient.right_inv.some.compContinuousMap j)) tx) ∧
      (∀ tx : I × B, square (tx, 1) = KrightNormalized tx) ∧
      (∀ s : I, ∀ x : B, square ((0, x), s) =
        (restrictedBoundary.symm.trans
          (eAmbient.right_inv.some.compContinuousMap j)) (0, x)) ∧
      (∀ s : I, ∀ x : B, square ((1, x), s) =
        (restrictedBoundary.symm.trans
          (eAmbient.right_inv.some.compContinuousMap j)) (1, x)) := by
  -- The right branch uses the same extractor once the normalized comparison has been isolated.
  simpa using
    boundaryFixedSquareOfHomotopyRel
      (rightNormalizedRestrictionComparison F eSubspace heSubspace eAmbient heAmbient)

private theorem restrictedBoundaryWhiskerComparisons
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j) (_G : PairMap j i)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap)
    (_hg : eAmbient.symm.toFun.Homotopy _G.ambientMap) :
    (let hBoundary :=
        correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
      let restrictedBoundaryRaw :
          ((eAmbient.symm.toFun.comp j).comp eSubspace.toFun).Homotopy
            ((i.comp eSubspace.symm.toFun).comp eSubspace.toFun) :=
        ContinuousMap.Homotopy.comp hBoundary (ContinuousMap.Homotopy.refl eSubspace.toFun)
      let restrictedBoundarySourceEq :
          (eAmbient.symm.toFun.comp j).comp eSubspace.toFun =
            (eAmbient.symm.toFun.comp eAmbient.toFun).comp i := by
        ext a
        have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
          simpa [heSubspace, heAmbient] using PairMap.comm F
        simpa using (congrArg eAmbient.symm.toFun (ContinuousMap.congr_fun hSquare a)).symm
      let restrictedBoundary :
          ((eAmbient.symm.toFun.comp eAmbient.toFun).comp i).Homotopy
            (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)) :=
        restrictedBoundaryRaw.cast restrictedBoundarySourceEq rfl
      let KleftNormalized :
          (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)).Homotopy
            (i.comp (ContinuousMap.id A)) :=
        ContinuousMap.Homotopy.comp
          (ContinuousMap.Homotopy.refl i) eSubspace.symm.right_inv.some
      ((restrictedBoundary.symm.trans
          (eAmbient.left_inv.some.compContinuousMap i)).toContinuousMap).HomotopicRel
        KleftNormalized.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set A)))
    ∧
    (let hBoundary :=
        correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
      let restrictedBoundaryRaw :
          ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
            ((eAmbient.toFun.comp i).comp eSubspace.symm.toFun) :=
        ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl eAmbient.toFun) hBoundary
      let restrictedBoundaryTargetEq :
          (eAmbient.toFun.comp i).comp eSubspace.symm.toFun =
            j.comp (eSubspace.toFun.comp eSubspace.symm.toFun) := by
        ext b
        have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
          simpa [heSubspace, heAmbient] using PairMap.comm F
        simpa using ContinuousMap.congr_fun hSquare (eSubspace.symm b)
      let restrictedBoundary :
          ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
            (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)) :=
        restrictedBoundaryRaw.cast rfl restrictedBoundaryTargetEq
      let KrightNormalized :
          (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)).Homotopy
            (j.comp (ContinuousMap.id B)) :=
        ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl j) eSubspace.right_inv.some
      ((restrictedBoundary.symm.trans
          (eAmbient.right_inv.some.compContinuousMap j)).toContinuousMap).HomotopicRel
        KrightNormalized.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set B))) := by
  -- Route correction: both branch blockers are the same transport problem packaged on opposite
  -- sides of the square, so keep them synchronized behind one frontier theorem.
  constructor
  · -- Package the explicit left branch filler square as the required relative comparison.
    let hBoundary :=
      correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
    let restrictedBoundaryRaw :
        ((eAmbient.symm.toFun.comp j).comp eSubspace.toFun).Homotopy
          ((i.comp eSubspace.symm.toFun).comp eSubspace.toFun) :=
      ContinuousMap.Homotopy.comp hBoundary (ContinuousMap.Homotopy.refl eSubspace.toFun)
    let restrictedBoundarySourceEq :
        (eAmbient.symm.toFun.comp j).comp eSubspace.toFun =
          (eAmbient.symm.toFun.comp eAmbient.toFun).comp i := by
      ext a
      have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
        simpa [heSubspace, heAmbient] using PairMap.comm F
      simpa using (congrArg eAmbient.symm.toFun (ContinuousMap.congr_fun hSquare a)).symm
    let restrictedBoundary :
        ((eAmbient.symm.toFun.comp eAmbient.toFun).comp i).Homotopy
          (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)) :=
      restrictedBoundaryRaw.cast restrictedBoundarySourceEq rfl
    let KleftNormalized :
        (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)).Homotopy
          (i.comp (ContinuousMap.id A)) :=
      ContinuousMap.Homotopy.comp
        (ContinuousMap.Homotopy.refl i) eSubspace.symm.right_inv.some
    obtain ⟨square, hZero, hOne, hLeft, hRight⟩ :=
      leftNormalizedRestrictionInteriorSquare F eSubspace heSubspace eAmbient heAmbient
    exact homotopyRelOfBoundaryFixedSquare square hZero hOne hLeft hRight
  · -- Package the symmetric right branch filler square in the same way.
    let hBoundary :=
      correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
    let restrictedBoundaryRaw :
        ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
          ((eAmbient.toFun.comp i).comp eSubspace.symm.toFun) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl eAmbient.toFun) hBoundary
    let restrictedBoundaryTargetEq :
        (eAmbient.toFun.comp i).comp eSubspace.symm.toFun =
          j.comp (eSubspace.toFun.comp eSubspace.symm.toFun) := by
      ext b
      have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
        simpa [heSubspace, heAmbient] using PairMap.comm F
      simpa using ContinuousMap.congr_fun hSquare (eSubspace.symm b)
    let restrictedBoundary :
        ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
          (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)) :=
      restrictedBoundaryRaw.cast rfl restrictedBoundaryTargetEq
    let KrightNormalized :
        (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)).Homotopy
          (j.comp (ContinuousMap.id B)) :=
      ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl j) eSubspace.right_inv.some
    obtain ⟨square, hZero, hOne, hLeft, hRight⟩ :=
      rightNormalizedRestrictionInteriorSquare F eSubspace heSubspace eAmbient heAmbient
    exact homotopyRelOfBoundaryFixedSquare square hZero hOne hLeft hRight

/-- Helper for Proposition 6.5.5: after rectifying the inverse square, the left composite
`F ≫ G` should contract to the identity through pair maps. -/
private theorem leftCompositeHomotopicPairMap_refl
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j) (G : PairMap j i)
    (hi : IsCofibration.{u, u, u} i)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap)
    (hGsub : G.subspaceMap = eSubspace.symm.toFun)
    (hg : eAmbient.symm.toFun.Homotopy G.ambientMap)
    (hgRestrict :
      ∀ z : I × B,
        hg (z.1, j z.2) =
          (correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient) z) :
    HomotopicPairMap (F ≫ G) (𝟙 (PairObject i)) := by
  let hBoundary :=
    correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
  let FfgRaw : (eAmbient.symm.toFun.comp eAmbient.toFun).Homotopy
      (G.ambientMap.comp eAmbient.toFun) :=
    ContinuousMap.Homotopy.comp hg (ContinuousMap.Homotopy.refl eAmbient.toFun)
  have FfgTargetEq : G.ambientMap.comp eAmbient.toFun = G.ambientMap.comp F.ambientMap := by
    -- Normalize the ambient endpoint to the actual ambient map of `F ≫ G`.
    ext x
    simp [heAmbient]
  let Ffg : (eAmbient.symm.toFun.comp eAmbient.toFun).Homotopy
      (G.ambientMap.comp F.ambientMap) :=
    FfgRaw.cast rfl FfgTargetEq
  let restrictedBoundaryRaw :
      ((eAmbient.symm.toFun.comp j).comp eSubspace.toFun).Homotopy
        ((i.comp eSubspace.symm.toFun).comp eSubspace.toFun) :=
    ContinuousMap.Homotopy.comp hBoundary (ContinuousMap.Homotopy.refl eSubspace.toFun)
  have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
    -- Reuse the commutative square when rewriting the restricted boundary loop.
    simpa [heSubspace, heAmbient] using PairMap.comm F
  have restrictedBoundarySourceEq :
      (eAmbient.symm.toFun.comp j).comp eSubspace.toFun =
        (eAmbient.symm.toFun.comp eAmbient.toFun).comp i := by
    ext a
    simpa using (congrArg eAmbient.symm.toFun (ContinuousMap.congr_fun hSquare a)).symm
  let restrictedBoundary :
      ((eAmbient.symm.toFun.comp eAmbient.toFun).comp i).Homotopy
        (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)) :=
    restrictedBoundaryRaw.cast restrictedBoundarySourceEq rfl
  have hRestriction :
      ((Ffg.symm.trans eAmbient.left_inv.some).toContinuousMap).comp
          ((ContinuousMap.id I).prodMap i) =
        (restrictedBoundary.symm.trans
          (eAmbient.left_inv.some.compContinuousMap i)).toContinuousMap := by
    -- The raw ambient contraction already has a controlled restriction; the remaining gap is to
    -- replace this normalized loop by the chosen subspace left inverse.
    simpa [hBoundary, FfgRaw, Ffg, restrictedBoundaryRaw, restrictedBoundary] using
      leftCompositeRestrictionEq F G eSubspace heSubspace eAmbient heAmbient hg hgRestrict
  -- Route correction: the generic pair-level rectifier is now available, so the remaining blocker
  -- is purely branch-local. One must cast `eSubspace.left_inv.some` to the left composite
  -- subspace map and prove that `hRestriction` is homotopic relative to the boundary to its
  -- whiskering by `i`, then feed that comparison to
  -- `homotopicPairMap_of_restrictedAmbientHomotopicRel`.
  let Kleft : (PairMap.subspaceMap (F ≫ G)).Homotopy (ContinuousMap.id A) :=
    eSubspace.left_inv.some.cast
      (leftCompositeSubspaceMap_eq F G eSubspace heSubspace hGsub) rfl
  let KleftWhiskered :
      (i.comp (PairMap.subspaceMap (F ≫ G))).Homotopy (i.comp (ContinuousMap.id A)) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl i) Kleft
  have hTargetAmbient :
      (Ffg.symm.trans eAmbient.left_inv.some).toContinuousMap.comp
          ((ContinuousMap.id I).prodMap i) =
        ((restrictedBoundary.symm.trans
            (eAmbient.left_inv.some.compContinuousMap i)).toContinuousMap) := by
    -- Keep the normalized restricted ambient loop available in the exact shape needed for the
    -- remaining branch-local comparison.
    simpa using hRestriction
  clear hTargetAmbient
  -- The existing normalization already identifies the restricted ambient contraction with a
  -- canonical whiskered left-inverse homotopy on `A`.
  let KleftNormalized :
      (i.comp (eSubspace.symm.toFun.comp eSubspace.toFun)).Homotopy
        (i.comp (ContinuousMap.id A)) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl i) eSubspace.symm.right_inv.some
  have hWhiskerEq : KleftNormalized.toContinuousMap = KleftWhiskered.toContinuousMap := by
    -- The canonical whiskered left inverse is exactly the casted subspace contraction used in the
    -- pair-level rectifier.
    ext z
    rcases z with ⟨t, a⟩
    change KleftNormalized (t, a) = KleftWhiskered (t, a)
    change i (eSubspace.symm.right_inv.some (t, a)) =
      i (eSubspace.left_inv.some (t, a))
    rfl
  have hRestrictedLoop :
      ((restrictedBoundary.symm.trans
          (eAmbient.left_inv.some.compContinuousMap i)).toContinuousMap).HomotopicRel
        KleftWhiskered.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set A)) := by
    have hRestrictedLoopNormalized :
        ((restrictedBoundary.symm.trans
            (eAmbient.left_inv.some.compContinuousMap i)).toContinuousMap).HomotopicRel
          KleftNormalized.toContinuousMap
          (({0, 1} : Set I) ×ˢ (Set.univ : Set A)) := by
      -- Reuse the shared normalized-loop frontier so both branch statements stay synchronized.
      simpa [hBoundary, FfgRaw, Ffg, restrictedBoundaryRaw, restrictedBoundary,
        KleftNormalized] using
        (restrictedBoundaryWhiskerComparisons
          F G eSubspace heSubspace eAmbient heAmbient hg).1
    -- Cast the normalized target back to the pair-level whiskered inverse used by the rectifier.
    rcases hRestrictedLoopNormalized with ⟨hRestrictedLoopNormalized⟩
    exact ⟨hRestrictedLoopNormalized.cast rfl hWhiskerEq⟩
  rcases hRestrictedLoop with ⟨hRestrictedLoop⟩
  have hRectified :
      ((Ffg.symm.trans eAmbient.left_inv.some).toContinuousMap.comp
          ((ContinuousMap.id I).prodMap i)).HomotopicRel
        KleftWhiskered.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set A)) := by
    -- Cast the solved normalized loop back to the restricted ambient composite used by the
    -- pair-level rectifier.
    exact ⟨hRestrictedLoop.cast hRestriction.symm hWhiskerEq⟩
  -- Once the restricted ambient loop is rectified, the existing cofibration-based pair rectifier
  -- upgrades it to a pair homotopy.
  exact
    homotopicPairMap_of_restrictedAmbientHomotopicRel
      hi Kleft (Ffg.symm.trans eAmbient.left_inv.some) hRectified

/-- Helper for Proposition 6.5.5: after rectifying the inverse square, the right composite
`G ≫ F` should contract to the identity through pair maps. -/
private theorem rightCompositeHomotopicPairMap_refl
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j) (G : PairMap j i)
    (hj : IsCofibration.{u, u, u} j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap)
    (hGsub : G.subspaceMap = eSubspace.symm.toFun)
    (hg : eAmbient.symm.toFun.Homotopy G.ambientMap)
    (hgRestrict :
      ∀ z : I × B,
        hg (z.1, j z.2) =
          (correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient) z) :
    HomotopicPairMap (G ≫ F) (𝟙 (PairObject j)) := by
  let hBoundary :=
    correctedInverseRestrictionHomotopic F eSubspace heSubspace eAmbient heAmbient
  let FgfRaw : (eAmbient.toFun.comp eAmbient.symm.toFun).Homotopy
      (eAmbient.toFun.comp G.ambientMap) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl eAmbient.toFun) hg
  have FgfTargetEq : eAmbient.toFun.comp G.ambientMap = F.ambientMap.comp G.ambientMap := by
    -- Normalize the ambient endpoint to the actual ambient map of `G ≫ F`.
    ext y
    simp [heAmbient]
  let Fgf : (eAmbient.toFun.comp eAmbient.symm.toFun).Homotopy
      (F.ambientMap.comp G.ambientMap) :=
    FgfRaw.cast rfl FgfTargetEq
  let restrictedBoundaryRaw :
      ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
        ((eAmbient.toFun.comp i).comp eSubspace.symm.toFun) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl eAmbient.toFun) hBoundary
  have hSquare : eAmbient.toFun.comp i = j.comp eSubspace.toFun := by
    -- Reuse the commutative square when rewriting the restricted boundary loop.
    simpa [heSubspace, heAmbient] using PairMap.comm F
  have restrictedBoundaryTargetEq :
      (eAmbient.toFun.comp i).comp eSubspace.symm.toFun =
        j.comp (eSubspace.toFun.comp eSubspace.symm.toFun) := by
    ext b
    simpa using ContinuousMap.congr_fun hSquare (eSubspace.symm b)
  let restrictedBoundary :
      ((eAmbient.toFun.comp eAmbient.symm.toFun).comp j).Homotopy
        (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)) :=
    restrictedBoundaryRaw.cast rfl restrictedBoundaryTargetEq
  have hRestriction :
      ((Fgf.symm.trans eAmbient.right_inv.some).toContinuousMap).comp
          ((ContinuousMap.id I).prodMap j) =
        (restrictedBoundary.symm.trans
          (eAmbient.right_inv.some.compContinuousMap j)).toContinuousMap := by
    -- The raw ambient contraction already has a controlled restriction; the remaining gap is to
    -- replace this normalized loop by the chosen subspace right inverse.
    simpa [hBoundary, FgfRaw, Fgf, restrictedBoundaryRaw, restrictedBoundary] using
      rightCompositeRestrictionEq F G eSubspace heSubspace eAmbient heAmbient hg hgRestrict
  -- Route correction: the symmetric branch reduces to the analogous local comparison after the
  -- generic pair-level rectifier added above. One must cast `eSubspace.right_inv.some` to the
  -- right composite subspace map and prove that `hRestriction` is homotopic relative to the
  -- boundary to its whiskering by `j`, then apply
  -- `homotopicPairMap_of_restrictedAmbientHomotopicRel`.
  let Kright : (PairMap.subspaceMap (G ≫ F)).Homotopy (ContinuousMap.id B) :=
    eSubspace.right_inv.some.cast
      (rightCompositeSubspaceMap_eq F G eSubspace heSubspace hGsub) rfl
  let KrightWhiskered :
      (j.comp (PairMap.subspaceMap (G ≫ F))).Homotopy (j.comp (ContinuousMap.id B)) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl j) Kright
  have hTargetAmbient :
      (Fgf.symm.trans eAmbient.right_inv.some).toContinuousMap.comp
          ((ContinuousMap.id I).prodMap j) =
        ((restrictedBoundary.symm.trans
            (eAmbient.right_inv.some.compContinuousMap j)).toContinuousMap) := by
    -- Keep the normalized restricted ambient loop available in the exact shape needed for the
    -- remaining branch-local comparison.
    simpa using hRestriction
  clear hTargetAmbient
  -- The symmetric normalization likewise identifies the restricted ambient contraction with a
  -- canonical whiskered right-inverse homotopy on `B`.
  let KrightNormalized :
      (j.comp (eSubspace.toFun.comp eSubspace.symm.toFun)).Homotopy
        (j.comp (ContinuousMap.id B)) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl j) eSubspace.right_inv.some
  have hWhiskerEq : KrightNormalized.toContinuousMap = KrightWhiskered.toContinuousMap := by
    -- The canonical whiskered right inverse is exactly the casted subspace contraction used in the
    -- pair-level rectifier.
    ext z
    rcases z with ⟨t, b⟩
    change KrightNormalized (t, b) = KrightWhiskered (t, b)
    change j (eSubspace.right_inv.some (t, b)) =
      j (eSubspace.right_inv.some (t, b))
    rfl
  have hRestrictedLoop :
      ((restrictedBoundary.symm.trans
          (eAmbient.right_inv.some.compContinuousMap j)).toContinuousMap).HomotopicRel
        KrightWhiskered.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set B)) := by
    have hRestrictedLoopNormalized :
        ((restrictedBoundary.symm.trans
            (eAmbient.right_inv.some.compContinuousMap j)).toContinuousMap).HomotopicRel
          KrightNormalized.toContinuousMap
          (({0, 1} : Set I) ×ˢ (Set.univ : Set B)) := by
      -- Reuse the same shared frontier theorem in the symmetric branch.
      simpa [hBoundary, FgfRaw, Fgf, restrictedBoundaryRaw, restrictedBoundary, KrightNormalized]
        using
          (restrictedBoundaryWhiskerComparisons
            F G eSubspace heSubspace eAmbient heAmbient hg).2
    -- Cast the normalized target back to the pair-level whiskered inverse used by the rectifier.
    rcases hRestrictedLoopNormalized with ⟨hRestrictedLoopNormalized⟩
    exact ⟨hRestrictedLoopNormalized.cast rfl hWhiskerEq⟩
  rcases hRestrictedLoop with ⟨hRestrictedLoop⟩
  have hRectified :
      ((Fgf.symm.trans eAmbient.right_inv.some).toContinuousMap.comp
          ((ContinuousMap.id I).prodMap j)).HomotopicRel
        KrightWhiskered.toContinuousMap
        (({0, 1} : Set I) ×ˢ (Set.univ : Set B)) := by
    -- Cast the normalized right loop back to the restricted ambient composite seen by the pair
    -- rectifier.
    exact ⟨hRestrictedLoop.cast hRestriction.symm hWhiskerEq⟩
  -- The same pair-level rectifier now closes the right composite.
  exact
    homotopicPairMap_of_restrictedAmbientHomotopicRel
      hj Kright (Fgf.symm.trans eAmbient.right_inv.some) hRectified

/-- Proposition 6.5.5. Given a commutative square `A → B`, `X → Y` whose vertical maps are
cofibrations and whose horizontal maps are ordinary homotopy equivalences, the induced map of
pairs `(X, A) → (Y, B)` is a homotopy equivalence of pairs. -/
theorem isPairHomotopyEquivalence_of_homotopyEquivSquare
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j)
    (hi : IsCofibration.{u, u, u} i) (hj : IsCofibration.{u, u, u} j)
    (eSubspace : A ≃ₕ B) (heSubspace : eSubspace.toFun = F.subspaceMap)
    (eAmbient : X ≃ₕ Y) (heAmbient : eAmbient.toFun = F.ambientMap) :
    IsPairHomotopyEquivalence F := by
  -- Route correction: the executable part of the source proof is to rectify the ambient inverse
  -- along `j` first, then contract the two composites through pair maps.
  obtain ⟨G, hGsub, hg, hgRestrict⟩ :=
    existsPairInverseMap_of_isCofibration
      (i := i) (j := j) F hj eSubspace heSubspace eAmbient heAmbient
  refine (isPairHomotopyEquivalence_iff).2 ?_
  refine ⟨G, ?_, ?_⟩
  · -- The left composite will be handled by the dedicated pair-level endpoint rectification
    -- helper.
    exact leftCompositeHomotopicPairMap_refl
      F G hi eSubspace heSubspace eAmbient heAmbient hGsub hg hgRestrict
  · -- The right composite uses the symmetric pair-level rectification helper.
    exact rightCompositeHomotopicPairMap_refl
      F G hj eSubspace heSubspace eAmbient heAmbient hGsub hg hgRestrict

/-- Existence-only restatement of Proposition 6.5.5 for callers that only know that the
horizontal maps of the square underlying `F` are ordinary homotopy equivalences. -/
theorem isPairHomotopyEquivalence_of_exists_homotopyEquivSquare
    {i : C(A, X)} {j : C(B, Y)} (F : PairMap i j)
    (hi : IsCofibration.{u, u, u} i) (hj : IsCofibration.{u, u, u} j)
    (hsubspace : ∃ e : A ≃ₕ B, e.toFun = F.subspaceMap)
    (hambient : ∃ e : X ≃ₕ Y, e.toFun = F.ambientMap) :
    IsPairHomotopyEquivalence F := by
  rcases hsubspace with ⟨eSubspace, heSubspace⟩
  rcases hambient with ⟨eAmbient, heAmbient⟩
  exact isPairHomotopyEquivalence_of_homotopyEquivSquare
    F hi hj eSubspace heSubspace eAmbient heAmbient
