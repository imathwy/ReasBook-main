import Mathlib
import StacksProject_2024.Chap14.Definition_14_26_1
import StacksProject_2024.Chap14.Remark_14_28_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.28.3:
- primary domain: simplicial and cosimplicial homotopy data under the standard opposite
  anti-equivalence;
- inspected same-kind owner declarations:
  `CategoryTheory.CosimplicialObject.DeltaOneHomotopy`,
  `CategoryTheory.CosimplicialObject.Homotopy`,
  `CategoryTheory.SimplicialObject.Homotopy`,
  `NatTrans.op`,
  `SSet.stdSimplex.objMk₁`;
- best owner abstraction: the target-side canonical owner is
  `CategoryTheory.SimplicialObject.Homotopy`, while the source-facing owner remains
  `DeltaOneHomotopy`, and the bridge/view is the canonical opposite natural transformation
  `NatTrans.op a`;
- primitive data: the degreewise `Δ[1]`-indexed family in `DeltaOneHomotopy` and the
  combinatorial operators `h n i` in `SimplicialObject.Homotopy`;
- derived API: the existence statements and the induced zigzag relations.

Source/core/bridge triage:
- `source-facing`: the equivalence between `DeltaOneHomotopy a b` and simplicial homotopy on the
  opposite simplicial maps;
- `core/canonical`: `SimplicialObject.Homotopy`;
- `bridge/view`: `NatTrans.op` on cosimplicial morphisms. -/

namespace DeltaOneHomotopy

private noncomputable def simplexIndexEquiv (n : ℕ) :
    Fin (n + 2) ≃ (Δ[1] : SSet.{0}).obj (Opposite.op ⦋n⦌) :=
  Equiv.ofBijective SSet.stdSimplex.objMk₁ SSet.stdSimplex.objMk₁_bijective

/-- Helper for Lemma 14.28.3: the forward direction of `simplexIndexEquiv` is exactly the
canonical simplex constructor. -/
private lemma simplexIndexEquiv_apply (n : ℕ) (k : Fin (n + 2)) :
    simplexIndexEquiv n k = SSet.stdSimplex.objMk₁ k := by
  -- The equivalence was defined from `SSet.stdSimplex.objMk₁`, so this is just the computation
  -- rule for its forward map.
  rfl

/-- Helper for Lemma 14.28.3: the constant `0` simplex of `Δ[1]` is the last simplex in the
canonical `Fin` indexing of `Δ[1]_n`. -/
private lemma deltaOneZeroEndpoint_eq_objMk₁_last (n : ℕ) :
    deltaOneZeroEndpoint ⦋n⦌ = SSet.stdSimplex.objMk₁ (Fin.last (n + 1)) := by
  -- Both simplices are the constant map with value `0`, so compare them on every vertex.
  ext j : 1
  rw [SSet.stdSimplex.objMk₁_of_castSucc_lt _ _ j.castSucc_lt_last]
  simp [deltaOneZeroEndpoint, SSet.stdSimplex.const]

/-- Helper for Lemma 14.28.3: the constant `1` simplex of `Δ[1]` is the zero simplex in the
canonical `Fin` indexing of `Δ[1]_n`. -/
private lemma deltaOneOneEndpoint_eq_objMk₁_zero (n : ℕ) :
    deltaOneOneEndpoint ⦋n⦌ = SSet.stdSimplex.objMk₁ (0 : Fin (n + 2)) := by
  -- Both simplices are the constant map with value `1`, so compare them on every vertex.
  ext j : 1
  rw [SSet.stdSimplex.objMk₁_of_le_castSucc _ _ (by simp)]
  simp [deltaOneOneEndpoint, SSet.stdSimplex.const]

/-- Helper for Lemma 14.28.3: rewriting the action of a face map on the canonical `objMk₁`
simplex into the `Δ[1].δ` notation exposes the standard `stdSimplex` normalization lemmas. -/
private lemma delta_one_map_objMk₁_delta {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.δ j).op (SSet.stdSimplex.objMk₁ i)) =
      Δ[1].δ j (SSet.stdSimplex.objMk₁ i) := by
  rfl

/-- Helper for Lemma 14.28.3: rewriting the action of a degeneracy map on the canonical `objMk₁`
simplex into the `Δ[1].σ` notation exposes the standard `stdSimplex` normalization lemmas. -/
private lemma delta_one_map_objMk₁_sigma {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.σ j).op (SSet.stdSimplex.objMk₁ i)) =
      Δ[1].σ j (SSet.stdSimplex.objMk₁ i) := by
  rfl

/-- Helper for Lemma 14.28.3: the interior face of the higher canonical simplex lands on the
canonical middle simplex used by the forward homotopy formula. -/
private lemma delta_one_face_objMk₁_succ_succ_castSucc {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.δ i.castSucc).op
      (SSet.stdSimplex.objMk₁ j.succ.succ.castSucc)) =
        SSet.stdSimplex.objMk₁ j.succ.castSucc := by
  -- This is the `δ_objMk₁_of_lt` branch, followed by the canonical predecessor normalization.
  rw [delta_one_map_objMk₁_delta]
  rw [SSet.stdSimplex.δ_objMk₁_of_lt]
  · simp
  · have hij' : (i : ℕ) ≤ (j : ℕ) := by
      simpa using hij
    show (i.castSucc.castSucc : Fin (n + 4)).1 <
        (j.succ.succ.castSucc : Fin (n + 4)).1
    simp
    omega

/-- Helper for Lemma 14.28.3: the left adjacent face in the middle branch again yields the
canonical middle simplex. -/
private lemma delta_one_face_objMk₁_adjacent_left {n : ℕ} (j : Fin (n + 1)) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.δ j.castSucc.succ).op
      (SSet.stdSimplex.objMk₁ j.succ.succ.castSucc)) =
        SSet.stdSimplex.objMk₁ j.succ.castSucc := by
  -- This is the special `δ_objMk₁_of_lt` branch at the adjacent face.
  rw [delta_one_map_objMk₁_delta]
  rw [SSet.stdSimplex.δ_objMk₁_of_lt _ _ (by simp)]
  simp

/-- Helper for Lemma 14.28.3: the right adjacent face in the middle branch yields the same
canonical middle simplex. -/
private lemma delta_one_face_objMk₁_adjacent_right {n : ℕ} (j : Fin (n + 1)) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.δ j.castSucc.succ).op
      (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc)) =
        SSet.stdSimplex.objMk₁ j.succ.castSucc := by
  -- This is the complementary `δ_objMk₁_of_le` branch at the adjacent face.
  rw [delta_one_map_objMk₁_delta]
  rw [SSet.stdSimplex.δ_objMk₁_of_le _ _ (by simp)]
  have hIndex :
      j.castSucc.castSucc.succ.castPred (by simp) = j.succ.castSucc := by
    ext
    simp
  simp [hIndex]

/-- Helper for Lemma 14.28.3: if the deleted face lies strictly after the transition index, the
face of the canonical interior simplex is the following canonical simplex. -/
private lemma deltaOneFaceObjMk₁OfGt {n : ℕ}
    (i : Fin (n + 2)) (l : Fin (n + 1)) (hli : l.succ < i) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.δ i).op
      (SSet.stdSimplex.objMk₁ l.castSucc.succ)) =
        SSet.stdSimplex.objMk₁ l.succ := by
  -- This is the `δ_objMk₁_of_le` branch, followed by the canonical cast-predecessor
  -- normalization for the successor index.
  rw [delta_one_map_objMk₁_delta]
  rw [SSet.stdSimplex.δ_objMk₁_of_le _ _ (by simpa using hli.le)]
  have hlt :
      (l.castSucc.succ : Fin (n + 3)).1 <
        (Fin.last (n + 2) : Fin (n + 3)).1 := by
    simp [l.is_lt]
  have hIndex :
      l.castSucc.succ.castPred (Fin.ne_last_of_lt hlt) = l.succ := by
    ext
    simp
  simp [hIndex]

/-- Helper for Lemma 14.28.3: if the deleted face lies at or before the transition index, the
face of the canonical interior simplex is the preceding canonical simplex. -/
private lemma deltaOneFaceObjMk₁OfLe {n : ℕ}
    (i : Fin (n + 2)) (l : Fin (n + 1)) (hil : i ≤ l.castSucc) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.δ i).op
      (SSet.stdSimplex.objMk₁ l.castSucc.succ)) =
        SSet.stdSimplex.objMk₁ l.castSucc := by
  -- This is the `δ_objMk₁_of_lt` branch; the predecessor of the successor index is the previous
  -- canonical simplex.
  rw [delta_one_map_objMk₁_delta]
  rw [SSet.stdSimplex.δ_objMk₁_of_lt _ _ (by simpa using hil)]
  rw [Fin.pred_succ]

/-- Helper for Chap14 Lemma 14 28 3: rewriting the exact mapped `simplexIndexEquiv` interior face
term in the `i ≤ l.castSucc` branch lands on the canonical predecessor simplex used by the
reverse delta proof. -/
private lemma deltaMapSimplexIndexEquivOfLe {n : ℕ}
    (i : Fin (n + 2)) (l : Fin (n + 1)) (hil : i ≤ l.castSucc) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.δ i).op
      (simplexIndexEquiv (n + 1) l.succ.castSucc)) =
        SSet.stdSimplex.objMk₁ l.castSucc := by
  -- Rewrite the exact mapped branch form to `stdSimplex`, then compute the predecessor index.
  rw [simplexIndexEquiv_apply, delta_one_map_objMk₁_delta]
  rw [SSet.stdSimplex.δ_objMk₁_of_lt _ _ (by simpa using hil)]
  have hIndex : l.succ.castSucc.pred (by simp) = l.castSucc := by
    ext
    simp
  simpa [hIndex]

/-- Helper for Chap14 Lemma 14 28 3: rewriting the exact mapped `simplexIndexEquiv` interior face
term in the adjacent branch lands on the canonical successor simplex used by the reverse delta
proof. -/
private lemma deltaMapSimplexIndexEquivAdjacent {n : ℕ} (l : Fin (n + 1)) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.δ l.succ).op
      (simplexIndexEquiv (n + 1) l.succ.castSucc)) =
        SSet.stdSimplex.objMk₁ l.succ := by
  -- In the adjacent case the `castPred` of the exact branch index is the successor simplex.
  rw [simplexIndexEquiv_apply, delta_one_map_objMk₁_delta]
  rw [SSet.stdSimplex.δ_objMk₁_of_le _ _ (by simp)]
  have hIndex : l.castSucc.succ.castPred (by simp) = l.succ := by
    ext
    simp
  simpa [hIndex]

/-- Helper for Chap14 Lemma 14 28 3: rewriting the exact mapped `simplexIndexEquiv` interior face
term in the `l.succ < i` branch lands on the following canonical simplex used by the reverse
delta proof. -/
private lemma deltaMapSimplexIndexEquivOfGt {n : ℕ}
    (i : Fin (n + 2)) (l : Fin (n + 1)) (hli : l.succ < i) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.δ i).op
      (simplexIndexEquiv (n + 1) l.succ.castSucc)) =
        SSet.stdSimplex.objMk₁ l.succ := by
  -- In the complementary branch the exact mapped term again reduces by a `castPred`.
  rw [simplexIndexEquiv_apply, delta_one_map_objMk₁_delta]
  rw [SSet.stdSimplex.δ_objMk₁_of_le _ _ (by simpa using hli.le)]
  have hIndex : l.castSucc.succ.castPred (by simp) = l.succ := by
    ext
    simp
  simpa [hIndex]

/-- Helper for Lemma 14.28.3: the interior degeneracy branch for `i ≤ j` lands on the next
canonical middle simplex. -/
private lemma delta_one_sigma_objMk₁_of_le {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.σ i.castSucc).op
      (SSet.stdSimplex.objMk₁ j.succ.castSucc)) =
        SSet.stdSimplex.objMk₁ j.succ.succ.castSucc := by
  -- This is the `σ_objMk₁_of_lt` branch after translating `i ≤ j` to the casted inequality.
  rw [delta_one_map_objMk₁_sigma]
  rw [SSet.stdSimplex.σ_objMk₁_of_lt _ _]
  · rfl
  · simpa using hij

/-- Helper for Lemma 14.28.3: the complementary interior degeneracy branch for `j ≤ i` lands on
the cast-successor canonical simplex used by the second simplicial-degeneracy axiom. -/
private lemma delta_one_sigma_objMk₁_of_gt {n : ℕ}
    (i j : Fin (n + 1)) (hji : j ≤ i) :
    ((Δ[1] : SSet.{0}).map (SimplexCategory.σ i.succ).op
      (SSet.stdSimplex.objMk₁ j.succ.castSucc)) =
        SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc := by
  -- This is the `σ_objMk₁_of_le` branch after translating the complementary inequality.
  rw [delta_one_map_objMk₁_sigma]
  rw [SSet.stdSimplex.σ_objMk₁_of_le _ _]
  · simp
  · simpa using hji

/-- Helper for Lemma 14.28.3: rewriting `σ_i ≫ δ_{j+1}` into owner-normal form in the strict case
`i < j`
exposes the target-side branch used by the first reverse sigma proof. -/
private lemma sigmaCompDeltaOfLe
    {X : CosimplicialObject C} {n : ℕ}
    (i j : Fin (n + 1)) (hij : i < j) :
    X.σ i ≫ X.δ j.castSucc =
      X.δ j.castSucc.succ ≫ X.σ i.castSucc := by
  -- This is exactly the complementary owner `δ ≫ σ` identity, rewritten in the orientation
  -- exposed by the reverse sigma branch.
  simpa using
    (X.δ_comp_σ_of_gt (i := j.castSucc) (j := i) (by simpa using hij)).symm

/-- Helper for Lemma 14.28.3: the adjacent target-side `δ_{i+1} ≫ σ_{i+1}` composite is the
identity, which is the normal form needed after rewriting the strict `σ ≫ δ` branch. -/
private lemma sigmaCompDeltaAdjacentIdentity
    {X : CosimplicialObject C} {n : ℕ} (i : Fin (n + 1)) :
    X.δ i.castSucc.succ ≫ X.σ i.castSucc = 𝟙 _ := by
  -- This is the owner adjacent `δ ≫ σ = 𝟙` relation with the index shifted by one.
  simpa using (X.δ_comp_σ_succ (i := i.castSucc))

/-- Helper for Lemma 14.28.3: rewriting `σ_i ≫ δ_{j+1}` into owner-normal form when `j ≤ i`
exposes the target-side branch used by the second reverse sigma proof. -/
private lemma sigmaCompDeltaOfGt
    {X : CosimplicialObject C} {n : ℕ}
    (i j : Fin (n + 1)) (hji : j ≤ i) :
    X.σ i ≫ X.δ j.castSucc =
      X.δ j.castSucc.castSucc ≫ X.σ i.succ := by
  -- This is the owner `δ ≫ σ` relation rewritten in the orientation exposed by the reverse
  -- degeneracy branches.
  simpa using
    (X.δ_comp_σ_of_le (i := j.castSucc) (j := i) (by simpa using hji)).symm

-- Proof sketch: the simplicial homotopy operators are the opposite of the nondegenerate
-- `Δ[1]`-components in degree `n + 1`, followed by the target degeneracy map. The simplicial
-- identities follow from the naturality squares of `H` together with the relations for
-- `SSet.stdSimplex.objMk₁`.
private def toOppositeSimplicialHomotopy
    {U V : CosimplicialObject C} {a b : U ⟶ V} (H : DeltaOneHomotopy a b) :
    SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b) where
  h i := (H.hom (SSet.stdSimplex.objMk₁ i.succ.castSucc) ≫ V.map (SimplexCategory.σ i)).op
  h_zero_comp_δ_zero n := by
    -- Route correction: the forward proof works by proving the corresponding equality in `C`,
    -- using the `Δ[1]` face normalization, and then taking opposites.
    have hnat :
        U.δ 0 ≫ H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 1)).succ.castSucc) =
          H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) ≫ V.δ 0 := by
      simpa [CosimplicialObject.δ, delta_one_map_objMk₁_delta] using
        (H.naturality (SimplexCategory.δ (0 : Fin (n + 2)))
          (SSet.stdSimplex.objMk₁ (0 : Fin (n + 1)).succ.castSucc)).w
    have hEq :
        U.δ 0 ≫ H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 1)).succ.castSucc) ≫ V.σ 0 =
          b.app ⦋n⦌ := by
      calc
        U.δ 0 ≫ H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 1)).succ.castSucc) ≫ V.σ 0 =
            (U.δ 0 ≫ H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 1)).succ.castSucc)) ≫ V.σ 0 := by
              simp [Category.assoc]
        _ = (H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) ≫ V.δ 0) ≫ V.σ 0 := by
              rw [hnat]
        _ = H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) ≫ (V.δ 0 ≫ V.σ 0) := by
              simp [Category.assoc]
        _ = H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) := by
              simpa using
                congrArg
                  (fun k ↦ H.hom (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) ≫ k)
                  (V.δ_comp_σ_self (i := (0 : Fin (n + 1))))
        _ = b.app ⦋n⦌ := by
              simpa [deltaOneOneEndpoint_eq_objMk₁_zero] using H.one_endpoint ⦋n⦌
    -- Unop the simplicial-object target equality back to the cosimplicial statement above.
    apply Quiver.Hom.unop_inj
    simpa [CosimplicialObject.σ, SimplicialObject.δ] using hEq
  h_last_comp_δ_last n := by
    -- Normalize the last face to the constant-`0` simplex and then use the `δσ = id` relation.
    have hmap :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.δ (Fin.last (n + 1))).op
          (SSet.stdSimplex.objMk₁ (Fin.last (n + 1)).castSucc)) =
            SSet.stdSimplex.objMk₁ (Fin.last (n + 1)) := by
      rw [delta_one_map_objMk₁_delta]
      simpa using
        (SSet.stdSimplex.δ_objMk₁_of_le
          (Fin.last (n + 1)).castSucc
          (Fin.last (n + 1))
          (by simp))
    have hnat :
        U.δ (Fin.last (n + 1)) ≫
            H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1)).castSucc) =
          H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1))) ≫ V.δ (Fin.last (n + 1)) := by
      simpa [CosimplicialObject.δ, hmap] using
        (H.naturality (SimplexCategory.δ (Fin.last (n + 1)))
          (SSet.stdSimplex.objMk₁ (Fin.last (n + 1)).castSucc)).w
    have hEq :
        U.δ (Fin.last (n + 1)) ≫
            H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1)).castSucc) ≫
              V.σ (Fin.last n) =
          a.app ⦋n⦌ := by
      calc
        U.δ (Fin.last (n + 1)) ≫
            H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1)).castSucc) ≫
              V.σ (Fin.last n) =
          (U.δ (Fin.last (n + 1)) ≫
            H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1)).castSucc)) ≫
              V.σ (Fin.last n) := by
                simp [Category.assoc]
        _ = (H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1))) ≫
              V.δ (Fin.last (n + 1))) ≫
                V.σ (Fin.last n) := by
              rw [hnat]
        _ = H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1))) ≫
              (V.δ (Fin.last (n + 1)) ≫ V.σ (Fin.last n)) := by
              simp [Category.assoc]
        _ = H.hom (SSet.stdSimplex.objMk₁ (Fin.last (n + 1))) := by
              rw [show V.δ (Fin.last (n + 1)) ≫ V.σ (Fin.last n) = 𝟙 _ by
                simpa using (V.δ_comp_σ_succ (i := Fin.last n))]
              rw [Category.comp_id]
        _ = a.app ⦋n⦌ := by
              simpa [deltaOneZeroEndpoint_eq_objMk₁_last] using H.zero_endpoint ⦋n⦌
    -- Unop the endpoint equality back to the simplicial-object goal.
    apply Quiver.Hom.unop_inj
    simpa [Category.assoc, CosimplicialObject.σ, SimplicialObject.δ] using hEq
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    -- Normalize the interior face to the canonical middle simplex, then use the second
    -- cosimplicial identity to move the target `δ` past the target `σ`.
    have hmap :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.δ i.castSucc).op
          (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ)) =
            SSet.stdSimplex.objMk₁ j.castSucc.succ := by
      simpa using delta_one_face_objMk₁_succ_succ_castSucc i j hij
    have hnat :
        U.δ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ i.castSucc := by
      simpa [CosimplicialObject.δ, hmap] using
        (H.naturality (SimplexCategory.δ i.castSucc)
          (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ)).w
    have hEq :
        U.δ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ j.succ =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j ≫ V.δ i := by
      calc
        U.δ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ j.succ =
            (U.δ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ)) ≫
              V.σ j.succ := by
              simp [Category.assoc]
        _ = (H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ i.castSucc) ≫ V.σ j.succ := by
              rw [hnat]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫
              (V.δ i.castSucc ≫ V.σ j.succ) := by
              simp [Category.assoc]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ (V.σ j ≫ V.δ i) := by
              rw [V.δ_comp_σ_of_le hij]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j ≫ V.δ i := by
              simp
    apply Quiver.Hom.unop_inj
    simpa [Category.assoc, CosimplicialObject.σ, SimplicialObject.δ] using hEq
  h_succ_comp_δ_castSucc_succ j := by
    -- Normalize both adjacent faces to the same middle simplex, then apply the two special
    -- `δσ = id` identities on the target.
    have hmap_left :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.δ j.castSucc.succ).op
          (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ)) =
            SSet.stdSimplex.objMk₁ j.castSucc.succ := by
      simpa using delta_one_face_objMk₁_adjacent_left j
    have hmap_right :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.δ j.castSucc.succ).op
          (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ)) =
            SSet.stdSimplex.objMk₁ j.castSucc.succ := by
      simpa using delta_one_face_objMk₁_adjacent_right j
    have hnat_left :
        U.δ j.castSucc.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ j.castSucc.succ := by
      simpa [CosimplicialObject.δ, hmap_left] using
        (H.naturality (SimplexCategory.δ j.castSucc.succ)
          (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ)).w
    have hnat_right :
        U.δ j.castSucc.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ) =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ j.castSucc.succ := by
      simpa [CosimplicialObject.δ, hmap_right] using
        (H.naturality (SimplexCategory.δ j.castSucc.succ)
          (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ)).w
    have hEq :
        U.δ j.castSucc.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ j.succ =
          U.δ j.castSucc.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ) ≫
            V.σ j.castSucc := by
      calc
        U.δ j.castSucc.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ j.succ =
            (H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ j.castSucc.succ) ≫
              V.σ j.succ := by
              simpa [Category.assoc] using hnat_left =≫ V.σ j.succ
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫
              (V.δ j.castSucc.succ ≫ V.σ j.succ) := by
              simp [Category.assoc]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ k)
                  (V.δ_comp_σ_self (i := j.succ))
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫
              (V.δ j.castSucc.succ ≫ V.σ j.castSucc) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ k)
                  (V.δ_comp_σ_succ (i := j.castSucc)).symm
        _ = (H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ j.castSucc.succ) ≫
              V.σ j.castSucc := by
              simp [Category.assoc]
        _ = U.δ j.castSucc.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ) ≫
              V.σ j.castSucc := by
              simpa [Category.assoc] using (hnat_right =≫ V.σ j.castSucc).symm
    apply Quiver.Hom.unop_inj
    simpa [Category.assoc, CosimplicialObject.σ, SimplicialObject.δ] using hEq
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    -- Normalize the complementary interior face to the same middle simplex, then use the
    -- fourth cosimplicial identity on the target.
    have hmap :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.δ i.succ).op
          (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ)) =
            SSet.stdSimplex.objMk₁ j.castSucc.succ := by
      rw [delta_one_map_objMk₁_delta]
      rw [SSet.stdSimplex.δ_objMk₁_of_le]
      · have hlt : j.castSucc.castSucc.succ < Fin.last _ := by
          show (j.castSucc.castSucc.succ : Fin _).1 < (Fin.last _ : Fin _).1
          have hj : (j : ℕ) < _ := j.is_lt
          simp
          omega
        have hIndex :
            j.castSucc.castSucc.succ.castPred
                (Fin.ne_last_of_lt hlt) =
              j.castSucc.succ := by
          ext
          simp
        simp [hIndex]
      · show (j.castSucc.castSucc.succ : Fin _).1 ≤ (i.succ.castSucc : Fin _).1
        have hji' : (j : ℕ) < (i : ℕ) := by
          simpa using hji
        simp
        omega
    have hnat :
        U.δ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ) =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ i.succ := by
      simpa [CosimplicialObject.δ, hmap] using
        (H.naturality (SimplexCategory.δ i.succ)
          (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ)).w
    have hEq :
        U.δ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ) ≫ V.σ j.castSucc =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j ≫ V.δ i := by
      calc
        U.δ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ) ≫ V.σ j.castSucc =
            (U.δ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.castSucc.succ)) ≫
              V.σ j.castSucc := by
              simp [Category.assoc]
        _ = (H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.δ i.succ) ≫
              V.σ j.castSucc := by
              rw [hnat]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫
              (V.δ i.succ ≫ V.σ j.castSucc) := by
              simp [Category.assoc]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ (V.σ j ≫ V.δ i) := by
              rw [V.δ_comp_σ_of_gt hji]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j ≫ V.δ i := by
              simp
    apply Quiver.Hom.unop_inj
    simpa [CosimplicialObject.σ, SimplicialObject.δ] using hEq
  h_comp_σ_castSucc_of_le i j hij := by
    -- Normalize the `Δ[1]` degeneracy to the next middle simplex, then use the fifth
    -- cosimplicial identity on the target.
    have hmap :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.σ i.castSucc).op
          (SSet.stdSimplex.objMk₁ j.castSucc.succ)) =
            SSet.stdSimplex.objMk₁ j.castSucc.succ.succ := by
      simpa using delta_one_sigma_objMk₁_of_le i j hij
    have hnat :
        U.σ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ i.castSucc := by
      simpa [CosimplicialObject.σ, hmap] using
        (H.naturality (SimplexCategory.σ i.castSucc)
          (SSet.stdSimplex.objMk₁ j.castSucc.succ)).w
    have hEq :
        U.σ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ j.succ ≫ V.σ i := by
      calc
        U.σ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j =
            (U.σ i.castSucc ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ)) ≫ V.σ j := by
              simp [Category.assoc]
        _ = (H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ i.castSucc) ≫ V.σ j := by
              rw [hnat]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫
              (V.σ i.castSucc ≫ V.σ j) := by
              simp [Category.assoc]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫
              (V.σ j.succ ≫ V.σ i) := by
              rw [V.σ_comp_σ hij]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.succ) ≫ V.σ j.succ ≫ V.σ i := by
              simp
    apply Quiver.Hom.unop_inj
    simpa [CosimplicialObject.σ, SimplicialObject.σ] using hEq
  h_comp_σ_succ_of_lt i j hji := by
    -- Normalize the complementary `Δ[1]` degeneracy branch, then use the reversed fifth
    -- cosimplicial identity on the target.
    have hmap :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.σ i.succ).op
          (SSet.stdSimplex.objMk₁ j.castSucc.succ)) =
            SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc := by
      simpa using delta_one_sigma_objMk₁_of_gt i j hji
    have hnat :
        U.σ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc) ≫ V.σ i.succ := by
      simpa [CosimplicialObject.σ, hmap] using
        (H.naturality (SimplexCategory.σ i.succ)
          (SSet.stdSimplex.objMk₁ j.castSucc.succ)).w
    have hEq :
        U.σ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j =
          H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc) ≫ V.σ j.castSucc ≫ V.σ i := by
      calc
        U.σ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ) ≫ V.σ j =
            (U.σ i.succ ≫ H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ)) ≫ V.σ j := by
              simp [Category.assoc]
        _ = (H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc) ≫ V.σ i.succ) ≫ V.σ j := by
              rw [hnat]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc) ≫
              (V.σ i.succ ≫ V.σ j) := by
              simp [Category.assoc]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc) ≫
              (V.σ j.castSucc ≫ V.σ i) := by
              rw [← V.σ_comp_σ hji]
        _ = H.hom (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc) ≫
              V.σ j.castSucc ≫ V.σ i := by
              simp
    apply Quiver.Hom.unop_inj
    simpa [CosimplicialObject.σ, SimplicialObject.σ] using hEq

private noncomputable def ofOppositeSimplicialHomotopyHom
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b)) :
    ∀ n : ℕ, (Δ[1] : SSet.{0}).obj (Opposite.op ⦋n⦌) → (U.obj ⦋n⦌ ⟶ V.obj ⦋n⦌) :=
  fun n α ↦
    match n with
    | 0 =>
        let i := (simplexIndexEquiv 0).symm α
        Fin.lastCases (a.app ⦋0⦌) (fun _ ↦ b.app ⦋0⦌) i
    | n + 1 =>
        let i := (simplexIndexEquiv (n + 1)).symm α
        Fin.lastCases
          (a.app ⦋n + 1⦌)
          (fun j ↦ Fin.cases
            (b.app ⦋n + 1⦌)
            (fun k ↦ (H.h k).unop ≫ V.δ k.castSucc)
            j)
          i

/-- Helper for Lemma 14.28.3: evaluating the reverse construction on the canonical simplex
`simplexIndexEquiv n k` reveals the endpoint/interior branch chosen by the `Fin` decomposition. -/
private lemma ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    (n : ℕ) (k : Fin (n + 2)) :
    ofOppositeSimplicialHomotopyHom H n (simplexIndexEquiv n k) =
      match n with
      | 0 =>
          Fin.lastCases (a.app ⦋0⦌) (fun _ ↦ b.app ⦋0⦌) k
      | n + 1 =>
          Fin.lastCases
            (a.app ⦋n + 1⦌)
            (fun j ↦ Fin.cases
              (b.app ⦋n + 1⦌)
              (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc)
              j)
            k := by
  cases n with
  | zero =>
      simp [ofOppositeSimplicialHomotopyHom, simplexIndexEquiv]
  | succ n =>
      simp [ofOppositeSimplicialHomotopyHom, simplexIndexEquiv]

/-- Helper for Lemma 14.28.3: the reverse construction evaluates on a canonical interior simplex
to the corresponding simplicial-homotopy operator followed by the target coface map. -/
private lemma ofOppositeSimplicialHomotopyHom_apply_interior
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    (n : ℕ) (i : Fin (n + 1)) :
    ofOppositeSimplicialHomotopyHom H (n + 1) (SSet.stdSimplex.objMk₁ i.succ.castSucc) =
      (H.h i).unop ≫ V.δ i.castSucc := by
  -- Evaluate on the canonical interior simplex and simplify the nested `Fin` branch selection.
  calc
    ofOppositeSimplicialHomotopyHom H (n + 1) (SSet.stdSimplex.objMk₁ i.succ.castSucc) =
        Fin.lastCases
          (a.app ⦋n + 1⦌)
          (fun j ↦
            Fin.cases
              (b.app ⦋n + 1⦌)
              (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc)
              j)
          i.succ.castSucc := by
            simpa [simplexIndexEquiv] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 1)
                i.succ.castSucc
    _ = (H.h i).unop ≫ V.δ i.castSucc := by
          rw [Fin.lastCases_castSucc, Fin.cases_succ]
          rfl

/-- Helper for Lemma 14.28.3: evaluating the reverse construction on a cast-successor simplex
removes the outer endpoint branch and exposes the remaining endpoint/interior split. -/
private lemma ofOppositeSimplicialHomotopyHom_apply_castSucc
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    (n : ℕ) (l : Fin (n + 1)) :
    ofOppositeSimplicialHomotopyHom H n (SSet.stdSimplex.objMk₁ l.castSucc) =
      match n with
      | 0 => b.app ⦋0⦌
      | n + 1 =>
          Fin.cases
            (b.app ⦋n + 1⦌)
            (fun m ↦ (H.h m).unop ≫ V.δ m.castSucc)
            l := by
  cases n with
  | zero =>
      -- In degree `0`, the cast-successor index is the constant-`1` endpoint.
      simpa [simplexIndexEquiv, Fin.lastCases_castSucc] using
        ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 0 l.castSucc
  | succ n =>
      -- In positive degrees, `Fin.lastCases_castSucc` removes the outer endpoint branch.
      simpa [simplexIndexEquiv, Fin.lastCases_castSucc] using
        ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 1) l.castSucc

/-- Helper for Lemma 14.28.3: evaluating the reverse construction on `objMk₁ l.succ` removes the
outer endpoint branch and packages the remaining value as the endpoint/interior split indexed by
`l`. -/
private lemma ofOppositeSimplicialHomotopyHom_apply_succ
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    (n : ℕ) (l : Fin (n + 2)) :
    ofOppositeSimplicialHomotopyHom H (n + 1) (SSet.stdSimplex.objMk₁ l.succ) =
      Fin.lastCases
        (a.app ⦋n + 1⦌)
        (fun m ↦ (H.h m).unop ≫ V.δ m.castSucc)
        l := by
  -- Reduce to the canonical `simplexIndexEquiv` formula and then simplify the `Fin` branches.
  calc
    ofOppositeSimplicialHomotopyHom H (n + 1) (SSet.stdSimplex.objMk₁ l.succ) =
        Fin.lastCases
          (a.app ⦋n + 1⦌)
          (fun j ↦
            Fin.cases
              (b.app ⦋n + 1⦌)
              (fun m ↦ (H.h m).unop ≫ V.δ m.castSucc)
              j)
          l.succ := by
            simpa [simplexIndexEquiv] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 1) l.succ
    _ =
        Fin.lastCases
          (a.app ⦋n + 1⦌)
          (fun m ↦ (H.h m).unop ≫ V.δ m.castSucc)
          l := by
            refine Fin.lastCases ?_ ?_ l
            · rw [Fin.succ_last, Fin.lastCases_last, Fin.lastCases_last]
            · intro m
              rw [Fin.succ_castSucc, Fin.lastCases_castSucc, Fin.cases_succ, Fin.lastCases_castSucc]

/-- Helper for Lemma 14.28.3: unop-ing the first simplicial face relation gives the cosimplicial
face identity needed for the reverse construction. -/
private lemma simplicial_face_relation_unop_zero
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    (n : ℕ) :
    U.δ 0 ≫ (H.h 0).unop = b.app ⦋n⦌ := by
  -- Reverse the endpoint face identity by taking opposites.
  simpa [CosimplicialObject.δ, SimplicialObject.δ, Category.assoc] using
    congrArg Quiver.Hom.unop (H.h_zero_comp_δ_zero n)

/-- Helper for Lemma 14.28.3: unop-ing the last simplicial endpoint face relation gives the
cosimplicial endpoint identity used in the reverse reconstruction. -/
private lemma simplicial_face_relation_unop_last
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    (n : ℕ) :
    U.δ (Fin.last (n + 1)) ≫ (H.h (Fin.last n)).unop = a.app ⦋n⦌ := by
  -- Reverse the terminal face identity by taking opposites.
  simpa [CosimplicialObject.δ, SimplicialObject.δ, Category.assoc] using
    congrArg Quiver.Hom.unop (H.h_last_comp_δ_last n)

/-- Helper for Lemma 14.28.3: unop-ing the first simplicial face relation gives the cosimplicial
face identity needed for the reverse construction. -/
private lemma simplicial_face_relation_unop_of_le
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    U.δ i.castSucc ≫ (H.h j.succ).unop = (H.h j).unop ≫ V.δ i := by
  -- Reverse the simplicial identity by passing to opposites and simplify the induced maps.
  simpa [CosimplicialObject.δ, SimplicialObject.δ, Category.assoc] using
    congrArg Quiver.Hom.unop (H.h_succ_comp_δ_castSucc_of_lt i j hij)

/-- Helper for Lemma 14.28.3: unop-ing the adjacent simplicial face relation yields the matching
cosimplicial equality between the two middle branches. -/
private lemma simplicial_face_relation_unop_adjacent
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    {n : ℕ} (j : Fin (n + 1)) :
    U.δ j.castSucc.succ ≫ (H.h j.succ).unop =
      U.δ j.castSucc.succ ≫ (H.h j.castSucc).unop := by
  -- Reverse the adjacent simplicial face identity by taking opposites.
  simpa [CosimplicialObject.δ, SimplicialObject.δ, Category.assoc] using
    congrArg Quiver.Hom.unop (H.h_succ_comp_δ_castSucc_succ j)

/-- Helper for Lemma 14.28.3: unop-ing the complementary simplicial face relation gives the
cosimplicial face identity for the remaining reverse branch. -/
private lemma simplicial_face_relation_unop_of_gt
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    U.δ i.succ ≫ (H.h j.castSucc).unop = (H.h j).unop ≫ V.δ i := by
  -- Reverse the complementary simplicial face identity by taking opposites.
  simpa [CosimplicialObject.δ, SimplicialObject.δ, Category.assoc] using
    congrArg Quiver.Hom.unop (H.h_castSucc_comp_δ_succ_of_lt i j hji)

/-- Helper for Lemma 14.28.3: unop-ing the first simplicial degeneracy relation gives the
cosimplicial degeneracy identity used in the reverse construction. -/
private lemma simplicial_sigma_relation_unop_of_le
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    U.σ i.castSucc ≫ (H.h j).unop = (H.h j.succ).unop ≫ V.σ i := by
  -- Reverse the simplicial degeneracy identity by passing to opposites.
  simpa [CosimplicialObject.σ, SimplicialObject.σ, Category.assoc] using
    congrArg Quiver.Hom.unop (H.h_comp_σ_castSucc_of_le i j hij)

/-- Helper for Lemma 14.28.3: unop-ing the complementary simplicial degeneracy relation gives the
cosimplicial degeneracy identity for the other reverse branch. -/
private lemma simplicial_sigma_relation_unop_of_gt
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    U.σ i.succ ≫ (H.h j).unop = (H.h j.castSucc).unop ≫ V.σ i := by
  -- Reverse the complementary simplicial degeneracy identity by passing to opposites.
  simpa [CosimplicialObject.σ, SimplicialObject.σ, Category.assoc] using
    congrArg Quiver.Hom.unop (H.h_comp_σ_succ_of_lt i j hji)

/-- Helper for Lemma 14.28.3: postcomposing the first unop degeneracy relation packages the
target-side coface that appears in the reverse naturality branches. -/
private lemma simplicial_sigma_relation_unop_of_le_assoc
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    U.σ i.castSucc ≫ (H.h j).unop ≫ V.δ j.castSucc =
      (H.h j.succ).unop ≫ V.σ i ≫ V.δ j.castSucc := by
  -- Postcompose the basic unop relation with the fixed target coface.
  simpa [Category.assoc] using
    simplicial_sigma_relation_unop_of_le H i j hij =≫ V.δ j.castSucc

/-- Helper for Lemma 14.28.3: postcomposing the complementary unop degeneracy relation packages
the target-side coface that appears in the second reverse naturality branch. -/
private lemma simplicial_sigma_relation_unop_of_gt_assoc
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    U.σ i.succ ≫ (H.h j).unop ≫ V.δ j.castSucc =
      (H.h j.castSucc).unop ≫ V.σ i ≫ V.δ j.castSucc := by
  -- Postcompose the complementary unop relation with the fixed target coface.
  simpa [Category.assoc] using
    simplicial_sigma_relation_unop_of_gt H i j hji =≫ V.δ j.castSucc

/-- Helper for Lemma 14.28.3: the reverse component family defines a morphism property on
`SimplexCategory`; proving it on the generators is enough to recover the full naturality field. -/
private def reverseNaturalityProperty
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b)) :
    MorphismProperty SimplexCategory :=
  fun _ _ θ ↦
    ∀ α, CommSq
      (U.map θ)
      (ofOppositeSimplicialHomotopyHom H _ (((Δ[1] : SSet.{0}).map θ.op α)))
      (ofOppositeSimplicialHomotopyHom H _ α)
      (V.map θ)

/-- Helper for Lemma 14.28.3: the reverse naturality predicate is multiplicative because
commutative squares compose horizontally. -/
private instance reverseNaturalityProperty_isMultiplicative
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b)) :
    (reverseNaturalityProperty H).IsMultiplicative where
  id_mem n α := by
    -- For identities, both simplicial reindexing and the two object maps are identities.
    refine ⟨?_⟩
    simp
  comp_mem θ₁ θ₂ hθ₁ hθ₂ α := by
    -- For compositions, paste the two known commutative squares.
    simpa [reverseNaturalityProperty, Functor.map_comp] using
      CommSq.horiz_comp
        (hθ₁ (((Δ[1] : SSet.{0}).map θ₂.op α)))
        (hθ₂ α)

/-- Helper for Lemma 14.28.3: the reverse component family is natural with respect to face
generators of `SimplexCategory`. -/
private lemma reverse_component_naturality_delta
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    {n : ℕ} (i : Fin (n + 2)) :
    reverseNaturalityProperty H (SimplexCategory.δ i) := by
  intro α
  refine ⟨?_⟩
  obtain ⟨k, rfl⟩ := (simplexIndexEquiv (n + 1)).surjective α
  -- Reduce the square to the canonical `Fin`-indexed simplices in degree `n + 1`.
  refine Fin.lastCases ?_ ?_ k
  · -- The last simplex is the `a`-endpoint, and faces preserve that endpoint.
    have hMap :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.δ i).op
          (SSet.stdSimplex.objMk₁ (Fin.last (n + 2)))) =
          SSet.stdSimplex.objMk₁ (Fin.last (n + 1)) := by
      rw [← deltaOneZeroEndpoint_eq_objMk₁_last (n := n + 1)]
      rw [← deltaOneZeroEndpoint_eq_objMk₁_last (n := n)]
      ext k : 1
      rfl
    have hLeft :
        ofOppositeSimplicialHomotopyHom H (n + 1)
            (SSet.stdSimplex.objMk₁ (Fin.last (n + 2))) =
          a.app ⦋n + 1⦌ := by
      simpa [simplexIndexEquiv, Fin.lastCases_last] using
        ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 1) (Fin.last (n + 2))
    have hRight :
        ofOppositeSimplicialHomotopyHom H n (SSet.stdSimplex.objMk₁ (Fin.last (n + 1))) =
          a.app ⦋n⦌ := by
      cases n with
      | zero =>
          simpa [simplexIndexEquiv, Fin.lastCases_last] using
            ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 0 (Fin.last 1)
      | succ n =>
          simpa [simplexIndexEquiv, Fin.lastCases_last] using
            ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 1)
              (Fin.last (n + 2))
    -- Rewriting both components to the endpoint branch reduces the square to `a.naturality`.
    simpa [simplexIndexEquiv, hLeft, hMap, hRight] using
      a.naturality (SimplexCategory.δ i)
  · intro j
    refine Fin.cases ?_ ?_ j
    · -- The zero simplex is the `b`-endpoint, and faces preserve that endpoint.
      have hMap :
          ((Δ[1] : SSet.{0}).map (SimplexCategory.δ i).op
            (SSet.stdSimplex.objMk₁ (0 : Fin (n + 3)))) =
            SSet.stdSimplex.objMk₁ (0 : Fin (n + 2)) := by
        rw [← deltaOneOneEndpoint_eq_objMk₁_zero (n := n + 1)]
        rw [← deltaOneOneEndpoint_eq_objMk₁_zero (n := n)]
        ext k : 1
        rfl
      have hLeft :
          ofOppositeSimplicialHomotopyHom H (n + 1) (SSet.stdSimplex.objMk₁ (0 : Fin (n + 3))) =
            b.app ⦋n + 1⦌ := by
        cases n with
        | zero =>
            simpa [simplexIndexEquiv, Fin.lastCases_castSucc] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 1 (0 : Fin 3)
        | succ n =>
            have hIndex :
                ofOppositeSimplicialHomotopyHom H (n + 2)
                    (SSet.stdSimplex.objMk₁ (0 : Fin (n + 4))) =
                  Fin.lastCases (a.app ⦋n + 2⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 2⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (Fin.castSucc 0) := by
              simpa [simplexIndexEquiv] using
                ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 2)
                  (Fin.castSucc 0)
            have hBranch :
                Fin.lastCases (a.app ⦋n + 2⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 2⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (0 : Fin (n + 4)) =
                  b.app ⦋n + 2⦌ := by
              change Fin.lastCases (a.app ⦋n + 2⦌)
                  (fun j ↦
                    Fin.cases (b.app ⦋n + 2⦌)
                      (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                  (Fin.castSucc 0) =
                b.app ⦋n + 2⦌
              rw [Fin.lastCases_castSucc]
              simp
            exact hIndex.trans hBranch
      have hRight :
          ofOppositeSimplicialHomotopyHom H n (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) =
            b.app ⦋n⦌ := by
        cases n with
        | zero =>
            simpa [simplexIndexEquiv, Fin.lastCases_castSucc] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 0 (0 : Fin 2)
        | succ n =>
            have hIndex :
                ofOppositeSimplicialHomotopyHom H (n + 1)
                    (SSet.stdSimplex.objMk₁ (0 : Fin (n + 3))) =
                  Fin.lastCases (a.app ⦋n + 1⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 1⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (Fin.castSucc 0) := by
              simpa [simplexIndexEquiv] using
                ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 1)
                  (Fin.castSucc 0)
            have hBranch :
                Fin.lastCases (a.app ⦋n + 1⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 1⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (0 : Fin (n + 3)) =
                  b.app ⦋n + 1⦌ := by
              change Fin.lastCases (a.app ⦋n + 1⦌)
                  (fun j ↦
                    Fin.cases (b.app ⦋n + 1⦌)
                      (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                  (Fin.castSucc 0) =
                b.app ⦋n + 1⦌
              rw [Fin.lastCases_castSucc]
              simp
            exact hIndex.trans hBranch
      simpa [simplexIndexEquiv, hLeft, hMap, hRight] using
        b.naturality (SimplexCategory.δ i)
    · intro l
      by_cases hil : i ≤ l.castSucc
      · -- Normalize the mapped simplex to the predecessor branch and then split the lower-degree
        -- reverse component into its endpoint and interior cases.
        have hMap :
            ((Δ[1] : SSet.{0}).map (SimplexCategory.δ i).op
              (simplexIndexEquiv (n + 1) l.succ.castSucc)) =
              SSet.stdSimplex.objMk₁ l.castSucc :=
          deltaMapSimplexIndexEquivOfLe i l hil
        cases n with
        | zero =>
            have hi0 : i = 0 := le_antisymm hil (Fin.zero_le _)
            subst hi0
            simpa [simplexIndexEquiv, hMap, Category.assoc] using
              simplicial_face_relation_unop_zero H 0 =≫ V.δ 0
        | succ n =>
            rw [ofOppositeSimplicialHomotopyHom_apply_interior, hMap,
              ofOppositeSimplicialHomotopyHom_apply_castSucc]
            refine Fin.cases ?_ ?_ l
            · have hi0 : i = 0 := le_antisymm hil (Fin.zero_le _)
              subst hi0
              simpa [Category.assoc] using simplicial_face_relation_unop_zero H (n + 1) =≫ V.δ 0
            · intro j
              simpa [Category.assoc] using
                simplicial_face_relation_unop_of_le H i j (by simpa using hil) =≫ V.δ i
      · by_cases hEq : i = l.succ
        · -- TODO: normalize the adjacent live branch with `deltaMapSimplexIndexEquivAdjacent`,
          -- then split the remaining right-hand component into the terminal and nonterminal
          -- cases closed by `simplicial_face_relation_unop_last` and
          -- `simplicial_face_relation_unop_adjacent`.
          sorry
        · -- TODO: derive `l.succ < i`, normalize the exact live branch with
          -- `deltaMapSimplexIndexEquivOfGt`, and then use `ofOppositeSimplicialHomotopyHom_apply_succ`
          -- together with `simplicial_face_relation_unop_of_gt`.
          sorry

/-- Helper for Lemma 14.28.3: the reverse component family is natural with respect to degeneracy
generators of `SimplexCategory`. -/
private lemma reverse_component_naturality_sigma
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    {n : ℕ} (i : Fin (n + 1)) :
    reverseNaturalityProperty H (SimplexCategory.σ i) := by
  intro α
  refine ⟨?_⟩
  obtain ⟨k, rfl⟩ := (simplexIndexEquiv n).surjective α
  -- Reduce the square to the canonical `Fin`-indexed simplices in degree `n`.
  refine Fin.lastCases ?_ ?_ k
  · -- The last simplex is the `a`-endpoint, and degeneracies preserve that endpoint.
    have hMap :
        ((Δ[1] : SSet.{0}).map (SimplexCategory.σ i).op
          (SSet.stdSimplex.objMk₁ (Fin.last (n + 1)))) =
          SSet.stdSimplex.objMk₁ (Fin.last (n + 2)) := by
      rw [delta_one_map_objMk₁_sigma]
      rw [SSet.stdSimplex.σ_objMk₁_of_lt _ _]
      · simp
      · simpa using (Fin.castSucc_lt_last i)
    have hLeft :
        ofOppositeSimplicialHomotopyHom H n (SSet.stdSimplex.objMk₁ (Fin.last (n + 1))) =
          a.app ⦋n⦌ := by
      cases n with
      | zero =>
          simpa [simplexIndexEquiv, Fin.lastCases_last] using
            ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 0 (Fin.last 1)
      | succ n =>
          simpa [simplexIndexEquiv, Fin.lastCases_last] using
            ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 1)
              (Fin.last (n + 2))
    have hRight :
        ofOppositeSimplicialHomotopyHom H (n + 1) (SSet.stdSimplex.objMk₁ (Fin.last (n + 2))) =
          a.app ⦋n + 1⦌ := by
      simpa [simplexIndexEquiv, Fin.lastCases_last] using
        ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 1) (Fin.last (n + 2))
    simpa [simplexIndexEquiv, hLeft, hMap, hRight] using
      a.naturality (SimplexCategory.σ i)
  · intro j
    refine Fin.cases ?_ ?_ j
    · -- The zero simplex is the `b`-endpoint, and degeneracies preserve that endpoint.
      have hMap :
          ((Δ[1] : SSet.{0}).map (SimplexCategory.σ i).op
            (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2)))) =
            SSet.stdSimplex.objMk₁ (0 : Fin (n + 3)) := by
        rw [← deltaOneOneEndpoint_eq_objMk₁_zero (n := n)]
        rw [← deltaOneOneEndpoint_eq_objMk₁_zero (n := n + 1)]
        ext k : 1
        rfl
      have hLeft :
          ofOppositeSimplicialHomotopyHom H n (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) =
            b.app ⦋n⦌ := by
        cases n with
        | zero =>
            simpa [simplexIndexEquiv, Fin.lastCases_castSucc] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 0 (0 : Fin 2)
        | succ n =>
            have hIndex :
                ofOppositeSimplicialHomotopyHom H (n + 1)
                    (SSet.stdSimplex.objMk₁ (0 : Fin (n + 3))) =
                  Fin.lastCases (a.app ⦋n + 1⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 1⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (Fin.castSucc 0) := by
              simpa [simplexIndexEquiv] using
                ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 1)
                  (Fin.castSucc 0)
            have hBranch :
                Fin.lastCases (a.app ⦋n + 1⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 1⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (0 : Fin (n + 3)) =
                  b.app ⦋n + 1⦌ := by
              change Fin.lastCases (a.app ⦋n + 1⦌)
                  (fun j ↦
                    Fin.cases (b.app ⦋n + 1⦌)
                      (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                  (Fin.castSucc 0) =
                b.app ⦋n + 1⦌
              rw [Fin.lastCases_castSucc]
              simp
            exact hIndex.trans hBranch
      have hRight :
          ofOppositeSimplicialHomotopyHom H (n + 1) (SSet.stdSimplex.objMk₁ (0 : Fin (n + 3))) =
            b.app ⦋n + 1⦌ := by
        cases n with
        | zero =>
            simpa [simplexIndexEquiv, Fin.lastCases_castSucc] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 1 (0 : Fin 3)
        | succ n =>
            have hIndex :
                ofOppositeSimplicialHomotopyHom H (n + 2)
                    (SSet.stdSimplex.objMk₁ (0 : Fin (n + 4))) =
                  Fin.lastCases (a.app ⦋n + 2⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 2⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (Fin.castSucc 0) := by
              simpa [simplexIndexEquiv] using
                ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 2)
                  (Fin.castSucc 0)
            have hBranch :
                Fin.lastCases (a.app ⦋n + 2⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋n + 2⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (0 : Fin (n + 4)) =
                  b.app ⦋n + 2⦌ := by
              change Fin.lastCases (a.app ⦋n + 2⦌)
                  (fun j ↦
                    Fin.cases (b.app ⦋n + 2⦌)
                      (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                  (Fin.castSucc 0) =
                b.app ⦋n + 2⦌
              rw [Fin.lastCases_castSucc]
              simp
            exact hIndex.trans hBranch
      simpa [simplexIndexEquiv, hLeft, hMap, hRight] using
        b.naturality (SimplexCategory.σ i)
    · intro l
      by_cases hil : i ≤ l.castSucc
      · -- Positive degree lets us reindex the simplicial operator as `σ i.castSucc`; once the
        -- mapped simplex is normalized, the branch is exactly the first reversed sigma identity.
        cases n with
        | zero =>
            exact Fin.elim0 l
        | succ n =>
            -- TODO: pass from the `simplexIndexEquiv` normal form to the canonical `objMk₁`
            -- simplex, then split the degeneracy index into the strict and adjacent subcases so
            -- the strict branch uses `sigmaCompDeltaOfLe` and the adjacent branch uses the two
            -- `δ_comp_σ = 𝟙` identities.
            sorry
      · have hli : l.castSucc < i := lt_of_not_ge hil
        -- In the complementary branch the simplicial operator is `σ i.succ`; after normalizing
        -- the mapped simplex, the branch is the second reversed sigma identity.
        cases n with
        | zero =>
            exact Fin.elim0 l
        | succ n =>
            -- TODO: pass from the `simplexIndexEquiv` normal form to the canonical `objMk₁`
            -- simplex, then use the corrected `sigmaCompDeltaOfGt` bridge to orient the exposed
            -- `σ ≫ δ` composite.
            sorry

/-- Helper for Lemma 14.28.3: once the reverse component family is natural on the generators, it
is natural for every simplex operator. -/
private lemma reverse_component_naturality_all_simplex_maps
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))
    {n₁ n₂ : SimplexCategory} (θ : n₁ ⟶ n₂) :
    reverseNaturalityProperty H θ := by
  -- The generator proofs and multiplicativity upgrade the property to all simplex maps.
  have htop :
      reverseNaturalityProperty H = ⊤ :=
    SimplexCategory.morphismProperty_eq_top
      (reverseNaturalityProperty H)
      (fun {_} i ↦ reverse_component_naturality_delta H i)
      (fun {_} i ↦ reverse_component_naturality_sigma H i)
  simpa [htop]

-- Proof sketch: recover each simplex-indexed component by splitting `Δ[1]_n` via the canonical
-- bijection `SSet.stdSimplex.objMk₁ : Fin (n + 2) ≃ Δ[1]_n`; the two endpoints come from `a` and
-- `b`, and the interior simplices are obtained from the simplicial homotopy operators by the
-- appropriate target face map.
private def ofOppositeSimplicialHomotopy
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b)) :
    DeltaOneHomotopy a b where
  hom {n} i := by
    cases n with
    | mk m =>
        exact ofOppositeSimplicialHomotopyHom H m i
  zero_endpoint n := by
    -- Normalize the endpoint simplex to the last canonical index and read off the `a` branch.
    cases n with
    | mk m =>
        rw [deltaOneZeroEndpoint_eq_objMk₁_last]
        cases m with
        | zero =>
            simpa [simplexIndexEquiv, Fin.lastCases_last] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 0 (Fin.last 1)
        | succ m =>
            simpa [simplexIndexEquiv, Fin.lastCases_last] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (m + 1) (Fin.last (m + 2))
  one_endpoint n := by
    -- Normalize the endpoint simplex to the zero canonical index and read off the `b` branch.
    cases n with
    | mk m =>
        rw [deltaOneOneEndpoint_eq_objMk₁_zero]
        cases m with
        | zero =>
            simpa [simplexIndexEquiv, Fin.lastCases_castSucc] using
              ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H 0 0
        | succ m =>
            have hIndex :
                ofOppositeSimplicialHomotopyHom H (m + 1) (SSet.stdSimplex.objMk₁ 0) =
                  Fin.lastCases (a.app ⦋m + 1⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋m + 1⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (Fin.castSucc 0) := by
              simpa [simplexIndexEquiv] using
                ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (m + 1) (Fin.castSucc 0)
            have hBranch :
                Fin.lastCases (a.app ⦋m + 1⦌)
                    (fun j ↦
                      Fin.cases (b.app ⦋m + 1⦌)
                        (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                    (0 : Fin (m + 3)) =
                  b.app ⦋m + 1⦌ := by
              change Fin.lastCases (a.app ⦋m + 1⦌)
                  (fun j ↦
                    Fin.cases (b.app ⦋m + 1⦌)
                      (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc) j)
                  (Fin.castSucc 0) =
                b.app ⦋m + 1⦌
              rw [Fin.lastCases_castSucc]
              simp
            exact hIndex.trans hBranch
  naturality σ i := by
    -- The reverse component family is natural on generators, hence on every simplex map.
    exact reverse_component_naturality_all_simplex_maps H σ i

/-- Helper for Lemma 14.28.3: the interior branch of the reverse-then-forward reconstruction
returns the original `Δ[1]`-indexed component. -/
private lemma forward_reverse_interior_reconstruction
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : DeltaOneHomotopy a b) {n : ℕ} (i : Fin (n + 1)) :
    (ofOppositeSimplicialHomotopy (toOppositeSimplicialHomotopy H)).hom
        (SSet.stdSimplex.objMk₁ i.succ.castSucc) =
      H.hom (SSet.stdSimplex.objMk₁ i.succ.castSucc) := by
  -- Route correction: after evaluating the reconstructed interior component, the exposed
  -- composite is exactly `V.σ i ≫ V.δ i.castSucc`, so the local `σ ≫ δ` adapter reduces it to a
  -- canonical `δ ≫ σ` identity.
  -- TODO: first evaluate the reconstructed component with
  -- `ofOppositeSimplicialHomotopyHom_apply_interior`, then rewrite the exposed `V.σ i ≫
  -- V.δ i.castSucc` composite through `sigmaCompDeltaOfLe (i := i) (j := i)`, and finally use the
  -- adjacent `δ_comp_σ_succ` identity to collapse the remaining target-side factor.
  sorry

private theorem ofOppositeSimplicialHomotopy_toOppositeSimplicialHomotopy
    {U V : CosimplicialObject C} {a b : U ⟶ V} (H : DeltaOneHomotopy a b) :
    ofOppositeSimplicialHomotopy (toOppositeSimplicialHomotopy H) = H := by
  -- Compare the two `Δ[1]`-indexed families on the canonical endpoint and interior simplices.
  apply DeltaOneHomotopy.ext
  intro n α
  cases n with
  | mk m =>
      obtain ⟨k, rfl⟩ := (simplexIndexEquiv m).surjective α
      cases m with
      | zero =>
          refine Fin.lastCases ?_ ?_ k
          · -- In degree `0`, the last canonical simplex is the constant `0` endpoint.
            simpa [deltaOneZeroEndpoint_eq_objMk₁_last] using
              (ofOppositeSimplicialHomotopy (toOppositeSimplicialHomotopy H)).zero_endpoint ⦋0⦌
                |>.trans (H.zero_endpoint ⦋0⦌).symm
          · intro j
            refine Fin.cases ?_ ?_ j
            · -- The zero canonical simplex is the constant `1` endpoint.
              simpa [deltaOneOneEndpoint_eq_objMk₁_zero] using
                (ofOppositeSimplicialHomotopy (toOppositeSimplicialHomotopy H)).one_endpoint ⦋0⦌
                  |>.trans (H.one_endpoint ⦋0⦌).symm
            · intro i
              exact Fin.elim0 i
      | succ m =>
          refine Fin.lastCases ?_ ?_ k
          · -- The last canonical simplex is the constant `0` endpoint.
            simpa [deltaOneZeroEndpoint_eq_objMk₁_last] using
              (ofOppositeSimplicialHomotopy (toOppositeSimplicialHomotopy H)).zero_endpoint
                  ⦋m + 1⦌
                |>.trans (H.zero_endpoint ⦋m + 1⦌).symm
          · intro j
            refine Fin.cases ?_ ?_ j
            · -- The zero canonical simplex is the constant `1` endpoint.
              simpa [deltaOneOneEndpoint_eq_objMk₁_zero] using
                (ofOppositeSimplicialHomotopy (toOppositeSimplicialHomotopy H)).one_endpoint
                    ⦋m + 1⦌
                  |>.trans (H.one_endpoint ⦋m + 1⦌).symm
            · intro i
              -- The remaining simplices are the canonical interior simplices.
              simpa using forward_reverse_interior_reconstruction (n := m) H i

private theorem toOppositeSimplicialHomotopy_ofOppositeSimplicialHomotopy
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b)) :
    toOppositeSimplicialHomotopy (ofOppositeSimplicialHomotopy H) = H := by
  -- Extensionality reduces the comparison to the `h i` components.
  ext n i
  apply Quiver.Hom.unop_inj
  -- Evaluate the reverse construction on the canonical interior simplex and simplify with the
  -- adjacent `δσ = id` relation in the cosimplicial target.
  have hEval :
      (ofOppositeSimplicialHomotopy H).hom (SSet.stdSimplex.objMk₁ i.succ.castSucc) =
        (H.h i).unop ≫ V.δ i.castSucc := by
    calc
      (ofOppositeSimplicialHomotopy H).hom (SSet.stdSimplex.objMk₁ i.succ.castSucc) =
          Fin.lastCases
            (a.app ⦋n + 1⦌)
            (fun j ↦
              Fin.cases
                (b.app ⦋n + 1⦌)
                (fun l ↦ (H.h l).unop ≫ V.δ l.castSucc)
                j)
            i.castSucc.succ := by
              simpa [ofOppositeSimplicialHomotopy, simplexIndexEquiv] using
                ofOppositeSimplicialHomotopyHom_apply_simplexIndexEquiv H (n + 1)
                  i.succ.castSucc
      _ = (H.h i).unop ≫ V.δ i.castSucc := by
            rw [Fin.succ_castSucc, Fin.lastCases_castSucc, Fin.cases_succ]
            rfl
  change (ofOppositeSimplicialHomotopy H).hom (SSet.stdSimplex.objMk₁ i.succ.castSucc) ≫
      V.σ i =
    (H.h i).unop
  rw [hEval]
  simpa [toOppositeSimplicialHomotopy, Category.assoc] using
    (show ((H.h i).unop ≫ V.δ i.castSucc) ≫ V.σ i = (H.h i).unop by
      simpa [Category.assoc] using
        congrArg (fun k ↦ (H.h i).unop ≫ k) (V.δ_comp_σ_self (i := i)))

/-- Lemma 14.28.3: a `Δ[1]`-indexed homotopy from `a` to `b` between cosimplicial objects is
equivalent, at the level of actual homotopy data, to a simplicial homotopy between the
corresponding opposite morphisms `a', b' : V' ⟶ U'`. -/
@[stacks 019X]
def equivOppositeSimplicialHomotopy
    {U V : CosimplicialObject C} (a b : U ⟶ V) :
    DeltaOneHomotopy a b ≃
      SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b) where
  toFun := toOppositeSimplicialHomotopy
  invFun := ofOppositeSimplicialHomotopy
  left_inv := ofOppositeSimplicialHomotopy_toOppositeSimplicialHomotopy
  right_inv := toOppositeSimplicialHomotopy_ofOppositeSimplicialHomotopy

end DeltaOneHomotopy

-- Proof sketch: this is the `Nonempty` companion of the data-level equivalence above.
-- Proof sketch: transport each generating step of the `Relation.EqvGen` closure across the
-- data-level equivalence above.
/-- The zigzag relation generated by `Δ[1]`-indexed cosimplicial homotopies agrees with the zigzag
relation generated by simplicial homotopies after passage to the opposite simplicial objects. -/
theorem deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag
    {U V : CosimplicialObject C} (a b : U ⟶ V) :
    DeltaOneHomotopic a b ↔
      SimplicialObject.Homotopic (NatTrans.op a) (NatTrans.op b) := by
  constructor
  · intro h
    induction h with
    | rel x y hxy =>
        exact SimplicialObject.Homotopic.of_homotopy
          (DeltaOneHomotopy.equivOppositeSimplicialHomotopy x y hxy.some)
    | refl x =>
        exact SimplicialObject.Homotopic.refl (NatTrans.op x)
    | symm x y _ ih =>
        exact ih.symm
    | trans x y z _ _ ihxy ihyz =>
        exact ihxy.trans ihyz
  · intro h
    have hunop :
        ∀ {x y : V.op ⟶ U.op}, SimplicialObject.Homotopic x y →
          DeltaOneHomotopic (NatTrans.unop x) (NatTrans.unop y) := by
      intro x y hxy
      induction hxy with
      | rel x y hxy =>
          exact DeltaOneHomotopic.of_homotopy <|
            (DeltaOneHomotopy.equivOppositeSimplicialHomotopy
              (NatTrans.unop x)
              (NatTrans.unop y)).symm <|
                by simpa using hxy.some
      | refl x =>
          exact DeltaOneHomotopic.refl (NatTrans.unop x)
      | symm x y _ ih =>
          exact ih.symm
      | trans x y z _ _ ihxy ihyz =>
          exact ihxy.trans ihyz
    simpa using hunop h

end CategoryTheory.CosimplicialObject
