import StacksProject_2024.stacks_project.Chap14.Lemma_14_18_4
import StacksProject_2024.stacks_project.Chap14.Lemma_14_21_3

open CategoryTheory
open Opposite
open scoped Simplicial

noncomputable section

universe u

/- Domain-style sampling for Lemma 14.21.4:
- primary domain: simplicial-set skeletons, truncated skeleton adjunctions, and simplicial-set
  dimension bounds;
- sampled owner declarations:
  `SSet.skeleton`,
  `SSet.HasDimensionLT`,
  `SSet.HasDimensionLE`,
  `SSet.hasDimensionLT_iff_of_iso`,
  `SSet.skAdj`;
- best owner abstraction: the canonical owner layer is the dimension predicate
  `SSet.HasDimensionLE`; the bridge is the source-faithful identification of `i_{m!} U` with the
  ordinary `(m + 1)`-skeleton of its underlying simplicial set;
- primitive data: only the truncated simplicial set `U`;
- derived API: the transported instance
  `((SSet.Truncated.sk m).obj U).HasDimensionLE m`, and the pointwise degree-`> m` degeneracy
  statement as a thin corollary.

Source/core/bridge triage:
- `source-facing`: the textbook claim that every simplex of `i_{m!} U` in degree `> m` is
  degenerate;
- `core/canonical`: the dimension bound `((SSet.Truncated.sk m).obj U).HasDimensionLE m`;
- `bridge/view`: the source-proof object `V' = V.skeleton (m + 1)` inside
  `V = (SSet.Truncated.sk m).obj U`, together with the adjunction argument showing `V' = V`. -/

/-- Helper for Lemma 14.21.4: the inclusion of the ordinary `(m + 1)`-skeleton becomes an
isomorphism after `m`-truncation, because the skeleton agrees with the ambient simplicial set in
all degrees `≤ m`. -/
lemma skeleton_inclusion_truncation_isIso (m : ℕ) (V : SSet.{u}) :
    IsIso ((SSet.truncation m).map (V.skeleton (m + 1)).ι) := by
  -- In each truncated degree, the skeleton inclusion is the identity on a top subobject.
  refine (NatTrans.isIso_iff_isIso_app _).2 ?_
  intro Δ
  cases Δ with
  | op Δ =>
      cases Δ with
      | mk Δ hΔ =>
          cases Δ with
          | mk i =>
              change IsIso (((V.skeleton (m + 1)).ι).app (op ⦋i⦌))
              rw [isIso_iff_bijective]
              constructor
              · rw [← mono_iff_injective]
                infer_instance
              · intro x
                refine ⟨⟨x, ?_⟩, rfl⟩
                rw [V.skeleton_obj_eq_top (Nat.lt_succ_of_le hΔ)]
                simp

/-- Helper for Lemma 14.21.4: after passing through the `skAdj` adjunction, the unit of `U`
produces a canonical morphism from `i_{m!} U` to the ordinary `(m + 1)`-skeleton. -/
noncomputable def truncated_extension_to_skeleton (m : ℕ) (U : SSet.Truncated m) :
    (SSet.Truncated.sk m).obj U ⟶ (((SSet.Truncated.sk m).obj U).skeleton (m + 1) : SSet) :=
  let V : SSet := (SSet.Truncated.sk m).obj U
  let ι : (V.skeleton (m + 1) : SSet) ⟶ V := (V.skeleton (m + 1)).ι
  ((SSet.skAdj m).homEquiv U ((V.skeleton (m + 1) : SSet))).symm
    ((SSet.skAdj m).unit.app U ≫
      @inv _ _ _ _ ((SSet.truncation m).map ι)
        (skeleton_inclusion_truncation_isIso (m := m) V))

/-- Helper for Lemma 14.21.4: the adjunction comparison map from `i_{m!} U` to the ordinary
`(m + 1)`-skeleton is a retraction of the skeleton inclusion. -/
lemma truncated_extension_to_skeleton_comp_inclusion (m : ℕ) (U : SSet.Truncated m) :
    truncated_extension_to_skeleton (m := m) U ≫
        (((SSet.Truncated.sk m).obj U).skeleton (m + 1)).ι =
      𝟙 ((SSet.Truncated.sk m).obj U) := by
  let V : SSet := (SSet.Truncated.sk m).obj U
  let ι : (V.skeleton (m + 1) : SSet) ⟶ V := (V.skeleton (m + 1)).ι
  have hcomp :
      ((SSet.skAdj m).unit.app U ≫
        @inv _ _ _ _ ((SSet.truncation m).map ι)
          (skeleton_inclusion_truncation_isIso (m := m) V)) ≫
        (SSet.truncation m).map ι =
      (SSet.skAdj m).unit.app U := by
    simp [Category.assoc]
  have hunit :
      (SSet.skAdj m).unit.app U =
        ((SSet.skAdj m).homEquiv U V) (𝟙 V) := by
    simpa using
      (Adjunction.homEquiv_unit (adj := SSet.skAdj m) (f := 𝟙 V)).symm
  have hnaturality :
      ((SSet.skAdj m).homEquiv U V)
          (truncated_extension_to_skeleton (m := m) U ≫ ι) =
        ((SSet.skAdj m).homEquiv U ((V.skeleton (m + 1) : SSet))
          (truncated_extension_to_skeleton (m := m) U)) ≫
          (SSet.truncation m).map ι := by
    simpa using
      (SSet.skAdj m).homEquiv_naturality_right
        (truncated_extension_to_skeleton (m := m) U) ι
  have hσcomp :
      ((SSet.skAdj m).homEquiv U ((V.skeleton (m + 1) : SSet))
          (truncated_extension_to_skeleton (m := m) U)) ≫
          (SSet.truncation m).map ι =
        ((SSet.skAdj m).unit.app U ≫
          @inv _ _ _ _ ((SSet.truncation m).map ι)
            (skeleton_inclusion_truncation_isIso (m := m) V)) ≫
          (SSet.truncation m).map ι := by
    simp [truncated_extension_to_skeleton, V, ι]
  -- Compare both maps after applying the `skAdj` hom-set equivalence.
  apply ((SSet.skAdj m).homEquiv U V).injective
  exact hnaturality.trans (hσcomp.trans (hcomp.trans hunit))

/-- Helper for Lemma 14.21.4: the skeleton inclusion is also a retraction of the adjunction
comparison map, so the two maps define an isomorphism. -/
lemma skeleton_inclusion_comp_truncated_extension_to_skeleton (m : ℕ) (U : SSet.Truncated m) :
    (((SSet.Truncated.sk m).obj U).skeleton (m + 1)).ι ≫
        truncated_extension_to_skeleton (m := m) U =
      𝟙 ((((SSet.Truncated.sk m).obj U).skeleton (m + 1) : SSet)) := by
  let V : SSet := (SSet.Truncated.sk m).obj U
  let ι : (V.skeleton (m + 1) : SSet) ⟶ V := (V.skeleton (m + 1)).ι
  -- Cancel the mono inclusion from the right using the previously proved splitting identity.
  apply (cancel_mono ι).1
  calc
    (ι ≫ truncated_extension_to_skeleton (m := m) U) ≫ ι =
        ι ≫ (truncated_extension_to_skeleton (m := m) U ≫ ι) := by
          simp [Category.assoc]
    _ = ι ≫ 𝟙 V := by
          rw [truncated_extension_to_skeleton_comp_inclusion (m := m) U]
    _ = (𝟙 (V.skeleton (m + 1) : SSet)) ≫ ι := by
          simp

/-- Helper for Lemma 14.21.4: the canonical extension `i_{m!} U` is isomorphic to the ordinary
`(m + 1)`-skeleton of its underlying simplicial set. -/
noncomputable def truncated_extension_iso_skeleton (m : ℕ) (U : SSet.Truncated m) :
    (SSet.Truncated.sk m).obj U ≅ (((SSet.Truncated.sk m).obj U).skeleton (m + 1) : SSet) :=
  { hom := truncated_extension_to_skeleton (m := m) U
    inv := (((SSet.Truncated.sk m).obj U).skeleton (m + 1)).ι
    hom_inv_id := truncated_extension_to_skeleton_comp_inclusion (m := m) U
    inv_hom_id := skeleton_inclusion_comp_truncated_extension_to_skeleton (m := m) U }

/-- Helper for Lemma 14.21.4: the canonical extension of an `m`-truncated simplicial set has
dimension at most `m`. -/
instance instTruncatedSkeletonHasDimensionLE (m : ℕ) (U : SSet.Truncated m) :
    ((SSet.Truncated.sk m).obj U).HasDimensionLE m := by
  -- Transport the standard dimension bound from the ordinary skeleton identified above.
  change ((SSet.Truncated.sk m).obj U).HasDimensionLT (m + 1)
  let e :
      (SSet.Truncated.sk m).obj U ≅
        (((SSet.Truncated.sk m).obj U).skeleton (m + 1) : SSet) :=
    truncated_extension_iso_skeleton (m := m) U
  rw [SSet.hasDimensionLT_iff_of_iso e (m + 1)]
  infer_instance

/-- Lemma 14.21.4: if `U` is an `m`-truncated simplicial set and `n > m`, then every `n`-simplex
of `i_{m!} U`, i.e. of `(SSet.Truncated.sk m).obj U`, is degenerate. -/
theorem truncatedSkeleton_mem_degenerate_of_lt
    (m : ℕ) (U : SSet.Truncated m) {n : ℕ} (h : m < n)
    (x : ((SSet.Truncated.sk m).obj U) _⦋n⦌) :
    x ∈ ((SSet.Truncated.sk m).obj U).degenerate n := by
  -- Once the owner-level dimension bound is in place, the high-degree degeneracy statement is
  -- exactly the defining property of `HasDimensionLT`.
  rw [((SSet.Truncated.sk m).obj U).degenerate_eq_top_of_hasDimensionLT (m + 1) n
    (Nat.succ_le_of_lt h)]
  exact Set.mem_univ x
