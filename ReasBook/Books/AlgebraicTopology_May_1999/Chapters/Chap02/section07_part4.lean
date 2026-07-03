import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_2_7_6 (from Chap02) -/
/- Lemma 2.7.6 is the finite-cover specialization of the canonical group-level van Kampen theorem
from Theorem 2.7.5. The owner of the open-cover diagram and its colimit statement is therefore
`fundamental_group_is_colimit_of_path_connected_open_cover`, not a separate finite-cover copy. -/
#check fundamental_group_is_colimit_of_path_connected_open_cover

/- The corresponding compatibility of the universal comparison morphism with the cocone legs is
likewise the companion theorem from Theorem 2.7.5. -/
#check fundamental_group_is_colimit_of_path_connected_open_cover_desc_fac

/-! ### ProofStep_2_7_7 (from Chap02) -/
universe u v

open unitInterval

noncomputable section

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

/-- ProofStep 2.7.7: for a finite open cover by path-connected open subsets that is closed under
finite intersections and contains the common basepoint `x`, one can choose for each `y : X` a
path from `x` to `y` such that whenever `y ∈ O i`, the chosen path is entirely contained in
`O i`. -/
-- Proof sketch: for each `y`, the family of cover members containing `y` is nonempty by the cover
-- assumption and finite because the cover is finite. Closure under finite intersections therefore
-- produces a member `O j` equal to the intersection of all those cover members. Since `x` belongs
-- to every `O i`, both `x` and `y` lie in `O j`; path connectedness of `O j` gives a path from
-- `x` to `y` inside `O j`, hence inside every cover member containing `y`.
theorem exists_cover_compatible_basepoint_paths
    (O : ι → TopologicalSpace.Opens X)
    [Finite ι]
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O) :
    ∃ γ : ∀ y : X, Path x y,
      ∀ (i : ι) (y : X), y ∈ O i → ∀ t : I, γ y t ∈ O i := by
  classical
  letI := Fintype.ofFinite ι
  let coverAt : X → Finset ι := fun y ↦ Finset.univ.filter fun i ↦ y ∈ O i
  have coverAt_nonempty : ∀ y, (coverAt y).Nonempty := fun y ↦ by
    obtain ⟨i, hi⟩ := hO.exists_mem y
    exact ⟨i, by simp [coverAt, hi]⟩
  let center : X → ι := fun y ↦ Classical.choose (hinter (coverAt y) (coverAt_nonempty y))
  have center_eq : ∀ y, (coverAt y).inf' (coverAt_nonempty y) O = O (center y) := fun y ↦
    Classical.choose_spec (hinter (coverAt y) (coverAt_nonempty y))
  have center_mem : ∀ y, y ∈ O (center y) := fun y ↦ by
    have hy : y ∈ (coverAt y).inf' (coverAt_nonempty y) O := by
      rw [Finset.inf'_eq_inf]
      change y ∈ (((coverAt y).inf O : TopologicalSpace.Opens X) : Set X)
      rw [TopologicalSpace.Opens.coe_finset_inf]
      simp [coverAt]
    simpa [center_eq y] using hy
  have center_le : ∀ {i y}, y ∈ O i → O (center y) ≤ O i := by
    intro i y hyi
    have hi : i ∈ coverAt y := by simp [coverAt, hyi]
    have hle : (coverAt y).inf' (coverAt_nonempty y) O ≤ O i := by
      rw [Finset.inf'_eq_inf]
      exact Finset.inf_le hi
    simpa [center_eq y] using hle
  let γ : ∀ y : X, Path x y := fun y ↦
    letI := hpath (center y)
    (PathConnectedSpace.somePath ⟨x, hx (center y)⟩ ⟨y, center_mem y⟩).map continuous_subtype_val
  refine ⟨γ, ?_⟩
  intro i y hyi t
  have hγ : γ y t ∈ O (center y) := by
    simp [γ]
  exact center_le hyi hγ

/-! ### ProofStep_2_7_8 (from Chap02) -/
universe u v

open CategoryTheory CategoryTheory.Limits
open scoped FundamentalGroupoid

noncomputable section

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v}

variable
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hPi : IsColimit (fundamental_groupoid_cover_cocone O))
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    (x : X)

/- ProofStep 2.7.8 is the bridge/view obtained by applying the canonical owner
`CategoryTheory.Functor.mapEnd` to the universal colimit-desc functor `hPi.desc S` at the object
`FundamentalGroupoid.mk x`. This restricts the universal functor `Π(X) ⥤ S.pt` to the vertex
group `π₁(X, x)`. -/
#check (hPi.desc S).mapEnd (FundamentalGroupoid.mk x)

/-! ### ProofStep_2_7_9 (from Chap02) -/
universe u v

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

/-- A finite subcollection of an indexed open cover is closed under nonempty finite intersections if
every nonempty finite subfamily has its intersection represented by another member of that same
finite subcollection. -/
def Finset.IsClosedUnderNonemptyFiniteIntersections
    (S : Finset ι) (O : ι → TopologicalSpace.Opens X) : Prop :=
  ∀ t : Finset ι, ∀ ht : t.Nonempty, (t : Set ι) ⊆ S → ∃ i ∈ S, t.inf' ht O = O i

/-- The source-facing owner for a nonempty finite subcollection of a cover that is itself closed
under nonempty finite intersections. -/
abbrev intersection_closed_subcover_index (O : ι → TopologicalSpace.Opens X) :=
  { S : Finset ι // S.Nonempty ∧ S.IsClosedUnderNonemptyFiniteIntersections O }

/-- Helper for ProofStep 2.7.9: the image of a continuous map from a compact parameter space lies
in a finite union of members of the ambient open cover. -/
theorem compact_image_subset_finite_union_of_cover
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (O : ι → TopologicalSpace.Opens X)
    (hO : TopologicalSpace.IsOpenCover O)
    (f : C(K, X)) :
    ∃ T : Finset ι, Set.range f ⊆ ⋃ i ∈ T, (O i : Set X) := by
  -- The compact image of `f` admits a finite subcover by members of the ambient open cover.
  have hcompact : IsCompact (Set.range f) := by
    simpa using isCompact_range f.continuous
  have hsU : Set.range f ⊆ ⋃ i, (O i : Set X) := by
    intro y hy
    rcases hy with ⟨k, rfl⟩
    obtain ⟨i, hi⟩ := hO.exists_mem (f k)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨T, hT⟩ :=
    hcompact.elim_finite_subcover (fun i ↦ (O i : Set X)) (fun i ↦ (O i).isOpen) hsU
  exact ⟨T, hT⟩

/-- Helper for ProofStep 2.7.9: a nonempty finite family of cover members can be enlarged to a
nonempty finite family that is internally closed under nonempty finite intersections. -/
theorem exists_nonempty_intersection_closed_finset_superset
    (O : ι → TopologicalSpace.Opens X)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (T : Finset ι) (hT : T.Nonempty) :
    ∃ S : intersection_closed_subcover_index O, T ⊆ (S : Finset ι) := by
  classical
  let nonemptySubsets : Finset { t : Finset ι // t ∈ T.powerset.filter Finset.Nonempty } :=
    (T.powerset.filter Finset.Nonempty).attach
  let representative :
      { t : Finset ι // t ∈ T.powerset.filter Finset.Nonempty } → ι := fun t ↦
    Classical.choose (hinter t.1 ((Finset.mem_filter.mp t.2).2))
  let closedCarrier : Finset ι := T ∪ nonemptySubsets.image representative
  have closedCarrier_nonempty : closedCarrier.Nonempty := by
    rcases hT with ⟨i, hi⟩
    exact ⟨i, Finset.mem_union.mpr (Or.inl hi)⟩
  have member_has_original_carrier :
      ∀ j ∈ closedCarrier, ∃ t : Finset ι,
        ∃ ht : t.Nonempty, (t : Set ι) ⊆ T ∧ t.inf' ht O = O j := by
    intro j hj
    rcases Finset.mem_union.mp hj with hjT | hjimage
    · have hj_mem_singleton : j ∈ ({j} : Finset ι) := by
        simp
      have hsingleton_nonempty : ({j} : Finset ι).Nonempty := ⟨j, hj_mem_singleton⟩
      refine ⟨{j}, hsingleton_nonempty, ?_, ?_⟩
      · intro k hk
        have hk' : k = j := by
          simpa using hk
        simpa [hk'] using hjT
      · exact Finset.inf'_singleton (f := O) (b := j)
    · rcases Finset.mem_image.mp hjimage with ⟨t, -, rfl⟩
      refine ⟨t.1, (Finset.mem_filter.mp t.2).2, ?_, ?_⟩
      · exact Finset.mem_powerset.mp (Finset.mem_filter.mp t.2).1
      · -- The chosen representative is defined to realize the finite intersection of `t`.
        simpa [representative] using
          (Classical.choose_spec (hinter t.1 ((Finset.mem_filter.mp t.2).2)))
  -- Replacing each index in a nonempty finite family by a chosen finite intersection of original
  -- cover members turns the whole finite infimum into the infimum over the union of those chosen
  -- carriers.
  have finite_inf_eq_biUnion_carrier_inf :
      ∀ (u : Finset ι) (hu : u.Nonempty) (carrier : ι → Finset ι)
        (hcarrier_nonempty : ∀ j ∈ u, (carrier j).Nonempty)
        (hcarrier_eq : ∀ j (hj : j ∈ u), O j = (carrier j).inf' (hcarrier_nonempty j hj) O)
        (hcarrier_union_nonempty : (u.biUnion carrier).Nonempty),
        u.inf' hu O =
          (u.biUnion carrier).inf' hcarrier_union_nonempty O := by
    intro u hu carrier hcarrier_nonempty hcarrier_eq hcarrier_union_nonempty
    ext x
    rw [Finset.inf'_eq_inf, Finset.inf'_eq_inf]
    rw [TopologicalSpace.Opens.coe_finset_inf, TopologicalSpace.Opens.coe_finset_inf]
    constructor
    · intro hx
      have hxu : ∀ j ∈ u, x ∈ O j := by
        simpa using hx
      have hxcarrier : ∀ j ∈ u, ∀ k ∈ carrier j, x ∈ O k := by
        intro j hj k hk
        have hxj : x ∈ O j := hxu j hj
        rw [hcarrier_eq j hj] at hxj
        rw [Finset.inf'_eq_inf] at hxj
        have hxj' : x ∈ (((carrier j).inf O : TopologicalSpace.Opens X) : Set X) := hxj
        rw [TopologicalSpace.Opens.coe_finset_inf] at hxj'
        have hforall : ∀ k ∈ carrier j, x ∈ O k := by
          simpa using hxj'
        exact hforall k hk
      simpa [Finset.mem_biUnion] using hxcarrier
    · intro hx
      have hxcarrier : ∀ j ∈ u, ∀ k ∈ carrier j, x ∈ O k := by
        simpa [Finset.mem_biUnion] using hx
      have hxu : ∀ j ∈ u, x ∈ O j := by
        intro j hj
        rw [hcarrier_eq j hj, Finset.inf'_eq_inf]
        have hforall : ∀ k ∈ carrier j, x ∈ O k := by
          intro k hk
          exact hxcarrier j hj k hk
        have hxj : x ∈ (((carrier j).inf O : TopologicalSpace.Opens X) : Set X) := by
          rw [TopologicalSpace.Opens.coe_finset_inf]
          simpa using hforall
        exact hxj
      simpa using hxu
  have closedCarrier_closed :
      closedCarrier.IsClosedUnderNonemptyFiniteIntersections O := by
    intro u hu hu_subset
    let carrier : ι → Finset ι := fun j ↦
      if hj : j ∈ closedCarrier then
        Classical.choose (member_has_original_carrier j hj)
      else
        ∅
    have carrier_nonempty : ∀ j ∈ u, (carrier j).Nonempty := by
      intro j hj
      have hjclosed : j ∈ closedCarrier := hu_subset hj
      simpa [carrier, hjclosed] using
        (Classical.choose (Classical.choose_spec (member_has_original_carrier j hjclosed)))
    have carrier_subset : ∀ j ∈ u, ((carrier j : Finset ι) : Set ι) ⊆ T := by
      intro j hj
      have hjclosed : j ∈ closedCarrier := hu_subset hj
      simpa [carrier, hjclosed] using
        (Classical.choose_spec (Classical.choose_spec (member_has_original_carrier j hjclosed))).1
    have carrier_eq : ∀ j (hj : j ∈ u),
        O j = (carrier j).inf' (carrier_nonempty j hj) O := by
      intro j hj
      have hjclosed : j ∈ closedCarrier := hu_subset hj
      symm
      simpa [carrier, hjclosed] using
        (Classical.choose_spec (Classical.choose_spec (member_has_original_carrier j hjclosed))).2
    have carrier_union_nonempty : (u.biUnion carrier).Nonempty := by
      rcases hu with ⟨j, hj⟩
      rcases carrier_nonempty j hj with ⟨k, hk⟩
      exact ⟨k, Finset.mem_biUnion.mpr ⟨j, hj, hk⟩⟩
    have carrier_union_mem :
        u.biUnion carrier ∈ T.powerset.filter Finset.Nonempty := by
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_powerset]
        intro k hk
        rcases Finset.mem_biUnion.mp hk with ⟨j, hj, hkj⟩
        exact carrier_subset j hj hkj
      · exact carrier_union_nonempty
    let carrierStage :
        { t : Finset ι // t ∈ T.powerset.filter Finset.Nonempty } :=
      ⟨u.biUnion carrier, carrier_union_mem⟩
    refine ⟨representative carrierStage, ?_, ?_⟩
    · have hcarrierStage_mem : carrierStage ∈ nonemptySubsets := by
        simp [nonemptySubsets]
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_image.mpr ⟨carrierStage, hcarrierStage_mem, rfl⟩
    · -- First collapse the finite infimum over `u` to the infimum over the original carriers, then
      -- use the chosen representative of that carrier union.
      calc
        u.inf' hu O
            = (u.biUnion carrier).inf' carrier_union_nonempty O := by
                exact
                  finite_inf_eq_biUnion_carrier_inf
                    u hu carrier carrier_nonempty carrier_eq carrier_union_nonempty
        _ = O (representative carrierStage) := by
              simpa [carrierStage, representative] using
                (Classical.choose_spec (hinter (u.biUnion carrier) carrier_union_nonempty))
  refine ⟨⟨closedCarrier, closedCarrier_nonempty, closedCarrier_closed⟩, ?_⟩
  -- The original finite family sits inside the enlarged intersection-closed carrier.
  intro i hi
  exact Finset.mem_union.mpr (Or.inl hi)

/-- Helper for ProofStep 2.7.9: any finite subcollection of a cover that is globally closed under
finite intersections can be enlarged to a finite subcollection whose restricted cover is itself
closed under nonempty finite intersections. -/
-- Proof sketch: split into the empty and nonempty cases. In the nonempty case, enlarge using the
-- stronger nonempty-stage lemma and then forget the subtype witness.
theorem exists_intersection_closed_finset_superset
    (O : ι → TopologicalSpace.Opens X)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (T : Finset ι) :
    ∃ S : Finset ι, T ⊆ S ∧
      S.IsClosedUnderNonemptyFiniteIntersections O := by
  classical
  by_cases hT : T.Nonempty
  · -- In the nonempty case, use the stronger stage construction and forget the nonempty witness.
    obtain ⟨S, hTS⟩ := exists_nonempty_intersection_closed_finset_superset O hinter T hT
    exact ⟨S.1, hTS, S.2.2⟩
  · -- In the empty case, the empty finite family is vacuously closed under nonempty intersections.
    refine ⟨∅, ?_, ?_⟩
    · intro i hi
      exact False.elim (hT ⟨i, hi⟩)
    · intro t ht ht_subset
      exfalso
      rcases ht with ⟨i, hi⟩
      have hi_empty : i ∈ (∅ : Finset ι) := ht_subset hi
      simp at hi_empty

/-- ProofStep 2.7.9 (1): every loop in the general cover case has image in a finite union `U_S`
coming from a nonempty finite subcover `S` of `O` that is itself closed under nonempty finite
intersections. -/
-- Proof sketch: the unit interval is compact, so the image of a loop is compact. Pull back the
-- open cover along the loop, extract a finite subcover of the image, and then enlarge the
-- resulting finite index set using `exists_intersection_closed_finset_superset`.
theorem loop_image_subset_finite_union_of_intersection_closed_subcover
    (O : ι → TopologicalSpace.Opens X)
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    {x : X} (γ : Path x x) :
    ∃ S : intersection_closed_subcover_index O,
      Set.range γ ⊆ ⋃ i ∈ (S : Finset ι), (O i : Set X) := by
  -- Compactness of the interval gives a finite cover of the loop image.
  obtain ⟨T, hT⟩ := compact_image_subset_finite_union_of_cover O hO γ.toContinuousMap
  have hT_nonempty : T.Nonempty := by
    -- The basepoint lies in the image, so one of the covering indices must appear in `T`.
    have hxrange : x ∈ Set.range γ := by
      refine ⟨0, ?_⟩
      simp
    have hxcover : x ∈ ⋃ i ∈ T, (O i : Set X) := hT hxrange
    rcases Set.mem_iUnion₂.mp hxcover with ⟨i, hiT, _⟩
    exact ⟨i, hiT⟩
  obtain ⟨S, hTS⟩ := exists_nonempty_intersection_closed_finset_superset O hinter T hT_nonempty
  refine ⟨S, ?_⟩
  -- Enlarge the finite image cover from `T` to the intersection-closed stage `S`.
  intro z hz
  have hzT : z ∈ ⋃ i ∈ T, (O i : Set X) := hT hz
  rcases Set.mem_iUnion₂.mp hzT with ⟨i, hiT, hzi⟩
  exact Set.mem_iUnion₂.mpr ⟨i, hTS hiT, hzi⟩

/-- ProofStep 2.7.9 (2): every homotopy between loops in the general cover case has image in a
finite union `U_S` coming from a nonempty finite subcover `S` of `O` that is itself closed under
nonempty finite intersections. -/
-- Proof sketch: the square `I × I` is compact, so the image of the homotopy is compact. Pull back
-- the open cover along the homotopy map, extract a finite subcover of its image, and then enlarge
-- the resulting finite index set using `exists_intersection_closed_finset_superset`.
theorem homotopy_image_subset_finite_union_of_intersection_closed_subcover
    (O : ι → TopologicalSpace.Opens X)
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    {x : X} {γ₀ γ₁ : Path x x} (H : Path.Homotopy γ₀ γ₁) :
    ∃ S : intersection_closed_subcover_index O,
      Set.range H ⊆ ⋃ i ∈ (S : Finset ι), (O i : Set X) := by
  -- Compactness of the square gives a finite cover of the homotopy image.
  obtain ⟨T, hT⟩ := compact_image_subset_finite_union_of_cover O hO H.toContinuousMap
  have hT_nonempty : T.Nonempty := by
    -- The constant basepoint value appears in the homotopy image, so `T` is nonempty.
    have hxrange : x ∈ Set.range H := by
      refine ⟨(0, 0), ?_⟩
      simp
    have hxcover : x ∈ ⋃ i ∈ T, (O i : Set X) := hT hxrange
    rcases Set.mem_iUnion₂.mp hxcover with ⟨i, hiT, _⟩
    exact ⟨i, hiT⟩
  obtain ⟨S, hTS⟩ := exists_nonempty_intersection_closed_finset_superset O hinter T hT_nonempty
  refine ⟨S, ?_⟩
  -- Enlarge the finite image cover from `T` to the intersection-closed stage `S`.
  intro z hz
  have hzT : z ∈ ⋃ i ∈ T, (O i : Set X) := hT hz
  rcases Set.mem_iUnion₂.mp hzT with ⟨i, hiT, hzi⟩
  exact Set.mem_iUnion₂.mpr ⟨i, hTS hiT, hzi⟩

/-! ### Lemma_2_7_10 (from Chap02) -/
universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace.Opens unitInterval

noncomputable section

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

/-- The open subset `U_S` obtained by taking the union of the members of a finite subcollection
`S`. -/
abbrev finite_intersection_closed_union
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (S : intersection_closed_subcover_index O) : TopologicalSpace.Opens (TopCat.of X) :=
  ⨆ i : (S : Finset ι), O i

local notation "U[" O ", " S "]" => finite_intersection_closed_union O S

/-- Enlarging a finite intersection-closed subcollection enlarges the corresponding finite union of
open sets. -/
-- Proof sketch: every summand `O i` appearing in the smaller union also appears in the larger
-- union, so the universal property of the supremum gives the required inclusion.
private theorem finite_intersection_closed_union_mono
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    {S T : intersection_closed_subcover_index O} (hST : S ≤ T) :
    U[O, S] ≤ U[O, T] := by
  -- Each summand of the smaller supremum also appears in the larger supremum.
  rw [finite_intersection_closed_union, finite_intersection_closed_union]
  refine iSup_le ?_
  intro i
  exact le_iSup (fun j : (T : Finset ι) ↦ O j) ⟨i, hST i.2⟩

/-- The common basepoint lies in the finite union attached to any nonempty finite
intersection-closed subcollection. -/
-- Proof sketch: choose an index in the nonempty finite subcollection. Since `x` lies in every
-- cover member, it lies in that chosen member and hence in the supremum defining `U_S`.
theorem basepoint_mem_finite_intersection_closed_union
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O) :
    x ∈ U[O, S] := by
  -- Choose any stage member and use that summand of the finite supremum.
  rcases S.2.1 with ⟨i, hi⟩
  have hxS : x ∈ ⋃ j : (S : Finset ι), (O j : Set X) := by
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx i⟩
  simpa [finite_intersection_closed_union] using hxS

-- Internal bridge: the source-facing index category of finite intersection-closed subcovers maps
-- to the canonical open-cover index category of the derived cover `S ↦ U_S`.
private def finite_intersection_closed_subcover_to_cover_index
    (O : ι → TopologicalSpace.Opens (TopCat.of X)) :
    intersection_closed_subcover_index O ⥤
      TopologicalSpace.IsOpenCover.Index (fun S ↦ U[O, S]) where
  obj S := S
  map hST := InducedCategory.homMk (homOfLE (finite_intersection_closed_union_mono O hST.le))
  map_id S := by
    ext
    rfl
  map_comp hST hTU := by
    ext
    rfl

/-- The diagram sending a finite intersection-closed subcollection `S` to the group `π₁(U_S, x)`.
-/
abbrev finite_intersection_closed_subcover_fundamental_group_diagram
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i) :
    intersection_closed_subcover_index O ⥤ GrpCat :=
  finite_intersection_closed_subcover_to_cover_index O ⋙
    fundamental_group_cover_diagram
      (fun S ↦ U[O, S]) x
      (basepoint_mem_finite_intersection_closed_union O x hx)

/-- The canonical cocone from the groups `π₁(U_S, x)` to the ambient fundamental group
`π₁(X, x)`. -/
abbrev finite_intersection_closed_subcover_fundamental_group_cocone
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i) :
    Cocone (finite_intersection_closed_subcover_fundamental_group_diagram O x hx) :=
  (fundamental_group_cover_cocone
      (fun S ↦ U[O, S]) x
      (basepoint_mem_finite_intersection_closed_union O x hx)).whisker
    (finite_intersection_closed_subcover_to_cover_index O)

/-- Helper for Lemma 2.7.10: every ambient loop is contained in some finite stage union `U_S`. -/
private theorem loop_image_subset_finite_intersection_closed_union
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    {x : X} (γ : Path x x) :
    ∃ S : intersection_closed_subcover_index O,
      Set.range γ ⊆ (U[O, S] : Set X) := by
  obtain ⟨S, hS⟩ :=
    loop_image_subset_finite_union_of_intersection_closed_subcover O hO hinter γ
  refine ⟨S, ?_⟩
  intro y hy
  rcases Set.mem_iUnion₂.mp (hS hy) with ⟨i, hiS, hyi⟩
  exact (le_iSup (fun j : (S : Finset ι) ↦ O j) ⟨i, hiS⟩) hyi

/-- Helper for Lemma 2.7.10: every loop homotopy is contained in some finite stage union `U_S`.
-/
private theorem homotopy_image_subset_finite_intersection_closed_union
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    {x : X} {γ₀ γ₁ : Path x x} (H : Path.Homotopy γ₀ γ₁) :
    ∃ S : intersection_closed_subcover_index O,
      Set.range H ⊆ (U[O, S] : Set X) := by
  obtain ⟨S, hS⟩ :=
    homotopy_image_subset_finite_union_of_intersection_closed_subcover O hO hinter H
  refine ⟨S, ?_⟩
  intro y hy
  rcases Set.mem_iUnion₂.mp (hS hy) with ⟨i, hiS, hyi⟩
  exact (le_iSup (fun j : (S : Finset ι) ↦ O j) ⟨i, hiS⟩) hyi

/-- Helper for Lemma 2.7.10: a nonempty finite family of stage indices admits an
intersection-closed common refinement. -/
private theorem exists_common_refinement_stage
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (T : Finset ι) (hT : T.Nonempty) :
    ∃ S : intersection_closed_subcover_index O, T ⊆ (S : Finset ι) := by
  obtain ⟨S, hTS, hclosed⟩ := exists_intersection_closed_finset_superset O hinter T
  have hS_nonempty : S.Nonempty := by
    rcases hT with ⟨i, hi⟩
    exact ⟨i, hTS hi⟩
  exact ⟨⟨S, hS_nonempty, hclosed⟩, hTS⟩

/-- Helper for Lemma 2.7.10: the common basepoint of `X` determines the canonical basepoint of a
finite stage `U_S`. -/
private noncomputable abbrev stage_union_basepoint
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O) :
    U[O, S] :=
  ⟨x, basepoint_mem_finite_intersection_closed_union O x hx S⟩

/-- Helper for Lemma 2.7.10: enlarging a finite stage preserves the chosen common basepoint. -/
private theorem stage_union_inclusion_basepoint
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T) :
    (((toTopCat (TopCat.of X)).map
        (homOfLE (finite_intersection_closed_union_mono O hST))).hom)
        (stage_union_basepoint O x hx S) =
      stage_union_basepoint O x hx T := by
  -- Both subtype points have ambient coordinate `x`; only the membership proof changes.
  apply Subtype.ext
  rfl

/-- Helper for Lemma 2.7.10: enlarging a finite stage induces the canonical map on fundamental
groups. -/
private noncomputable abbrev stage_union_inclusion_hom
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T) :
    GrpCat.of (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S)) ⟶
      GrpCat.of (FundamentalGroup U[O, T] (stage_union_basepoint O x hx T)) :=
  GrpCat.ofHom <|
    FundamentalGroup.mapOfEq
      (((toTopCat (TopCat.of X)).map
          (homOfLE (finite_intersection_closed_union_mono O hST))).hom)
      (stage_union_inclusion_basepoint O x hx hST)

/-- Helper for Lemma 2.7.10: the ambient cocone leg at a stage is the canonical map induced by
including that stage union into `X`. -/
private theorem stage_union_to_ambient_basepoint
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O) :
    (inclusion' U[O, S]).hom (stage_union_basepoint O x hx S) = x := by
  -- The stage-union inclusion forgets the subtype proof and keeps the ambient point.
  rfl

/-- Helper for Lemma 2.7.10: the inclusion of a finite stage union into `X` gives the canonical
map on fundamental groups. -/
private noncomputable abbrev stage_union_to_ambient_hom
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O) :
    GrpCat.of (FundamentalGroup U[O, S] (stage_union_basepoint O x hx S)) ⟶
      GrpCat.of (FundamentalGroup X x) :=
  GrpCat.ofHom <|
    FundamentalGroup.mapOfEq (inclusion' U[O, S]).hom
      (stage_union_to_ambient_basepoint O x hx S)

/-- Helper for Lemma 2.7.10: the derived-stage diagram map is definitionally the canonical
fundamental-group map induced by stage enlargement. -/
private theorem finite_intersection_closed_subcover_fundamental_group_diagram_map_eq
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ⟶ T) :
    (finite_intersection_closed_subcover_fundamental_group_diagram O x hx).map hST =
      stage_union_inclusion_hom O x hx hST.le := by
  rfl

/-- Helper for Lemma 2.7.10: the whiskered ambient cocone leg is definitionally the canonical
stage-union inclusion map on fundamental groups. -/
private theorem finite_intersection_closed_subcover_fundamental_group_cocone_app_eq
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O) :
    (finite_intersection_closed_subcover_fundamental_group_cocone O x hx).ι.app S =
      stage_union_to_ambient_hom O x hx S := by
  rfl

/-- Helper for Lemma 2.7.10: the literal stage lift of an ambient loop starts at the chosen stage
basepoint. -/
private theorem ambient_loop_in_stage_source
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : Path x x)
    (hγ : Set.range γ ⊆ (U[O, S] : Set X)) :
    (⟨γ 0, hγ ⟨0, rfl⟩⟩ : U[O, S]) = stage_union_basepoint O x hx S := by
  -- At time `0`, the ambient loop is at `x`, so the lifted stage point is the chosen basepoint.
  apply Subtype.ext
  simpa using γ.source

/-- Helper for Lemma 2.7.10: the literal stage lift of an ambient loop ends at the chosen stage
basepoint. -/
private theorem ambient_loop_in_stage_target
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : Path x x)
    (hγ : Set.range γ ⊆ (U[O, S] : Set X)) :
    (⟨γ 1, hγ ⟨1, rfl⟩⟩ : U[O, S]) = stage_union_basepoint O x hx S := by
  -- At time `1`, the ambient loop again returns to `x`.
  apply Subtype.ext
  simpa using γ.target

/-- Helper for Lemma 2.7.10: an ambient loop whose image lies in a finite stage can be regarded as
a loop in that stage union. -/
private noncomputable def ambient_loop_in_stage
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : Path x x)
    (hγ : Set.range γ ⊆ (U[O, S] : Set X)) :
    Path (stage_union_basepoint O x hx S) (stage_union_basepoint O x hx S) :=
  { toContinuousMap :=
      { toFun := fun t ↦ ⟨γ t, hγ ⟨t, rfl⟩⟩
        continuous_toFun := Continuous.subtype_mk γ.continuous fun t ↦ hγ ⟨t, rfl⟩ }
    source' := ambient_loop_in_stage_source O x hx S γ hγ
    target' := ambient_loop_in_stage_target O x hx S γ hγ }

/-- Helper for Lemma 2.7.10: after enlarging a finite stage, the lifted ambient loop becomes the
same literal loop in the larger stage. -/
private theorem ambient_loop_in_stage_map_stage_union_inclusion
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T)
    (γ : Path x x)
    (hγS : Set.range γ ⊆ (U[O, S] : Set X))
    (hγT : Set.range γ ⊆ (U[O, T] : Set X)) :
    ((ambient_loop_in_stage O x hx S γ hγS).map
          (((toTopCat (TopCat.of X)).map
              (homOfLE (finite_intersection_closed_union_mono O hST))).hom.continuous)).cast
        (stage_union_inclusion_basepoint O x hx hST).symm
        (stage_union_inclusion_basepoint O x hx hST).symm =
      ambient_loop_in_stage O x hx T γ hγT := by
  -- Both paths have the same ambient coordinate at every time, so extensionality suffices.
  ext t
  apply Subtype.ext
  rfl

/-- Helper for Lemma 2.7.10: enlarging a finite stage sends the lifted ambient loop class to the
same ambient loop class viewed in the larger stage. -/
private theorem stage_union_inclusion_hom_apply_ambient_loop
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : intersection_closed_subcover_index O}
    (hST : S ≤ T)
    (γ : Path x x)
    (hγS : Set.range γ ⊆ (U[O, S] : Set X))
    (hγT : Set.range γ ⊆ (U[O, T] : Set X)) :
    (stage_union_inclusion_hom O x hx hST).hom
        (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧) =
      FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧ := by
  let f :
      C(U[O, S], U[O, T]) :=
    ((toTopCat (TopCat.of X)).map
      (homOfLE (finite_intersection_closed_union_mono O hST))).hom
  have hraw :=
    FundamentalGroup.mapOfEq_apply
      (f := f)
      (h := stage_union_inclusion_basepoint O x hx hST)
      (p := ambient_loop_in_stage O x hx S γ hγS)
  have hnorm :
      FundamentalGroup.fromPath
          ⟦((ambient_loop_in_stage O x hx S γ hγS).map f.continuous).cast
              (stage_union_inclusion_basepoint O x hx hST).symm
              (stage_union_inclusion_basepoint O x hx hST).symm⟧ =
        FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧ := by
    -- Normalize the mapped lifted loop to the literal lift in the larger stage.
    exact congrArg FundamentalGroup.fromPath <|
      congrArg Path.Homotopic.Quotient.mk <|
        ambient_loop_in_stage_map_stage_union_inclusion O x hx hST γ hγS hγT
  -- Apply `mapOfEq_apply`, then rewrite the mapped loop into the larger-stage lift.
  simpa [stage_union_inclusion_hom, f] using hraw.trans hnorm

/-- Helper for Lemma 2.7.10: evaluating one ambient loop in two finite stages gives the same
result after passing to a common refinement. -/
private theorem ambient_stage_value_eq_of_common_refinement
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (C : Cocone (finite_intersection_closed_subcover_fundamental_group_diagram O x hx))
    (γ : Path x x)
    {S T : intersection_closed_subcover_index O}
    (hγS : Set.range γ ⊆ (U[O, S] : Set X))
    (hγT : Set.range γ ⊆ (U[O, T] : Set X)) :
    (C.ι.app S).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧) =
      (C.ι.app T).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧) := by
  classical
  have hST_nonempty : (((S : Finset ι) ∪ (T : Finset ι)) : Finset ι).Nonempty := by
    rcases S.2.1 with ⟨i, hi⟩
    exact ⟨i, Finset.mem_union.mpr (Or.inl hi)⟩
  obtain ⟨R, hR⟩ :=
    exists_common_refinement_stage O hinter ((S : Finset ι) ∪ (T : Finset ι))
      hST_nonempty
  have hSR : S ≤ R := fun i hi ↦ hR (Finset.mem_union.mpr (Or.inl hi))
  have hTR : T ≤ R := fun i hi ↦ hR (Finset.mem_union.mpr (Or.inr hi))
  have hγR_fromS : Set.range γ ⊆ (U[O, R] : Set X) := by
    -- Enlarging the stage preserves containment of the loop image.
    intro y hy
    exact finite_intersection_closed_union_mono O hSR (hγS hy)
  have hγR_fromT : Set.range γ ⊆ (U[O, R] : Set X) := by
    -- The same enlargement argument applies from `T` to `R`.
    intro y hy
    exact finite_intersection_closed_union_mono O hTR (hγT hy)
  have hS_to_R :
      (C.ι.app S).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧) =
        (C.ι.app R).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx R γ hγR_fromS⟧) := by
    have hnat :=
      congrArg
        (fun k ↦
          k.hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧))
        (C.w (show S ⟶ R from homOfLE hSR))
    calc
      (C.ι.app S).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧) =
        (C.ι.app R).hom
          (((finite_intersection_closed_subcover_fundamental_group_diagram O x hx).map
              (show S ⟶ R from homOfLE hSR)).hom
            (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧)) := by
              simpa [GrpCat.comp_apply] using hnat.symm
      _ = (C.ι.app R).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx R γ hγR_fromS⟧) := by
            rw [finite_intersection_closed_subcover_fundamental_group_diagram_map_eq O x hx]
            exact congrArg (fun z ↦ (C.ι.app R).hom z) <|
              stage_union_inclusion_hom_apply_ambient_loop O x hx hSR γ hγS hγR_fromS
  have hT_to_R :
      (C.ι.app T).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧) =
        (C.ι.app R).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx R γ hγR_fromT⟧) := by
    have hnat :=
      congrArg
        (fun k ↦
          k.hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧))
        (C.w (show T ⟶ R from homOfLE hTR))
    calc
      (C.ι.app T).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧) =
        (C.ι.app R).hom
          (((finite_intersection_closed_subcover_fundamental_group_diagram O x hx).map
              (show T ⟶ R from homOfLE hTR)).hom
            (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧)) := by
              simpa [GrpCat.comp_apply] using hnat.symm
      _ = (C.ι.app R).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx R γ hγR_fromT⟧) := by
            rw [finite_intersection_closed_subcover_fundamental_group_diagram_map_eq O x hx]
            exact congrArg (fun z ↦ (C.ι.app R).hom z) <|
              stage_union_inclusion_hom_apply_ambient_loop O x hx hTR γ hγT hγR_fromT
  -- Both stage evaluations agree with the common-refinement evaluation.
  exact hS_to_R.trans hT_to_R.symm

/-- Helper for Lemma 2.7.10: if a loop homotopy stays inside one finite stage, then the source
loop already stays inside that stage. -/
private theorem path_range_subset_of_homotopy_source
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (S : intersection_closed_subcover_index O)
    {x : X} {γ₀ γ₁ : Path x x} (H : Path.Homotopy γ₀ γ₁)
    (hH : Set.range H ⊆ (U[O, S] : Set X)) :
    Set.range γ₀ ⊆ (U[O, S] : Set X) := by
  -- Evaluate the homotopy on the left edge to recover the source loop.
  intro y hy
  rcases hy with ⟨t, rfl⟩
  exact hH ⟨(0, t), by simpa using H.map_zero_left t⟩

/-- Helper for Lemma 2.7.10: if a loop homotopy stays inside one finite stage, then the target
loop already stays inside that stage. -/
private theorem path_range_subset_of_homotopy_target
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (S : intersection_closed_subcover_index O)
    {x : X} {γ₀ γ₁ : Path x x} (H : Path.Homotopy γ₀ γ₁)
    (hH : Set.range H ⊆ (U[O, S] : Set X)) :
    Set.range γ₁ ⊆ (U[O, S] : Set X) := by
  -- Evaluate the homotopy on the right edge to recover the target loop.
  intro y hy
  rcases hy with ⟨t, rfl⟩
  exact hH ⟨(1, t), by simpa using H.map_one_left t⟩

/-- Helper for Lemma 2.7.10: if two loops both stay inside one finite stage, then their
concatenation stays inside that stage as well. -/
private theorem path_trans_range_subset
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (S : intersection_closed_subcover_index O)
    {x : X} {γ δ : Path x x}
    (hδ : Set.range δ ⊆ (U[O, S] : Set X))
    (hγ : Set.range γ ⊆ (U[O, S] : Set X)) :
    Set.range (δ.trans γ) ⊆ (U[O, S] : Set X) := by
  -- Split the concatenated path at time `1/2` and use the corresponding factor.
  intro y hy
  rcases hy with ⟨t, rfl⟩
  rw [Path.trans_apply]
  split_ifs with ht
  · exact hδ ⟨⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, rfl⟩
  · exact hγ
      ⟨⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, rfl⟩

/-- Helper for Lemma 2.7.10: a loop homotopy that stays in one finite stage yields homotopic
stage lifts of its endpoints. -/
private theorem ambient_loop_in_stage_homotopic
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    {γ₀ γ₁ : Path x x} (H : Path.Homotopy γ₀ γ₁)
    (hH : Set.range H ⊆ (U[O, S] : Set X)) :
    (ambient_loop_in_stage O x hx S γ₀
        (path_range_subset_of_homotopy_source O S H hH)).Homotopic
      (ambient_loop_in_stage O x hx S γ₁
        (path_range_subset_of_homotopy_target O S H hH)) := by
  -- Lift the ambient homotopy pointwise into the stage subtype.
  refine ⟨
    { toContinuousMap :=
        { toFun := fun p ↦ ⟨H p, hH ⟨p, rfl⟩⟩
          continuous_toFun := Continuous.subtype_mk H.continuous fun p ↦ hH ⟨p, rfl⟩ }
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
  · intro t
    -- On the left edge we recover the lifted source loop.
    apply Subtype.ext
    simpa [ambient_loop_in_stage] using H.map_zero_left t
  · intro t
    -- On the right edge we recover the lifted target loop.
    apply Subtype.ext
    simpa [ambient_loop_in_stage] using H.map_one_left t
  · intro t y hy
    -- Along the top and bottom edges the homotopy stays at the common basepoint.
    apply Subtype.ext
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using H.prop t y hy

/-- Helper for Lemma 2.7.10: lifting an ambient concatenation into one finite stage agrees with
concatenating the two lifted stage loops. -/
private theorem ambient_loop_in_stage_trans
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ δ : Path x x)
    (hγ : Set.range γ ⊆ (U[O, S] : Set X))
    (hδ : Set.range δ ⊆ (U[O, S] : Set X)) :
    ambient_loop_in_stage O x hx S (δ.trans γ) (path_trans_range_subset O S hδ hγ) =
      (ambient_loop_in_stage O x hx S δ hδ).trans
        (ambient_loop_in_stage O x hx S γ hγ) := by
  -- Both paths have the same ambient coordinate at every time after expanding concatenation.
  ext t
  change
    (δ.trans γ) t =
      (((ambient_loop_in_stage O x hx S δ hδ).trans
          (ambient_loop_in_stage O x hx S γ hγ)) t).1
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs <;> rfl

/-- Helper for Lemma 2.7.10: once two ambient loops already live in one finite stage, the cocone
value of their product is computed inside that single stage. -/
private theorem ambient_stage_value_mul_of_common_stage
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (C : Cocone (finite_intersection_closed_subcover_fundamental_group_diagram O x hx))
    (S : intersection_closed_subcover_index O)
    (γ δ : Path x x)
    (hγ : Set.range γ ⊆ (U[O, S] : Set X))
    (hδ : Set.range δ ⊆ (U[O, S] : Set X)) :
    (C.ι.app S).hom
        (FundamentalGroup.fromPath
          ⟦ambient_loop_in_stage O x hx S (δ.trans γ) (path_trans_range_subset O S hδ hγ)⟧) =
      ((C.ι.app S).hom
          (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧)) *
        ((C.ι.app S).hom
          (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S δ hδ⟧)) := by
  have hloop :
      FundamentalGroup.fromPath
          ⟦ambient_loop_in_stage O x hx S (δ.trans γ) (path_trans_range_subset O S hδ hγ)⟧ =
        FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧ *
          FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S δ hδ⟧ := by
    -- Normalize the lifted concatenation to the product in the stage fundamental group.
    rw [ambient_loop_in_stage_trans O x hx S γ δ hγ hδ]
    change FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.trans
          ⟦ambient_loop_in_stage O x hx S δ hδ⟧
          ⟦ambient_loop_in_stage O x hx S γ hγ⟧) =
      _
    change FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧ *
        FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S δ hδ⟧ =
      _
    rfl
  -- After rewriting the source loop class, multiplicativity of the cocone leg finishes.
  exact (congrArg (fun q ↦ (C.ι.app S).hom q) hloop).trans (MonoidHom.map_mul _ _ _)

/-- Helper for Lemma 2.7.10: the ambient image of a loop in a finite stage still lies in that
same stage union. -/
private theorem stage_loop_range_subset
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : Path (stage_union_basepoint O x hx S) (stage_union_basepoint O x hx S)) :
    Set.range (γ.map continuous_subtype_val) ⊆ (U[O, S] : Set X) := by
  -- Every point of the mapped loop comes from the stage subtype itself.
  intro y hy
  rcases hy with ⟨t, rfl⟩
  exact (γ t).2

/-- Helper for Lemma 2.7.10: lifting the ambient image of a literal stage loop back into the same
stage recovers the original stage loop. -/
private theorem ambient_loop_in_stage_of_stage_loop
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : Path (stage_union_basepoint O x hx S) (stage_union_basepoint O x hx S)) :
    ambient_loop_in_stage O x hx S
        (γ.map continuous_subtype_val)
        (stage_loop_range_subset O x hx S γ) =
      γ := by
  -- Both loops have the same stage-valued coordinate at every time.
  ext t
  rfl

/-- Helper for Lemma 2.7.10: the finite-stage inclusion sends a literal stage loop class to the
class of the same loop viewed in `X`. -/
private theorem stage_union_to_ambient_hom_apply_stage_loop
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : Path (stage_union_basepoint O x hx S) (stage_union_basepoint O x hx S)) :
    (stage_union_to_ambient_hom O x hx S).hom (FundamentalGroup.fromPath ⟦γ⟧) =
      FundamentalGroup.fromPath ⟦γ.map continuous_subtype_val⟧ := by
  have hraw :=
    FundamentalGroup.mapOfEq_apply
      (f := (inclusion' U[O, S]).hom)
      (h := stage_union_to_ambient_basepoint O x hx S)
      (p := γ)
  have hnorm :
      FundamentalGroup.fromPath
          ⟦((γ.map (inclusion' U[O, S]).hom.continuous).cast
              (stage_union_to_ambient_basepoint O x hx S).symm
              (stage_union_to_ambient_basepoint O x hx S).symm)⟧ =
        FundamentalGroup.fromPath ⟦γ.map continuous_subtype_val⟧ := by
    -- Mapping the literal stage loop to `X` just forgets the subtype proof.
    exact congrArg FundamentalGroup.fromPath <|
      congrArg Path.Homotopic.Quotient.mk <| by
        ext t
        rfl
  -- Apply `mapOfEq_apply`, then normalize the mapped stage loop.
  simpa [stage_union_to_ambient_hom] using hraw.trans hnorm

/-- Helper for Lemma 2.7.10: the finite-stage inclusion sends the lifted ambient loop class back
to the original ambient loop class. -/
private theorem stage_union_to_ambient_hom_apply_ambient_loop
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : intersection_closed_subcover_index O)
    (γ : Path x x)
    (hγ : Set.range γ ⊆ (U[O, S] : Set X)) :
    (stage_union_to_ambient_hom O x hx S).hom
        (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧) =
      FundamentalGroup.fromPath ⟦γ⟧ := by
  have hraw :=
    FundamentalGroup.mapOfEq_apply
      (f := (inclusion' U[O, S]).hom)
      (h := stage_union_to_ambient_basepoint O x hx S)
      (p := ambient_loop_in_stage O x hx S γ hγ)
  have hnorm :
      FundamentalGroup.fromPath
          ⟦(((ambient_loop_in_stage O x hx S γ hγ).map
                (inclusion' U[O, S]).hom.continuous).cast
              (stage_union_to_ambient_basepoint O x hx S).symm
              (stage_union_to_ambient_basepoint O x hx S).symm)⟧ =
        FundamentalGroup.fromPath ⟦γ⟧ := by
    -- Forgetting the stage subtype recovers the original ambient loop.
    exact congrArg FundamentalGroup.fromPath <|
      congrArg Path.Homotopic.Quotient.mk <| by
        ext t
        rfl
  -- Apply `mapOfEq_apply`, then collapse back to the original ambient loop.
  simpa [stage_union_to_ambient_hom] using hraw.trans hnorm

-- Internal universal-property formulation used to build the public `IsColimit` datum via the
-- canonical `IsColimit.ofExistsUnique` owner API.
private theorem finite_intersection_closed_subcover_fundamental_group_existsUnique
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O) :
    ∀ S : Cocone (finite_intersection_closed_subcover_fundamental_group_diagram O x hx),
      ∃! d :
        (finite_intersection_closed_subcover_fundamental_group_cocone O x hx).pt ⟶ S.pt,
        ∀ T,
          (finite_intersection_closed_subcover_fundamental_group_cocone O x hx).ι.app T ≫ d =
            S.ι.app T := by
  intro C
  classical
  let chosen_stage : Path x x → intersection_closed_subcover_index O := fun γ ↦
    Classical.choose (loop_image_subset_finite_intersection_closed_union O hO hinter γ)
  let chosen_stage_mem : ∀ γ : Path x x, Set.range γ ⊆ (U[O, chosen_stage γ] : Set X) := fun γ ↦
    Classical.choose_spec (loop_image_subset_finite_intersection_closed_union O hO hinter γ)
  let stage_value :
      (γ : Path x x) →
        (T : intersection_closed_subcover_index O) →
          Set.range γ ⊆ (U[O, T] : Set X) → C.pt := fun γ T hγ ↦
    (C.ι.app T).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγ⟧)
  let raw_value : Path x x → C.pt := fun γ ↦
    stage_value γ (chosen_stage γ) (chosen_stage_mem γ)
  have raw_value_spec :
      ∀ (γ : Path x x) (T : intersection_closed_subcover_index O)
        (hγ : Set.range γ ⊆ (U[O, T] : Set X)),
        raw_value γ = stage_value γ T hγ := by
    -- The common-refinement comparison makes the chosen stage irrelevant.
    intro γ T hγ
    exact ambient_stage_value_eq_of_common_refinement O x hx hinter C γ (chosen_stage_mem γ) hγ
  have raw_value_respects :
      ∀ {γ₀ γ₁ : Path x x}, γ₀.Homotopic γ₁ → raw_value γ₀ = raw_value γ₁ := by
    intro γ₀ γ₁ hγ
    rcases hγ with ⟨H⟩
    obtain ⟨T, hH⟩ :=
      homotopy_image_subset_finite_intersection_closed_union O hO hinter H
    have hγ₀ : Set.range γ₀ ⊆ (U[O, T] : Set X) :=
      path_range_subset_of_homotopy_source O T H hH
    have hγ₁ : Set.range γ₁ ⊆ (U[O, T] : Set X) :=
      path_range_subset_of_homotopy_target O T H hH
    have hquot :
        FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ₀ hγ₀⟧ =
          FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ₁ hγ₁⟧ := by
      -- Lift the ambient homotopy to the chosen common stage and descend it to the quotient.
      apply congrArg FundamentalGroup.fromPath
      exact Quotient.sound (ambient_loop_in_stage_homotopic O x hx T H hH)
    calc
      raw_value γ₀ = stage_value γ₀ T hγ₀ := raw_value_spec γ₀ T hγ₀
      _ = stage_value γ₁ T hγ₁ := by
            simpa [stage_value] using congrArg (fun q ↦ (C.ι.app T).hom q) hquot
      _ = raw_value γ₁ := (raw_value_spec γ₁ T hγ₁).symm
  let dMonoid : FundamentalGroup X x →* C.pt :=
    { toFun := fun q ↦ Quotient.liftOn q raw_value fun _ _ h ↦ raw_value_respects h
      map_one' := by
        -- Evaluate the ambient descendant on the constant loop inside any stage containing it.
        obtain ⟨T, hT⟩ :=
          loop_image_subset_finite_intersection_closed_union O hO hinter (Path.refl x)
        have href :
            ambient_loop_in_stage O x hx T (Path.refl x) hT =
              Path.refl (stage_union_basepoint O x hx T) := by
          ext t
          rfl
        calc
          Quotient.liftOn (1 : FundamentalGroup X x) raw_value
              (fun _ _ h ↦ raw_value_respects h) =
            raw_value (Path.refl x) := by
                rfl
          _ = stage_value (Path.refl x) T hT := raw_value_spec (Path.refl x) T hT
          _ = 1 := by
                change
                  (C.ι.app T).hom
                      (FundamentalGroup.fromPath ⟦Path.refl (stage_union_basepoint O x hx T)⟧) =
                    1
                change (C.ι.app T).hom 1 = 1
                simpa using (C.ι.app T).hom.map_one
      map_mul' := by
        intro a b
        induction a using Path.Homotopic.Quotient.ind with
        | mk γ =>
            induction b using Path.Homotopic.Quotient.ind with
            | mk δ =>
                -- Put both representative loops in one common stage and compute there.
                obtain ⟨Sγ, hγ⟩ :=
                  loop_image_subset_finite_intersection_closed_union O hO hinter γ
                obtain ⟨Sδ, hδ⟩ :=
                  loop_image_subset_finite_intersection_closed_union O hO hinter δ
                have hS_nonempty : (((Sγ : Finset ι) ∪ (Sδ : Finset ι)) : Finset ι).Nonempty := by
                  rcases Sγ.2.1 with ⟨i, hi⟩
                  exact ⟨i, Finset.mem_union.mpr (Or.inl hi)⟩
                obtain ⟨R, hR⟩ :=
                  exists_common_refinement_stage O hinter
                    ((Sγ : Finset ι) ∪ (Sδ : Finset ι)) hS_nonempty
                have hγR : Set.range γ ⊆ (U[O, R] : Set X) := by
                  intro y hy
                  exact finite_intersection_closed_union_mono O
                    (fun i hi ↦ hR (Finset.mem_union.mpr (Or.inl hi))) (hγ hy)
                have hδR : Set.range δ ⊆ (U[O, R] : Set X) := by
                  intro y hy
                  exact finite_intersection_closed_union_mono O
                    (fun i hi ↦ hR (Finset.mem_union.mpr (Or.inr hi))) (hδ hy)
                change raw_value (δ.trans γ) = raw_value γ * raw_value δ
                calc
                  raw_value (δ.trans γ) =
                      stage_value (δ.trans γ) R (path_trans_range_subset O R hδR hγR) :=
                    raw_value_spec (δ.trans γ) R (path_trans_range_subset O R hδR hγR)
                  _ = stage_value γ R hγR * stage_value δ R hδR := by
                        simpa [stage_value] using
                          ambient_stage_value_mul_of_common_stage O x hx C R γ δ hγR hδR
                  _ = raw_value γ * raw_value δ := by
                        rw [raw_value_spec γ R hγR, raw_value_spec δ R hδR] }
  let d :
      (finite_intersection_closed_subcover_fundamental_group_cocone O x hx).pt ⟶ C.pt :=
    GrpCat.ofHom dMonoid
  refine ⟨d, ?_, ?_⟩
  · intro T
    ext g
    induction g using Path.Homotopic.Quotient.ind with
    | mk γ =>
        calc
          dMonoid
              (((finite_intersection_closed_subcover_fundamental_group_cocone O x hx).ι.app T).hom
                (FundamentalGroup.fromPath ⟦γ⟧)) =
            dMonoid (FundamentalGroup.fromPath ⟦γ.map continuous_subtype_val⟧) := by
              rw [finite_intersection_closed_subcover_fundamental_group_cocone_app_eq O x hx]
              exact congrArg dMonoid (stage_union_to_ambient_hom_apply_stage_loop O x hx T γ)
          _ = stage_value (γ.map continuous_subtype_val) T (stage_loop_range_subset O x hx T γ) := by
                exact raw_value_spec (γ.map continuous_subtype_val) T
                  (stage_loop_range_subset O x hx T γ)
          _ = (C.ι.app T).hom (FundamentalGroup.fromPath ⟦γ⟧) := by
                simpa [stage_value] using congrArg
                  (fun q ↦ (C.ι.app T).hom (FundamentalGroup.fromPath q))
                  (congrArg Path.Homotopic.Quotient.mk <|
                    ambient_loop_in_stage_of_stage_loop O x hx T γ)
  · intro ψ hψ
    ext g
    induction g using Path.Homotopic.Quotient.ind with
    | mk γ =>
        obtain ⟨T, hγ⟩ :=
          loop_image_subset_finite_intersection_closed_union O hO hinter γ
        let loopClass :
            FundamentalGroup U[O, T] (stage_union_basepoint O x hx T) :=
          FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγ⟧
        have hrestrict_apply :
            (((finite_intersection_closed_subcover_fundamental_group_cocone O x hx).ι.app T) ≫ ψ).hom
                loopClass =
              (C.ι.app T).hom loopClass := by
          -- Apply the assumed factorization equality at the stage containing `γ`.
          simpa [loopClass, GrpCat.comp_apply] using congrArg
            (fun k ↦ k.hom loopClass) (hψ T)
        have hraw :
            (C.ι.app T).hom loopClass =
              dMonoid (FundamentalGroup.fromPath ⟦γ⟧) := by
          -- The definition of `dMonoid` evaluates an ambient loop by any containing stage.
          simpa [loopClass, stage_value, raw_value, dMonoid] using (raw_value_spec γ T hγ).symm
        have hleft :
            ψ.hom (FundamentalGroup.fromPath ⟦γ⟧) =
              (((finite_intersection_closed_subcover_fundamental_group_cocone O x hx).ι.app T) ≫ ψ).hom
                loopClass := by
          rw [finite_intersection_closed_subcover_fundamental_group_cocone_app_eq O x hx]
          simpa [loopClass, GrpCat.comp_apply] using
            (congrArg ψ.hom
              (stage_union_to_ambient_hom_apply_ambient_loop O x hx T γ hγ)).symm
        exact hleft.trans (hrestrict_apply.trans hraw)

/-- Lemma 2.7.10: the colimit of the groups `π₁(U_S, x)` over nonempty finite
intersection-closed subcollections `S` of the cover is the ambient fundamental group
`π₁(X, x)`. -/
-- Proof sketch: by ProofStep 2.7.9, every loop in `X` and every homotopy between loops is
-- contained in some finite union `U_S` coming from a finite subcollection closed under nonempty
-- finite intersections. This lets one define the universal map out of `π₁(X, x)` by choosing a
-- sufficiently large `S` for each loop class, while the homotopy statement guarantees
-- well-definedness and compatibility with the transition maps, giving the colimit universal
-- property.
def fundamental_group_is_colimit_of_finite_intersection_closed_subcover_unions
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O) :
    IsColimit (finite_intersection_closed_subcover_fundamental_group_cocone O x hx) :=
  IsColimit.ofExistsUnique
    (finite_intersection_closed_subcover_fundamental_group_existsUnique O hO x hx hinter)

/-- The colimit cocone from the finite-intersection-closed van Kampen lemma induces the canonical
comparison morphism from `π₁(X, x)` to any other cocone over the finite-subcover diagram, and this
morphism is compatible with the cocone legs. -/
-- Proof sketch: apply the universal property packaged by
-- `fundamental_group_is_colimit_of_finite_intersection_closed_subcover_unions`; its `fac` field
-- gives the stated compatibility for each finite intersection-closed subcover.
theorem fundamental_group_is_colimit_of_finite_intersection_closed_subcover_unions_desc_fac
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (finite_intersection_closed_subcover_fundamental_group_diagram O x hx))
    (T : intersection_closed_subcover_index O) :
    (finite_intersection_closed_subcover_fundamental_group_cocone O x hx).ι.app T ≫
        (fundamental_group_is_colimit_of_finite_intersection_closed_subcover_unions
          O hO x hx hinter).desc S =
      S.ι.app T := by
  simpa using
    (fundamental_group_is_colimit_of_finite_intersection_closed_subcover_unions
      O hO x hx hinter).fac S T

/-! ### Lemma_2_7_11 (from Chap02) -/
universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : Type u₁} [Category.{v₁} C]
variable {F : C ⥤ Cat}
variable [∀ S : C, HasColimitsOfShape (F.obj S) GrpCat]
variable [HasColimitsOfShape C GrpCat]

/- Lemma 2.7.11 is the `GrpCat` specialization of the canonical Grothendieck-construction
comparison isomorphism: taking the fiberwise colimit first and then the colimit over the base is
canonically isomorphic to taking the single colimit over all pairs `(S, U)`. -/
#check
  (fun fundamentalGroupDiagram : Grothendieck F ⥤ GrpCat ↦
    (colimitFiberwiseColimitIso fundamentalGroupDiagram :
      colimit (fiberwiseColimit fundamentalGroupDiagram) ≅
        colimit fundamentalGroupDiagram))

/- The cocone leg for a pair `(S, U)` factors through the iterated-colimit comparison by the
canonical component formula. -/
#check
  (fun (fundamentalGroupDiagram : Grothendieck F ⥤ GrpCat) (S : C) (U : F.obj S) ↦
    (ι_colimitFiberwiseColimitIso_hom fundamentalGroupDiagram S U :
      colimit.ι (Grothendieck.ι F S ⋙ fundamentalGroupDiagram) U ≫
          colimit.ι (fiberwiseColimit fundamentalGroupDiagram) S ≫
          (colimitFiberwiseColimitIso fundamentalGroupDiagram).hom =
        colimit.ι fundamentalGroupDiagram ⟨S, U⟩))
