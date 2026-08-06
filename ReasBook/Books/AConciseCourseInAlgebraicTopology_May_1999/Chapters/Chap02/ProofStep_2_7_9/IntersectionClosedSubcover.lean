module

public import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.FundamentalGroupoidOpenCover

universe u v

open TopologicalSpace.IsOpenCover
open TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

/-- A finite subcollection of an indexed open cover is closed under nonempty finite intersections
if every nonempty finite subfamily has its intersection represented by another member of that same
finite subcollection. -/
public def Finset.IsClosedUnderNonemptyFiniteIntersections
    (S : Finset ι) (O : ι → TopologicalSpace.Opens X) : Prop :=
  ∀ t : Finset ι, ∀ ht : t.Nonempty, (t : Set ι) ⊆ S → ∃ i ∈ S, t.inf' ht O = O i

namespace Finset.IsClosedUnderNonemptyFiniteIntersections

/-- Unpack the source-facing finite-stage intersection-closure predicate into its defining
universal property. -/
public theorem iff
    {S : Finset ι} {O : ι → TopologicalSpace.Opens X} :
    S.IsClosedUnderNonemptyFiniteIntersections O ↔
      ∀ t : Finset ι, ∀ ht : t.Nonempty, (t : Set ι) ⊆ S → ∃ i ∈ S, t.inf' ht O = O i :=
  Iff.rfl

end Finset.IsClosedUnderNonemptyFiniteIntersections

/-- The source-facing owner for a nonempty finite subcollection of a cover that is itself closed
under nonempty finite intersections. -/
public structure IntersectionClosedSubcover (O : ι → TopologicalSpace.Opens X) where
  carrier : Finset ι
  nonempty : carrier.Nonempty
  closedUnderNonemptyFiniteIntersections :
    carrier.IsClosedUnderNonemptyFiniteIntersections O

namespace IntersectionClosedSubcover

variable (O : ι → TopologicalSpace.Opens X)

@[ext] public theorem ext
    {O : ι → TopologicalSpace.Opens X}
    {S T : IntersectionClosedSubcover O} (h : S.carrier = T.carrier) :
    S = T := by
  cases S
  cases T
  cases h
  simp

attribute [coe] IntersectionClosedSubcover.carrier

public instance : Membership ι (IntersectionClosedSubcover O) where
  mem S i := i ∈ S.carrier

public instance : CoeSort (IntersectionClosedSubcover O) (Type v) where
  coe S := { i // i ∈ S }

public noncomputable instance instFintype (S : IntersectionClosedSubcover O) : Fintype S :=
  Fintype.ofFinset S.carrier fun i ↦ by
    exact Iff.rfl

public noncomputable instance instFinite (S : IntersectionClosedSubcover O) : Finite S :=
  Finite.of_fintype S

public instance : PartialOrder (IntersectionClosedSubcover O) where
  le S T := ∀ ⦃i : ι⦄, i ∈ S → i ∈ T
  le_refl S := by
    intro i hi
    exact hi
  le_trans S T U hST hTU := by
    intro i hi
    exact hTU (hST hi)
  le_antisymm S T hST hTS := by
    apply ext
    exact Finset.ext fun i ↦
      ⟨fun hi ↦ show i ∈ T.carrier from hST hi, fun hi ↦ show i ∈ S.carrier from hTS hi⟩

variable {O}

/-- A finite intersection-closed subcover index is closed under nonempty finite intersections by
construction. -/
public theorem isClosedUnderNonemptyFiniteIntersections
    {O : ι → TopologicalSpace.Opens X} (S : IntersectionClosedSubcover O) :
    S.carrier.IsClosedUnderNonemptyFiniteIntersections O :=
  S.closedUnderNonemptyFiniteIntersections

@[simp] public theorem mem_carrier
    {O : ι → TopologicalSpace.Opens X}
    {S : IntersectionClosedSubcover O} {i : ι} :
    i ∈ S.carrier ↔ i ∈ S := by
  change i ∈ S ↔ i ∈ S
  exact Iff.rfl

/-- The resulting intersection-closed enlargement is nonempty. -/
public theorem nonempty'
    {O : ι → TopologicalSpace.Opens X}
    (S : IntersectionClosedSubcover O) :
    S.carrier.Nonempty :=
  S.nonempty

end IntersectionClosedSubcover

/-- The open subset `U[O, S]` obtained by taking the union of the members of a finite
intersection-closed subcover `S`. -/
public abbrev finite_intersection_closed_union
    (O : ι → TopologicalSpace.Opens X)
    (S : IntersectionClosedSubcover O) : TopologicalSpace.Opens X :=
  ⨆ i : S, O i

scoped[IntersectionClosedSubcover] notation "U[" O ", " S "]" =>
  finite_intersection_closed_union O S

open scoped IntersectionClosedSubcover

/-- A point lies in `U[O, S]` exactly when it lies in one member indexed by the finite stage `S`. -/
@[simp] public theorem mem_finite_intersection_closed_union
    {O : ι → TopologicalSpace.Opens X}
    {S : IntersectionClosedSubcover O} {x : X} :
    x ∈ U[O, S] ↔ ∃ i : S, x ∈ O i := by
  simp [finite_intersection_closed_union]

/-- Each member of a finite intersection-closed stage is contained in the corresponding stage
union. -/
public theorem le_finite_intersection_closed_union
    (O : ι → TopologicalSpace.Opens X)
    (S : IntersectionClosedSubcover O) (i : S) :
    O i ≤ U[O, S] := by
  exact le_iSup (fun j : S ↦ O j) i

/-- Enlarging a finite intersection-closed subcover enlarges the corresponding stage union. -/
public theorem finite_intersection_closed_union_mono
    (O : ι → TopologicalSpace.Opens X)
    {S T : IntersectionClosedSubcover O} (hST : S ≤ T) :
    U[O, S] ≤ U[O, T] := by
  rw [finite_intersection_closed_union, finite_intersection_closed_union]
  refine iSup_le fun i ↦ ?_
  exact le_iSup (fun j : T ↦ O j) ⟨i.1, show i.1 ∈ T from hST i.2⟩

/-- A point lying in every member of the cover lies in every finite stage union `U[O, S]`. -/
public theorem basepoint_mem_finite_intersection_closed_union
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : IntersectionClosedSubcover O) :
    x ∈ U[O, S] := by
  rcases S.nonempty with ⟨i, hi⟩
  have hxS : x ∈ ⋃ j : S, (O j : Set X) := by
    exact Set.mem_iUnion.mpr ⟨⟨i, show i ∈ S from hi⟩, hx i⟩
  simpa [finite_intersection_closed_union] using hxS

/-- The image of a continuous map from a compact parameter space lies in a finite union of
members of the ambient open cover. -/
public theorem compact_image_subset_finite_union_of_cover
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (O : ι → TopologicalSpace.Opens X)
    (hO : TopologicalSpace.IsOpenCover O)
    (f : C(K, X)) :
    ∃ T : Finset ι, Set.range f ⊆ ⋃ i ∈ T, (O i : Set X) := by
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

/-- Membership in the finite infimum of open subsets is equivalent to membership in each
constituent open. -/
private theorem mem_finset_inf_opens
    {κ : Type*} (s : Finset κ) (U : κ → TopologicalSpace.Opens X) (x : X) :
    x ∈ s.inf U ↔ ∀ i ∈ s, x ∈ U i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi hs =>
      simp [Finset.inf_insert, hs]

/-- A nonempty finite family of cover members can be enlarged to a nonempty finite family that is
internally closed under nonempty finite intersections. -/
public theorem exists_nonempty_intersection_closed_finset_superset
    (O : ι → TopologicalSpace.Opens X)
    (hinter : ClosedUnderNonemptyFiniteIntersections O)
    (T : Finset ι) (hT : T.Nonempty) :
    ∃ S : IntersectionClosedSubcover O, T ⊆ S.carrier := by
  classical
  let nonemptySubsets : Finset { t : Finset ι // t ∈ T.powerset.filter Finset.Nonempty } :=
    (T.powerset.filter Finset.Nonempty).attach
  let representative :
      { t : Finset ι // t ∈ T.powerset.filter Finset.Nonempty } → ι := fun t ↦
    Classical.choose (exists_eq_inf_finset hinter t.1 ((Finset.mem_filter.mp t.2).2))
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
      · change ({j} : Finset ι).inf' (Finset.singleton_nonempty j) O = O j
        exact @Finset.inf'_singleton (TopologicalSpace.Opens X) ι _ O j
    · rcases Finset.mem_image.mp hjimage with ⟨t, -, rfl⟩
      refine ⟨t.1, (Finset.mem_filter.mp t.2).2, ?_, ?_⟩
      · exact Finset.mem_powerset.mp (Finset.mem_filter.mp t.2).1
      · simpa [representative] using
          Classical.choose_spec
            (exists_eq_inf_finset hinter t.1 ((Finset.mem_filter.mp t.2).2))
  have finite_inf_eq_biUnion_carrier_inf :
      ∀ (u : Finset ι) (hu : u.Nonempty) (carrier : ι → Finset ι)
        (hcarrier_nonempty : ∀ j ∈ u, (carrier j).Nonempty)
        (hcarrier_eq : ∀ j (hj : j ∈ u), (carrier j).inf' (hcarrier_nonempty j hj) O = O j)
        (hcarrier_union_nonempty : (u.biUnion carrier).Nonempty),
        u.inf' hu O =
          (u.biUnion carrier).inf' hcarrier_union_nonempty O := by
    intro u hu carrier hcarrier_nonempty hcarrier_eq hcarrier_union_nonempty
    ext x
    rw [Finset.inf'_eq_inf, Finset.inf'_eq_inf]
    constructor
    · intro hx
      have hxu : ∀ j ∈ u, x ∈ O j := (mem_finset_inf_opens u O x).mp hx
      have hxcarrier : ∀ j ∈ u, ∀ k ∈ carrier j, x ∈ O k := by
        intro j hj k hk
        have hxj : x ∈ O j := hxu j hj
        rw [← hcarrier_eq j hj] at hxj
        rw [Finset.inf'_eq_inf] at hxj
        exact (mem_finset_inf_opens (carrier j) O x).mp hxj k hk
      exact (mem_finset_inf_opens (u.biUnion carrier) O x).mpr fun k hk ↦ by
        rcases Finset.mem_biUnion.mp hk with ⟨j, hj, hk'⟩
        exact hxcarrier j hj k hk'
    · intro hx
      have hxb : ∀ k ∈ u.biUnion carrier, x ∈ O k :=
        (mem_finset_inf_opens (u.biUnion carrier) O x).mp hx
      have hxu : ∀ j ∈ u, x ∈ O j := by
        intro j hj
        rw [← hcarrier_eq j hj, Finset.inf'_eq_inf]
        exact (mem_finset_inf_opens (carrier j) O x).mpr fun k hk ↦
          hxb k (Finset.mem_biUnion.mpr ⟨j, hj, hk⟩)
      exact (mem_finset_inf_opens u O x).mpr hxu
  have closedCarrier_closed :
      closedCarrier.IsClosedUnderNonemptyFiniteIntersections O := by
    intro u hu hu_closed
    have hmembers :
        ∀ j ∈ u, ∃ t : Finset ι, ∃ ht : t.Nonempty, (t : Set ι) ⊆ T ∧ t.inf' ht O = O j := by
      intro j hj
      exact member_has_original_carrier j (hu_closed hj)
    choose carrier hcarrier_nonempty hcarrier_subset hcarrier_eq using hmembers
    let expanded : ι → Finset ι := fun j ↦ if hj : j ∈ u then carrier j hj else ∅
    have hexpanded_subset : u.biUnion expanded ⊆ T := by
      intro k hk
      rcases Finset.mem_biUnion.mp hk with ⟨j, hj, hk'⟩
      have hk'' : k ∈ carrier j hj := by
        simpa [expanded, hj] using hk'
      exact hcarrier_subset j hj hk''
    have hexpanded_nonempty : (u.biUnion expanded).Nonempty := by
      rcases hu with ⟨j, hj⟩
      rcases hcarrier_nonempty j hj with ⟨k, hk⟩
      refine ⟨k, Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩⟩
      simpa [expanded, hj] using hk
    have hexpanded_each_nonempty : ∀ j ∈ u, (expanded j).Nonempty := by
      intro j hj
      simpa [expanded, hj] using hcarrier_nonempty j hj
    have hexpanded_eq :
        ∀ j (hj : j ∈ u), (expanded j).inf' (hexpanded_each_nonempty j hj) O = O j := by
      intro j hj
      simpa [expanded, hj] using hcarrier_eq j hj
    have hinf :
        u.inf' hu O = (u.biUnion expanded).inf' hexpanded_nonempty O :=
      finite_inf_eq_biUnion_carrier_inf u hu expanded hexpanded_each_nonempty hexpanded_eq
        hexpanded_nonempty
    have hsubset_closed : (u.biUnion expanded : Set ι) ⊆ closedCarrier := by
      intro k hk
      exact Finset.mem_union.mpr (Or.inl (hexpanded_subset hk))
    let expandedSubset : { t : Finset ι // t ∈ T.powerset.filter Finset.Nonempty } :=
      ⟨u.biUnion expanded, by
        refine Finset.mem_filter.mpr ?_
        exact ⟨Finset.mem_powerset.mpr hexpanded_subset, hexpanded_nonempty⟩⟩
    refine ⟨representative expandedSubset, ?_, ?_⟩
    · exact Finset.mem_union.mpr <|
        Or.inr <| Finset.mem_image.mpr ⟨expandedSubset, by simp [nonemptySubsets]⟩
    · have hEq :
          (u.biUnion expanded).inf' hexpanded_nonempty O = O (representative expandedSubset) := by
          simpa [representative, expandedSubset] using
            Classical.choose_spec <|
              exists_eq_inf_finset hinter expandedSubset.1
                ((Finset.mem_filter.mp expandedSubset.2).2)
      exact hinf.trans hEq
  refine ⟨
    { carrier := closedCarrier
      nonempty := closedCarrier_nonempty
      closedUnderNonemptyFiniteIntersections := closedCarrier_closed },
    ?_⟩
  intro i hi
  exact Finset.mem_union.mpr (Or.inl hi)

/-- From any finite subcover family, one obtains a nonempty finite intersection-closed stage
covering the same compact image. -/
public theorem compact_image_subset_finite_intersection_closed_union
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (k₀ : K)
    (O : ι → TopologicalSpace.Opens X)
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : ClosedUnderNonemptyFiniteIntersections O)
    (f : C(K, X)) :
    ∃ S : IntersectionClosedSubcover O,
      Set.range f ⊆ U[O, S] := by
  obtain ⟨T, hT⟩ := compact_image_subset_finite_union_of_cover O hO f
  have hTnonempty : T.Nonempty := by
    have hk : f k₀ ∈ Set.range f := ⟨k₀, rfl⟩
    have hkT := hT hk
    rw [Set.mem_iUnion] at hkT
    rcases hkT with ⟨i, hkT⟩
    rw [Set.mem_iUnion] at hkT
    exact ⟨i, hkT.1⟩
  obtain ⟨S, hTS⟩ := exists_nonempty_intersection_closed_finset_superset O hinter T hTnonempty
  refine ⟨S, ?_⟩
  intro x hx
  have hxT := hT hx
  rw [Set.mem_iUnion] at hxT
  rcases hxT with ⟨i, hxT⟩
  rw [Set.mem_iUnion] at hxT
  rcases hxT with ⟨hiT, hxT⟩
  have hiS : i ∈ S.carrier := hTS hiT
  exact mem_finite_intersection_closed_union.mpr ⟨⟨i, hiS⟩, hxT⟩
