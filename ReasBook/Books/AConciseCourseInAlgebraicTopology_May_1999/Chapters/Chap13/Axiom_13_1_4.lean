import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.PairHomologyTheory

open CategoryTheory
open SpacePair

universe u

-- Semantic recall: Chapter 10 already fixes the excisive-triad owner as `Triad.IsExcisive`,
-- while `lean_leansearch` surfaced closure/interior complement lemmas for the later bridge to
-- `PairHomologyTheory.excision`. This file therefore keeps the genuine relative pair map
-- `(A, A ∩ B) ⟶ (X, B)` and uses the established triad-level hypothesis.

/-- The triad `(X; A, B)` attached to the excision map `(A, A ∩ B) ⟶ (X, B)`. -/
abbrev pairHomologyExcisionTriad {X : Type u} [TopologicalSpace X] (A B : Set X) : Triad X where
  subspaceA := A
  subspaceB := B

/-- The target pair `(X, B)` in the excision axiom. -/
abbrev pairHomologyExcisionTargetPair {X : Type u} [TopologicalSpace X] (B : Set X) : SpacePair
    where
  space := TopCat.of X
  subspace := B

/-- The genuine source pair `(A, A ∩ B)` in the excision axiom. -/
abbrev pairHomologyExcisionSourcePair {X : Type u} [TopologicalSpace X] (A B : Set X) :
    SpacePair where
  space := TopCat.of A
  subspace := { a : A | (a : X) ∈ B }

/-- The inclusion `(A, A ∩ B) ⟶ (X, B)` appearing in the excision axiom. -/
def pairHomologyExcisionInclusion {X : Type u} [TopologicalSpace X] (A B : Set X) :
    pairHomologyExcisionSourcePair A B ⟶ pairHomologyExcisionTargetPair B :=
  { hom := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    map_subspace' := by
      intro a ha
      exact ha }

/-- The canonical comparison from the genuine source pair `(A, A ∩ B)` to the excision owner
`removeSubset (X, B) Aᶜ`. -/
private def pairHomologyExcisionSourcePairToRemoveSubset {X : Type u} [TopologicalSpace X]
    (A B : Set X) :
    pairHomologyExcisionSourcePair A B ⟶
      removeSubset (pairHomologyExcisionTargetPair B) Aᶜ :=
  { hom := TopCat.ofHom
      ⟨fun a ↦ ⟨a.1, by
          exact Set.notMem_compl_iff.mpr a.2⟩,
        continuous_subtype_val.subtype_mk fun a ↦ by
          exact Set.notMem_compl_iff.mpr a.2⟩
    map_subspace' := by
      intro a ha
      exact ha }

/-- The inverse comparison from the canonical excision owner `removeSubset (X, B) Aᶜ` back to the
genuine source pair `(A, A ∩ B)`. -/
private def pairHomologyExcisionRemoveSubsetToSourcePair {X : Type u} [TopologicalSpace X]
    (A B : Set X) :
    removeSubset (pairHomologyExcisionTargetPair B) Aᶜ ⟶
      pairHomologyExcisionSourcePair A B :=
  { hom := TopCat.ofHom
      ⟨fun a ↦ ⟨a.1, by
          exact Set.notMem_compl_iff.mp a.2⟩,
        continuous_subtype_val.subtype_mk fun a ↦ by
          exact Set.notMem_compl_iff.mp a.2⟩
    map_subspace' := by
      intro a ha
      exact ha }

/-- The forward and backward transport between `(A, A ∩ B)` and `removeSubset (X, B) Aᶜ`
compose to the identity on `(A, A ∩ B)`. -/
private theorem pairHomologyExcisionSourcePairToRemoveSubset_hom_inv_id
    {X : Type u} [TopologicalSpace X] (A B : Set X) :
    pairHomologyExcisionSourcePairToRemoveSubset A B ≫
        pairHomologyExcisionRemoveSubsetToSourcePair A B =
      𝟙 (pairHomologyExcisionSourcePair A B) := by
  apply SpacePair.hom_ext
  ext a
  rfl

/-- The forward and backward transport between `(A, A ∩ B)` and `removeSubset (X, B) Aᶜ`
compose to the identity on `removeSubset (X, B) Aᶜ`. -/
private theorem pairHomologyExcisionSourcePairToRemoveSubset_inv_hom_id
    {X : Type u} [TopologicalSpace X] (A B : Set X) :
    pairHomologyExcisionRemoveSubsetToSourcePair A B ≫
        pairHomologyExcisionSourcePairToRemoveSubset A B =
      𝟙 (removeSubset (pairHomologyExcisionTargetPair B) Aᶜ) := by
  apply SpacePair.hom_ext
  ext a
  rfl

/-- The genuine source pair `(A, A ∩ B)` is canonically isomorphic to the excision owner
`removeSubset (X, B) Aᶜ`. -/
def pairHomologyExcisionSourcePairIsoRemoveSubset {X : Type u} [TopologicalSpace X]
    (A B : Set X) :
    pairHomologyExcisionSourcePair A B ≅
      removeSubset (pairHomologyExcisionTargetPair B) Aᶜ where
  hom := pairHomologyExcisionSourcePairToRemoveSubset A B
  inv := pairHomologyExcisionRemoveSubsetToSourcePair A B
  hom_inv_id := pairHomologyExcisionSourcePairToRemoveSubset_hom_inv_id A B
  inv_hom_id := pairHomologyExcisionSourcePairToRemoveSubset_inv_hom_id A B

/-- After transporting `(A, A ∩ B)` to `removeSubset (X, B) Aᶜ`, the source-facing inclusion is
the canonical `removeSubsetInclusion`. -/
theorem pairHomologyExcisionInclusion_eq_transport_comp
    {X : Type u} [TopologicalSpace X] (A B : Set X) :
    pairHomologyExcisionInclusion A B =
      (pairHomologyExcisionSourcePairIsoRemoveSubset A B).hom ≫
        removeSubsetInclusion (pairHomologyExcisionTargetPair B) Aᶜ := by
  apply SpacePair.hom_ext
  ext a
  rfl

/-- The triad-level excisive condition on `(X; A, B)` is equivalent to the closure/interior
criterion used by `PairHomologyTheory.excision`. -/
theorem pairHomologyExcisionTriad_isExcisive_iff
    {X : Type u} [TopologicalSpace X] (A B : Set X) :
    (pairHomologyExcisionTriad A B).IsExcisive ↔ closure Aᶜ ⊆ interior B := by
  change interior A ∪ interior B = (Set.univ : Set X) ↔ closure Aᶜ ⊆ interior B
  rw [closure_compl, Set.eq_univ_iff_forall, Set.subset_def]
  constructor
  · intro h x hx
    exact (h x).resolve_left hx
  · intro h x
    by_cases hx : x ∈ interior A
    · exact Or.inl hx
    · exact Or.inr (h x hx)

/-- The triad hypothesis on `(X; A, B)` supplies the closure/interior side condition required by
`PairHomologyTheory.excision`. -/
private theorem pairHomologyExcisionClosureComplement_subset_interior
    {X : Type u} [TopologicalSpace X] (A B : Set X)
    (hExcisive : (pairHomologyExcisionTriad A B).IsExcisive) :
    closure Aᶜ ⊆ interior B :=
  (pairHomologyExcisionTriad_isExcisive_iff A B).mp hExcisive

/-- Typeclass form of the excision isomorphism for the source-facing inclusion
`(A, A ∩ B) ⟶ (X, B)`. -/
instance pairHomologyExcision_isIso
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (A B : Set X) (q : ℤ)
    (hExcisive : (pairHomologyExcisionTriad A B).IsExcisive) :
    IsIso ((H q).map (pairHomologyExcisionInclusion A B)) := by
  let hTransport :
      IsIso ((H q).map (pairHomologyExcisionSourcePairToRemoveSubset A B)) := by
    change IsIso ((H q).map (pairHomologyExcisionSourcePairIsoRemoveSubset A B).hom)
    infer_instance
  let hRemoveSubset :
      IsIso ((H q).map
        (removeSubsetInclusion (pairHomologyExcisionTargetPair B) Aᶜ)) :=
    H.excision q (pairHomologyExcisionTargetPair B) Aᶜ
      (pairHomologyExcisionClosureComplement_subset_interior A B hExcisive)
  simpa [pairHomologyExcisionInclusion_eq_transport_comp, Functor.map_comp] using
    (IsIso.comp_isIso' hTransport hRemoveSubset)

/-- Axiom 13.1.4: for an excisive triad `(X; A, B)`, the inclusion
`pairHomologyExcisionInclusion A B : (A, A ∩ B) ⟶ (X, B)` induces an isomorphism on the
degree-`q` homology object of any Chapter 13 pair homology theory. -/
theorem pairHomologyExcision
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (A B : Set X) (q : ℤ)
    (hExcisive : (pairHomologyExcisionTriad A B).IsExcisive) :
    IsIso ((H q).map (pairHomologyExcisionInclusion A B)) := by
  exact pairHomologyExcision_isIso H A B q hExcisive
