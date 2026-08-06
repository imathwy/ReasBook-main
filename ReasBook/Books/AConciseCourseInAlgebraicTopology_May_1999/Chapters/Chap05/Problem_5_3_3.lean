import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {X : Type u} [TopologicalSpace X]

-- Semantic search hit: `UCompactlyGeneratedSpace`; local Chapter 5 precedent:
-- `Subtype.weaklyHausdorffSpace` and `Subtype.uCompactlyGeneratedSpace`. The genuinely new
-- content here is the compactly generated component for a subtype whose points admit open
-- neighborhoods with closure contained in the subtype; this hypothesis already forces openness, so
-- the textbook owner `CompactlyGeneratedWeakHausdorffSpace` is still recovered by the existing
-- package instance from `Definition_5_1_10`.

/-- If every point of `U` has an open neighborhood whose closure is contained in `U`, then `U` is
open. -/
theorem isOpen_of_forall_mem_exists_isOpen_closure_subset {U : Set X}
    (h_local : ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ closure V ⊆ U) : IsOpen U := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases h_local x hx with ⟨V, hV_open, hxV, hV_closure⟩
  exact Filter.mem_of_superset (hV_open.mem_nhds hxV) (subset_closure.trans hV_closure)

section

variable [CompactlyGeneratedWeakHausdorffSpace.{u, v} X]
variable {U : Set X}
variable (h_local : ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ closure V ⊆ U)

/-- Helper for Problem 5.3.3: a closed subspace of a compactly generated space is compactly
generated. -/
theorem Subtype.uCompactlyGeneratedSpaceOfIsClosed {A : Set X} (hA : IsClosed A) :
    UCompactlyGeneratedSpace.{v} A := by
  -- Use the compactly-closed characterization on the closed embedding `A ↪ X`.
  refine uCompactlyGeneratedSpace_of_isClosed fun t ht ↦ ?_
  refine hA.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.2 <|
    UCompactlyGeneratedSpace.isClosed fun K g ↦ ?_
  let B : Set K := g ⁻¹' A
  have hB : IsClosed B := hA.preimage g.continuous
  letI : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  let g' : C(B, A) :=
    ⟨fun x : B ↦ ⟨g x, x.2⟩,
      (g.continuous.comp continuous_subtype_val).subtype_mk fun x : B ↦ x.2⟩
  have hclosed : IsClosed (g' ⁻¹' t) := ht (CompHaus.of.{v} ↥B) g'
  have himage : IsClosed (((↑) : B → K) '' (g' ⁻¹' t)) :=
    hB.isClosedMap_subtype_val _ hclosed
  suffices ((↑) : B → K) '' (g' ⁻¹' t) = g ⁻¹' ((↑) '' (t : Set A)) by
    simpa [this] using himage
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g' x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hxB : x ∈ B := by
      change g x ∈ A
      simpa [hyx] using y.2
    refine ⟨⟨x, hxB⟩, ?_, rfl⟩
    change (⟨g x, hxB⟩ : A) ∈ t
    have hxy : (⟨g x, hxB⟩ : A) = y := by
      apply Subtype.ext
      simp [hyx]
    simpa [hxy] using hy

/-- Helper for Problem 5.3.3: the canonical continuous inclusion `closure V → U` induced by a
closure containment `closure V ⊆ U`. -/
def closureToSubtypeMap {V U : Set X} (hVU : closure V ⊆ U) : C((closure V), U) :=
  ⟨fun x ↦ ⟨x.1, hVU x.2⟩, continuous_subtype_val.subtype_mk fun x ↦ hVU x.2⟩

/-- Helper for Problem 5.3.3: restricting a compactly-closed subset of `U` to `closure V` gives
an ambient closed image in `X`. -/
theorem isClosedImageRestrictToClosure {s : Set U} {V : Set X} (hVU : closure V ⊆ U)
    (hs : ∀ (S : CompHaus.{v}) (f : C(S, U)), IsClosed (f ⁻¹' s)) :
    IsClosed (Subtype.val '' (((closureToSubtypeMap hVU) ⁻¹' s : Set (closure V)))) := by
  let _ : UCompactlyGeneratedSpace.{v} (closure V) :=
    Subtype.uCompactlyGeneratedSpaceOfIsClosed (A := closure V) isClosed_closure
  -- First prove closedness in the closed subspace `closure V`.
  have hclosedClosure : IsClosed (((closureToSubtypeMap hVU) ⁻¹' s : Set (closure V))) := by
    refine UCompactlyGeneratedSpace.isClosed fun S g ↦ ?_
    simpa using hs S ((closureToSubtypeMap hVU).comp g)
  -- Then transport that closedness to the ambient image in `X`.
  exact
    isClosed_closure.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.1 hclosedClosure

/-- The compactly generated component of Problem 5.3.3 for a subtype `U` satisfying the local
closure-neighborhood hypothesis. -/
instance Subtype.uCompactlyGeneratedSpaceOfClosureSubset :
    UCompactlyGeneratedSpace.{v} U := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s hs ↦ ?_
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  rcases h_local x.1 x.2 with ⟨V, hV_open, hxV, hV_closure⟩
  let restrictedImage : Set X :=
    Subtype.val '' (((closureToSubtypeMap hV_closure) ⁻¹' s : Set (closure V)))
  have hrestrictedClosed : IsClosed restrictedImage :=
    isClosedImageRestrictToClosure hV_closure hs
  -- Separate `x` from `s` using the closed image coming from the smaller closed neighborhood.
  refine (mem_nhds_subtype U x (sᶜ)).2 ?_
  refine ⟨V ∩ restrictedImageᶜ, ?_, ?_⟩
  · have hxNotImage : x.1 ∈ restrictedImageᶜ := by
      exact fun hyImage ↦ hx <| by
        rcases hyImage with ⟨y, hy, hyx⟩
        have hyEq : closureToSubtypeMap hV_closure y = x := by
          apply Subtype.ext
          simpa using hyx
        simpa [hyEq] using hy
    exact
      Filter.inter_mem (hV_open.mem_nhds hxV)
        (hrestrictedClosed.isOpen_compl.mem_nhds hxNotImage)
  · intro y hy
    rcases hy with ⟨hyV, hyNotImage⟩
    change y ∉ s
    intro hyS
    have hyClosure : y.1 ∈ closure V := subset_closure hyV
    have hyPreimage :
        (⟨y.1, hyClosure⟩ : closure V) ∈ ((closureToSubtypeMap hV_closure) ⁻¹' s) := by
      change closureToSubtypeMap hV_closure ⟨y.1, hyClosure⟩ ∈ s
      have hyEq : closureToSubtypeMap hV_closure ⟨y.1, hyClosure⟩ = y := by
        apply Subtype.ext
        rfl
      simpa [hyEq] using hyS
    exact hyNotImage ⟨⟨y.1, hyClosure⟩, hyPreimage, rfl⟩

/-- Helper for Problem 5.3.3: register the proved compactly generated structure on `U` so the
final packaging check can use Definition 5.1.10 directly. -/
local instance instUCompactlyGeneratedSpaceClosureSubset :
    UCompactlyGeneratedSpace.{v} U :=
  Subtype.uCompactlyGeneratedSpaceOfClosureSubset (U := U) h_local

/- Problem 5.3.3: a subset `U` of a compactly generated weak Hausdorff space `X` is again
compactly generated weak Hausdorff if every point of `U` has an open neighborhood in `X` whose
closure is contained in `U`; this local hypothesis already implies that `U` is open, so the
generic packaging instance from Definition 5.1.10 applies directly. -/
#check (by
  let _ : UCompactlyGeneratedSpace.{v} U :=
    Subtype.uCompactlyGeneratedSpaceOfClosureSubset (U := U) h_local
  infer_instance : CompactlyGeneratedWeakHausdorffSpace.{u, v} U)

end

section PositiveLocus

variable {Y : Type u} [TopologicalSpace Y]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} Y]

/-- The positive locus of a continuous real-valued function on a compactly generated weak
Hausdorff space is again compactly generated with its ordinary subtype topology. -/
theorem Subtype.uCompactlyGeneratedSpaceOfContinuousPositive
    {f : Y → ℝ} (hf : Continuous f) :
    UCompactlyGeneratedSpace.{u} {y : Y | 0 < f y} := by
  refine Subtype.uCompactlyGeneratedSpaceOfClosureSubset (U := {y : Y | 0 < f y}) ?_
  intro y hy
  let V : Set Y := {z | f y / 2 < f z}
  refine ⟨V, ?_, ?_, ?_⟩
  · exact isOpen_lt continuous_const hf
  · change f y / 2 < f y
    change 0 < f y at hy
    linarith
  · have hVsubset : V ⊆ {z : Y | f y / 2 ≤ f z} := by
      intro z hz
      change f y / 2 < f z at hz
      exact le_of_lt hz
    have hclosed : IsClosed {z : Y | f y / 2 ≤ f z} :=
      isClosed_le continuous_const hf
    have hclosure : closure V ⊆ {z : Y | f y / 2 ≤ f z} :=
      closure_minimal hVsubset hclosed
    intro z hz
    change 0 < f z
    change 0 < f y at hy
    exact lt_of_lt_of_le (half_pos hy) (hclosure hz)

/-- The positive locus also inherits weak Hausdorffness, hence is a May space. -/
theorem Subtype.compactlyGeneratedWeakHausdorffSpaceOfContinuousPositive
    {f : Y → ℝ} (hf : Continuous f) :
    CompactlyGeneratedWeakHausdorffSpace.{u, u} {y : Y | 0 < f y} := by
  let _ : WeaklyHausdorffSpace.{u, u} {y : Y | 0 < f y} :=
    Subtype.weaklyHausdorffSpace
  let _ : UCompactlyGeneratedSpace.{u} {y : Y | 0 < f y} :=
    Subtype.uCompactlyGeneratedSpaceOfContinuousPositive hf
  infer_instance

end PositiveLocus
