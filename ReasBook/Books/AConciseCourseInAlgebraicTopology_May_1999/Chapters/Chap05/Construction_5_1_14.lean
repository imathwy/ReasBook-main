import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_7

open scoped Topology

universe u v

-- The source-facing k-ification topology declares a subset closed exactly when it is compactly
-- closed in the sense of Definition 5.1.7. Mathlib's canonical `compactlyGenerated` topology
-- remains available below as the compact Hausdorff bridge.

/- The k-ification `kX` of a space `X` is the topology whose closed sets are the compactly closed
subsets of `X`. This file records that source-facing construction and keeps the `CompHaus`
description of `TopologicalSpace.compactlyGenerated X` as bridge API. -/

/-- The topology on `X` whose closed sets are the compactly closed subsets of the original
topology. -/
@[implicit_reducible] def compactlyClosedTopology (X : Type u) [TopologicalSpace X] :
    TopologicalSpace X where
  IsOpen U := IsCompactlyClosed.{u, v} Uᶜ
  isOpen_univ := by
    simpa using
      (isClosed_empty.isCompactlyClosed :
        IsCompactlyClosed.{u, v} (∅ : Set X))
  isOpen_inter U V hU hV := by
    intro K _ _ g
    simpa [Set.compl_inter, Set.preimage_union] using (hU g).union (hV g)
  isOpen_sUnion S hS := by
    intro K _ _ g
    rw [Set.compl_sUnion, Set.sInter_image, Set.preimage_iInter₂]
    exact isClosed_biInter fun A hA ↦ by
      simpa [Set.preimage_compl] using hS A hA g

/-- A subset of `X` is open for `compactlyClosedTopology X` exactly when its complement is
compactly closed in the original topology. -/
theorem isOpen_compactlyClosedTopology_iff
    {X : Type u} [TopologicalSpace X] {U : Set X} :
    IsOpen[compactlyClosedTopology.{u, v} X] U ↔ IsCompactlyClosed.{u, v} Uᶜ :=
  Iff.rfl

/-- Construction 5.1.14. A subset of `X` is closed for `compactlyClosedTopology X` exactly when
it is compactly closed in the original topology. -/
theorem isClosed_compactlyClosedTopology_iff_isCompactlyClosed
    {X : Type u} [TopologicalSpace X] {A : Set X} :
    IsClosed[compactlyClosedTopology.{u, v} X] A ↔ IsCompactlyClosed.{u, v} A := by
  have hOpenCompl :
      IsOpen[compactlyClosedTopology.{u, v} X] Aᶜ ↔
        IsCompactlyClosed.{u, v} (Aᶜ)ᶜ :=
    isOpen_compactlyClosedTopology_iff
  constructor
  · intro hA
    simpa using hOpenCompl.1 hA.isOpen_compl
  · intro hA
    refine @IsClosed.mk X (compactlyClosedTopology.{u, v} X) A ?_
    exact hOpenCompl.2 (by simpa using hA)

/-- If pullbacks of `A` along all continuous maps from compact Hausdorff spaces are closed, then
`A` is closed for `TopologicalSpace.compactlyGenerated.{v} X`. -/
theorem isClosed_compactlyGenerated_of_compHausClosed
    {X : Type u} [TopologicalSpace X] {A : Set X}
    (hA : ∀ (S : CompHaus.{v}) (f : C(S, X)), IsClosed (f ⁻¹' A)) :
    IsClosed[TopologicalSpace.compactlyGenerated.{v, u} X] A := by
  -- Unfold the coinduced owner and check closedness on each compact Hausdorff generator.
  rw [TopologicalSpace.compactlyGenerated, isClosed_coinduced, isClosed_sigma_iff]
  rintro ⟨S, f⟩
  exact hA S f

/-- A subset of `X` is closed for `TopologicalSpace.compactlyGenerated.{v} X` exactly when its
pullback along every continuous map from a compact Hausdorff space to `X` is closed. -/
theorem isClosed_compactlyGenerated_iff_compHausClosed
    {X : Type u} [TopologicalSpace X] {A : Set X} :
    IsClosed[TopologicalSpace.compactlyGenerated.{v, u} X] A ↔
      ∀ (S : CompHaus.{v}) (f : C(S, X)), IsClosed (f ⁻¹' A) := by
  constructor
  · intro hA
    rw [TopologicalSpace.compactlyGenerated, isClosed_coinduced, isClosed_sigma_iff] at hA
    intro S f
    exact hA ⟨S, f⟩
  · exact isClosed_compactlyGenerated_of_compHausClosed

/-- A compactly closed subset of `X` is closed for `TopologicalSpace.compactlyGenerated X`. -/
lemma isClosed_compactlyGenerated_of_isCompactlyClosed
    {X : Type u} [TopologicalSpace X] {A : Set X} (hA : IsCompactlyClosed.{u, v} A) :
    IsClosed[TopologicalSpace.compactlyGenerated.{v, u} X] A := by
  -- Restrict the compact-source condition to compact Hausdorff test spaces.
  refine isClosed_compactlyGenerated_of_compHausClosed ?_
  intro S f
  exact hA.isClosed_preimage f f.continuous
