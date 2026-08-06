import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Corollary_3_8_12
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Lemma_4_1_7

universe u v

open CategoryTheory

variable {X₀ : Type u} {J : Type v}

-- Semantic recall: `PathConnectedSpace.of_locPathConnectedSpace` supplies the path-connectedness
-- used in the Chapter 3 classification, and the covering-space classification itself is packaged
-- by `ConnectedCoveringSpace.fundamentalGroupoidFunctor_isEquivalence`.

/-- Graph realizations inherit the covering-space classification functor equivalence from the
general connected, locally path connected, semilocally simply connected case when equipped with
the chapter's source-faithful quotient topology. -/
instance graphRealization_fundamentalGroupoidFunctor_isEquivalence
    (boundary : J ↪ Fin 2 → X₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)] :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    Functor.IsEquivalence
      (ConnectedCoveringSpace.fundamentalGroupoidFunctor :
        ConnectedCoveringSpace (graphRealization boundary) ⥤
          ConnectedCovering (FundamentalGroupoid (graphRealization boundary))) := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : ConnectedSpace (graphRealization boundary) := hConnected
  let _ : StronglyLocallyContractibleSpace (graphRealization boundary) :=
    graphRealization_stronglyLocallyContractibleSpace boundary
  let _ : LocPathConnectedSpace (graphRealization boundary) :=
    instLocPathConnectedSpace
  let hLocallyContractible :
      LocallyContractibleSpace (graphRealization boundary) :=
    graphRealization_locallyContractibleSpace boundary
  let _ : SemilocallySimplyConnectedSpace (graphRealization boundary) :=
    LocallyContractibleSpace.semilocallySimplyConnectedSpace hLocallyContractible
  exact ConnectedCoveringSpace.fundamentalGroupoidFunctor_isEquivalence

/-- Corollary 4.1.8: every connected graph has all possible covering spaces, formalized by the
canonical equivalence between connected covering spaces over the source-faithful realization
`graphRealization boundary` and connected coverings of
`FundamentalGroupoid (graphRealization boundary)`. -/
theorem graphRealization_hasAllCoveringSpaces
    (boundary : J ↪ Fin 2 → X₀)
    [hConnected :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      ConnectedSpace (graphRealization boundary)] :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    Functor.IsEquivalence
      (ConnectedCoveringSpace.fundamentalGroupoidFunctor :
        ConnectedCoveringSpace (graphRealization boundary) ⥤
          ConnectedCovering (FundamentalGroupoid (graphRealization boundary))) := by
  -- The labeled corollary is just the graph-specialized companion instance above.
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : ConnectedSpace (graphRealization boundary) := hConnected
  let _ : StronglyLocallyContractibleSpace (graphRealization boundary) :=
    graphRealization_stronglyLocallyContractibleSpace boundary
  let _ : LocPathConnectedSpace (graphRealization boundary) :=
    instLocPathConnectedSpace
  let hLocallyContractible :
      LocallyContractibleSpace (graphRealization boundary) :=
    graphRealization_locallyContractibleSpace boundary
  let _ : SemilocallySimplyConnectedSpace (graphRealization boundary) :=
    LocallyContractibleSpace.semilocallySimplyConnectedSpace hLocallyContractible
  exact graphRealization_fundamentalGroupoidFunctor_isEquivalence boundary
