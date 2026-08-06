import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Definition_18_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_5_1

open CategoryTheory Limits
open scoped Manifold Topology

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` only surfaced generic compact-space and terminal-colimit
-- APIs, while local Chapter 20 precedent already fixes `compactlySupportedCohomology` on the
-- Chapter 18 pair-cohomology owner. This file therefore records the canonical comparison
-- `H_c^p(M; π) ⟶ H^p(M, ∅; π)`, and then isolates the compact oriented case needed for
-- Corollary 20.5.4.

section comparison

variable {π : Type u} [AddCommGroup π]
variable (H : PairCohomologyTheory π)
variable (X : TopCat.{u})

-- The inclusion maps into `H^p(M, ∅; π)` are natural over the compact-subset diagram defining
-- `H_c^p(TopCat.of M; H)`.
private theorem compactlySupportedToOrdinaryCohomology_naturality
    (p : ℤ) {K L : TopologicalSpace.Compacts X} (h : K ⟶ L) :
    (compactlySupportedCohomologyDiagram H X p).map h ≫
        (H.cohomology p).map
          (subsetPairInclusion (Set.empty_subset ((L : Set X)ᶜ))).op =
      (H.cohomology p).map
        (subsetPairInclusion (Set.empty_subset ((K : Set X)ᶜ))).op := by
  simpa using
    congrArg (fun f ↦ (H.cohomology p).map f.op)
      (subsetPairInclusion_comp
        (Set.compl_subset_compl.mpr h.le)
        (Set.empty_subset ((L : Set X)ᶜ))).symm

-- The maps `H^p(M, M \ K; π) ⟶ H^p(M, ∅; π)` induced by `∅ ⊆ M \ K` assemble into a cocone
-- over the compact-subset diagram.
private def compactlySupportedToOrdinaryCohomologyCocone
    (p : ℤ) : Cocone (compactlySupportedCohomologyDiagram H X p) where
  pt := (H.absoluteCohomology p).obj (Opposite.op X)
  ι :=
    { app := fun K ↦
        (H.cohomology p).map
          (subsetPairInclusion (Set.empty_subset ((K : Set X)ᶜ))).op
      naturality := fun _ _ h ↦ compactlySupportedToOrdinaryCohomology_naturality H X p h }

/-- The canonical comparison morphism from compactly supported cohomology to ordinary cohomology. -/
def compactlySupportedToOrdinaryCohomology
    (p : ℤ) :
    H_c^p(X; H) ⟶ (H.absoluteCohomology p).obj (Opposite.op X) :=
  colimit.desc _ (compactlySupportedToOrdinaryCohomologyCocone H X p)

/-- The `K`-component of `compactlySupportedToOrdinaryCohomology` is the relative-cohomology map
induced by the inclusion `∅ ⊆ M \ K`. -/
@[simp] theorem colimit_ι_compactlySupportedToOrdinaryCohomology
    (p : ℤ) (K : TopologicalSpace.Compacts X) :
    colimit.ι (compactlySupportedCohomologyDiagram H X p) K ≫
        compactlySupportedToOrdinaryCohomology H X p =
      (H.cohomology p).map
        (subsetPairInclusion (Set.empty_subset ((K : Set X)ᶜ))).op := by
  simpa
      [compactlySupportedToOrdinaryCohomology,
        compactlySupportedToOrdinaryCohomologyCocone]
    using
      colimit.ι_desc
        (compactlySupportedToOrdinaryCohomologyCocone H X p) K

end comparison

section compactSpace

variable {π : Type u} [AddCommGroup π]
variable (H : PairCohomologyTheory π)
variable (X : TopCat.{u}) [CompactSpace X]

/-- For a compact space `X`, the compact-support comparison morphism `H_c^p(X; H) ⟶ H^p(X, ∅; π)`
is the inverse of the terminal colimit inclusion at `⊤ : TopologicalSpace.Compacts X`. This is the
canonical compact-space owner behind Corollary 20.5.4. -/
theorem compactlySupportedToOrdinaryCohomology_isIso_of_compactSpace
    (p : ℤ) :
    IsIso (compactlySupportedToOrdinaryCohomology H X p) := by
  let ιtop := colimit.ι (compactlySupportedCohomologyDiagram H X p)
    (⊤ : TopologicalSpace.Compacts X)
  haveI :
      IsIso ιtop := by
    exact isIso_ι_of_isTerminal (isTerminalTop : IsTerminal (⊤ : TopologicalSpace.Compacts X)) _
  have h_top_subset : (((⊤ : TopologicalSpace.Compacts X) : Set X)ᶜ) ⊆ (∅ : Set X) := by
    simp [TopologicalSpace.Compacts.coe_top]
  let ftop :
      Opposite.op (subsetPair X (((⊤ : TopologicalSpace.Compacts X) : Set X)ᶜ)) ⟶
        Opposite.op (subsetPair X ∅) :=
    (subsetPairInclusion
      (Set.empty_subset (((⊤ : TopologicalSpace.Compacts X) : Set X)ᶜ))).op
  let gtop :
      Opposite.op (subsetPair X ∅) ⟶
        Opposite.op (subsetPair X (((⊤ : TopologicalSpace.Compacts X) : Set X)ᶜ)) :=
    (subsetPairInclusion h_top_subset).op
  have h_gtop_ftop : gtop ≫ ftop = 𝟙 _ := by
    apply Quiver.Hom.unop_inj
    apply SpacePair.hom_ext
    rfl
  have h_ftop_gtop : ftop ≫ gtop = 𝟙 _ := by
    apply Quiver.Hom.unop_inj
    apply SpacePair.hom_ext
    rfl
  haveI : IsIso ftop := by
    exact ⟨⟨gtop, h_ftop_gtop, h_gtop_ftop⟩⟩
  let mtop :
      (compactlySupportedCohomologyDiagram H X p).obj (⊤ : TopologicalSpace.Compacts X) ⟶
        (H.absoluteCohomology p).obj (Opposite.op X) :=
    (H.cohomology p).map ftop
  haveI : IsIso mtop := by
    refine ⟨⟨(H.cohomology p).map gtop, ?_, ?_⟩⟩
    · dsimp [mtop]
      simpa using congrArg ((H.cohomology p).map) h_ftop_gtop
    · dsimp [mtop]
      simpa using congrArg ((H.cohomology p).map) h_gtop_ftop
  have h_top :
      ιtop ≫ compactlySupportedToOrdinaryCohomology H X p = mtop := by
    dsimp [ιtop, mtop, ftop]
    exact
      colimit_ι_compactlySupportedToOrdinaryCohomology H X p
        (⊤ : TopologicalSpace.Compacts X)
  have h_eq :
      compactlySupportedToOrdinaryCohomology H X p =
        inv ιtop ≫ mtop := by
    calc
      compactlySupportedToOrdinaryCohomology H X p =
          inv ιtop ≫ (ιtop ≫ compactlySupportedToOrdinaryCohomology H X p) := by
            simp
      _ = inv ιtop ≫ mtop := by rw [h_top]
  rw [h_eq]
  refine ⟨⟨inv mtop ≫ ιtop, ?_, ?_⟩⟩
  · calc
      (inv ιtop ≫ mtop) ≫ (inv mtop ≫ ιtop) = inv ιtop ≫ (mtop ≫ inv mtop) ≫ ιtop := by
        simp [Category.assoc]
      _ = inv ιtop ≫ ιtop := by simp
      _ = 𝟙 _ := by simp
  · calc
      (inv mtop ≫ ιtop) ≫ (inv ιtop ≫ mtop) = inv mtop ≫ (ιtop ≫ inv ιtop) ≫ mtop := by
        simp [Category.assoc]
      _ = inv mtop ≫ mtop := by simp
      _ = 𝟙 _ := by simp

end compactSpace

section compactOriented

variable {R : Type u} [CommRing R]
variable {π : Type u} [AddCommGroup π]
variable (H : PairCohomologyTheory π)
variable {n : ℕ}
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {H' : Type u} [TopologicalSpace H'] {I : ModelWithCorners ℝ V H'} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H' M] [CompactSpace M]
variable [Fact (Module.finrank ℝ V = n)]
variable [ROrientedManifold R I n M]

/-- Corollary 20.5.4. For compact oriented `M`, compactly supported cohomology agrees with
ordinary cohomology: the canonical comparison morphism
`compactlySupportedToOrdinaryCohomology H (TopCat.of M) p` is an isomorphism. This source-facing
specialization uses only compactness, and is the compact-space identification used to recover the
compact Poincare duality theorem from Theorem 20.5.3 and Theorem 20.1.2. -/
theorem compactlySupportedToOrdinaryCohomology_isIso_of_rOrientedManifold
    (p : ℤ) :
    IsIso (compactlySupportedToOrdinaryCohomology H (TopCat.of M) p) := by
  simpa using compactlySupportedToOrdinaryCohomology_isIso_of_compactSpace
    H (TopCat.of M) p

end compactOriented

section compactSpaceInstance

variable {π : Type u} [AddCommGroup π]
variable (H : PairCohomologyTheory π)
variable {M : Type u} [TopologicalSpace M] [CompactSpace M]

/-- A compact ambient space turns the canonical comparison morphism
`H_c^p(M; π) ⟶ H^p(M, ∅; π)` into an automation-facing `IsIso` instance. -/
instance compactlySupportedToOrdinaryCohomology_isIso
    (p : ℤ) :
    IsIso (compactlySupportedToOrdinaryCohomology H (TopCat.of M) p) :=
  compactlySupportedToOrdinaryCohomology_isIso_of_compactSpace H (TopCat.of M) p

end compactSpaceInstance
