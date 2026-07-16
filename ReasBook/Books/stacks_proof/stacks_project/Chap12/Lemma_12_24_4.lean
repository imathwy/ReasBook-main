import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_24_5
import stacks_proof.stacks_project.Chap12.Lemma_12_24_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

namespace CategoryTheory

open FilteredComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

variable {K L : FilteredComplex 𝒜}

/-
Domain-style sampling for Lemma `12.24.4`.
- primary domain: functoriality of the Chapter `12` associated cohomological spectral sequence of a
  filtered complex;
- sampled core/canonical declarations in this domain:
  `SpectralSequence.Hom`,
  `SpectralSequence.hom_ext`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.pageZeroIso`,
  `FilteredComplex.pageZeroColumnFunctor`,
  `FilteredComplex.gradedPieceColumnFunctor`;
- best owner abstraction: the mathlib owner category of cohomological spectral sequences, via
  `SpectralSequence.Hom`, together with the Chapter `12` owner predicate
  `IsAssociatedToFilteredComplex K E` and its canonical page-zero comparison isomorphisms
  `FilteredComplex.pageZeroIso`; the fixed-column comparison maps are derived by functoriality from
  `FilteredComplex.pageZeroColumnFunctor` and `FilteredComplex.gradedPieceColumnFunctor`;
- primitive data: a morphism `α : K ⟶ L` of filtered complexes, owner witnesses expressing that
  the chosen spectral sequences `E` and `E'` are associated to `K` and `L`, and the compatible
  spectral-sequence morphism supplied by the construction of the associated spectral sequence;
- derived API in this file: the supplied morphism `associatedSpectralSequenceMap E E' α η`, its
  page-zero compatibility theorem `associatedSpectralSequenceMap_commSq E E' α η`, and the
  companion uniqueness theorem once such data are supplied;
- source/core/bridge triage:
  `source-facing`: `associatedSpectralSequenceMap`;
  `core/canonical`: `IsAssociatedToFilteredComplex`, `pageZeroIso`,
    `pageZeroColumnFunctor`, and `gradedPieceColumnFunctor`;
  `bridge/view`: the fixed-column comparison squares obtained from those owner functors. -/

section AssociatedSpectralSequenceMap

variable (E E' : CohomologicalSpectralSequence 𝒜 0)
variable [IsAssociatedToFilteredComplex K E] [IsAssociatedToFilteredComplex L E']
variable (α : K ⟶ L)

/-- The source-level construction of associated spectral sequences supplies a morphism compatible
with the canonical page-zero comparisons. The local predicate `IsAssociatedToFilteredComplex` only
records the page-zero identification, so this construction is explicit data rather than something
that can be recovered from that predicate alone. -/
structure AssociatedSpectralSequenceMapData where
  hom : E ⟶ E'
  commSq :
    ∀ p : ℤ,
      CommSq
        ((pageZeroColumnFunctor p).map hom)
        (pageZeroIso K E p).hom
        (pageZeroIso L E' p).hom
        ((gradedPieceColumnFunctor p).map α)

/-- A supplied associated spectral-sequence map gives the expected existence statement. -/
theorem exists_associatedSpectralSequenceMap
    (η : AssociatedSpectralSequenceMapData E E' α) :
    ∃ φ : E ⟶ E',
      ∀ p : ℤ,
        CommSq
          ((pageZeroColumnFunctor p).map φ)
          (pageZeroIso K E p).hom
          (pageZeroIso L E' p).hom
          ((gradedPieceColumnFunctor p).map α) :=
  ⟨η.hom, η.commSq⟩

/-- Helper for Chap12 Lemma 12 24 4: the page-zero comparison squares already determine the
`0`-page morphism of an associated spectral-sequence map. -/
lemma zeroPageHom_eq_of_commSq
    {φ ψ : E ⟶ E'}
    (hφ :
      ∀ p : ℤ,
        CommSq
          ((pageZeroColumnFunctor p).map φ)
          (pageZeroIso K E p).hom
          (pageZeroIso L E' p).hom
          ((gradedPieceColumnFunctor p).map α))
    (hψ :
      ∀ p : ℤ,
        CommSq
          ((pageZeroColumnFunctor p).map ψ)
          (pageZeroIso K E p).hom
          (pageZeroIso L E' p).hom
          ((gradedPieceColumnFunctor p).map α)) :
    φ.hom 0 = ψ.hom 0 := by
  -- Compare each fixed column through the canonical page-zero isomorphism.
  apply HomologicalComplex.hom_ext _ _
  intro pq
  rcases pq with ⟨p, q⟩
  have hcomm :
      (pageZeroColumnFunctor p).map φ ≫ (pageZeroIso L E' p).hom =
        (pageZeroColumnFunctor p).map ψ ≫ (pageZeroIso L E' p).hom := by
    exact (hφ p).w.trans (hψ p).w.symm
  have hq := congrArg (fun f ↦ f.f q) hcomm
  -- Cancel the target page-zero isomorphism to recover equality in the source column.
  simpa [pageZeroColumnFunctor] using
    (cancel_mono ((pageZeroIso L E' p).hom.f q)).1 hq

/-- Two morphisms of associated spectral sequences are equal as soon as they induce the same
canonical page-zero comparison squares. -/
theorem associatedSpectralSequenceMap_ext
    {φ ψ : E ⟶ E'}
    (hφ :
      ∀ p : ℤ,
        CommSq
          ((pageZeroColumnFunctor p).map φ)
          (pageZeroIso K E p).hom
          (pageZeroIso L E' p).hom
          ((gradedPieceColumnFunctor p).map α))
    (hψ :
      ∀ p : ℤ,
        CommSq
          ((pageZeroColumnFunctor p).map ψ)
          (pageZeroIso K E p).hom
          (pageZeroIso L E' p).hom
          ((gradedPieceColumnFunctor p).map α)) :
    φ = ψ := by
  -- Propagate equality from the page-zero comparison squares through the spectral-sequence pages.
  apply SpectralSequence.hom_ext
  intro r hr
  induction r, hr using Int.le_induction with
  | base =>
      -- The base page is controlled exactly by the page-zero comparison squares.
      exact zeroPageHom_eq_of_commSq E E' α hφ hψ
  | succ n hn hn_eq =>
      -- Higher pages follow from the recursive compatibility squares of spectral-sequence maps.
      apply HomologicalComplex.hom_ext _ _
      intro pq
      have hcomm :
          (E.iso n (n + 1) pq).hom ≫ (φ.hom (n + 1)).f pq =
            (E.iso n (n + 1) pq).hom ≫ (ψ.hom (n + 1)).f pq := by
        calc
          (E.iso n (n + 1) pq).hom ≫ (φ.hom (n + 1)).f pq =
              HomologicalComplex.homologyMap (φ.hom n) pq ≫ (E'.iso n (n + 1) pq).hom := by
                exact (φ.comm n (n + 1) pq).symm
          _ = HomologicalComplex.homologyMap (ψ.hom n) pq ≫ (E'.iso n (n + 1) pq).hom := by
                simp [hn_eq]
          _ = (E.iso n (n + 1) pq).hom ≫ (ψ.hom (n + 1)).f pq := by
                simpa using (ψ.comm n (n + 1) pq)
      exact (cancel_epi ((E.iso n (n + 1) pq).hom)).1 hcomm

/-- Chap12 Lemma 12 24 4: the induced morphism of associated spectral sequences is uniquely
determined by the page-zero comparison squares, once a compatible morphism has been supplied by
the associated-sequence construction. -/
theorem existsUnique_associatedSpectralSequenceMap
    (η : AssociatedSpectralSequenceMapData E E' α) :
    ∃! φ : E ⟶ E',
      ∀ p : ℤ,
        CommSq
          ((pageZeroColumnFunctor p).map φ)
          (pageZeroIso K E p).hom
          (pageZeroIso L E' p).hom
          ((gradedPieceColumnFunctor p).map α) := by
  rcases exists_associatedSpectralSequenceMap E E' α η with ⟨φ, hφ⟩
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  exact associatedSpectralSequenceMap_ext E E' α hψ hφ

/-- The morphism of associated spectral sequences supplied by the source-level construction. -/
noncomputable def associatedSpectralSequenceMap
    (η : AssociatedSpectralSequenceMapData E E' α) : E ⟶ E' :=
  η.hom

/-- The supplied morphism of associated spectral sequences satisfies the canonical page-zero
comparison squares by construction. -/
theorem associatedSpectralSequenceMap_commSq
    (η : AssociatedSpectralSequenceMapData E E' α) (p : ℤ) :
    CommSq
      ((pageZeroColumnFunctor p).map (associatedSpectralSequenceMap E E' α η))
      (pageZeroIso K E p).hom
      (pageZeroIso L E' p).hom
      ((gradedPieceColumnFunctor p).map α) :=
  η.commSq p

end AssociatedSpectralSequenceMap

end CategoryTheory
