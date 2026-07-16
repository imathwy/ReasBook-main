import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_5
import StacksProject_2024.stacks_project.Chap12.Lemma_12_24_2

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
- primitive data: a morphism `α : K ⟶ L` of filtered complexes and owner witnesses expressing that
  the chosen spectral sequences `E` and `E'` are associated to `K` and `L`;
- derived API in this file: the induced morphism `associatedSpectralSequenceMap E E' α`, its
  page-zero compatibility theorem `associatedSpectralSequenceMap_commSq E E' α`, and the
  companion existence/uniqueness theorems;
- source/core/bridge triage:
  `source-facing`: `associatedSpectralSequenceMap`;
  `core/canonical`: `IsAssociatedToFilteredComplex`, `pageZeroIso`,
    `pageZeroColumnFunctor`, and `gradedPieceColumnFunctor`;
  `bridge/view`: the fixed-column comparison squares obtained from those owner functors. -/

section AssociatedSpectralSequenceMap

variable (E E' : CohomologicalSpectralSequence 𝒜 0)
variable [IsAssociatedToFilteredComplex K E] [IsAssociatedToFilteredComplex L E']
variable (α : K ⟶ L)

/-- A morphism of filtered complexes induces at least one compatible morphism between any chosen
associated spectral sequences. -/
theorem exists_associatedSpectralSequenceMap :
    ∃ φ : E ⟶ E',
      ∀ p : ℤ,
        CommSq
          ((pageZeroColumnFunctor p).map φ)
          (pageZeroIso K E p).hom
          (pageZeroIso L E' p).hom
          ((gradedPieceColumnFunctor p).map α) := by
  sorry

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
  apply SpectralSequence.hom_ext
  intro r hr
  induction r, hr using Int.le_induction with
  | base =>
      apply HomologicalComplex.hom_ext _ _
      intro pq
      rcases pq with ⟨p, q⟩
      have hcomm :
          (pageZeroColumnFunctor p).map φ ≫ (pageZeroIso L E' p).hom =
            (pageZeroColumnFunctor p).map ψ ≫ (pageZeroIso L E' p).hom := by
        exact (hφ p).w.trans (hψ p).w.symm
      have hq := congrArg (fun f ↦ f.f q) hcomm
      simpa [pageZeroColumnFunctor] using
        (cancel_mono ((pageZeroIso L E' p).hom.f q)).1 hq
  | succ n hn hn_eq =>
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

/-- The induced morphism of associated spectral sequences is uniquely determined by the page-zero
comparison squares. -/
theorem existsUnique_associatedSpectralSequenceMap :
    ∃! φ : E ⟶ E',
      ∀ p : ℤ,
        CommSq
          ((pageZeroColumnFunctor p).map φ)
          (pageZeroIso K E p).hom
          (pageZeroIso L E' p).hom
          ((gradedPieceColumnFunctor p).map α) := by
  have h :
      ∃ φ : E ⟶ E',
        ∀ p : ℤ,
          CommSq
            ((pageZeroColumnFunctor p).map φ)
            (pageZeroIso K E p).hom
            (pageZeroIso L E' p).hom
            ((gradedPieceColumnFunctor p).map α) :=
    exists_associatedSpectralSequenceMap E E' α
  rcases h with ⟨φ, hφ⟩
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  exact associatedSpectralSequenceMap_ext E E' α hψ hφ

/-- The canonical morphism of associated spectral sequences induced by a morphism of filtered
complexes between chosen associated spectral sequences `E` and `E'`. -/
noncomputable def associatedSpectralSequenceMap : E ⟶ E' :=
  Classical.choose <|
    (existsUnique_associatedSpectralSequenceMap E E' α).exists

/-- The induced morphism of associated spectral sequences satisfies the canonical page-zero
comparison squares. -/
theorem associatedSpectralSequenceMap_commSq (p : ℤ) :
    CommSq
      ((pageZeroColumnFunctor p).map (associatedSpectralSequenceMap E E' α))
      (pageZeroIso K E p).hom
      (pageZeroIso L E' p).hom
      ((gradedPieceColumnFunctor p).map α) := by
  have h :
      ∀ p : ℤ,
        CommSq
          ((pageZeroColumnFunctor p).map (associatedSpectralSequenceMap E E' α))
          (pageZeroIso K E p).hom
          (pageZeroIso L E' p).hom
          ((gradedPieceColumnFunctor p).map α) :=
    Classical.choose_spec <|
      (existsUnique_associatedSpectralSequenceMap E E' α).exists
  exact h p

end AssociatedSpectralSequenceMap

end CategoryTheory
