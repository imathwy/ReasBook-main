import Mathlib
import Mathlib.CategoryTheory.Sites.Limits
import StacksProject_2024.Chap07.Lemma_7_17_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.GrothendieckTopology

universe u v w

noncomputable section

variable {X : TopCat.{u}} {I : Type v} [Category.{w} I] [IsFiltered I]
local notation "JX" => Opens.grothendieckTopology X

/- Domain-style sampling for Lemma 6.29.1:
- primary domain: filtered colimits of set-valued sheaves on the site of opens of a topological
  space;
- sampled owner abstractions:
  `CategoryTheory.GrothendieckTopology.HasCofinalFiniteQuasiCompactOverlapCoverings`,
  `sheafSections`,
  `colimit.post`,
  `CategoryTheory.sheafFilteredColimitSectionsComparison_bijective_of_cofinalFiniteQuasiCompactOverlapCoverings`;
- source-facing layer in this file: the topological `IsCompact` specializations for opens of `X`;
- core/canonical owner for the comparison map: `colimit.post` evaluated at the sections functor on
  `U`;
- core/canonical owner for the cover hypothesis:
  `CategoryTheory.GrothendieckTopology.HasCofinalFiniteQuasiCompactOverlapCoverings JX U`;
- bridge/view layer: the statements below specialize the site-level filtered-colimit comparison
  results to the opens site of a topological space.

Primitive data are only the diagram `𝓕` and the open `U`. The comparison map is derived from the
ambient colimit cocone, so it should not be stored as a separate public definition.
-/

private theorem quasiCompactObject_of_isCompact (U : Opens X) (hU : IsCompact (U : Set X)) :
    QuasiCompactObject JX U := by
  intro S
  let Uᵢ : S.Arrow → Opens X := fun I ↦ I.Y
  have hcover : (U : Set X) ⊆ ⋃ I, ((Uᵢ I : Opens X) : Set X) := by
    intro x hx
    rcases S.condition x hx with ⟨V, i, hi, hxV⟩
    exact Set.mem_iUnion.mpr ⟨⟨V, i, hi⟩, hxV⟩
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun I ↦ ((Uᵢ I : Opens X) : Set X))
    (fun I ↦ (Uᵢ I).isOpen) hcover
  refine ⟨(↑t : Set S.Arrow), t.finite_toSet, ?_⟩
  change Sieve.ofArrows (fun I : ↑↑t ↦ I.1.Y) (fun I ↦ I.1.f) ∈ JX U
  intro x hx
  rcases Set.mem_iUnion₂.mp (ht hx) with ⟨I, hI, hxI⟩
  refine ⟨I.Y, I.f, Sieve.ofArrows_mk (fun J : ↑↑t ↦ J.1.Y) (fun J ↦ J.1.f) ⟨I, hI⟩, hxI⟩

-- Proof sketch: this is the opens-site specialization of the abstract site theorem from
-- Chapter 7.
/-- Lemma 6.29.1 (1): if all transition maps are monomorphisms, equivalently pointwise injective on
the sections of every open subset, then the canonical map from the colimit of sections over `U` to
the sections of the colimit sheaf over `U` is injective. -/
theorem injective_sheafColimitSectionComparison_of_transitionMapsInjective
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) (U : Opens X)
    [HasColimit 𝓕]
    [HasColimit (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op U))]
    (hmono : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (𝓕.map f)) :
    Function.Injective (colimit.post 𝓕 ((sheafSections JX (Type (max u v w))).obj (op U))) := by
  simpa using
    CategoryTheory.sheafFilteredColimitSectionsComparison_injective_of_transitionMonomorphisms.{max
      v w, v, u, u, w} 𝓕 hmono U

-- Proof sketch: convert quasi-compactness of the open subset into the opens-site owner
-- `JX.QuasiCompactObject U`, then apply the Chapter 7 theorem.
/-- Lemma 6.29.1 (2): if `U` is quasi-compact, then the canonical map from the colimit of sections
over `U` to the sections of the colimit sheaf over `U` is injective. -/
theorem injective_sheafColimitSectionComparison_of_isCompact
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) (U : Opens X)
    [HasColimit 𝓕]
    [HasColimit (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op U))]
    (hU : IsCompact (U : Set X)) :
    Function.Injective (colimit.post 𝓕 ((sheafSections JX (Type (max u v w))).obj (op U))) := by
  simpa using
    CategoryTheory.sheafFilteredColimitSectionsComparison_injective_of_quasiCompactObject.{max v
      w, v, u, u, w} 𝓕 U (quasiCompactObject_of_isCompact U hU)

-- Proof sketch: after converting `hU` to the opens-site quasi-compactness owner, this is the
-- Type-valued specialization of the Chapter 7 isomorphism statement.
/-- Lemma 6.29.1 (3): if `U` is quasi-compact and all transition maps are injective, then the
canonical comparison map is an isomorphism. The transition-map hypothesis is stated canonically as
monomorphy in the sheaf category. -/
theorem isIso_sheafColimitSectionComparison_of_isCompact_of_transitionMapsInjective
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) (U : Opens X)
    [HasColimit 𝓕]
    [HasColimit (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op U))]
    (hU : IsCompact (U : Set X))
    (hmono : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (𝓕.map f)) :
    IsIso (colimit.post 𝓕 ((sheafSections JX (Type (max u v w))).obj (op U))) := by
  simpa using
    CategoryTheory.sheafFilteredColimitSectionsComparison_isIso_of_quasiCompactObject_of_transitionMonomorphisms.{max
      v w, v, u, u, w} 𝓕 U (quasiCompactObject_of_isCompact U hU) hmono

-- Proof sketch: this is exactly the opens-site specialization of the Chapter 7 owner theorem with
-- the same cover hypothesis.
/-- Auxiliary filtered-colimit criterion: if every open cover of `U` admits a finite refinement
whose pairwise intersections are quasi-compact, then the canonical comparison map is bijective. The
cover hypothesis is stated canonically as the opens-site owner
`HasCofinalFiniteQuasiCompactOverlapCoverings JX U`. -/
theorem bijective_sheafColimitSectionComparison_of_cofinalFiniteQuasiCompactOverlapCoverings
    (𝓕 : I ⥤ X.Sheaf (Type (max u v w))) (U : Opens X)
    [HasColimit 𝓕]
    [HasColimit (𝓕 ⋙ (sheafSections JX (Type (max u v w))).obj (op U))]
    (hU : HasCofinalFiniteQuasiCompactOverlapCoverings JX U) :
    Function.Bijective
      (colimit.post 𝓕 ((sheafSections JX (Type (max u v w))).obj (op U))) := by
  simpa using
    CategoryTheory.sheafFilteredColimitSectionsComparison_bijective_of_cofinalFiniteQuasiCompactOverlapCoverings.{max
      v w, v, u, u, w} 𝓕 U hU
