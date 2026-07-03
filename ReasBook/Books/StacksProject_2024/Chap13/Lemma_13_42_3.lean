import Mathlib
import StacksProject_2024.Chap04.Lemma_4_22_10
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Lemma_13_42_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite
open scoped CategoryTheory

universe w v u uI vI uC vC

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/- Domain-style sampling for Lemma 13.42.3:
- primary domain: sequential inverse systems in `D(𝒜)`, boundedness via the canonical
  `t`-structure owners, and fixed pro-object values detected on the cohomology towers.
- sampled owner-level declarations:
  `SequentialInverseSystem` in `Chap12/Definition_12_31_2`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `DerivedCategory.isZero_of_isGE`,
  `DerivedCategory.isZero_of_isLE`,
  the chapter cohomology notation owner `H^i` in `Chap13/Definition_13_11_3`,
  `IsEssentiallyConstantCofilteredDiagram` in `Chap04/Definition_4_22_2`,
  `HasProObjectValue` in `Chap04/Remark_4_22_7`,
  `essentiallyConstant_proObject_characterizations` in `Chap04/Lemma_4_22_10`,
  `essentiallyConstant_middle_and_tail_value_triangle_of_essentiallyConstant_outer_terms` in
    `Chap13/Lemma_13_42_2`.
- best owner abstraction: the source-facing content is the bounded-cohomology induction theorem
  for a sequential inverse system in `D(𝒜)`; the canonical owners underneath it are
  `SequentialInverseSystem`, `DerivedCategory.IsGE`, `DerivedCategory.IsLE`,
  `IsEssentiallyConstantCofilteredDiagram`, and `HasProObjectValue`.
- primitive-vs-derived split: the primitive data are the inverse system `F` and the uniform
  cohomological bounds recorded canonically by `IsGE a` and `IsLE b` on every stage. The
  cohomology towers `F ⋙ H^i` for `i ∈ Set.Icc a b`, their essential constancy, and the resulting
  pro-object values are derived API around those owners; outside `Set.Icc a b`, the towers are
  canonically zero by `DerivedCategory.isZero_of_isGE` and `DerivedCategory.isZero_of_isLE`.

Source/core/bridge triage:
- `source-facing`: `essentiallyConstant_of_uniformly_bounded_essentiallyConstant_cohomology`,
  which records the textbook essential-constancy conclusion.
- `core/canonical`: `exists_proObjectValue_of_uniformly_bounded_essentiallyConstant_cohomology`,
  together with the owner predicates `DerivedCategory.IsGE`, `DerivedCategory.IsLE`,
  `HasProObjectValue`, and `H^i`.
- `bridge/view`: the textbook formulation "cohomology vanishes outside `[a, b]`", which is
  equivalent to the pair of owner assumptions `(F.obj (op n)).IsGE a` and
  `(F.obj (op n)).IsLE b`. -/

-- Proof sketch: induct on the width `b - a` of the cohomological amplitude. The truncation
-- triangle at the bottom degree identifies `τ_{\le a} (A_n)` with `H^a(A_n)[-a]`, so the left
-- term system is essentially constant by the hypothesis on degree-`a` cohomology. The remaining
-- tail `τ_{\ge a + 1} (A_n)` has smaller amplitude and degreewise essentially constant
-- cohomology, hence is essentially constant by induction. Apply Lemma `13.42.2` to the resulting
-- inverse system of truncation triangles, then read off the cohomology values from the outer-term
-- identifications and the final clause of Lemma `13.42.2`. The source-facing essential-constancy
-- conclusion is then recovered from the Chapter 4 owner theorem
-- `essentiallyConstant_proObject_characterizations`.
/-- Core/canonical owner form of Lemma 13.42.3: under the same boundedness and degreewise
essential-constancy hypotheses, the sequential inverse system has a fixed pro-object value `A`,
and every cohomology tower `H^i(A_n)` is corepresented by `H^i(A)`. The textbook conclusion that
`F` is essentially constant is derived from this by the Chapter 4 owner criterion
`essentiallyConstant_proObject_characterizations`. -/
theorem exists_proObjectValue_of_uniformly_bounded_essentiallyConstant_cohomology
    (F : SequentialInverseSystem (DerivedCategory 𝒜)) (a b : ℤ)
    (hGE : ∀ n : ℕ, (F.obj (op n)).IsGE a)
    (hLE : ∀ n : ℕ, (F.obj (op n)).IsLE b)
    (hH : ∀ i ∈ Set.Icc a b, IsEssentiallyConstantCofilteredDiagram (F ⋙ H^i)) :
    ∃ A : DerivedCategory 𝒜,
      HasProObjectValue F A ∧
        ∀ i : ℤ,
          HasProObjectValue (F ⋙ H^i) ((H^i).obj A) := sorry

/-- Lemma 13.42.3: if a sequential inverse system in `D(\mathcal A)` has uniformly bounded
cohomology, say in degrees `[a, b]`, and each cohomology inverse system `H^i(A_n)` is
essentially constant for `i ∈ [a, b]`, then the inverse system itself is essentially constant. -/
theorem essentiallyConstant_of_uniformly_bounded_essentiallyConstant_cohomology
    (F : SequentialInverseSystem (DerivedCategory 𝒜)) (a b : ℤ)
    (hGE : ∀ n : ℕ, (F.obj (op n)).IsGE a)
    (hLE : ∀ n : ℕ, (F.obj (op n)).IsLE b)
    (hH : ∀ i ∈ Set.Icc a b, IsEssentiallyConstantCofilteredDiagram (F ⋙ H^i)) :
    IsEssentiallyConstantCofilteredDiagram F := by
  rcases exists_proObjectValue_of_uniformly_bounded_essentiallyConstant_cohomology
      F a b hGE hLE hH with ⟨_, hA, _⟩
  rcases hA with ⟨e⟩
  exact (essentiallyConstant_proObject_characterizations F).mp e.isCorepresentable

end CategoryTheory
