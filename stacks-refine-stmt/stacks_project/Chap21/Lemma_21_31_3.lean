import Mathlib
import stacks_project.Chap21.Definition_21_31_2
import stacks_project.Chap21.Lemma_21_31_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily.Over

/-
Domain-style sampling for Lemma 21.31.3:
- primary domain: qc-covering families in `LC`, together with their stability under isomorphism,
  refinement, and pullback;
- inspected declarations:
  `SemiRepresentableFamily.Over.IsQcCoveringOne`,
  `SemiRepresentableFamily.Over.IsQcCoveringOne.exists_finite_compact_image_neighborhood`,
  `SemiRepresentableFamily.Over.ofArrows`,
  `compactSpace_pullback`,
  `isCompact_univ_pullback_of_compact`;
- best owner abstraction: the source-facing owner is the predicate
  `SemiRepresentableFamily.Over.IsQcCoveringOne`; the present file should contribute only closure
  lemmas for that owner rather than parallel wrapper APIs;
- primitive vs derived:
  primitive data are only the fixed-target owner object `ofArrows X_ f` together with the finite
  compact-image neighborhood condition from `IsQcCoveringOne`;
  isomorphism, composition, and base change are derived closure properties, not new packaged data.

Source/core/bridge triage:
- `source-facing`: qc coverings in `LC` and their stability properties from the Stacks text;
- `core/canonical`: the owner predicate `SemiRepresentableFamily.Over.IsQcCoveringOne` together
  with the pullback object in `LCCat`;
- `bridge/view`: `SemiRepresentableFamily.Over.ofArrows` for the indexed-arrow presentation, and
  the direct use of the canonical pullback API from `CategoryTheory.Limits`. -/

section

variable {I : Type v} {J : I → Type w}
variable {X X' : LCCat.{u}} {X_ : I → LCCat.{u}}
variable {f : ∀ i, X_ i ⟶ X}

-- Proof sketch: an isomorphism is a homeomorphism on the underlying spaces, so every point of `X`
-- has a neighborhood equal to the image of the singleton finite family indexed by `PUnit`; take the
-- whole source space, which is quasi-compact in a neighborhood of every point because `X'` lies in
-- `LC`.
/-- Lemma 21.31.3 (1): a singleton family consisting of an isomorphism in `LC` is a qc covering. -/
theorem IsQcCoveringOne.singleton_of_isIso (f : X' ⟶ X) [IsIso f] :
    (ofArrows (fun _ : PUnit ↦ X') (fun _ : PUnit ↦ f)).IsQcCoveringOne := sorry

-- Proof sketch: for a point of `X`, start with finitely many compact subsets witnessing that
-- `fᵢ : Xᵢ ⟶ X` is a qc covering near that point. Then refine each compact subset using the qc
-- covering on `Xᵢ`, extract finite subcovers by compactness, and compose the corresponding maps.
/-- Lemma 21.31.3 (2): a family obtained by refining each member of a qc covering by another qc
covering is again a qc covering. -/
theorem IsQcCoveringOne.comp
    {X__ : ∀ i, J i → LCCat.{u}} (g : ∀ i j, X__ i j ⟶ X_ i)
    (hf : (ofArrows X_ f).IsQcCoveringOne)
    (hg : ∀ i, (ofArrows (X__ i) (g i)).IsQcCoveringOne) :
    (ofArrows
      (fun ij : Sigma J ↦ X__ ij.1 ij.2)
      (fun ij : Sigma J ↦ g ij.1 ij.2 ≫ f ij.1)).IsQcCoveringOne := sorry

-- Proof sketch: let `x' ∈ X'` map to `x ∈ X`. Choose finitely many compact subsets upstairs over
-- `X` witnessing the qc covering near `x`, then intersect them with a compact neighborhood of `x'`
-- after base change. The pullbacks of compact subsets remain compact by Lemma `21.31.1`, and their
-- images cover a neighborhood of `x'`.
/-- Lemma 21.31.3 (3): qc coverings in `LC` are stable under base change. -/
theorem IsQcCoveringOne.baseChange (hf : (ofArrows X_ f).IsQcCoveringOne) (φ : X' ⟶ X) :
    (ofArrows
      (fun i ↦ pullback φ (f i))
      (fun i ↦ pullback.fst φ (f i))).IsQcCoveringOne := sorry

end
