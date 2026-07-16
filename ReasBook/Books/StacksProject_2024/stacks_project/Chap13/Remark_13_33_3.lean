import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_33_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-
Domain-style sampling for Remark 13.33.3:
- primary domain: morphisms between telescope triangles in a pretriangulated category;
- sampled owner declarations:
  `CategoryTheory.NatTrans.ofSequence`,
  `CategoryTheory.sequentialTelescopeMap_naturality`,
  `CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism`,
  `CategoryTheory.Pretriangulated.completeDistinguishedTriangleMorphism`,
  `CategoryTheory.TriangleMorphism`;
- best owner abstraction: the TR3 existence theorem
  `Pretriangulated.complete_distinguished_triangle_morphism`, with `TriangleMorphism` as the
  canonical bridge/view packaging;
- primitive-vs-derived split:
  the primitive data are the sequential diagrams `S`, `T`, a natural transformation `α : S ⟶ T`,
  and the two distinguished telescope presentations;
  the map between the two derived-colimit objects is derived API, namely the third component of a
  triangle morphism completing the telescope-map square.

Source/core/bridge triage:
- `source-facing`: a morphism of sequential systems together with two chosen telescope
  presentations;
- `core/canonical`: `Pretriangulated.complete_distinguished_triangle_morphism`;
- `bridge/view`: `TriangleMorphism`, `NatTrans.ofSequence`, and
  `sequentialTelescopeMap_naturality`. -/

variable {S T : ℕ ⥤ D} [HasCoproduct S.obj] [HasCoproduct T.obj]
  [HasCoproduct (fun n ↦ S.obj n⟦(1 : ℤ)⟧)] [HasCoproduct (fun n ↦ T.obj n⟦(1 : ℤ)⟧)]

-- Proof sketch: apply the TR3 owner `complete_distinguished_triangle_morphism` to the two chosen
-- telescope triangles and to the commuting square
-- `sequentialTelescopeMap_naturality α`. The resulting third component is the required map
-- between the two chosen derived-colimit objects. For source-style component maps `aₙ`, first
-- package them as `NatTrans.ofSequence aₙ ...`.
/-- Remark 13.33.3: a morphism of sequential systems induces at least one morphism between any two
chosen derived-colimit presentations, compatible with the structure maps and the connecting maps of
the two telescope triangles. No uniqueness is asserted. -/
theorem exists_morphism_between_derivedColimit_presentations (α : S ⟶ T)
    {Kcolim Lcolim : D} (i : ∀ n : ℕ, S.obj n ⟶ Kcolim) (j : ∀ n : ℕ, T.obj n ⟶ Lcolim)
    (c : Kcolim ⟶ ∐ fun n : ℕ ↦ S.obj n⟦(1 : ℤ)⟧)
    (d : Lcolim ⟶ ∐ fun n : ℕ ↦ T.obj n⟦(1 : ℤ)⟧)
    (hS : Triangle.mk (sequentialTelescopeMap S)
      (Limits.Sigma.desc i)
      (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈ distTriang D)
    (hT : Triangle.mk (sequentialTelescopeMap T)
      (Limits.Sigma.desc j)
      (d ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) T.obj).inv) ∈ distTriang D) :
    ∃ a : Kcolim ⟶ Lcolim,
      CommSq (Limits.Sigma.desc i) (Limits.Sigma.map α.app) a (Limits.Sigma.desc j) ∧
        CommSq
          (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv)
          a
          ((Limits.Sigma.map α.app)⟦(1 : ℤ)⟧')
          (d ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) T.obj).inv) := by
  obtain ⟨a, ha₂, ha₃⟩ :=
    complete_distinguished_triangle_morphism _ _ hS hT (Limits.Sigma.map α.app)
      (Limits.Sigma.map α.app) (by simpa using sequentialTelescopeMap_naturality α)
  exact ⟨a, ⟨ha₂⟩, ⟨ha₃⟩⟩

end

end CategoryTheory
