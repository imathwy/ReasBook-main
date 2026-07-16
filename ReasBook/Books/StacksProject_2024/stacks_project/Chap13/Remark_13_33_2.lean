import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_33_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_4_7

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

/- Domain-style sampling for Remark 13.33.2:
- primary domain: sequential homotopy colimits in a pretriangulated category;
- sampled owner declarations:
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.sequentialTelescopeMap`,
  `CategoryTheory.Limits.Sigma.desc`,
  `CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂`,
  `CategoryTheory.exists_distinguished_triangle_unique_up_to_iso`;
- best owner abstraction: the chapter owner predicate `IsHomotopyColimitOf S Khocolim`;
- primitive-vs-derived split:
  the primitive source-facing presentation data are the maps `ι : ∀ n, S.obj n ⟶ K`, the
  connecting morphism `c : K ⟶ ∐ n, S.obj n⟦1⟧`, and the distinguished telescope triangle;
  the compatibility relation `S.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n` is derived from
  that triangle and should not be stored as primitive public data.

Source/core/bridge triage:
- `source-facing`: an explicit telescope presentation by structure maps and a distinguished
  triangle;
- `core/canonical`: `IsHomotopyColimitOf S Khocolim`;
- `bridge/view`: the theorems below converting between the canonical owner and explicit
  source-style presentation data. -/

variable {S : ℕ ⥤ D} [HasCoproduct S.obj]
  [HasCoproduct (fun n ↦ S.obj n⟦(1 : ℤ)⟧)]

/-- In a distinguished telescope triangle, the induced structure maps from the coproduct summands
are automatically compatible with the sequential transition maps. -/
theorem telescopePresentation_compat {Khocolim : D} (ι : ∀ n, S.obj n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ S.obj n⟦(1 : ℤ)⟧)
    (hK :
      Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈
          distTriang D) (n : ℕ) :
    S.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n := by
  have hzero :
      sequentialTelescopeMap S ≫ Limits.Sigma.desc ι = 0 := by
    simpa [Triangle.mk] using comp_distTriang_mor_zero₁₂ _ hK
  have hcompat :
      ι n - S.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = 0 := by
    have hzero' := congrArg (fun f ↦ Sigma.ι S.obj n ≫ f) hzero
    simpa [Sigma.ι_comp_sequentialTelescopeMap_assoc, Preadditive.sub_comp, Limits.Sigma.ι_desc,
      Category.assoc, comp_zero] using hzero'
  have hcompat' : ι n = S.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) := by
    simpa [sub_eq_zero] using hcompat
  simpa using hcompat'.symm

namespace IsHomotopyColimitOf

/-- A homotopy-colimit object admits source-style structure maps from each term and a connecting
morphism whose telescope triangle is distinguished; the compatibility of the structure maps is
derived, not additional primitive data. -/
theorem exists_presentation {Khocolim : D} (hK : IsHomotopyColimitOf S Khocolim) :
    ∃ (ι : ∀ n, S.obj n ⟶ Khocolim) (c : Khocolim ⟶ ∐ fun n ↦ S.obj n⟦(1 : ℤ)⟧),
      (∀ n, S.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n) ∧
        Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι)
          (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈
            distTriang D := by
  rcases hK with ⟨g, h, htriangle⟩
  let ι : ∀ n, S.obj n ⟶ Khocolim := fun n ↦ Sigma.ι S.obj n ≫ g
  let c : Khocolim ⟶ ∐ fun n ↦ S.obj n⟦(1 : ℤ)⟧ :=
    h ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).hom
  have hdesc : Limits.Sigma.desc ι = g := by
    apply Limits.Sigma.hom_ext
    intro n
    simpa [ι] using Limits.Sigma.ι_desc ι n
  have hc :
      c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv = h := by
    dsimp [c]
    have hc' :
        h ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).hom ≫
            (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv =
          h ≫ 𝟙 _ := by
      exact congrArg (fun f ↦ h ≫ f)
        (Iso.hom_inv_id (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj))
    simpa [Category.assoc] using hc'
  have hpresentation :
      Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈
          distTriang D := by
    rw [hdesc, hc]
    exact htriangle
  refine ⟨ι, c, ?_, hpresentation⟩
  intro n
  exact telescopePresentation_compat ι c hpresentation n

end IsHomotopyColimitOf

-- Proof sketch: both source-style presentations define distinguished telescope triangles with the
-- same first morphism. Apply the upstream comparison theorem
-- `exists_distinguished_triangle_unique_up_to_iso` from Lemma `13.4.7` to those two triangles and
-- extract the third component of the resulting triangle isomorphism.
/-- Any two source-style telescope presentations of a sequential homotopy colimit are isomorphic
through a map compatible with the structure maps and with the connecting morphisms. -/
theorem exists_iso_between_derived_colimit_presentations {Khocolim Khocolim' : D}
    (ι : ∀ n, S.obj n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ S.obj n⟦(1 : ℤ)⟧)
    (hK :
      Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈
          distTriang D)
    (ι' : ∀ n, S.obj n ⟶ Khocolim') (c' : Khocolim' ⟶ ∐ fun n ↦ S.obj n⟦(1 : ℤ)⟧)
    (hK' :
      Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι')
        (c' ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈
          distTriang D) :
    ∃ e : Khocolim ≅ Khocolim',
      (∀ n, ι n ≫ e.hom = ι' n) ∧
        e.hom ≫ c' = c := by
  obtain ⟨eT, he₁, he₂⟩ := exists_distinguished_triangle_unique_up_to_iso hK hK'
  refine ⟨Triangle.π₃.mapIso eT, ?_, ?_⟩
  · intro n
    have comm₂ := eT.hom.comm₂
    simpa [Limits.Sigma.ι_desc, Limits.Sigma.ι_desc_assoc, he₂] using
      congrArg (fun f ↦ Sigma.ι S.obj n ≫ f) comm₂
  · apply (cancel_mono (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv).1
    have comm₃ := eT.hom.comm₃
    simpa [he₁, Category.assoc] using comm₃.symm

-- Proof sketch: this is exactly the comparison theorem for two telescope presentations proved
-- above, restated as the label-associated entry for the Stacks remark.
/-- Remark 13.33.2: any two source-style telescope presentations of a sequential derived colimit
are canonically isomorphic through a map compatible with the structure maps and the connecting
morphisms of the distinguished triangles. -/
theorem exists_iso_between_derivedColimit_presentations {Khocolim Khocolim' : D}
    (ι : ∀ n, S.obj n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ S.obj n⟦(1 : ℤ)⟧)
    (hK :
      Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈
          distTriang D)
    (ι' : ∀ n, S.obj n ⟶ Khocolim')
    (c' : Khocolim' ⟶ ∐ fun n ↦ S.obj n⟦(1 : ℤ)⟧)
    (hK' :
      Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι')
        (c' ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈
          distTriang D) :
    ∃ e : Khocolim ≅ Khocolim',
      (∀ n, ι n ≫ e.hom = ι' n) ∧
        e.hom ≫ c' = c := by
  exact exists_iso_between_derived_colimit_presentations ι c hK ι' c' hK'

end

end CategoryTheory
