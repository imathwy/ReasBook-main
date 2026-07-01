import stacks_project.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

noncomputable section

universe u v

namespace CochainComplex

variable {R : Type u} [CommRing R]

/- Domain sampling pass:
* primary domain: K-flat cochain complexes of `R`-modules and stability of the owner predicate
  under filtered colimits;
* sampled owner declarations:
  - `CochainComplex.IsKFlat` from `Definition_15_59_1`, the source-facing owner predicate;
  - `CochainComplex.isKFlat_iff` from `Definition_15_59_1`, the canonical eliminator exposing only
    the acyclicity-preservation content of `IsKFlat`;
  - `CategoryTheory.Limits.colimit`, the canonical owner of the filtered colimit object;
  - the ambient filtered-category typeclass `IsFiltered`, which is the canonical owner abstraction
    for the indexing hypothesis rather than a bespoke sequential-system wrapper.

Source/core/bridge triage:
* `source-facing`: the textbook closure of K-flatness under filtered colimits of module-valued
  cochain complexes;
* `core/canonical`: `CochainComplex.IsKFlat` on `CochainComplex (ModuleCat R) ℤ` together with the
  canonical colimit object `colimit F`;
* `bridge/view`: the sequential specialization obtained by instantiating the owner theorem at the
  preorder category `ℕ`; this file keeps that only as derived prose, not as a second public owner.

Primitive data are only the diagram `F`, the ambient colimit instance `[HasColimit F]`, and the
stagewise K-flatness hypotheses `hF`. The colimit complex and its K-flatness are derived from the
canonical colimit owner and the predicate `CochainComplex.IsKFlat`, so this file should not
introduce any auxiliary wrapper for sequential systems or filtered-colimit K-flat data.
-/

-- Proof sketch: let `M^•` be any acyclic complex. Tensoring with the filtered colimit identifies
-- `HomologicalComplex.tensorObj M (colimit F)` with the filtered colimit of the tensor products
-- `HomologicalComplex.tensorObj M (F.obj i)` by Lemma `10.12.9`, and each stage is acyclic by the
-- assumed K-flatness. Exactness of filtered colimits from Lemma `10.8.8` then gives acyclicity of
-- the colimit tensor complex.
/-- Lemma 15.59.8: any filtered colimit of K-flat cochain complexes of `R`-modules is K-flat.
Specializing to the preorder category `ℕ` recovers the sequential-colimit case. -/
theorem isKFlat_colimit_of_isFiltered
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ)
    [HasColimit F]
    (hF : ∀ i : I, (F.obj i).IsKFlat) :
    (colimit F).IsKFlat := sorry

end CochainComplex
