import stacks_project.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u v

namespace CochainComplex

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [MonoidalCategory C] [MonoidalPreadditive C] [(curriedTensor C).Additive]
  [∀ X : C, ((curriedTensor C).obj X).Additive]
  [∀ (K L : CochainComplex C ℤ), CochainComplex.HasMapBifunctor K L (curriedTensor C)]

/- Domain sampling pass:
* primary domain: K-flat cochain complexes in a monoidal preadditive category and their totalized
  tensor product on `CochainComplex C ℤ`;
* sampled owner declarations:
  - `CochainComplex.IsKFlat` from `Definition_15_59_1`, the source-facing owner predicate;
  - `CochainComplex.isKFlat_iff` from `Definition_15_59_1`, the canonical eliminator exposing only
    the acyclicity-preservation content of that owner;
  - `HomologicalComplex.tensorObj`, the canonical tensor construction on cochain complexes whose
    K-flatness is the mathematical content of this lemma;
  - mathlib's `HomologicalComplex.monoidalCategory`, whose tensor notation `K ⊗ L` is a derived
    surface only under stronger ambient hypotheses than this lemma assumes;
  - the ringed-space and ringed-site specializations later in the project, which should be derived
    by specialization from this owner theorem rather than carried as parallel owners.

Source/core/bridge triage:
* `source-facing`: the tensor-closure statement for K-flat cochain complexes in the ambient
  monoidal category;
* `core/canonical`: `CochainComplex.IsKFlat` together with `HomologicalComplex.tensorObj`;
* `bridge/view`: the later ringed-space and ringed-site specializations.

Primitive data are only the two K-flatness hypotheses `hK` and `hL`. The tensor product
`HomologicalComplex.tensorObj K L` is canonical derived structure, so this file should expose only
the owner-level closure theorem and not introduce any auxiliary wrapper for tensor-K-flat data.
The raw `tensorObj` spelling is also the right public surface here: replacing it by monoidal
notation would silently strengthen the ambient API by demanding a `MonoidalCategory` instance on
cochain complexes instead of only the tensor data used by `IsKFlat`.
-/

-- Proof sketch: for any acyclic complex `M^•`, use the associativity isomorphism for totalized
-- tensor products to identify `Tot(M^• ⊗ Tot(K^• ⊗ L^•))` with
-- `Tot(Tot(M^• ⊗ K^•) ⊗ L^•)`. K-flatness of `K^•` makes the inner total tensor acyclic, and
-- then K-flatness of `L^•` finishes.
/-- Lemma 15.59.4: if `K^•` and `L^•` are K-flat cochain complexes in a monoidal preadditive
category, then the totalized tensor product `\mathrm{Tot}(K^• \otimes L^•)` is again K-flat. -/
theorem tensorObj_isKFlat_of_isKFlat
    (K L : CochainComplex C ℤ) (hK : K.IsKFlat) (hL : L.IsKFlat) :
    IsKFlat (HomologicalComplex.tensorObj K L) := sorry

end

end CochainComplex
