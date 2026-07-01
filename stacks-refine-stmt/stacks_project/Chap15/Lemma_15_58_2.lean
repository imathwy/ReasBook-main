import Mathlib.Algebra.Homology.BifunctorHomotopy

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 15.58.2:
- primary domain: homotopy transport along totalized tensor-product maps for cochain complexes;
- sampled owner declarations:
  `HomologicalComplex.mapBifunctorMapHomotopy₁`,
  `Functor.map₂CochainComplex`,
  `Functor.mapHomotopyCategory`;
- best owner abstraction: the core/canonical owner is
  `HomologicalComplex.mapBifunctorMapHomotopy₁`, while the induced homotopy-category functor is
  the canonical owner `((tensor.map₂CochainComplex).flip.obj Y).mapHomotopyCategory (up ℤ)`;
- source/core/bridge triage:
  `source-facing`: the fixed-right-factor tensor homotopy statement from the text;
  `core/canonical`: `HomologicalComplex.mapBifunctorMapHomotopy₁`,
    `Functor.mapHomotopyCategory`;
  `bridge/view`: none;
- layer: `bridge/view`; Lemma 15.58.2 is only the `ModuleCat R` tensor specialization of the
  canonical homotopy-transport statement, so the refined file should reuse the upstream owner
  directly rather than keep a second public definition with the same interface;
- primitive data: a bilinear bifunctor, a fixed right complex, and a homotopy in the varying left
  complex;
- derived API: the induced morphisms on totalized tensor products and their transported homotopy
  are already provided by the sampled owners above.
-/

/- Lemma 15.58.2: for the totalized tensor product with a fixed right factor, a homotopy
`α ∼ β` in the varying left complex induces a homotopy between the corresponding totalized tensor
maps. This is exactly the canonical owner `HomologicalComplex.mapBifunctorMapHomotopy₁`,
specialized in applications to `curriedTensor (ModuleCat R)`. -/
#check HomologicalComplex.mapBifunctorMapHomotopy₁
