import stacks_proof.stacks_project.Chap12.Remark_12_18_4
import stacks_proof.stacks_project.Chap13.Remark_13_10_9
import stacks_proof.stacks_project.Chap15.Definition_15_59_1
import Mathlib.Tactic.StacksAttribute

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
/-- Helper for Lemma 15.59.4: acyclicity is preserved under isomorphisms of cochain complexes. -/
private theorem acyclic_of_iso
    {K L : CochainComplex C ℤ} (e : K ≅ L) (hK : K.Acyclic) :
    L.Acyclic := by
  -- Read acyclicity degreewise and transport each exactness witness across the complex isomorphism.
  intro n
  exact HomologicalComplex.ExactAt.of_iso (hK n) e

/-- Helper for Lemma 15.59.4: reassociating a triple total tensor product gives a canonical
isomorphism of cochain complexes. -/
-- TODO: instantiate `HomologicalComplex.mapBifunctorAssociator` for `curriedTensor C`.
-- The current blocker is the missing trifunctor colimit-preservation bridge
-- `HasGoodTrifunctor₁₂Obj/₂₃Obj` for the ambient assumptions in this file.
private noncomputable def tensorObj_assoc_iso
    (M K L : CochainComplex C ℤ) :
    HomologicalComplex.tensorObj M (HomologicalComplex.tensorObj K L) ≅
      HomologicalComplex.tensorObj (HomologicalComplex.tensorObj M K) L := sorry

/-- Helper for Lemma 15.59.4: tensoring an acyclic test complex with two K-flat complexes remains
acyclic after totalizing the iterated tensor product. -/
private theorem acyclic_tensorObj_tensorObj_of_isKFlat
    (M K L : CochainComplex C ℤ) (hM : M.Acyclic) (hK : K.IsKFlat) (hL : L.IsKFlat) :
    (HomologicalComplex.tensorObj M (HomologicalComplex.tensorObj K L)).Acyclic := by
  -- First tensor the acyclic test complex with `K`; K-flatness keeps the result acyclic.
  have hMK : (HomologicalComplex.tensorObj M K).Acyclic :=
    CochainComplex.acyclic_tensorObj_of_isKFlat hK hM
  -- Then tensor that already-acyclic complex with `L`; K-flatness of `L` closes the right-associated side.
  have hRight : (HomologicalComplex.tensorObj (HomologicalComplex.tensorObj M K) L).Acyclic :=
    CochainComplex.acyclic_tensorObj_of_isKFlat hL hMK
  -- Transport acyclicity back across the canonical reassociation isomorphism.
  exact acyclic_of_iso (tensorObj_assoc_iso (C := C) M K L).symm hRight

/-- Lemma 15.59.4: if `K^•` and `L^•` are K-flat cochain complexes in a monoidal preadditive
category, then the totalized tensor product `\mathrm{Tot}(K^• \otimes L^•)` is again K-flat. -/
@[stacks 0795]
theorem tensorObj_isKFlat_of_isKFlat
    (K L : CochainComplex C ℤ) (hK : K.IsKFlat) (hL : L.IsKFlat) :
    IsKFlat (HomologicalComplex.tensorObj K L) := by
  -- Unfold K-flatness and test the tensor product against an arbitrary acyclic complex `M`.
  rw [CochainComplex.isKFlat_iff]
  intro M _ hM
  -- The source-faithful route is: tensor with `K`, tensor again with `L`, then reassociate back.
  exact acyclic_tensorObj_tensorObj_of_isKFlat (C := C) M K L hM hK hL

end

end CochainComplex
