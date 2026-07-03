import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import stacks_project.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex MonoidalCategory

noncomputable section

universe v u

section

variable {C : Type u} [Category.{v} C]
variable [Preadditive C] [HasZeroObject C] [CategoryWithHomology C]
variable [MonoidalCategory C] [MonoidalPreadditive C]

variable (K : CochainComplex C ℤ)
variable [∀ X : CochainComplex C ℤ, CochainComplex.HasMapBifunctor X K (curriedTensor C)]

/- Domain-style sampling:
- primary domain: quasi-isomorphism invariance of totalized tensoring by a fixed K-flat cochain
  complex;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `HomologicalComplex.HasTensor`,
  `tensorHom`,
  `QuasiIso`,
  `Functor.map`;
- best owner abstraction: the source-facing owner map is the canonical tensor morphism
  `tensorHom f (𝟙 K)` induced by fixed-right totalized tensoring with `K`, rather than a separate
  local functor wrapper;
- primitive vs derived:
  primitive data are the complex `K`, the source morphism `f`, and the K-flat/quasi-isomorphism
  hypotheses;
  the tensor-induced morphism `tensorHom f (𝟙 K)` is derived API from fixed-right tensoring;
- source/core/bridge triage:
  `source-facing`: the quasi-isomorphism preservation statement from Lemma 15.59.2;
  `core/canonical`: `CochainComplex.IsKFlat`, `tensorHom`, and `QuasiIso`;
  `bridge/view`: the functorial interpretation of `tensorHom f (𝟙 K)` as the map induced by
    fixed-right tensoring on the homotopy category. -/

/-- Lemma 15.59.2: if `K^\bullet` is a K-flat cochain complex in a monoidal preadditive category,
then for every quasi-isomorphism `f : L^\bullet ⟶ M^\bullet`, the induced tensor map
`\mathrm{Tot}(f \otimes \mathrm{id}_{K^\bullet}) = tensorHom f (\mathrm{id}_{K^\bullet})` is again
a quasi-isomorphism. -/
-- Proof sketch: identify the cone of `tensorHom f (𝟙 K)` with the totalized tensor of the cone
-- of `f` with `K`. If `f` is a quasi-isomorphism, its cone is acyclic, and K-flatness of `K`
-- keeps that tensor cone acyclic.
theorem tensorHom_right_quasiIso_of_isKFlat
    (hK : K.IsKFlat)
    {L M : CochainComplex C ℤ} (f : L ⟶ M) (hf : QuasiIso f) :
    QuasiIso (tensorHom f (𝟙 K)) :=
  sorry

end
