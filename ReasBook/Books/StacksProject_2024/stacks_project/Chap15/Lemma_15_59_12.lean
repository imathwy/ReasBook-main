import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import StacksProject_2024.Chap15.Lemma_15_58_1
import StacksProject_2024.Chap15.Lemma_15_59_2
import StacksProject_2024.Chap15.Lemma_15_59_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape MonoidalCategory

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

/-
Domain sampling pass:
* primary domain: K-flat cochain complexes of `R`-modules and quasi-isomorphism invariance of the
  totalized tensor product;
* sampled owner declarations:
  - `CochainComplex.IsKFlat` from `Definition_15_59_1`, the chapter owner for the source-facing
    K-flatness predicate;
  - `SymmetricCategory (CochainComplex (ModuleCat R) ℤ)` from `Lemma_15_58_1`, the chapter owner
    that identifies left tensoring with right tensoring via the canonical braiding `β_`;
  - `tensorHom_right_quasiIso_of_isKFlat` from `Lemma_15_59_2`, the chapter owner for
    quasi-isomorphism invariance after tensoring with a fixed K-flat right factor;
  - `CochainComplex.exists_epi_kFlatResolution` from `Lemma_15_59_10`, the chapter owner for the
    K-flat resolution used to reduce the arbitrary left tensor factor to the K-flat case;
  - `HomologicalComplex.tensorHom`, the canonical
    owner abstraction for the induced morphism on totalized tensor products of complexes.

Source/core/bridge triage:
* `source-facing`: the quasi-isomorphism invariance of `Tot(L^• ⊗_R -)` on a quasi-isomorphism
  `α : P^• ⟶ Q^•` between K-flat complexes;
* `core/canonical`: `CochainComplex.IsKFlat`, `tensorHom (𝟙 L) α`, and the symmetric-monoidal
  braiding `β_`;
* `bridge/view`: the right-tensor quasi-isomorphism owner of `Lemma_15_59_2` and the K-flat
  resolution owner of `Lemma_15_59_10`, used to justify the left-tensor statement.

Primitive data are only the complexes `L`, `P`, `Q`, the morphism `α`, and the K-flat/quasi-iso
hypotheses. The induced tensor morphism and the symmetry comparison maps are derived API from the
monoidal owners, so the theorem surface should use `tensorHom (𝟙 L) α` rather than restating the
underlying `mapBifunctorMap` machinery or packaging the braiding into a separate local wrapper.
-/

-- Proof sketch: choose a termwise-epimorphic K-flat resolution `K^• ⟶ L^•` from Lemma `15.59.10`.
-- Lemma `15.59.2` gives quasi-isomorphisms on the vertical maps after tensoring with `P^•` and
-- `Q^•`, and also on the top horizontal map after tensoring the quasi-isomorphism `α` with the
-- K-flat complex `K^•`. The commutative square then shows that the bottom horizontal map is a
-- quasi-isomorphism.
/-- Lemma 15.59.12: if `α : P^• ⟶ Q^•` is a quasi-isomorphism between K-flat cochain complexes of
`R`-modules, then for every cochain complex `L^•` the induced map
`\mathrm{Tot}(\mathrm{id}_{L^•} \otimes \alpha) :
\mathrm{Tot}(L^• \otimes_R P^•) ⟶ \mathrm{Tot}(L^• \otimes_R Q^•)` is a quasi-isomorphism. -/
theorem quasiIso_totalizedTensor_map_right_of_quasiIso_of_isKFlat
    (L P Q : CochainComplex (ModuleCat R) ℤ)
    (hP : P.IsKFlat) (hQ : Q.IsKFlat)
    (α : P ⟶ Q) (hα : QuasiIso α) :
    QuasiIso (tensorHom (𝟙 L) α) := by
  obtain ⟨K, π, hK, _, hπ, _⟩ := CochainComplex.exists_epi_kFlatResolution L
  have hπP : QuasiIso (tensorHom π (𝟙 P)) :=
    tensorHom_right_quasiIso_of_isKFlat P hP π hπ
  have hπQ : QuasiIso (tensorHom π (𝟙 Q)) :=
    tensorHom_right_quasiIso_of_isKFlat Q hQ π hπ
  have hKα_right : QuasiIso (tensorHom α (𝟙 K)) :=
    tensorHom_right_quasiIso_of_isKFlat K hK α hα
  have hKα : QuasiIso (tensorHom (𝟙 K) α) := by
    have hcomp : QuasiIso (tensorHom (𝟙 K) α ≫ (β_ K Q).hom) := by
      letI : QuasiIso ((β_ K P).hom) := inferInstance
      letI := hKα_right
      simpa [BraidedCategory.braiding_naturality_right K α] using
        (quasiIso_comp ((β_ K P).hom) (tensorHom α (𝟙 K)))
    letI : QuasiIso ((β_ K Q).hom) := inferInstance
    letI := hcomp
    exact quasiIso_of_comp_right (tensorHom (𝟙 K) α) (β_ K Q).hom
  have hsquare :
      tensorHom π (𝟙 P) ≫ tensorHom (𝟙 L) α =
        tensorHom (𝟙 K) α ≫ tensorHom π (𝟙 Q) := by
    simpa using (((curriedTensor (CochainComplex (ModuleCat R) ℤ)).map π).naturality α).symm
  have hcomp : QuasiIso (tensorHom π (𝟙 P) ≫ tensorHom (𝟙 L) α) := by
    letI := hKα
    letI := hπQ
    have hcomp' : QuasiIso (tensorHom (𝟙 K) α ≫ tensorHom π (𝟙 Q)) :=
      quasiIso_comp (tensorHom (𝟙 K) α) (tensorHom π (𝟙 Q))
    rw [← hsquare] at hcomp'
    exact hcomp'
  letI := hπP
  letI := hcomp
  exact quasiIso_of_comp_left (tensorHom π (𝟙 P)) (tensorHom (𝟙 L) α)

end
