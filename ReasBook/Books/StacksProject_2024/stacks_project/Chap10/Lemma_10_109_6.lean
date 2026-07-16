import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_55_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling:
* primary domain: projective dimension together with bounded finite-projective resolutions of
  `ModuleCat R`;
* sampled owner declarations:
  `FiniteProjectiveModuleCat`,
  `finiteProjectiveModuleProperty`,
  `HasProjectiveDimensionLE`,
  `HasFiniteProjectiveResolutionLengthLE`;
* best owner abstraction: the bounded resolution is source-facing, but its terms should live in the
  canonical owner `FiniteProjectiveModuleCat R`, and the ambient module should be `M : ModuleCat R`
  rather than a raw type with repeated module structure fields;
* layer triage:
  `FiniteProjectiveModuleCat R` is `core/canonical`,
  `ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms` below is `source-facing`,
  the final equivalence with `HasProjectiveDimensionLE` is a `bridge/view`;
* primitive data: the finite exact sequence ending in `M`;
* derived API: finiteness and projectivity of the terms, supplied by the owner category rather than
  stored as separate primitive fields.
-/

namespace ModuleCat

/-- A finite projective resolution of `M` of length at most `d` whose terms are finite
`R`-modules. In degree `0`, this means that `M` itself is finite projective. -/
def HasFiniteProjectiveResolutionLengthLEWithFiniteTerms (M : ModuleCat.{v} R) (d : ℕ) : Prop :=
  match d with
  | 0 => Module.Projective R M ∧ Module.Finite R M
  | n + 1 =>
      ∃ (P : Fin (n + 2) → FiniteProjectiveModuleCat R)
        (δ : (i : Fin (n + 1)) → P i.succ ⟶ P i.castSucc)
        (π : (P 0).obj ⟶ M),
          Function.Surjective π ∧
            Function.Exact (δ 0).hom π ∧
            (∀ i : Fin n, Function.Exact (δ i.succ).hom (δ i.castSucc).hom) ∧
            Function.Injective (δ (Fin.last n)).hom

-- Proof sketch: unfold `HasFiniteProjectiveResolutionLengthLEWithFiniteTerms`; the `d = 0` branch
-- is defined to be the conjunction of projectivity and finite generation of `M`.
/-- In degree `0`, a finite-term projective resolution is exactly the assertion that `M` is a
finite projective `R`-module. -/
theorem hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff (M : ModuleCat.{v} R) :
    HasFiniteProjectiveResolutionLengthLEWithFiniteTerms M 0 ↔
      Module.Projective R M ∧ Module.Finite R M :=
  Iff.rfl

end ModuleCat

section

variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: combine Lemma `10.109.4`, which identifies projective dimension `≤ d` with the
-- existence of a bounded projective resolution, with Lemma `10.71.1`, which provides a finite
-- free resolution of `M`; the `d`th syzygy is then finite as a submodule of a finite free module
-- over a Noetherian ring, so the projective top term may be replaced by that finite syzygy.
/-- Lemma 10.109.6: for a finite module `M` over a Noetherian ring `R`, having projective
dimension at most `d` is equivalent to admitting a resolution
`0 ⟶ P_d ⟶ P_{d-1} ⟶ ⋯ ⟶ P₀ ⟶ M ⟶ 0`
in which every `Pᵢ` is a finite projective `R`-module. -/
theorem hasProjectiveDimensionLE_iff_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
    [IsNoetherianRing R] [Module.Finite R M] (d : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of R M) d ↔
      ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms (ModuleCat.of R M) d := sorry

end
end
