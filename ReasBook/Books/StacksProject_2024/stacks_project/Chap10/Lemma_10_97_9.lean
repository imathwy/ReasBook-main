import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_96_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-
Domain triage:
- primary domain: adic completion of surjections and splitting of the completed short exact
  sequence;
- sampled owner-style declarations in this domain:
  `AdicCompletion.map_surjective`,
  `completionShortComplex_shortExact_of_flat_cokernel`,
  `projective_of_projective_quotient_of_isNilpotent_of_flat`,
  `Module.projective_lifting_property`;
- best owner abstraction: the completed surjection `AdicCompletion.map I g`, equivalently the
  completed short exact sequence furnished by `completionShortComplex_shortExact_of_flat_cokernel`;
  stagewise projectivity is only a proof-side bridge, not the public core.
- primitive data: the surjection `g : P →ₗ[R] M`, the ideal `I`, flatness of `M`, and the
  projective quotient hypothesis on `M ⧸ (I • ⊤)`;
- derived API: a section of the completed surjection `P^∧ → M^∧`.

Layer classification:
- `source-facing`: the public theorem below, stated as existence of a section of the completed
  surjection;
- `core/canonical`: `AdicCompletion.map`, `AdicCompletion.map_surjective`, and the completed short
  exact sequence API from Lemma `10.96.1`;
- `bridge/view`: the stagewise projectivity theorem
  `projective_of_projective_quotient_of_isNilpotent_of_flat`, used to build compatible splittings
  modulo `I ^ (n + 1)`.
-/

-- Proof sketch: for each `n`, apply Lemma `10.77.7` to the induced nilpotent ideal in
-- `R ⧸ I ^ (n + 1)` to show that `M ⧸ (I ^ (n + 1) • ⊤)` is projective over `R ⧸ I ^ (n + 1)`.
-- Hence the surjection `P ⧸ (I ^ (n + 1) • ⊤) → M ⧸ (I ^ (n + 1) • ⊤)` admits a section. Choose
-- these sections compatibly; passing to the inverse limit then yields a section of the completed
-- surjection `AdicCompletion.map I g`. Lemma `10.96.1` supplies the canonical completion map and
-- its surjectivity.
/-- Lemma 10.97.9: if `g : P → M` is a surjective `R`-linear map, `M` is flat, and `M / IM` is
projective over `R ⧸ I`, then the induced surjection on `I`-adic completions
`P^∧ → M^∧` admits an `AdicCompletion I R`-linear section. -/
theorem completionMap_has_section_of_flat_of_projective_quotient
    (g : P →ₗ[R] M) [Module.Flat R M] (hg : Function.Surjective g)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    ∃ s : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I P,
      (AdicCompletion.map I g).comp s = LinearMap.id := by
  sorry

end
