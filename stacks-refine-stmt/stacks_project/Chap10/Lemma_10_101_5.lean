import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] [Algebra R R']
variable {I : Ideal R}
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: commutative algebra of flatness over nilpotent thickenings and injective base
  change;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `flat_quotient_comap_map_sq_of_flat_mod_ideal_and_flat_baseChange`,
  `flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes`,
  `Module.Flat.baseChange`;
- best owner abstraction: the canonical flatness predicate `Module.Flat`, with Chapter 10's
  quotient-flatness and nilpotent-ideal owners supplying the source-facing criterion;
- primitive data: the rings `R`, `R'`, the `R`-algebra structure on `R'`, the ideal `I`, and the
  `R`-module `M`;
- derived API: the flatness hypotheses on `M / IM` and `R' ⊗[R] M`, and the resulting flatness
  of `M`.

Layering:
- this item is `source-facing`: it is the textbook nilpotent-ideal criterion under an injective
  base change;
- its proof should reuse the `core/canonical` owners above rather than introduce any parallel
  flatness wrapper or alternate owner object;
- no additional `bridge/view` declaration is needed in this file.
-/

-- Proof sketch: define recursively the ideals `I₁ = I` and
-- `I_{n + 1} = comap φ ((map φ I_n)^2)` for `φ = algebraMap R R'`. Lemma `10.101.4` shows by
-- induction that each quotient `M / I_n M` is flat over `R / I_n`. Since `I` is nilpotent, the
-- images `φ(I_n)` eventually vanish; injectivity of `φ` then gives `I_n = 0` for some `n`, so the
-- flat quotient criterion yields flatness of `M` over `R`.
/-- Lemma 10.101.5: if `I` is nilpotent, `R → R'` is injective, `M / IM` is flat over `R / I`,
and the base change `R' ⊗[R] M` is flat over `R'`, then `M` is flat over `R`. -/
theorem flat_of_nilpotent_ideal_of_injective_algebraMap_of_flat_mod_ideal_and_flat_baseChange
    (hI : IsNilpotent I) (hinj : Function.Injective (algebraMap R R'))
    (hflat_mod_ideal : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (hflat_baseChange : Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat R M := sorry

end
