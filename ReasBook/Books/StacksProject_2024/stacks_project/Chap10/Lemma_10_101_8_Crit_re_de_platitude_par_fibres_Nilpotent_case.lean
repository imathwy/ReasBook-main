import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap10.«Lemma_10_101_8_Critère_de_platitude_par_fibres_Nilpotent_case»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {I : Ideal R}
variable {M : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

local notation "IS" => Ideal.map (algebraMap R S) I
local notation "Mbar" => M ⧸ (IS • (⊤ : Submodule S M))

/- Domain-style sampling for the nilpotent fiberwise flatness criterion:
- primary domain: flatness of modules and algebra maps across a nilpotent thickening `R → S`,
  together with prime-local detection via nontrivial residue-field fibers;
- sampled owner declarations of the same kind:
  `flat_over_target_of_nilpotent_of_flat_over_base_and_flat_mod_extended_ideal`,
  `atPrime_flat_of_flat_module_and_nontrivial_fiber`,
  `Module.Flat`,
  `RingHom.Flat`;
- best owner abstraction: the canonical owners are `Module.Flat` for module flatness and
  `RingHom.Flat` for the localized algebra map; the quotient `Mbar` over `S ⧸ IS` is bridge data,
  not a second owner object.

Primitive data vs. derived API:
- primitive data: the nilpotent ideal `I`, the `S`-module `M` with its restricted `R`-module
  structure, flatness of `M` over `R`, and flatness of the quotient fiber `Mbar` over `S ⧸ IS`;
- derived API: flatness of `M` over `S`, and then flatness of each localized map
  `R → Localization.AtPrime q.asIdeal`.

Source/core/bridge triage:
- `source-facing`: clause `(2)` below, which packages the nilpotent assumptions of clause `(1)`
  with the prime-fiber hypothesis;
- `core/canonical`: the upstream owner theorems
  `flat_over_target_of_nilpotent_of_flat_over_base_and_flat_mod_extended_ideal` and
  `atPrime_flat_of_flat_module_and_nontrivial_fiber`;
- `bridge/view`: the quotient fiber `Mbar` and the specialization from the flat-over-`S` owner to
  the source-facing localized statement.
-/

/- Lemma 10.101.8 (1): exact-interface reuse of the upstream owner theorem for the nilpotent
fiberwise flatness criterion. -/
recall flat_over_target_of_nilpotent_of_flat_over_base_and_flat_mod_extended_ideal

-- Proof sketch: first apply clause `(1)` via the upstream owner theorem to get flatness of `M`
-- over `S`. Then use the prime-local owner theorem `atPrime_flat_of_flat_module_and_nontrivial_fiber`
-- to pass from `R`-flatness of `M`, `S`-flatness of `M`, and the nontrivial fiber at `q` to
-- flatness of `Localization.AtPrime q.asIdeal` over `R`.
/-- Lemma 10.101.8 (2): if `I` is nilpotent, `M / ISM` is flat over `S / IS`, `M` is flat over
`R`, and the fiber `M ⊗[S] κ(q)` is nontrivial, then the localization `S_q` is flat over `R`. -/
theorem localized_flat_over_R_of_nilpotent_of_flat_quotient_and_nontrivial_fiber
    (hI : IsNilpotent I)
    (hflat_mod : Module.Flat (S ⧸ IS) Mbar)
    (hflat_R : Module.Flat R M)
    (q : PrimeSpectrum S)
    (hq : Nontrivial (M ⊗[S] q.asIdeal.ResidueField)) :
    (algebraMap R (Localization.AtPrime q.asIdeal)).Flat := by
  have hflat_S :
      Module.Flat S M :=
    flat_over_target_of_nilpotent_of_flat_over_base_and_flat_mod_extended_ideal
      hI hflat_mod hflat_R
  exact atPrime_flat_of_flat_module_and_nontrivial_fiber q hflat_R hflat_S hq

end
