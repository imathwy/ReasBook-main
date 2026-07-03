import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [Algebra.EssFiniteType R S]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/-
Domain-style sampling:
- primary domain: local quasi-finite algebra maps and Zariski-main finiteness over local rings;
- sampled owner declarations:
  `Ideal.Fiber`,
  `Algebra.QuasiFiniteAt`,
  `Algebra.EssFiniteType`,
  `Algebra.EssFiniteType.essFiniteType_iff_exists_subalgebra`,
  `exists_finite_subalgebra_of_integralClosure_with_zariskiMain_properties`;
- best owner abstraction: the closed fiber is the canonical owner `Ideal.Fiber`, and the decisive
  local finiteness condition is the owner predicate `Algebra.QuasiFiniteAt R (maximalIdeal S)`,
  while the source-facing finite-localization conclusion is organized through `Subalgebra R S`
  together with `IsLocalization`;
- source/core/bridge triage:
  `source-facing`: the existence of a finite `R`-subalgebra of `S` whose localization is `S`;
  `core/canonical`: `Ideal.Fiber`, `Algebra.QuasiFiniteAt`, `Algebra.EssFiniteType`,
    `Subalgebra R S`, and `IsLocalization`;
  `bridge/view`: the local closed-fiber hypotheses imply the canonical quasi-finite owner at
  `maximalIdeal S`, which then feeds the Zariski-main finite-localization argument;
- primitive data: the local map, the essentially finite type owner, the finite residue-field
  extension `ResidueField R → ResidueField S`, and the canonical closed fiber `ClosedFiber`;
- derived API: quasi-finiteness at `maximalIdeal S` and the resulting finite-subalgebra
  localization witness.
-/

/-- The local source hypotheses, including the finite residue-field extension
`ResidueField R → ResidueField S`, make `R → S` quasi-finite at the maximal ideal of `S`. -/
-- Proof sketch: write `S` as a localization of the canonical finite-type subalgebra supplied by
-- `Algebra.EssFiniteType`. Because `ClosedFiber` is a finite-type `ResidueField R`-algebra,
-- the hypothesis `hκ` and `ringKrullDim ClosedFiber = 0` match clause `(6)` of the isolated-point
-- criterion from Lemmas `10.122.1` and `10.122.4` for the unique point of the local closed fiber,
-- which is exactly the owner predicate `Algebra.QuasiFiniteAt R (maximalIdeal S)`.
theorem quasiFiniteAt_maximalIdeal_of_closedFiber_dimZero
    (hκ : Module.Finite (ResidueField R) (ResidueField S))
    (hdim : ringKrullDim ClosedFiber = 0) :
    Algebra.QuasiFiniteAt R (maximalIdeal S) := sorry

/-- Lemma 10.124.2: if `R → S` is a local homomorphism of local rings, `S` is essentially of
finite type over `R`, and the canonical closed fiber `ClosedFiber = κ(R) ⊗[R] S`, equivalently
`S ⧸ maximalIdeal R • S`, has Krull dimension zero, and the induced residue-field extension
`ResidueField R → ResidueField S` is finite, then `S` is the localization of a finite
`R`-subalgebra of `S`. -/
-- Proof sketch: first apply the previous theorem to obtain the canonical owner
-- `Algebra.QuasiFiniteAt R (maximalIdeal S)`. Present `S` by the canonical finite-type
-- subalgebra coming from `Algebra.EssFiniteType`, use Lemma `10.123.13` to shrink to a basic open
-- neighborhood on which the map is quasi-finite, and then apply Lemma `10.123.14` to replace
-- that neighborhood by the localization of a finite `R`-subalgebra of `S`.
theorem exists_finite_algebra_localization_of_essFiniteType_of_closedFiber_dimZero
    (hκ : Module.Finite (ResidueField R) (ResidueField S))
    (hdim : ringKrullDim ClosedFiber = 0) :
    ∃ (A : Subalgebra R S) (M : Submonoid A),
      Module.Finite R A ∧ IsLocalization M S := sorry

end
