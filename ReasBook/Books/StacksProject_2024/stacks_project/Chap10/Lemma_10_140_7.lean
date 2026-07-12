import Mathlib
import Mathlib.Tactic.TFAE
import StacksProject_2024.Chap10.Lemma_10_140_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace Algebra

section

variable {k : Type u} {S : Type v}
variable [Field k] [CharZero k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-
Domain-style sampling for Lemma 10.140.7:
- primary domain: primewise smoothness criteria for finite type algebras over a characteristic-zero
  field, organized around the local owner `Localization.AtPrime q`;
- sampled owner declarations:
  `Algebra.IsSmoothAt`,
  `Algebra.FormallySmooth.projective_kaehlerDifferential`,
  `KaehlerDifferential.finite`,
  `isSmoothAt_iff_isRegularLocalRing_of_separable_residueField`;
- best owner abstraction: the canonical owner is the ideal-level smoothness predicate
  `IsSmoothAt k q` for a prime ideal `q : Ideal S`; the `PrimeSpectrum S` wrapper carried no extra
  mathematical data here, so the public theorem should live directly on `q`, with the localized
  Kähler module and the regular-local condition as derived views of the same owner local ring
  `Localization.AtPrime q`;
- primitive data: a prime ideal `q : Ideal S`;
- derived API: the finite/free condition on `Ω[Localization.AtPrime q⁄k]` and the regular-local
  condition on `Localization.AtPrime q`.

Source/core/bridge triage:
- `source-facing`: the three-way Stacks criterion relating smoothness, finite freeness of the local
  Kähler module, and regularity of the local ring;
- `core/canonical`: `IsSmoothAt k q`, equivalently `FormallySmooth k (Localization.AtPrime q)`,
  together with `IsRegularLocalRing (Localization.AtPrime q)`;
- `bridge/view`: the finite/free Kähler-differential clause, which is derived from the local smooth
  owner rather than a second owner abstraction.
-/

variable (q : Ideal S) [q.IsPrime]

local notation "S_q" => Localization.AtPrime q
local notation "Ω_q" => Ω[S_q⁄k]

-- Proof sketch: under characteristic `0`, the residue-field extension `q.ResidueField / k` is
-- separable by the chapter's perfect-field owner, so Lemma `10.140.5` identifies smoothness at
-- `q` with regularity of `S_q`. If `S_q` is smooth over `k`, then `S_q` is formally smooth and
-- essentially of finite type, so `Ω_q` is finite and projective; since `S_q` is local, this makes
-- `Ω_q` free. The converse from finite freeness of `Ω_q` to regularity is the genuinely new local
-- argument of the present lemma.
/-- Lemma 10.140.7: let `k` be a field of characteristic `0`, let `S` be a finite type
`k`-algebra, and let `q` be a prime ideal of `S`. The following are equivalent: `(1)` `S` is
smooth at `q` over `k`, i.e. `IsSmoothAt k q`; `(2)` the localized module of Kähler differentials
`Ω[Localization.AtPrime q⁄k]` is finite free over `Localization.AtPrime q`; and `(3)` the local
ring `Localization.AtPrime q` is regular. -/
theorem isSmoothAt_tfae_finite_free_kaehlerDifferential_isRegularLocalRing_of_charZero :
    List.TFAE
      [ IsSmoothAt k q
      , Module.Finite S_q Ω_q ∧ Module.Free S_q Ω_q
      , IsRegularLocalRing S_q
      ] := by
  tfae_have 1 ↔ 3 := by
    letI : PerfectField k := PerfectField.ofCharZero
    letI : IsSeparableOver k q.ResidueField := inferInstance
    simpa using
      (isSmoothAt_iff_isRegularLocalRing_of_separable_residueField q)
  tfae_have 1 → 2 := by
    intro hsmooth
    letI : FormallySmooth k S_q := hsmooth
    letI : Algebra.EssFiniteType S S_q := .of_isLocalization _ q.primeCompl
    letI : Algebra.EssFiniteType k S_q := .comp _ S _
    letI : Module.Flat S_q Ω_q := Module.Flat.of_projective
    exact ⟨inferInstance, Module.free_of_flat_of_isLocalRing⟩
  tfae_have 2 → 3 := by
    intro hOmega
    sorry
  tfae_finish

end

end Algebra
