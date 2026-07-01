import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [FinitePresentation R S]

/- Domain-style sampling:
- primary domain: local étaleness criteria for finitely presented ring maps;
- sampled owner declarations:
  `Algebra.IsEtaleAt`,
  `Algebra.IsUnramifiedAt`,
  `Algebra.isUnramifiedAt_iff_map_eq`,
  `[Algebra.IsUnramifiedAt R q] → Module.Finite p.ResidueField q.ResidueField`,
  `Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat`,
  `Algebra.IsSmoothAt.of_formallySmooth_fiber`;
- best owner abstraction: `Algebra.IsEtaleAt R q` is the canonical local owner.

Source/core/bridge triage:
- `source-facing`: the Stacks local criterion for étaleness at `q`;
- `core/canonical`: the owner predicates `IsEtaleAt`, `IsUnramifiedAt`, and `IsSmoothAt`;
- `bridge/view`: the local flatness hypothesis together with the maximal-ideal equality and the
  separable residue-field extension.

Primitive data vs. derived API:
- primitive data: local flatness of `R_p → S_q`, the equality `pS_q = 𝔪_{S_q}`, and separability
  of `κ(q) / κ(p)`;
- derived API: local unramifiedness, finiteness of `κ(q) / κ(p)`, local smoothness, and hence
  local étaleness.

This file should keep the bridge theorem rather than collapse to the sampled owner theorem
`Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat`, because that owner theorem assumes global
flatness `Module.Flat R S`, while the source statement only assumes flatness of the localized map
`R_p → S_q`.
-/
-- Proof sketch: use `Algebra.isUnramifiedAt_iff_map_eq` to deduce that `R → S` is unramified at
-- `q` from the equality `pS_q = 𝔪_{S_q}` and the separability of `κ(q) / κ(p)`. The flat-local
-- and finite-presentation hypotheses then give smoothness at `q` by the smooth-fiber criterion;
-- once unramifiedness is known, mathlib's local unramified API supplies the finiteness of
-- `κ(q) / κ(p)`, so the fiber identifies with a finite separable field extension. Combine
-- smoothness and unramifiedness to conclude étaleness at `q`.
/-- Lemma 10.143.7: let `q` be a prime of `S` lying over a prime `p` of `R`. If `R → S` is of
finite presentation, the localized map `R_p → S_q` is flat, `p S_q` is the maximal ideal of the
local ring `S_q`, and the residue field extension `κ(q) / κ(p)` is separable, then `R → S` is
étale at `q`; the finiteness of `κ(q) / κ(p)` is automatic from these hypotheses. -/
theorem isEtaleAt_of_flat_localRingHom_of_map_eq_maximalIdeal_of_separableResidueField
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hflat : (Localization.localRingHom p q (algebraMap R S) (q.over_def p)).Flat)
    (hmax : p.map (algebraMap R (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q))
    [Algebra.IsSeparable p.ResidueField q.ResidueField] :
    IsEtaleAt R q := sorry

end

end Algebra
