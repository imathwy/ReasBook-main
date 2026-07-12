import Mathlib.Algebra.Module.LocalizedModule.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: localization of modules and torsion-freeness over domains;
- sampled owner API:
  `Submodule.torsion`,
  `Submodule.QuotientTorsion.instIsTorsionFree`,
  `IsLocalizedModule.isTorsionFree`,
  the specialized `LocalizedModule` torsion-free instance;
- best owner abstraction: `IsLocalizedModule.isTorsionFree`;
- source-facing layer: the textbook specialization asserting that `LocalizedModule S M` is
  torsion-free over `Localization S`;
- core/canonical layer: `IsLocalizedModule.isTorsionFree`;
- bridge/view layer: specialize that theorem along `LocalizedModule.mkLinearMap S M`.

Primitive data are the base domain `R`, the `R`-module `M`, and the multiplicative set `S`.
Torsion-freeness of the localization is derived API already owned upstream, so this file should
reuse the named owner theorem rather than a parallel local wrapper or anonymous instance search.
-/

section

open Module

variable {R : Type u} [CommRing R] [IsDomain R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M] [IsTorsionFree R M]

/- Lemma 15.22.3: if `M` is a torsion-free module over a domain `R`, then for every
multiplicative set `S ⊆ R` the localized module `LocalizedModule S M` is torsion-free over
`Localization S`. Mathlib owns this through the general localized-module theorem
`IsLocalizedModule.isTorsionFree`, whose specialization to `LocalizedModule` is the source-facing
statement here. -/
#check (IsLocalizedModule.isTorsionFree (LocalizedModule.mkLinearMap S M) S :
  IsTorsionFree (Localization S) (LocalizedModule S M))

end
