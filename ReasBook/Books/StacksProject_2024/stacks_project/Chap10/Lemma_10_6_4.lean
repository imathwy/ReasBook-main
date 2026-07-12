import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.FiniteType

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Algebra.FiniteType R S]

namespace Module.FinitePresentation

/- Domain-style sampling:
- primary domain: finite presentation of modules under change of scalars along a finite-type
  algebra map;
- sampled owner declarations:
  `Module.FinitePresentation`,
  `Module.Finite.of_restrictScalars_finite`,
  `Algebra.FiniteType.of_restrictScalars_finiteType`,
  `Module.FinitePresentation.trans`;
- best owner abstraction: `Module.FinitePresentation`;
- primitive data: an `S`-module structure on `M`, finite presentation of `M` over `R`, and the
  finite-type algebra map `R → S`;
- derived API: finite presentation of `M` over `S`, and downstream equivalences such as
  `Lemma_10_36_23` obtained by combining this bridge with `Module.FinitePresentation.trans`.

Source/core/bridge triage:
- `source-facing`: the scalar-restriction permanence statement below for finitely presented
  modules;
- `core/canonical`: the owner predicates `Module.FinitePresentation` and `Algebra.FiniteType`;
- `bridge/view`: this theorem upgrades the base-ring finite-presentation hypothesis to the
  algebra-ring finite-presentation conclusion. There is no upstream exact theorem with this
  interface, so the chapter keeps this bridge theorem instead of replacing it by a recall item.
-/
/-
Proof sketch: finite type means the `S`-action on `M` is controlled by finitely many algebra
generators of `S` over `R`. Inside `Hom_R(M, -)`, the condition that an `R`-linear map is
`S`-linear is therefore cut out by finitely many commutation equalities. Since `M` is finitely
presented over `R`, these finite equalizer conditions preserve filtered colimits, which upgrades
the `R`-finite-presentation owner to `Module.FinitePresentation S M`.
-/
variable (R)

/-- Lemma 10.6.4 (0561): if `R → S` is of finite type and an `S`-module `M` is finitely
presented over `R`, then `M` is finitely presented over `S`. -/
theorem of_restrictScalars_finiteType [Module.FinitePresentation R M] :
    Module.FinitePresentation S M := sorry

end Module.FinitePresentation

end
