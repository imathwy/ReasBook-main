import Mathlib.RingTheory.Kaehler.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Domain triage:
- primary domain: Kähler differentials and finite generation over finite type algebras;
- sampled owner declarations:
  `KaehlerDifferential`,
  `KaehlerDifferential.D`,
  `KaehlerDifferential.ideal_fg`,
  `KaehlerDifferential.finite`;
- best owner abstraction: the canonical owner is the mathlib instance
  `KaehlerDifferential.finite : Module.Finite S Ω[S⁄R]`, whose primitive hypothesis is the weaker
  `Algebra.EssFiniteType R S`;
- layer: `bridge/view`, because this numbered item is the source-facing finite-type specialization
  of that owner instance, not new primitive data;
- primitive data: the `R`-algebra `S` and the finite type hypothesis on `R → S`;
- derived API: the finite `S`-module structure on `Ω[S⁄R]`.
-
The file should therefore expose only the source-facing instance consequence and not introduce any
parallel local theorem or wrapper around `KaehlerDifferential.finite`.
-/
/- Lemma 10.131.16: if `R → S` is of finite type, then the module of relative Kähler
differentials `Ω[S⁄R]` is a finite `S`-module. This is the canonical mathlib instance
`KaehlerDifferential.finite`, available under `Algebra.FiniteType`. -/
#check (inferInstance : Module.Finite S Ω[S⁄R])

end
