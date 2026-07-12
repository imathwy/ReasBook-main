import Mathlib.RingTheory.Extension.Cotangent.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]

/- Domain triage:
- primary domain: Kähler differentials and cotangent-complex finiteness for finitely presented
  algebras;
- sampled owner declarations: `KaehlerDifferential`, `KaehlerDifferential.D`,
  `Module.FinitePresentation`, and the canonical instance
  `[Algebra.FinitePresentation R S] : Module.FinitePresentation S Ω[S⁄R]` from
  `RingTheory.Extension.Cotangent.Basic`;
- best owner abstraction: `Module.FinitePresentation S Ω[S⁄R]`;
- layer: `bridge/view`, since the source lemma is the derived finite-presentation statement for the
  canonical owner `Ω[S⁄R]`, not new primitive data;
- primitive data: the `R`-algebra `S` and the finite-presentation hypothesis on `R → S`;
- derived API: the finitely presented `S`-module structure on `Ω[S⁄R]`.
-/
/- Lemma 10.131.15: if `R → S` is of finite presentation, then the module of relative
Kahler differentials `Ω[S⁄R]` is a finitely presented `S`-module. This is exactly the canonical
mathlib instance for `KaehlerDifferential`. -/
#check (inferInstance : Module.FinitePresentation S Ω[S⁄R])

end
