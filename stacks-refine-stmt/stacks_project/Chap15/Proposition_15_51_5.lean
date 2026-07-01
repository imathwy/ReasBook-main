import Mathlib
import stacks_project.Chap15.Lemma_15_51_3
import stacks_project.Chap15.Lemma_15_51_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/- Domain sampling pass:
- primary domain: permanence of the Chapter 15 `P`-ring formal-fiber condition under essentially
  finite type algebra maps;
- sampled owner declarations:
  `IsPRing`,
  `FieldAlgebraProperty.HasPropertyA`,
  `FieldAlgebraProperty.HasPropertyB`,
  `FieldAlgebraProperty.HasPropertyC`,
  `FieldAlgebraProperty.HasPropertyD`,
  `isPRing_of_quasiFinite`,
  `isPRing_iff_localFormalFibersHaveProperty_atMaximal`;
- best owner abstraction: the source-facing owner is `IsPRing P R`; the theorem should stay on
  that owner and reuse the Chapter 15 permanence axioms as inferable classes, rather than
  expanding the prime-pair condition or carrying redundant Noetherian hypotheses in the public
  interface;
- primitive data: the `R`-algebra `S`, the essentially finite type hypothesis, the four transfer
  axioms `(A)` through `(D)` on `P`, and the owner input `hR : IsPRing P R`;
- derived API: the resulting owner conclusion `IsPRing P S`.

Source/core/bridge triage:
- `source-facing`: `isPRing_of_essFiniteType`;
- `core/canonical`: `IsPRing` together with the owner axioms `P.HasPropertyA`, `P.HasPropertyB`,
  `P.HasPropertyC`, and `P.HasPropertyD`;
- `bridge/view`: `isPRing_of_quasiFinite` and
  `isPRing_iff_localFormalFibersHaveProperty_atMaximal`, which supply the canonical local and
  quasi-finite reductions used by the proof strategy.
-/
variable (P : FieldAlgebraProperty)
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
variable [P.HasPropertyA] [P.HasPropertyB] [P.HasPropertyC] [P.HasPropertyD]

-- Proof sketch: reduce by `isPRing_iff_localFormalFibersHaveProperty_atMaximal` to the local
-- rings `S_m` at maximal ideals of `S`. Present each `S_m` as essentially finite type over the
-- corresponding localization of `R`, use the quasi-finite permanence theorem `isPRing_of_quasiFinite`
-- from Lemma `15.51.3` together with axioms `(A)` and `(B)` to handle the finite-type part, and
-- then apply axioms `(C)` and `(D)` through Lemma `15.51.4` to descend the comparison on formal
-- fibers.
/-- Proposition 15.51.5: if `R` is a `P`-ring and `R → S` is essentially of finite type, where
`P` satisfies `(A)`, `(B)`, `(C)`, and `(D)`, then `S` is again a `P`-ring. -/
theorem isPRing_of_essFiniteType
    (hR : IsPRing P R) :
    IsPRing P S := sorry

end
