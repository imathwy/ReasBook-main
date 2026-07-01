import Mathlib
import stacks_project.Chap10.Lemma_10_155_1
import stacks_project.Chap10.Lemma_10_155_2
import stacks_project.Chap15.Lemma_15_45_3
import stacks_project.Chap15.Lemma_15_51_3
import stacks_project.Chap15.Lemma_15_51_7

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable (P : FieldAlgebraProperty)
variable [P.HasPropertyB]
variable [FieldAlgebraProperty.HasPropertyC P] [FieldAlgebraProperty.HasPropertyD P]
variable [P.HasPropertyE]

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain sampling pass:
- primary domain: permanence of the Chapter 15 owner `IsPRing P R` under henselization and strict
  henselization of Noetherian local rings;
- sampled owner declarations:
  `IsPRing`,
  `FieldAlgebraProperty.HasPropertyE`,
  `isPRing_henselizationRing`,
  `strictHenselization_over_henselization_isStrictHenselizationOf`;
- best owner abstraction: the source-facing conclusions are owner statements `IsPRing P Rh` and
  `IsPRing P Rsh`; clause `(E)` already has the canonical owner `P.HasPropertyE`, so it should
  not reappear as a duplicate theorem argument;
- primitive data: a Noetherian local `P`-ring `R` together with chosen henselization and strict
  henselization owners;
- derived API: the paired conjunction theorem below, assembled from the two atomic owner-level
  consequences.

Source/core/bridge triage:
- `source-facing`: the permanence statements for henselization and strict henselization;
- `core/canonical`: `IsPRing` and `P.HasPropertyE`;
- `bridge/view`: the canonical pair-henselization theorem `isPRing_henselizationRing` and the
  comparison from a strict henselization over a henselization back to the base ring.
-/

-- Proof sketch: compare an arbitrary henselization `Rh` with the canonical pair-henselization
-- ring from Lemma `15.51.7` and transport the `P`-ring owner statement across that canonical
-- comparison.
/-- Lemma 15.51.8, henselization case: if `R` is a `P`-ring, where `P` satisfies `(B)`, `(C)`,
`(D)`, and `(E)`, then any henselization `Rh` of `R` is a `P`-ring. -/
theorem isPRing_henselization
    (hR : IsPRing P R) :
    IsPRing P Rh := by
  let _ : IsPRing P R := hR
  sorry

-- Proof sketch: use Lemma `15.51.4` to reduce to local formal fibers. For a prime `r` of `Rsh`
-- over `p ⊂ R`, Lemma `15.45.13` writes the fiber over `p` as a finite product of residue fields
-- and shows `κ(r) / κ(p)` is separable algebraic. Lemma `15.45.3` and Proposition `15.49.2`
-- identify the completion comparison `R^∧ → (R^sh)^∧` as regular, and then `(C)`, `(B)`, and
-- `(E)` transfer property `P` from the formal fibers of `R` to those of `Rsh`.
/-- Lemma 15.51.8, strict-henselization case: if `R` is a `P`-ring, where `P` satisfies `(B)`,
`(C)`, `(D)`, and `(E)`, then any strict henselization `Rsh` of `R` is a `P`-ring. -/
theorem isPRing_strictHenselization
    (hR : IsPRing P R) :
    IsPRing P Rsh := by
  let _ : IsPRing P R := hR
  sorry

/-- Lemma 15.51.8: if `R` is a `P`-ring, where `P` satisfies `(B)`, `(C)`, `(D)`, and `(E)`,
then any henselization `Rh` and any strict henselization `Rsh` of `R` are `P`-rings. -/
theorem isPRing_henselization_and_strictHenselization
    (hR : IsPRing P R) :
    IsPRing P Rh ∧ IsPRing P Rsh := by
  exact ⟨isPRing_henselization P hR, isPRing_strictHenselization P hR⟩

end
