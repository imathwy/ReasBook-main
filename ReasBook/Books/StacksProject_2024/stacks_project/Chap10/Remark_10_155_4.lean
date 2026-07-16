import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_2

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable {R : Type u} {Rh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

/-
Domain-style sampling pass for Remark 10.155.4.

Primary domain: local commutative algebra of henselizations, strict henselizations, and residue-
field comparison maps.

Sampled owner declarations:
* `IsHenselizationOf`;
* `IsHenselizationOf.residueFieldEquiv`;
* `IsStrictHenselizationOf`;
* `exists_henselization_to_strictHenselization`.

Best owner abstraction:
* source-facing owner data already live in `IsStrictHenselizationOf`;
* the chosen residue-field identification belongs to the bridge theorem
  `exists_henselization_to_strictHenselization`;
* the fact that a strict henselization over a henselization is again a strict henselization of the
  base is derived API and should not stay bundled as primitive existential data.

Primitive data vs. derived API:
* primitive data: a strict henselization of `Rh` together with the chosen residue-field
  identification with `Ksep`;
* derived API: the resulting `R`-algebra is also a strict henselization of `R`.

Source/core/bridge triage:
* `source-facing`: `exists_strictHenselization_of_henselization`;
* `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`,
  `IsHenselizationOf.residueFieldEquiv`, `exists_henselization_to_strictHenselization`;
* `bridge/view`: `strictHenselization_over_henselization_isStrictHenselizationOf`.
-/

-- Proof sketch: transport the filtered-colimit-of-étale and maximal-ideal conditions from
-- `Rh → Rsh` back along the henselization map `R → Rh`, and obtain strict henselianity of `Rsh`
-- over `R` from the same underlying local ring together with the unchanged separably closed
-- residue field.
/-- A strict henselization over a henselization is again a strict henselization of the base local
ring. This is the owner-level bridge behind Remark 10.155.4. -/
theorem strictHenselization_over_henselization_isStrictHenselizationOf
    {Rsh : Type u} [CommRing Rsh] [Algebra Rh Rsh] [Algebra R Rsh] [IsScalarTower R Rh Rsh]
    [IsStrictHenselizationOf Rh Rsh] :
    IsStrictHenselizationOf R Rsh := sorry

variable {Ksep : Type u}
variable [Field Ksep] [Algebra (ResidueField R) Ksep] [IsSepClosure (ResidueField R) Ksep]

-- Proof sketch: transport the chosen separable closure `Ksep` of `ResidueField R` across the
-- canonical residue-field isomorphism of the henselization `Rh`, then apply the strict
-- henselization existence theorem to `Rh`. The resulting `Rh`-algebra is strictly henselian with
-- residue field `Ksep`; viewed as an `R`-algebra through `R → Rh`, it is still a filtered colimit
-- of étale `R`-algebras, so Lemma `10.154.7` identifies it with the strict henselization of `R`.
/-- Remark 10.155.4: starting from a henselization `R → Rh` and a chosen separable closure `Ksep`
of `ResidueField R`, one can construct a strict henselization over `Rh`; the resulting `Rh`-algebra
has residue field identified with `Ksep` over `ResidueField R`. The companion theorem
`strictHenselization_over_henselization_isStrictHenselizationOf` records that the same `Rh`-algebra
is also a strict henselization of `R`. -/
theorem exists_strictHenselization_of_henselization :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra Rh Rsh)
      (_ : IsStrictHenselizationOf Rh Rsh) (ι : ResidueField Rsh ≃+* Ksep),
      ι.toRingHom.comp
          (ResidueField.map ((algebraMap Rh Rsh).comp (algebraMap R Rh))) =
        algebraMap (ResidueField R) Ksep := sorry

end
