import Mathlib
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.SeparableClosure
import stacks_project.Chap10.Definition_10_153_1
import stacks_project.Chap10.Lemma_10_154_3
import stacks_project.Chap10.Lemma_10_155_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open CommRingCat
open IsLocalRing
open RingHom

universe u

section

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable (S : Type u) [CommRing S] [Algebra R S]

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations and strict henselizations;
- sampled owner declarations of the same kind:
  `StrictHenselianLocalRing`,
  `IsLocalHom`,
  `RingHom.IsFilteredColimitOfEtale`,
  `IsHenselizationOf`;
- best owner abstraction: there is no upstream bundled strict-henselization owner in mathlib, so
  the source-facing owner here is `IsStrictHenselizationOf R S`, built from the canonical owners
  above;
- primitive data: strict henselianity of the target, locality of `R → S`, the filtered-colimit-
  of-étale presentation, and the maximal-ideal image equality;
- derived API: any choice of henselization-to-strict-henselization comparison map and any chosen
  residue-field identification with a separable closure.

Source/core/bridge triage:
- `source-facing`: `IsStrictHenselizationOf` and
  `exists_henselization_to_strictHenselization`;
- `core/canonical`: `StrictHenselianLocalRing`, `IsLocalHom`, and
  `RingHom.IsFilteredColimitOfEtale`;
- `bridge/view`: `exists_strictHenselization`, which forgets the auxiliary chosen separable-closure
  identification and keeps only the strict-henselization owner.
-/
/-- A strict henselization of the local ring `R` is an `R`-algebra `S` for which `R → S` is a
local map, `S` is strictly henselian, `S` is a filtered colimit of étale `R`-algebras, and the
maximal ideal of `S` is the image of the maximal ideal of `R`. -/
class IsStrictHenselizationOf : Prop extends StrictHenselianLocalRing S,
    IsLocalHom (algebraMap R S) where
  isFilteredColimitOfEtale :
    (algebraMap R S).IsFilteredColimitOfEtale
  map_maximalIdeal :
    Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S

variable (Ksep : Type u) [Field Ksep] [Algebra (ResidueField R) Ksep]
variable [IsSepClosure (ResidueField R) Ksep]

-- Proof sketch: repeat the filtered-colimit construction of the henselization, but index stages
-- by triples `(S, 𝔮, α)` where `R → S` is étale, `𝔮` lies over `maximalIdeal R`, and `α`
-- embeds the stage residue field into `Ksep`. The colimit then carries compatible maps from both
-- a henselization `Rʰ` and the chosen separable closure of the residue field, while
-- `Lemma 10.154.8` and `Definition 10.153.1` give strict henselianity from the separably closed
-- residue field.
/-- Lemma 10.155.2: given a separable closure `Ksep` of the residue field of a local ring `R`,
there exist a henselization `Rʰ` of `R`, a strict henselization `Rˢʰ` of `R`, a local map
`Rʰ → Rˢʰ`, and a residue-field isomorphism from `ResidueField Rˢʰ` to `Ksep` compatible with the
canonical map from `ResidueField R`. -/
theorem exists_henselization_to_strictHenselization :
    ∃ (Rh : Type u) (_ : CommRing Rh) (_ : Algebra R Rh) (_ : IsHenselizationOf R Rh)
      (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra R Rsh)
      (_ : IsStrictHenselizationOf R Rsh) (_ : Algebra Rh Rsh) (_ : IsScalarTower R Rh Rsh)
      (_ : IsLocalHom (algebraMap Rh Rsh)) (φ : ResidueField Rsh ≃+* Ksep),
      φ.toRingHom.comp (ResidueField.map (algebraMap R Rsh)) =
        algebraMap (ResidueField R) Ksep := sorry

-- Proof sketch: apply Lemma `10.155.2` with the canonical separable closure
-- `SeparableClosure (ResidueField R)` and discard the auxiliary henselization and residue-field
-- comparison data. The strict-henselization owner is the primitive public output.
/-- Every local ring admits a strict henselization. This is the owner-level existence theorem
obtained from Lemma `10.155.2` by choosing the canonical separable closure of the residue field
and forgetting the auxiliary comparison data. -/
theorem exists_strictHenselization :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra R Rsh), IsStrictHenselizationOf R Rsh := by
  let Ksep := SeparableClosure (ResidueField R)
  let _ : Field Ksep := inferInstance
  let _ : Algebra (ResidueField R) Ksep := inferInstance
  let _ : IsSepClosure (ResidueField R) Ksep := inferInstance
  obtain ⟨_, _, _, _, Rsh, _, _, hRsh, _, _, _, _, _⟩ :=
    exists_henselization_to_strictHenselization R Ksep
  exact ⟨Rsh, inferInstance, inferInstance, hRsh⟩

end
