import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_6
import StacksProject_2024.stacks_project.Chap10.Remark_10_155_4

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

noncomputable section

variable {R S : Type u}
variable {Rph Rpsh Sqh : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
local notation "Rₚ" => Localization.AtPrime p
local notation "S_q" => Localization.AtPrime q
variable [CommRing Rph] [CommRing Sqh] [CommRing Rpsh]
variable [Algebra (Localization.AtPrime p) Rph] [IsHenselizationOf (Localization.AtPrime p) Rph]
variable [Algebra (Localization.AtPrime q) Sqh]
variable [IsHenselizationOf (Localization.AtPrime q) Sqh]
variable [Algebra Rph Rpsh]
variable [IsStrictHenselizationOf Rph Rpsh]

noncomputable local instance : Algebra Rₚ S_q :=
  (Localization.localRingHom p q (algebraMap R S) (Ideal.over_def q p)).toAlgebra

local instance : IsLocalHom (algebraMap Rₚ S_q) := by
  simpa [RingHom.algebraMap_toAlgebra] using
    Localization.isLocalHom_localRingHom p q (algebraMap R S) (Ideal.over_def q p)

/-- The canonical `Rph`-algebra structure on `Sqh`, induced by the henselization comparison
`Rₚ → S_q`. -/
private noncomputable abbrev henselizationComparisonAlgebra : Algebra Rph Sqh := by
  let _ : Algebra Rₚ Sqh := Algebra.compHom Sqh (algebraMap Rₚ S_q)
  let _ : IsScalarTower Rₚ S_q Sqh := IsScalarTower.of_algebraMap_eq' rfl
  exact @henselizationMapAlgebra Rₚ Rph Sqh _ _ _ _ _ _ _ S_q _ _ _ _ _ _ _

/-- The canonical `S_q`-algebra structure on `Sqh ⊗[Rph] Rpsh`, induced from the left tensor
factor through the comparison `S_q → Sqh`. -/
private noncomputable abbrev tensorStrictHenselizationAlgebra :
    let _ : Algebra Rph Sqh := henselizationComparisonAlgebra p q
    Algebra S_q (Sqh ⊗[Rph] Rpsh) := by
  let _ : Algebra Rph Sqh := henselizationComparisonAlgebra p q
  exact Algebra.compHom (Sqh ⊗[Rph] Rpsh) (algebraMap S_q Sqh)

/-
Domain-style sampling:
- primary domain: strict henselization base change along local maps between localizations at prime
  ideals;
- sampled owner declarations of the same kind:
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `henselizationMap`,
  `henselizationMapAlgebra`,
  `strictHenselization_over_henselization_isStrictHenselizationOf`,
  `exists_strictHenselization_of_henselization`,
  `isStrictHenselizationOf_localizationAt_strictHenselizationTensorPrime`;
- best owner abstraction: the source-facing statement is the chosen-`Ksep` strict-henselization
  comparison over the henselization `Sqh`; the owner `IsStrictHenselizationOf` remains the core
  abstraction, while the residue-field equivalence to the chosen common separable closure is
  source-facing bridge data that must remain visible in the main theorem;
- primitive data: the henselization owners on `Rph` and `Sqh`, the canonical induced
  henselization map `Rph → Sqh`, the strict-henselization owner of `Rpsh` over `Rph`, and the
  chosen common separable closure data;
- derived API: the file-local canonical `Rph`-algebra on `Sqh`, the resulting `S_q`-algebra on
  `Sqh ⊗[Rph] Rpsh`, and the inherited residue-field identification with `Ksep`.

Source/core/bridge triage:
- `source-facing`: the present tensor-product strict-henselization statement together with the
  chosen residue-field identification with `Ksep`;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`, and `henselizationMap`;
- `bridge/view`: `strictHenselization_over_henselization_isStrictHenselizationOf` from
  Remark 10.155.4, together with the chosen-`Ksep` existence theorem
  `exists_strictHenselization_of_henselization`.
-/
-- Proof sketch: use the canonical local map `Rₚ → S_q` induced by `R → S` and the assumption that
-- `κ(p) → κ(q)` is bijective. View the chosen common separable closure `Ksep` as an `S_q`
-- residue field, and suppose the chosen strict henselization `Rpsh` of `Rph` is already equipped
-- with the corresponding residue-field identification. The canonical `Rph`-algebra on `Sqh` is
-- the owner-level bridge `henselizationMapAlgebra`; base-changing `Rpsh` along `Rph → Sqh`
-- produces the strict henselization of `Sqh` built from the same `Ksep`, and hence also, via
-- Remark `10.155.4`, a strict henselization of `S_q`. This is the Lean form of the textbook
-- identity `(S_q)^sh = (S_q)^h ⊗_{(R_p)^h} (R_p)^sh` for the strict henselizations constructed
-- from a common separable closure.
section ChosenSepClosure

private lemma henselization_tensor_strictHenselization_aux
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)))
    {Ksep : Type u}
    [Field Ksep]
    [Algebra (ResidueField S_q) Ksep]
    [IsSepClosure (ResidueField S_q) Ksep]
    (ιR : ResidueField Rpsh ≃+* Ksep)
    (hιR :
      ιR.toRingHom.comp
          (IsLocalRing.ResidueField.map
            ((algebraMap Rph Rpsh).comp (algebraMap Rₚ Rph))) =
        (algebraMap (ResidueField S_q) Ksep).comp (ResidueField.map (algebraMap Rₚ S_q))) :
    let _ : Algebra Rph Sqh := henselizationComparisonAlgebra p q
    let _ : Algebra S_q (Sqh ⊗[Rph] Rpsh) := tensorStrictHenselizationAlgebra p q
    ∃ _ : IsStrictHenselizationOf S_q (Sqh ⊗[Rph] Rpsh),
      ∃ ιS : ResidueField (Sqh ⊗[Rph] Rpsh) ≃+* Ksep,
        ιS.toRingHom.comp
            (ResidueField.map (algebraMap S_q (Sqh ⊗[Rph] Rpsh))) =
          algebraMap (ResidueField S_q) Ksep := by
  sorry

/-- Lemma 10.155.13: assume the residue-field map `κ(p) → κ(q)` is bijective, fix a field `Ksep`
equipped with the chosen map `κ(S_q) → Ksep`, and suppose `Rpsh` is the strict henselization of
`Rph` corresponding to that same `Ksep` via the induced map `κ(Rₚ) → κ(S_q) → Ksep`. Then the
canonical tensor product `Sqh ⊗[Rph] Rpsh`, formed using the canonical comparison
`Rph → Sqh = (S_q)^h`, is a strict henselization of `S_q` whose residue field is identified with
the same chosen `Ksep`. -/
lemma henselization_tensor_strictHenselization
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)))
    {Ksep : Type u}
    [Field Ksep]
    [Algebra (ResidueField S_q) Ksep]
    [IsSepClosure (ResidueField S_q) Ksep]
    (ιR : ResidueField Rpsh ≃+* Ksep)
    (hιR :
      ιR.toRingHom.comp
          (IsLocalRing.ResidueField.map
            ((algebraMap Rph Rpsh).comp (algebraMap Rₚ Rph))) =
        (algebraMap (ResidueField S_q) Ksep).comp (ResidueField.map (algebraMap Rₚ S_q))) :
    let _ : Algebra Rph Sqh := henselizationComparisonAlgebra p q
    let _ : Algebra S_q (Sqh ⊗[Rph] Rpsh) := tensorStrictHenselizationAlgebra p q
    ∃ _ : IsStrictHenselizationOf S_q (Sqh ⊗[Rph] Rpsh),
      ∃ ιS : ResidueField (Sqh ⊗[Rph] Rpsh) ≃+* Ksep,
        ιS.toRingHom.comp
            (ResidueField.map (algebraMap S_q (Sqh ⊗[Rph] Rpsh))) =
          algebraMap (ResidueField S_q) Ksep := by
  exact henselization_tensor_strictHenselization_aux p q hκ ιR hιR

end ChosenSepClosure

/-- Owner-level corollary of Lemma 10.155.13, forgetting the chosen common separable closure
identification. -/
lemma henselization_tensor_strictHenselization_isStrictHenselizationOf
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p))) :
    let _ : Algebra Rph Sqh := henselizationComparisonAlgebra p q
    let _ : Algebra S_q (Sqh ⊗[Rph] Rpsh) := tensorStrictHenselizationAlgebra p q
    IsStrictHenselizationOf S_q (Sqh ⊗[Rph] Rpsh) := by
  sorry

end
