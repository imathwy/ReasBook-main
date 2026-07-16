import StacksProject_2024.stacks_project.Chap15.Definition_15_112_7
import StacksProject_2024.stacks_project.Chap15.Lemma_15_112_9
import StacksProject_2024.stacks_project.Chap15.Lemma_15_112_3

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing Algebra

universe u v w

section

variable {A : Type u} {L : Type v} {M : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L]
variable [Algebra.IsSeparable (FractionRing A) L]
variable [Field M] [Algebra A M] [Algebra L M] [Algebra (FractionRing A) M]
variable [IsScalarTower A L M] [IsScalarTower A (FractionRing A) M]
variable [IsScalarTower (FractionRing A) L M]
variable [FiniteDimensional L M]
variable [Algebra.IsSeparable L M]

local notation "K" => FractionRing A
local notation "B" => integralClosure A L
local notation "C" => integralClosure A M
local notation "κA" => Ideal.ResidueField (maximalIdeal A)

/-- The canonical map `B → C` on integral closures induced by the tower map `L → M`. -/
private noncomputable abbrev integralClosureTowerMap : B →ₐ[A] C :=
  (IsScalarTower.toAlgHom A L M).mapIntegralClosure

noncomputable local instance : Algebra B C :=
  integralClosureTowerMap.toAlgebra

local instance : IsScalarTower A B C := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  ext
  simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A L M]

private local instance algebraIsIntegral_base : Algebra.IsIntegral A B :=
  IsIntegralClosure.isIntegral_algebra A L

private local instance algebraIsIntegral_top : Algebra.IsIntegral A C :=
  IsIntegralClosure.isIntegral_algebra A M

private local instance algebraIsIntegral_tower : Algebra.IsIntegral B C :=
  Algebra.IsIntegral.tower_top A

private local instance isFractionRing_base : IsFractionRing B L :=
  integralClosure.isFractionRing_of_finite_extension K L

private local instance moduleFinite_base : Module.Finite A B :=
  IsIntegralClosure.finite A K L B

private local instance isDedekindDomain_base : IsDedekindDomain B :=
  integralClosure.isDedekindDomain A K L

/-- Helper for Lemma 15.115.5: the intermediate field extension is torsion-free over the base
discrete valuation ring. -/
private local instance torsionFree_fraction_base : Module.IsTorsionFree A L :=
  .trans_faithfulSMul A K L

/-- Helper for Lemma 15.115.5: the top field extension is torsion-free over the base discrete
valuation ring. -/
private local instance torsionFree_fraction_top : Module.IsTorsionFree A M :=
  .trans_faithfulSMul A K M

private local instance torsionFree_base : Module.IsTorsionFree A B :=
  IsIntegralClosure.isTorsionFree A L

private local instance torsionFree_top : Module.IsTorsionFree A C :=
  IsIntegralClosure.isTorsionFree A M

/-- Helper for Lemma 15.115.5: the top integral closure is torsion-free as a module over the
intermediate integral closure. -/
private local instance torsionFree_tower : Module.IsTorsionFree B C := by
  let _ : IsScalarTower B C M := IsScalarTower.of_algebraMap_eq fun b ↦ by
    rfl
  let _ : Module.IsTorsionFree B M := Module.IsTorsionFree.trans_faithfulSMul B L M
  -- Pull torsion-freeness back along the injective inclusion `C ↪ M`.
  exact Function.Injective.moduleIsTorsionFree
    (f := fun x : C ↦ (x : M))
    Subtype.val_injective
    (fun b c ↦ by
      simp [Algebra.smul_def, IsScalarTower.algebraMap_apply B C M])

private instance liesOver_maximalIdeal_base (p : Ideal B) [p.IsMaximal] :
    p.LiesOver (maximalIdeal A) :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal p)).symm⟩

private instance liesOver_maximalIdeal_top (P : Ideal C) [P.IsMaximal] :
    P.LiesOver (maximalIdeal A) :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)).symm⟩

/- Domain-style sampling for tame ramification in an integral-closure tower:
- primary domain: ramification theory for finite separable extensions over a discrete valuation
  ring, measured on maximal ideals of integral closures;
- owner abstraction: `IsTamelyRamifiedWithRespectTo A L` from
  `Definition_15_112_7`, together with the tower bridge for `Ideal.ramificationIdx` from
  `Lemma_15_112_3`;
- source/core/bridge triage: this file is a `bridge/view` statement, lifting primitive local tame
  branch data on `B ⊆ C` to the global owner on `A ⊆ M`;
- primitive data: for each maximal branch `P` of `C`, the intermediate branch ideal is
  canonically `P.under B`; the primitive local data are that the residue-field extension
  `(P.under B).ResidueField ⊂ P.ResidueField` is separable and the relative ramification index
  `ramificationIdx (P.under B) P` is prime to the residue characteristic of `(P.under B).ResidueField`.

This local branch data is primitive theorem input, not a second packaged owner. -/

-- Proof sketch: for a maximal ideal `P` of `C`, let `p = P ∩ B`. The
-- assumption on `L/K` gives tameness of `p` over `A`, and the assumption on `M/L` gives tameness
-- of `P` over `p`. Use the tower `κ(P)/κ(p)/κA` for separability of residue fields and Lemma
-- `15.112.3` for multiplicativity of ramification indices to conclude that the ramification index
-- of `P` over `A` is still prime to the residue characteristic.
/-- Helper for Lemma 15.115.5: the contraction of a maximal branch ideal of the top integral
closure to the intermediate integral closure is again maximal. -/
private lemma under_isMaximal
    (P : Ideal C) [P.IsMaximal] :
    (P.under B).IsMaximal := by
  -- Identify `P.under B` with the comap along the integral-closure tower map.
  simpa [Ideal.under_def] using
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P :
      (Ideal.comap (algebraMap B C) P).IsMaximal)

/-- Helper for Lemma 15.115.5: the ramification index of a maximal branch in the top integral
closure factors through its contraction to the intermediate integral closure. -/
private lemma ramificationIdx_maximalIdeal_eq_under_mul
    (P : Ideal C) [P.IsMaximal] :
    ramificationIdx (maximalIdeal A) P =
      ramificationIdx (maximalIdeal A) (P.under B) * ramificationIdx (P.under B) P := by
  -- Install the branch data needed to apply the ideal-theoretic tower formula.
  let _ : FiniteDimensional K M := FiniteDimensional.trans K L M
  let _ : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  let _ : IsFractionRing C M := integralClosure.isFractionRing_of_finite_extension K M
  let _ : IsDedekindDomain C := integralClosure.isDedekindDomain A K M
  letI : (P.under B).IsMaximal := under_isMaximal P
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : (P.under B).LiesOver (maximalIdeal A) := inferInstance
  letI : P.LiesOver (P.under B) := by
    simpa using (Ideal.over_under (A := B) P)
  -- Lemma `15.112.3` is exactly the multiplicativity statement for this tower of ideals.
  simpa using
    (Ideal.ramificationIdx_algebra_tower' (maximalIdeal A) (P.under B) P :
      ramificationIdx (maximalIdeal A) P =
        ramificationIdx (maximalIdeal A) (P.under B) * ramificationIdx (P.under B) P)

/-- Helper for Lemma 15.115.5: the residue-field map from the base residue field to the
contracted branch residue field is the ambient algebra map. -/
private lemma residueField_map_eq_algebraMap_under_branch
    (P : Ideal C) [P.IsMaximal] :
    Ideal.ResidueField.map (maximalIdeal A) (P.under B) (algebraMap A B)
        ((P.under B).over_def (maximalIdeal A)) =
      algebraMap κA (P.under B).ResidueField := by
  letI : (P.under B).IsMaximal := under_isMaximal P
  letI : (P.under B).IsPrime := Ideal.IsMaximal.isPrime inferInstance
  -- Both maps agree on residue classes of elements of `A`.
  ext a
  rfl

/-- Helper for Lemma 15.115.5: the residue-field map from the base residue field to a top branch
residue field is the ambient algebra map. -/
private lemma residueField_map_eq_algebraMap_top_branch
    (P : Ideal C) [P.IsMaximal] :
    Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A C)
        (P.over_def (maximalIdeal A)) =
      algebraMap κA P.ResidueField := by
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  -- Again, the quotient-level map agrees with the canonical algebra map on generators.
  ext a
  rfl

/-- Helper for Lemma 15.115.5: the canonical residue-field maps along
`κA → (P.under B).ResidueField → P.ResidueField` form a scalar tower. -/
private lemma residueField_isScalarTower_of_under_branch
    (P : Ideal C) [P.IsMaximal] :
    IsScalarTower κA (P.under B).ResidueField P.ResidueField := by
  letI : (P.under B).IsMaximal := under_isMaximal P
  letI : (P.under B).IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : (P.under B).LiesOver (maximalIdeal A) := inferInstance
  letI : P.LiesOver (P.under B) := by
    simpa using (Ideal.over_under (A := B) P)
  letI : Algebra κA (P.under B).ResidueField := ResidueField.instAlgebra
  letI : Algebra κA P.ResidueField := ResidueField.instAlgebra
  -- Compare the two candidate maps `κA → P.ResidueField` on residue classes coming from `A`.
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  obtain ⟨a, rfl⟩ := (maximalIdeal A).algebraMap_residueField_surjective x
  rw [← residueField_map_eq_algebraMap_top_branch (P := P),
    ← residueField_map_eq_algebraMap_under_branch (P := P)]
  simpa [IsScalarTower.algebraMap_apply A B C] using
    (show
      (algebraMap C P.ResidueField) ((algebraMap B C) ((algebraMap A B) a)) =
        (algebraMap (P.under B).ResidueField P.ResidueField)
          ((algebraMap B (P.under B).ResidueField) ((algebraMap A B) a)) from
      (Ideal.ResidueField.map_algebraMap (P.under B) P (algebraMap B C)
        (P.over_def (P.under B)) ((algebraMap A B) a)).symm)

/-- Helper for Lemma 15.115.5: the residue characteristic of `κA` is inherited by the contracted
intermediate residue field. -/
private lemma charP_under_residueField
    (P : Ideal C) [P.IsMaximal]
    (q : ℕ) [Fact q.Prime] [CharP κA q] :
    CharP (P.under B).ResidueField q := by
  -- The algebra map from the base residue field into the contracted residue field is injective.
  letI : (P.under B).IsMaximal := under_isMaximal P
  letI : (P.under B).IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : (P.under B).LiesOver (maximalIdeal A) := inferInstance
  letI : Algebra κA (P.under B).ResidueField := ResidueField.instAlgebra
  exact charP_of_injective_algebraMap
    (R := κA) (A := (P.under B).ResidueField)
    (RingHom.injective (algebraMap κA (P.under B).ResidueField)) q

/-- Helper for Lemma 15.115.5: residue-field separability for the contracted branch and for the
top branch over it compose to residue-field separability over the base residue field. -/
private lemma residueField_separable_of_branch_tame_tower
    (hL : IsTamelyRamifiedWithRespectTo A L)
    (hM_sep : ∀ (P : Ideal C) [P.IsMaximal],
      Algebra.IsSeparable (P.under B).ResidueField P.ResidueField)
    (P : Ideal C) [P.IsMaximal] :
    Algebra.IsSeparable κA P.ResidueField := by
  -- First make the intermediate branch `P.under B` available with its canonical residue-field map.
  letI : (P.under B).IsMaximal := under_isMaximal P
  letI : (P.under B).IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : (P.under B).LiesOver (maximalIdeal A) := inferInstance
  letI : P.LiesOver (maximalIdeal A) := inferInstance
  letI : Algebra κA (P.under B).ResidueField := ResidueField.instAlgebra
  letI : Algebra κA P.ResidueField := ResidueField.instAlgebra
  letI : IsScalarTower κA (P.under B).ResidueField P.ResidueField :=
    residueField_isScalarTower_of_under_branch P
  letI : Algebra.IsSeparable κA (P.under B).ResidueField := by
    simpa using hL.residueField_separable (P.under B)
  letI : Algebra.IsSeparable (P.under B).ResidueField P.ResidueField := by
    simpa using hM_sep P
  -- Separability is transitive along the residue-field tower `κA ⊂ κ(P ∩ B) ⊂ κ(P)`.
  exact Algebra.IsSeparable.trans κA (P.under B).ResidueField P.ResidueField

/-- Helper for Lemma 15.115.5: coprimality of the two ramification indices in the branch tower
implies coprimality of the total ramification index over the base. -/
private lemma ramificationIdx_coprime_of_branch_tame_tower
    (hL : IsTamelyRamifiedWithRespectTo A L)
    (hM_coprime : ∀ (P : Ideal C) [P.IsMaximal]
      (q : ℕ) [Fact q.Prime] [CharP (P.under B).ResidueField q],
        Nat.Coprime (ramificationIdx (P.under B) P) q)
    (P : Ideal C) [P.IsMaximal]
    (q : ℕ) [Fact q.Prime] [CharP κA q] :
    Nat.Coprime (ramificationIdx (maximalIdeal A) P) q := by
  -- First transfer the residue characteristic to the intermediate branch residue field.
  letI : (P.under B).IsMaximal := under_isMaximal P
  letI : (P.under B).IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : (P.under B).LiesOver (maximalIdeal A) := inferInstance
  letI : Algebra κA (P.under B).ResidueField := ResidueField.instAlgebra
  letI : CharP (P.under B).ResidueField q := charP_under_residueField P q
  have hbase : Nat.Coprime (ramificationIdx (maximalIdeal A) (P.under B)) q := by
    simpa using hL.ramificationIdx_coprime q (P.under B)
  have htop : Nat.Coprime (ramificationIdx (P.under B) P) q := hM_coprime P q
  -- Then rewrite the total ramification index as the product of the two branch indices.
  rw [ramificationIdx_maximalIdeal_eq_under_mul (A := A) (L := L) (M := M) P]
  exact Nat.Coprime.mul_left hbase htop

/-- Lemma 15.115.5: let `A` be a discrete valuation ring with fraction field `FractionRing A`, let
`L / FractionRing A` and `M / L` be finite separable extensions, and let `B = integralClosure A L`.
If `L / FractionRing A` is tamely ramified with respect to `A`, and for every maximal ideal
`P : Ideal C` the canonical intermediate branch ideal `P.under B` induces a tame extension on the
localized step `B_(P ∩ B) ⊂ C_P`, then `M / FractionRing A` is tamely ramified with respect to
`A`; the branchwise `LiesOver (maximalIdeal A)` conditions are supplied canonically because every
maximal ideal of an integral closure over the discrete valuation ring `A` contracts to
`maximalIdeal A`. -/
theorem isTamelyRamifiedWithRespectTo_of_tame_of_forall_tame_over_integralClosure
    (hL : IsTamelyRamifiedWithRespectTo A L)
    (hM_sep : ∀ (P : Ideal C) [P.IsMaximal],
      Algebra.IsSeparable (P.under B).ResidueField P.ResidueField)
    (hM_coprime : ∀ (P : Ideal C) [P.IsMaximal]
      (q : ℕ) [Fact q.Prime] [CharP (P.under B).ResidueField q],
        Nat.Coprime (ramificationIdx (P.under B) P) q) :
    IsTamelyRamifiedWithRespectTo A M := by
  let _ : FiniteDimensional K M := FiniteDimensional.trans K L M
  let _ : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  refine
    { residueField_separable := ?_
      ramificationIdx_coprime := ?_ }
  · intro P _ _
    -- Compose the separable residue-field extensions along `κA ⊂ κ(P ∩ B) ⊂ κ(P)`.
    exact residueField_separable_of_branch_tame_tower hL hM_sep P
  · intro q _ _ P _ _
    -- Use multiplicativity of ramification indices in the branch tower and preserve coprimality.
    exact ramificationIdx_coprime_of_branch_tame_tower hL hM_coprime P q

end
