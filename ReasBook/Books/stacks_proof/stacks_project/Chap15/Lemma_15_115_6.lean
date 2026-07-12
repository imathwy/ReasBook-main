import Mathlib
import StacksProject_2024.Chap15.Definition_15_112_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Ideal IsLocalRing Algebra

noncomputable section

section

/- Domain-style sampling:
- source-facing owner: `IsTamelyRamifiedWithRespectTo A L` from `Definition_15_112_7`;
- sampled canonical declarations in this domain:
  `IsTamelyRamifiedWithRespectTo`,
  `FiniteDimensional.trans`,
  `Algebra.IsSeparable.trans`,
  `FiniteDimensional.right`,
  `Algebra.isSeparable_tower_top_of_isSeparable`;
- best owner abstraction: the chapter owner `IsTamelyRamifiedWithRespectTo A L`;
- primitive-vs-derived split: the branchwise residue-field separability and ramification-index
  coprimality data stay primitive in `Definition_15_112_7`, while this file only adds the derived
  tower-descent API.

Source/core/bridge triage:
- `source-facing`: the Stacks Project tower-descent statement for tame ramification;
- `core/canonical`: `IsTamelyRamifiedWithRespectTo`, together with the standard tower finiteness
  and separability owners;
- `bridge/view`: this file, which packages those tower hypotheses into the single descended tame
  owner rather than introducing branchwise duplicate local data.
-/

end

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

local notation "K" => FractionRing A

variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable {M : Type w} [Field M] [Algebra A M] [Algebra (FractionRing A) M] [Algebra L M]
variable [IsScalarTower A (FractionRing A) M] [IsScalarTower (FractionRing A) L M]
variable [FiniteDimensional (FractionRing A) L] [FiniteDimensional L M]
variable [Algebra.IsSeparable (FractionRing A) L] [Algebra.IsSeparable L M]

local notation "B" => integralClosure A L
local notation "C" => integralClosure A M
local notation "κA" => Ideal.ResidueField (maximalIdeal A)

local instance : IsScalarTower A L M := by
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  -- The `A → M` structure factors through `K → L → M`.
  rw [IsScalarTower.algebraMap_apply A K M, IsScalarTower.algebraMap_apply A K L,
    IsScalarTower.algebraMap_apply K L M]

/-- The canonical map `B → C` induced by the tower map `L → M`. -/
private noncomputable abbrev integralClosureTowerMap : B →ₐ[A] C :=
  (IsScalarTower.toAlgHom A L M).mapIntegralClosure

noncomputable local instance : Algebra B C :=
  integralClosureTowerMap.toAlgebra

local instance : IsScalarTower A B C := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  ext
  simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A L M]

/-- Helper for Lemma 15.115.6: the intermediate integral closure inherits the fraction-field owner
needed to view `C` as finite over `B`. -/
private local instance integralClosure_isFractionRing_base :
    IsFractionRing B L :=
  integralClosure.isFractionRing_of_finite_extension K L

/-- Helper for Lemma 15.115.6: both integral closures are finite over the base discrete valuation
ring, so the Dedekind-domain ramification API applies to each branch. -/
private local instance integralClosure_moduleFinite_base :
    Module.Finite A B :=
  IsIntegralClosure.finite A K L B

/-- Helper for Lemma 15.115.6: the intermediate integral closure is Dedekind. -/
private local instance integralClosure_isDedekindDomain_base :
    IsDedekindDomain B :=
  integralClosure.isDedekindDomain A K L

/-- Helper for Lemma 15.115.6: the intermediate field extension is torsion-free over the base
ring. -/
private local instance torsionFree_fraction_base :
    Module.IsTorsionFree A L :=
  .trans_faithfulSMul A K L

/-- Helper for Lemma 15.115.6: the top field extension is torsion-free over the base ring. -/
private local instance torsionFree_fraction_top :
    Module.IsTorsionFree A M :=
  .trans_faithfulSMul A K M

/-- Helper for Lemma 15.115.6: the top field is a faithful `B`-algebra because `L` is the
fraction field of `B`. -/
private local instance faithfulSmul_topField :
    FaithfulSMul B M :=
  FaithfulSMul.of_field_isFractionRing B M L M

/-- Helper for Lemma 15.115.6: torsion-freeness of the intermediate integral closure over the
base ring. -/
private local instance integralClosure_torsionFree_base :
    Module.IsTorsionFree A B :=
  IsIntegralClosure.isTorsionFree A L

/-- Helper for Lemma 15.115.6: torsion-freeness of the top integral closure over the base ring. -/
private local instance integralClosure_torsionFree_top :
    Module.IsTorsionFree A C :=
  IsIntegralClosure.isTorsionFree A M

/-- Helper for Lemma 15.115.6: the algebra map `B → C` is injective, so `C` is a faithful
`B`-algebra. -/
private local instance faithfulSmul_tower :
    FaithfulSMul B C := by
  refine (faithfulSMul_iff_algebraMap_injective B C).mpr fun x y hxy ↦ ?_
  have hxyM : algebraMap B M x = algebraMap B M y := by
    exact congrArg (algebraMap C M) hxy
  change algebraMap B M x = algebraMap B M y at hxyM
  exact FaithfulSMul.algebraMap_injective B M hxyM

/-- Helper for Lemma 15.115.6: the top integral closure is torsion-free over the intermediate
integral closure. -/
private local instance integralClosure_torsionFree_tower :
    Module.IsTorsionFree B C := by
  -- Embed the tower into the ambient field `M` and use that fields have no zero divisors.
  refine Module.IsTorsionFree.of_smul_eq_zero fun b c h ↦ ?_
  change (algebraMap B C b) * c = 0 at h
  have hmul : (algebraMap B C b) * c = 0 := h
  rcases mul_eq_zero.mp hmul with hzero | hzero
  · have hzero' : algebraMap B M b = algebraMap B M 0 := by
      simpa using congrArg (fun x : C ↦ (x : M)) hzero
    exact Or.inl <| FaithfulSMul.algebraMap_injective B M hzero'
  · exact Or.inr hzero

/-- Helper for Lemma 15.115.6: the map `B → C` is integral because both rings sit in the same
fraction-field tower. -/
private local instance integralClosure_isIntegral_tower :
    Algebra.IsIntegral B C :=
  Algebra.IsIntegral.tower_top A

/-- Helper for Lemma 15.115.6: every maximal ideal of the intermediate integral closure lies over
the maximal ideal of the base discrete valuation ring. -/
private local instance liesOver_maximalIdeal_base (p : Ideal B) [p.IsMaximal] :
    p.LiesOver (maximalIdeal A) :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal p)).symm⟩

/-- Helper for Lemma 15.115.6: every maximal ideal of the top integral closure lies over the
maximal ideal of the base discrete valuation ring. -/
private local instance liesOver_maximalIdeal_top (P : Ideal C) [P.IsMaximal] :
    P.LiesOver (maximalIdeal A) :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)).symm⟩

/-- Helper for Lemma 15.115.6: a maximal ideal of the intermediate integral closure admits a
maximal ideal above it in the top integral closure. -/
private lemma exists_maximal_liesOver_of_integralClosure_tower
    (p : Ideal B) [p.IsMaximal] :
    ∃ P : Ideal C, P.IsMaximal ∧ P.LiesOver p := by
  -- Use lying-over for the integral map `B → C` to lift the chosen branch.
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := C) p
  exact ⟨P, hPmax, hPover⟩

/-- Helper for Lemma 15.115.6: the ramification index along the chosen branch tower factors as
the product of the lower ramification index and the relative ramification index upstairs. -/
private lemma ramificationIdx_maximalIdeal_eq_mul_of_branch_liesOver
    (p : Ideal B) [p.IsMaximal] [p.LiesOver (maximalIdeal A)]
    (P : Ideal C) [P.IsMaximal] [P.LiesOver p] :
    ramificationIdx (maximalIdeal A) P =
      ramificationIdx (maximalIdeal A) p * ramificationIdx p P := by
  -- First install the base-to-top lies-over data needed by the ramification tower formula.
  letI : p.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.LiesOver (maximalIdeal A) := Ideal.LiesOver.trans P p (maximalIdeal A)
  let _ : FiniteDimensional K M := FiniteDimensional.trans K L M
  let _ : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  let _ : IsDedekindDomain C := integralClosure.isDedekindDomain A K M
  -- Then specialize the ideal-theoretic tower formula to this branch.
  simpa using
    (Ideal.ramificationIdx_algebra_tower' (maximalIdeal A) p P :
      ramificationIdx (maximalIdeal A) P =
        ramificationIdx (maximalIdeal A) p * ramificationIdx p P)

/-- Helper for Lemma 15.115.6: for a maximal branch of `integralClosure A L` above
`maximalIdeal A`, the induced residue-field map from `κA` is the ambient algebra map. -/
private lemma residueField_map_eq_algebraMap_base
    (p : Ideal B) [p.IsMaximal] [p.LiesOver (maximalIdeal A)] :
    Ideal.ResidueField.map (maximalIdeal A) p (algebraMap A B)
        (p.over_def (maximalIdeal A)) =
      algebraMap κA p.ResidueField := by
  letI : p.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  ext a
  change
    Ideal.ResidueField.map (maximalIdeal A) p (algebraMap A B)
        (p.over_def (maximalIdeal A)) ((algebraMap A κA) a) =
      (algebraMap κA p.ResidueField) ((algebraMap A κA) a)
  rw [Ideal.ResidueField.map_algebraMap (maximalIdeal A) p (algebraMap A B)
    (p.over_def (maximalIdeal A)) a]
  -- Both sides send the image of `a : A` to the same element of `p.ResidueField`.
  have hB : (algebraMap B p.ResidueField) ((algebraMap A B) a) =
      (algebraMap A p.ResidueField) a := by
    exact IsScalarTower.algebraMap_apply A B p.ResidueField a
  have hκ : (algebraMap κA p.ResidueField) ((algebraMap A κA) a) =
      (algebraMap A p.ResidueField) a := by
    exact (IsScalarTower.algebraMap_apply A κA p.ResidueField a).symm
  exact hB.trans hκ.symm

/-- Helper for Lemma 15.115.6: the residue-field maps
`κA → P.ResidueField` coming from `A → C` agree with the ambient algebra map. -/
private lemma residueField_map_eq_algebraMap_top
    (P : Ideal C) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
    Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A C)
        (P.over_def (maximalIdeal A)) =
      algebraMap κA P.ResidueField := by
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  ext a
  change
    Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A C)
        (P.over_def (maximalIdeal A)) ((algebraMap A κA) a) =
      (algebraMap κA P.ResidueField) ((algebraMap A κA) a)
  rw [Ideal.ResidueField.map_algebraMap (maximalIdeal A) P (algebraMap A C)
    (P.over_def (maximalIdeal A)) a]
  -- Both sides send the image of `a : A` to the same element of `P.ResidueField`.
  have hC : (algebraMap C P.ResidueField) ((algebraMap A C) a) =
      (algebraMap A P.ResidueField) a := by
    exact IsScalarTower.algebraMap_apply A C P.ResidueField a
  have hκ : (algebraMap κA P.ResidueField) ((algebraMap A κA) a) =
      (algebraMap A P.ResidueField) a := by
    exact (IsScalarTower.algebraMap_apply A κA P.ResidueField a).symm
  exact hC.trans hκ.symm

/-- Helper for Lemma 15.115.6: the residue-field maps
`κA → p.ResidueField → P.ResidueField` form a scalar tower along a branch lift. -/
private lemma residueField_isScalarTower_of_branch_liesOver
    (p : Ideal B) [p.IsMaximal] [p.LiesOver (maximalIdeal A)]
    (P : Ideal C) [P.IsMaximal] [P.LiesOver p] :
    IsScalarTower κA p.ResidueField P.ResidueField := by
  -- Compare both algebra maps on quotient representatives coming from `A`.
  letI : p.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.LiesOver (maximalIdeal A) := inferInstance
  letI : Algebra κA p.ResidueField := inferInstance
  letI : Algebra κA P.ResidueField := inferInstance
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  obtain ⟨a, rfl⟩ := (maximalIdeal A).algebraMap_residueField_surjective x
  rw [← residueField_map_eq_algebraMap_top (P := P),
    ← residueField_map_eq_algebraMap_base (p := p)]
  rw [Ideal.ResidueField.map_algebraMap (maximalIdeal A) P (algebraMap A C)
      (P.over_def (maximalIdeal A)) a,
    Ideal.ResidueField.map_algebraMap (maximalIdeal A) p (algebraMap A B)
      (p.over_def (maximalIdeal A)) a]
  rw [IsScalarTower.algebraMap_apply A B C]
  exact
    (Ideal.ResidueField.map_algebraMap p P (algebraMap B C) (P.over_def p)
      ((algebraMap A B) a)).symm

/-- Helper for Lemma 15.115.6: if the lifted branch upstairs is tame over `A`, then the lower
residue-field extension is separable over `κA`. -/
private lemma residueField_separable_of_tame_over_branch
    (hM : IsTamelyRamifiedWithRespectTo A M)
    (p : Ideal B) [p.IsMaximal] [p.LiesOver (maximalIdeal A)]
    (P : Ideal C) [P.IsMaximal] [P.LiesOver p] :
    Algebra.IsSeparable κA p.ResidueField := by
  -- Route correction: use the direct tower-descent theorem for separable extensions once the
  -- residue-field tower `κA ⊂ κ(p) ⊂ κ(P)` is in place.
  letI : p.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.LiesOver (maximalIdeal A) := inferInstance
  letI : Algebra κA p.ResidueField := inferInstance
  letI : Algebra κA P.ResidueField := inferInstance
  letI : IsScalarTower κA p.ResidueField P.ResidueField :=
    residueField_isScalarTower_of_branch_liesOver (A := A) (L := L) (M := M) p P
  letI : Algebra.IsSeparable κA P.ResidueField := by
    simpa using hM.residueField_separable P
  -- Separability descends to the intermediate field in a tower of field extensions.
  exact Algebra.isSeparable_tower_bot_of_isSeparable κA p.ResidueField P.ResidueField

-- Proof sketch: let `B` and `C` be the integral closures of `A` in `L` and `M`. Since `C` is
-- integral over `B`, every maximal ideal of `B` over `maximalIdeal A` lifts to a maximal ideal of
-- `C`. For such a pair, separability of `κ(p) / κA` descends from the separable upstairs residue
-- field `κ(P) / κA`, while multiplicativity of ramification indices shows that
-- `ramificationIdx (maximalIdeal A) p` divides `ramificationIdx (maximalIdeal A) P`; hence the
-- lower ramification index remains prime to the residue characteristic.
/-- Lemma 15.115.6: let `A` be a discrete valuation ring with fraction field `FractionRing A`. If
`M / L / K` is a tower of finite separable extensions, where `K = FractionRing A`, and `M` is
tamely ramified with respect to `A`, then `L` is tamely ramified with respect to `A`. -/
@[stacks 0EXV]
theorem isTamelyRamifiedWithRespectTo_of_tower
    {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    {M : Type w} [Field M] [Algebra A M] [Algebra K M] [Algebra L M]
    [IsScalarTower A K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]
    (hM : IsTamelyRamifiedWithRespectTo A M) :
    IsTamelyRamifiedWithRespectTo A L := by
  classical
  refine
    { residueField_separable := ?_
      ramificationIdx_coprime := ?_ }
  · intro p _ _
    -- Lift the chosen branch `p` to a maximal branch `P` upstairs and descend separability.
    obtain ⟨P, hPmax, hPover⟩ :=
      exists_maximal_liesOver_of_integralClosure_tower (A := A) (L := L) (M := M) p
    letI : P.IsMaximal := hPmax
    letI : P.LiesOver p := hPover
    exact residueField_separable_of_tame_over_branch (A := A) (L := L) (M := M) hM p P
  · intro q _ _ p _ _
    -- Lift `p` to a maximal branch `P`, then descend coprimality along the ramification product.
    obtain ⟨P, hPmax, hPover⟩ :=
      exists_maximal_liesOver_of_integralClosure_tower (A := A) (L := L) (M := M) p
    letI : P.IsMaximal := hPmax
    letI : P.LiesOver p := hPover
    letI : P.LiesOver (maximalIdeal A) := inferInstance
    have htop : Nat.Coprime (ramificationIdx (maximalIdeal A) P) q := by
      simpa using hM.ramificationIdx_coprime q P
    have hdvd : ramificationIdx (maximalIdeal A) p ∣ ramificationIdx (maximalIdeal A) P := by
      refine ⟨ramificationIdx p P, ?_⟩
      -- Multiplicativity of ramification indices makes the lower index a divisor of the upper one.
      exact
        ramificationIdx_maximalIdeal_eq_mul_of_branch_liesOver
          (A := A) (L := L) (M := M) p P
    exact Nat.Coprime.of_dvd_left hdvd htop

end
