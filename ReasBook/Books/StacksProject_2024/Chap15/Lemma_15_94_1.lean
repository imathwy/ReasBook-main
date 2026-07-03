import Mathlib
import stacks_project.Chap04.Example_4_22_6
import stacks_project.Chap12.Definition_12_31_2
import stacks_project.Chap15.Definition_15_89_1
import stacks_project.Chap15.PrincipalIdeal
import stacks_project.Chap15.Situation_15_92_15

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open CochainComplex.HomComplex
open CochainComplex.HomComplex.Cochain
open Opposite
open SequentialInverseSystem
open SequentialProObjectMorphismRep
open scoped IdealPowerTorsion

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)
local notation "singleCpx₀" => CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)
private abbrev principalPowerKoszulTower (f : A) : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat A) :=
  derivedCompletionKoszulPowersDerivedInverseSystem (fun _ : Fin 1 ↦ f)
private abbrev principalPowerKoszulStage (f : A) (n : ℕ) : DerivedCategory (ModuleCat A) :=
  (principalPowerKoszulTower f).obj (op n)
private abbrev principalPowerQuotientTower (f : A) : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat A) :=
  koszulPowerQuotientInverseSystem (fun _ : Fin 1 ↦ f) ⋙ single₀
private abbrev principalPowerQuotientStage (f : A) (n : ℕ) : DerivedCategory (ModuleCat A) :=
  (principalPowerQuotientTower f).obj (op n)
local notation "Kstage(" f ", " n ")" =>
  principalPowerKoszulStage f n
local notation "Qstage(" f ", " n ")" =>
  principalPowerQuotientStage f n
local notation "Ktower(" f ")" =>
  principalPowerKoszulTower f
local notation "Qtower(" f ")" =>
  principalPowerQuotientTower f

/- Domain-style sampling for Lemma 15.94.1:
- primary domain: sequential pro-object comparisons between the one-variable powered Koszul tower
  and the principal-power quotient tower in `D(A)`;
- sampled owner declarations:
  `SequentialProObjectMorphismRep`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`,
  `koszulPowerQuotientStage`,
  `koszulPowerQuotientInverseSystem`,
  `CategoryTheory.CommSq`;
- best owner abstraction: the chapter powered-Koszul and quotient inverse-system owners
  `derivedCompletionKoszulPowersDerivedInverseSystem` and
  `koszulPowerQuotientInverseSystem`, with
  `SequentialProObjectMorphismRep` as the owner for the resulting pro-object comparisons;
- primitive data: the stagewise quotient maps out of the two-term Koszul complexes;
- derived API: the identity-reindex and shift-by-`c` representatives, their source-facing
  stagewise comparison maps, and the induced pro-object isomorphism statement.

Source/core/bridge triage:
- `source-facing`: the comparison maps between the Koszul and quotient towers;
- `core/canonical`: `SequentialProObjectMorphismRep ...` and `.toProObjectHom`;
- `bridge/view`: the one-variable specializations of the chapter powered-Koszul and quotient
  towers, together with the explicit stagewise maps assembling into those representatives. -/

/-- The owner-level bounded-torsion condition `A[f^∞] = A[f^c]` is equivalent to eventual
constancy of the source-facing principal-power torsion stages from `c` onward. -/
theorem fPowerTorsion_eq_iff_stabilizesFrom (f : A) (c : ℕ) :
    (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A) ↔
      ∀ m : ℕ, c ≤ m → (A[f ^ m] : Submodule A A) = (A[f ^ c] : Submodule A A) := by
  constructor
  · intro hstable m hcm
    apply le_antisymm
    · intro x hx
      have hxInf : x ∈ (A[f^∞] : Submodule A A) := by
        rw [Submodule.mem_torsion'_iff]
        rw [Submodule.mem_torsionBy_iff] at hx
        exact ⟨⟨f ^ m, ⟨m, rfl⟩⟩, by simpa using hx⟩
      rw [← hstable]
      exact hxInf
    · exact Submodule.torsionBy_le_torsionBy_of_dvd (f ^ c) (f ^ m) (pow_dvd_pow f hcm)
  · intro hstable
    apply le_antisymm
    · intro x hx
      rw [Submodule.mem_torsion'_iff] at hx
      rcases hx with ⟨⟨a, ha⟩, hx⟩
      rcases (Submonoid.mem_powers_iff a f).mp ha with ⟨m, rfl⟩
      have hxm : x ∈ (A[f ^ (max c m)] : Submodule A A) :=
        (Submodule.torsionBy_le_torsionBy_of_dvd (f ^ m) (f ^ max c m)
          (pow_dvd_pow f (Nat.le_max_right c m))) hx
      rw [← hstable (max c m) (Nat.le_max_left c m)]
      exact hxm
    · intro x hx
      rw [Submodule.mem_torsion'_iff]
      rw [Submodule.mem_torsionBy_iff] at hx
      exact ⟨⟨f ^ c, ⟨c, rfl⟩⟩, by simpa using hx⟩

private theorem range_fin1_power (f : A) (n : ℕ) :
    Set.range (fun _ : Fin 1 ↦ f ^ (n + 1)) = ({f ^ (n + 1)} : Set A) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    simp
  · intro hx
    refine ⟨0, ?_⟩
    simpa using hx.symm

private theorem principalPowerSingletonIdeal_eq (f : A) (n : ℕ) :
    koszulPowerIdeal (fun _ : Fin 1 ↦ f) n = principalPowerIdeal f (n + 1) := by
  rw [koszulPowerIdeal, principalPowerIdeal, range_fin1_power, Ideal.span_singleton_pow]

/-- The module endomorphism `A ⟶ A` given by multiplication by `f^n`. -/
private abbrev principalPowerKoszulMap (f : A) (n : ℕ) :
    ModuleCat.of A A ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (LinearMap.mulRight A (f ^ n))

/-- The quotient module `A / (f^n)`. -/
private abbrev principalPowerQuotientModule (f : A) (n : ℕ) : ModuleCat A :=
  ModuleCat.of A (A ⧸ principalPowerIdeal f n)

/-- The quotient map `A ⟶ A / (f^n)`. -/
private abbrev principalPowerQuotientMk (f : A) (n : ℕ) :
    ModuleCat.of A A ⟶ principalPowerQuotientModule f n :=
  ModuleCat.ofHom ((Ideal.Quotient.mkₐ A (principalPowerIdeal f n)).toLinearMap)

private abbrev principalPowerKoszulModelComplex (f : A) (n : ℕ) :
    CochainComplex (ModuleCat A) ℤ :=
  CochainComplex.mappingCone ((singleCpx₀).map (principalPowerKoszulMap f n))

private theorem principalPowerSingletonKoszulDerived_eq (f : A) (n : ℕ) :
    Kstage(f, n) =
      DerivedCategory.Q.obj (principalPowerKoszulModelComplex f (n + 1)) :=
  by
    sorry

private abbrev principalPowerKoszulStageIso (f : A) (n : ℕ) :
    Kstage(f, n) ≅ DerivedCategory.Q.obj (principalPowerKoszulModelComplex f (n + 1)) :=
  eqToIso (principalPowerSingletonKoszulDerived_eq f n)

private theorem principalPowerSingletonQuotientDerived_eq (f : A) (n : ℕ) :
    Qstage(f, n) = (single₀).obj (principalPowerQuotientModule f (n + 1)) := by
  simpa [principalPowerQuotientStage, principalPowerQuotientTower, principalPowerQuotientModule,
    koszulPowerQuotientStage] using
    congrArg (fun I : Ideal A ↦ (single₀).obj (ModuleCat.of A (A ⧸ I)))
      (principalPowerSingletonIdeal_eq f n)

private abbrev principalPowerQuotientStageIso (f : A) (n : ℕ) :
    Qstage(f, n) ≅
      DerivedCategory.Q.obj ((singleCpx₀).obj (principalPowerQuotientModule f (n + 1))) :=
  eqToIso (principalPowerSingletonQuotientDerived_eq f n) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      (principalPowerQuotientModule f (n + 1))

-- Proof sketch: the quotient map kills the image of multiplication by `f^n` because
-- `f^n ∈ (f^n)`.
/-- The quotient map `A ⟶ A / (f^n)` annihilates multiplication by `f^n`. -/
private theorem principalPowerKoszulMap_comp_quotientMk (f : A) (n : ℕ) :
    principalPowerKoszulMap f n ≫ principalPowerQuotientMk f n = 0 := sorry

private theorem singleCpx_principalPowerKoszulMap_comp_quotientMk (f : A) (n : ℕ) :
    (singleCpx₀).map (principalPowerKoszulMap f n) ≫
        (singleCpx₀).map (principalPowerQuotientMk f n) =
      0 := by
  simpa using
    congrArg (fun φ ↦ (singleCpx₀).map φ) (principalPowerKoszulMap_comp_quotientMk f n)

-- Proof sketch: apply `mappingCone.desc` with zero cochain and the quotient map on the degree-zero
-- term; the previous theorem gives the required vanishing condition.
/-- The zero cochain witnesses the factorization of the quotient map through the two-term Koszul
mapping cone. -/
private theorem principalPowerKoszulToQuotientComplexMap_desc_condition (f : A) (n : ℕ) :
    δ (-1) 0
        (0 :
          Cochain
            ((singleCpx₀).obj (ModuleCat.of A A))
            ((singleCpx₀).obj (principalPowerQuotientModule f n))
            (-1)) =
      Cochain.ofHom
        (((singleCpx₀).map (principalPowerKoszulMap f n)) ≫
          (singleCpx₀).map (principalPowerQuotientMk f n)) := by
  rw [δ_zero]
  simp [singleCpx_principalPowerKoszulMap_comp_quotientMk]

/-- The canonical chain map from the two-term Koszul complex `A \xrightarrow{f^n} A` to the
single complex on `A / (f^n)`. -/
private abbrev principalPowerKoszulToQuotientComplexMap (f : A) (n : ℕ) :
    principalPowerKoszulModelComplex f n ⟶
      (singleCpx₀).obj (principalPowerQuotientModule f n) :=
  CochainComplex.mappingCone.desc
    ((singleCpx₀).map (principalPowerKoszulMap f n))
    0
    ((singleCpx₀).map (principalPowerQuotientMk f n))
    (principalPowerKoszulToQuotientComplexMap_desc_condition f n)

/-- The stagewise canonical map
`(A \xrightarrow{f^(n+1)} A) ⟶ A/(f^(n+1))`,
viewed as a map from the one-variable specialization of the chapter powered-Koszul stage. -/
private abbrev principalPowerKoszulToQuotient (f : A) (n : ℕ) :
    Ktower(f).obj (op n) ⟶ Qtower(f).obj (op n) :=
  (principalPowerKoszulStageIso f n).hom ≫
    DerivedCategory.Q.map (principalPowerKoszulToQuotientComplexMap f (n + 1)) ≫
      (principalPowerQuotientStageIso f n).inv

-- Proof sketch: both towers are built from adjacent powers of `f`, and the quotient map out of
-- the two-term complex is functorial with respect to the transition maps.
/-- Naturality of the canonical stagewise maps from the powered Koszul tower to the canonical
quotient tower owner. -/
private theorem principalPowerKoszulToQuotient_naturality
    (f : A) {i j : ℕᵒᵖ} (h : i ⟶ j) :
    Ktower(f).map h ≫ principalPowerKoszulToQuotient f j.unop =
      principalPowerKoszulToQuotient f i.unop ≫
        Qtower(f).map h :=
  sorry

private abbrev principalPowerKoszulToQuotientNatTrans (f : A) :
    Ktower(f) ⟶ Qtower(f) :=
  { app := fun n ↦
      show Ktower(f).obj n ⟶ Qtower(f).obj n from principalPowerKoszulToQuotient f n.unop
    naturality := fun _ _ h ↦ principalPowerKoszulToQuotient_naturality f h }

/-- Lemma 15.94.1 (1): the canonical quotient maps
`(A \xrightarrow{f^(n+1)} A) ⟶ A/(f^(n+1))`
define the identity-reindex representative from the one-variable powered-Koszul tower to the
canonical quotient tower owner. -/
abbrev principalPowerKoszulToQuotientRep (f : A) :
    SequentialProObjectMorphismRep (Ktower(f)) (Qtower(f)) :=
  ofNatTrans (principalPowerKoszulToQuotientNatTrans f)

private theorem principalPowerTorsionLift_condition (f : A) (c : ℕ) :
    (A[f ^ c] : Submodule A A) ≤ LinearMap.ker (LinearMap.mulRight A (f ^ c)) := by
  intro x hx
  rw [Submodule.mem_torsionBy_iff] at hx
  change x * f ^ c = 0
  simpa [smul_eq_mul, mul_comm] using hx

/-- The quotient module `A / A[f^c]`. -/
private abbrev principalPowerTorsionQuotientModule (f : A) (c : ℕ) : ModuleCat A :=
  ModuleCat.of A (A ⧸ (A[f ^ c] : Submodule A A))

/-- The map `A / A[f^c] ⟶ A` given by multiplication by `f^c`. -/
private abbrev principalPowerTorsionLift (f : A) (c : ℕ) :
    principalPowerTorsionQuotientModule f c ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom <|
    Submodule.liftQ
      (A[f ^ c] : Submodule A A)
      (LinearMap.mulRight A (f ^ c))
      (principalPowerTorsionLift_condition f c)

private theorem principalPowerTorsionTopMap_condition (f : A) (c n : ℕ) :
    (A[f ^ c] : Submodule A A) ≤ LinearMap.ker (LinearMap.mulRight A (f ^ (c + n + 1))) := by
  intro x hx
  rw [Submodule.mem_torsionBy_iff] at hx
  change x * f ^ (c + n + 1) = 0
  have hx' : x * f ^ c = 0 := by
    simpa [smul_eq_mul, mul_comm] using hx
  calc
    x * f ^ (c + n + 1) = x * (f ^ c * f ^ (n + 1)) := by
      rw [show c + n + 1 = c + (n + 1) by omega, pow_add]
    _ = (x * f ^ c) * f ^ (n + 1) := by ac_rfl
    _ = 0 := by rw [hx', zero_mul]

private abbrev principalPowerTorsionTopMap (f : A) (c n : ℕ) :
    principalPowerTorsionQuotientModule f c ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom <|
    Submodule.liftQ
      (A[f ^ c] : Submodule A A)
      (LinearMap.mulRight A (f ^ (c + n + 1)))
      (principalPowerTorsionTopMap_condition f c n)

private abbrev principalPowerTorsionComplex (f : A) (c n : ℕ) :
    CochainComplex (ModuleCat A) ℤ :=
  CochainComplex.mappingCone ((singleCpx₀).map (principalPowerTorsionTopMap f c n))

private theorem principalPowerQuotientToKoszulRoof_comm (f : A) (c n : ℕ) :
    CommSq
      ((singleCpx₀).map (principalPowerTorsionTopMap f c n))
      ((singleCpx₀).map (principalPowerTorsionLift f c))
      (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
      ((singleCpx₀).map (principalPowerKoszulMap f (n + 1))) := by
  refine CommSq.mk ?_
  sorry

private abbrev principalPowerQuotientToKoszulRoofMap (f : A) (c n : ℕ) :
    principalPowerTorsionComplex f c n ⟶ principalPowerKoszulModelComplex f (n + 1) :=
  CochainComplex.mappingCone.map
    ((singleCpx₀).map (principalPowerTorsionTopMap f c n))
    ((singleCpx₀).map (principalPowerKoszulMap f (n + 1)))
    ((singleCpx₀).map (principalPowerTorsionLift f c))
    (𝟙 ((singleCpx₀).obj (ModuleCat.of A A)))
    (principalPowerQuotientToKoszulRoof_comm f c n).w

private theorem principalPowerTorsionTopMap_comp_quotientMk (f : A) (c n : ℕ) :
    principalPowerTorsionTopMap f c n ≫ principalPowerQuotientMk f (c + n + 1) = 0 := by
  sorry

private theorem singleCpx_principalPowerTorsionTopMap_comp_quotientMk (f : A) (c n : ℕ) :
    (singleCpx₀).map (principalPowerTorsionTopMap f c n) ≫
        (singleCpx₀).map (principalPowerQuotientMk f (c + n + 1)) =
      0 := by
  simpa using
    congrArg
      (fun φ ↦ (singleCpx₀).map φ)
      (principalPowerTorsionTopMap_comp_quotientMk f c n)

private theorem principalPowerTorsionComplexToQuotient_desc_condition (f : A) (c n : ℕ) :
    δ (-1) 0
        (0 :
          Cochain
            ((singleCpx₀).obj (principalPowerTorsionQuotientModule f c))
            ((singleCpx₀).obj (principalPowerQuotientModule f (c + n + 1)))
            (-1)) =
      Cochain.ofHom
        (((singleCpx₀).map (principalPowerTorsionTopMap f c n)) ≫
          (singleCpx₀).map (principalPowerQuotientMk f (c + n + 1))) := by
  rw [δ_zero]
  simp [singleCpx_principalPowerTorsionTopMap_comp_quotientMk]

private def principalPowerTorsionComplexToQuotientComplexMap (f : A) (c n : ℕ) :
    principalPowerTorsionComplex f c n ⟶
      (singleCpx₀).obj (principalPowerQuotientModule f (c + n + 1)) :=
  CochainComplex.mappingCone.desc
    ((singleCpx₀).map (principalPowerTorsionTopMap f c n))
    0
    ((singleCpx₀).map (principalPowerQuotientMk f (c + n + 1)))
    (principalPowerTorsionComplexToQuotient_desc_condition f c n)

private theorem principalPowerTorsionComplexToQuotientComplexMap_quasiIso
    (f : A) (c n : ℕ) :
    QuasiIso (principalPowerTorsionComplexToQuotientComplexMap f c n) := by
  sorry

private instance principalPowerTorsionComplexToQuotientComplexMap_isIso
    (f : A) (c n : ℕ) :
    IsIso (DerivedCategory.Q.map (principalPowerTorsionComplexToQuotientComplexMap f c n)) := by
  letI : QuasiIso (principalPowerTorsionComplexToQuotientComplexMap f c n) :=
    principalPowerTorsionComplexToQuotientComplexMap_quasiIso f c n
  infer_instance

private abbrev principalPowerTorsionComplexToQuotientIso (f : A) (c n : ℕ) :
    DerivedCategory.Q.obj (principalPowerTorsionComplex f c n) ≅
      DerivedCategory.Q.obj ((singleCpx₀).obj (principalPowerQuotientModule f (c + n + 1))) :=
  asIso (DerivedCategory.Q.map (principalPowerTorsionComplexToQuotientComplexMap f c n))

/-- The stagewise reverse comparison map of Lemma 15.94.1, indexed so that stage `0` corresponds
to the textbook exponent `n = 1`. It is the source-facing map
`A/(f^(c + n)) ⟶ (A \xrightarrow{f^n} A)` obtained from the Stacks proof diagram with
`A / A[f^c]` as an intermediate roof object. -/
private abbrev principalPowerQuotientToKoszul (f : A) (c n : ℕ) :
    Qtower(f).obj (op (c + n)) ⟶ Ktower(f).obj (op n) :=
  (principalPowerQuotientStageIso f (c + n)).hom ≫
      (principalPowerTorsionComplexToQuotientIso f c n).symm.hom ≫
        DerivedCategory.Q.map (principalPowerQuotientToKoszulRoofMap f c n) ≫
          (principalPowerKoszulStageIso f n).inv

/-- Naturality of the shifted stagewise reverse maps with respect to the canonical quotient
tower owner. -/
private theorem principalPowerQuotientToKoszul_naturality
    (f : A) (c : ℕ) {i j : ℕᵒᵖ} (h : i ⟶ j) :
    (SequentialInverseSystem.shift (Qtower(f)) c).map h ≫
        principalPowerQuotientToKoszul f c j.unop =
      principalPowerQuotientToKoszul f c i.unop ≫
        Ktower(f).map h := by
  sorry

private abbrev principalPowerQuotientToKoszulShiftNatTrans (f : A) (c : ℕ) :
    SequentialInverseSystem.shift (Qtower(f)) c ⟶ Ktower(f) :=
  { app := fun n ↦
      show (SequentialInverseSystem.shift (Qtower(f)) c).obj n ⟶ Ktower(f).obj n from
        principalPowerQuotientToKoszul f c n.unop
    naturality := fun _ _ h ↦ by
      simpa using principalPowerQuotientToKoszul_naturality f c h }

/-- Lemma 15.94.1 (2): the reverse comparison maps
`A/(f^(c + n)) ⟶ (A \xrightarrow{f^n} A)` assemble to the canonical shift-by-`c`
representative from the principal-power quotient tower to the powered Koszul tower. -/
abbrev principalPowerQuotientToKoszulShiftRep (f : A) (c : ℕ) :
    SequentialProObjectMorphismRep (Qtower(f)) (Ktower(f)) :=
  ofShiftNatTrans c (principalPowerQuotientToKoszulShiftNatTrans f c)


-- Proof sketch: the stabilization hypothesis identifies the torsion submodules `A[f^m]` with
-- `A[f^c]` for all sufficiently large stages, so the explicit reverse representative above and the
-- forward representative `principalPowerKoszulToQuotientRep f` become inverse after common
-- refinement in the canonical owner `SequentialProObjectMorphismRep.IsProIsomorphism`.
/-- Lemma 15.94.1 (2): if the `f`-power torsion submodules `A[f^m]` stabilize from stage
`c`, equivalently if `A[f^∞] = A[f^c]`, then the explicit shift-by-`c` reverse comparison
representative is a pro-isomorphism. -/
theorem principalPowerQuotientToKoszulShift_isProIsomorphism
    (f : A) (c : ℕ)
    (hstable : (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A)) :
    (principalPowerQuotientToKoszulShiftRep f c).IsProIsomorphism := by
  sorry

/-- Companion to Lemma 15.94.1 (2): the explicit shift-by-`c` reverse comparison representative
induces an isomorphism of the associated sequential pro-objects. -/
theorem principalPowerQuotientToKoszulShift_isIso
    (f : A) (c : ℕ)
    (hstable : (A[f^∞] : Submodule A A) = (A[f ^ c] : Submodule A A)) :
    IsIso (principalPowerQuotientToKoszulShiftRep f c).toProObjectHom := by
  sorry

end
