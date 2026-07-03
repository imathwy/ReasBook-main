import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_94_1 (from Chap15) -/
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

/-! ### Lemma_15_94_2 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped IdealPowerTorsion PrincipalIdeal

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single0" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

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

private theorem principalPowerQuotientDerivedStage_eq (f : A) (n : ℕ) :
    (derivedCompletionPowerQuotientDerivedInverseSystem (fun _ : Fin 1 ↦ f)).obj (op n) =
      idealPowerQuotientDerivedStage ((f) : Ideal A) n := by
  simpa [derivedCompletionPowerQuotientDerivedInverseSystem, idealPowerQuotientDerivedStage,
    koszulPowerQuotientStage] using
    congrArg (fun I : Ideal A ↦ (single0).obj (ModuleCat.of A (A ⧸ I)))
      (principalPowerSingletonIdeal_eq f n)

private abbrev principalPowerQuotientDerivedStageIso (f : A) (n : ℕ) :
    (derivedCompletionPowerQuotientDerivedInverseSystem (fun _ : Fin 1 ↦ f)).obj (op n) ≅
      idealPowerQuotientDerivedStage ((f) : Ideal A) n :=
  eqToIso (principalPowerQuotientDerivedStage_eq f n)

private abbrev principalPowerCompletionStageMap (f : A) (K : DMod) (n : ℕ) :
    (derivedCompletionKoszulPowerTensorDerivedInverseSystem K (fun _ : Fin 1 ↦ f)).obj (op n) ⟶
      (idealPowerQuotientTensorDerivedInverseSystem ((f) : Ideal A) K).obj (op n) :=
  (derivedTensorProduct K).map ((principalPowerKoszulToQuotientRep f).hom.app (op n)) ≫
    (derivedTensorProduct K).map (principalPowerQuotientDerivedStageIso f n).hom

namespace CategoryTheory

/-- A natural transformation from principal derived completion to a functor
`K ↦ naiveDerivedCompletionFunctor.obj K` is the source-facing comparison to naive principal-power
completion if, objectwise, the source and target are presented by the canonical Milnor-triangle
comparisons and those presentations are compatible with the stagewise map induced by
`principalPowerKoszulToQuotientRep`. -/
def IsPrincipalDerivedCompletionQuotientComparison
    (f : A)
    {naiveDerivedCompletionFunctor : DMod ⥤ DMod}
    (toNaiveDerivedCompletion : 𝟭 DMod ⟶ naiveDerivedCompletionFunctor)
    (comparison :
      DerivedCategory.derivedCompletion ((f) : Ideal A) (principalIdeal_fg f) ⟶
        naiveDerivedCompletionFunctor) : Prop :=
  ∀ K : DMod,
    ∃ _ : HasProduct
        (inverseSystemFamily
          (derivedCompletionKoszulPowerTensorDerivedInverseSystem K (fun _ : Fin 1 ↦ f))),
      ∃ _ : HasProduct
          (inverseSystemFamily
            (idealPowerQuotientTensorDerivedInverseSystem ((f) : Ideal A) K)),
        ∃ ιhat :
            DerivedCategory.derivedCompletionOf ((f) : Ideal A) (principalIdeal_fg f) K ⟶
              ∏ᶜ inverseSystemFamily
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K (fun _ : Fin 1 ↦ f)),
          ∃ ι' :
              naiveDerivedCompletionFunctor.obj K ⟶
                ∏ᶜ inverseSystemFamily
                  (idealPowerQuotientTensorDerivedInverseSystem ((f) : Ideal A) K),
            HasMilnorTriangle.WithMap
                (derivedCompletionKoszulPowerTensorDerivedInverseSystem K (fun _ : Fin 1 ↦ f))
                ιhat ∧
              HasMilnorTriangle.WithMap
                  (idealPowerQuotientTensorDerivedInverseSystem ((f) : Ideal A) K)
                  ι' ∧
                (∀ n : ℕ,
                  DerivedCategory.toDerivedCompletion ((f) : Ideal A) (principalIdeal_fg f) K ≫
                      ιhat ≫
                      Pi.π
                        (inverseSystemFamily
                          (derivedCompletionKoszulPowerTensorDerivedInverseSystem
                            K (fun _ : Fin 1 ↦ f)))
                        n =
                    derivedCompletionKoszulPowerTensorToStage K (fun _ : Fin 1 ↦ f) n) ∧
                (∀ n : ℕ,
                  toNaiveDerivedCompletion.app K ≫
                      ι' ≫
                      Pi.π
                        (inverseSystemFamily
                          (idealPowerQuotientTensorDerivedInverseSystem ((f) : Ideal A) K))
                        n =
                    idealPowerQuotientTensorToStage ((f) : Ideal A) K n) ∧
                ∀ n : ℕ,
                  CommSq
                    (comparison.app K)
                    (ιhat ≫
                      Pi.π
                        (inverseSystemFamily
                          (derivedCompletionKoszulPowerTensorDerivedInverseSystem
                            K (fun _ : Fin 1 ↦ f)))
                        n)
                    (ι' ≫
                      Pi.π
                        (inverseSystemFamily
                          (idealPowerQuotientTensorDerivedInverseSystem ((f) : Ideal A) K))
                        n)
                    (principalPowerCompletionStageMap f K n)

end CategoryTheory

/- Domain-style sampling for Lemma 15.94.2:
- primary domain: principal derived completion versus naive principal-power completion in `D(A)`,
  expressed through the chapter derived-completion owner, the quotient-tower derived-limit owner,
  and the principal tower comparison from Lemma `15.94.1`;
- sampled owner declarations:
  `DerivedCategory.derivedCompletion`,
  `CategoryTheory.IsDerivedCompletionKoszulPowerTensorComparison`,
  `CategoryTheory.IsDerivedCompletionIdealPowerQuotientTensorComparison`,
  `CategoryTheory.IsPrincipalDerivedCompletionQuotientComparison`,
  `idealPowerQuotientTensorDerivedInverseSystem`,
  `principalIdeal` together with the owner notation `(f)`,
  `principalPowerKoszulToQuotientRep`,
  `HasMilnorTriangle.WithMap`;
- best owner abstraction: the left-hand functor should be the canonical owner
  `DerivedCategory.derivedCompletion ((f) : Ideal A) ...`, while the right-hand source-facing
  data should be the chapter owner
  `IsDerivedCompletionIdealPowerQuotientTensorComparison ((f) : Ideal A)` and the source-facing
  bridge owner `CategoryTheory.IsPrincipalDerivedCompletionQuotientComparison`, which packages
  the compatible Milnor-triangle presentations and the thin principal bridge from
  Lemma `15.94.1`;
- primitive vs. derived: primitive data are the ring `A`, the element `f`, the canonical map
  `K ⟶ R lim (K ⊗_A^{\mathbf L} A/f^(n+1))`, and the stagewise compatibility with the principal
  Koszul-to-quotient tower map from Lemma `15.94.1`; the bounded `f`-power torsion criterion is
  derived API, not extra structure on the completion functor.

Source/core/bridge triage:
- `source-facing`: the comparison between principal derived completion and naive principal-power
  completion, specified objectwise by the actual Koszul and quotient towers and the induced map
  on their chosen derived limits, now packaged by
  `CategoryTheory.IsPrincipalDerivedCompletionQuotientComparison`;
- `core/canonical`: `DerivedCategory.derivedCompletion`,
  `IsDerivedCompletionKoszulPowerTensorComparison`,
  `IsDerivedCompletionIdealPowerQuotientTensorComparison`, and the chapter owner `(f)` for the
  principal ideal;
- `bridge/view`: the principal one-generator specialization and the induced comparison map
  determined by `principalPowerKoszulToQuotientRep`. -/

-- Proof sketch: if the `f`-power torsion is bounded, Lemma `15.94.1` upgrades the canonical
-- stagewise principal Koszul-to-quotient maps to a pro-isomorphism, so the induced canonical map
-- on chosen derived limits is an isomorphism. Conversely, if the canonical comparison from
-- principal derived completion to naive principal-power completion is an isomorphism, apply the
-- Milnor-triangle criterion from Lemma `15.88.11` to the cone tower, then test on `K = A` and on
-- a countable direct sum of copies of `A` to force the torsion tower `(A[f^(n+1)])_n` to be
-- eventually constant, equivalently `A[f^∞] = A[f^c]` for some `c`.
/-- Lemma 15.94.2: let `A` be a ring and `f ∈ A`. Let
`DerivedCategory.derivedCompletion ((f) : Ideal A) (principalIdeal_fg f)` be the
canonical derived completion functor `K ↦ R lim (K ⊗_A^{\mathbf L} (A \xrightarrow{f^(n+1)} A))`.
Suppose `toNaiveDerivedCompletion : 𝟭 ⟶ naiveDerivedCompletionFunctor` presents the right-hand
functor objectwise as the canonical derived limit of the principal-power quotient tower
`K ↦ R lim (K ⊗_A^{\mathbf L} (A / f^(n+1) A)[0])`, and suppose `comparison` is objectwise the
canonical map induced by the principal Koszul-to-quotient tower morphism of Lemma `15.94.1`.
The source canonicality, target canonicality, and stagewise compatibility with
`principalPowerKoszulToQuotientRep` are recorded by
`CategoryTheory.IsPrincipalDerivedCompletionQuotientComparison`.
Then this canonical comparison natural transformation is an isomorphism if and only if the
`f`-power torsion of `A` is bounded.
-/
theorem isIso_principalDerivedCompletionComparison_iff_exists_powerTorsionStabilizes
    (f : A)
    {naiveDerivedCompletionFunctor : DMod ⥤ DMod}
    (toNaiveDerivedCompletion : 𝟭 DMod ⟶ naiveDerivedCompletionFunctor)
    (comparison :
      DerivedCategory.derivedCompletion ((f) : Ideal A) (principalIdeal_fg f) ⟶
        naiveDerivedCompletionFunctor)
    (hcomparison :
      CategoryTheory.IsPrincipalDerivedCompletionQuotientComparison
        f toNaiveDerivedCompletion comparison) :
    IsIso comparison ↔ ∃ c : ℕ, A[f^∞] = A[f ^ c] := sorry

end

/-! ### Example_15_94_3 (from Chap15) -/
open CategoryTheory
open scoped IdealPowerTorsion PrincipalIdeal

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: derived completeness of `A`-modules with respect to `(f)` and short exact
  sequences in `ModuleCat A`;
- sampled owner-side declarations:
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `principalIdeal` together with the owner notation `(f)`,
  `ShortComplex.mk`,
  `ShortComplex.ShortExact`;
- best owner abstraction: the short exact sequence data `K ⟶ L ⟶ M` itself, rather than a
  wrapper predicate on an arbitrary short complex;
- primitive data: the module objects `K`, `L`, the maps `ι`, `π`, and the relation `ι ≫ π = 0`;
- derived API: short exactness of `ShortComplex.mk ι π h`, `(f)`-adic completeness of `K` and `L`,
  and vanishing of their `f`-torsion.

Layer triage:
- `source-facing`: the existence of a short exact sequence `0 → K → L → M → 0` with the listed
  completeness and torsion conditions;
- `core/canonical`: `ModuleCat.IsDerivedCompleteWithRespectTo`, `principalIdeal`/`(f)`, and
  `ShortComplex.ShortExact`;
- `bridge/view`: the realization of the source sequence as `ShortComplex.mk ι π h`. -/

-- Proof sketch: for the forward implication, choose a surjection from a free module onto `M`,
-- replace the free module by its `(f)`-adic completion, and let `K` be the kernel of the induced
-- map to `M`; derived completeness of kernels is supplied by Lemma `15.92.6`, while the free and
-- kernel terms are `(f)`-adically complete with zero `f`-torsion. For the reverse implication,
-- tensor the short exact sequence with the two-term complexes `(A \xrightarrow{f^n} A)`, use the
-- vanishing of `f`-torsion on the complete terms to identify the derived tensors with
-- `(K / f^n K \to L / f^n L)`, and pass to `R lim`; Lemma `15.92.17` then gives derived
-- completeness of `M`.
/-- Example 15.94.3: if `f` is a nonzerodivisor in a ring `A`, then an `A`-module `M` is derived
complete with respect to `(f)` if and only if it fits into a short exact sequence
`0 → K → L → M → 0` in which `K` and `L` are `(f)`-adically complete and have zero
`f`-torsion. -/
theorem isDerivedCompleteWithRespectTo_principalIdeal_iff_exists_principalDerivedCompletePresentation
    (f : A) (M : ModuleCat A) (hf : IsRegular f) :
    M.IsDerivedCompleteWithRespectTo ((f) : Ideal A) ↔
      ∃ (K L : ModuleCat A) (ι : K ⟶ L) (π : L ⟶ M) (h : ι ≫ π = 0),
        (ShortComplex.mk ι π h).ShortExact ∧
          IsAdicComplete ((f) : Ideal A) K ∧
          IsAdicComplete ((f) : Ideal A) L ∧
          (K[f^1] : Submodule A K) = ⊥ ∧
          (L[f^1] : Submodule A L) = ⊥ := sorry

end

/-! ### Example_15_94_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Polynomial
open scoped PrincipalIdeal BigOperators

section

variable (p : ℕ) [Fact p.Prime]

local notation "Zp" => ℤ_[p]
local notation "ZpPoly" => Polynomial Zp
local notation:max "(p)" => principalIdeal (p : Zp)
local notation "ZpPolyHat" => AdicCompletion (p) ZpPoly

/- Domain-style sampling:
- primary domain: `(p)`-adic completions of `ℤ_[p][X]`, module-category cokernels, and
  derived/adic completeness for the resulting example module;
- sampled owner-side declarations:
  `principalIdeal` together with the owner notation `(f)`,
  `AdicCompletion.map`,
  `cokernel`,
  `ModuleCat.cokernelIsoRangeQuotient`,
  `ModuleCat.IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the chapter owner `principalIdeal` for the ambient ideal `(p)`,
  together with the categorical cokernel of the completed substitution morphism; the
  quotient-by-range description remains only a bridge;
- primitive data: the principal ideal `(p)` in `ℤ_[p]` and the completed substitution linear map
  induced by `X ↦ pX`;
- derived API: the quotient-model bridge, derived completeness, the named geometric-series class in
  the cokernel, and failure of adic completeness.

Layer triage:
- `source-facing`: the completed substitution map and the example module defined as its cokernel;
- `core/canonical`: `AdicCompletion.map`, `cokernel`,
  `ModuleCat.IsDerivedCompleteWithRespectTo`, `IsAdicComplete`, and `principalIdeal`/`(p)`;
- `bridge/view`: `ModuleCat.cokernelIsoRangeQuotient`, identifying the categorical cokernel with
  the explicit quotient by the image. -/

/-- The map on ordinary `p`-adic completions induced by the substitution
`ℤ_[p][X] → ℤ_[p][X]`, `X ↦ pX`. -/
abbrev padicPolynomialCompletionMap :
    ZpPolyHat →ₗ[Zp] ZpPolyHat :=
  (AdicCompletion.map (p)
      ((aeval (C (p : Zp) * X) : ZpPoly →ₐ[Zp] ZpPoly).toLinearMap)).restrictScalars Zp

/-- Example 15.94.4: the example module is the cokernel of the map on ordinary `p`-adic
completions induced by `ℤ_[p][x] → ℤ_[p][y]`, `x ↦ py`; using the common polynomial ring
`ℤ_[p][X]`, Lean takes the categorical cokernel of the completed substitution morphism
`X ↦ pX`. -/
abbrev padicPolynomialCompletionCokernel : ModuleCat Zp :=
  cokernel (ModuleCat.ofHom (padicPolynomialCompletionMap p))

-- Proof sketch: Proposition `15.92.5` gives derived completeness for the completed polynomial
-- modules, and Lemma `15.92.6` shows that the cokernel of a morphism between derived-complete
-- modules is again derived complete.
/-- The cokernel of the completed substitution map `X ↦ pX` is derived complete as a
`ℤ_[p]`-module with respect to `(p)`. -/
theorem padicPolynomialCompletionCokernel_isDerivedComplete :
    (padicPolynomialCompletionCokernel p).IsDerivedCompleteWithRespectTo
      (p) :=
  sorry

private abbrev padicPolynomialCompletionGeometricSeriesTruncation (n : ℕ) : ZpPoly :=
  ∑ i ∈ Finset.range n, C ((p : Zp) ^ i) * X ^ i

private abbrev padicPolynomialCompletionGeometricSeriesToQuotient (n : ℕ) :
    Zp →ₗ[Zp] (ZpPoly ⧸ (((p) ^ n) • (⊤ : Submodule Zp ZpPoly))) :=
  (Submodule.mkQ (((p) ^ n) • (⊤ : Submodule Zp ZpPoly))).comp <|
    LinearMap.smulRight (LinearMap.id : Zp →ₗ[Zp] Zp)
      (padicPolynomialCompletionGeometricSeriesTruncation p n)

private theorem padicPolynomialCompletionGeometricSeriesToQuotient_compatible
    {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap (p) ZpPoly hmn ∘ₗ
        padicPolynomialCompletionGeometricSeriesToQuotient p n =
      padicPolynomialCompletionGeometricSeriesToQuotient p m := by
  sorry

private noncomputable abbrev padicPolynomialCompletionGeometricSeries : ZpPolyHat :=
  (AdicCompletion.lift (p) (padicPolynomialCompletionGeometricSeriesToQuotient p)
    fun hle ↦ padicPolynomialCompletionGeometricSeriesToQuotient_compatible p hle) 1

-- Proof sketch: represent the formal series `1 + pX + p^2 X^2 + ⋯` by its compatible system of
-- truncations in the completed target polynomial ring. Its class in the cokernel is nonzero, and
-- multiplying by any power `p^n` shifts the series so that the class remains in `p^n M`.
/-- The class of `1 + pX + p^2 X^2 + ⋯` in the cokernel of the completed substitution map
`X ↦ pX`. -/
noncomputable abbrev padicPolynomialCompletionCokernelGeometricSeries :
    padicPolynomialCompletionCokernel p :=
  (cokernel.π (ModuleCat.ofHom (padicPolynomialCompletionMap p))).hom
    (padicPolynomialCompletionGeometricSeries p)

/-- The geometric-series class in the example cokernel is nonzero. -/
theorem padicPolynomialCompletionCokernelGeometricSeries_ne_zero :
    padicPolynomialCompletionCokernelGeometricSeries p ≠ 0 :=
  sorry

/-- The geometric-series class in the example cokernel lies in every submodule `p^n M`. -/
theorem padicPolynomialCompletionCokernelGeometricSeries_mem_p_pow_smul_top (n : ℕ) :
    padicPolynomialCompletionCokernelGeometricSeries p ∈
      ((p) ^ n) • (⊤ : Submodule Zp (padicPolynomialCompletionCokernel p)) :=
  sorry

-- Proof sketch: the geometric-series class is nonzero and lies in `⋂ n, p^n M`, so the module is
-- not Hausdorff for the `(p)`-adic topology. Since `IsAdicComplete` includes Hausdorffness, the
-- cokernel cannot be `p`-adically complete.
/-- The example cokernel is not `p`-adically complete as a `ℤ_[p]`-module. -/
theorem padicPolynomialCompletionCokernel_not_isAdicComplete :
    ¬ IsAdicComplete (p) (padicPolynomialCompletionCokernel p) :=
  sorry

end

/-! ### Example_15_94_5 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open scoped PrincipalIdeal PrincipalTateModule

universe u

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Example `15.94.5`.
- primary domain: principal derived completion of modules and derived objects, together with the
  degree-`-1`/`0` module case and the general cohomology short exact sequence;
- sampled owner declarations:
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `principalTateModule`,
  `DerivedCategory.derivedCompletionOf`;
- sampled bridge companion declarations:
  `principalDerivedCompletion_cohomology_has_comparison_diagram`;
- best owner abstraction: the source-facing owner is the canonical derived completion object
  `((single0).obj M)^∧[(f), principalIdeal_fg f]`, together with the chapter owners
  `principalTateModule` and `principalPowerQuotientTower`/`principalPowerTorsionTower`; the later
  comparison theorem from `Lemma_15_94_6` is bridge/view data, while the degree-zero short exact
  sequence itself is owned canonically by the Milnor theorem
  `CategoryTheory.derivedLimit_cohomology_shortExact` specialized to the principal completion
  tower;
- primitive vs. derived:
  primitive data are the ring element `f`, the module `M`, and the canonical principal towers
  `principalPowerQuotientTower f M` and `principalPowerTorsionTower f M`, together with the
  derived object `K` and degree `p` for the general cohomology sequence;
  derived API is the `H^{-1}` Tate-module comparison, the module-level `H^0` short exact sequence
  against the ordinary completion tower, the general short exact sequence
  `0 → H^0(H^p(K)^∧) → H^p(K^∧) → T_f(H^{p+1}(K)) → 0`, and the amplitude bound below.

Source/core/bridge triage:
- `source-facing`: the `H^{-1}`/`H^0` module statements for
  `((single0).obj M)^∧[(f), principalIdeal_fg f]`, the general short exact sequence for
  `H^p(K^∧[(f), principalIdeal_fg f])`, and the amplitude bound;
- `core/canonical`: `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `principalTateModule`, `principalPowerQuotientTower`, `principalPowerTorsionTower`, and
  `DerivedCategory.derivedCompletionOf`;
- `bridge/view`: the later comparison theorem from `Lemma_15_94_6`, specialized to `K = M[0]` and
  `p = -1, 0` in the module case and used below to recover the general cohomology sequence. -/

section

variable {A : Type u} [CommRing A]

local notation "ModA" => ModuleCat A
local notation "DMod" => DerivedCategory ModA
local notation "H" => DerivedCategory.homologyFunctor ModA
local notation "single0" => DerivedCategory.singleFunctor ModA (0 : ℤ)

/- Example 15.94.5: the source-facing Tate module in this chapter is the owner
`principalTateModule`, written `T[f] M`. -/
recall principalTateModule

/- Companion bridge: Lemma `15.94.6` records the comparison rows and columns used to recover the
source-facing module statements below. -/

section

variable (f : A)

local notation "I" => ((f) : Ideal A)
local notation "hI" => principalIdeal_fg f

/-- Example 15.94.5: the degree-zero cohomology of principal derived completion of a module fits
into the short exact sequence
`0 → R^1 lim_n M[f^(n + 1)] → H^0(M^∧) → lim_n M / f^(n + 1) M → 0`. -/
theorem principalDerivedCompletionModule_hzero_shortExact
    (M : ModA) :
    ∃ (ι :
        firstDerivedLimit (principalPowerTorsionTower f M) ⟶
          (H 0).obj (((single0).obj M)^∧[I, hI]))
      (π :
        (H 0).obj (((single0).obj M)^∧[I, hI]) ⟶
          limit (principalPowerQuotientTower f M))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

/-- Example 15.94.5: the degree-`-1` cohomology of principal derived completion of a module is
canonically isomorphic to the principal Tate module `T[f] M`. -/
theorem principalDerivedCompletionModule_hnegOne_isomorphic_tateModule
    (M : ModA) :
    IsIsomorphic ((H (-1)).obj (((single0).obj M)^∧[I, hI])) (T[f] M) := sorry

/-- Example 15.94.5: for every `K ∈ D(A)` and `p : ℤ`, the cohomology of principal derived
completion fits into the short exact sequence
`0 → H^0(H^p(K)^∧) → H^p(K^∧) → T_f(H^{p+1}(K)) → 0`. -/
theorem principalDerivedCompletion_cohomology_shortExact
    (K : DMod) (p : ℤ) :
    ∃ (ι :
        (H 0).obj (((single0).obj ((H p).obj K))^∧[I, hI]) ⟶
          (H p).obj (K^∧[I, hI]))
      (π :
        (H p).obj (K^∧[I, hI]) ⟶
          T[f] ((H (p + 1)).obj K))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

-- Proof sketch: the derived inverse limit of a tower of modules has no cohomology above degree
-- `1`, and for the principal completion tower all degrees below `-1` are trivially zero because
-- each stage is a two-term complex.
/-- The derived `(f)`-adic completion of a module has cohomology only in degrees `-1` and `0`. -/
theorem principalDerivedCompletionModule_homology_isZero_of_ne_zero_or_negOne
    (M : ModA) (p : ℤ)
    (hp0 : p ≠ 0) (hpneg1 : p ≠ -1) :
    IsZero ((H p).obj (((single0).obj M)^∧[I, hI])) := sorry

end

end

/-! ### Lemma_15_94_6 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open scoped PrincipalIdeal PrincipalTateModule

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "ModA" => ModuleCat A
local notation "DMod" => DerivedCategory ModA
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "single0" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/- Domain-style sampling for Lemma `15.94.6`.
- primary domain: comparison of Milnor short exact sequences for principal derived completion in
  `DerivedCategory (ModuleCat A)`;
- sampled owner declarations:
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `CategoryTheory.ShortComplex.Hom`,
  `DerivedCategory.derivedCompletionOf`,
  `principalPowerQuotientTower`,
  `principalPowerTorsionTower`;
- best owner abstraction: the rows and columns of the textbook diagram should be expressed by the
  canonical owners `ShortComplex`, `ShortComplex.Hom`, and `CommSq`, while the quotient, torsion,
  and Koszul towers are reused directly from the earlier chapter owners instead of being recopied
  into a local diagram package;
- primitive vs. derived:
  primitive data are the four short complexes, the row morphism between the top and middle rows,
  and the bottom comparison isomorphism between the two `R^1 lim` terms;
  derived API is the short exactness of those short complexes and the remaining bottom
  commutative square.

Source/core/bridge triage:
- `source-facing`: the existence of the comparison diagram in Lemma `15.94.6`;
- `core/canonical`: `ShortComplex`, `ShortComplex.Hom`, `CommSq`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`, `DerivedCategory.derivedCompletionOf`,
  `principalPowerQuotientTower`, and `principalPowerTorsionTower`;
- `bridge/view`: the specific four-row-and-column comparison assembling those owner constructions in
  the principal one-generator case. -/

variable (f : A)

local notation "I" => ((f) : Ideal A)
local notation "hI" => principalIdeal_fg f

private abbrev principalTower (f : A) (K : DMod) : ℕᵒᵖ ⥤ DMod :=
  CategoryTheory.derivedCompletionKoszulPowerTensorDerivedInverseSystem K (fun _ : Fin 1 ↦ f)

private abbrev principalDerivedCompletionComparisonTopLeft (f : A) (K : DMod) (p : ℤ) : ModA :=
  limit (principalPowerQuotientTower f ((H p).obj K))

private abbrev principalDerivedCompletionComparisonTopMiddle (f : A) (K : DMod) (p : ℤ) : ModA :=
  limit (principalTower f K ⋙ H p)

private abbrev principalDerivedCompletionComparisonMiddleLeft (f : A) (K : DMod) (p : ℤ) : ModA :=
  (H 0).obj
    (DerivedCategory.derivedCompletionOf
      ((f) : Ideal A)
      (principalIdeal_fg f)
      ((single0).obj ((H p).obj K)))

private abbrev principalDerivedCompletionComparisonMiddleMiddle (f : A) (K : DMod) (p : ℤ) : ModA :=
  (H p).obj
    (DerivedCategory.derivedCompletionOf ((f) : Ideal A) (principalIdeal_fg f) K)

private abbrev principalDerivedCompletionComparisonRight (f : A) (K : DMod) (p : ℤ) : ModA :=
  T[f] ((H (p + 1)).obj K)

private abbrev principalDerivedCompletionComparisonBottomLeft (f : A) (K : DMod) (p : ℤ) : ModA :=
  firstDerivedLimit (principalPowerTorsionTower f ((H p).obj K))

private abbrev principalDerivedCompletionComparisonBottomMiddle (f : A) (K : DMod) (p : ℤ) : ModA :=
  firstDerivedLimit (principalTower f K ⋙ H (p - 1))

-- Proof sketch: the top row comes from the inverse-limit short exact sequences
-- `0 → H^p(K) / f^(n+1) H^p(K) → H^p(K_n) → H^{p+1}(K)[f^(n+1)] → 0` after taking `lim`. The
-- middle row is Example `15.94.5`, the middle column is the Milnor short exact sequence for the
-- principal Koszul tensor tower `(K_n)_n`, and the left column is the module-level Milnor short
-- exact sequence for `H^p(K)`. Applying these to `L = τ_{\le p} K` and comparing `L_n → K_n`
-- gives the commutative diagram and the bottom isomorphism.
/-- Lemma 15.94.6: for `K_n = K ⊗_A^{\mathbf L} (A \xrightarrow{f^(n+1)} A)` and every
`p : ℤ`, there is a comparison diagram whose top and middle rows and left and middle columns are
short exact `ShortComplex`es, whose top-to-middle comparison is a morphism of short complexes with
right component the identity on `T[f] (H^{p+1}(K))`, and whose bottom horizontal map identifies the
two `R^1 lim` terms. The principal derived completion terms are written with the chapter owner
notation `K^∧[(f), principalIdeal_fg f]`. -/
theorem principalDerivedCompletion_cohomology_has_comparison_diagram
    (K : DMod) (p : ℤ) :
    let topLeft := principalDerivedCompletionComparisonTopLeft f K p
    let topMiddle := principalDerivedCompletionComparisonTopMiddle f K p
    let middleLeft := principalDerivedCompletionComparisonMiddleLeft f K p
    let middleMiddle := principalDerivedCompletionComparisonMiddleMiddle f K p
    let right := principalDerivedCompletionComparisonRight f K p
    let bottomLeft := principalDerivedCompletionComparisonBottomLeft f K p
    let bottomMiddle := principalDerivedCompletionComparisonBottomMiddle f K p
    ∃ (topRowLeft : topLeft ⟶ topMiddle)
      (topRowRight : topMiddle ⟶ right)
      (middleRowLeft : middleLeft ⟶ middleMiddle)
      (middleRowRight : middleMiddle ⟶ right)
      (leftColumnTop : topLeft ⟶ middleLeft)
      (leftColumnBottom : middleLeft ⟶ bottomLeft)
      (middleColumnTop : topMiddle ⟶ middleMiddle)
      (middleColumnBottom : middleMiddle ⟶ bottomMiddle)
      (topRowZero : topRowLeft ≫ topRowRight = 0)
      (middleRowZero : middleRowLeft ≫ middleRowRight = 0)
      (leftColumnZero : leftColumnTop ≫ leftColumnBottom = 0)
      (middleColumnZero : middleColumnTop ≫ middleColumnBottom = 0)
      (bottomIso : bottomLeft ≅ bottomMiddle),
      let topRow : ShortComplex ModA := ShortComplex.mk topRowLeft topRowRight topRowZero
      let middleRow : ShortComplex ModA := ShortComplex.mk middleRowLeft middleRowRight middleRowZero
      let leftColumn : ShortComplex ModA :=
        ShortComplex.mk leftColumnTop leftColumnBottom leftColumnZero
      let middleColumn : ShortComplex ModA :=
        ShortComplex.mk middleColumnTop middleColumnBottom middleColumnZero
      ∃ topToMiddle : topRow ⟶ middleRow,
        topRow.ShortExact ∧
          middleRow.ShortExact ∧
          leftColumn.ShortExact ∧
          middleColumn.ShortExact ∧
          topToMiddle.τ₁ = leftColumn.f ∧
          topToMiddle.τ₂ = middleColumn.f ∧
          topToMiddle.τ₃ = 𝟙 topRow.X₃ ∧
          CommSq middleRow.f leftColumn.g middleColumn.g bottomIso.hom := sorry

end

/-! ### Remark_15_94_7 (from Chap15) -/
noncomputable section

open CategoryTheory
open Opposite
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open scoped IdealPowerTorsion

universe u

section

variable {A : Type u} [CommRing A]

local notation "ModA" => ModuleCat A

/- Domain-style sampling for Remark `15.94.7`.
- primary domain: sequential inverse systems of `A`-modules, their Mittag-Leffler condition, and
  the principal-power quotient/torsion towers attached to one element `f : A`;
- sampled owner declarations:
  `principalPowerIdeal`,
  `Ideal.powerTorsion`,
  `Submodule.torsionBy`,
  `CategoryTheory.SequentialInverseSystem`,
  `SequentialInverseSystem.transitionMap`,
  `SequentialInverseSystem.IsMittagLeffler`,
  `SequentialInverseSystem.isMittagLeffler_middle_of_shortExact`;
- best owner abstraction: the ambient tower object is the chapter owner
  `SequentialInverseSystem (ModuleCat A)`, while the stagewise principal-power data should reuse
  the chapter owner `principalPowerIdeal` and the chapter notation `M[f^n]` for finite principal
  torsion; the target file should expose only the principal quotient/torsion constructions and the
  source-facing remark built on those owners, not parallel wrappers for the ideal powers, torsion
  submodules, tower type, or Mittag-Leffler predicate;
- primitive vs. derived:
  primitive data are the element `f`, the module stages `M / f^(n + 1) M` and `M[f^(n + 1)]`, and
  their canonical transition maps;
  derived API is the resulting towers, the Tate module, the quotient-tower Mittag-Leffler
  statement, and the short-exact transfer criterion in the remark.

Source/core/bridge triage:
- `source-facing`: the principal-power towers, the Tate module `T[f] M`, and the remark comparing
  Mittag-Leffler for the middle and torsion towers;
- `core/canonical`: `SequentialInverseSystem`, `transitionMap`, and `IsMittagLeffler`;
- `bridge/view`: the specialization of the general short-exact Mittag-Leffler machinery to the
  quotient/torsion towers generated by one element. -/

/-- The submodule `f^n M`, modeled as the action of the principal ideal `(f)^n` on `M`. -/
abbrev principalPowerSubmodule (f : A) (M : ModA) (n : ℕ) : Submodule A M :=
  principalPowerIdeal f n • (⊤ : Submodule A M)

/- Textbook notation for the principal-power submodule `f^n M`. -/
scoped[PrincipalPowerSubmodule] notation:max f:max "^{" n:max "} " M:max =>
  principalPowerSubmodule f M n

open scoped PrincipalPowerSubmodule

-- Proof sketch: `(f)^(n + 2) ≤ (f)^(n + 1)` implies the same containment after acting on `M`.
/-- The principal-power submodules `f^n M` form a descending chain. -/
theorem principalPowerSubmodule_step_le
    (f : A) (M : ModA) (n : ℕ) :
    f^{(n + 2)} M ≤ f^{(n + 1)} M := sorry

/-- The quotient stage `M / f^(n + 1) M`. -/
abbrev principalPowerQuotientStage (f : A) (M : ModA) (n : ℕ) : ModA :=
  ModuleCat.of A (M ⧸ f^{(n + 1)} M)

/-- The transition map `M / f^(n + 2) M ⟶ M / f^(n + 1) M` in the principal-power quotient
tower. -/
abbrev principalPowerQuotientStep (f : A) (M : ModA) (n : ℕ) :
    principalPowerQuotientStage f M (n + 1) ⟶ principalPowerQuotientStage f M n :=
  ModuleCat.ofHom <|
    Submodule.mapQ
      (f^{(n + 2)} M)
      (f^{(n + 1)} M)
      (LinearMap.id : M →ₗ[A] M)
      (principalPowerSubmodule_step_le f M n)

/-- The inverse system `(M / f^(n + 1) M)_n` of principal-power quotients. -/
abbrev principalPowerQuotientTower (f : A) (M : ModA) :
    SequentialInverseSystem ModA :=
  Functor.ofOpSequence (principalPowerQuotientStep f M)

/-- The stage `M[f^(n + 1)]` of the principal-power torsion tower. -/
abbrev principalPowerTorsionStage (f : A) (M : ModA) (n : ℕ) : ModA :=
  ModuleCat.of A (M[f ^ (n + 1)])

-- Proof sketch: if `x` is annihilated by `f^(n + 2)`, then `f • x` is annihilated by
-- `f^(n + 1)`.
/-- Multiplication by `f` maps `M[f^(n + 2)]` into `M[f^(n + 1)]`. -/
theorem principalPowerTorsion_smul_mem
    (f : A) (M : ModA) (n : ℕ) (x : M[f ^ (n + 2)]) :
    f • x.1 ∈ (M[f ^ (n + 1)] : Submodule A M) := sorry

/-- The transition map `M[f^(n + 2)] ⟶ M[f^(n + 1)]` in the principal-power torsion tower. -/
abbrev principalPowerTorsionStep (f : A) (M : ModA) (n : ℕ) :
    principalPowerTorsionStage f M (n + 1) ⟶ principalPowerTorsionStage f M n :=
  ModuleCat.ofHom <|
    LinearMap.codRestrict
      (M[f ^ (n + 1)] : Submodule A M)
      ((((f : A) • (LinearMap.id : M →ₗ[A] M)).domRestrict
          (M[f ^ (n + 2)] : Submodule A M)))
      (principalPowerTorsion_smul_mem f M n)

/-- The inverse system `(M[f^(n + 1)])_n` with transition maps given by multiplication by `f`. -/
abbrev principalPowerTorsionTower (f : A) (M : ModA) :
    SequentialInverseSystem ModA :=
  Functor.ofOpSequence (principalPowerTorsionStep f M)

/-- The principal Tate module `T_f(M) = \varprojlim_n M[f^(n + 1)]`. -/
abbrev principalTateModule (f : A) (M : ModA) : ModA :=
  limit (principalPowerTorsionTower f M)

/- Textbook notation for the principal Tate module `T_f(M)`. -/
scoped[PrincipalTateModule] notation:max "T[" f "]" M:max => principalTateModule f M

-- Proof sketch: each transition map in the quotient tower
-- `M / f^(n + 2) M ⟶ M / f^(n + 1) M` is surjective, so the images into any fixed stage are
-- eventually constant.
/-- The quotient tower `(M / f^(n + 1) M)_n` attached to powers of a principal ideal is
Mittag-Leffler. -/
theorem principalPowerQuotientTower_isMittagLeffler
    (f : A) (M : ModA) :
    IsMittagLeffler (principalPowerQuotientTower f M) := sorry

-- Proof sketch: Lemma `15.94.6` provides a short exact sequence of inverse systems
-- `0 → (H^p(K) / f^(n + 1) H^p(K))_n → (H^p(K_n))_n → (H^{p + 1}(K)[f^(n + 1)])_n → 0`. The left
-- quotient tower is Mittag-Leffler by the preceding theorem, so the middle tower is
-- Mittag-Leffler exactly when the right torsion tower is.
/-- Remark 15.94.7: if a sequential inverse system `B` of `A`-modules fits into a short exact
sequence
`0 → (M / f^(n + 1) M)_n → B → (N[f^(n + 1)])_n → 0`,
then `B` is Mittag-Leffler if and only if the torsion tower `(N[f^(n + 1)])_n` is
Mittag-Leffler. Applying this with `M = H^p(K)`, `B_n = H^p(K_n)`, and `N = H^{p + 1}(K)`
recovers the textbook remark. -/
theorem principalPower_shortExact_middle_isMittagLeffler_iff_torsion
    (f : A) (M N : ModA) (B : SequentialInverseSystem ModA)
    (ι : principalPowerQuotientTower f M ⟶ B)
    (π : B ⟶ principalPowerTorsionTower f N)
    (h : ι ≫ π = 0)
    (hShort : (ShortComplex.mk ι π).ShortExact) :
    IsMittagLeffler B ↔ IsMittagLeffler (principalPowerTorsionTower f N) := sorry

end

/-! ### Lemma_15_94_8_Bhatt (from Chap15) -/
universe u

section

variable {A : Type u} [CommRing A]

namespace ModuleCat

/- Domain-style sampling:
- primary domain: ideal-power torsion modules and derived completeness over a commutative ring;
- sampled owner-side declarations:
  `Module.IsIdealPowerTorsion`,
  `Module.isIdealPowerTorsion_iff`,
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `Module.exists_pow_smul_top_eq_bot_iff_support_subset_zeroLocus`;
- best owner abstraction: the source-facing theorem should take the chapter owner predicate
  `Module.IsIdealPowerTorsion I M` together with the module-level derived-completeness predicate
  `M.IsDerivedCompleteWithRespectTo I`;
- primitive data: the ideal `I`, the module `M`, finite generation of `I`, ideal-power torsion of
  `M`, and derived completeness of `M` with respect to `I`;
- derived API: the elementwise annihilation criterion
  `Module.isIdealPowerTorsion_iff` and the support/annihilator reformulation of the conclusion.

Layer triage:
- `source-facing`: Bhatt's annihilation theorem for derived-complete ideal-power torsion modules;
- `core/canonical`: `Module.IsIdealPowerTorsion` and `ModuleCat.IsDerivedCompleteWithRespectTo`;
- `bridge/view`: the elementwise torsion criterion and the equivalent annihilator form
  `(I ^ n) • (⊤ : Submodule A M) = ⊥`. -/

-- Proof sketch: first reduce to the principal case by choosing finitely many generators of `I`
-- and proving that each generator acts nilpotently on `M`. For `I = (f)`, use
-- Example `15.94.3` to represent `M` as the cokernel of a map `u : K → L` between `(f)`-adically
-- complete modules with zero `f`-torsion. The `f`-power torsion hypothesis implies
-- `L = ⋃ₙ {x | f^n x ∈ u(K)}`; the open mapping lemmas then show `u(K)` is open in `L`, so some
-- power of `f` lands inside `u(K)`, which means that power annihilates `M`.
/-- Lemma 15.94.8 (Bhatt): if `I` is a finitely generated ideal in a ring `A` and `M` is a
derived complete `A`-module which is `I`-power torsion, then some power of `I` annihilates `M`,
i.e. `(I ^ n) • M = 0` for some `n`. In Lean the torsion hypothesis is
`Module.IsIdealPowerTorsion I M`, and the conclusion is
`(I ^ n) • (⊤ : Submodule A M) = ⊥`. -/
theorem exists_pow_smul_top_eq_bot_of_isIdealPowerTorsion_of_isDerivedCompleteWithRespectTo
    (I : Ideal A) (M : ModuleCat A) (hI : I.FG) (hMtors : Module.IsIdealPowerTorsion I M)
    (hM : M.IsDerivedCompleteWithRespectTo I) :
    ∃ n : ℕ, (I ^ n) • (⊤ : Submodule A M) = ⊥ := sorry

end ModuleCat

end

/-! ### Lemma_15_94_9 (from Chap15) -/
universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: principal-adic completion kernels for derived-complete modules over a
  commutative ring;
- sampled owner-side declarations:
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `principalIdeal`,
  `principalPowerIdeal`,
  `AdicCompletion.of`;
- best owner abstraction: the source-facing principal-power intersection ideal
  `⨅ n : ℕ, principalPowerIdeal f n`, acting on the canonical completion-kernel owner
  `LinearMap.ker (AdicCompletion.of (principalIdeal f) M)`;
- primitive data: `f : A`, `M : ModuleCat A`, the derived-completeness hypothesis with respect to
  `(f)`, and the principal completion map;
- derived API: the ring specialization where the same ideal acts on its own completion kernel.

Layer triage:
- `source-facing`: the annihilation statement for the kernel of the principal completion map;
- `core/canonical`: `AdicCompletion.of`, `LinearMap.ker`, and
  `ModuleCat.IsDerivedCompleteWithRespectTo`;
- `bridge/view`: the ring specialization yielding the square-zero conclusion. -/

local notation "J(" f ")" => ⨅ n : ℕ, principalPowerIdeal f n

-- Proof sketch: let `x` lie in the kernel of the principal-adic completion map and let
-- `g ∈ ⋂ n, (f)^n`. For each `n`, the kernel condition identifies `x` with an element divisible by
-- `f ^ n`, and since `g` lies in `(f)^n`, the products define a compatible sequence over the
-- localization `A_f`. Lemma `15.92.1` says every map from `A_f` into a derived-complete module
-- vanishes, so these products are all zero. Hence every element of `⋂ n, (f)^n` annihilates the
-- completion kernel.
/-- Lemma 15.94.9: if an `A`-module `M` is derived complete with respect to the principal ideal
`(f)`, then the intersection `J = ⋂ n, (f)^n` annihilates the kernel of the completion map
`M → lim_n M / (f)^n M`, modeled in Lean as `AdicCompletion.of (principalIdeal f) M`. -/
theorem principalPowerIntersection_smul_completionKernel_eq_bot_of_isDerivedComplete
    (f : A) (M : ModuleCat A)
    (hM : M.IsDerivedCompleteWithRespectTo (principalIdeal f)) :
    J(f) • LinearMap.ker (AdicCompletion.of (principalIdeal f) M) = ⊥ := sorry

-- Proof sketch: apply the previous theorem to the `A`-module `A` itself. The kernel of the
-- completion map `A → lim_n A / (f)^n` is exactly `⋂ n, (f)^n`, so the annihilation statement
-- becomes `J * J = 0`, i.e. `J ^ 2 = ⊥`.
/-- If the ring `A`, viewed as an `A`-module, is derived complete with respect to `(f)`, then the
intersection `⋂ n, (f)^n` is an ideal of square zero. -/
theorem principalPowerIntersection_sq_eq_bot_of_ring_isDerivedComplete
    (f : A)
    (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo (principalIdeal f)) :
    J(f) ^ 2 = ⊥ := sorry

end

/-! ### Lemma_15_94_10 (from Chap15) -/
universe u

section

variable {A : Type u} [CommRing A] {I : Ideal A}

/-
Domain-style sampling:
- primary domain: derived completeness of the ring `A`, viewed as an `A`-module, and the induced
  henselian pair structure on `(A, I)`;
- sampled owner-side declarations:
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `HenselianRing`,
  `ModuleCat.surjective_adicCompletion_of_isDerivedCompleteWithRespectTo`,
  `principalPowerIntersection_sq_eq_bot_of_ring_isDerivedComplete`;
- best owner abstraction: the source-facing statement should conclude directly in the canonical
  owner `HenselianRing A I`; the source hypothesis is already the chapter owner
  `(ModuleCat.of A A).IsDerivedCompleteWithRespectTo I`, so no additional wrapper around henselian
  pairs or derived-complete rings is appropriate here;
- primitive data: the ring `A`, the ideal `I`, and the derived-completeness hypothesis on the
  canonical `A`-module `ModuleCat.of A A`;
- derived API: principal-ideal reduction through `largestHenselianIdeal`, the principal completion
  surjectivity bridge
  `ModuleCat.surjective_adicCompletion_of_isDerivedCompleteWithRespectTo`, the locally nilpotent
  henselian owner bridge `henselianRing_of_isLocallyNilpotent`, the quotient comparison
  `henselianRing_iff_henselianRing_and_quotient_henselianRing`, and the canonical mathlib
  completion-to-henselian bridge `IsAdicComplete.henselianRing`.

Source/core/bridge triage:
- `source-facing`: the theorem below, matching the Stacks statement that derived completeness of
  `A` with respect to `I` makes `(A, I)` a henselian pair;
- `core/canonical`: `HenselianRing A I` together with the owner predicate
  `ModuleCat.IsDerivedCompleteWithRespectTo`;
- `bridge/view`: the principal-adic completion and nilpotent-intersection lemmas used to pass from
  derived completeness to the henselian owner.
-/

-- Proof sketch: use the canonical maximal owner `largestHenselianIdeal` from Lemma `15.11.15` to
-- reduce to the principal ideals generated by elements of `I`. For a fixed `f ∈ I`, derived
-- completeness with respect to `I` restricts to derived completeness with respect to the principal
-- ideal `(f)`, so Lemma `15.92.3` makes the map to the `f`-adic completion surjective. The target
-- quotient is henselian by the canonical completion owner bridge `IsAdicComplete.henselianRing`,
-- and Lemma `15.11.9` reduces the original henselianity statement to showing that the
-- intersection `⋂ n, (f)^n` is locally nilpotent; this follows from Lemma `15.94.9` together with
-- the locally nilpotent owner bridge `henselianRing_of_isLocallyNilpotent`.
/-- Lemma 15.94.10: if the ring `A`, viewed as an `A`-module, is derived complete with respect to
an ideal `I`, then the canonical owner predicate `HenselianRing A I` holds. -/
theorem henselianRing_of_isDerivedCompleteWithRespectTo
    (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I) :
    HenselianRing A I := sorry

end

/-! ### Lemma_15_94_11 (from Chap15) -/
universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: derived completeness for finitely generated ideals and the intersection of their
  powers in a commutative ring;
- sampled owner-side declarations:
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `DerivedCategory.ideal_fg_of_exists_fin_generators`,
  `principalPowerIntersection_sq_eq_bot_of_ring_isDerivedComplete`,
  `isAdicComplete_of_isReduced_of_isDerivedCompleteWithRespectTo_of_fg`;
- best owner abstraction: the source-facing ideal-level theorem on an arbitrary ideal `I`,
  together with the witness that `I` is generated by `r` elements;
- primitive data: the ideal `I`, the integer `r`, a generating-family witness
  `∃ f : Fin r → A, Ideal.span (Set.range f) = I`, and derived completeness of `A` with respect
  to `I`;
- derived API: the chosen-presentation specialization for `Ideal.span (Set.range f)`.

Layer triage:
- `source-facing`: the ideal-level nilpotence statement for `J = ⋂ n, I ^ n`;
- `core/canonical`: `ModuleCat.IsDerivedCompleteWithRespectTo` and the ideal-power intersection
  `⨅ n : ℕ, I ^ n`;
- `bridge/view`: the specialization to a chosen family `f : Fin r → A`. -/

local notation "J(" I ")" => ⨅ n : ℕ, I ^ n

-- Proof sketch: argue by induction on the number of generators. For one generator this is
-- Lemma `15.94.9`. For `I = (f₁, …, fᵣ)` with `r > 1`, choose generators, quotient by powers of
-- the last generator and use Lemma `15.92.6` to keep derived completeness after passage to
-- `A / fᵣ^t A`.
-- The image of `J(I) = ⋂ n, I^n` in each quotient lies in the corresponding intersection for
-- the ideal generated by `f₁, …, fᵣ₋₁`, so the induction hypothesis gives nilpotence of order
-- `2^(r - 1)` there. Intersecting the kernels over all `t` produces the principal-generator case
-- for `fᵣ`, whose square-zero conclusion yields `J(I)^(2^r) = 0`.
/-- Lemma 15.94.11: if a ring `A`, viewed as an `A`-module, is derived complete with respect to an
ideal `I`, then for `J(I) = ⋂ n, I^n` one has `J(I)^N = 0` with `N = 2^r` whenever `I` can be
generated by `r` elements. -/
theorem powerIntersection_pow_two_pow_eq_bot_of_ring_isDerivedComplete
    (I : Ideal A) (r : ℕ) (hgen : ∃ f : Fin r → A, Ideal.span (Set.range f) = I)
    (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I) :
    J(I) ^ (2 ^ r) = ⊥ := sorry

/-- The chosen-generator specialization of Lemma `15.94.11`. -/
theorem powerIntersection_pow_two_pow_eq_bot_of_ring_isDerivedComplete_of_span_range
    {r : ℕ} (f : Fin r → A)
    (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f))) :
    J(Ideal.span (Set.range f)) ^ (2 ^ r) = ⊥ := by
  simpa using
    powerIntersection_pow_two_pow_eq_bot_of_ring_isDerivedComplete
      (Ideal.span (Set.range f)) r ⟨f, rfl⟩ hA

end

/-! ### Lemma_15_94_12 (from Chap15) -/
universe u

section

variable {A : Type u} [CommRing A] [IsReduced A]

/- Domain-style sampling:
- primary domain: derived completeness and adic completeness for a ring viewed as a module over
  itself;
- sampled owner-side declarations:
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `ModuleCat.isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff`,
  `powerIntersection_pow_two_pow_eq_bot_of_ring_isDerivedComplete`,
  `nilradical_eq_zero`;
- best owner abstraction: the owner bridge from derived completeness plus `IsHausdorff` to
  `IsAdicComplete`, with Lemma `15.94.11` supplying the source-facing nilpotence input;
- primitive data: the ideal `I`, finite generation `hI : I.FG`, and derived completeness of `A`
  with respect to `I`;
- derived API: the adic-completeness conclusion and the intermediate Hausdorff property obtained
  from reducedness.

Layer triage:
- `source-facing`: Lemma `15.94.12`, which says reducedness kills the nilpotent intersection
  obstruction;
- `core/canonical`: `IsAdicComplete`, `IsHausdorff`, and
  `ModuleCat.IsDerivedCompleteWithRespectTo`;
- `bridge/view`: Lemma `15.94.11` turning derived completeness for finitely generated ideals into
  nilpotence of `⨅ n, I ^ n`. -/

-- Proof sketch: apply Proposition `15.92.5` to the `A`-module `A`. By Lemma `15.94.11`, finite
-- generation of `I` and derived completeness force the ideal intersection `⋂ n, I^n` to be
-- nilpotent. Since `A` is reduced, that nilpotent ideal is zero, giving the separatedness
-- hypothesis required by Proposition `15.92.5`.
/-- Lemma 15.94.12: if a reduced ring `A`, viewed as an `A`-module, is derived complete with
respect to a finitely generated ideal `I`, then `A` is `I`-adically complete. -/
theorem isAdicComplete_of_isReduced_of_isDerivedCompleteWithRespectTo_of_fg
    (I : Ideal A) (hI : I.FG) (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I) :
    IsAdicComplete I A := by
  have hIfg : I.FG := hI
  obtain ⟨s, hs⟩ := hI
  let f : Fin s.card → A := fun i ↦ (s.equivFin.symm i : A)
  have hspan : Ideal.span (Set.range f) = I := by
    rw [← hs]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hx
      exact ⟨s.equivFin ⟨x, hx⟩, by simp [f]⟩
  change IsAdicComplete I (ModuleCat.of A A)
  rw [ModuleCat.isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff hIfg]
  refine ⟨hA, ?_⟩
  refine ⟨fun x hx ↦ ?_⟩
  have hx' : x ∈ (⨅ n : ℕ, I ^ n : Ideal A) := by
    rw [Ideal.mem_iInf]
    intro n
    simpa [SModEq.zero, smul_eq_mul, Ideal.one_eq_top] using hx n
  have hpow :
      (⨅ n : ℕ, I ^ n : Ideal A) ^ (2 ^ s.card) = ⊥ := by
    exact powerIntersection_pow_two_pow_eq_bot_of_ring_isDerivedComplete I s.card ⟨f, hspan⟩ hA
  have hxpow : x ^ (2 ^ s.card) = 0 := by
    have : x ^ (2 ^ s.card) ∈ (⨅ n : ℕ, I ^ n : Ideal A) ^ (2 ^ s.card) :=
      Ideal.pow_mem_pow hx' _
    simpa [hpow] using this
  have hxnil : x ∈ nilradical A := mem_nilradical.2 ⟨2 ^ s.card, hxpow⟩
  simpa [nilradical_eq_zero A] using hxnil

end
