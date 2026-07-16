import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Lemma_10_46_8
import stacks_proof.stacks_project.Chap10.Lemma_10_155_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
open IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

noncomputable section

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsPrime]
variable (q : Ideal S) [q.IsPrime] [q.LiesOver p]
variable {Rpsh Ssh : Type u} [CommRing Rpsh] [CommRing Ssh]
variable [Algebra (Localization.AtPrime p) Rpsh]
variable [IsStrictHenselizationOf (Localization.AtPrime p) Rpsh]
variable [Algebra (Localization.AtPrime q) Ssh]
variable [IsStrictHenselizationOf (Localization.AtPrime q) Ssh]

local notation "Rp" => Localization.AtPrime p
local notation "Sq" => Localization.AtPrime q

noncomputable local instance :
    Algebra Rp Sq :=
  (Localization.localRingHom p q (algebraMap R S) (q.over_def p)).toAlgebra

local instance :
    IsLocalHom (algebraMap Rp Sq) := by
  simpa [RingHom.algebraMap_toAlgebra] using
    Localization.isLocalHom_localRingHom p q (algebraMap R S) (q.over_def p)

variable (φ : ResidueField Rpsh →+* ResidueField Ssh)
variable (hφ :
  φ.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rpsh)) =
    (ResidueField.map (algebraMap (Localization.AtPrime q) Ssh)).comp
      (ResidueField.map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))))

local notation "comparison" => (strictHenselizationComparison p q φ hφ : Rpsh →+* Ssh)

/- Domain-style sampling:
- primary domain: local commutative algebra of strict henselizations and quasi-finite maps at a
  prime;
- sampled owner declarations of the same kind:
  `IsStrictHenselizationOf`,
  `strictHenselizationComparison`,
  `RingHom.Finite`,
  `FiniteDimensional`,
  `IsPurelyInseparable`;
- best owner abstraction: the canonical comparison `Rₚ^sh → S_q^sh` from Lemma `10.155.12` is
  the owner object, and its finiteness/locality consequences should be stated on that comparison
  via `RingHom.Finite`, `IsLocalHom`, and the direct residue-field extension owners
  `FiniteDimensional` and `IsPurelyInseparable`, rather than through a parallel public `Algebra`
  bridge or the generic all-primes predicate;
- primitive data: the strict henselization owners on `Rₚ` and `S_q`, together with the
  compatible residue-field map `φ`;
- derived API: finiteness of the canonical comparison, its locality, and the induced residue-field
  consequences.

Source/core/bridge triage:
- `source-facing`: the quasi-finite finiteness, locality, and residue-field consequences for the
  induced map `Rₚ^sh → S_q^sh`;
- `core/canonical`: `IsStrictHenselizationOf`, `strictHenselizationComparison`, and
  `strictHenselizationTensorPrime`, together with the finiteness owner `RingHom.Finite`;
- `bridge/view`: the chosen residue-field map `φ`, which determines the canonical comparison
  `strictHenselizationComparison p q φ hφ`.
-/

/- Lemma 10.156.3 (1): the strict-henselization comparison and its canonical tensor prime are
already owned by Lemma `10.155.12`. The quasi-finite specialization here should therefore reuse
that owner directly, rather than restating a second tensor-prime construction. -/
recall isStrictHenselizationOf_localizationAt_strictHenselizationTensorPrime

-- Proof sketch: apply the quasi-finite finiteness statement over the strictly henselian base
-- `R_p^sh` to the canonical comparison `strictHenselizationComparison p q φ hφ`.
/-- The canonical comparison map `R_p^sh → S_q^sh` induced by the compatible residue-field map
`φ` is finite under the quasi-finite hypothesis at `q`. -/
theorem strictHenselizationComparison_finite_of_quasiFiniteAt
    [Algebra.QuasiFiniteAt R q] :
    RingHom.Finite comparison := by
  -- TODO: prove the structural finite-map step by showing that the localized tensor product
  -- `Rpsh ⊗[R] S` at the canonical strict-henselization tensor prime is finite over `Rpsh`
  -- from the mathlib `Algebra.QuasiFiniteAt R q` hypothesis, then compose with the strict
  -- henselization map supplied by Lemma 10.155.12.
  sorry

private theorem strictHenselizationComparison_isLocalHom_aux :
    IsLocalHom comparison := by
  let _ : Algebra Rp Ssh := ((algebraMap Sq Ssh).comp (algebraMap Rp Sq)).toAlgebra
  let _ : IsScalarTower Rp Sq Ssh := IsScalarTower.of_algebraMap_eq' rfl
  let hexists :=
    ExistsUnique.exists <|
      existsUnique_algHom_between_strictHenselizations_of_residueFieldMap
        (RingEquiv.refl _) rfl
        (RingEquiv.refl _) rfl
        φ hφ
  let hchosen := Classical.choose_spec hexists
  rcases hchosen with ⟨hlocal, -⟩
  simpa [strictHenselizationComparison] using hlocal

/-- The canonical comparison map `R_p^sh → S_q^sh` induced by `φ` is local, since
`strictHenselizationComparison` is chosen from the unique local map supplied by
Lemma `10.155.10`. -/
theorem strictHenselizationComparison_isLocalHom :
    IsLocalHom comparison :=
  strictHenselizationComparison_isLocalHom_aux p q φ hφ

instance strictHenselizationComparison_isLocalHomInst :
    IsLocalHom comparison :=
  strictHenselizationComparison_isLocalHom p q φ hφ

/-- Helper for Chap10 Lemma 10 156 3: a finite local map out of a strictly henselian local ring
induces a finite-dimensional purely inseparable extension on ordinary residue fields. -/
private lemma residueField_finite_purelyInseparable_of_finite_localHom
    {A B : Type u} [CommRing A] [CommRing B] [StrictHenselianLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hf : RingHom.Finite f) :
    let _ : Algebra (ResidueField A) (ResidueField B) := RingHom.toAlgebra (ResidueField.map f)
    let _ : Module (ResidueField A) (ResidueField B) :=
      (RingHom.toAlgebra (ResidueField.map f)).toModule
    FiniteDimensional (ResidueField A) (ResidueField B) ∧
      IsPurelyInseparable (ResidueField A) (ResidueField B) := by
  -- View `f` as the algebra map so that the standard residue-field finiteness theorem applies.
  letI : Algebra A B := RingHom.toAlgebra f
  letI : IsLocalHom (algebraMap A B) := by
    simpa [RingHom.algebraMap_toAlgebra] using (inferInstance : IsLocalHom f)
  letI : Module.Finite A B := by
    rw [← RingHom.finite_algebraMap]
    simpa [RingHom.algebraMap_toAlgebra] using hf
  have hmap : algebraMap (ResidueField A) (ResidueField B) = ResidueField.map f := rfl
  have hfres : RingHom.Finite (ResidueField.map f) := by
    -- First prove finiteness for the canonical residue-field algebra map, then rewrite it to
    -- the explicit `RingHom.toAlgebra (ResidueField.map f)` surface used by this item.
    rw [← hmap]
    rw [RingHom.finite_algebraMap]
    exact IsLocalRing.ResidueField.finite_of_module_finite (R := A) (S := B)
  letI : Algebra (ResidueField A) (ResidueField B) := RingHom.toAlgebra (ResidueField.map f)
  letI : Module (ResidueField A) (ResidueField B) :=
    (RingHom.toAlgebra (ResidueField.map f)).toModule
  have hfresModule : Module.Finite (ResidueField A) (ResidueField B) := by
    rw [← RingHom.finite_algebraMap]
    exact hfres
  dsimp
  constructor
  · exact hfresModule
  · -- A finite extension is algebraic, and over a separably closed field algebraic extensions are
    -- purely inseparable.
    letI : Module.Finite (ResidueField A) (ResidueField B) := hfresModule
    letI : Algebra.IsAlgebraic (ResidueField A) (ResidueField B) :=
      Algebra.IsAlgebraic.of_finite (ResidueField A) (ResidueField B)
    exact Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed

noncomputable local instance residueFieldComparisonAlgebra :
    Algebra (ResidueField Rpsh) (ResidueField Ssh) :=
  RingHom.toAlgebra (ResidueField.map comparison)

local instance residueFieldComparisonModule :
    Module (ResidueField Rpsh) (ResidueField Ssh) :=
  (RingHom.toAlgebra (ResidueField.map comparison)).toModule

-- Proof sketch: the residue-field extension induced by the canonical comparison
-- `R_p^sh → S_q^sh` is the unique residue-field extension controlled by quasi-finiteness at `q`.
-- Since both source and target are local, the natural owner surface here is the direct field
-- extension `ResidueField S_q^sh / ResidueField R_p^sh`, expressed by `FiniteDimensional` and
-- `IsPurelyInseparable`.
/-- Under the quasi-finite hypothesis at `q`, the residue-field extension induced by the canonical
comparison `R_p^sh → S_q^sh` is finite-dimensional and purely inseparable. -/
theorem residueField_finite_purelyInseparable_strictHenselizationComparison_of_quasiFiniteAt
    [Algebra.QuasiFiniteAt R q] :
    let _ : Algebra (ResidueField Rpsh) (ResidueField Ssh) :=
      RingHom.toAlgebra (ResidueField.map comparison)
    let _ : Module (ResidueField Rpsh) (ResidueField Ssh) :=
      (RingHom.toAlgebra (ResidueField.map comparison)).toModule
    FiniteDimensional (ResidueField Rpsh) (ResidueField Ssh) ∧
      IsPurelyInseparable (ResidueField Rpsh) (ResidueField Ssh) := by
  -- Reduce the residue-field statement to the finite local comparison map proved above.
  exact residueField_finite_purelyInseparable_of_finite_localHom comparison
    (strictHenselizationComparison_finite_of_quasiFiniteAt p q φ hφ)

end

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsPrime]
variable (q : Ideal S) [q.IsPrime] [q.LiesOver p]
variable {Rpsh Ssh : Type u} [CommRing Rpsh] [CommRing Ssh]
variable {K1sep : Type v} {K2sep : Type w} [Field K1sep] [Field K2sep]
variable [Algebra (Localization.AtPrime p) Rpsh]
variable [IsStrictHenselizationOf (Localization.AtPrime p) Rpsh]
variable [Algebra (Localization.AtPrime q) Ssh]
variable [IsStrictHenselizationOf (Localization.AtPrime q) Ssh]
variable [Algebra K1sep K2sep]

local notation "Rp" => Localization.AtPrime p
local notation "Sq" => Localization.AtPrime q

noncomputable local instance :
    Algebra Rp Sq :=
  (Localization.localRingHom p q (algebraMap R S) (q.over_def p)).toAlgebra

local instance :
    IsLocalHom (algebraMap Rp Sq) := by
  simpa [RingHom.algebraMap_toAlgebra] using
    Localization.isLocalHom_localRingHom p q (algebraMap R S) (q.over_def p)

variable (φ : ResidueField Rpsh →+* ResidueField Ssh)
variable (hφ :
  φ.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rpsh)) =
    (ResidueField.map (algebraMap (Localization.AtPrime q) Ssh)).comp
      (ResidueField.map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))))

-- Proof sketch: transport the previous residue-field statement across the chosen identifications
-- `ResidueField R_p^sh ≃ K1sep` and `ResidueField S_q^sh ≃ K2sep`, now expressed directly against
-- the compatible residue-field map `φ` that determines the canonical comparison
-- `R_p^sh → S_q^sh`.
/-- Under chosen identifications of `ResidueField R_p^sh` and `ResidueField S_q^sh` with `K1sep`
and `K2sep`, if the chosen residue-field map `φ` agrees with `algebraMap K1sep K2sep`, then the
extension `K2sep / K1sep` is finite and purely inseparable under the quasi-finite hypothesis at
`q`. -/
theorem sepClosureExtension_finite_purelyInseparable_of_quasiFiniteAt
    [Algebra.QuasiFiniteAt R q]
    (ιR : ResidueField Rpsh ≃+* K1sep)
    (ιS : ResidueField Ssh ≃+* K2sep)
    (hι :
      ιS.toRingHom.comp φ =
        (algebraMap K1sep K2sep).comp ιR.toRingHom) :
    FiniteDimensional K1sep K2sep ∧ IsPurelyInseparable K1sep K2sep := by
  -- TODO: prove that `ResidueField.map (strictHenselizationComparison p q φ hφ) = φ` from the
  -- chosen strict-henselization comparison, then transport the previous residue-field result
  -- across `ιR` and `ιS` using `hι`.
  sorry

end
