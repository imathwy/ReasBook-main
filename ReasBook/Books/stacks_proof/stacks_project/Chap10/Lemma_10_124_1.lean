import Mathlib.Tactic.Recall
import Mathlib.Tactic.StacksAttribute
import StacksProject_2024.Chap10.Lemma_10_121_8
import StacksProject_2024.Chap10.Lemma_10_123_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open IsLocalRing
open Topology

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]
variable [FiniteDimensional (FractionRing A) (FractionRing B)]

local notation "κA" => Ideal.ResidueField (maximalIdeal A)

-- Semantic search note: `lean_leansearch` only surfaced the canonical owner `Ring.ordFrac`; the
-- source-facing closed-fiber formulation was then verified directly against the local
-- `Ideal.primesOver`/`LiesOver` API and the Stacks source proof.
/-- The maximal ideals of `B` lying over the closed point of `Spec A`. -/
abbrev ClosedFiberMaximalSpectrum
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] :=
  { m : MaximalSpectrum B // m.asIdeal.LiesOver (maximalIdeal A) }

/-- The defining subtype witness supplies the `LiesOver` instance needed for closed-fiber
constructions. -/
instance instLiesOverClosedFiberMaximalSpectrum
    (m : ClosedFiberMaximalSpectrum A B) : m.1.asIdeal.LiesOver (maximalIdeal A) :=
  m.2

/-- A closed-fiber maximal ideal of `B` induces the canonical `κ(A)`-algebra structure on its
residue field. -/
noncomputable instance residueFieldAlgebraOfClosedFiberMaximalSpectrum
    (m : ClosedFiberMaximalSpectrum A B) :
    Algebra κA (Ideal.ResidueField m.1.asIdeal) :=
  (Ideal.ResidueField.map (maximalIdeal A) m.1.asIdeal (algebraMap A B) m.2.over).toAlgebra

/-- Helper for Chap10 Lemma 10 124 1: the logarithmic fraction-field order of a nonzero
ring element is the finite ring order converted to a natural number. -/
private theorem log_ordFrac_algebraMap_eq_ord_toNat
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    (x : R) (hx : x ≠ 0) :
    WithZero.log (Ring.ordFrac R (algebraMap R K x)) = (Ring.ord R x).toNat := by
  -- Move from the fraction-field valuation to the ring-level valuation owner.
  rw [Ring.ordFrac_eq_ord R x hx]
  have hxNonZeroDivisor : x ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hx
  have hfinite : Ring.ord R x ≠ ⊤ := by
    -- In a one-dimensional Noetherian domain, quotienting by a nonzero principal ideal has
    -- finite length, so its order of vanishing is not infinite.
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton R hxNonZeroDivisor)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  -- Unfold the multiplicative order owner once; the nonzerodivisor branch is the exponential of
  -- the finite `ℕ∞` order, whose logarithm is definitional after rewriting by `hn`.
  simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  rw [if_pos hxNonZeroDivisor, ← hn]
  rfl

/-- Helper for Chap10 Lemma 10 124 1: a nonzero element of a one-dimensional Noetherian domain
has finite order of vanishing. -/
private theorem ord_ne_top_of_ne_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (x : R) (hx : x ≠ 0) :
    Ring.ord R x ≠ ⊤ := by
  -- The principal quotient by a nonzero element has finite length, so the order owner is finite.
  exact Module.length_ne_top_iff.mpr
    (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_iff_ne_zero.mpr hx))

/-- Helper for Chap10 Lemma 10 124 1: the structural map `A → Frac(B)` is injective, so nonzero
elements of `A` stay nonzero in the common fraction field. -/
private theorem fractionRingB_map_ne_zero_of_ne_zero
    [Algebra (FractionRing A) (FractionRing B)]
    [IsScalarTower A (FractionRing A) (FractionRing B)]
    (x : A) (hx : x ≠ 0) :
    algebraMap A (FractionRing B) x ≠ 0 := by
  intro hxFracB
  exact hx <|
    (algebraMap_injective_of_field_isFractionRing
      A (FractionRing B) (FractionRing A) (FractionRing B)) <|
      by simpa using hxFracB

/-- Helper for Chap10 Lemma 10 124 1: under module-finiteness, the closed-fiber subtype is just
the full maximal spectrum because every maximal ideal lies over `maximalIdeal A`. -/
private def closedFiberMaximalSpectrumEquivOfModuleFinite
    [Module.Finite A B] :
    MaximalSpectrum B ≃ ClosedFiberMaximalSpectrum A B :=
  { toFun := fun m ↦ ⟨m, maximalIdeal_liesOver_of_moduleFinite A m⟩
    invFun := fun m ↦ m.1
    left_inv := fun _ ↦ rfl
    right_inv := fun m ↦ by
      cases m
      rfl }

/-- Helper for Chap10 Lemma 10 124 1: if `C` is finite over `A`, then every residue field of `C`
inherits the canonical `κ(A)`-algebra structure from Lemma `10.121.8`. -/
private noncomputable instance residueFieldAlgebraOfFiniteSubalgebra
    {C : Subalgebra A B} [Module.Finite A C] (m : MaximalSpectrum C) :
    Algebra κA (Ideal.ResidueField m.asIdeal) :=
  residueFieldAlgebra_of_moduleFinite A m

/-- Helper for Chap10 Lemma 10 124 1: residue fields of finite intermediate subalgebras are
finite-dimensional over `κ(A)`. -/
private instance moduleFiniteResidueFieldOfFiniteSubalgebra
    {C : Subalgebra A B} [Module.Finite A C] (m : MaximalSpectrum C) :
    Module.Finite κA (Ideal.ResidueField m.asIdeal) :=
  moduleFinite_residueField_of_moduleFinite A m

/-- Helper for Chap10 Lemma 10 124 1: the base algebra map into any intermediate subalgebra
`C ⊆ B` is injective because composing with the inclusion `C → B` recovers the injective map
`A → B`. -/
private theorem subalgebra_algebraMap_injective
    {C : Subalgebra A B} :
    Function.Injective (algebraMap A C) := by
  intro a b hab
  apply (algebraMap_injective_of_field_isFractionRing
    A B (FractionRing A) (FractionRing B))
  simpa using congrArg (fun z : C ↦ (z : B)) hab

/-- Helper for Chap10 Lemma 10 124 1: the composite map `A → C → Frac(C)` is injective for every
intermediate subalgebra `C ⊆ B`. -/
private theorem subalgebra_fractionRing_algebraMap_injective
    {C : Subalgebra A B} :
    Function.Injective (algebraMap A (FractionRing ↥C)) := by
  -- Proof comment: the map `A → Frac(C)` is the composite of the injective map `A → C` with the
  -- injective fraction-field map `C → Frac(C)`.
  simpa using Function.Injective.comp
    (IsFractionRing.injective (↥C) (FractionRing ↥C))
    subalgebra_algebraMap_injective

/-- Helper for Chap10 Lemma 10 124 1: the canonical action of `A` on the fraction field of any
intermediate subalgebra `C ⊆ B` is faithful. -/
private theorem faithfulSMul_fractionRing_of_subalgebra
    {C : Subalgebra A B} :
    FaithfulSMul A (FractionRing C) := by
  -- Proof comment: faithfulness is equivalent to injectivity of `A → Frac(C)`, already isolated
  -- in the preceding helper.
  exact (faithfulSMul_iff_algebraMap_injective A (FractionRing C)).mpr
    (subalgebra_fractionRing_algebraMap_injective (C := C))

/-- Helper for Chap10 Lemma 10 124 1: a nonzero element of `A` remains nonzero after localizing
`B` at any maximal ideal in the module-finite case. -/
private theorem localizationAtPrime_map_ne_zero_of_ne_zero
    [Module.Finite A B]
    (m : MaximalSpectrum B) (x : A) (hx : x ≠ 0) :
    algebraMap A (Localization.AtPrime m.asIdeal) x ≠ 0 := by
  -- First keep `x` nonzero in `B`, then use injectivity of the localization map.
  have hBx0 : algebraMap A B x ≠ 0 := by
    intro hxB
    exact hx <|
      (algebraMap_injective_of_field_isFractionRing
        A B (FractionRing A) (FractionRing B)) <|
        by simpa using hxB
  intro hxLoc
  have hinjLoc : Function.Injective (algebraMap B (Localization.AtPrime m.asIdeal)) :=
    IsLocalization.injective
      (Localization.AtPrime m.asIdeal) m.asIdeal.primeCompl_le_nonZeroDivisors
  exact hBx0 <| hinjLoc <| by
    simpa [IsScalarTower.algebraMap_eq A B (Localization.AtPrime m.asIdeal)] using hxLoc

/-- Helper for Chap10 Lemma 10 124 1: under module-finiteness, Lemma `10.121.8` rewrites to the
source-facing `ℕ∞` equality for the weighted sum of local orders over the closed fiber of
`Spec B → Spec A`. -/
private theorem sum_residueFieldDegree_mul_local_ord_eq_fractionFieldDegree_mul_ord_of_moduleFinite
    (hfinite : Module.Finite A B)
    (x : A) (hx : x ∈ maximalIdeal A) (hx0 : x ≠ 0) :
    (let _ : Finite (MaximalSpectrum B) := finite_maximalSpectrum_of_moduleFinite A
    let _ : Finite (ClosedFiberMaximalSpectrum A B) := by infer_instance
    let _ : Fintype (ClosedFiberMaximalSpectrum A B) :=
      Fintype.ofFinite (ClosedFiberMaximalSpectrum A B)
    ∑ m : ClosedFiberMaximalSpectrum A B,
      (Module.finrank κA (Ideal.ResidueField m.1.asIdeal) : ℕ∞) *
        Ring.ord (Localization.AtPrime m.1.asIdeal)
          (algebraMap A (Localization.AtPrime m.1.asIdeal) x)) =
      (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x := by
  classical
  letI : Module.Finite A B := hfinite
  letI : Finite (MaximalSpectrum B) := finite_maximalSpectrum_of_moduleFinite A
  letI : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
  letI : Finite (ClosedFiberMaximalSpectrum A B) := by infer_instance
  letI : Fintype (ClosedFiberMaximalSpectrum A B) := Fintype.ofFinite (ClosedFiberMaximalSpectrum A B)
  letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  letI : ∀ m : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
    fun m ↦
      IsLocalization.isNoetherianRing m.asIdeal.primeCompl
        (Localization.AtPrime m.asIdeal) inferInstance
  letI : ∀ m : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal) :=
    fun m ↦ krullDimLE_one_localizationAtPrime_of_moduleFinite A m
  letI : ∀ m : MaximalSpectrum B,
      IsScalarTower A (Localization.AtPrime m.asIdeal) (FractionRing B) :=
    fun m ↦
      IsScalarTower.of_algebraMap_eq fun a ↦ by
        -- Proof comment: the direct base map `A → Frac(B)` factors through the localization
        -- `B_m`, and the factorization is the standard scalar-tower composite.
        change algebraMap A (FractionRing B) a =
          algebraMap (Localization.AtPrime m.asIdeal) (FractionRing B)
            (algebraMap B (Localization.AtPrime m.asIdeal) (algebraMap A B a))
        calc
          algebraMap A (FractionRing B) a =
              algebraMap B (FractionRing B) (algebraMap A B a) := by
                exact (IsScalarTower.algebraMap_apply A B (FractionRing B) a).symm
          _ =
              algebraMap (Localization.AtPrime m.asIdeal) (FractionRing B)
                (algebraMap B (Localization.AtPrime m.asIdeal) (algebraMap A B a)) := by
                  exact IsScalarTower.algebraMap_apply B (Localization.AtPrime m.asIdeal)
                    (FractionRing B) (algebraMap A B a)
  let y : (FractionRing B)ˣ :=
    Units.mk0 (algebraMap A (FractionRing B) x)
      (fractionRingB_map_ne_zero_of_ne_zero x hx0)
  have hlogBase :
      WithZero.log (Ring.ordFrac A (algebraMap A (FractionRing A) x)) =
        ((Ring.ord A x).toNat : ℤ) := by
    simpa using
      (log_ordFrac_algebraMap_eq_ord_toNat x hx0)
  have hlogLocal (m : MaximalSpectrum B) :
      WithZero.log (Ring.ordFrac (Localization.AtPrime m.asIdeal) (y : FractionRing B)) =
        ((Ring.ord (Localization.AtPrime m.asIdeal)
          (algebraMap A (Localization.AtPrime m.asIdeal) x)).toNat : ℤ) := by
    -- Proof comment: the chosen unit is exactly the image of `x` in the local fraction field.
    simpa [y, IsScalarTower.algebraMap_eq A (Localization.AtPrime m.asIdeal) (FractionRing B)] using
      (log_ordFrac_algebraMap_eq_ord_toNat
        (algebraMap A (Localization.AtPrime m.asIdeal) x)
        (localizationAtPrime_map_ne_zero_of_ne_zero m x hx0))
  have hnorm :
      Algebra.norm (FractionRing A) (y : FractionRing B) =
        (algebraMap A (FractionRing A) x) ^
          Module.finrank (FractionRing A) (FractionRing B) := by
    -- Proof comment: the field norm of a scalar from the base is the corresponding power.
    simpa [y, IsScalarTower.algebraMap_eq A (FractionRing A) (FractionRing B)] using
      (Algebra.norm_algebraMap (FractionRing A) (FractionRing B)
        (algebraMap A (FractionRing A) x))
  have hmainInt :
      WithZero.log (Ring.ordFrac A (Algebra.norm (FractionRing A) (y : FractionRing B))) =
        (let _ : Finite (MaximalSpectrum B) := finite_maximalSpectrum_of_moduleFinite A
         let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
         let _ : IsNoetherianRing B := IsNoetherianRing.of_finite A B
         let _ : ∀ m : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
           fun m ↦
             IsLocalization.isNoetherianRing m.asIdeal.primeCompl
               (Localization.AtPrime m.asIdeal) inferInstance
         let _ : ∀ m : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal) :=
           fun m ↦ krullDimLE_one_localizationAtPrime_of_moduleFinite A m
         ∑ m : MaximalSpectrum B,
           (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
             WithZero.log (Ring.ordFrac (Localization.AtPrime m.asIdeal) (y : FractionRing B))) := by
    simpa using ordFrac_norm_eq_sum_residueFieldDegree_mul_local_ordFrac A y
  have hmainInt' :
      (((Module.finrank (FractionRing A) (FractionRing B) *
          (Ring.ord A x).toNat : ℕ) : ℤ)) =
        ∑ m : MaximalSpectrum B,
          (((Module.finrank κA (Ideal.ResidueField m.asIdeal) *
              (Ring.ord (Localization.AtPrime m.asIdeal)
                (algebraMap A (Localization.AtPrime m.asIdeal) x)).toNat : ℕ) : ℤ)) := by
    -- Proof comment: rewrite the norm side and every local term into the ring-level order owners.
    simpa [hnorm, hlogBase, hlogLocal, Nat.cast_mul, nsmul_eq_mul, mul_comm, mul_left_comm,
      mul_assoc] using hmainInt
  have hmainNat :
      Module.finrank (FractionRing A) (FractionRing B) * (Ring.ord A x).toNat =
        ∑ m : MaximalSpectrum B,
          Module.finrank κA (Ideal.ResidueField m.asIdeal) *
            (Ring.ord (Localization.AtPrime m.asIdeal)
              (algebraMap A (Localization.AtPrime m.asIdeal) x)).toNat := by
    exact_mod_cast hmainInt'
  have hmainENat :
      ((Module.finrank (FractionRing A) (FractionRing B) * (Ring.ord A x).toNat : ℕ) : ℕ∞) =
        ∑ m : MaximalSpectrum B,
          ((Module.finrank κA (Ideal.ResidueField m.asIdeal) *
              (Ring.ord (Localization.AtPrime m.asIdeal)
                (algebraMap A (Localization.AtPrime m.asIdeal) x)).toNat : ℕ) : ℕ∞) := by
    simpa [Nat.cast_sum] using congrArg (fun n : ℕ ↦ (n : ℕ∞)) hmainNat
  have hbaseENat :
      ((Module.finrank (FractionRing A) (FractionRing B) * (Ring.ord A x).toNat : ℕ) : ℕ∞) =
        (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x := by
    -- Proof comment: `x ≠ 0` makes the base order finite, so the `ℕ∞` product is a casted natural.
    rw [← ENat.coe_toNat (ord_ne_top_of_ne_zero x hx0)]
    simp
  have htermENat (m : MaximalSpectrum B) :
      ((Module.finrank κA (Ideal.ResidueField m.asIdeal) *
          (Ring.ord (Localization.AtPrime m.asIdeal)
            (algebraMap A (Localization.AtPrime m.asIdeal) x)).toNat : ℕ) : ℕ∞) =
        (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℕ∞) *
          Ring.ord (Localization.AtPrime m.asIdeal)
            (algebraMap A (Localization.AtPrime m.asIdeal) x) := by
    -- Proof comment: each localized order is finite because `x` stays nonzero after localization.
    rw [← ENat.coe_toNat
      (ord_ne_top_of_ne_zero
        (algebraMap A (Localization.AtPrime m.asIdeal) x)
        (localizationAtPrime_map_ne_zero_of_ne_zero m x hx0))]
    simp
  have hsumMax :
      ∑ m : MaximalSpectrum B,
        (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℕ∞) *
          Ring.ord (Localization.AtPrime m.asIdeal)
            (algebraMap A (Localization.AtPrime m.asIdeal) x) =
        (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x := by
    -- Proof comment: after converting the integer identity to `ℕ∞`, rewrite both sides back to
    -- the source-facing weighted-order terms.
    calc
      ∑ m : MaximalSpectrum B,
          (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℕ∞) *
            Ring.ord (Localization.AtPrime m.asIdeal)
              (algebraMap A (Localization.AtPrime m.asIdeal) x)
        =
          ∑ m : MaximalSpectrum B,
            ((Module.finrank κA (Ideal.ResidueField m.asIdeal) *
                (Ring.ord (Localization.AtPrime m.asIdeal)
                  (algebraMap A (Localization.AtPrime m.asIdeal) x)).toNat : ℕ) : ℕ∞) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            symm
            exact htermENat m
      _ = ((Module.finrank (FractionRing A) (FractionRing B) *
            (Ring.ord A x).toNat : ℕ) : ℕ∞) := hmainENat.symm
      _ = (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x :=
            hbaseENat
  -- Proof comment: under module-finiteness every maximal ideal lies over the closed point, so the
  -- closed-fiber sum is just a reindexed copy of the maximal-spectrum sum above.
  simpa [closedFiberMaximalSpectrumEquivOfModuleFinite] using
    (Fintype.sum_equiv closedFiberMaximalSpectrumEquivOfModuleFinite
      (fun m : MaximalSpectrum B ↦
        (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℕ∞) *
          Ring.ord (Localization.AtPrime m.asIdeal)
            (algebraMap A (Localization.AtPrime m.asIdeal) x))
      (fun m : ClosedFiberMaximalSpectrum A B ↦
        (Module.finrank κA (Ideal.ResidueField m.1.asIdeal) : ℕ∞) *
          Ring.ord (Localization.AtPrime m.1.asIdeal)
            (algebraMap A (Localization.AtPrime m.1.asIdeal) x))
      (fun _ ↦ rfl)).symm.trans hsumMax

/-- Helper for Chap10 Lemma 10 124 1: over the generic point of `Spec A`, a prime of `B` must be
the generic point when the fraction-field extension is finite. -/
private theorem primeOverBot_eq_bot_of_finiteType_fractionExtension
    (q : Ideal B) [q.IsPrime]
    (hcomap : Ideal.comap (algebraMap A B) q = ⊥) :
    q = ⊥ := by
  have hinj : Function.Injective (algebraMap A B) :=
    algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B)
  have hq : q.LiesOver (⊥ : Ideal A) := ⟨hcomap.symm⟩
  have hbound :
      ENat.toNat (Ideal.primeHeight q) +
          Cardinal.toNat (Algebra.trdeg (⊥ : Ideal A).ResidueField q.ResidueField) ≤
        ENat.toNat (Ideal.primeHeight (⊥ : Ideal A)) +
          Cardinal.toNat (Algebra.trdeg (FractionRing A) (FractionRing B)) :=
    primeHeight_add_residueFieldTrdeg_le_primeHeight_add_fractionRing_trdeg_of_finiteType
      hinj (⊥ : Ideal A) q hq
  have hbot_height : Ideal.primeHeight (⊥ : Ideal A) = 0 := by
    rw [Ideal.primeHeight_eq_zero_iff]
    simp [IsDomain.minimalPrimes_eq_singleton_bot A]
  have hgeneric :
      Cardinal.toNat (Algebra.trdeg (FractionRing A) (FractionRing B)) = 0 := by
    -- Proof comment: finite-dimensional field extensions are algebraic, so the transcendence
    -- degree of the generic fiber vanishes.
    simpa using
      congrArg Cardinal.toNat
        (show Algebra.trdeg (FractionRing A) (FractionRing B) = 0 by
          exact (trdeg_eq_zero : Algebra.trdeg (FractionRing A) (FractionRing B) = 0))
  have hbound_zero :
      ENat.toNat (Ideal.primeHeight q) +
          Cardinal.toNat (Algebra.trdeg (⊥ : Ideal A).ResidueField q.ResidueField) ≤ 0 := by
    simpa [hbot_height, hgeneric] using hbound
  have hheight_toNat : ENat.toNat (Ideal.primeHeight q) = 0 := by
    -- Proof comment: the residue transcendence term is nonnegative, so the height term must be
    -- zero.
    omega
  have hheight_zero : Ideal.primeHeight q = 0 := by
    letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
    have hfinite : Ideal.primeHeight q ≠ ⊤ := Ideal.primeHeight_ne_top q
    rw [← ENat.coe_toNat hfinite]
    exact_mod_cast hheight_toNat
  have hmin : q ∈ minimalPrimes B := Ideal.primeHeight_eq_zero_iff.mp hheight_zero
  -- Proof comment: a domain has only one minimal prime, namely `⊥`.
  simpa [IsDomain.minimalPrimes_eq_singleton_bot B] using hmin

/-- Helper for Chap10 Lemma 10 124 1: the closed fiber over the maximal ideal of `A` is finite
under the finite-type and finite fraction-field extension hypotheses. -/
private theorem finite_primesOver_maximalIdeal_of_localDomain_fractionExtension :
    Finite ((maximalIdeal A).primesOver B) := by
  by_cases hfield : IsField A
  · have hmax_bot : maximalIdeal A = (⊥ : Ideal A) :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
    refine Finite.of_injective (fun _ : (maximalIdeal A).primesOver B ↦ PUnit.unit) ?_
    intro P Q _
    apply Subtype.ext
    have hPcomap : Ideal.comap (algebraMap A B) P.1 = ⊥ := by
      have hover : maximalIdeal A = Ideal.comap (algebraMap A B) P.1 := P.2.2.over
      simpa [hmax_bot] using hover.symm
    have hQcomap : Ideal.comap (algebraMap A B) Q.1 = ⊥ := by
      have hover : maximalIdeal A = Ideal.comap (algebraMap A B) Q.1 := Q.2.2.over
      simpa [hmax_bot] using hover.symm
    rw [primeOverBot_eq_bot_of_finiteType_fractionExtension P.1 hPcomap]
    rw [primeOverBot_eq_bot_of_finiteType_fractionExtension Q.1 hQcomap]
  · have hdim : ringKrullDim A = 1 := by
      have hnot_dim0 : ¬ ringKrullDim A ≤ 0 := fun hdim0 ↦ by
        have hkrull0 : Ring.KrullDimLE 0 A := Ring.krullDimLE_iff.mpr hdim0
        exact hfield Ring.KrullDimLE.isField_of_isDomain
      have hle : ringKrullDim A ≤ 1 := Ring.krullDimLE_iff.mp inferInstance
      exact le_antisymm hle (Order.succ_le_of_lt (lt_of_not_ge hnot_dim0))
    exact finite_primesOver_maximalIdeal_of_finite_fractionField_extension hdim

/-- Helper for Chap10 Lemma 10 124 1: a one-dimensional local domain with finite-type target and
finite fraction-field extension is quasi-finite. -/
private theorem quasiFinite_of_localDomain_finiteFractionExtension :
    Algebra.QuasiFinite A B := by
  -- Proof comment: every prime of the local base is either the generic point or the closed point,
  -- and both fibers are finite by the two helper lemmas above.
  rw [Algebra.QuasiFinite.iff_finite_primesOver]
  intro p hp
  by_cases hp0 : p = ⊥
  · subst hp0
    refine Finite.of_injective (fun q : (⊥ : Ideal A).primesOver B ↦ PUnit.unit) ?_
    intro q₁ q₂ _
    apply Subtype.ext
    rw [primeOverBot_eq_bot_of_finiteType_fractionExtension q₁.1 q₁.2.2.over.symm]
    rw [primeOverBot_eq_bot_of_finiteType_fractionExtension q₂.1 q₂.2.2.over.symm]
  · have hpmax : p = maximalIdeal A := by
      have hpMax : p.IsMaximal :=
        (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance) p hp0 hp
      exact IsLocalRing.eq_maximalIdeal hpMax
    simpa [hpmax] using finite_primesOver_maximalIdeal_of_localDomain_fractionExtension

/-- Helper for Chap10 Lemma 10 124 1: an injective reindexing gives a sub-sum
comparison for weighted `ℕ∞` terms, and a positive omitted target term makes the
comparison strict. -/
private theorem sum_le_and_lt_of_injective_weightedTerms
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α → β) (he : Function.Injective e) (f : α → ℕ∞) (g : β → ℕ∞)
    (hfg : ∀ a, f a = g (e a)) :
    (∑ a : α, f a ≤ ∑ b : β, g b) ∧
      (∀ b : β, b ∉ Set.range e → 0 < g b → (∑ a : α, f a) ≠ ⊤ →
        ∑ a : α, f a < ∑ b : β, g b) := by
  classical
  -- First rewrite the source sum as the sum over the image of the injection.
  have himage :
      ∑ a : α, f a = ∑ b ∈ (Finset.univ.image e), g b := by
    calc
      ∑ a : α, f a = ∑ a : α, g (e a) := by
        exact Finset.sum_congr rfl fun a _ ↦ hfg a
      _ = ∑ b ∈ (Finset.univ.image e), g b := by
        rw [Finset.sum_image]
        exact fun a _ a' _ haa' ↦ he haa'
  constructor
  · -- The image is a subset of the full finite target set, so the reindexed sum is bounded above.
    rw [himage]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro b hb; exact Finset.mem_univ b)
      (by intro b _ _; exact zero_le (g b))
  · intro b hb hpos hfinite
    -- A positive term outside the image upgrades the subset comparison to a strict inequality.
    rw [himage]
    have hb_image : b ∉ Finset.univ.image e := by
      simpa [Finset.mem_image, Set.mem_range] using hb
    have himageFinite : (∑ c ∈ Finset.univ.image e, g c) ≠ ⊤ := by
      rwa [← himage]
    have hlt_insert :
        ∑ c ∈ Finset.univ.image e, g c <
          ∑ c ∈ insert b (Finset.univ.image e), g c := by
      rw [Finset.sum_insert hb_image]
      simpa [zero_add, add_comm] using
        (ENat.add_lt_add_of_lt_of_le himageFinite hpos le_rfl)
    have hle_insert_univ :
        ∑ c ∈ insert b (Finset.univ.image e), g c ≤ ∑ c : β, g c :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by intro c hc; exact Finset.mem_univ c)
        (by intro c _ _; exact zero_le (g c))
    exact hlt_insert.trans_le hle_insert_univ

/-- Helper for Chap10 Lemma 10 124 1: an omitted positive target summand makes the
injectively reindexed source sum strictly smaller than the full target sum. -/
private theorem sum_lt_of_omitted_positive_weightedTerm
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α → β) (he : Function.Injective e) (f : α → ℕ∞) (g : β → ℕ∞)
    (hfg : ∀ a, f a = g (e a)) {b : β} (hb : b ∉ Set.range e)
    (hpos : 0 < g b) (hfinite : (∑ a : α, f a) ≠ ⊤) :
    ∑ a : α, f a < ∑ b : β, g b := by
  -- Consume the strict branch of the finite image-sum comparison for the omitted summand.
  exact (sum_le_and_lt_of_injective_weightedTerms e he f g hfg).2 b hb hpos hfinite

/-- Helper for Chap10 Lemma 10 124 1: a nonzero element of the maximal ideal of a one-dimensional
Noetherian local domain has strictly positive local order. -/
private theorem localOrd_pos_of_mem_maximal
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] (x : R) (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0) :
    0 < Ring.ord R x := by
  -- Proof comment: membership in the maximal ideal shows `(x)` is proper, so the principal
  -- quotient is nontrivial and therefore has positive length.
  have hspan_ne_top : Ideal.span ({x} : Set R) ≠ ⊤ := by
    intro htop
    have hunit : IsUnit x := (Ideal.span_singleton_eq_top).mp htop
    exact (IsLocalRing.notMem_maximalIdeal.mpr hunit) hx
  let _ : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) := Ideal.Quotient.nontrivial_iff.2 hspan_ne_top
  have hlength_pos :
      0 < Module.length R (R ⧸ Ideal.span ({x} : Set R)) := by
    simpa using (Module.length_pos_iff).2 inferInstance
  -- Proof comment: `Ring.ord` is defined as the length of this principal quotient in the
  -- one-dimensional Noetherian local domain setting.
  simpa [Ring.ord] using hlength_pos

/-- Helper for Chap10 Lemma 10 124 1: a bijective away map `C_r → B_r` upgrades to a bijection on
the localizations at any prime of `B` avoiding `r`. -/
private theorem subalgebraLocalRingHomBijectiveOfAwayMapBijective
    {C : Subalgebra A B} {Q : Ideal B} [Q.IsPrime]
    (r : C) (hrQ : (r : B) ∉ Q)
    (hr : Function.Bijective (Localization.awayMap C.val.toRingHom r)) :
    let q : Ideal C := Ideal.comap C.val.toRingHom Q
    Function.Bijective (Localization.localRingHom q Q C.val.toRingHom rfl) := by
  let q : Ideal C := Ideal.comap C.val.toRingHom Q
  letI : q.IsPrime := Ideal.comap_isPrime C.val.toRingHom Q
  letI : Q.LiesOver q := by
    exact ⟨rfl⟩
  have hsat : C.saturation (Q.primeCompl ⊓ C.toSubmonoid) (by simp) = ⊤ := by
    -- Proof comment: surjectivity of `C_r → B_r` is exactly the denominator-clearing condition
    -- that forces the localization saturation to be all of `C`.
    rw [← top_le_iff]
    intro x hx
    obtain ⟨b, n, hb⟩ := (Localization.awayMap_surjective_iff).mp hr.2 x
    refine ⟨r.1 ^ n, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact Q.primeCompl.pow_mem (show r.1 ∈ Q.primeCompl from hrQ) n
      · exact C.pow_mem r.2 n
    · simpa [smul_eq_mul] using (show r.1 ^ n * x ∈ C from hb.symm ▸ b.2)
  -- Proof comment: the saturation-top criterion is the canonical bridge from a basic-open
  -- isomorphism to a bijection on the corresponding stalk.
  have hbij : Function.Bijective (Localization.localRingHom q Q C.val.toRingHom rfl) :=
    @Localization.localRingHom_bijective_of_saturated_inf_eq_top A _ B _ _ Q _ C hsat q _ _
  simpa [q] using hbij

/-- Helper for Chap10 Lemma 10 124 1: contracting a closed-fiber maximal ideal of `B` along a
finite intermediate subalgebra `C ⊆ B` gives the corresponding ideal of `C`. -/
private abbrev closedFiberContractionIdeal
    {C : Subalgebra A B} (m : ClosedFiberMaximalSpectrum A B) : Ideal C :=
  Ideal.comap C.val.toRingHom m.1.asIdeal

/-- Helper for Chap10 Lemma 10 124 1: the contracted ideal of a closed-fiber maximal ideal is
again maximal in any finite intermediate subalgebra. -/
private theorem closedFiberContractionIdeal_isMaximal
    {C : Subalgebra A B} [Module.Finite A C]
    (m : ClosedFiberMaximalSpectrum A B) :
    ((closedFiberContractionIdeal : ClosedFiberMaximalSpectrum A B → Ideal C) m).IsMaximal := by
  let q : Ideal C := closedFiberContractionIdeal m
  -- Proof comment: `A → C` is integral because `C` is finite over `A`, so a contraction whose
  -- further contraction to `A` is `maximalIdeal A` is itself maximal.
  letI : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  have hcomap_max : (Ideal.comap (algebraMap A C) q).IsMaximal := by
    have hover :
        maximalIdeal A = Ideal.comap (algebraMap A C) q := by
      simpa [q, closedFiberContractionIdeal, Ideal.comap_comap, Ideal.under_def] using m.2.over
    simpa [hover] using (maximalIdeal.isMaximal A)
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q hcomap_max

/-- Helper for Chap10 Lemma 10 124 1: the contracted ideal still lies over the closed point of
`Spec A`. -/
private theorem closedFiberContractionIdeal_liesOver
    {C : Subalgebra A B} (m : ClosedFiberMaximalSpectrum A B) :
    ((closedFiberContractionIdeal : ClosedFiberMaximalSpectrum A B → Ideal C) m).LiesOver
      (maximalIdeal A) := by
  let q : Ideal C := closedFiberContractionIdeal m
  -- Proof comment: contracting once more from `C` to `A` is the same as contracting directly from
  -- `B` to `A`.
  refine ⟨?_⟩
  simpa [q, closedFiberContractionIdeal, Ideal.under_def, Ideal.comap_comap] using m.2.over

/-- Helper for Chap10 Lemma 10 124 1: a finite intermediate subalgebra yields a contraction map
from the closed-fiber maximal spectrum of `B` to that of `C`. -/
private noncomputable def closedFiberContraction
    {C : Subalgebra A B} [Module.Finite A C] :
    ClosedFiberMaximalSpectrum A B → ClosedFiberMaximalSpectrum A C :=
  fun m ↦
    ⟨⟨closedFiberContractionIdeal m, closedFiberContractionIdeal_isMaximal m⟩,
      closedFiberContractionIdeal_liesOver m⟩

/-- Helper for Chap10 Lemma 10 124 1: `closedFiberContraction` has the expected contracted ideal as
its underlying maximal ideal. -/
private theorem closedFiberContraction_asIdeal
    {C : Subalgebra A B} [Module.Finite A C]
    (m : ClosedFiberMaximalSpectrum A B) :
    (((closedFiberContraction : ClosedFiberMaximalSpectrum A B → ClosedFiberMaximalSpectrum A C)
      m).1.asIdeal) =
      Ideal.comap C.val.toRingHom m.1.asIdeal := by
  rfl

/-- Helper for Chap10 Lemma 10 124 1: the closed-fiber contraction map is injective when
`Spec B → Spec C` is an open embedding. -/
private theorem closedFiberContraction_injective
    {C : Subalgebra A B} [Module.Finite A C]
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap C.val.toRingHom)) :
    Function.Injective
      (closedFiberContraction : ClosedFiberMaximalSpectrum A B → ClosedFiberMaximalSpectrum A C) := by
  intro m n hmn
  apply Subtype.ext
  apply MaximalSpectrum.toPrimeSpectrum_injective
  have hcomap :
      Ideal.comap C.val.toRingHom m.1.asIdeal =
        Ideal.comap C.val.toRingHom n.1.asIdeal := by
    simpa [closedFiberContraction_asIdeal] using congrArg
      (fun z : ClosedFiberMaximalSpectrum A C ↦ z.1.asIdeal) hmn
  have hprime :
      PrimeSpectrum.comap C.val.toRingHom (MaximalSpectrum.toPrimeSpectrum m.1) =
        PrimeSpectrum.comap C.val.toRingHom (MaximalSpectrum.toPrimeSpectrum n.1) := by
    exact PrimeSpectrum.ext_iff.mpr hcomap
  exact hopen.injective hprime

/-- Helper for Chap10 Lemma 10 124 1: a bijective away map on a finite intermediate subalgebra
upgrades to an isomorphism on the corresponding local rings. -/
private noncomputable def subalgebraLocalRingEquivOfAwayMapBijective
    {C : Subalgebra A B} {Q : Ideal B} [Q.IsPrime]
    (r : C) (hrQ : (r : B) ∉ Q)
    (haway : Function.Bijective (Localization.awayMap C.val.toRingHom r)) :
    Localization.AtPrime (Ideal.comap C.val.toRingHom Q) ≃+* Localization.AtPrime Q :=
  RingEquiv.ofBijective
    (Localization.localRingHom (Ideal.comap C.val.toRingHom Q) Q C.val.toRingHom rfl)
    (subalgebraLocalRingHomBijectiveOfAwayMapBijective r hrQ haway)

/-- Helper for Chap10 Lemma 10 124 1: the local-ring equivalence from an away-bijective
comparison has the expected forward map. -/
private theorem subalgebraLocalRingEquivOfAwayMapBijective_apply
    {C : Subalgebra A B} {Q : Ideal B} [Q.IsPrime]
    (r : C) (hrQ : (r : B) ∉ Q)
    (haway : Function.Bijective (Localization.awayMap C.val.toRingHom r))
    (x : Localization.AtPrime (Ideal.comap C.val.toRingHom Q)) :
    subalgebraLocalRingEquivOfAwayMapBijective r hrQ haway x =
      Localization.localRingHom (Ideal.comap C.val.toRingHom Q) Q C.val.toRingHom rfl x := by
  -- Proof comment: `RingEquiv.ofBijective` keeps the original local-ring homomorphism as its
  -- forward map.
  rfl

/-- Helper for Chap10 Lemma 10 124 1: around the contraction of a closed-fiber maximal ideal, the
open image of `Spec B → Spec C` contains a basic open neighborhood. -/
private theorem exists_basicOpen_subset_range_of_closedFiberContraction
    {C : Subalgebra A B} [Module.Finite A C]
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap C.val.toRingHom))
    (m : ClosedFiberMaximalSpectrum A B) :
    ∃ g : C,
      MaximalSpectrum.toPrimeSpectrum
          ((closedFiberContraction : ClosedFiberMaximalSpectrum A B →
            ClosedFiberMaximalSpectrum A C) m).1 ∈
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ∧
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap C.val.toRingHom) := by
  classical
  let qPoint : PrimeSpectrum C :=
    MaximalSpectrum.toPrimeSpectrum (closedFiberContraction m).1
  let U : Set (PrimeSpectrum C) := Set.range (PrimeSpectrum.comap C.val.toRingHom)
  have hUopen : IsOpen U := hopen.isOpen_range
  have hq_mem : qPoint ∈ U := by
    -- Proof comment: the contracted closed-fiber point is, by construction, the image of `m`.
    refine ⟨MaximalSpectrum.toPrimeSpectrum m.1, ?_⟩
    apply PrimeSpectrum.ext_iff.mpr
    simpa [qPoint] using (closedFiberContraction_asIdeal m).symm
  obtain ⟨V, hVbasis, hqV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hq_mem hUopen
  rcases hVbasis with ⟨g, rfl⟩
  exact ⟨g, hqV, hVU⟩

/-- Helper for Chap10 Lemma 10 124 1: the Zariski-main basic-open comparison yields a canonical
local-ring equivalence between `C` localized at the contracted closed-fiber point and `B`
localized at the original closed-fiber maximal ideal. -/
private noncomputable def closedFiberLocalRingEquivOfContraction
    {C : Subalgebra A B} [Module.Finite A C]
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap C.val.toRingHom))
    (haway : ∀ g : C,
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap C.val.toRingHom)) →
        Function.Bijective (Localization.awayMap C.val.toRingHom g))
    (m : ClosedFiberMaximalSpectrum A B) :
    Localization.AtPrime
        (((closedFiberContraction : ClosedFiberMaximalSpectrum A B →
          ClosedFiberMaximalSpectrum A C) m).1.asIdeal) ≃+*
      Localization.AtPrime m.1.asIdeal := by
  classical
  let hbasic := exists_basicOpen_subset_range_of_closedFiberContraction hopen m
  let g : C := Classical.choose hbasic
  have hgm :
      MaximalSpectrum.toPrimeSpectrum
          (closedFiberContraction m).1 ∈
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) :=
    (Classical.choose_spec hbasic).1
  have hgsub :
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap C.val.toRingHom) :=
    (Classical.choose_spec hbasic).2
  have hgQ : (g : B) ∉ m.1.asIdeal := by
    -- Proof comment: membership in the contracted ideal is exactly membership in `m`.
    intro hgQ
    have hgq : (g : C) ∉ (closedFiberContraction m).1.asIdeal := by
      simpa [PrimeSpectrum.mem_basicOpen] using hgm
    exact hgq <| by simpa [closedFiberContraction_asIdeal, Ideal.mem_comap] using hgQ
  -- Proof comment: once the basic open lies in the image, the away-map bijection upgrades to the
  -- required localization equivalence.
  simpa [closedFiberContraction_asIdeal] using
    (subalgebraLocalRingEquivOfAwayMapBijective g hgQ (haway g hgsub))

/-- Helper for Chap10 Lemma 10 124 1: the closed-fiber local-ring equivalence is the expected
localized inclusion on elements coming from `C`. -/
private theorem closedFiberLocalRingEquivOfContraction_apply
    {C : Subalgebra A B} [Module.Finite A C]
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap C.val.toRingHom))
    (haway : ∀ g : C,
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap C.val.toRingHom)) →
        Function.Bijective (Localization.awayMap C.val.toRingHom g))
    (m : ClosedFiberMaximalSpectrum A B)
    (z : Localization.AtPrime
      (((closedFiberContraction : ClosedFiberMaximalSpectrum A B →
        ClosedFiberMaximalSpectrum A C) m).1.asIdeal)) :
    closedFiberLocalRingEquivOfContraction hopen haway m z =
      Localization.localRingHom
          (((closedFiberContraction : ClosedFiberMaximalSpectrum A B →
            ClosedFiberMaximalSpectrum A C) m).1.asIdeal)
          m.1.asIdeal C.val.toRingHom
          (closedFiberContraction_asIdeal m).symm z := by
  classical
  obtain ⟨g, hgm, hgsub⟩ :=
    exists_basicOpen_subset_range_of_closedFiberContraction hopen m
  have hgQ : (g : B) ∉ m.1.asIdeal := by
    -- Proof comment: the chosen basic-open generator is outside the source maximal ideal because
    -- the contracted point lies in that basic open.
    intro hgQ
    have hgq : (g : C) ∉ (closedFiberContraction m).1.asIdeal := by
      simpa [PrimeSpectrum.mem_basicOpen] using hgm
    exact hgq <| by simpa [closedFiberContraction_asIdeal, Ideal.mem_comap] using hgQ
  -- Proof comment: this is the forward-map description of the away-bijective localization
  -- equivalence, rewritten through the contraction identity.
  simpa [closedFiberLocalRingEquivOfContraction, closedFiberContraction_asIdeal]
    using
      (subalgebraLocalRingEquivOfAwayMapBijective_apply g hgQ (haway g hgsub) z)

/-- Helper for Chap10 Lemma 10 124 1: the closed-fiber local-ring equivalence commutes with the
base `A`-algebra maps. -/
private theorem closedFiberLocalRingEquivOfContraction_commutes
    {C : Subalgebra A B} [Module.Finite A C]
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap C.val.toRingHom))
    (haway : ∀ g : C,
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap C.val.toRingHom)) →
        Function.Bijective (Localization.awayMap C.val.toRingHom g))
    (m : ClosedFiberMaximalSpectrum A B) (x : A) :
    closedFiberLocalRingEquivOfContraction hopen haway m
        (algebraMap A
          (Localization.AtPrime (closedFiberContraction m).1.asIdeal) x) =
      algebraMap A (Localization.AtPrime m.1.asIdeal) x := by
  let qC : Ideal C := (closedFiberContraction m).1.asIdeal
  have hqC_over_A : maximalIdeal A = Ideal.comap (algebraMap A C) qC := by
    -- Proof comment: the contracted closed-fiber point still lies over the closed point of
    -- `Spec A`, so the localization source prime is exactly `maximalIdeal A`.
    simpa [qC] using (closedFiberContractionIdeal_liesOver m).over
  let fC :
      Localization.AtPrime (maximalIdeal A) →+*
        Localization.AtPrime qC :=
    Localization.localRingHom (maximalIdeal A) qC (algebraMap A C) hqC_over_A
  let fB :
      Localization.AtPrime (maximalIdeal A) →+*
        Localization.AtPrime m.1.asIdeal :=
    Localization.localRingHom (maximalIdeal A) m.1.asIdeal (algebraMap A B) m.2.over
  have hcomp :
      fB =
        (Localization.localRingHom qC m.1.asIdeal C.val.toRingHom
          (by simpa [qC] using
            (closedFiberContraction_asIdeal m).symm)).comp fC := by
    -- Proof comment: the local map from `A_(m_A)` to `B_m` factors canonically through the
    -- contracted localization `C_(m ∩ C)`.
    simpa [fB, fC, qC] using
      (Localization.localRingHom_comp (maximalIdeal A) qC m.1.asIdeal
        (algebraMap A C) hqC_over_A C.val.toRingHom
        (by simpa [qC] using
          (closedFiberContraction_asIdeal m).symm))
  have hfC :
      fC (algebraMap A (Localization.AtPrime (maximalIdeal A)) x) =
        algebraMap A (Localization.AtPrime qC) x := by
    -- Proof comment: evaluating the first localization map on `x` is the standard
    -- `Localization.localRingHom_to_map` computation.
    simpa [fC, qC, IsScalarTower.algebraMap_eq A C (Localization.AtPrime qC)] using
      Localization.localRingHom_to_map (maximalIdeal A) qC (algebraMap A C) hqC_over_A x
  have hfB :
      fB (algebraMap A (Localization.AtPrime (maximalIdeal A)) x) =
        algebraMap A (Localization.AtPrime m.1.asIdeal) x := by
    -- Proof comment: the direct localization map to `B_m` computes on `x` in the same way.
    show Localization.localRingHom (maximalIdeal A) m.1.asIdeal (algebraMap A B) m.2.over
        (algebraMap A (Localization.AtPrime (maximalIdeal A)) x) =
      algebraMap A (Localization.AtPrime m.1.asIdeal) x
    simpa [IsScalarTower.algebraMap_eq A B (Localization.AtPrime m.1.asIdeal)] using
      Localization.localRingHom_to_map
        (maximalIdeal A) m.1.asIdeal (algebraMap A B) m.2.over x
  -- Proof comment: after rewriting the equivalence as the local-ring homomorphism on `C_(m ∩ C)`,
  -- the factorization above identifies both sides on the base element `x`.
  rw [closedFiberLocalRingEquivOfContraction_apply]
  calc
    Localization.localRingHom qC m.1.asIdeal C.val.toRingHom
        (by simpa [qC] using
          (closedFiberContraction_asIdeal m).symm)
        (algebraMap A (Localization.AtPrime qC) x)
        =
      Localization.localRingHom qC m.1.asIdeal C.val.toRingHom
        (by simpa [qC] using
          (closedFiberContraction_asIdeal m).symm)
        (fC (algebraMap A (Localization.AtPrime (maximalIdeal A)) x)) := by
          rw [hfC.symm]
    _ = fB (algebraMap A (Localization.AtPrime (maximalIdeal A)) x) := by
          exact congrArg
            (fun g : Localization.AtPrime (maximalIdeal A) →+*
              Localization.AtPrime m.1.asIdeal ↦
              g (algebraMap A (Localization.AtPrime (maximalIdeal A)) x))
            hcomp.symm
    _ = algebraMap A (Localization.AtPrime m.1.asIdeal) x := hfB

/-- Helper for Chap10 Lemma 10 124 1: a ring equivalence preserves the order of vanishing of
corresponding elements. -/
private theorem ringEquiv_ord_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (x : R) :
    Ring.ord R x = Ring.ord S (e x) := by
  let I : Ideal R := Ideal.span ({x} : Set R)
  let J : Ideal S := Ideal.span ({e x} : Set S)
  have hJ : J = I.map (e : R →+* S) := by
    -- Proof comment: a ring equivalence carries the principal ideal `(x)` to `(e x)`.
    simp [I, J, Ideal.map_span, Set.image_singleton]
  let qEquiv : R ⧸ I ≃+* S ⧸ J := Ideal.quotientEquiv I J e hJ
  let _ : Algebra (R ⧸ I) (S ⧸ J) := qEquiv.toRingHom.toAlgebra
  let qLinear : (R ⧸ I) ≃ₗ[R ⧸ I] (S ⧸ J) :=
    { toFun := qEquiv
      invFun := qEquiv.symm
      left_inv := qEquiv.left_inv
      right_inv := qEquiv.right_inv
      map_add' := qEquiv.map_add
      map_smul' := by
        intro a b
        -- Proof comment: the transported scalar action on `S ⧸ J` is multiplication through the
        -- quotient ring equivalence `qEquiv`.
        change qEquiv (a * b) = qEquiv a * qEquiv b
        exact qEquiv.map_mul a b }
  -- Route correction: instead of transporting `Ring.ord` through dependent quotient rewrites,
  -- compare the principal quotients via `Ideal.quotientEquiv` and use surjective base change on
  -- module length.
  calc
    Ring.ord R x = Module.length (R ⧸ I) (R ⧸ I) := by
      -- Proof comment: `R / (x)` has the same length over `R` and over the quotient ring because
      -- the quotient map `R → R / (x)` is surjective.
      rw [Ring.ord]
      let hmkI : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
      simpa [I] using Module.length_eq_of_surjective hmkI
    _ = Module.length (R ⧸ I) (S ⧸ J) := by
      -- Proof comment: the quotient equivalence identifies the two principal-ideal quotients as
      -- modules over the source quotient ring.
      simpa [qLinear] using (LinearEquiv.length_eq qLinear)
    _ = Module.length (S ⧸ J) (S ⧸ J) := by
      -- Proof comment: after transporting scalars along the quotient equivalence, the same
      -- surjective-base-change argument compares lengths over `R / (x)` and `S / (e x)`.
      simpa [qEquiv] using (Module.length_eq_of_surjective qEquiv.surjective)
    _ = Ring.ord S (e x) := by
      -- Proof comment: rewrite the target quotient length back to the canonical owner `Ring.ord`.
      rw [Ring.ord]
      let hmkJ : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
      simpa [J] using (Module.length_eq_of_surjective hmkJ).symm

/-- Helper for Chap10 Lemma 10 124 1: an element of `maximalIdeal A` remains in the maximal ideal
after mapping to the localization of a closed-fiber point. -/
private theorem localizedBaseImage_mem_maximal_of_closedFiber
    {C : Subalgebra A B} [Module.Finite A C]
    (q : ClosedFiberMaximalSpectrum A C) (x : A) (hx : x ∈ maximalIdeal A) :
    algebraMap C (Localization.AtPrime q.1.asIdeal) (algebraMap A C x) ∈
      maximalIdeal (Localization.AtPrime q.1.asIdeal) := by
  have hxC : algebraMap A C x ∈ q.1.asIdeal := by
    -- Proof comment: the defining closed-fiber witness identifies the contraction of `q` with the
    -- maximal ideal of the base, so `x` lands in the contracted ideal of `C`.
    simpa [Ideal.mem_comap, q.2.over] using hx
  -- Proof comment: in the canonical `C → C_q` spelling, maximal-ideal membership is exactly the
  -- localization owner lemma `to_map_mem_maximal_iff`.
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime q.1.asIdeal) q.1.asIdeal (algebraMap A C x)).2 hxC

/-- Helper for Chap10 Lemma 10 124 1: the local-ring equivalence on a closed-fiber contraction
induces the corresponding residue-field equivalence. -/
private noncomputable def closedFiberResidueFieldEquivOfContraction
    {C : Subalgebra A B} [Module.Finite A C]
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap C.val.toRingHom))
    (haway : ∀ g : C,
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap C.val.toRingHom)) →
        Function.Bijective (Localization.awayMap C.val.toRingHom g))
    (m : ClosedFiberMaximalSpectrum A B) :
    Ideal.ResidueField
        (((closedFiberContraction : ClosedFiberMaximalSpectrum A B →
          ClosedFiberMaximalSpectrum A C) m).1.asIdeal) ≃+*
      Ideal.ResidueField m.1.asIdeal :=
  IsLocalRing.ResidueField.mapEquiv (closedFiberLocalRingEquivOfContraction hopen haway m)

/-- Helper for Chap10 Lemma 10 124 1: the residue-field degree is unchanged by transporting a
closed-fiber point along the Zariski-main local-ring equivalence. -/
private theorem closedFiberResidueFieldEquivOfContraction_commutesBase
    {C : Subalgebra A B} [Module.Finite A C]
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap C.val.toRingHom))
    (haway : ∀ g : C,
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap C.val.toRingHom)) →
        Function.Bijective (Localization.awayMap C.val.toRingHom g))
    (m : ClosedFiberMaximalSpectrum A B) (z : κA) :
    closedFiberResidueFieldEquivOfContraction hopen haway m
        (algebraMap κA
          (Ideal.ResidueField
            (((closedFiberContraction : ClosedFiberMaximalSpectrum A B →
              ClosedFiberMaximalSpectrum A C) m).1.asIdeal)) z) =
      algebraMap κA (Ideal.ResidueField m.1.asIdeal) z := by
  let q : Ideal C := (closedFiberContraction m).1.asIdeal
  let hκsurj : Function.Surjective (algebraMap A κA) :=
    Ideal.algebraMap_residueField_surjective (maximalIdeal A)
  obtain ⟨a, rfl⟩ := hκsurj z
  have hqBase :
      algebraMap κA (Ideal.ResidueField q) (algebraMap A κA a) =
        algebraMap A (Ideal.ResidueField q) a := by
    change
      Ideal.ResidueField.map (maximalIdeal A) q (algebraMap A C)
          (closedFiberContractionIdeal_liesOver m).over
          ((algebraMap A κA) a) =
        algebraMap A (Ideal.ResidueField q) a
    rw [Ideal.ResidueField.map_algebraMap]
    rw [IsScalarTower.algebraMap_apply A C (Ideal.ResidueField q)]
  have hmBase :
      algebraMap κA (Ideal.ResidueField m.1.asIdeal) (algebraMap A κA a) =
        algebraMap A (Ideal.ResidueField m.1.asIdeal) a := by
    change
      Ideal.ResidueField.map (maximalIdeal A) m.1.asIdeal (algebraMap A B) m.2.over
          ((algebraMap A κA) a) =
        algebraMap A (Ideal.ResidueField m.1.asIdeal) a
    rw [Ideal.ResidueField.map_algebraMap]
    rw [IsScalarTower.algebraMap_apply A B (Ideal.ResidueField m.1.asIdeal)]
  -- Proof comment: after rewriting both residue-field algebra maps through `A`, the transport is
  -- exactly the image of `closedFiberLocalRingEquivOfContraction_commutes` under the residue map.
  rw [hqBase, hmBase]
  simpa [q, closedFiberResidueFieldEquivOfContraction, IsLocalRing.ResidueField.map_residue] using
    congrArg
      (IsLocalRing.residue (Localization.AtPrime m.1.asIdeal))
      (closedFiberLocalRingEquivOfContraction_commutes hopen haway m a)

/-- Helper for Chap10 Lemma 10 124 1: the residue-field degree is unchanged by transporting a
closed-fiber point along the Zariski-main local-ring equivalence. -/
private theorem closedFiberResidueDegree_eq_ofContraction
    {C : Subalgebra A B} [Module.Finite A C]
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap C.val.toRingHom))
    (haway : ∀ g : C,
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap C.val.toRingHom)) →
        Function.Bijective (Localization.awayMap C.val.toRingHom g))
    (m : ClosedFiberMaximalSpectrum A B) :
    Module.finrank κA (Ideal.ResidueField m.1.asIdeal) =
      Module.finrank κA
        (Ideal.ResidueField
          (((closedFiberContraction : ClosedFiberMaximalSpectrum A B →
            ClosedFiberMaximalSpectrum A C) m).1.asIdeal)) := by
  let qPoint : ClosedFiberMaximalSpectrum A C := closedFiberContraction m
  let q : Ideal C := qPoint.1.asIdeal
  let eκRing := closedFiberResidueFieldEquivOfContraction hopen haway m
  let eκ :
      Ideal.ResidueField q ≃ₐ[κA] Ideal.ResidueField m.1.asIdeal :=
    { toRingEquiv := eκRing
      commutes' := fun z ↦ closedFiberResidueFieldEquivOfContraction_commutesBase hopen haway m z }
  have hcompat :
      algebraMap κA (Ideal.ResidueField m.1.asIdeal) =
        RingHom.comp
          (closedFiberResidueFieldEquivOfContraction hopen haway m).toRingHom
          (algebraMap κA (Ideal.ResidueField q)) := by
    apply RingHom.ext
    intro z
    simpa [RingHom.comp_apply] using
      (closedFiberResidueFieldEquivOfContraction_commutesBase hopen haway m z).symm
  letI : Module.Finite κA (Ideal.ResidueField q) :=
    moduleFinite_residueField_of_moduleFinite A qPoint.1
  letI : Module.Finite κA (Ideal.ResidueField m.1.asIdeal) :=
    Module.Finite.equiv eκ.toLinearEquiv
  -- Proof comment: after upgrading the residue-field comparison to a `κA`-algebra equivalence and
  -- transporting finite generation, the residue degrees are equal by linear equivalence.
  simpa [q] using (LinearEquiv.finrank_eq eκ.toLinearEquiv).symm

/-- Helper for Chap10 Lemma 10 124 1: transporting a closed-fiber point along the Zariski-main
local-ring equivalence preserves the weighted local-order summand. -/
private theorem closedFiberWeightedTerm_eq_ofContraction
    {C : Subalgebra A B} [Module.Finite A C]
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap C.val.toRingHom))
    (haway : ∀ g : C,
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap C.val.toRingHom)) →
        Function.Bijective (Localization.awayMap C.val.toRingHom g))
    (m : ClosedFiberMaximalSpectrum A B) (x : A) :
    (Module.finrank κA (Ideal.ResidueField m.1.asIdeal) : ℕ∞) *
        Ring.ord (Localization.AtPrime m.1.asIdeal)
          (algebraMap A (Localization.AtPrime m.1.asIdeal) x) =
    (Module.finrank κA
          (Ideal.ResidueField
            (((closedFiberContraction : ClosedFiberMaximalSpectrum A B →
              ClosedFiberMaximalSpectrum A C) m).1.asIdeal)) : ℕ∞) *
        Ring.ord
          (Localization.AtPrime
            (((closedFiberContraction : ClosedFiberMaximalSpectrum A B →
              ClosedFiberMaximalSpectrum A C) m).1.asIdeal))
          (algebraMap A
            (Localization.AtPrime
              (((closedFiberContraction : ClosedFiberMaximalSpectrum A B →
                ClosedFiberMaximalSpectrum A C) m).1.asIdeal)) x) := by
  let q : Ideal C := (closedFiberContraction m).1.asIdeal
  let e :
      Localization.AtPrime q ≃+* Localization.AtPrime m.1.asIdeal :=
    closedFiberLocalRingEquivOfContraction hopen haway m
  have hcoeff :
      Module.finrank κA (Ideal.ResidueField m.1.asIdeal) =
        Module.finrank κA (Ideal.ResidueField q) :=
    closedFiberResidueDegree_eq_ofContraction hopen haway m
  have hord :
      Ring.ord (Localization.AtPrime m.1.asIdeal)
          (algebraMap A (Localization.AtPrime m.1.asIdeal) x) =
        Ring.ord (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) x) := by
    -- Proof comment: `ringEquiv_ord_eq` moves the local order across the equivalence, and the
    -- source element is identified by `closedFiberLocalRingEquivOfContraction_commutes`.
    simpa [q, e, closedFiberLocalRingEquivOfContraction_commutes
      hopen haway m x] using
      (ringEquiv_ord_eq e (algebraMap A (Localization.AtPrime q) x)).symm
  -- Proof comment: the residue-degree coefficient and the local order term transport separately,
  -- so the weighted product is unchanged.
  calc
    (Module.finrank κA (Ideal.ResidueField m.1.asIdeal) : ℕ∞) *
          Ring.ord (Localization.AtPrime m.1.asIdeal)
            (algebraMap A (Localization.AtPrime m.1.asIdeal) x)
      =
        (Module.finrank κA (Ideal.ResidueField q) : ℕ∞) *
          Ring.ord (Localization.AtPrime m.1.asIdeal)
            (algebraMap A (Localization.AtPrime m.1.asIdeal) x) := by
          rw [hcoeff]
    _ =
        (Module.finrank κA (Ideal.ResidueField q) : ℕ∞) *
          Ring.ord (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) x) := by
          rw [hord]

/-- Helper for Chap10 Lemma 10 124 1: every omitted maximal ideal of the finite intermediary
contributes a strictly positive weighted local-order term. -/
private theorem closedFiberMissingWeightedTerm_pos
    {C : Subalgebra A B} [Module.Finite A C]
    (q : ClosedFiberMaximalSpectrum A C) (x : A)
    (hx : x ∈ maximalIdeal A) (hx0 : x ≠ 0) :
    0 <
      (Module.finrank κA (Ideal.ResidueField q.1.asIdeal) : ℕ∞) *
        Ring.ord (Localization.AtPrime q.1.asIdeal)
          (algebraMap A (Localization.AtPrime q.1.asIdeal) x) := by
  letI : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  letI : Ring.KrullDimLE 1 (Localization.AtPrime q.1.asIdeal) :=
    krullDimLE_one_localizationAtPrime_of_moduleFinite A q.1
  letI : Module.Finite κA (Ideal.ResidueField q.1.asIdeal) :=
    moduleFinite_residueField_of_moduleFinite A q.1
  have hcoeff :
      0 < (Module.finrank κA (Ideal.ResidueField q.1.asIdeal) : ℕ∞) := by
    -- Proof comment: the residue field at a maximal ideal is a nontrivial finite-dimensional
    -- `κA`-vector space, so its finite rank is strictly positive.
    simpa using
      (show 0 < Module.finrank κA (Ideal.ResidueField q.1.asIdeal) from Module.finrank_pos)
  have hmem :
      algebraMap C (Localization.AtPrime q.1.asIdeal) (algebraMap A C x) ∈
        maximalIdeal (Localization.AtPrime q.1.asIdeal) := by
    exact localizedBaseImage_mem_maximal_of_closedFiber q x hx
  have hord :
      0 < Ring.ord (Localization.AtPrime q.1.asIdeal)
        (algebraMap C (Localization.AtPrime q.1.asIdeal) (algebraMap A C x)) := by
    have hxB0 : algebraMap A B x ≠ 0 := by
      intro hxB
      exact hx0 <|
        (algebraMap_injective_of_field_isFractionRing
          A B (FractionRing A) (FractionRing B)) <|
          by simpa using hxB
    have hxC0 : algebraMap A C x ≠ 0 := by
      intro hxC
      exact hxB0 <| by
        simpa using congrArg (fun z : C ↦ (z : B)) hxC
    have hinjLoc : Function.Injective (algebraMap C (Localization.AtPrime q.1.asIdeal)) :=
      IsLocalization.injective
        (Localization.AtPrime q.1.asIdeal) q.1.asIdeal.primeCompl_le_nonZeroDivisors
    have hy0 :
        algebraMap C (Localization.AtPrime q.1.asIdeal) (algebraMap A C x) ≠ 0 := by
      intro hy
      exact hxC0 <| hinjLoc <| hy.trans (map_zero _).symm
    -- Proof comment: once the image of `x` lands in the localized maximal ideal and stays
    -- nonzero, the local-order positivity lemma applies at the stalk `C_q`.
    exact localOrd_pos_of_mem_maximal
      (algebraMap C (Localization.AtPrime q.1.asIdeal) (algebraMap A C x)) hmem hy0
  have hy0 :
      algebraMap C (Localization.AtPrime q.1.asIdeal) (algebraMap A C x) ≠ 0 := by
    intro hy
    have hxB0 : algebraMap A B x ≠ 0 := by
      intro hxB
      exact hx0 <|
        (algebraMap_injective_of_field_isFractionRing
          A B (FractionRing A) (FractionRing B)) <|
          by simpa using hxB
    have hxC0 : algebraMap A C x ≠ 0 := by
      intro hxC
      exact hxB0 <| by
        simpa using congrArg (fun z : C ↦ (z : B)) hxC
    have hinjLoc : Function.Injective (algebraMap C (Localization.AtPrime q.1.asIdeal)) :=
      IsLocalization.injective
        (Localization.AtPrime q.1.asIdeal) q.1.asIdeal.primeCompl_le_nonZeroDivisors
    exact hxC0 <| hinjLoc <| hy.trans (map_zero _).symm
  have hordFinite :
      Ring.ord (Localization.AtPrime q.1.asIdeal)
        (algebraMap C (Localization.AtPrime q.1.asIdeal) (algebraMap A C x)) ≠ ⊤ :=
    ord_ne_top_of_ne_zero
      (algebraMap C (Localization.AtPrime q.1.asIdeal) (algebraMap A C x)) hy0
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hordFinite
  have hcoeffNat :
      0 < Module.finrank κA (Ideal.ResidueField q.1.asIdeal) :=
    Module.finrank_pos
  have hnpos : 0 < n := by
    have hnposENat : (0 : ℕ∞) < (n : ℕ∞) := by
      simpa [hn] using hord
    exact_mod_cast hnposENat
  have hposC :
      0 <
        (Module.finrank κA (Ideal.ResidueField q.1.asIdeal) : ℕ∞) *
          Ring.ord (Localization.AtPrime q.1.asIdeal)
            (algebraMap C (Localization.AtPrime q.1.asIdeal) (algebraMap A C x)) := by
    rw [← hn]
    exact_mod_cast Nat.mul_pos hcoeffNat hnpos
  -- Proof comment: both the residue-degree coefficient and the localized order term are positive,
  -- and after rewriting the finite local order as a natural number the product is a positive
  -- natural number viewed in `ℕ∞`.
  simpa [IsScalarTower.algebraMap_eq A C (Localization.AtPrime q.1.asIdeal)] using hposC

/-- Helper for Chap10 Lemma 10 124 1: the finite intermediate subalgebra cannot have larger
fraction-field degree than the ambient ring. -/
private noncomputable def fractionRingSubalgebraToAmbientAlgHom
    {C : Subalgebra A B} [Module.Finite A C]
    [Algebra (FractionRing A) (FractionRing C)]
    [IsScalarTower A (FractionRing A) (FractionRing C)] :
    FractionRing C →ₐ[FractionRing A] FractionRing B := by
  let g : C →ₐ[A] FractionRing B :=
    ((IsScalarTower.toAlgHom A B (FractionRing B)).comp C.val)
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    exact IsFractionRing.injective B (FractionRing B) <| by simpa [g] using hxy
  let φA : FractionRing C →ₐ[A] FractionRing B :=
    IsFractionRing.liftAlgHom hg
  have hcomp :
      RingHom.comp φA.toRingHom (algebraMap (FractionRing A) (FractionRing C)) =
        algebraMap (FractionRing A) (FractionRing B) := by
    have hInj :
        Function.Injective
          (fun f : FractionRing A →+* FractionRing B ↦
            f.comp (algebraMap A (FractionRing A))) := by
      simpa using
        (IsFractionRing.injective_comp_algebraMap :
          Function.Injective
            (fun f : FractionRing A →+* FractionRing B ↦
              f.comp (algebraMap A (FractionRing A))))
    apply hInj
    ext a
    -- Proof comment: both maps from `Frac(A)` to `Frac(B)` are lifts of the same base map
    -- `A → B → Frac(B)`, so it suffices to compare them on `a : A`.
    simp only [RingHom.comp_apply]
    have hA :
        algebraMap (FractionRing A) (FractionRing C) (algebraMap A (FractionRing A) a) =
          algebraMap C (FractionRing C) (algebraMap A C a) := by
      calc
        algebraMap (FractionRing A) (FractionRing C) (algebraMap A (FractionRing A) a) =
            algebraMap A (FractionRing C) a := by
              exact (IsScalarTower.algebraMap_apply A (FractionRing A) (FractionRing C) a).symm
        _ = algebraMap C (FractionRing C) (algebraMap A C a) := by
              exact (IsScalarTower.algebraMap_apply A C (FractionRing C) a).symm
    have hB :
        algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) a) =
          algebraMap A (FractionRing B) a := by
      exact (IsScalarTower.algebraMap_apply A (FractionRing A) (FractionRing B) a).symm
    rw [hA, hB]
    simpa [φA, g, AlgHom.comp_apply, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply A B (FractionRing B)] using
      (IsFractionRing.lift_algebraMap hg (algebraMap A C a))
  exact
    { toRingHom := φA.toRingHom
      commutes' := by
        intro z
        simpa [RingHom.comp_apply] using
          congrArg (fun f : FractionRing A →+* FractionRing B ↦ f z) hcomp }

/-- Helper for Chap10 Lemma 10 124 1: a finite intermediate subalgebra has finite-dimensional
fraction field over `Frac(A)` because its fraction field injects into `Frac(B)`. -/
private theorem fractionRingFiniteDimensional_of_subalgebra
    {C : Subalgebra A B} (hCfinite : Module.Finite A C)
    [Algebra (FractionRing A) (FractionRing C)]
    [IsScalarTower A (FractionRing A) (FractionRing C)] :
    FiniteDimensional (FractionRing A) (FractionRing C) := by
  letI : Module.Finite A C := hCfinite
  let φ :
      FractionRing C →ₐ[FractionRing A] FractionRing B :=
    fractionRingSubalgebraToAmbientAlgHom
  -- Proof comment: the canonical `Frac(C) → Frac(B)` map is injective and `Frac(B)` is already
  -- finite-dimensional over `Frac(A)`, so `Frac(C)` inherits finite dimensionality.
  exact FiniteDimensional.of_injective φ.toLinearMap φ.injective

/-- Helper for Chap10 Lemma 10 124 1: the finite intermediate subalgebra maps canonically into
the ambient fraction field over `Frac(A)`. -/
private theorem fractionRingFinrank_le_of_subalgebra
    {C : Subalgebra A B} [Module.Finite A C]
    [Algebra (FractionRing A) (FractionRing C)]
    [IsScalarTower A (FractionRing A) (FractionRing C)]
    [FiniteDimensional (FractionRing A) (FractionRing C)] :
    Module.finrank (FractionRing A) (FractionRing C) ≤
      Module.finrank (FractionRing A) (FractionRing B) := by
  let φ :
      FractionRing C →ₐ[FractionRing A] FractionRing B :=
    fractionRingSubalgebraToAmbientAlgHom
  let φlin : FractionRing C →ₗ[FractionRing A] FractionRing B := φ.toLinearMap
  have hφlin : Function.Injective φlin := φ.injective
  -- Proof comment: the named comparison map is `Frac(A)`-linear and injective, so finite
  -- dimensionality over `Frac(A)` gives the desired degree monotonicity.
  simpa [φ, φlin] using
    (LinearMap.finrank_le_finrank_of_injective hφlin)

/-- Helper for Chap10 Lemma 10 124 1: for a finite intermediary `C`, the full closed-fiber
weighted sum already has the module-finite normal form from Lemma `10.121.8`. -/
private theorem closedFiberWeightedSum_eq_moduleFiniteNormalForm
    {C : Subalgebra A B} (hCfinite : Module.Finite A C)
    [Algebra (FractionRing A) (FractionRing C)]
    [IsScalarTower A (FractionRing A) (FractionRing C)]
    [FiniteDimensional (FractionRing A) (FractionRing C)]
    (x : A) (hx : x ∈ maximalIdeal A) (hx0 : x ≠ 0) :
    (let _ : Finite (MaximalSpectrum C) := finite_maximalSpectrum_of_moduleFinite A
    let _ : Finite (ClosedFiberMaximalSpectrum A C) := by infer_instance
    let _ : Fintype (ClosedFiberMaximalSpectrum A C) :=
      Fintype.ofFinite (ClosedFiberMaximalSpectrum A C)
    ∑ q : ClosedFiberMaximalSpectrum A C,
      (Module.finrank κA (Ideal.ResidueField q.1.asIdeal) : ℕ∞) *
        Ring.ord (Localization.AtPrime q.1.asIdeal)
          (algebraMap A (Localization.AtPrime q.1.asIdeal) x)) =
      (Module.finrank (FractionRing A) (FractionRing C) : ℕ∞) * Ring.ord A x := by
  letI : Module.Finite A C := hCfinite
  -- Proof comment: once the `Frac(A) → Frac(C)` tower is installed explicitly, the finite-owner
  -- equality from Lemma `10.121.8` applies verbatim to the intermediary `C`.
  simpa using
    (sum_residueFieldDegree_mul_local_ord_eq_fractionFieldDegree_mul_ord_of_moduleFinite
      hCfinite x hx hx0)

/-- Helper for Chap10 Lemma 10 124 1: if a closed-fiber point of the finite intermediary `C`
is omitted from the image of `closedFiberContraction`, then the reindexed `B`-sum is strictly
smaller than the full `C`-sum. -/
private theorem closedFiberImageSum_lt_of_omittedPoint
    {C : Subalgebra A B} [Module.Finite A C]
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap C.val.toRingHom))
    (haway : ∀ g : C,
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap C.val.toRingHom)) →
        Function.Bijective (Localization.awayMap C.val.toRingHom g))
    (x : A) (hx : x ∈ maximalIdeal A) (hx0 : x ≠ 0)
    (q : ClosedFiberMaximalSpectrum A C)
    (hq : q ∉ Set.range
      (closedFiberContraction : ClosedFiberMaximalSpectrum A B → ClosedFiberMaximalSpectrum A C))
    (hfiniteBsum :
      (let _ : Finite (MaximalSpectrum B) :=
        finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension A
      let _ : Finite (ClosedFiberMaximalSpectrum A B) := by infer_instance
      let _ : Fintype (ClosedFiberMaximalSpectrum A B) :=
        Fintype.ofFinite (ClosedFiberMaximalSpectrum A B)
      ∑ m : ClosedFiberMaximalSpectrum A B,
        (Module.finrank κA (Ideal.ResidueField m.1.asIdeal) : ℕ∞) *
          Ring.ord (Localization.AtPrime m.1.asIdeal)
            (algebraMap A (Localization.AtPrime m.1.asIdeal) x)) ≠ ⊤) :
    (let _ : Finite (MaximalSpectrum B) :=
      finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension A
    let _ : Finite (ClosedFiberMaximalSpectrum A B) := by infer_instance
    let _ : Fintype (ClosedFiberMaximalSpectrum A B) :=
      Fintype.ofFinite (ClosedFiberMaximalSpectrum A B)
    ∑ m : ClosedFiberMaximalSpectrum A B,
      (Module.finrank κA (Ideal.ResidueField m.1.asIdeal) : ℕ∞) *
        Ring.ord (Localization.AtPrime m.1.asIdeal)
          (algebraMap A (Localization.AtPrime m.1.asIdeal) x)) <
      (let _ : Finite (MaximalSpectrum C) := finite_maximalSpectrum_of_moduleFinite A
      let _ : Finite (ClosedFiberMaximalSpectrum A C) := by infer_instance
      let _ : Fintype (ClosedFiberMaximalSpectrum A C) :=
        Fintype.ofFinite (ClosedFiberMaximalSpectrum A C)
      ∑ q' : ClosedFiberMaximalSpectrum A C,
        (Module.finrank κA (Ideal.ResidueField q'.1.asIdeal) : ℕ∞) *
          Ring.ord (Localization.AtPrime q'.1.asIdeal)
            (algebraMap A (Localization.AtPrime q'.1.asIdeal) x)) := by
  classical
  letI : Finite (MaximalSpectrum B) :=
    finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension A
  letI : Finite (ClosedFiberMaximalSpectrum A B) := by infer_instance
  letI : Fintype (ClosedFiberMaximalSpectrum A B) :=
    Fintype.ofFinite (ClosedFiberMaximalSpectrum A B)
  letI : Finite (MaximalSpectrum C) := finite_maximalSpectrum_of_moduleFinite A
  letI : Finite (ClosedFiberMaximalSpectrum A C) := by infer_instance
  letI : Fintype (ClosedFiberMaximalSpectrum A C) :=
    Fintype.ofFinite (ClosedFiberMaximalSpectrum A C)
  -- Proof comment: compare the `B`-sum with the `C`-sum through the injective contraction map,
  -- then use the omitted positive summand at `q` to make the comparison strict.
  let contraction : ClosedFiberMaximalSpectrum A B → ClosedFiberMaximalSpectrum A C :=
    closedFiberContraction
  simpa using
    sum_lt_of_omitted_positive_weightedTerm
      contraction
      (closedFiberContraction_injective hopen)
      (fun m : ClosedFiberMaximalSpectrum A B ↦
        (Module.finrank κA (Ideal.ResidueField m.1.asIdeal) : ℕ∞) *
          Ring.ord (Localization.AtPrime m.1.asIdeal)
            (algebraMap A (Localization.AtPrime m.1.asIdeal) x))
      (fun q' : ClosedFiberMaximalSpectrum A C ↦
        (Module.finrank κA (Ideal.ResidueField q'.1.asIdeal) : ℕ∞) *
          Ring.ord (Localization.AtPrime q'.1.asIdeal)
            (algebraMap A (Localization.AtPrime q'.1.asIdeal) x))
      (fun m ↦ closedFiberWeightedTerm_eq_ofContraction hopen haway m x)
      hq
      (closedFiberMissingWeightedTerm_pos q x hx hx0)
      hfiniteBsum

/-- Helper for Chap10 Lemma 10 124 1: the fraction-field degree of a finite intermediary `C`
gives a smaller `ℕ∞` degree term than the ambient ring `B`. -/
private theorem intermediateDegreeMulOrd_le_ambientDegreeMulOrd
    {C : Subalgebra A B} [Module.Finite A C]
    [Algebra (FractionRing A) (FractionRing C)]
    [IsScalarTower A (FractionRing A) (FractionRing C)]
    [FiniteDimensional (FractionRing A) (FractionRing C)]
    (x : A) (hx0 : x ≠ 0) :
    (Module.finrank (FractionRing A) (FractionRing C) : ℕ∞) * Ring.ord A x ≤
      (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x := by
  have hord : Ring.ord A x ≠ ⊤ := ord_ne_top_of_ne_zero x hx0
  -- Proof comment: once `ord_A(x)` is rewritten as a casted natural number, the comparison is
  -- exactly the natural-number monotonicity of `finrank` along `Frac(C) ↪ Frac(B)`.
  rw [← ENat.coe_toNat hord, ← Nat.cast_mul, ← Nat.cast_mul]
  exact_mod_cast Nat.mul_le_mul_right (Ring.ord A x).toNat
    fractionRingFinrank_le_of_subalgebra

/-- Helper for Chap10 Lemma 10 124 1: if the global weighted-order sum for `B` already attains
the ambient fraction-field degree bound, then the contraction map from the closed fiber of `B`
onto that of a finite Zariski-main intermediary `C` is surjective. -/
private theorem closedFiberContraction_surjective_of_globalEquality
    {C : Subalgebra A B} [Module.Finite A C]
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap C.val.toRingHom))
    (haway : ∀ g : C,
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap C.val.toRingHom)) →
        Function.Bijective (Localization.awayMap C.val.toRingHom g))
    (x : A) (hx : x ∈ maximalIdeal A) (hx0 : x ≠ 0)
    (heq :
      (let _ : Finite (MaximalSpectrum B) :=
        finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension A
      let _ : Finite (ClosedFiberMaximalSpectrum A B) := by infer_instance
      let _ : Fintype (ClosedFiberMaximalSpectrum A B) :=
        Fintype.ofFinite (ClosedFiberMaximalSpectrum A B)
      ∑ m : ClosedFiberMaximalSpectrum A B,
        (Module.finrank κA (Ideal.ResidueField m.1.asIdeal) : ℕ∞) *
          Ring.ord (Localization.AtPrime m.1.asIdeal)
            (algebraMap A (Localization.AtPrime m.1.asIdeal) x)) =
        (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x) :
    Function.Surjective
      (closedFiberContraction : ClosedFiberMaximalSpectrum A B → ClosedFiberMaximalSpectrum A C) := by
  classical
  letI : Finite (MaximalSpectrum B) :=
    finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension A
  letI : Finite (ClosedFiberMaximalSpectrum A B) := by infer_instance
  letI : Fintype (ClosedFiberMaximalSpectrum A B) :=
    Fintype.ofFinite (ClosedFiberMaximalSpectrum A B)
  letI : Finite (MaximalSpectrum C) := finite_maximalSpectrum_of_moduleFinite A
  letI : Finite (ClosedFiberMaximalSpectrum A C) := by infer_instance
  letI : Fintype (ClosedFiberMaximalSpectrum A C) :=
    Fintype.ofFinite (ClosedFiberMaximalSpectrum A C)
  letI : FaithfulSMul A (FractionRing C) := faithfulSMul_fractionRing_of_subalgebra (C := C)
  letI : Algebra (FractionRing A) (FractionRing C) := FractionRing.liftAlgebra A (FractionRing C)
  letI : IsScalarTower A (FractionRing A) (FractionRing C) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing C)
  letI : FiniteDimensional (FractionRing A) (FractionRing C) :=
    fractionRingFiniteDimensional_of_subalgebra (C := C) inferInstance
  let Bsum : ℕ∞ :=
    ∑ m : ClosedFiberMaximalSpectrum A B,
      (Module.finrank κA (Ideal.ResidueField m.1.asIdeal) : ℕ∞) *
        Ring.ord (Localization.AtPrime m.1.asIdeal)
          (algebraMap A (Localization.AtPrime m.1.asIdeal) x)
  let Csum : ℕ∞ :=
    ∑ q : ClosedFiberMaximalSpectrum A C,
      (Module.finrank κA (Ideal.ResidueField q.1.asIdeal) : ℕ∞) *
        Ring.ord (Localization.AtPrime q.1.asIdeal)
          (algebraMap A (Localization.AtPrime q.1.asIdeal) x)
  let Bdeg : ℕ∞ := (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x
  let Cdeg : ℕ∞ := (Module.finrank (FractionRing A) (FractionRing C) : ℕ∞) * Ring.ord A x
  have hEqNamed : Bsum = Bdeg := by
    change
      (∑ m : ClosedFiberMaximalSpectrum A B,
        (Module.finrank κA (Ideal.ResidueField m.1.asIdeal) : ℕ∞) *
          Ring.ord (Localization.AtPrime m.1.asIdeal)
            (algebraMap A (Localization.AtPrime m.1.asIdeal) x)) =
        (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x
    exact heq
  have hBsumFinite : Bsum ≠ ⊤ := by
    rw [hEqNamed]
    dsimp [Bdeg]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ord_ne_top_of_ne_zero x hx0)
    rw [← hn]
    simpa [Nat.cast_mul] using
      (ENat.coe_ne_top (Module.finrank (FractionRing A) (FractionRing B) * n))
  have hCsumEq : Csum = Cdeg := by
    -- Proof comment: the finite intermediary `C` satisfies the exact normal form from
    -- Lemma `10.121.8`.
    change
      (∑ q : ClosedFiberMaximalSpectrum A C,
        (Module.finrank κA (Ideal.ResidueField q.1.asIdeal) : ℕ∞) *
          Ring.ord (Localization.AtPrime q.1.asIdeal)
            (algebraMap A (Localization.AtPrime q.1.asIdeal) x)) =
        (Module.finrank (FractionRing A) (FractionRing C) : ℕ∞) * Ring.ord A x
    exact closedFiberWeightedSum_eq_moduleFiniteNormalForm (C := C) inferInstance x hx hx0
  have hCdegLe : Cdeg ≤ Bdeg := by
    -- Proof comment: `Frac(C)` injects into `Frac(B)`, so the degree term for `C` is smaller.
    change
      (Module.finrank (FractionRing A) (FractionRing C) : ℕ∞) * Ring.ord A x ≤
        (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x
    exact intermediateDegreeMulOrd_le_ambientDegreeMulOrd (C := C) x hx0
  -- Route correction: keep the omitted-point strictness and the `ℕ∞` normalization as separate
  -- named facts, so the equality-case contradiction stays linear and elaboration-stable.
  by_contra hsurj
  rw [Function.Surjective] at hsurj
  push Not at hsurj
  obtain ⟨q, hq⟩ := hsurj
  have hqRange :
      q ∉ Set.range
        (closedFiberContraction : ClosedFiberMaximalSpectrum A B → ClosedFiberMaximalSpectrum A C) := by
    intro hq'
    rcases hq' with ⟨m, rfl⟩
    exact hq m rfl
  have hlt : Bsum < Csum := by
    -- Proof comment: an omitted closed-fiber point of `C` contributes a strictly positive term.
    change
      (∑ m : ClosedFiberMaximalSpectrum A B,
        (Module.finrank κA (Ideal.ResidueField m.1.asIdeal) : ℕ∞) *
          Ring.ord (Localization.AtPrime m.1.asIdeal)
            (algebraMap A (Localization.AtPrime m.1.asIdeal) x)) <
        ∑ q : ClosedFiberMaximalSpectrum A C,
          (Module.finrank κA (Ideal.ResidueField q.1.asIdeal) : ℕ∞) *
            Ring.ord (Localization.AtPrime q.1.asIdeal)
              (algebraMap A (Localization.AtPrime q.1.asIdeal) x)
    exact closedFiberImageSum_lt_of_omittedPoint (C := C) hopen haway x hx hx0 q hqRange hBsumFinite
  have hnotLt : ¬ Bsum < Csum := by
    -- Proof comment: equality for `B` and the ambient degree bound force the `C`-sum to be no
    -- larger than `Bsum`, contradicting the omitted-point strictness.
    rw [hEqNamed, hCsumEq]
    exact not_lt_of_ge hCdegLe
  exact hnotLt hlt

/-- Helper for Chap10 Lemma 10 124 1: along a closed-fiber contraction point, every `b : B`
admits a denominator from `C` outside the contracted maximal ideal whose product with `b` already
lies in `C`. -/
private theorem exists_notMem_mul_mem_of_closedFiberContractionPoint
    {C : Subalgebra A B} [Module.Finite A C]
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap C.val.toRingHom))
    (haway : ∀ g : C,
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap C.val.toRingHom)) →
        Function.Bijective (Localization.awayMap C.val.toRingHom g))
    (m : ClosedFiberMaximalSpectrum A B) (b : B) :
    ∃ s : C,
      s ∉ (closedFiberContraction m).1.asIdeal ∧
      ((s : C) : B) * b ∈ C := by
  let q : ClosedFiberMaximalSpectrum A C := closedFiberContraction m
  let e :
      Localization.AtPrime q.1.asIdeal ≃+* Localization.AtPrime m.1.asIdeal :=
    closedFiberLocalRingEquivOfContraction hopen haway m
  let z : Localization.AtPrime q.1.asIdeal :=
    e.symm (algebraMap B (Localization.AtPrime m.1.asIdeal) b)
  obtain ⟨c, s, hz⟩ := IsLocalization.exists_mk'_eq q.1.asIdeal.primeCompl z
  refine ⟨s.1, s.2, ?_⟩
  have hz' :
      e (IsLocalization.mk' (Localization.AtPrime q.1.asIdeal) c s) =
        algebraMap B (Localization.AtPrime m.1.asIdeal) b := by
    simpa [z, e] using congrArg e hz
  rw [closedFiberLocalRingEquivOfContraction_apply] at hz'
  rw [Localization.localRingHom_mk'] at hz'
  have hcross :
      algebraMap B (Localization.AtPrime m.1.asIdeal) (((c : C) : B) : B) =
        algebraMap B (Localization.AtPrime m.1.asIdeal) b *
          algebraMap B (Localization.AtPrime m.1.asIdeal) ((s : C) : B) := by
    rw [IsLocalization.mk'_eq_iff_eq_mul] at hz'
    simpa using hz'
  have hdesc :
      algebraMap B (Localization.AtPrime m.1.asIdeal) (((s : C) : B) * b) =
        algebraMap B (Localization.AtPrime m.1.asIdeal) (c : B) := by
    calc
      algebraMap B (Localization.AtPrime m.1.asIdeal) (((s : C) : B) * b) =
          algebraMap B (Localization.AtPrime m.1.asIdeal) ((s : C) : B) *
            algebraMap B (Localization.AtPrime m.1.asIdeal) b := by
              rw [map_mul]
      _ =
          algebraMap B (Localization.AtPrime m.1.asIdeal) b *
            algebraMap B (Localization.AtPrime m.1.asIdeal) ((s : C) : B) := by
              rw [mul_comm]
      _ = algebraMap B (Localization.AtPrime m.1.asIdeal) (c : B) := hcross.symm
  have hinj :
      Function.Injective (algebraMap B (Localization.AtPrime m.1.asIdeal)) :=
    IsLocalization.injective
      (Localization.AtPrime m.1.asIdeal) m.1.asIdeal.primeCompl_le_nonZeroDivisors
  have hmul :
      (((s : C) : B) * b) = (c : B) := hinj hdesc
  -- Proof comment: after clearing the localization denominator and descending through injectivity,
  -- the product is literally the numerator `c`, hence lies in the subalgebra `C`.
  exact hmul ▸ c.2

/-- Helper for Chap10 Lemma 10 124 1: if the contraction map on the closed fiber is surjective,
then the finite intermediary subalgebra `C` already equals `B`. -/
private theorem subalgebra_eq_top_of_closedFiberContraction_surjective
    {C : Subalgebra A B} [Module.Finite A C]
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap C.val.toRingHom))
    (haway : ∀ g : C,
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap C.val.toRingHom)) →
        Function.Bijective (Localization.awayMap C.val.toRingHom g))
    (hsurj : Function.Surjective
      (closedFiberContraction : ClosedFiberMaximalSpectrum A B → ClosedFiberMaximalSpectrum A C)) :
    C = ⊤ := by
  classical
  apply Algebra.eq_top_iff.2
  intro b
  have hzero :
      ((0 : C) : B) * b ∈ C := by
    simpa using (C.zero_mem : (0 : B) ∈ C)
  have hadd :
      ∀ c d : C, ((c : B) * b) ∈ C → ((d : B) * b) ∈ C →
        (((c + d : C) : C) : B) * b ∈ C := by
    intro c d hc hd
    simpa [add_mul] using C.add_mem hc hd
  have hsmul :
      ∀ a c : C, ((c : B) * b) ∈ C → (((a * c : C) : C) : B) * b ∈ C := by
    intro a c hc
    simpa [mul_assoc] using C.mul_mem a.2 hc
  let I : Ideal C :=
    { carrier := { c : C | ((c : C) : B) * b ∈ C }
      zero_mem' := hzero
      add_mem' := fun ha hb ↦ hadd _ _ ha hb
      smul_mem' := fun a _ hc ↦ hsmul a _ hc }
  have hItop : I = ⊤ := by
    by_contra hI
    obtain ⟨M, hMmax, hIleM⟩ := Ideal.exists_le_maximal I hI
    let mC : MaximalSpectrum C := ⟨M, hMmax⟩
    let q : ClosedFiberMaximalSpectrum A C := ⟨mC, maximalIdeal_liesOver_of_moduleFinite A mC⟩
    obtain ⟨m, hm⟩ := hsurj q
    obtain ⟨s, hsnot, hsmem⟩ :=
      exists_notMem_mul_mem_of_closedFiberContractionPoint hopen haway m b
    have hsI : s ∈ I := hsmem
    have hsM : s ∈ M := hIleM hsI
    exact hsnot <| by simpa [q, mC] using hm ▸ hsM
  have hone : (1 : C) ∈ I := by
    simpa [hItop] using (show (1 : C) ∈ (⊤ : Ideal C) by exact Ideal.mem_top)
  -- Proof comment: membership of `1` in the conductor ideal says exactly that `1 * b = b`
  -- already lies in `C`, so every element of `B` belongs to `C`.
  have hbmem : (((1 : C) : B) * b) ∈ C := hone
  simpa using hbmem

/- Domain-style sampling:
- primary domain: one-dimensional Noetherian local domains, local orders of vanishing, and the
  residue-field-degree weighted sum over maximal localizations of a finite-type algebra with finite
  fraction-field extension;
- sampled owner declarations:
  `finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension`,
  `Ring.ordFrac`,
  `Ring.ordFrac_eq_ord`,
  `ordFrac_norm_eq_sum_residueFieldDegree_mul_local_ordFrac`,
  `Module.Finite`;
- best owner abstraction: `Ring.ordFrac` is the canonical valuation owner, and
  `ordFrac_norm_eq_sum_residueFieldDegree_mul_local_ordFrac` is the chapter owner for the weighted
  maximal-spectrum sum, while
  `finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension` is the owner for the
  semilocality conclusion; this file should expose only the source-facing ring-level
  reformulations in terms of `Ring.ord`, not a parallel public owner for that sum;
- source/core/bridge triage:
  `source-facing`: the semilocality conclusion for `B`, together with the textbook inequality and
    equality criterion for the weighted sum of local orders of an element `x : A`;
  `core/canonical`: `Ring.ordFrac`, `Module.finrank`, and the chapter theorem
    `ordFrac_norm_eq_sum_residueFieldDegree_mul_local_ordFrac`, together with the semilocality
    owner `finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension`;
  `bridge/view`: `Ring.ordFrac_eq_ord` translates the fraction-field owner to the ring-level local
    orders that appear in the source statement;
- primitive data: the algebra tower and the chosen element `x : A`;
- derived API: finiteness of `MaximalSpectrum B`, the induced residue-field extensions, and the
  canonical weighted closed-fiber sum.
-/

/- Lemma 10.124.1 first asserts that `B` is semilocal. This is exactly the chapter owner theorem
`finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension`. -/
recall finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension

-- Proof sketch: let `B'` be the integral closure of `A` in `B`, choose the finite intermediate
-- `A`-subalgebra `C ⊂ B'` supplied by Lemma `10.123.14`, and apply Lemma `10.121.8` to `C`. The
-- localizations of `C` at the primes lying under the closed-fiber maximal ideals of `B` agree with the
-- corresponding localizations of `B`, while the extra maximal ideals of `C` contribute a
-- nonnegative remainder term, giving the inequality. The source fixes a nonzero
-- `x ∈ maximalIdeal A`, and the public statement keeps those hypotheses explicit.
/-- The weighted sum of local orders of `x` over the maximal ideals of `B` lying over the closed
point of `Spec A` is bounded above by the fraction-field degree times its order on `A`. -/
theorem sum_residueFieldDegree_mul_local_ord_le_fractionFieldDegree_mul_ord
    (x : A) (hx : x ∈ maximalIdeal A) (hx0 : x ≠ 0) :
    (let _ : Finite (MaximalSpectrum B) :=
      finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension A
    let _ : Finite (ClosedFiberMaximalSpectrum A B) := by
      infer_instance
    let _ : Fintype (ClosedFiberMaximalSpectrum A B) :=
      Fintype.ofFinite (ClosedFiberMaximalSpectrum A B)
    ∑ m : ClosedFiberMaximalSpectrum A B,
      (Module.finrank κA (Ideal.ResidueField m.1.asIdeal) : ℕ∞) *
        Ring.ord (Localization.AtPrime m.1.asIdeal)
          (algebraMap A (Localization.AtPrime m.1.asIdeal) x)) ≤
      (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x := by
  classical
  letI : Algebra.QuasiFinite A B := quasiFinite_of_localDomain_finiteFractionExtension
  obtain ⟨C, _, hCfinite, hopen, haway⟩ :=
    exists_finite_subalgebra_of_integralClosure_with_zariskiMain_properties (R := A) (S := B)
  letI : Module.Finite A C := hCfinite
  letI : Finite (MaximalSpectrum B) :=
    finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension A
  letI : Finite (ClosedFiberMaximalSpectrum A B) := by infer_instance
  letI : Fintype (ClosedFiberMaximalSpectrum A B) :=
    Fintype.ofFinite (ClosedFiberMaximalSpectrum A B)
  letI : Finite (MaximalSpectrum C) := finite_maximalSpectrum_of_moduleFinite A
  letI : Finite (ClosedFiberMaximalSpectrum A C) := by infer_instance
  letI : Fintype (ClosedFiberMaximalSpectrum A C) :=
    Fintype.ofFinite (ClosedFiberMaximalSpectrum A C)
  letI : FaithfulSMul A (FractionRing C) := faithfulSMul_fractionRing_of_subalgebra (C := C)
  letI : Algebra (FractionRing A) (FractionRing C) := FractionRing.liftAlgebra A (FractionRing C)
  letI : IsScalarTower A (FractionRing A) (FractionRing C) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing C)
  letI : FiniteDimensional (FractionRing A) (FractionRing C) :=
    fractionRingFiniteDimensional_of_subalgebra (C := C) hCfinite
  let Bsum : ℕ∞ :=
    ∑ m : ClosedFiberMaximalSpectrum A B,
      (Module.finrank κA (Ideal.ResidueField m.1.asIdeal) : ℕ∞) *
        Ring.ord (Localization.AtPrime m.1.asIdeal)
          (algebraMap A (Localization.AtPrime m.1.asIdeal) x)
  let Csum : ℕ∞ :=
    ∑ q : ClosedFiberMaximalSpectrum A C,
      (Module.finrank κA (Ideal.ResidueField q.1.asIdeal) : ℕ∞) *
        Ring.ord (Localization.AtPrime q.1.asIdeal)
          (algebraMap A (Localization.AtPrime q.1.asIdeal) x)
  let f : ClosedFiberMaximalSpectrum A B → ℕ∞ := fun m ↦
    (Module.finrank κA (Ideal.ResidueField m.1.asIdeal) : ℕ∞) *
      Ring.ord (Localization.AtPrime m.1.asIdeal)
        (algebraMap A (Localization.AtPrime m.1.asIdeal) x)
  let g : ClosedFiberMaximalSpectrum A C → ℕ∞ := fun q ↦
    (Module.finrank κA (Ideal.ResidueField q.1.asIdeal) : ℕ∞) *
      Ring.ord (Localization.AtPrime q.1.asIdeal)
        (algebraMap A (Localization.AtPrime q.1.asIdeal) x)
  have hfg : ∀ m, f m = g (closedFiberContraction m) := by
    intro m
    dsimp [f, g]
    exact closedFiberWeightedTerm_eq_ofContraction (C := C) hopen haway m x
  have hcompare : Bsum ≤ Csum := by
    -- Proof comment: reindex the `B`-sum through the injective contraction map into the full
    -- closed fiber of the finite intermediary `C`.
    change
      (∑ m : ClosedFiberMaximalSpectrum A B, f m) ≤
        ∑ q : ClosedFiberMaximalSpectrum A C, g q
    exact
      (sum_le_and_lt_of_injective_weightedTerms
        (closedFiberContraction : ClosedFiberMaximalSpectrum A B → ClosedFiberMaximalSpectrum A C)
        (closedFiberContraction_injective (C := C) hopen)
        f
        g
        hfg).1
  have hCsumEq :
      Csum = (Module.finrank (FractionRing A) (FractionRing C) : ℕ∞) * Ring.ord A x := by
    -- Proof comment: for the finite intermediary `C`, the full sum is exactly the module-finite
    -- normal form.
    change
      (∑ q : ClosedFiberMaximalSpectrum A C,
        (Module.finrank κA (Ideal.ResidueField q.1.asIdeal) : ℕ∞) *
          Ring.ord (Localization.AtPrime q.1.asIdeal)
            (algebraMap A (Localization.AtPrime q.1.asIdeal) x)) =
        (Module.finrank (FractionRing A) (FractionRing C) : ℕ∞) * Ring.ord A x
    exact closedFiberWeightedSum_eq_moduleFiniteNormalForm (C := C) hCfinite x hx hx0
  have hdegLe :
      (Module.finrank (FractionRing A) (FractionRing C) : ℕ∞) * Ring.ord A x ≤
        (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x := by
    -- Proof comment: the fraction-field degree of `C` cannot exceed that of `B`.
    exact intermediateDegreeMulOrd_le_ambientDegreeMulOrd (C := C) x hx0
  calc
    Bsum ≤ Csum := hcompare
    _ = (Module.finrank (FractionRing A) (FractionRing C) : ℕ∞) * Ring.ord A x := hCsumEq
    _ ≤ (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x := hdegLe

-- Proof sketch: the inequality above comes from the finite intermediate subalgebra `C`. Equality
-- holds exactly when there are no extra maximal ideals of `C` beyond those coming from maximal
-- ideals of `B` in the closed fiber over `maximalIdeal A`; then `C → B` induces a bijection on
-- those maximal ideals and is an isomorphism after
-- localizing at each maximal ideal, forcing `B = C`, hence `B` is finite over `A`. Conversely, if
-- `A → B` is finite, the equality is exactly Lemma `10.121.8` applied to `B`. The source-facing
-- hypotheses are the primitive conditions `x ∈ maximalIdeal A` and `x ≠ 0`, rather than the
-- derived inequalities `0 < Ring.ord A x` and `Ring.ord A x < ⊤`.
/-- Chap10 Lemma 10 124 1: for a finite-type extension of domains `A ⊂ B` with `A` a one-dimensional
Noetherian local domain and finite fraction-field extension, once the semilocality conclusion for
`B` is recalled above, equality between the global order term `[Frac(B) : Frac(A)] ord_A(x)` and
the weighted sum of local orders over the maximal ideals of `B` lying over the closed point of
`Spec A` holds exactly when `A → B` is finite, for `x ∈ maximalIdeal A` nonzero. -/
@[stacks 02MM]
theorem sum_residueFieldDegree_mul_local_ord_eq_fractionFieldDegree_mul_ord_iff_moduleFinite
    (x : A) (hx : x ∈ maximalIdeal A) (hx0 : x ≠ 0) :
    (let _ : Finite (MaximalSpectrum B) :=
      finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension A
    let _ : Finite (ClosedFiberMaximalSpectrum A B) := by
      infer_instance
    let _ : Fintype (ClosedFiberMaximalSpectrum A B) :=
      Fintype.ofFinite (ClosedFiberMaximalSpectrum A B)
    ∑ m : ClosedFiberMaximalSpectrum A B,
      (Module.finrank κA (Ideal.ResidueField m.1.asIdeal) : ℕ∞) *
        Ring.ord (Localization.AtPrime m.1.asIdeal)
          (algebraMap A (Localization.AtPrime m.1.asIdeal) x)) =
      (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x ↔
      Module.Finite A B := by
  classical
  constructor
  · intro heq
    letI : Algebra.QuasiFinite A B := quasiFinite_of_localDomain_finiteFractionExtension
    obtain ⟨C, _, hCfinite, hopen, haway⟩ :=
      exists_finite_subalgebra_of_integralClosure_with_zariskiMain_properties (R := A) (S := B)
    letI : Module.Finite A C := hCfinite
    have hsurj :
        Function.Surjective
          (closedFiberContraction :
            ClosedFiberMaximalSpectrum A B → ClosedFiberMaximalSpectrum A C) :=
      closedFiberContraction_surjective_of_globalEquality (C := C) hopen haway x hx hx0 heq
    have htop : C = ⊤ :=
      subalgebra_eq_top_of_closedFiberContraction_surjective (C := C) hopen haway hsurj
    let e : C ≃ₐ[A] B := (Subalgebra.equivOfEq C ⊤ htop).trans Subalgebra.topEquiv
    -- Proof comment: once the finite intermediary fills all of `B`, module-finiteness transports
    -- across the resulting algebra equivalence.
    exact Module.Finite.equiv e.toLinearEquiv
  · intro hfinite
    -- Proof comment: the reverse implication is exactly the already-proved module-finite case.
    simpa using
      (sum_residueFieldDegree_mul_local_ord_eq_fractionFieldDegree_mul_ord_of_moduleFinite
        hfinite x hx hx0)

end
