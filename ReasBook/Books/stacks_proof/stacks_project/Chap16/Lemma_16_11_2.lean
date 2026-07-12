import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Definition_10_137_10
import StacksProject_2024.Chap10.Definition_10_166_2
import StacksProject_2024.Chap10.Lemma_10_97_7
import StacksProject_2024.Chap15.Proposition_15_35_1
import StacksProject_2024.Chap15.Lemma_15_116_12
import StacksProject_2024.Chap16.Lemma_16_11_1

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open scoped TensorProduct

universe u v w

namespace Algebra

section

variable {k : Type u} [Field k]
variable {Λ : Type v} [CommRing Λ] [Algebra k Λ]

/- Domain-style sampling for Lemma 16.11.2.

Primary domain: localized prime quotients by maximal-ideal powers and their factorization through
local Artinian rings in the approximation step for geometrically regular `k`-algebras.

Sampled owner declarations in the surrounding project/mathlib style:
* `Localization.AtPrime` and `Localization.localRingHom` for the canonical localized source/target
  rings and the induced local map;
* `Localization.AtPrime.map_eq_maximalIdeal` and
  `pow_maximalIdeal_le_comap_pow_maximalIdeal` for the canonical maximal-ideal owner on those
  localizations and the induced quotient map API;
* `AlgHom.SmoothAtPrime` and object-prefix flatness owners `f.Flat` for the source-map
  smoothness and the map-level flatness conditions;
* `geometricallyRegularLocalRing_tfae_of_charP` and
  `localizedPolynomialSubextensionMap_flat_and_regular_closedFiber_of_geometricallyRegularLocalRing`
  for the local geometric-regularity criteria reused later in the chapter, both of which keep
  Noetherianity explicit on the local target ring;
* `Algebra.exists_artinianLocalSubalgebraApproximation` from `Lemma_16_11_1.lean`, which exposes
  the approximation-family properties directly on a family `S : ι → Subalgebra k Λ`.

Best owner abstraction: the source-facing theorem should expose the primitive polynomial map data
and the later factorization data directly, namely the flat localized source map together with the
maps
`k[y]_(φ⁻¹(𝔮)) / 𝔪(k[y]_(φ⁻¹(𝔮)))^n → D → Λ_𝔮 / 𝔪(Λ_𝔮)^n` together with the canonical localized
source data and their flatness, smoothness, and factorization properties. The source-smoothness
condition is naturally a property of the induced `AlgHom` attached to the chosen first map, so the
canonical owners are `(localMap).Flat`, that induced map's `SmoothAtPrime` predicate, and
`DToTarget.Flat`, rather than fully expanded `Algebra.SmoothAtPrime` / `Module.Flat` clauses.
Introducing a separate public wrapper predicate would only repackage theorem output data that the
surrounding chapter style keeps explicit.

Layering:
* `source-facing`: existence of primitive factorization data whose image contains the chosen finite
  subset `E`;
* `core/canonical`: the canonical prime `Ideal.comap φ.toRingHom 𝔮`, the localized quotient rings,
  the local map `Localization.localRingHom (Ideal.comap φ.toRingHom 𝔮) 𝔮 φ.toRingHom rfl`, and
  the induced quotient map built from `Ideal.quotientMap`;
* `bridge/view`: the containment condition `E ⊆ range DToTarget`, which is a property of a chosen
  factorization rather than primitive owner data.
-/

local notation:max "k[y]_" 𝔭 => Localization.AtPrime 𝔭
local notation:max "Λ_" 𝔮 => Localization.AtPrime 𝔮

variable {m : ℕ} {φ : MvPolynomial (Fin m) k →ₐ[k] Λ}
variable {𝔮 : Ideal Λ} [𝔮.IsPrime] {n : ℕ}

local notation "pφ" => Ideal.comap φ.toRingHom 𝔮
local notation:max "Source" => k[y]_ pφ
local notation:max "SourceQuot" => Source ⧸ (maximalIdeal Source) ^ n
local notation:max "Target" => (Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n
local notation:max "localMap" => Localization.localRingHom pφ 𝔮 φ.toRingHom rfl
local notation:max "targetMap" =>
  Ideal.quotientMap
    ((maximalIdeal (Λ_ 𝔮)) ^ n)
    localMap
    (pow_maximalIdeal_le_comap_pow_maximalIdeal localMap n)

/-- Helper for Lemma 16.11.2: a nonempty directed family of subalgebras whose supremum is `⊤`
contains every finite subset of the target quotient in one stage. -/
private lemma exists_stage_subalgebra_contains_finset
    {ι : Type*} [Nonempty ι]
    (S : ι → Subalgebra k Target) (hdir : Directed (· ≤ ·) S)
    (hSup : iSup S = (⊤ : Subalgebra k Target))
    (s : Finset Target) :
    ∃ i, (↑s : Set Target) ⊆ S i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨Classical.choice ‹Nonempty ι›, ?_⟩
      simp
  | @insert a s ha hs =>
      rcases hs with ⟨i, hi⟩
      -- The new element `a` belongs to some stage because the directed supremum is `⊤`.
      have ha_mem : a ∈ iSup S := by
        simpa [hSup] using (show a ∈ (⊤ : Subalgebra k Target) from trivial)
      have ha_stage : ∃ j, a ∈ S j := by
        change a ∈ ((iSup S : Subalgebra k Target) : Set Target) at ha_mem
        rw [Subalgebra.coe_iSup_of_directed hdir] at ha_mem
        simpa [Set.mem_iUnion] using ha_mem
      rcases ha_stage with ⟨j, hj⟩
      rcases hdir i j with ⟨m, him, hjm⟩
      refine ⟨m, ?_⟩
      intro x hx
      simp only [Finset.mem_insert, SetLike.mem_coe] at hx ⊢
      rcases hx with rfl | hx
      · exact hjm hj
      · exact him (hi hx)

/-- Helper for Lemma 16.11.2: once the canonical quotient map lands in a chosen subalgebra, it
factors through that subalgebra by codomain restriction. -/
private lemma targetMap_factors_through_subalgebra
    {D : Subalgebra k Target}
    (hD : Set.range targetMap ⊆ D) :
    ∃ sourceToD : SourceQuot →+* D, D.subtype.comp sourceToD = targetMap := by
  let sourceToD : SourceQuot →+* D :=
    RingHom.codRestrict targetMap D (fun x ↦ hD ⟨x, rfl⟩)
  refine ⟨sourceToD, ?_⟩
  -- Restricting the codomain does not change the underlying map to `Target`.
  ext x
  rfl

/-- Helper for Lemma 16.11.2: quotienting `Λ_𝔮` by a positive power of its maximal ideal remains
nontrivial. This is the local-ring input needed before invoking the quotient `IsLocalRing`
construction. -/
private theorem targetQuotient_nontrivial (hn : 1 ≤ n) : Nontrivial Target := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact Ideal.Quotient.nontrivial_iff.2 <| by
    simpa [Nat.add_comm] using
      (quotient_pow_maximalIdeal_ne_top (R := Λ_ 𝔮) r)

/-- Helper for Lemma 16.11.2: the target quotient by a positive maximal-ideal power is a local
ring. -/
private theorem targetQuotient_isLocalRing (hn : 1 ≤ n) : IsLocalRing Target := by
  let _ : Nontrivial Target :=
    targetQuotient_nontrivial hn
  exact
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk ((maximalIdeal (Λ_ 𝔮)) ^ n))
      Ideal.Quotient.mk_surjective

/-- Helper for Lemma 16.11.2: quotienting by an ideal kills that ideal under the quotient map. -/
private lemma quotient_map_ideal_eq_bot
    {R : Type*} [CommRing R] (I : Ideal R) :
    Ideal.map (Ideal.Quotient.mk I) I = (⊥ : Ideal (R ⧸ I)) := by
  -- Proof comment: the quotient map annihilates exactly the ideal we quotient by.
  exact (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk I)).2 (by simpa [Ideal.mk_ker])

/-- Helper for Lemma 16.11.2: the target quotient by a positive maximal-ideal power is Artinian. -/
private theorem targetQuotient_isArtinianRing [IsNoetherianRing Λ] (hn : 1 ≤ n) :
    IsArtinianRing Target := by
  let _ : IsLocalRing Target := targetQuotient_isLocalRing hn
  let _ : IsNoetherianRing (Localization.AtPrime 𝔮) :=
    IsLocalization.isNoetherianRing 𝔮.primeCompl (Localization.AtPrime 𝔮) inferInstance
  let _ : IsNoetherianRing Target := inferInstance
  let π : Localization.AtPrime 𝔮 →+* Target :=
    Ideal.Quotient.mk ((maximalIdeal (Localization.AtPrime 𝔮)) ^ n)
  -- Proof comment: the quotient maximal ideal is nilpotent because we quotient by its `n`th power.
  refine (isArtinianRing_iff_isNilpotent_maximalIdeal (R := Target)).mpr ?_
  refine ⟨n, ?_⟩
  have hmax :
      maximalIdeal Target = Ideal.map π (maximalIdeal (Λ_ 𝔮)) := by
    symm
    exact IsLocalRing.map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective
  calc
    maximalIdeal Target ^ n = Ideal.map π (maximalIdeal (Λ_ 𝔮)) ^ n := by
      rw [hmax]
    _ = Ideal.map π (maximalIdeal (Λ_ 𝔮) ^ n) := by
      rw [Ideal.map_pow]
    _ = ⊥ := by
      exact (Ideal.map_eq_bot_iff_le_ker π).2 (by simpa [π, Ideal.mk_ker])

/-- Helper for Lemma 16.11.2: Proposition `15.35.1` supplies the regular-local and injective
`H₁(L_{κ(A)/k}) → H₁(L_{κ(A)/A})` package for any geometrically regular local `k`-algebra in
characteristic `p > 0`. -/
private theorem geometricallyRegularLocalRing_h1Cotangent_map_injective_of_charP
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A]
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsGeometricallyRegular k A] :
    IsRegularLocalRing A ∧
      Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A)) := by
  letI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : Algebra (ZMod p) A := ZMod.algebra A p
  letI : IsScalarTower (ZMod p) k A := by infer_instance
  let T : List Prop :=
    [ IsGeometricallyRegular k A
    , ∀ (K : IntermediateField k (AlgebraicClosure k)) [FiniteDimensional k K],
        K ≤ onePthRootExtension k p → IsRegularRing (K ⊗[k] A)
    , IsRegularLocalRing A ∧
        Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A))
    , IsRegularLocalRing A ∧
        Function.Injective (KaehlerDifferential.residueFieldComparison (ZMod p) k A)
    ]
  have hTfae : List.TFAE T := by
    -- Proof comment: package Proposition `15.35.1` in the same list spelling used later in the
    -- chapter so the `(1) → (3)` implication can be reused directly here.
    simpa [T] using
      (geometricallyRegularLocalRing_tfae_of_charP (k := k) (A := A) (p := p))
  -- Proof comment: this is exactly the regular-local and injectivity clause needed for the
  -- localized prime ring `Λ_𝔮` in the source proof.
  simpa [T] using (hTfae.out 0 2).mp (show IsGeometricallyRegular k A from inferInstance)

/-- Helper for Lemma 16.11.2: the cotangent module of a finitely generated ideal is finite over
the corresponding quotient ring. This is the tiny Chapter 15 bridge needed for the residue-field
cotangent-space estimate, kept local here to avoid importing an unavailable `.olean`. -/
private theorem idealCotangentFinite_of_fg
    {R : Type*} [CommRing R] {I : Ideal R} (hI : I.FG) :
    Module.Finite (R ⧸ I) I.Cotangent := by
  letI : Module.Finite R I := Module.Finite.of_fg hI
  have hfiniteCotangent : Module.Finite R I.Cotangent := by
    -- Proof comment: `I / I²` is a quotient of the finitely generated ideal `I`.
    exact Module.Finite.of_surjective (Ideal.toCotangent I) (Ideal.toCotangent_surjective I)
  letI : Module.Finite R I.Cotangent := hfiniteCotangent
  letI : IsScalarTower R (R ⧸ I) I.Cotangent :=
    Module.IsTorsionBySet.isScalarTower (Ideal.isTorsionBySet_cotangent I)
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) I.Cotangent

/-- Helper for Lemma 16.11.2: for a Noetherian geometrically regular local `k`-algebra in
characteristic `p > 0`, the residue-field cotangent homology over `k` is finite-dimensional. -/
private theorem finiteDimensionalH1Cotangent_residueField_of_geometricallyRegularLocalRing
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A]
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsGeometricallyRegular k A] :
    FiniteDimensional (ResidueField A) (Algebra.H1Cotangent k (ResidueField A)) := by
  let K0 := ResidueField A
  have hsurj : Function.Surjective (algebraMap A K0) := by
    -- Proof comment: the algebra map to the residue field is the residue morphism.
    simpa [ResidueField.algebraMap_eq] using
      (residue_surjective : Function.Surjective (IsLocalRing.residue A))
  have hfg : (maximalIdeal A).FG := Ideal.fg_of_isNoetherianRing (maximalIdeal A)
  let _ : Module.Finite K0 (maximalIdeal A).Cotangent :=
    idealCotangentFinite_of_fg (R := A) (I := maximalIdeal A) hfg
  let _ : FiniteDimensional K0 (maximalIdeal A).Cotangent :=
    FiniteDimensional.of_finite K0 (maximalIdeal A).Cotangent
  let cotangentEquiv :
      (RingHom.ker (algebraMap A K0)).Cotangent ≃ₗ[K0] (maximalIdeal A).Cotangent :=
    Ideal.Cotangent.equivOfEq
      (RingHom.ker (algebraMap A K0))
      (maximalIdeal A)
      (by
        simpa [ResidueField.algebraMap_eq] using
          (ker_residue : RingHom.ker (IsLocalRing.residue A) = maximalIdeal A))
  let residueFieldH1ToCotangent :
      Algebra.H1Cotangent k K0 →ₗ[K0] (maximalIdeal A).Cotangent :=
    cotangentEquiv.toLinearMap.comp
      (((surjective_algebra_h1Cotangent_equiv_cotangent
          (A := A) (B := K0) hsurj).toLinearMap).comp
        (H1Cotangent.map k A K0 K0))
  have hInjective :
      Function.Injective residueFieldH1ToCotangent := by
    intro x y hxy
    -- Proof comment: the comparison from Proposition `15.35.1` is injective, and the two
    -- cotangent identifications are linear equivalences.
    apply (geometricallyRegularLocalRing_h1Cotangent_map_injective_of_charP
      (k := k) (A := A) (p := p)).2
    apply (surjective_algebra_h1Cotangent_equiv_cotangent
      (A := A) (B := K0) hsurj).injective
    apply cotangentEquiv.injective
    simpa [residueFieldH1ToCotangent, LinearMap.comp_apply] using hxy
  -- Proof comment: an injective linear map into a finite-dimensional residue-field cotangent
  -- space forces `H₁(L_{κ(A)/k})` itself to be finite-dimensional.
  exact FiniteDimensional.of_injective residueFieldH1ToCotangent hInjective

/-- Helper for Chap16 Lemma 16 11 2: quotienting `Λ_𝔮` by a positive power of its maximal ideal
does not change the finite-dimensionality of the residue-field cotangent homology over `k`. -/
private theorem finiteDimensionalH1Cotangent_targetResidueField
    {p : ℕ} [Fact p.Prime] [CharP k p] [IsGeometricallyRegular k Λ] [IsNoetherianRing Λ]
    (𝔮 : Ideal Λ) [𝔮.IsPrime] (n : ℕ) (hn : 1 ≤ n) :
    FiniteDimensional
      (ResidueField ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n))
      (Algebra.H1Cotangent k (ResidueField ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n))) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  let Kq := ResidueField (Λ_ 𝔮)
  let Kt := ResidueField ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ (r + 1))
  have hfdResidueH1 :
      FiniteDimensional Kq (Algebra.H1Cotangent k Kq) :=
    finiteDimensionalH1Cotangent_residueField_of_geometricallyRegularLocalRing
      (k := k) (A := Λ_ 𝔮) (p := p)
  let eRing : Kt ≃+* Kq :=
    residueField_quotient_pow_maximalIdeal_equiv (R := Λ_ 𝔮) r
  let eAlg : Kt ≃ₐ[k] Kq :=
    AlgEquiv.ofRingEquiv eRing fun x ↦ by
      -- Proof comment: the quotient residue-field equivalence respects the original `k`-algebra
      -- structure because it identifies residue classes of scalar images.
      simpa [Kt, ResidueField.algebraMap_eq] using
        residueField_quotient_pow_maximalIdeal_equiv_apply_residue
          (R := Λ_ 𝔮) r ((algebraMap k (Λ_ 𝔮)) x)
  have hrank :
      Module.rank Kt (Algebra.H1Cotangent k Kt) =
        Module.rank Kq (Algebra.H1Cotangent k Kq) := by
    -- Proof comment: `H₁(L_{-/k})` is functorial under algebra equivalences, so its rank is
    -- unchanged when we replace `Kq` by the quotient residue field `Kt`.
    refine
      rank_eq_of_equiv_equiv eRing
        (Algebra.H1Cotangent.mapEquiv eAlg).toAddEquiv
        eRing.bijective ?_
    intro x y
    simpa [eAlg, Kq, Kt] using
      (LinearMap.CompatibleSMul.map_smul
        (Algebra.H1Cotangent.map k k Kt Kq) x y)
  have hrank_nat :
      Module.rank Kt (Algebra.H1Cotangent k Kt) =
        (Module.finrank Kq (Algebra.H1Cotangent k Kq) : Cardinal) := by
    rw [hrank, ← Module.finrank_eq_rank]
  let _ : Module.Finite Kt (Algebra.H1Cotangent k Kt) :=
    Module.finite_of_rank_eq_nat hrank_nat
  exact FiniteDimensional.of_finite Kt (Algebra.H1Cotangent k Kt)

end

section

variable {k : Type u} [Field k]
variable {Λ : Type v} [CommRing Λ] [Algebra k Λ]

local notation:max "Λ_" 𝔮 => Localization.AtPrime 𝔮

/-- Helper for Lemma 16.11.2: the localized polynomial source ring attached to `φ` and `𝔮`. -/
private abbrev approximationSource
    {m : ℕ} (φ : MvPolynomial (Fin m) k →ₐ[k] Λ) (𝔮 : Ideal Λ) [𝔮.IsPrime] :=
  Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)

/-- Helper for Lemma 16.11.2: the quotient of the localized polynomial source by the `n`th power
of its maximal ideal. -/
private abbrev approximationSourceQuot
    {m : ℕ} (φ : MvPolynomial (Fin m) k →ₐ[k] Λ) (𝔮 : Ideal Λ) [𝔮.IsPrime] (n : ℕ) :=
  approximationSource (φ := φ) 𝔮 ⧸ (maximalIdeal (approximationSource (φ := φ) 𝔮)) ^ n

/-- Helper for Lemma 16.11.2: the canonical localized map from the polynomial source to `Λ_𝔮`. -/
private abbrev approximationLocalMap
    {m : ℕ} (φ : MvPolynomial (Fin m) k →ₐ[k] Λ) (𝔮 : Ideal Λ) [𝔮.IsPrime] :
    approximationSource (φ := φ) 𝔮 →+* Λ_ 𝔮 :=
  Localization.localRingHom (Ideal.comap φ.toRingHom 𝔮) 𝔮 φ.toRingHom rfl

/-- Helper for Lemma 16.11.2: the quotient map induced by the localized polynomial source map on
the `n`th maximal-ideal power quotients. -/
private abbrev approximationTargetMap
    {m : ℕ} (φ : MvPolynomial (Fin m) k →ₐ[k] Λ) (𝔮 : Ideal Λ) [𝔮.IsPrime] (n : ℕ) :
    approximationSourceQuot (φ := φ) 𝔮 n →+*
      ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n) :=
  let localMap := approximationLocalMap (φ := φ) 𝔮
  Ideal.quotientMap
    ((maximalIdeal (Λ_ 𝔮)) ^ n)
    localMap
    (pow_maximalIdeal_le_comap_pow_maximalIdeal localMap n)

/-- Helper for Chap16 Lemma 16 11 2: after moving to the Artinian target quotient, Lemma
`16.11.1` supplies a local Artinian essentially-finite-type stage containing the chosen finite
subset `E`. -/
private theorem existsApproximationStageContainingE
    {p : ℕ} [Fact p.Prime] [CharP k p] [IsGeometricallyRegular k Λ] [IsNoetherianRing Λ]
    (𝔮 : Ideal Λ) [𝔮.IsPrime] (n : ℕ) (hn : 1 ≤ n)
    (E : Finset ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n)) :
    ∃ D : Subalgebra k ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n),
      (↑E : Set ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n)) ⊆ D ∧
        IsArtinianRing D ∧
        IsLocalRing D ∧
        D.subtype.Flat ∧
        Ideal.map D.subtype (maximalIdeal D) =
          maximalIdeal ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n) ∧
        Algebra.EssFiniteType k D := by
  let _ : Nontrivial ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n) :=
    targetQuotient_nontrivial (Λ := Λ) (𝔮 := 𝔮) hn
  let _ : IsLocalRing ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n) :=
    targetQuotient_isLocalRing (Λ := Λ) (𝔮 := 𝔮) hn
  let _ : IsArtinianRing ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n) :=
    targetQuotient_isArtinianRing (Λ := Λ) (𝔮 := 𝔮) hn
  let _ :
      FiniteDimensional
        (ResidueField ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n))
        (Algebra.H1Cotangent k
          (ResidueField ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n))) :=
    finiteDimensionalH1Cotangent_targetResidueField
      (k := k) (Λ := Λ) (p := p) 𝔮 n hn
  obtain ⟨ι, S, hdir, hArtinian, hLocal, hFlat, hMaximal, hEssFiniteType, hSup⟩ :=
    exists_artinianLocalSubalgebraApproximation
      (k := k) (Λ := ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n))
  obtain ⟨i, hi⟩ :=
    exists_stage_subalgebra_contains_finset (k := k) S hdir hSup E
  refine ⟨S i, hi, hArtinian i, hLocal i, ?_, ?_, hEssFiniteType i⟩
  -- Proof comment: the stage inclusion produced by Lemma `16.11.1` is flat by construction.
  simpa using hFlat i
  -- Proof comment: the same stage also preserves the closed-point maximal ideal of the target
  -- quotient, which is the transport datum needed later for residue fields and closed fibers.
  simpa using hMaximal i

/-- Helper for Chap16 Lemma 16 11 2: once an Artinian local stage with maximal-ideal
compatibility is fixed, the remaining source route is to build the polynomial map and the smooth
factorization through that stage. -/
private theorem existsSmoothApproximationFactorization_of_stageData
    {p : ℕ} [Fact p.Prime] [CharP k p] [IsGeometricallyRegular k Λ] [IsNoetherianRing Λ]
    (𝔮 : Ideal Λ) [𝔮.IsPrime] (n : ℕ) (hn : 1 ≤ n)
    (D : Subalgebra k ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n))
    (hArtinianD : IsArtinianRing D)
    (hLocalD : IsLocalRing D)
    (hFlatD : D.subtype.Flat)
    (hMaximalD :
      Ideal.map D.subtype (maximalIdeal D) =
        maximalIdeal ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n))
    (hEssFiniteTypeD : Algebra.EssFiniteType k D) :
    ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ),
      ∃ (_ : (approximationLocalMap (φ := φ) 𝔮).Flat)
        (sourceToD : approximationSourceQuot (φ := φ) 𝔮 n →+* D),
        D.subtype.comp sourceToD = approximationTargetMap (φ := φ) 𝔮 n ∧
          sourceToD.SmoothAtPrime (closedPoint D) := by
  -- Proof comment: this is the exact remaining frontier from the source proof. One must transport
  -- residue-field data along `hMaximalD`, choose polynomial generators inside `Λ`, and then apply
  -- the Chapter 15 flat-plus-regular-closed-fiber theorem before the local smoothness criterion.
  let _ : IsArtinianRing D := hArtinianD
  let _ : IsLocalRing D := hLocalD
  let _ : Algebra.EssFiniteType k D := hEssFiniteTypeD
  let _ := hFlatD
  let _ := hMaximalD
  let _ := hn
  -- TODO: use `hMaximalD` to compare residue fields and closed fibers, then build `φ` and the
  -- codomain restriction `sourceToD` from the lifted residue generators.
  sorry

-- Proof sketch: apply Lemma `16.11.1` to the local Artinian quotient
-- `Λ_𝔮 / (𝔮 Λ_𝔮)^n` to find an essentially finite type local Artinian subalgebra containing `E`;
-- choose polynomial generators lifting a basis of differentials of its residue field and then add a
-- regular system of parameters for the remaining regular local quotient. The resulting localized
-- polynomial algebra is flat over `Λ_𝔮`, the induced quotient map factors through the chosen local
-- Artinian subalgebra, and Lemmas `10.39.9`, `10.54.4`, and `10.143.7` upgrade that factorization
-- to the required flat and essentially smooth local factorization.
/-- Lemma 16.11.2: let `k` be a field of characteristic `p > 0`, let `Λ` be a Noetherian
geometrically regular `k`-algebra, let `𝔮 ⊂ Λ` be a prime ideal, let `n` be a natural number, and let
`E` be a finite subset of `Λ_𝔮 / 𝔪(Λ_𝔮)^n`, equivalently
`Λ_𝔮 / (𝔮 Λ_𝔮)^n`. Then there exists a polynomial algebra `k[y₁, …, yₘ]` mapping to `Λ` such that
after localizing at the canonical prime `φ⁻¹(𝔮)`, the induced quotient modulo the `n`th powers of
the localized maximal ideals factors through a local Artinian ring `D`, with the source-to-`D`
map essentially smooth at the closed point of `D`, the map
`D → Λ_𝔮 / 𝔪(Λ_𝔮)^n` flat, and `E` contained in the image of `D`. The source hypothesis
`n ≥ 1` is retained: when `n = 0`, both source and target quotients collapse to the zero ring,
while the conclusion still requires a factorization through a local ring `D`, and `IsLocalRing`
in mathlib carries nontriviality. -/

@[stacks 07FH]
theorem exists_localArtinianPolynomialApproximation
    {p : ℕ} [Fact p.Prime] [CharP k p] [IsGeometricallyRegular k Λ] [IsNoetherianRing Λ]
    (𝔮 : Ideal Λ) [𝔮.IsPrime] (n : ℕ) (hn : 1 ≤ n)
    (E : Finset ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n)) :
    ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ),
      ∃ (_ : (approximationLocalMap (φ := φ) 𝔮).Flat),
        ∃ (D : Type w) (_ : CommRing D) (_ : IsArtinianRing D) (_ : IsLocalRing D),
          ∃ (sourceToD : approximationSourceQuot (φ := φ) 𝔮 n →+* D)
            (DToTarget : D →+* ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n)),
            DToTarget.comp sourceToD = approximationTargetMap (φ := φ) 𝔮 n ∧
              sourceToD.SmoothAtPrime (closedPoint D) ∧
              DToTarget.Flat ∧
              (↑E : Set ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n)) ⊆ Set.range DToTarget := by
  -- Route correction: the executable prefix is now split off into helper lemmas above, including
  -- the Artinian quotient package and the stage-selection theorem from Lemma `16.11.1`.
  have hfdResidueH1 :
      FiniteDimensional
        (ResidueField (Λ_ 𝔮))
        (Algebra.H1Cotangent k (ResidueField (Λ_ 𝔮))) :=
    finiteDimensionalH1Cotangent_residueField_of_geometricallyRegularLocalRing
      (k := k) (A := Λ_ 𝔮) (p := p)
  obtain ⟨D, hE, hArtinianD, hLocalD, hFlatD, hMaximalD, hEssFiniteTypeD⟩ :=
    existsApproximationStageContainingE
      (k := k) (Λ := Λ) (p := p) 𝔮 n hn E
  -- Proof comment: the quotient target has now been replaced by a local Artinian essentially
  -- finite-type stage `D` containing `E`; the remaining gap is to choose the polynomial map `φ`,
  -- force `approximationTargetMap` to land in `D`, and then apply the closed-point smoothness
  -- criterion to the resulting factorization.
  have _ :
      FiniteDimensional
        (ResidueField ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n))
        (Algebra.H1Cotangent k
          (ResidueField ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n))) :=
    finiteDimensionalH1Cotangent_targetResidueField
      (k := k) (Λ := Λ) (p := p) 𝔮 n hn
  let _ : IsArtinianRing D := hArtinianD
  let _ : IsLocalRing D := hLocalD
  let _ : Algebra.EssFiniteType k D := hEssFiniteTypeD
  let DToTarget : D →+* ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n) := D.subtype
  have hE_range : (↑E : Set ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n)) ⊆ Set.range DToTarget := by
    intro x hx
    refine ⟨⟨x, hE hx⟩, rfl⟩
  obtain ⟨m, φ, hFlatLocal, sourceToD, hfactor, hsmooth⟩ :=
    existsSmoothApproximationFactorization_of_stageData
      (k := k) (Λ := Λ) (p := p) 𝔮 n hn D hArtinianD hLocalD hFlatD hMaximalD hEssFiniteTypeD
  clear hfdResidueH1
  -- Proof comment: after the factorization helper returns the polynomial map and the smooth local
  -- source-to-stage map, the theorem is just the explicit assembly of the stored stage data.
  exact ⟨m, φ, hFlatLocal, D, inferInstance, hArtinianD, hLocalD, sourceToD, DToTarget,
    hfactor, hsmooth, hFlatD, hE_range⟩

end

end Algebra
