import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_38_1 (from Chap15) -/
universe u v w

namespace RingHom

open IsLocalRing

/-
Domain-style sampling for Lemma 15.38.1:
- primary domain: infinitesimal lifting criteria for formal smoothness of local ring maps in
  maximal-ideal adic topology;
- inspected owner declarations of the same kind:
  * `RingHom.formally_smooth_for_adic`,
  * `RingHom.FormallySmooth.exists_lift`,
  * `IsLocalRing.of_surjective'`,
  * `RingHom.IsSmallExtension.isLocalRingTarget`;
- best owner abstraction: `RingHom.formally_smooth_for_adic` is the chapter owner, while the local
  extension-map facts should be expressed through the canonical local-ring derivation owners
  `IsLocalRing.of_surjective'` and `IsSmallExtension.isLocalRingTarget`; in particular, the target
  local structure for a square-zero surjection or small extension is derived internally rather than
  stored as extra theorem-level data. The lift itself is the same derived payload as in
  `RingHom.FormallySmooth.exists_lift`;
- primitive data on the right-hand side: the chosen square-zero surjection or small extension
  `π : A' →+* A`, the local map `g : S →+* A`, the nilpotence of `maximalIdeal A'`, the
  residue-field bijectivity, and the commutative square;
- derived API: the existential lift payload, and the locality of any lift `S →+* A`, which should
  not be primitive public data in this bridge theorem.

Source/core/bridge triage:
- `source-facing`: the local lifting criteria against square-zero and small extensions;
- `core/canonical`: `RingHom.formally_smooth_for_adic`;
- `bridge/view`: the equivalences below, which compare the owner predicate with those lifting
  criteria.
-/

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

private abbrev maximalIdealAdic_liftPayload
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A]
    (f : R →+* S) (π : A' →+* A) (g : S →+* A) (g0 : R →+* A') : Prop :=
  ∃ gLift : S →+* A', π.comp gLift = g ∧ gLift.comp f = g0

private theorem maximalIdealAdic_nontrivialTarget_of_squareZero
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A] [IsLocalRing A']
    (π : A' →+* A) (hπsq : RingHom.ker π ^ 2 = ⊥) : Nontrivial A := by
  classical
  by_contra hA
  letI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
  have hker : RingHom.ker π = ⊤ := by
    ext x
    simp [RingHom.mem_ker, Subsingleton.elim (π x) 0]
  have h1sq : (1 : A') ∈ RingHom.ker π ^ 2 := by
    rw [pow_two, hker]
    simpa using Ideal.mul_mem_mul (show (1 : A') ∈ (⊤ : Ideal A') from Ideal.mem_top)
      (show (1 : A') ∈ (⊤ : Ideal A') from Ideal.mem_top)
  have h1 : (1 : A') = 0 := by
    have hmem : (1 : A') ∈ (⊥ : Ideal A') := by
      exact hπsq ▸ h1sq
    exact hmem
  let _ : Nontrivial A' := IsLocalRing.toNontrivial
  exact one_ne_zero h1

private abbrev maximalIdealAdic_residueFieldMapBijective
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A] [IsLocalRing A']
    (π : A' →+* A) (hπsurj : Function.Surjective π) (hπsq : RingHom.ker π ^ 2 = ⊥)
    (g : S →+* A) [IsLocalHom g] : Prop :=
  let _ : Nontrivial A := maximalIdealAdic_nontrivialTarget_of_squareZero π hπsq
  letI : IsLocalRing A := IsLocalRing.of_surjective' π hπsurj
  Function.Bijective (ResidueField.map g)

private theorem maximalIdealAdic_isLocalRingTargetOfSmallExtension
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A]
    (π : A' →+* A) [hπ : IsSmallExtension π] : IsLocalRing A := by
  let _ : Nontrivial A := hπ.instNontrivialTarget
  exact IsLocalRing.of_surjective' π hπ.surjective

private abbrev maximalIdealAdic_residueFieldMapBijectiveOfSmallExtension
    {A' : Type w} {A : Type w} [CommRing A'] [CommRing A]
    (π : A' →+* A) [IsSmallExtension π] (g : S →+* A) [IsLocalHom g] : Prop :=
  let _ : Nontrivial A := inferInstance
  letI : IsLocalRing A := maximalIdealAdic_isLocalRingTargetOfSmallExtension π
  Function.Bijective (ResidueField.map g)

/-- The square-zero local lifting condition appearing in Lemma 15.38.1. The target local-ring
structure is derived canonically from the surjective map `π : A' → A`, so it is not part of the
public data of the condition. -/
abbrev maximalIdealAdic_squareZeroResidueFieldIsoLiftingCondition (f : R →+* S) : Prop :=
  ∀ {A' : Type w} {A : Type w} [CommRing A'] [CommRing A] [IsLocalRing A']
    (π : A' →+* A) (hπsurj : Function.Surjective π) (hπsq : RingHom.ker π ^ 2 = ⊥)
    (_ : IsNilpotent (maximalIdeal A')) (g : S →+* A),
      let _ : Nontrivial A := maximalIdealAdic_nontrivialTarget_of_squareZero π hπsq
      letI : IsLocalRing A := IsLocalRing.of_surjective' π hπsurj
      ∀ [IsLocalHom g] (g0 : R →+* A')
        (_ : maximalIdealAdic_residueFieldMapBijective π hπsurj hπsq g)
        (_ : π.comp g0 = g.comp f),
          maximalIdealAdic_liftPayload f π g g0

/-- The small-extension local lifting condition appearing in the Noetherian refinement of Lemma
15.38.1. The target local-ring structure is derived canonically from the owner predicate
`IsSmallExtension π`, so only the actual extension and residue-field data remain visible. -/
abbrev maximalIdealAdic_smallExtensionResidueFieldIsoLiftingCondition (f : R →+* S) : Prop :=
  ∀ {A' : Type w} {A : Type w} [CommRing A'] [CommRing A]
    (π : A' →+* A) [IsSmallExtension π] (g : S →+* A),
      letI : IsLocalRing A := maximalIdealAdic_isLocalRingTargetOfSmallExtension π
      ∀ [IsLocalHom g] (g0 : R →+* A')
        (_ : maximalIdealAdic_residueFieldMapBijectiveOfSmallExtension π g)
        (_ : π.comp g0 = g.comp f),
          maximalIdealAdic_liftPayload f π g g0

-- Proof sketch: use Lemma `15.37.2` to identify formal smoothness for the maximal-ideal-adic
-- topology with the discrete-source lifting property, then restrict the test objects to local
-- square-zero extensions with nilpotent maximal ideal and residue-field isomorphism. For the
-- converse, replace an arbitrary square-zero lifting problem by the inverse-image local subring
-- generated by the image of `S` in `A ⧸ J`, exactly as in the Stacks argument. The lifted ring
-- hom is automatically local because its composite with the quotient map is `g`.
/-- Lemma 15.38.1: a local homomorphism `f : R →+* S` is formally smooth for the maximal-ideal-adic
topology on `S` if and only if every square-zero lifting problem against a local ring `A` with
nilpotent maximal ideal and residue-field isomorphism `S → A ⧸ J` admits a lift
(hence automatically a local lift). -/
theorem formally_smooth_for_maximalIdeal_adic_iff_local_square_zero_residueFieldIso_lifting
    (f : R →+* S) [IsLocalHom f] :
    f.formally_smooth_for_adic (maximalIdeal S) ↔
      maximalIdealAdic_squareZeroResidueFieldIsoLiftingCondition f := sorry

-- Proof sketch: the forward implication is the main equivalence above. For the converse under the
-- Noetherian hypothesis on `S`, devissage through the filtration of `J` by one-dimensional
-- residue-field quotients reduces the square-zero criterion to the case where `A → A ⧸ J` is a
-- small extension, and then the assumed lifting property supplies the required lift, which is
-- again automatically local.
/-- The Noetherian refinement of the local lifting criterion: it is enough to test liftings only
against small extensions `A → A ⧸ J` with the same residue-field condition, asking only for a
lift in the conclusion since locality is derived. -/
theorem formally_smooth_for_maximalIdeal_adic_iff_local_smallExtension_residueFieldIso_lifting
    (f : R →+* S) [IsLocalHom f] [IsNoetherianRing S] :
    f.formally_smooth_for_adic (maximalIdeal S) ↔
      maximalIdealAdic_smallExtensionResidueFieldIsoLiftingCondition f := sorry

end

end RingHom

/-! ### Lemma_15_38_2 (from Chap15) -/
open IsLocalRing

universe u v

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A] [IsLocalRing A] [IsNoetherianRing A]

/- Domain-style sampling for Lemma 15.38.2:
- primary domain: local commutative algebra relating adic formal smoothness of `k → A` to the
  regular-local owner on `A`;
- sampled owner declarations of the same kind:
  `RingHom.formally_smooth_for_adic`,
  `RingHom.formally_smooth_for_adic_tfae_completion_invariance`,
  `IsRegularLocalRing`,
  `RingHom.IsRegularRingMap.of_comp_of_faithfullyFlat`;
- best owner abstraction: the hypothesis should be stated directly with the chapter owner
  `(algebraMap k A).formally_smooth_for_adic (maximalIdeal A)`, while the conclusion stays on the
  canonical owner `IsRegularLocalRing A`;
- primitive data: the field `k`, the Noetherian local `k`-algebra `A`, and adic formal smoothness
  of the structure map;
- derived API: completion invariance, complete-local presentations, and regularity descent are
  proof inputs only and should not appear as extra wrapper data in the public statement.

Source/core/bridge triage:
- `source-facing`: the implication from maximal-ideal-adic formal smoothness to regularity;
- `core/canonical`: `RingHom.formally_smooth_for_adic` and `IsRegularLocalRing`;
- `bridge/view`: completion and Cohen-structure arguments used internally in the proof.
-/

-- Proof sketch: pass from the given `k`-adic formal smoothness hypothesis to the completion using
-- the completion invariance results from Section `15.37`, reduce to the complete local case, and
-- then apply Cohen structure to identify the completed ring with a quotient of a power series ring.
-- The induced surjection to the power series ring is an isomorphism on `maximalIdeal / maximalIdeal^2`,
-- forcing the dimension of `A` to equal the embedding dimension, which is the definition of
-- regularity for a Noetherian local ring.
/-- Lemma 15.38.2: if `A` is a Noetherian local `k`-algebra and the structure map `k → A` is
formally smooth for the `maximalIdeal A`-adic topology, then `A` is a regular local ring. -/
theorem isRegularLocalRing_of_formallySmooth_for_maximalIdeal_adic
    (hfs : (algebraMap k A).formally_smooth_for_adic (maximalIdeal A)) :
    IsRegularLocalRing A := sorry

end

/-! ### Lemma_15_38_3 (from Chap15) -/
open IsLocalRing

universe u v

section

variable (A : Type v) [CommRing A] [IsCompleteLocalRing A]

local notation "κA" => ResidueField A

/- Domain-style sampling for Lemma 15.38.3:
- primary domain: coefficient fields of complete local algebras, obtained by lifting the
  residue-field quotient through adic formal smoothness;
- sampled owner declarations:
  `Algebra.formallySmooth_of_isSeparableOver`,
  `RingHom.formally_smooth_for_adic`,
  `RingHom.exists_continuous_lift_of_formally_smooth_for_adic`,
  `IsLocalRing.residue`;
- best owner abstraction: this lemma is `source-facing`, but its section should be exposed in the
  canonical residue-map owner shape rather than through the derived `IsScalarTower.toAlgHom`
  wrapper;
- primitive data: the complete local `k`-algebra `A` and the separability of `ResidueField A / k`;
- derived API: a coefficient-field section of the canonical residue map `residue A`.

Source/core/bridge triage:
- `source-facing`: existence of a coefficient field in the complete local equal-characteristic case;
- `core/canonical`: `Algebra.FormallySmooth k (ResidueField A)` and the chapter owner
  `RingHom.formally_smooth_for_adic`;
- `bridge/view`: the adic lifting theorem producing the section of the residue-field quotient.
-/

-- Proof sketch: use Proposition `10.158.9` to upgrade the separability hypothesis on
-- `ResidueField A / k` to formal smoothness of `k → ResidueField A`, then apply Lemma `15.37.2`
-- and Lemma `15.37.5` to the maximal-ideal-adic topology on `A` and the quotient map
-- `A → ResidueField A` to obtain a lift of the identity of `ResidueField A`.
/-- Lemma 15.38.3: if `A` is a complete local `k`-algebra and the residue field extension
`κA / k` is separable in the Stacks Project sense, then the residue map `residue A : A →+* κA`
admits a `k`-algebra section. -/
theorem exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver
    (k : Type u) [Field k] [Algebra k A]
    [Algebra.IsSeparableOver k κA] :
    ∃ φ : κA →ₐ[k] A, (residue A).comp φ = RingHom.id κA := by
  letI : TopologicalSpace κA := ⊥
  letI : DiscreteTopology κA := ⟨rfl⟩
  letI : TopologicalSpace A := Ideal.adicTopology (maximalIdeal A)
  let f : k →+* κA := algebraMap k κA
  have hf : f.formally_smooth_for_adic (⊥ : Ideal κA) := by
    letI : TopologicalSpace k := ⊥
    letI : DiscreteTopology k := ⟨rfl⟩
    let B : RingFilterBasis κA := Ideal.ringFilterBasis (⊥ : Ideal κA)
    letI : TopologicalSpace κA := Ideal.adicTopology (⊥ : Ideal κA)
    letI : IsTopologicalRing κA := by
      change @IsTopologicalRing κA B.topology _
      infer_instance
    letI : TopologicalRing.IsPreadicRing κA :=
      { toIsTopologicalRing := ‹IsTopologicalRing κA›
        exists_ideal_isAdic := ⟨⊥, rfl⟩ }
    rw [RingHom.formally_smooth_for_adic_iff]
    have hfs : (algebraMap k κA).FormallySmooth := by
      rw [RingHom.formallySmooth_algebraMap]
      exact Algebra.formallySmooth_of_isSeparableOver
    simpa [f] using RingHom.FormallySmooth.toTopologically hfs continuous_of_discreteTopology
  have hA : IsAdic (maximalIdeal A) := rfl
  have hS : IsAdic (⊥ : Ideal κA) := by
    rw [is_bot_adic_iff]
    infer_instance
  have hJClosed : IsClosed ((maximalIdeal A : Ideal A) : Set A) := by
    have hOpen : IsOpen ((maximalIdeal A : Ideal A) : Set A) := by
      simpa [pow_one] using (isAdic_iff.mp hA).1 1
    simpa using AddSubgroup.isClosed_of_isOpen (maximalIdeal A).toAddSubgroup hOpen
  let ψ : κA →+* A ⧸ maximalIdeal A := RingHom.id κA
  have hψ : Continuous ψ := continuous_of_discreteTopology
  have hcomm :
      (Ideal.Quotient.mk (maximalIdeal A)).comp (algebraMap k A) = ψ.comp f := by
    ext x
    rfl
  have hpow : ∃ t : ℕ+, maximalIdeal A ^ (t : ℕ) ≤ maximalIdeal A := by
    exact ⟨1, by simpa using (le_rfl : maximalIdeal A ^ (1 : ℕ) ≤ maximalIdeal A)⟩
  have hlift :
      ∃ φ : κA →+* A,
        (Ideal.Quotient.mk (maximalIdeal A)).comp φ = RingHom.id κA ∧
          φ.comp f = algebraMap k A ∧ Continuous φ := by
    exact
      f.exists_continuous_lift_of_formally_smooth_for_adic
        (⊥ : Ideal κA) hf hS
        (maximalIdeal A) (maximalIdeal A) hA hJClosed hpow
        ψ hψ (algebraMap k A) hcomm
  rcases hlift with ⟨φ, hφ, hφk, _⟩
  have hφres : (residue A).comp φ = RingHom.id κA := by
    simpa using hφ
  refine ⟨{ toRingHom := φ, commutes' := DFunLike.congr_fun hφk }, by simpa using hφres⟩

end

/-! ### Lemma_15_38_4 (from Chap15) -/
open IsLocalRing

universe u v

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A] [IsCompleteLocalRing A]
  [IsRegularLocalRing A]

/- Domain-style sampling for Lemma 15.38.4:
- primary domain: equal-characteristic Cohen-structure presentations of complete regular local
  algebras.
- sampled owner declarations:
  `exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver`,
  `exists_algEquiv_mvPowerSeries_of_residueField_bijective`,
  `MvPowerSeries.renameEquiv`,
  `AlgEquiv.restrictScalars`.
- best owner abstraction: the canonical owner is the finite-index power-series presentation
  `MvPowerSeries σ (ResidueField A)` with `[Finite σ]` from Lemma `10.160.10 (2)`. This file is a
  `source-facing` bridge that keeps the textbook `Fin d` surface by reindexing the canonical owner
  rather than duplicating it.
- primitive data: the complete regular local `k`-algebra `A` and the separability of
  `ResidueField A / k`.
- derived API: a `k`-algebra equivalence from a finite-variable formal power series ring over the
  residue field of `A`.

Source/core/bridge triage:
- `source-facing`: the `Fin d`-indexed Stacks Project presentation below.
- `core/canonical`: `exists_algEquiv_mvPowerSeries_of_residueField_bijective`.
- `bridge/view`: the residue-field section from Lemma `15.38.3`, followed by reindexing along
  `Fintype.equivFin`.
-/

-- Proof sketch: choose a `k`-algebra section `ResidueField A →ₐ[k] A` of the residue map via
-- Lemma `15.38.3`. This gives `A` a coefficient-field structure over `ResidueField A`, and the
-- induced residue-field map is the identity. Apply the canonical finite-index presentation from
-- Lemma `10.160.10 (2)` over `ResidueField A`, then reindex the variables along
-- `Fintype.equivFin` and restrict scalars back to `k`.
/-- Lemma 15.38.4: if `A` is a complete regular local `k`-algebra and the residue field extension
`ResidueField A / k` is separable in the Stacks Project sense, then `A` is `k`-algebra
isomorphic to a finite-variable formal power series ring over its residue field. -/
theorem exists_algEquiv_mvPowerSeries_residueField_of_isSeparableOver_of_isRegularLocalRing
    [Algebra.IsSeparableOver k (ResidueField A)] :
    ∃ d : ℕ, Nonempty (MvPowerSeries (Fin d) (ResidueField A) ≃ₐ[k] A) := by
  sorry

end

/-! ### Lemma_15_38_5 (from Chap15) -/
open IsLocalRing

universe u v

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A] [IsRegularLocalRing A]

/- Domain-style sampling for Lemma 15.38.5:
- primary domain: local commutative algebra of regular local `k`-algebras and maximal-ideal-adic
  formal smoothness.
- sampled owner declarations:
  `RingHom.formally_smooth_for_adic`,
  `RingHom.formally_smooth_for_adic_tfae_completion_invariance`,
  `exists_algEquiv_mvPowerSeries_residueField_of_isSeparableOver_of_isRegularLocalRing`,
  `Algebra.IsSeparableOver`.
- best owner abstraction: the public conclusion should be stated directly with the chapter owner
  `(algebraMap k A).formally_smooth_for_adic (maximalIdeal A)`. Completion invariance and the
  finite-variable power-series presentation are proof bridges, not extra public data.
- primitive data: the field `k`, the regular local `k`-algebra `A`, and the Stacks-separability
  hypothesis on `ResidueField A / k`.
- derived API: formal smoothness of the structural map for the `maximalIdeal A`-adic topology.

Source/core/bridge triage:
- `source-facing`: the textbook implication from regularity plus separable residue field to adic
  formal smoothness.
- `core/canonical`: `RingHom.formally_smooth_for_adic`.
- `bridge/view`: completion invariance and the complete-regular-local power-series presentation.
-/

-- Proof sketch: by Lemma `15.37.4`, formal smoothness for the `maximalIdeal A`-adic topology can
-- be checked after passing to the completion. Lemma `15.38.4` identifies the completed regular
-- local `k`-algebra with a finite-variable power series ring over `ResidueField A`, and
-- Lemma `10.138.3` together with Lemma `15.37.2` shows that this power series ring is formally
-- smooth over `k` for its maximal-ideal-adic topology.
/-- Lemma 15.38.5: if `(A, maximalIdeal A, ResidueField A)` is a regular local `k`-algebra and the
residue field extension `ResidueField A / k` is separable in the Stacks Project sense, then the
structure map `k → A`, formalized by `algebraMap k A`, is formally smooth for the
`maximalIdeal A`-adic topology. -/
theorem formallySmooth_for_maximalIdeal_adic_of_isRegularLocalRing_of_isSeparableOver
    [Algebra.IsSeparableOver k (ResidueField A)] :
    (algebraMap k A).formally_smooth_for_adic (maximalIdeal A) := sorry

end

/-! ### Lemma_15_38_6 (from Chap15) -/
open IsLocalRing
open RingHom

universe u v

namespace Algebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain-style sampling for Lemma 15.38.6:
- primary domain: smoothness at a prime versus adic formal smoothness of the induced local map in
  commutative algebra;
- sampled owner declarations:
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `Localization.localRingHom`,
  `Algebra.FormallySmooth.localization_base`,
  `RingHom.FormallySmooth.toTopologically`;
- best owner abstraction: the source-facing owner is `SmoothAtPrime A B q`, while the canonical
  local owner `IsSmoothAt A q.asIdeal` is the internal bridge, and the localized adic
  formal-smoothness condition is derived from the canonical localized algebra and then translated
  to the chapter owner `RingHom.formally_smooth_for_adic`;
- primitive data: a prime `q : PrimeSpectrum B` together with the finite-presentation hypothesis
  needed for the source-facing/local smoothness bridge;
- derived API: the equivalence between smoothness at `q` and adic formal smoothness of the
  canonical local map `A_(q ∩ A) → B_q`.

Source/core/bridge triage:
- `source-facing`: the equivalence between `SmoothAtPrime A B q` and adic formal smoothness of
  `A_(q ∩ A) → B_q`;
- `core/canonical`: `IsSmoothAt A q.asIdeal`;
- `bridge/view`: `(Localization.localRingHom ...).formally_smooth_for_adic` for the localized map
  `Localization.AtPrime (q.asIdeal.under A) → Localization.AtPrime q.asIdeal`. -/

private theorem localRingHom_formally_smooth_for_adic_of_isSmoothAt
    (q : PrimeSpectrum B) [IsSmoothAt A q.asIdeal] :
    formally_smooth_for_adic
      (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl)
      (maximalIdeal (Localization.AtPrime q.asIdeal)) := by
  let f := Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl
  letI : Algebra (Localization.AtPrime (q.asIdeal.under A)) (Localization.AtPrime q.asIdeal) :=
    f.toAlgebra
  letI : TopologicalSpace (Localization.AtPrime (q.asIdeal.under A)) := ⊥
  letI : DiscreteTopology (Localization.AtPrime (q.asIdeal.under A)) := ⟨rfl⟩
  letI : TopologicalSpace (Localization.AtPrime q.asIdeal) :=
    Ideal.adicTopology (maximalIdeal (Localization.AtPrime q.asIdeal))
  letI : TopologicalRing.IsPreadicRing (Localization.AtPrime q.asIdeal) :=
    { toIsTopologicalRing := inferInstance
      exists_ideal_isAdic := ⟨maximalIdeal (Localization.AtPrime q.asIdeal), rfl⟩ }
  change f.FormallySmoothTopologically
  have hfsAlg :
      Algebra.FormallySmooth (Localization.AtPrime (q.asIdeal.under A))
        (Localization.AtPrime q.asIdeal) := by
    letI : Algebra.FormallySmooth A (Localization.AtPrime q.asIdeal) := ‹IsSmoothAt A q.asIdeal›
    simpa using
      (Algebra.FormallySmooth.localization_base (Ideal.primeCompl (q.asIdeal.under A)))
  have hfs : f.FormallySmooth := by
    simpa [f, RingHom.algebraMap_toAlgebra] using hfsAlg
  simpa [formally_smooth_for_adic, f] using
    (FormallySmooth.toTopologically hfs continuous_of_discreteTopology)

private theorem isSmoothAt_of_localRingHom_formally_smooth_for_adic
    [FinitePresentation A B] (q : PrimeSpectrum B)
    (hq :
      formally_smooth_for_adic
        (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl)
        (maximalIdeal (Localization.AtPrime q.asIdeal))) :
    IsSmoothAt A q.asIdeal := by
  sorry

-- Proof sketch: rewrite `SmoothAtPrime A B q` through `smoothAtPrime_iff_isSmoothAt`, then use
-- the canonical localized-owner chain
-- `IsSmoothAt A q.asIdeal → Algebra.FormallySmooth A B_q
--   → Algebra.FormallySmooth A_(q ∩ A) B_q
--   → (A_(q ∩ A) → B_q).formally_smooth_for_adic (maximalIdeal B_q)`.
-- The converse uses the same localized map as source-facing adic data together with the
-- finite-presentation hypothesis carried by the theorem.
/-- Lemma 15.38.6 as a source-facing bridge: if `A → B` is finitely presented and `q` is a prime
of `B`, then `A → B` is smooth at `q` in the Stacks sense if and only if the induced local map
`A_(q ∩ A) → B_q` is formally smooth for the `maximalIdeal B_q`-adic topology. -/
theorem smoothAtPrime_iff_formally_smooth_for_adic_localized_map
    [FinitePresentation A B] (q : PrimeSpectrum B) :
    SmoothAtPrime A B q ↔
      formally_smooth_for_adic
        (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl)
        (maximalIdeal (Localization.AtPrime q.asIdeal)) := by
  rw [smoothAtPrime_iff_isSmoothAt]
  constructor
  · intro hq
    letI : IsSmoothAt A q.asIdeal := hq
    exact localRingHom_formally_smooth_for_adic_of_isSmoothAt q
  · intro hq
    exact isSmoothAt_of_localRingHom_formally_smooth_for_adic q hq

end

end Algebra
