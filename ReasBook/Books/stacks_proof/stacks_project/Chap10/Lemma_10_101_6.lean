import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_99_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits IsLocalRing
open LinearMap
open scoped Pointwise TensorProduct

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {I : Ideal R}

local notation "IM" => I • (⊤ : Submodule R M)
local notation "𝔪" => maximalIdeal R
local notation "k" => IsLocalRing.ResidueField R
local notation "M̄" => M ⧸ (𝔪 • (⊤ : Submodule R M))
local notation "mkQ𝔪" => Submodule.mkQ (𝔪 • (⊤ : Submodule R M))
set_option quotPrecheck false in
local notation "Tor₁[" R "](" N ", " M ")" =>
  (((Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M))

/- Domain triage:
- primary domain: commutative algebra of flatness over quotient rings and nilpotent thickenings in
  an Artinian local ring;
- sampled owner declarations:
  `Module.Flat`,
  `flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes`,
  `flat_tfae_tor_vanishing_criteria`,
  `isArtinianRing_iff_isNilpotent_maximalIdeal`;
- best owner abstraction: the canonical flatness predicate `Module.Flat`, with the nilpotent-ideal
  criterion from `10.99.8` supplying the core reverse implication;
- primitive data: the ring `R`, module `M`, and ideal `I`;
- derived API: quotient flatness over `R ⧸ I` and the vanishing statement `Tor₁^R(R ⧸ I, M) = 0`.

Layering:
- `source-facing`: the Artinian-local iff criterion stated in the textbook;
- `core/canonical`: `Module.Flat` together with the Chapter 10 nilpotent-ideal flatness owner;
- `bridge/view`: the Artinian-local specialization, using that every proper ideal lies in the
  nilpotent maximal ideal.
-/

-- The forward implication is quotient flatness plus freeness of a flat module over an Artinian
-- local ring, which gives Tor-vanishing by projectivity. The reverse implication reduces the
-- Artinian-local case to the earlier nilpotent-ideal criterion after proving that every proper
-- ideal is nilpotent.
/-- Helper for Lemma 10.101.6: once `J • M = M`, the same holds for every power of `J`. -/
lemma pow_smul_top_eq_top_of_smul_top_eq_top
    {J : Ideal R} (hJM : J • (⊤ : Submodule R M) = ⊤) :
    ∀ n : ℕ, (J ^ n) • (⊤ : Submodule R M) = ⊤
  | 0 => by
      -- The zeroth power acts as the identity on the top submodule.
      simpa [Submodule.pow_zero]
  | n + 1 => by
      -- Rewrite one more power of `J` as one further smul by `J`.
      rw [J.pow_succ, Submodule.mul_smul, hJM, pow_smul_top_eq_top_of_smul_top_eq_top hJM n]

/-- Helper for Lemma 10.101.6: a nilpotent ideal acting surjectively on `M` forces `M = 0`. -/
lemma subsingleton_of_ideal_smul_top_eq_top_of_isNilpotent
    (J : Ideal R) (hJM : J • (⊤ : Submodule R M) = ⊤) (hJ : IsNilpotent J) :
    Subsingleton M := by
  rcases hJ with ⟨n, hn⟩
  -- Push the equality `J • M = M` through the nilpotent power.
  have hpow : (J ^ n) • (⊤ : Submodule R M) = ⊤ :=
    pow_smul_top_eq_top_of_smul_top_eq_top (M := M) hJM n
  exact (Submodule.subsingleton_iff R).mp <|
    subsingleton_of_bot_eq_top <| by
      simpa [hn] using hpow

/-- Helper for Lemma 10.101.6: if `N + JN' = M` and `J` is nilpotent, then `N = M`. -/
lemma eq_top_of_sup_eq_top_of_isNilpotent
    (J : Ideal R) (N N' : Submodule R M) (hMN : N ⊔ J • N' = ⊤) (hJ : IsNilpotent J) :
    N = ⊤ := by
  -- Pass to the quotient by `N`, where the hypothesis becomes `J • Q = Q`.
  have hquot_smul : J • Submodule.map N.mkQ N' = ⊤ := by
    rw [← Submodule.map_smul'', Submodule.map_mkQ_eq_top, hMN]
  have hquot_top : J • (⊤ : Submodule R (M ⧸ N)) = ⊤ := by
    apply top_unique
    have hle : J • Submodule.map N.mkQ N' ≤ J • (⊤ : Submodule R (M ⧸ N)) :=
      smul_mono_right J
        (show Submodule.map N.mkQ N' ≤ (⊤ : Submodule R (M ⧸ N)) from le_top)
    calc
      (⊤ : Submodule R (M ⧸ N)) = J • Submodule.map N.mkQ N' := by
        symm
        exact hquot_smul
      _ ≤ J • (⊤ : Submodule R (M ⧸ N)) := hle
  have hsub : Subsingleton (M ⧸ N) :=
    subsingleton_of_ideal_smul_top_eq_top_of_isNilpotent (M := M ⧸ N) J hquot_top hJ
  exact Submodule.Quotient.subsingleton_iff.mp hsub

/-- Helper for Lemma 10.101.6: a lifted basis of `M / maximalIdeal R • M` is a basis of a flat
module when the maximal ideal is nilpotent. -/
lemma basis_of_lifts_of_quotient_basis_of_flat_of_nilpotent_maximalIdeal
    {A : Type*} (h_nil : IsNilpotent 𝔪) (x : A → M)
    (hbar : ∃ bbar : Module.Basis A (R ⧸ 𝔪) M̄, ∀ a, bbar a = mkQ𝔪 (x a))
    (hflat : Module.Flat R M) :
    ∃ b : Module.Basis A R M, ∀ a, b a = x a := by
  classical
  letI : Module.Flat R M := hflat
  rcases hbar with ⟨bbar, hbbar⟩
  let f : (R ⧸ 𝔪) →ₗ[R ⧸ 𝔪] M →ₗ[R] M̄ :=
    (LinearMap.ringLmapEquivSelf (R ⧸ 𝔪) (R ⧸ 𝔪) (M →ₗ[R] M̄)).symm mkQ𝔪
  let e₀ : ((R ⧸ 𝔪) ⊗[R] M) →ₗ[R ⧸ 𝔪] M̄ :=
    TensorProduct.AlgebraTensorModule.lift f
  have e₀_apply (y : M) : e₀ ((1 : R ⧸ 𝔪) ⊗ₜ[R] y) = mkQ𝔪 y := by
    simp [e₀, f]
  have e₀_restrictScalars :
      e₀.restrictScalars R = (TensorProduct.quotTensorEquivQuotSMul M 𝔪).toLinearMap := by
    apply TensorProduct.ext'
    intro r y
    refine Quotient.inductionOn r ?_
    intro a
    change e₀ (Ideal.Quotient.mk 𝔪 a ⊗ₜ[R] y) =
      TensorProduct.quotTensorEquivQuotSMul M 𝔪 (Ideal.Quotient.mk 𝔪 a ⊗ₜ[R] y)
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    simp [e₀, f]
    simpa using (algebraMap_smul (R ⧸ 𝔪) a (Submodule.Quotient.mk y))
  let e : ((R ⧸ 𝔪) ⊗[R] M) ≃ₗ[R ⧸ 𝔪] M̄ :=
    LinearEquiv.ofBijective e₀
      ⟨by
          intro u v huv
          have huv' : e₀.restrictScalars R u = e₀.restrictScalars R v := huv
          rw [e₀_restrictScalars] at huv'
          exact (TensorProduct.quotTensorEquivQuotSMul M 𝔪).injective huv'
        , by
          intro z
          obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (𝔪 • (⊤ : Submodule R M)) z
          exact ⟨(1 : R ⧸ 𝔪) ⊗ₜ[R] y, e₀_apply y⟩⟩
  have e_apply (y : M) : e ((1 : R ⧸ 𝔪) ⊗ₜ[R] y) = mkQ𝔪 y := e₀_apply y
  -- The lifted family is linearly independent because its image modulo `𝔪` is a basis.
  have hx_tensor_li :
      LinearIndependent (R ⧸ 𝔪) (TensorProduct.mk R (R ⧸ 𝔪) M 1 ∘ x) := by
    refine ((e.toLinearMap).linearIndependent_iff (by simp)).mp ?_
    have hcomp : e ∘ TensorProduct.mk R (R ⧸ 𝔪) M 1 ∘ x = bbar := by
      funext a
      simpa [hbbar a] using e_apply (x a)
    simpa [hcomp] using bbar.linearIndependent
  have hx_li : LinearIndependent R x :=
    Module.IsLocalRing.linearIndependent_of_flat _ hx_tensor_li
  -- The quotient basis also shows that the lifts span modulo `𝔪`, hence span all of `M`.
  have hmkQx : mkQ𝔪 ∘ x = bbar := by
    funext a
    exact (hbbar a).symm
  have hgen : Submodule.span R (mkQ𝔪 '' Set.range x) = ⊤ := by
    rw [← Set.range_comp, hmkQx, ← Submodule.restrictScalars_span R (R ⧸ 𝔪)
      Ideal.Quotient.mk_surjective, Submodule.restrictScalars_eq_top_iff]
    exact bbar.span_eq
  have hsup : Submodule.span R (Set.range x) ⊔ 𝔪 • (⊤ : Submodule R M) = ⊤ := by
    have hmap : Submodule.map mkQ𝔪 (Submodule.span R (Set.range x)) = ⊤ := by
      rw [Submodule.map_span]
      exact hgen
    simpa [sup_comm] using
      (Submodule.map_mkQ_eq_top
        (p := 𝔪 • (⊤ : Submodule R M)) (p' := Submodule.span R (Set.range x))).mp hmap
  have hx_span_eq : Submodule.span R (Set.range x) = ⊤ :=
    eq_top_of_sup_eq_top_of_isNilpotent (R := R) (M := M) 𝔪
      (Submodule.span R (Set.range x)) (⊤ : Submodule R M) hsup h_nil
  have hbij : Function.Bijective (Finsupp.linearCombination R x) := by
    refine ⟨hx_li, ?_⟩
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hx_span_eq
  refine ⟨Module.Basis.ofRepr (LinearEquiv.ofBijective (Finsupp.linearCombination R x) hbij).symm,
    ?_⟩
  intro a
  simp

/-- Helper for Lemma 10.101.6: the maximal ideal of an Artinian local ring is nilpotent. -/
lemma maximalIdeal_isNilpotent_of_artinian_local :
    IsNilpotent (maximalIdeal R) := by
  -- The Artinian-local hypothesis gives the nilpotence of the maximal ideal directly.
  exact (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp inferInstance

/-- Helper for Lemma 10.101.6: a flat module over an Artinian local ring is free. -/
lemma free_of_flat_of_artinian_local
    (hflat : Module.Flat R M) :
    Module.Free R M := by
  classical
  -- Use the Artinian-local hypothesis to access the nilpotent maximal-ideal basis criterion.
  have h_nil : IsNilpotent 𝔪 :=
    maximalIdeal_isNilpotent_of_artinian_local (R := R)
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  -- Choose a basis of the residue-field quotient and lift each basis vector to `M`.
  let bbar := Module.Free.chooseBasis (R ⧸ 𝔪) M̄
  let x := fun a ↦
    Classical.choose (Submodule.mkQ_surjective (𝔪 • (⊤ : Submodule R M)) (bbar a))
  -- The nilpotent maximal-ideal basis criterion upgrades the lifted quotient basis to `M`.
  obtain ⟨b, _hb⟩ :=
    basis_of_lifts_of_quotient_basis_of_flat_of_nilpotent_maximalIdeal
      (R := R) (M := M) h_nil x
      ⟨bbar, fun a ↦ (Classical.choose_spec
        (Submodule.mkQ_surjective (𝔪 • (⊤ : Submodule R M)) (bbar a))).symm⟩
      hflat
  exact Module.Free.of_basis b

/-- Helper for Lemma 10.101.6: flatness descends to the quotient module after base change to
`R ⧸ I`. -/
lemma flat_quotient_module_of_flat
    (hflat : Module.Flat R M) :
    Module.Flat (R ⧸ I) (M ⧸ IM) := by
  -- Base change gives flatness of the tensor model `(R ⧸ I) ⊗[R] M`.
  letI : Module.Flat R M := hflat
  have hTensor : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
    Module.Flat.baseChange (R := R) (S := R ⧸ I) (M := M)
  -- Transport the owner statement across the standard quotient-tensor comparison.
  let e : (M ⧸ IM) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] M) :=
    (TensorProduct.quotTensorEquivQuotSMul M I).symm.extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  letI : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) := hTensor
  exact Module.Flat.of_linearEquiv e

/-- Helper for Lemma 10.101.6: flat modules have vanishing `Tor₁^R(R ⧸ I, M)`. -/
lemma tor_one_quotient_vanishes_of_flat
    (hflat : Module.Flat R M) :
    IsZero (Tor₁[R](R ⧸ I, M)) := by
  -- Over an Artinian local ring, a flat module is free, hence projective.
  letI : Module.Free R M := free_of_flat_of_artinian_local (R := R) (M := M) hflat
  letI : Module.Projective R M := inferInstance
  -- Projective modules kill higher `Tor` in the second variable.
  simpa using
    (CategoryTheory.isZero_Tor_succ_of_projective
      (ModuleCat R) (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R M) 0)

/-- Helper for Lemma 10.101.6: every proper ideal of an Artinian local ring is nilpotent. -/
lemma isNilpotent_of_proper_ideal_of_artinian_local
    (hI : I ≠ ⊤) :
    IsNilpotent I := by
  -- A proper ideal lies in the maximal ideal of the local ring, and that maximal ideal is
  -- nilpotent in the Artinian case.
  rcases maximalIdeal_isNilpotent_of_artinian_local (R := R) with ⟨n, hn⟩
  refine ⟨n, le_antisymm ?_ bot_le⟩
  calc
    I ^ n ≤ maximalIdeal R ^ n :=
      Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hI) n
    _ = 0 := hn

-- Proof sketch: for the forward implication, reuse the canonical flat base-change and Tor-vanishing
-- owners. For the converse, a proper ideal in an Artinian local ring is nilpotent because it lies
-- in the nilpotent maximal ideal, so the argument reduces to the Chapter 10 nilpotent-thickening
-- criterion specialized to this Artinian-local setting.
/-- Lemma 10.101.6: for an Artinian local ring `R`, an `R`-module `M`, and a proper ideal
`I ⊂ R`, the module `M` is flat over `R` if and only if `M / IM` is flat over `R / I` and
`Tor₁^R(R / I, M)` vanishes. -/
@[stacks 051K]
theorem flat_iff_flat_mod_ideal_and_tor_one_quotient_vanishes_of_artinian_local
    (hI : I ≠ ⊤) :
    Module.Flat R M ↔
      Module.Flat (R ⧸ I) (M ⧸ IM) ∧
        IsZero (Tor₁[R](R ⧸ I, M)) := by
  constructor
  · intro hflat
    -- The easy direction is just quotient flatness plus Tor-vanishing for a flat module.
    exact ⟨flat_quotient_module_of_flat (R := R) (M := M) (I := I) hflat,
      tor_one_quotient_vanishes_of_flat (R := R) (M := M) (I := I) hflat⟩
  · rintro ⟨hflatQuot, htor⟩
    -- Route correction: the textbook quotient-basis route would pass through Lemmas `10.101.2`
    -- and `10.101.3`, but that dependency chain currently rebuilds through a broken earlier file.
    -- The stable earlier owner `10.99.8` packages the same nilpotent-thickening conclusion.
    have hnil : IsNilpotent I :=
      isNilpotent_of_proper_ideal_of_artinian_local (R := R) (I := I) hI
    -- Apply the earlier nilpotent-ideal criterion once the Artinian-local nilpotence is known.
    exact (flatness_and_tor_vanishing_along_ideal_powers
      (R := R) (I := I) (M := M) hflatQuot htor).2.2 hnil

end
