import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Lemma_10_10_2
import StacksProject_2024.Chap10.Lemma_10_23_2
import StacksProject_2024.Chap10.Lemma_10_78_2
import StacksProject_2024.Chap10.Definition_10_78_1
import StacksProject_2024.Chap15.Definition_15_118_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory

universe u v

namespace ModuleCat

section

variable {R : Type u} [CommRing R]
variable (M : ModuleCat R)

/-- Helper for Lemma 15.118.2: a one-sided tensor-unit witness is equivalent to the chapter owner
`(tensorLeft M).IsEquivalence`. -/
lemma tensor_unit_iff_tensorLeft_isEquivalence :
    (∃ N : ModuleCat R, Nonempty (M ⊗ N ≅ 𝟙_ _)) ↔ (tensorLeft M).IsEquivalence := by
  constructor
  · intro h
    rcases h with ⟨N, ⟨e⟩⟩
    -- A one-sided tensor inverse already gives the specialized invertibility predicate.
    have hInvertible : Module.Invertible R M :=
      Module.Invertible.left e.toLinearEquiv
    exact (tensorLeft_isEquivalence_iff_moduleInvertible M).2 hInvertible
  · intro hM
    -- Forget the second isomorphism from the two-sided tensor-inverse owner theorem.
    rcases (CategoryTheory.tensorLeft_isEquivalence_iff_exists_tensor_inverse M).1 hM with
      ⟨N, ⟨e⟩, -⟩
    exact ⟨N, ⟨e⟩⟩

/-- Helper for Lemma 15.118.2: an invertible module becomes free of rank `1` on some basic open
neighborhood of every prime. -/
lemma exists_basicOpen_linearEquiv_fin_one_of_moduleInvertible [Module.Invertible R M]
    (p : PrimeSpectrum R) :
    ∃ r : R, r ∉ p.asIdeal ∧
      Nonempty (LocalizedModule.Away r M ≃ₗ[Localization.Away r] (Fin 1 → Localization.Away r)) := by
  letI : Module.Finite R M := inferInstance
  letI : Module.Projective R M := inferInstance
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  letI : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) := by
    letI : Module.Invertible (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) :=
      Module.Invertible.of_isLocalization p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    infer_instance
  obtain ⟨r, hr, hfree, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (Localization.AtPrime p.asIdeal)
  letI : Module.Free (Localization.Away r) (LocalizedModule.Away r M) := hfree
  letI : Module.Invertible (Localization.Away r) (LocalizedModule.Away r M) := inferInstance
  have hlinear :
      Nonempty (LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r) :=
    (Module.Invertible.free_iff_linearEquiv (R := Localization.Away r)
      (M := LocalizedModule.Away r M)).mp hfree
  -- The away-localized free rank-one module is equivalent to the standard free module of rank `1`.
  rcases hlinear with ⟨e⟩
  exact ⟨r, hr, ⟨e.trans (LinearEquiv.funUnique (Fin 1) (Localization.Away r)
    (Localization.Away r)).symm⟩⟩

/-- Helper for Lemma 15.118.2: an invertible module is finite locally free of rank `1`. -/
lemma finiteLocallyFreeOfRank_one_of_moduleInvertible [Module.Invertible R M] :
    Module.FiniteLocallyFreeOfRank R M 1 := by
  let s : Set R := {r | Nonempty (LocalizedModule.Away r M ≃ₗ[Localization.Away r] (Fin 1 → Localization.Away r))}
  have hs_cover : (⨆ r ∈ s, PrimeSpectrum.basicOpen r) = ⊤ := by
    apply SetLike.ext'
    change (↑(⨆ r ∈ s, PrimeSpectrum.basicOpen r) : Set (PrimeSpectrum R)) = Set.univ
    rw [Set.eq_univ_iff_forall]
    intro p
    rcases exists_basicOpen_linearEquiv_fin_one_of_moduleInvertible (M := M) p with ⟨r, hr, he⟩
    have hrs : r ∈ s := he
    have hp_basic : p ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      simpa [PrimeSpectrum.mem_basicOpen] using hr
    exact
      (show (PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum R)) ≤
          ⨆ t ∈ s, PrimeSpectrum.basicOpen t from
          le_iSup_of_le r <| le_iSup_of_le hrs le_rfl) hp_basic
  have hs_span : Ideal.span s = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hs_cover
  -- The standard-open cover `s` now matches the owner data for finite local freeness of rank `1`.
  exact ⟨s, hs_span, fun r hr ↦ hr⟩

/-- Helper for Lemma 15.118.2: rank-one finite local freeness implies finite presentation. -/
lemma finitePresentation_of_finiteLocallyFreeOfRank_one [Module.FiniteLocallyFreeOfRank R M 1] :
    Module.FinitePresentation R M := by
  -- The rank-one hypothesis first gives finite local freeness.
  letI : Module.FiniteLocallyFree R M := Module.finiteLocallyFree_ofRank (R := R) (M := M) 1
  -- Then the finite-projective TFAE supplies finite presentation.
  have hfpflat : Module.FinitePresentation R M ∧ Module.Flat R M :=
    (module_finite_projective_tfae.out 6 0).mp
      (show Module.FiniteLocallyFree R M from inferInstance)
  exact hfpflat.1

/-- Helper for Lemma 15.118.2: localizing the codomain `R` of the contraction map identifies it
with the away-localized ring. -/
noncomputable def localized_contractLeft_target_equiv (f : R) :
    LocalizedModule.Away f R ≃ₗ[R] Localization.Away f :=
  IsLocalizedModule.linearEquiv (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) R)
    (Algebra.linearMap R (Localization.Away f))

/-- Helper for Lemma 15.118.2: localizing the dual module identifies it with the dual of the
away-localized module. -/
noncomputable def localized_dual_equiv (f : R) [Module.FinitePresentation R M] :
    LocalizedModule.Away f (Module.Dual R M) ≃ₗ[R]
      ((LocalizedModule.Away f M) →ₗ[Localization.Away f] Localization.Away f) :=
  (Module.FinitePresentation.linearEquivMapExtendScalars
      (M := M) (N := R) (Submonoid.powers f)).trans
    (LinearEquiv.restrictScalars R <|
      (LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)
        (localized_contractLeft_target_equiv (R := R) f)).congrRight)

/-- Helper for Lemma 15.118.2: localizing `Mᵛ ⊗ M` identifies it with the source of the local
contraction pairing. -/
noncomputable def localized_contractLeft_source_equiv (f : R) [Module.FinitePresentation R M] :
    LocalizedModule.Away f (TensorProduct R (Module.Dual R M) M) ≃ₗ[R]
      TensorProduct (Localization.Away f)
        (((LocalizedModule.Away f M) →ₗ[Localization.Away f] Localization.Away f))
        (LocalizedModule.Away f M) :=
  (IsLocalizedModule.linearEquiv (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) (TensorProduct R (Module.Dual R M) M))
      (TensorProduct.map
        (LocalizedModule.mkLinearMap (Submonoid.powers f) (Module.Dual R M))
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M))).trans <|
    (localized_dual_equiv (R := R) (M := M) f).rTensor (LocalizedModule.Away f M) |>.trans <|
      (LinearEquiv.restrictScalars R <|
        (IsLocalization.moduleTensorEquiv (Submonoid.powers f) (Localization.Away f)
          ((LocalizedModule.Away f M) →ₗ[Localization.Away f] Localization.Away f)
          (LocalizedModule.Away f M)).symm)

/-- Helper for Lemma 15.118.2: a rank-one trivialization over `R_f` makes `M_f` invertible. -/
lemma away_invertible_of_rank_one_trivialization (f : R)
    (e : LocalizedModule.Away f M ≃ₗ[Localization.Away f] (Fin 1 → Localization.Away f)) :
    Module.Invertible (Localization.Away f) (LocalizedModule.Away f M) := by
  -- Replace the standard free rank-one module by the ring itself.
  let e' := e.trans (LinearEquiv.funUnique (Fin 1) (Localization.Away f) (Localization.Away f))
  -- Transport the canonical invertible structure on the ring module along this equivalence.
  letI : Module.Invertible (Localization.Away f) (Localization.Away f) := inferInstance
  exact Module.Invertible.congr (M := Localization.Away f) (N := LocalizedModule.Away f M) e'.symm

/-- Helper for Lemma 15.118.2: after a rank-one trivialization, the local contraction map is
bijective. -/
lemma local_contractLeft_bijective_of_rank_one_trivialization (f : R)
    (e : LocalizedModule.Away f M ≃ₗ[Localization.Away f] (Fin 1 → Localization.Away f)) :
    Function.Bijective
      (contractLeft (Localization.Away f) (LocalizedModule.Away f M)) := by
  -- The local invertibility statement is the owner predicate for bijectivity of `contractLeft`.
  letI : Module.Invertible (Localization.Away f) (LocalizedModule.Away f M) :=
    away_invertible_of_rank_one_trivialization (M := M) f e
  simpa using (Module.Invertible.bijective (R := Localization.Away f)
    (M := LocalizedModule.Away f M))

/-- Helper for Lemma 15.118.2: the localized target equivalence sends `mk r 1` to the obvious
localization class of `r`. -/
lemma localized_contractLeft_target_equiv_apply_mk_one (f : R) (r : R) :
    (localized_contractLeft_target_equiv (R := R) f) (LocalizedModule.mk r 1) =
      Localization.mk r (1 : Submonoid.powers f) := by
  -- The target equivalence is the canonical identification between the localized ring module and
  -- the localization ring itself, so on denominator `1` it is definitional.
  simpa [localized_contractLeft_target_equiv] using
    (IsLocalizedModule.linearEquiv_apply (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) R)
      (Algebra.linearMap R (Localization.Away f)) r)

/-- Helper for Lemma 15.118.2: evaluating the codomain transport on `mk m 1` simply applies the
localized target equivalence after the localized linear form itself. -/
lemma extendScalars_congrRight_eval_on_mk_one (f : R)
    (ψ : LocalizedModule.Away f M →ₗ[Localization.Away f] LocalizedModule.Away f R) (m : M) :
    ((LinearEquiv.restrictScalars R <|
        (LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)
          (localized_contractLeft_target_equiv (R := R) f)).congrRight) ψ)
      (LocalizedModule.mk m 1) =
      (localized_contractLeft_target_equiv (R := R) f) (ψ (LocalizedModule.mk m 1)) := by
  -- Evaluate the codomain transport on the chosen localized generator before comparing scalar
  -- values.
  rw [LinearEquiv.restrictScalars_apply]
  change (LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)
      (localized_contractLeft_target_equiv (R := R) f)) (ψ (LocalizedModule.mk m 1)) = _
  rw [LinearEquiv.extendScalarsOfIsLocalization_apply]

/-- Helper for Lemma 15.118.2: on a localized pure tensor generator, the two candidate
descriptions of the localized contraction map agree. -/
lemma localized_dual_equiv_apply_mk_apply_mk (f : R)
    [Module.FinitePresentation R M] (φ : Module.Dual R M) (m : M) :
    ((localized_dual_equiv (R := R) (M := M) f) (LocalizedModule.mk φ 1))
      (LocalizedModule.mk m 1) = Localization.mk (φ m) (1 : Submonoid.powers f) := by
  -- Evaluate the localized dual equivalence on denominator-`1` generators before any tensor
  -- bookkeeping, so the remaining comparison reduces to the explicit scalar `φ m`.
  rw [localized_dual_equiv, LinearEquiv.trans_apply]
  rw [show (Module.FinitePresentation.linearEquivMapExtendScalars (Submonoid.powers f))
      (LocalizedModule.mk φ 1) =
      (IsLocalizedModule.mapExtendScalars (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) R)
        (Localization.Away f)) φ by
      simpa using Module.FinitePresentation.linearEquivMapExtendScalars_apply
        (S := Submonoid.powers f) (f := φ)]
  rw [extendScalars_congrRight_eval_on_mk_one (R := R) (M := M) f
    ((IsLocalizedModule.mapExtendScalars (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) R)
      (Localization.Away f)) φ) m]
  have hmap :
      ((IsLocalizedModule.mapExtendScalars (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) R)
          (Localization.Away f)) φ)
        (LocalizedModule.mk m 1) = LocalizedModule.mk (φ m) 1 := by
    -- Compare the localized evaluation map with the numerator map on the source generator `m`.
    change ((LinearMap.restrictScalars R
        ((IsLocalizedModule.mapExtendScalars (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) R)
          (Localization.Away f)) φ))
        (LocalizedModule.mk m 1)) = _
    simpa using
      LinearMap.congr_fun
        (IsLocalizedModule.map_comp (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) R) φ)
        m
  rw [hmap]
  simpa using localized_contractLeft_target_equiv_apply_mk_one (R := R) f (φ m)

/-- Helper for Lemma 15.118.2: the first source-side localization equivalence sends
`mk (φ ⊗ m) 1` to the tensor of the denominator-`1` localized factors. -/
lemma localized_tensor_linearEquiv_apply_mk_tmul_one (f : R)
    [Module.FinitePresentation R M] (φ : Module.Dual R M) (m : M) :
    (IsLocalizedModule.linearEquiv (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) (TensorProduct R (Module.Dual R M) M))
        (TensorProduct.map
          (LocalizedModule.mkLinearMap (Submonoid.powers f) (Module.Dual R M))
          (LocalizedModule.mkLinearMap (Submonoid.powers f) M)))
      (LocalizedModule.mk (φ ⊗ₜ[R] m) 1) =
        (LocalizedModule.mk φ 1) ⊗ₜ[R] (LocalizedModule.mk m 1) := by
  -- The first localization comparison is the canonical tensor map on the numerator `φ ⊗ₜ m`.
  simpa using
    (IsLocalizedModule.linearEquiv_apply (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) (TensorProduct R (Module.Dual R M) M))
      (TensorProduct.map
        (LocalizedModule.mkLinearMap (Submonoid.powers f) (Module.Dual R M))
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M))
      (φ ⊗ₜ[R] m))

/-- Helper for Lemma 15.118.2: the localized source equivalence sends a denominator-`1` pure
tensor to the corresponding pure tensor of localized factors. -/
lemma localized_contractLeft_source_equiv_apply_mk_tmul (f : R)
    [Module.FinitePresentation R M] (φ : Module.Dual R M) (m : M) :
    (localized_contractLeft_source_equiv (R := R) (M := M) f)
      (LocalizedModule.mk (φ ⊗ₜ[R] m) 1) =
        ((localized_dual_equiv (R := R) (M := M) f) (LocalizedModule.mk φ 1)) ⊗ₜ[Localization.Away f]
          (LocalizedModule.mk m 1) := by
  -- Normalize the localization/tensor transports only on the pure tensor `φ ⊗ₜ m`, matching the
  -- source proof's denominator-`1` computation before any later extension step.
  rw [localized_contractLeft_source_equiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply]
  rw [localized_tensor_linearEquiv_apply_mk_tmul_one (R := R) (M := M) f φ m]
  rw [LinearEquiv.rTensor_tmul]
  rfl

/-- Helper for Lemma 15.118.2: on denominator-`1` pure tensors, the localized global contraction
map matches the local contraction pairing. -/
lemma localized_contractLeft_eq_local_contractLeft_tmul (f : R)
    [Module.FinitePresentation R M] (φ : Module.Dual R M) (m : M) :
    (localized_contractLeft_target_equiv (R := R) f)
        (((LocalizedModule.map (Submonoid.powers f) (contractLeft R M))
          (LocalizedModule.mk (φ ⊗ₜ[R] m) 1))) =
      (LinearMap.restrictScalars R
        (contractLeft (Localization.Away f) (LocalizedModule.Away f M)))
        ((localized_contractLeft_source_equiv (R := R) (M := M) f)
          (LocalizedModule.mk (φ ⊗ₜ[R] m) 1)) := by
  -- Route correction: instead of transporting arbitrary denominators through every equivalence,
  -- first compute both composites on the denominator-`1` generator `mk (φ ⊗ₜ m) 1`.
  calc
    (localized_contractLeft_target_equiv (R := R) f)
        (((LocalizedModule.map (Submonoid.powers f) (contractLeft R M))
          (LocalizedModule.mk (φ ⊗ₜ[R] m) 1)))
        = Localization.mk (φ m) (1 : Submonoid.powers f) := by
            -- The localized global contraction map sends `φ ⊗ₜ m` to the localized scalar `φ m`.
            rw [LocalizedModule.map_mk, contractLeft_apply]
            simpa using localized_contractLeft_target_equiv_apply_mk_one (R := R) f (φ m)
    _ = (LinearMap.restrictScalars R
          (contractLeft (Localization.Away f) (LocalizedModule.Away f M)))
          ((localized_contractLeft_source_equiv (R := R) (M := M) f)
            (LocalizedModule.mk (φ ⊗ₜ[R] m) 1)) := by
            -- The local contraction pairing on the normalized source pure tensor yields the same
            -- localized scalar, using the evaluated dual-localization formula above.
            rw [localized_contractLeft_source_equiv_apply_mk_tmul (R := R) (M := M) f φ m]
            simp [localized_dual_equiv_apply_mk_apply_mk]

/-- Helper for Lemma 15.118.2: on denominator-`1` localized tensors, the localized global
contraction map agrees with the local contraction map. -/
lemma localized_contractLeft_eq_local_contractLeft_mk_one (f : R)
    [Module.FinitePresentation R M] (x : TensorProduct R (Module.Dual R M) M) :
    (localized_contractLeft_target_equiv (R := R) f)
        (((LocalizedModule.map (Submonoid.powers f) (contractLeft R M))
          (LocalizedModule.mk x 1))) =
      (LinearMap.restrictScalars R
        (contractLeft (Localization.Away f) (LocalizedModule.Away f M)))
        ((localized_contractLeft_source_equiv (R := R) (M := M) f)
          (LocalizedModule.mk x 1)) := by
  -- Extend the pure-tensor comparison across the whole tensor product before dealing with any
  -- localization denominator transport.
  let F :
      LocalizedModule.Away f (TensorProduct R (Module.Dual R M) M) →ₗ[R] Localization.Away f :=
    (localized_contractLeft_target_equiv (R := R) f).toLinearMap.comp
      (LinearMap.restrictScalars R
        (LocalizedModule.map (Submonoid.powers f) (contractLeft R M)))
  let G :
      LocalizedModule.Away f (TensorProduct R (Module.Dual R M) M) →ₗ[R] Localization.Away f :=
    (LinearMap.restrictScalars R
      (contractLeft (Localization.Away f) (LocalizedModule.Away f M))).comp
        (localized_contractLeft_source_equiv (R := R) (M := M) f).toLinearMap
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- Both comparison maps are linear, so the zero tensor is immediate.
    have hmk_zero :
        LocalizedModule.mk (0 : TensorProduct R (Module.Dual R M) M) (1 : Submonoid.powers f) = 0 := by
      simp
    calc
      F (LocalizedModule.mk (0 : TensorProduct R (Module.Dual R M) M) 1) = F 0 := by
        rw [hmk_zero]
      _ = 0 := by
        rw [F.map_zero]
      _ = G 0 := by
        rw [G.map_zero]
      _ = G (LocalizedModule.mk (0 : TensorProduct R (Module.Dual R M) M) 1) := by
        rw [hmk_zero]
  · intro φ m
    -- The pure-tensor case is exactly the denominator-`1` computation already established.
    simpa [F, G, LinearMap.comp_apply] using
      localized_contractLeft_eq_local_contractLeft_tmul (R := R) (M := M) f φ m
  · intro x y hx hy
    -- Rewrite the denominator-`1` localization class of `x + y` as a sum, then use linearity of
    -- the two comparison maps.
    have hmk :
        LocalizedModule.mk (x + y) (1 : Submonoid.powers f) =
          LocalizedModule.mk x (1 : Submonoid.powers f) +
            LocalizedModule.mk y (1 : Submonoid.powers f) := by
      simpa only [one_smul, one_mul] using
        (LocalizedModule.mk_add_mk (m1 := x) (m2 := y)
          (s1 := (1 : Submonoid.powers f)) (s2 := (1 : Submonoid.powers f))).symm
    have hx' : F (LocalizedModule.mk x 1) = G (LocalizedModule.mk x 1) := by
      simpa [F, G, LinearMap.comp_apply] using hx
    have hy' : F (LocalizedModule.mk y 1) = G (LocalizedModule.mk y 1) := by
      simpa [F, G, LinearMap.comp_apply] using hy
    have hFadd :
        F (LocalizedModule.mk x 1 + LocalizedModule.mk y 1) =
          F (LocalizedModule.mk x 1) + F (LocalizedModule.mk y 1) := by
      simpa using F.map_add (LocalizedModule.mk x 1) (LocalizedModule.mk y 1)
    have hGadd :
        G (LocalizedModule.mk x 1 + LocalizedModule.mk y 1) =
          G (LocalizedModule.mk x 1) + G (LocalizedModule.mk y 1) := by
      simpa using G.map_add (LocalizedModule.mk x 1) (LocalizedModule.mk y 1)
    calc
      F (LocalizedModule.mk (x + y) 1) =
          F (LocalizedModule.mk x 1 + LocalizedModule.mk y 1) := by rw [hmk]
      _ = F (LocalizedModule.mk x 1) + F (LocalizedModule.mk y 1) := hFadd
      _ = G (LocalizedModule.mk x 1) + G (LocalizedModule.mk y 1) := by rw [hx', hy']
      _ = G (LocalizedModule.mk x 1 + LocalizedModule.mk y 1) := hGadd.symm
      _ = G (LocalizedModule.mk (x + y) 1) := by rw [hmk]

/-- Helper for Lemma 15.118.2: the localized global contraction map and the local contraction map
agree on every localized generator. -/
lemma localized_contractLeft_eq_local_contractLeft_mk (f : R)
    [Module.FinitePresentation R M] (x : TensorProduct R (Module.Dual R M) M)
    (s : Submonoid.powers f) :
    (localized_contractLeft_target_equiv (R := R) f)
        (((LocalizedModule.map (Submonoid.powers f) (contractLeft R M))
          (LocalizedModule.mk x s))) =
      (LinearMap.restrictScalars R
        (contractLeft (Localization.Away f) (LocalizedModule.Away f M)))
        ((localized_contractLeft_source_equiv (R := R) (M := M) f)
          (LocalizedModule.mk x s)) := by
  -- Route correction: prove the underlying map equality first from the denominator-`1` tensor
  -- computation, then evaluate that map equality on the chosen localized generator.
  let F :
      LocalizedModule.Away f (TensorProduct R (Module.Dual R M) M) →ₗ[R] Localization.Away f :=
    (localized_contractLeft_target_equiv (R := R) f).toLinearMap.comp
      (LinearMap.restrictScalars R
        (LocalizedModule.map (Submonoid.powers f) (contractLeft R M)))
  let G :
      LocalizedModule.Away f (TensorProduct R (Module.Dual R M) M) →ₗ[R] Localization.Away f :=
    (LinearMap.restrictScalars R
      (contractLeft (Localization.Away f) (LocalizedModule.Away f M))).comp
        (localized_contractLeft_source_equiv (R := R) (M := M) f).toLinearMap
  have hcompare : F = G := by
    -- The universal property of localization reduces equality of maps out of the localized tensor
    -- product to the denominator-`1` numerator images.
    apply IsLocalizedModule.linearMap_ext (S := Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f)
        (TensorProduct R (Module.Dual R M) M))
      (Algebra.linearMap R (Localization.Away f))
    exact LinearMap.ext fun y ↦ by
      simpa [F, G, LinearMap.comp_apply] using
        localized_contractLeft_eq_local_contractLeft_mk_one (R := R) (M := M) f y
  simpa [F, G, LinearMap.comp_apply] using
    congrArg (fun k => k (LocalizedModule.mk x s)) hcompare

/-- Helper for Lemma 15.118.2: after localizing, the global contraction map is conjugate to the
local contraction map over `R_f`. -/
lemma localized_contractLeft_eq_local_contractLeft (f : R) [Module.FinitePresentation R M] :
    (localized_contractLeft_target_equiv (R := R) f).toLinearMap.comp
        (LinearMap.restrictScalars R
          (LocalizedModule.map (Submonoid.powers f) (contractLeft R M))) =
      (LinearMap.restrictScalars R
        (contractLeft (Localization.Away f) (LocalizedModule.Away f M))).comp
        (localized_contractLeft_source_equiv (R := R) (M := M) f).toLinearMap := by
  -- The universal property of localization reduces the map equality to the denominator-`1`
  -- tensor computations already established.
  apply IsLocalizedModule.linearMap_ext (S := Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f)
      (TensorProduct R (Module.Dual R M) M))
    (Algebra.linearMap R (Localization.Away f))
  exact LinearMap.ext fun x ↦ by
    simpa [LinearMap.comp_apply] using
      localized_contractLeft_eq_local_contractLeft_mk_one (R := R) (M := M) f x

/-- Helper for Lemma 15.118.2: a rank-one trivialization over `R_f` makes the localized global
contraction map bijective. -/
lemma localized_map_contractLeft_bijective_of_rank_one_trivialization (f : R)
    [Module.FinitePresentation R M]
    (e : LocalizedModule.Away f M ≃ₗ[Localization.Away f] (Fin 1 → Localization.Away f)) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers f) (contractLeft R M)) := by
  let eSource := localized_contractLeft_source_equiv (R := R) (M := M) f
  let eTarget := localized_contractLeft_target_equiv (R := R) f
  have hcompare := localized_contractLeft_eq_local_contractLeft (R := R) (M := M) f
  have hlocal :
      Function.Bijective
        (LinearMap.restrictScalars R
          (contractLeft (Localization.Away f) (LocalizedModule.Away f M))) := by
    -- The rank-one trivialization identifies the local contraction map with the canonical one.
    simpa using
      local_contractLeft_bijective_of_rank_one_trivialization (M := M) f e
  constructor
  · intro x y hxy
    -- Apply the conjugation relation on both inputs and use injectivity of the local map.
    have hx :
        eTarget (((LocalizedModule.map (Submonoid.powers f) (contractLeft R M)) x)) =
          (LinearMap.restrictScalars R
            (contractLeft (Localization.Away f) (LocalizedModule.Away f M))) (eSource x) := by
      simpa [eSource, eTarget, LinearMap.comp_apply] using
        congrArg (fun k => k x) hcompare
    have hy :
        eTarget (((LocalizedModule.map (Submonoid.powers f) (contractLeft R M)) y)) =
          (LinearMap.restrictScalars R
            (contractLeft (Localization.Away f) (LocalizedModule.Away f M))) (eSource y) := by
      simpa [eSource, eTarget, LinearMap.comp_apply] using
        congrArg (fun k => k y) hcompare
    have hxy' : eSource x = eSource y := by
      apply hlocal.injective
      calc
        (LinearMap.restrictScalars R
            (contractLeft (Localization.Away f) (LocalizedModule.Away f M))) (eSource x)
            = eTarget (((LocalizedModule.map (Submonoid.powers f) (contractLeft R M)) x)) := hx.symm
        _ = eTarget (((LocalizedModule.map (Submonoid.powers f) (contractLeft R M)) y)) := by
            simp [hxy]
        _ = (LinearMap.restrictScalars R
            (contractLeft (Localization.Away f) (LocalizedModule.Away f M))) (eSource y) := hy
    exact eSource.injective hxy'
  · intro z
    -- Pull back a local preimage through the source equivalence and compare via the target one.
    obtain ⟨w, hw⟩ := hlocal.surjective (eTarget z)
    refine ⟨eSource.symm w, ?_⟩
    apply eTarget.injective
    calc
      eTarget
          (((LocalizedModule.map (Submonoid.powers f) (contractLeft R M)) (eSource.symm w))) =
        (LinearMap.restrictScalars R
          (contractLeft (Localization.Away f) (LocalizedModule.Away f M)))
          (eSource (eSource.symm w)) := by
            simpa [eSource, eTarget, LinearMap.comp_apply] using
              congrArg (fun k => k (eSource.symm w)) hcompare
      _ = eTarget z := by simp [hw]

/-- Helper for Lemma 15.118.2: a finite locally free module of rank `1` is invertible. -/
theorem moduleInvertible_of_finiteLocallyFreeOfRank_one [Module.FiniteLocallyFreeOfRank R M 1] :
    Module.Invertible R M := by
  -- Route correction: the remaining step is the source-faithful localization argument for
  -- `contractLeft`; the scaffolding above isolates the comparison maps already.
  letI : Module.FinitePresentation R M :=
    finitePresentation_of_finiteLocallyFreeOfRank_one (R := R) (M := M)
  obtain ⟨s, hs_span, hs_triv⟩ :=
    Module.FiniteLocallyFreeOfRank.exists_standardOpen_cover (R := R) (M := M) (r := 1)
  have hbij : Function.Bijective (contractLeft R M) := by
    -- The global contraction map is bijective because it is so after localizing on a spanning
    -- standard-open cover where `M` becomes free of rank `1`.
    apply bijective_of_localized_span s hs_span (contractLeft R M)
    intro f
    rcases hs_triv f f.property with ⟨e⟩
    simpa using
      localized_map_contractLeft_bijective_of_rank_one_trivialization
        (R := R) (M := M) f.1 e
  exact ⟨hbij⟩

/- Domain-style sampling for Lemma 15.118.2:
- primary domain: invertible modules and rank-one finite local freeness in `ModuleCat R`;
- sampled owner declarations:
  `Module.FiniteLocallyFreeOfRank R M 1`,
  `(tensorLeft M).IsEquivalence`,
  `tensorLeft_isEquivalence_iff_moduleInvertible`,
  `Module.Invertible.left`,
  `tensorLeft_isEquivalence_iff_exists_tensor_inverse`;
- best owner abstraction: the chapter-wide tensor-left equivalence owner `(tensorLeft M).IsEquivalence`;
- primitive vs. derived:
  the source-facing primitive clauses are rank-one finite local freeness and the one-sided
  tensor-unit witness `∃ N, M ⊗ N ≅ 𝟙`, while the chapter owner `(tensorLeft M).IsEquivalence`
  is the canonical core abstraction tying them together; the specialized predicate
  `Module.Invertible R M` and the two-sided tensor-inverse criterion are derived bridge/view API.

Source/core/bridge triage:
- `source-facing`: the rank-one finite-locally-free / invertible / tensor-inverse TFAE;
- `core/canonical`: `(tensorLeft M).IsEquivalence`;
- `bridge/view`: the module-specific predicate `Module.Invertible R M`, the passage from the
  one-sided tensor-unit witness to invertibility via `Module.Invertible.left`, and the Chapter
  `4` two-sided tensor-inverse comparison
  `tensorLeft_isEquivalence_iff_exists_tensor_inverse`.

Definition `15.118.1` already identifies the specialized mathlib predicate `Module.Invertible R M`
with the chapter owner `(tensorLeft M).IsEquivalence`, so the present source-facing TFAE keeps the
chapter owner itself and the genuinely source-facing one-sided tensor-unit condition. -/

-- Proof sketch: if `M` is finite locally free of rank `1`, take the dual module
-- `Module.Dual R M`; the evaluation pairing becomes an isomorphism after localizing on any open
-- where `M` is free of rank `1`, and Lemma `10.23.2` descends that isomorphism globally. If
-- `M ⊗ N ≅ R`, first promote that one-sided tensor-unit witness to `Module.Invertible R M` via
-- `Module.Invertible.left`, then use Definition `15.118.1` to reach the chapter owner
-- `(tensorLeft M).IsEquivalence`. Conversely, if `tensorLeft M` is an equivalence, apply the
-- Chapter `4` owner theorem `tensorLeft_isEquivalence_iff_exists_tensor_inverse` to obtain a
-- two-sided tensor inverse and then forget the second isomorphism; the resulting local tensor
-- trivializations recover finite local freeness of rank `1` by the finite-projective local
-- criterion.
/-- Lemma 15.118.2: for an `R`-module `M`, the following are equivalent: `M` is finite locally
free of rank `1`; tensoring on the left by `M` is an equivalence of `ModuleCat R`; and there
exists an `R`-module `N` such that `M ⊗ N` is isomorphic to the tensor unit in `ModuleCat R`.
The specialized predicate `Module.Invertible R M` remains only a bridge from
Definition `15.118.1`, while the public statement keeps the chapter owner
`(tensorLeft M).IsEquivalence` and the source-facing one-sided tensor-unit witness. -/
theorem invertible_tfae_finiteLocallyFreeOfRank_one_and_tensor_unit :
    List.TFAE
      [ Module.FiniteLocallyFreeOfRank R M 1
      , (tensorLeft M).IsEquivalence
      , ∃ N : ModuleCat R, Nonempty (M ⊗ N ≅ 𝟙_ _)
      ] := by
  let h12 : Module.FiniteLocallyFreeOfRank R M 1 → (tensorLeft M).IsEquivalence := fun hM ↦ by
    -- Route correction: the forward direction is isolated through the dedicated helper theorem.
    letI : Module.FiniteLocallyFreeOfRank R M 1 := hM
    exact (tensorLeft_isEquivalence_iff_moduleInvertible M).2
      (moduleInvertible_of_finiteLocallyFreeOfRank_one (M := M))
  let h21 : (tensorLeft M).IsEquivalence → Module.FiniteLocallyFreeOfRank R M 1 := fun hM ↦ by
    -- The backward direction uses the invertible-module bridge and the basic-open rank-one cover.
    letI : Module.Invertible R M := (tensorLeft_isEquivalence_iff_moduleInvertible M).1 hM
    exact finiteLocallyFreeOfRank_one_of_moduleInvertible (M := M)
  let h23 : (tensorLeft M).IsEquivalence →
      ∃ N : ModuleCat R, Nonempty (M ⊗ N ≅ 𝟙_ _) :=
    (tensor_unit_iff_tensorLeft_isEquivalence (M := M)).mpr
  let h32 : (∃ N : ModuleCat R, Nonempty (M ⊗ N ≅ 𝟙_ _)) → (tensorLeft M).IsEquivalence :=
    (tensor_unit_iff_tensorLeft_isEquivalence (M := M)).mp
  intro x hx y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl
  · rcases hy with rfl | rfl | rfl
    · exact Iff.rfl
    · exact ⟨h12, h21⟩
    · exact ⟨fun h ↦ h23 (h12 h), fun h ↦ h21 (h32 h)⟩
  · rcases hy with rfl | rfl | rfl
    · exact ⟨h21, h12⟩
    · exact Iff.rfl
    · exact ⟨h23, h32⟩
  · rcases hy with rfl | rfl | rfl
    · exact ⟨fun h ↦ h21 (h32 h), fun h ↦ h23 (h12 h)⟩
    · exact ⟨h32, h23⟩
    · exact Iff.rfl

end

end ModuleCat
