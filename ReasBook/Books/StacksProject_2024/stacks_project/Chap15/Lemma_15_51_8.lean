import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_43_9
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_51_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_51_6
import StacksProject_2024.stacks_project.Chap15.Lemma_15_51_7
import StacksProject_2024.stacks_project.Chap15.Proposition_15_49_2

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open RingPairCat

universe u

section

variable (P : FieldAlgebraProperty)
variable [P.HasPropertyB]
variable [FieldAlgebraProperty.HasPropertyC P] [FieldAlgebraProperty.HasPropertyD P]
variable [P.HasPropertyE]

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-- Helper for Lemma 15.51.8: the canonical pair henselization exists as the right adjoint from
Lemma `15.12.1`. -/
local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

/-- Helper for Lemma 15.51.8: any chosen henselization of a local ring is canonically equivalent
to the owner pair henselization at the maximal ideal. -/
lemma chosen_henselization_equiv_pair_henselization :
    Rh ≃ₐ[R] henselizationRing (pairOfIdeal (maximalIdeal R)) := by
  let _ : IsScalarTower R R Rh := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower R R (henselizationRing (pairOfIdeal (maximalIdeal R))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let f : Rh →ₐ[R] henselizationRing (pairOfIdeal (maximalIdeal R)) :=
    henselizationMap (R := R) (S := R) (Rh := Rh)
      (Sh := henselizationRing (pairOfIdeal (maximalIdeal R)))
  let g : henselizationRing (pairOfIdeal (maximalIdeal R)) →ₐ[R] Rh :=
    henselizationMap (R := R) (S := R)
      (Rh := henselizationRing (pairOfIdeal (maximalIdeal R))) (Sh := Rh)
  have hf_local : IsLocalHom (f : Rh →+* henselizationRing (pairOfIdeal (maximalIdeal R))) := by
    -- The canonical map between henselizations is local.
    simpa [f] using
      (henselizationMap_isLocalHom (R := R) (S := R) (Rh := Rh)
        (Sh := henselizationRing (pairOfIdeal (maximalIdeal R))) :
        IsLocalHom ((henselizationMap (R := R) (S := R) (Rh := Rh)
          (Sh := henselizationRing (pairOfIdeal (maximalIdeal R))) :
          Rh →ₐ[R] henselizationRing (pairOfIdeal (maximalIdeal R))).toRingHom))
  have hg_local :
      IsLocalHom (g : henselizationRing (pairOfIdeal (maximalIdeal R)) →+* Rh) := by
    -- The reverse canonical comparison is local as well.
    simpa [g] using
      (henselizationMap_isLocalHom (R := R) (S := R)
        (Rh := henselizationRing (pairOfIdeal (maximalIdeal R))) (Sh := Rh) :
        IsLocalHom ((henselizationMap (R := R) (S := R)
          (Rh := henselizationRing (pairOfIdeal (maximalIdeal R))) (Sh := Rh) :
          henselizationRing (pairOfIdeal (maximalIdeal R)) →ₐ[R] Rh).toRingHom))
  have hgf_local : IsLocalHom ((g.comp f : Rh →ₐ[R] Rh).toRingHom) := by
    -- Composites of local maps are local.
    let _ : IsLocalHom (f : Rh →+* henselizationRing (pairOfIdeal (maximalIdeal R))) := hf_local
    let _ : IsLocalHom (g : henselizationRing (pairOfIdeal (maximalIdeal R)) →+* Rh) := hg_local
    simpa [f, g] using
      (RingHom.isLocalHom_comp
        (g : henselizationRing (pairOfIdeal (maximalIdeal R)) →+* Rh)
        (f : Rh →+* henselizationRing (pairOfIdeal (maximalIdeal R))) :
        IsLocalHom
          ((g : henselizationRing (pairOfIdeal (maximalIdeal R)) →+* Rh).comp
            (f : Rh →+* henselizationRing (pairOfIdeal (maximalIdeal R)))))
  have hfg_local :
      IsLocalHom
        ((f.comp g : henselizationRing (pairOfIdeal (maximalIdeal R)) →ₐ[R]
          henselizationRing (pairOfIdeal (maximalIdeal R))).toRingHom) := by
    -- The same argument works in the opposite direction.
    let _ : IsLocalHom (f : Rh →+* henselizationRing (pairOfIdeal (maximalIdeal R))) := hf_local
    let _ : IsLocalHom (g : henselizationRing (pairOfIdeal (maximalIdeal R)) →+* Rh) := hg_local
    simpa [f, g] using
      (RingHom.isLocalHom_comp
        (f : Rh →+* henselizationRing (pairOfIdeal (maximalIdeal R)))
        (g : henselizationRing (pairOfIdeal (maximalIdeal R)) →+* Rh) :
        IsLocalHom
          ((f : Rh →+* henselizationRing (pairOfIdeal (maximalIdeal R))).comp
            (g : henselizationRing (pairOfIdeal (maximalIdeal R)) →+* Rh)))
  have hgf :
      g.comp f = AlgHom.id R Rh := by
    -- Uniqueness in the henselization universal property forces the endomorphism to be the identity.
    rcases
        existsUnique_algHom_between_henselizations_of_localHom
          (R := R) (S := R) (Rh := Rh) (Sh := Rh) with
      ⟨φ, hφ_local, hφ_unique⟩
    have hid_local : IsLocalHom (((AlgHom.id R Rh : Rh →ₐ[R] Rh) : Rh →+* Rh)) := by
      simpa using (show IsLocalHom (algebraMap Rh Rh) by infer_instance)
    calc
      g.comp f = φ := hφ_unique (g.comp f) hgf_local
      _ = AlgHom.id R Rh := (hφ_unique (AlgHom.id R Rh) hid_local).symm
  have hfg :
      f.comp g = AlgHom.id R (henselizationRing (pairOfIdeal (maximalIdeal R))) := by
    -- The same uniqueness argument applies to the owner henselization.
    rcases
        existsUnique_algHom_between_henselizations_of_localHom
          (R := R) (S := R)
          (Rh := henselizationRing (pairOfIdeal (maximalIdeal R)))
          (Sh := henselizationRing (pairOfIdeal (maximalIdeal R))) with
      ⟨φ, hφ_local, hφ_unique⟩
    have hid_local :
        IsLocalHom
          (((AlgHom.id R (henselizationRing (pairOfIdeal (maximalIdeal R))) :
            henselizationRing (pairOfIdeal (maximalIdeal R)) →ₐ[R]
              henselizationRing (pairOfIdeal (maximalIdeal R))) :
            henselizationRing (pairOfIdeal (maximalIdeal R)) →+*
              henselizationRing (pairOfIdeal (maximalIdeal R)))) := by
      simpa using
        (show IsLocalHom
            (algebraMap
              (henselizationRing (pairOfIdeal (maximalIdeal R)))
              (henselizationRing (pairOfIdeal (maximalIdeal R)))) by
          infer_instance)
    calc
      f.comp g = φ := hφ_unique (f.comp g) hfg_local
      _ = AlgHom.id R (henselizationRing (pairOfIdeal (maximalIdeal R))) :=
        (hφ_unique (AlgHom.id R (henselizationRing (pairOfIdeal (maximalIdeal R))))
          hid_local).symm
  have hf_injective : Function.Injective f := by
    -- A left inverse gives injectivity.
    intro x y hxy
    calc
      x = g (f x) := by
        symm
        exact DFunLike.congr_fun hgf x
      _ = g (f y) := by rw [hxy]
      _ = y := DFunLike.congr_fun hgf y
  have hf_surjective : Function.Surjective f := by
    -- A right inverse gives surjectivity.
    intro y
    refine ⟨g y, ?_⟩
    exact DFunLike.congr_fun hfg y
  -- Package the inverse maps into the canonical algebra equivalence.
  exact AlgEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩

/-- Helper for Lemma 15.51.8: localizing a product of branch fibers at the prime coming from one
coordinate recovers the localization of that chosen coordinate factor. -/
noncomputable lemma localizationAtPrime_mapPiEval_ringEquiv
    {ι : Type u} [Finite ι] {S : ι → Type u} [∀ i, CommRing (S i)]
    (i : ι) (Q : PrimeSpectrum (S i)) :
    Localization.AtPrime (Ideal.comap (Pi.evalRingHom S i) Q.asIdeal) ≃+*
      Localization.AtPrime Q.asIdeal := by
  -- Proof comment: the localization map induced by evaluation at the chosen coordinate is
  -- bijective, so the resulting local rings are canonically isomorphic.
  simpa [PrimeSpectrum.comap_asIdeal] using
    (RingEquiv.ofBijective
      (Localization.AtPrime.mapPiEvalRingHom Q.asIdeal)
      (Localization.AtPrime.mapPiEvalRingHom_bijective Q.asIdeal) :
        Localization.AtPrime (Ideal.comap (Pi.evalRingHom S i) Q.asIdeal) ≃+*
          Localization.AtPrime Q.asIdeal)

/-- Helper for Lemma 15.51.8: once property `P` holds on the completed `κ(p)`-fiber, the source
proof isolates any chosen branch over `p` after the strict/henselian finite product split. -/
lemma completionFiber_branch_hasProperty_of_primesOver_split
    {B : Type u} [CommRing B] [IsLocalRing B] [Algebra R B] [IsNoetherianRing B]
    (p : PrimeSpectrum R) (q : p.asIdeal.primesOver B)
    (hbij : Function.Bijective (p.asIdeal.fiberToPiResidueField B))
    (hbase :
      P p.asIdeal.ResidueField
        (p.asIdeal.Fiber (AdicCompletion (maximalIdeal B) B))) :
    P p.asIdeal.ResidueField
      (q.1.asIdeal.Fiber (AdicCompletion (maximalIdeal B) B)) := by
  -- Route correction: the remaining gap is no longer the coordinate-localization step itself.
  -- The new helper `localizationAtPrime_mapPiEval_ringEquiv` already supplies the factor
  -- localization used in the source proof after splitting the completed `κ(p)`-fiber by branches.
  -- TODO: tensor the `fiberToPiResidueField` decomposition with the completion of `B`, transport
  -- property `P` from `hbase` across that completed-fiber/product comparison, and then combine
  -- `(B)` with `localizationAtPrime_mapPiEval_ringEquiv` to reassemble the chosen branch fiber.
  let _ := hbij
  let _ := hbase
  sorry

/-- Helper for Lemma 15.51.8: the formal fibers of a chosen henselization inherit property `P`
from the base local `P`-ring. -/
lemma localFormalFibersHaveProperty_henselization
    (hR : IsPRing P R) :
    LocalFormalFibersHaveProperty P Rh := by
  let _ : IsPRing P R := hR
  let _ : IsNoetherianRing R := hR.toIsNoetherian
  let _ : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  intro q
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R Rh) q
  let qOver : p.asIdeal.primesOver Rh := Ideal.primesOver.mk p.asIdeal q.asIdeal
  let Rhat := AdicCompletion (maximalIdeal R) R
  let Hhat := AdicCompletion (maximalIdeal Rh) Rh
  have hsource :
      ∀ q' : PrimeSpectrum R,
        P q'.asIdeal.ResidueField (q'.asIdeal.Fiber Rhat) := by
    intro q'
    -- Proof comment: the base `P`-ring hypothesis gives every completed fiber of `R`.
    simpa [Rhat] using
      completion_fibers_have_property_of_pRing
        (P := P) (A := R) (I := maximalIdeal R) hR q'
  let eCompletion : Rhat ≃ₐ[R] Hhat :=
    AlgEquiv.ofRingEquiv
      (henselization_completion_equiv (R := R) (Rh := Rh))
      (fun x ↦ by
        -- Proof comment: the completion comparison extends the original map `R → Rh`.
        simpa [Rhat, Hhat, henselization_completion_equiv] using
          DFunLike.congr_fun (maximalIdealCompletionMap_comp (algebraMap R Rh)) x)
  let _ : Algebra Rhat Hhat := eCompletion.toRingHom.toAlgebra
  let _ : IsScalarTower R Rhat Hhat := by
    exact IsScalarTower.of_algebraMap_eq' <| RingHom.ext fun x ↦ by
      change eCompletion ((algebraMap R Rhat) x) = (algebraMap R Hhat) x
      exact eCompletion.commutes x
  let _ : Module.Flat R Rhat := maximalIdeal_completion_flat_of_isNoetherian (S := R)
  let _ : (algebraMap Rhat Hhat).IsRegularRingMap := by
    simpa [RingHom.algebraMap_toAlgebra] using
      (ringEquiv_isRegularRingMap eCompletion.toRingEquiv :
        eCompletion.toRingHom.IsRegularRingMap)
  have hbase :
      P p.asIdeal.ResidueField (p.asIdeal.Fiber Hhat) := by
    -- Proof comment: axiom `(C)` ascends the completed `κ(p)`-fiber across `R^∧ → (R^h)^∧`.
    simpa [Rhat, Hhat] using
      (FieldAlgebraProperty.HasPropertyC.regularAscent
        (P := P) R Rhat Hhat hsource p)
  have hbranch :
      P p.asIdeal.ResidueField (q.asIdeal.Fiber Hhat) := by
    -- Proof comment: isolate the chosen henselization branch over `p` inside the completed fiber.
    simpa [p, qOver, Hhat] using
      completionFiber_branch_hasProperty_of_primesOver_split
        (P := P) (R := R) (B := Rh) p qOver
        (fiberToPiResidueField_henselization_bijective (R := R) (Rh := Rh) p)
        hbase
  have hsep :
      Algebra.IsSeparable p.asIdeal.ResidueField q.asIdeal.ResidueField := by
    simpa [p, qOver] using
      (henselization_residueField_isAlgebraic_and_separable
        (R := R) (Rh := Rh) p qOver).2
  let _ : Algebra.IsSeparable p.asIdeal.ResidueField q.asIdeal.ResidueField := hsep
  -- Proof comment: axiom `(E)` upgrades the ground field from `κ(p)` to `κ(q)`.
  simpa [p] using
    (FieldAlgebraProperty.HasPropertyE.separableBaseChange
      (P := P) p.asIdeal.ResidueField q.asIdeal.ResidueField
      (q.asIdeal.Fiber Hhat) hbranch)

/-- Helper for Lemma 15.51.8: on a Noetherian local ring, the `P`-ring criterion is reduced to
transporting the formal-fiber condition to the closed-point localization. -/
theorem isPRing_of_localFormalFibersHaveProperty_closed_point_support
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (htransport :
      LocalFormalFibersHaveProperty P A →
        LocalFormalFibersHaveProperty P (Localization.AtPrime (maximalIdeal A)))
    (hformal : LocalFormalFibersHaveProperty P A) :
    IsPRing P A := by
  -- Proof comment: Lemma `15.51.4` only asks for maximal localizations, and a local ring has a
  -- unique maximal ideal, so one transport to the closed-point localization is enough.
  rw [isPRing_iff_localFormalFibersHaveProperty_atMaximal]
  intro m
  have hm : m.asIdeal = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal m.isMaximal
  cases m
  cases hm
  simpa using htransport hformal

/-- Helper for Lemma 15.51.8: in a Noetherian local ring, the formal fibers at the closed-point
localization are exactly the original formal fibers indexed by primes below the maximal ideal. -/
lemma localFormalFibersHaveProperty_closed_point_support
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hformal : LocalFormalFibersHaveProperty P A) :
    LocalFormalFibersHaveProperty P (Localization.AtPrime (maximalIdeal A)) := by
  let m : MaximalSpectrum A := ⟨maximalIdeal A, inferInstance⟩
  -- Proof comment: Lemma `15.51.4` reindexes the formal fibers of the closed-point localization
  -- by primes of `A` lying under the maximal ideal.
  rw [localFormalFibersHaveProperty_localizationAtMaximal_iff_primePair
    (P := P) (m := m)]
  intro q hq
  -- Proof comment: in a local ring every prime is contained in the unique maximal ideal, so the
  -- original formal-fiber hypothesis applies directly.
  simpa [LocalFormalFibersHaveProperty] using hformal q

/-- Helper for Lemma 15.51.8: the formal fibers of a strict henselization should transport to the
closed-point localization of that strict henselization. -/
lemma strictHenselization_closedPoint_support
    (hformal : LocalFormalFibersHaveProperty P Rsh) :
    LocalFormalFibersHaveProperty P (Localization.AtPrime (maximalIdeal Rsh)) := by
  let _ : IsNoetherianRing Rsh := isNoetherianRing_strictHenselization R Rsh
  -- Proof comment: this is the local closed-point support lemma specialized to `Rsh`.
  exact
    localFormalFibersHaveProperty_closed_point_support
      (P := P) (A := Rsh) hformal

/-- Helper for Lemma 15.51.8: the completed comparison map `R^∧ → (R^sh)^∧` is regular. -/
lemma strict_henselization_completionMap_regular
    (hR : IsPRing P R) :
    (maximalIdealCompletionMap (algebraMap R Rsh)).IsRegularRingMap := by
  let _ : IsPRing P R := hR
  let _ : IsNoetherianRing R := hR.toIsNoetherian
  let _ : IsNoetherianRing Rsh := isNoetherianRing_strictHenselization R Rsh
  let Rhat := AdicCompletion (maximalIdeal R) R
  let Shat := AdicCompletion (maximalIdeal Rsh) Rsh
  let fhat : Rhat →+* Shat := maximalIdealCompletionMap (algebraMap R Rsh)
  have hcont :
      letI : TopologicalSpace R := Ideal.adicTopology (maximalIdeal R)
      letI : TopologicalSpace Rsh := Ideal.adicTopology (maximalIdeal Rsh)
      Continuous (algebraMap R Rsh) := by
    rw [RingHom.continuous_adic_iff_exists_pow_map_le]
    refine ⟨1, ?_⟩
    have hmap :
        Ideal.map (algebraMap R Rsh) (maximalIdeal R) ≤ maximalIdeal Rsh := by
      rw [Ideal.map_le_iff_le_comap]
      simpa using (show maximalIdeal R ≤ maximalIdeal R by exact le_rfl)
    simpa [pow_one] using hmap
  have hTFAE :
      List.TFAE [
        (algebraMap R Rsh).formally_smooth_for_adic (maximalIdeal Rsh),
        ((algebraMap Rsh Shat).comp (algebraMap R Rsh)).formally_smooth_for_adic
          (Ideal.map (algebraMap Rsh Shat) (maximalIdeal Rsh)),
        fhat.formally_smooth_for_adic
          (Ideal.map (algebraMap Rsh Shat) (maximalIdeal Rsh))
      ] := by
    simpa [fhat] using
      RingHom.formally_smooth_for_adic_tfae_completion_invariance
        (maximalIdeal R) (Ideal.fg_of_isNoetherianRing (maximalIdeal R))
        (maximalIdeal Rsh) (Ideal.fg_of_isNoetherianRing (maximalIdeal Rsh))
        (algebraMap R Rsh) hcont
  have hfhat_map :
      fhat.formally_smooth_for_adic
        (Ideal.map (algebraMap Rsh Shat) (maximalIdeal Rsh)) :=
    (hTFAE.out 0 2).mp strictHenselizationMap_formallySmooth_for_maximalIdeal_adic
  have hfhat :
      fhat.formally_smooth_for_adic (maximalIdeal Shat) := by
    simpa [Shat, completion_map_maximalIdeal_eq_maximalIdeal (R := Rsh)] using hfhat_map
  let _ : IsCompleteLocalRing Rhat :=
    completion_isCompleteLocalRing_of_maximalIdeal_fg
      (S := R) (Ideal.fg_of_isNoetherianRing (maximalIdeal R))
  let _ : IsNoetherianRing Rhat := adicCompletion_isNoetherianRing (R := R) (I := maximalIdeal R)
  let _ : IsLocalHom fhat := by infer_instance
  exact
    ((regularMap_specialFiber_characterizations_tfae
      (A := Rhat) (B := Shat)).out 3 0).mp hfhat

/-- Helper for Lemma 15.51.8: property `P` ascends from the formal fibers of `R` to the
completed `κ(p)`-fiber of `(R^sh)^∧`. -/
lemma strict_henselization_completed_base_fiber_hasProperty
    (hR : IsPRing P R) (p : PrimeSpectrum R) :
    P p.asIdeal.ResidueField
      (p.asIdeal.Fiber (AdicCompletion (maximalIdeal Rsh) Rsh)) := by
  let _ : IsPRing P R := hR
  let _ : IsNoetherianRing R := hR.toIsNoetherian
  let _ : IsNoetherianRing Rsh := isNoetherianRing_strictHenselization R Rsh
  let Rhat := AdicCompletion (maximalIdeal R) R
  let Shat := AdicCompletion (maximalIdeal Rsh) Rsh
  let _ : Algebra Rhat Shat := (maximalIdealCompletionMap (algebraMap R Rsh)).toAlgebra
  let _ : Algebra R Shat := inferInstance
  let _ : IsScalarTower R Rhat Shat := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    simpa [Rhat, Shat, RingHom.comp_apply] using
      (maximalIdealCompletionMap_comp (algebraMap R Rsh))
  let _ : IsNoetherianRing Rhat := adicCompletion_isNoetherianRing (R := R) (I := maximalIdeal R)
  let _ : IsNoetherianRing Shat :=
    adicCompletion_isNoetherianRing (R := Rsh) (I := maximalIdeal Rsh)
  let _ : Module.Flat R Rhat := maximalIdeal_completion_flat_of_isNoetherian (S := R)
  let _ : (algebraMap Rhat Shat).IsRegularRingMap :=
    strict_henselization_completionMap_regular (P := P) (R := R) (Rsh := Rsh) hR
  have hformal :
      ∀ q : PrimeSpectrum R,
        P q.asIdeal.ResidueField (q.asIdeal.Fiber Rhat) := by
    intro q
    simpa [Rhat] using
      completion_fibers_have_property_of_pRing
        (P := P) (A := R) (I := maximalIdeal R) hR q
  -- Proof comment: apply axiom `(C)` to the flat completion map `R → R^∧` and the regular
  -- completed comparison `R^∧ → (R^sh)^∧`.
  simpa [Rhat, Shat] using
    (FieldAlgebraProperty.HasPropertyC.regularAscent
      (P := P) R Rhat Shat hformal p)

/-- Helper for Lemma 15.51.8: once property `P` holds on the completed `κ(p)`-fiber, the source
proof isolates the chosen `r`-branch over `p`. -/
lemma strict_henselization_branch_formalFiber_hasProperty_over_base
    (p : PrimeSpectrum R) (r : p.asIdeal.primesOver Rsh)
    (hbase :
      P p.asIdeal.ResidueField
        (p.asIdeal.Fiber (AdicCompletion (maximalIdeal Rsh) Rsh))) :
    P p.asIdeal.ResidueField
      (r.1.asIdeal.Fiber (AdicCompletion (maximalIdeal Rsh) Rsh)) := by
  -- Proof comment: this is the strict-henselization specialization of the shared branch helper.
  simpa using
    completionFiber_branch_hasProperty_of_primesOver_split
      (P := P) (R := R) (B := Rsh) p r
      (fiberToPiResidueField_strictHenselization_bijective
        (R := R) (Rsh := Rsh) p)
      hbase

/-- Helper for Lemma 15.51.8: the strict henselization inherits formal fibers with property `P`
from the base local `P`-ring. -/
lemma localFormalFibersHaveProperty_strictHenselization
    (hR : IsPRing P R) :
    LocalFormalFibersHaveProperty P Rsh := by
  let _ : IsPRing P R := hR
  intro r
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R Rsh) r
  let rOver : p.asIdeal.primesOver Rsh := Ideal.primesOver.mk p.asIdeal r.asIdeal
  have hbase :
      P p.asIdeal.ResidueField
        (p.asIdeal.Fiber (AdicCompletion (maximalIdeal Rsh) Rsh)) :=
    strict_henselization_completed_base_fiber_hasProperty
      (P := P) (R := R) (Rsh := Rsh) hR p
  have hbranch :
      P p.asIdeal.ResidueField
        (r.asIdeal.Fiber (AdicCompletion (maximalIdeal Rsh) Rsh)) := by
    simpa [p, rOver] using
      strict_henselization_branch_formalFiber_hasProperty_over_base
        (P := P) (R := R) (Rsh := Rsh) p rOver hbase
  have hsep :
      Algebra.IsSeparable p.asIdeal.ResidueField r.asIdeal.ResidueField := by
    simpa [p, rOver] using
      (strictHenselization_residueField_isAlgebraic_and_separable
        (R := R) (Rsh := Rsh) p rOver).2
  let _ : Algebra.IsSeparable p.asIdeal.ResidueField r.asIdeal.ResidueField := hsep
  -- Proof comment: after isolating the chosen branch over `κ(p)`, axiom `(E)` upgrades the
  -- ground field to the residue field `κ(r)`.
  simpa [p] using
    (FieldAlgebraProperty.HasPropertyE.separableBaseChange
      (P := P) p.asIdeal.ResidueField r.asIdeal.ResidueField
      (r.asIdeal.Fiber (AdicCompletion (maximalIdeal Rsh) Rsh)) hbranch)

/- Domain sampling pass:
- primary domain: permanence of the Chapter 15 owner `IsPRing P R` under henselization and strict
  henselization of Noetherian local rings;
- sampled owner declarations:
  `IsPRing`,
  `FieldAlgebraProperty.HasPropertyE`,
  `isPRing_henselizationRing`,
  `strictHenselization_over_henselization_isStrictHenselizationOf`;
- best owner abstraction: the source-facing conclusions are owner statements `IsPRing P Rh` and
  `IsPRing P Rsh`; clause `(E)` already has the canonical owner `P.HasPropertyE`, so it should
  not reappear as a duplicate theorem argument;
- primitive data: a Noetherian local `P`-ring `R` together with chosen henselization and strict
  henselization owners;
- derived API: the paired conjunction theorem below, assembled from the two atomic owner-level
  consequences.

Source/core/bridge triage:
- `source-facing`: the permanence statements for henselization and strict henselization;
- `core/canonical`: `IsPRing` and `P.HasPropertyE`;
- `bridge/view`: the canonical pair-henselization theorem `isPRing_henselizationRing` and the
  comparison from a strict henselization over a henselization back to the base ring.
-/

-- Proof sketch: reduce to local formal fibers by Lemma `15.51.4`, then follow the source proof
-- directly on primes of `Rh`.
/-- Lemma 15.51.8, henselization case: if `R` is a `P`-ring, where `P` satisfies `(B)`, `(C)`,
`(D)`, and `(E)`, then any henselization `Rh` of `R` is a `P`-ring. -/
theorem isPRing_henselization
    (hR : IsPRing P R) :
    IsPRing P Rh := by
  let _ : IsPRing P R := hR
  let _ : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  have hformal :
      LocalFormalFibersHaveProperty P Rh :=
    localFormalFibersHaveProperty_henselization
      (P := P) (R := R) (Rh := Rh) hR
  -- Proof comment: once the henselization formal fibers are in place, the local closed-point
  -- support reduction from Lemma `15.51.4` finishes the `P`-ring statement.
  exact
    isPRing_of_localFormalFibersHaveProperty_closed_point_support
      (P := P) (A := Rh)
      (localFormalFibersHaveProperty_closed_point_support (P := P) (A := Rh))
      hformal

-- Proof sketch: use Lemma `15.51.4` to reduce to local formal fibers. For a prime `r` of `Rsh`
-- over `p ⊂ R`, Lemma `15.45.13` writes the fiber over `p` as a finite product of residue fields
-- and shows `κ(r) / κ(p)` is separable algebraic. Lemma `15.45.3` and Proposition `15.49.2`
-- identify the completion comparison `R^∧ → (R^sh)^∧` as regular, and then `(C)`, `(B)`, and
-- `(E)` transfer property `P` from the formal fibers of `R` to those of `Rsh`.
/-- Lemma 15.51.8, strict-henselization case: if `R` is a `P`-ring, where `P` satisfies `(B)`,
`(C)`, `(D)`, and `(E)`, then any strict henselization `Rsh` of `R` is a `P`-ring. -/
theorem isPRing_strictHenselization
    (hR : IsPRing P R) :
    IsPRing P Rsh := by
  let _ : IsPRing P R := hR
  let _ : IsNoetherianRing Rsh := isNoetherianRing_strictHenselization R Rsh
  have hformal :
      LocalFormalFibersHaveProperty P Rsh :=
    localFormalFibersHaveProperty_strictHenselization
      (P := P) (R := R) (Rsh := Rsh) hR
  -- Proof comment: once the strict-henselization formal fibers are known, the local case of
  -- Lemma `15.51.4` reduces the `P`-ring condition to transporting those fibers to the closed
  -- point localization.
  exact
    isPRing_of_localFormalFibersHaveProperty_closed_point_support
      (P := P) (A := Rsh)
      (strictHenselization_closedPoint_support (P := P) (R := R) (Rsh := Rsh))
      hformal

/-- Lemma 15.51.8: if `R` is a `P`-ring, where `P` satisfies `(B)`, `(C)`, `(D)`, and `(E)`,
then any henselization `Rh` and any strict henselization `Rsh` of `R` are `P`-rings. -/
theorem isPRing_henselization_and_strictHenselization
    (hR : IsPRing P R) :
    IsPRing P Rh ∧ IsPRing P Rsh := by
  exact ⟨isPRing_henselization P hR, isPRing_strictHenselization P hR⟩

end
