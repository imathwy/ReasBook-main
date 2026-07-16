import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_60_10
import stacks_proof.stacks_project.Chap10.Lemma_10_112_7

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v

open IsLocalRing
open scoped TensorProduct

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/-- The canonical quotient presentation of the closed fiber
`ClosedFiber = (maximalIdeal R).Fiber S`. -/
noncomputable def closedFiberQuotAlgEquiv : ClosedFiber ≃ₐ[R] S ⧸ 𝔪S :=
  (Algebra.TensorProduct.congr (.symm <| .ofBijective _
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.restrictScalars _)

/-- The canonical closed fiber is regular as soon as its quotient presentation
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` is regular. -/
theorem isRegularLocalRing_closedFiber_of_quotient
    [IsRegularLocalRing (S ⧸ 𝔪S)] :
    IsRegularLocalRing ClosedFiber := by
  simpa using
    (IsRegularLocalRing.of_ringEquiv closedFiberQuotAlgEquiv.toRingEquiv.symm :
      IsRegularLocalRing ClosedFiber)

end

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsRegularLocalRing R] [IsNoetherianRing S] [Module.Flat R S]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/- Domain sampling pass:
* primary domain: local commutative algebra of closed fibers of local ring maps;
* sampled owner declarations:
  - `Ideal.Fiber`, the canonical fiber-ring owner `κ(p) ⊗[R] S`;
  - the induced local-ring instance on `ClosedFiber` for local maps;
  - the canonical quotient view `ClosedFiber ≃ₐ[R] S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`;
  - downstream chapter usage already centered on `((maximalIdeal A).Fiber B)`, for example in
    `Lemma_15_78_6`.

Source/core/bridge triage:
* source-facing: the regular-closed-fiber criterion for a flat local homomorphism of local rings;
* core/canonical: the owner predicate `IsRegularLocalRing` on the owner fiber ring
  `ClosedFiber`;
* bridge/view: the quotient presentation `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`.

Primitive data are the ambient flat local algebra map and regularity of the closed fiber. The
local and Noetherian structure on `ClosedFiber` are derived from the owner assumption
`IsRegularLocalRing ClosedFiber`, so no extra wrapper or auxiliary data should be introduced here.
-/
-- Proof sketch: combine Lemma `10.112.7` with the canonical criterion
-- `isRegularLocalRing_iff` on `R`, `S`, and the owner closed fiber `ClosedFiber`. The dimension
-- formula gives `dim S = dim R + dim ClosedFiber`, while generators of `maximalIdeal R` together
-- with lifts of generators of the maximal ideal of `ClosedFiber` generate `maximalIdeal S`;
-- comparing the resulting generator count with the dimension yields regularity.
/-- Lemma 10.112.8: if `R → S` is a flat local homomorphism of local Noetherian rings, `R` is a
regular local ring, and the closed fibre `((maximalIdeal R).Fiber S)`, equivalently
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`, is a regular local ring, then `S` is a
regular local ring. -/
@[stacks 031E]
theorem isRegularLocalRing_of_flat_localHom_of_regular_closedFiber
    (hclosedFiber : IsRegularLocalRing ClosedFiber) :
    IsRegularLocalRing S := by
  classical
  letI : IsRegularLocalRing ClosedFiber := hclosedFiber
  let hquot : IsRegularLocalRing (S ⧸ 𝔪S) :=
    IsRegularLocalRing.of_ringEquiv closedFiberQuotAlgEquiv.toRingEquiv
  letI : IsRegularLocalRing (S ⧸ 𝔪S) := hquot
  let d : ℕ := (maximalIdeal R).spanFinrank
  let e : ℕ := (maximalIdeal (S ⧸ 𝔪S)).spanFinrank
  have hdimR : ringKrullDim R = d := by
    simpa [d] using
      ((isRegularLocalRing_iff (R := R)).1 (inferInstance : IsRegularLocalRing R)).symm
  have hdimQ : ringKrullDim (S ⧸ 𝔪S) = e := by
    simpa [e] using ((isRegularLocalRing_iff (R := S ⧸ 𝔪S)).1 hquot).symm
  -- Choose regular systems of parameters on the source and on the quotient closed fiber.
  obtain ⟨x, hx⟩ :=
    (isRegularLocalRing_iff_exists_regularSystemOfParameters (R := R) (d := d) hdimR).1
      inferInstance
  obtain ⟨ybar, hybar⟩ :=
    (isRegularLocalRing_iff_exists_regularSystemOfParameters (R := S ⧸ 𝔪S) (d := e) hdimQ).1
      inferInstance
  have hx_parameter : parameterIdeal x = maximalIdeal R := by
    exact (isRegularSystemOfParameters_iff_of_ringKrullDim_eq (R := R) hdimR x).1 hx
  have hybar_parameter : parameterIdeal ybar = maximalIdeal (S ⧸ 𝔪S) := by
    exact (isRegularSystemOfParameters_iff_of_ringKrullDim_eq (R := S ⧸ 𝔪S) hdimQ ybar).1 hybar
  have h𝔪S_ne_top : 𝔪S ≠ ⊤ :=
    (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne
  have h𝔪S_le : 𝔪S ≤ maximalIdeal S :=
    IsLocalRing.le_maximalIdeal h𝔪S_ne_top
  have hxS_mem :
      ∀ i : Fin d, algebraMap R S ((x i : maximalIdeal R) : R) ∈ maximalIdeal S := by
    intro i
    exact h𝔪S_le (Ideal.mem_map_of_mem _ (x i).2)
  let xS : Fin d → maximalIdeal S :=
    fun i ↦ ⟨algebraMap R S ((x i : maximalIdeal R) : R), hxS_mem i⟩
  have hxS_range :
      Set.range (fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)) =
        (algebraMap R S) '' Set.range (fun i : Fin d ↦ ((x i : maximalIdeal R) : R)) := by
    ext s
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨((x i : maximalIdeal R) : R), ⟨i, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  have hxS_parameter : parameterIdeal xS = 𝔪S := by
    -- Mapping the source parameters into `S` recovers the ideal `𝔪_R S`.
    calc
      parameterIdeal xS = Ideal.span (Set.range fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)) := by
        rw [parameterIdeal_eq_span]
      _ = Ideal.span ((algebraMap R S) '' Set.range fun i : Fin d ↦ ((x i : maximalIdeal R) : R)) := by
        rw [hxS_range]
      _ = Ideal.map (algebraMap R S) (Ideal.span (Set.range fun i : Fin d ↦ ((x i : maximalIdeal R) : R))) := by
        rw [Ideal.map_span]
      _ = Ideal.map (algebraMap R S) (parameterIdeal x) := by
        rw [parameterIdeal_eq_span]
      _ = 𝔪S := by
        rw [hx_parameter]
  have hmaxmap :
      Ideal.map (Ideal.Quotient.mk 𝔪S) (maximalIdeal S) = maximalIdeal (S ⧸ 𝔪S) := by
    -- The quotient map sends the maximal ideal of `S` onto the maximal ideal of the quotient.
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk 𝔪S)
      Ideal.Quotient.mk_surjective
  choose y hy_mem hy_eq using fun i : Fin e ↦ by
    have hyi :
        ((ybar i : maximalIdeal (S ⧸ 𝔪S)) : S ⧸ 𝔪S) ∈
          Ideal.map (Ideal.Quotient.mk 𝔪S) (maximalIdeal S) := by
      simpa [hmaxmap] using (ybar i).2
    exact (Ideal.mem_map_iff_of_surjective (f := Ideal.Quotient.mk 𝔪S)
      (hf := Ideal.Quotient.mk_surjective)
      (I := maximalIdeal S)
      (y := ((ybar i : maximalIdeal (S ⧸ 𝔪S)) : S ⧸ 𝔪S))).1 hyi
  let yLift : Fin e → maximalIdeal S := fun i ↦ ⟨y i, hy_mem i⟩
  have hyLift_parameter_map :
      Ideal.map (Ideal.Quotient.mk 𝔪S) (parameterIdeal yLift) = parameterIdeal ybar := by
    -- The chosen lifts project back to the quotient parameters coordinatewise.
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, parameterIdeal_eq_span]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      refine Ideal.mem_comap.2 ?_
      change Ideal.Quotient.mk 𝔪S ((yLift i : maximalIdeal S) : S) ∈ parameterIdeal ybar
      rw [show Ideal.Quotient.mk 𝔪S ((yLift i : maximalIdeal S) : S) =
        ((ybar i : maximalIdeal (S ⧸ 𝔪S)) : S ⧸ 𝔪S) by
          simpa [yLift] using hy_eq i]
      exact Ideal.subset_span ⟨i, rfl⟩
    · rw [parameterIdeal_eq_span]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      have hyi_mem : ((yLift i : maximalIdeal S) : S) ∈ parameterIdeal yLift := by
        rw [parameterIdeal_eq_span]
        exact Ideal.subset_span ⟨i, rfl⟩
      have hyi_map_mem :
          (((ybar i : maximalIdeal (S ⧸ 𝔪S)) : S ⧸ 𝔪S)) ∈
            Ideal.map (Ideal.Quotient.mk 𝔪S) (parameterIdeal yLift) := by
        refine (Ideal.mem_map_iff_of_surjective (f := Ideal.Quotient.mk 𝔪S)
          (hf := Ideal.Quotient.mk_surjective)
          (I := parameterIdeal yLift)
          (y := ((ybar i : maximalIdeal (S ⧸ 𝔪S)) : S ⧸ 𝔪S))).2 ?_
        refine ⟨((yLift i : maximalIdeal S) : S), hyi_mem, ?_⟩
        simpa [yLift] using hy_eq i
      simpa using hyi_map_mem
  have hyLift_sup : parameterIdeal yLift ⊔ 𝔪S = maximalIdeal S := by
    -- Pulling the quotient maximal ideal back along the quotient map adds back only the kernel.
    calc
      parameterIdeal yLift ⊔ 𝔪S =
          Ideal.comap (Ideal.Quotient.mk 𝔪S)
            (Ideal.map (Ideal.Quotient.mk 𝔪S) (parameterIdeal yLift)) := by
              rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk 𝔪S)
                Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      _ = Ideal.comap (Ideal.Quotient.mk 𝔪S) (maximalIdeal (S ⧸ 𝔪S)) := by
        rw [hyLift_parameter_map, hybar_parameter]
      _ = maximalIdeal S := by
        rw [← hmaxmap, Ideal.comap_map_of_surjective (Ideal.Quotient.mk 𝔪S)
          Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
          sup_eq_left.mpr h𝔪S_le]
  have hgenerator :
      Ideal.span
          (Set.range (fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)) ∪
            Set.range (fun i : Fin e ↦ ((yLift i : maximalIdeal S) : S))) =
        maximalIdeal S := by
    -- The source parameters generate `𝔪_R S`, and adjoining lifted quotient parameters generates
    -- the whole maximal ideal of `S`.
    calc
      Ideal.span
          (Set.range (fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)) ∪
            Set.range (fun i : Fin e ↦ ((yLift i : maximalIdeal S) : S))) =
          Ideal.span (Set.range fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)) ⊔
            Ideal.span (Set.range fun i : Fin e ↦ ((yLift i : maximalIdeal S) : S)) := by
              rw [Ideal.span_union]
      _ = parameterIdeal xS ⊔ parameterIdeal yLift := by
        rw [← parameterIdeal_eq_span, ← parameterIdeal_eq_span]
      _ = maximalIdeal S := by
        rw [hxS_parameter, sup_comm]
        exact hyLift_sup
  let gX : Set S := Set.range fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)
  let gY : Set S := Set.range fun i : Fin e ↦ ((yLift i : maximalIdeal S) : S)
  have hgX_ncard : gX.ncard ≤ d := by
    let sx : Finset S := Finset.univ.image fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)
    have hsx : gX = (sx : Set S) := by
      ext s
      constructor
      · rintro ⟨i, rfl⟩
        simp [sx]
      · intro hs
        simp only [sx, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hs
        rcases hs with ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    rw [hsx, Set.ncard_coe_finset]
    simpa [sx] using
      (Finset.card_image_le
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun i : Fin d ↦ ((xS i : maximalIdeal S) : S)))
  have hgY_ncard : gY.ncard ≤ e := by
    let sy : Finset S := Finset.univ.image fun i : Fin e ↦ ((yLift i : maximalIdeal S) : S)
    have hsy : gY = (sy : Set S) := by
      ext s
      constructor
      · rintro ⟨i, rfl⟩
        simp [sy]
      · intro hs
        simp only [sy, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hs
        rcases hs with ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    rw [hsy, Set.ncard_coe_finset]
    simpa [sy] using
      (Finset.card_image_le
        (s := (Finset.univ : Finset (Fin e)))
        (f := fun i : Fin e ↦ ((yLift i : maximalIdeal S) : S)))
  have hspan_le : (maximalIdeal S).spanFinrank ≤ d + e := by
    have hgenerator' : Ideal.span (gX ∪ gY) = maximalIdeal S := by
      simpa [gX, gY] using hgenerator
    -- The generating family has at most `d + e` distinct elements.
    calc
      (maximalIdeal S).spanFinrank = (Ideal.span (gX ∪ gY)).spanFinrank := by
        rw [hgenerator']
      _ ≤ (gX ∪ gY).ncard := by
        exact Submodule.spanFinrank_span_le_ncard_of_finite (gX.toFinite.union gY.toFinite)
      _ ≤ gX.ncard + gY.ncard := Set.ncard_union_le gX gY
      _ ≤ d + e := add_le_add hgX_ncard hgY_ncard
  have hdimS : ringKrullDim S = d + e := by
    let q : PrimeSpectrum S := ⟨maximalIdeal S, inferInstance⟩
    let h_unitsR : (maximalIdeal R).primeCompl ≤ IsUnit.submonoid R := by
      intro r hr
      simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Classical.not_not] using hr
    let h_unitsS : (maximalIdeal S).primeCompl ≤ IsUnit.submonoid S := by
      intro s hs
      simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Classical.not_not] using hs
    let pUnder : Ideal R := Ideal.under R (maximalIdeal S)
    letI : pUnder.IsPrime := by
      dsimp [pUnder]
      infer_instance
    have hpUnder : pUnder = maximalIdeal R := by
      simpa [pUnder, Ideal.under_def] using IsLocalRing.maximalIdeal_comap (algebraMap R S)
    have h_unitsP : pUnder.primeCompl ≤ IsUnit.submonoid R := by
      intro r hr
      have hr' : r ∉ maximalIdeal R := by
        simpa [pUnder, hpUnder] using hr
      simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Classical.not_not] using hr'
    letI : IsLocalization pUnder.primeCompl R := IsLocalization.self h_unitsP
    letI : IsLocalization (maximalIdeal S).primeCompl S := IsLocalization.self h_unitsS
    let eP : Localization.AtPrime pUnder ≃ₐ[R] R :=
      IsLocalization.algEquiv pUnder.primeCompl (Localization.AtPrime pUnder) R
    let eS : Localization.AtPrime (maximalIdeal S) ≃ₐ[S] S :=
      IsLocalization.algEquiv (maximalIdeal S).primeCompl
        (Localization.AtPrime (maximalIdeal S)) S
    let Iunder : Ideal (Localization.AtPrime (maximalIdeal S)) :=
      Ideal.map (algebraMap R (Localization.AtPrime (maximalIdeal S))) pUnder
    have hIunder_map : Ideal.map eS.toRingHom Iunder = 𝔪S := by
      -- Localizing a local ring at its maximal ideal does not change the extended source ideal.
      calc
        Ideal.map eS.toRingHom Iunder =
            Ideal.map
              (eS.toRingHom.comp (algebraMap R (Localization.AtPrime (maximalIdeal S))))
              pUnder := by
                simpa [Iunder] using
                  (Ideal.map_map (I := pUnder)
                    (algebraMap R (Localization.AtPrime (maximalIdeal S))) eS.toRingHom)
        _ = Ideal.map (algebraMap R S) pUnder := by
          congr 1
          ext r
          simpa [IsScalarTower.algebraMap_eq R S (Localization.AtPrime (maximalIdeal S))] using
            (eS.commutes (algebraMap R S r))
        _ = Ideal.map (algebraMap R S) (maximalIdeal R) := by
          rw [hpUnder]
        _ = 𝔪S := rfl
    have hIunder_comap : Ideal.comap eS.toRingHom 𝔪S = Iunder := by
      rw [← hIunder_map, Ideal.comap_map_of_surjective eS.toRingHom eS.surjective,
        Ideal.comap_bot_of_injective (f := eS.toRingHom) eS.injective, sup_eq_left]
      exact bot_le
    let φ : Localization.AtPrime (maximalIdeal S) →+* S ⧸ 𝔪S :=
      (Ideal.Quotient.mk 𝔪S).comp eS.toRingHom
    have hφ_surj : Function.Surjective φ := Ideal.Quotient.mk_surjective.comp eS.surjective
    have hker_aux :
        RingHom.ker ((Ideal.Quotient.mk 𝔪S).comp eS.toRingHom) =
          Ideal.comap eS.toRingHom 𝔪S := by
      ext z
      simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    have hkerφ : RingHom.ker φ = Iunder := by
      change RingHom.ker ((Ideal.Quotient.mk 𝔪S).comp eS.toRingHom) = Iunder
      rw [hker_aux, hIunder_comap]
    let eQ : (Localization.AtPrime (maximalIdeal S)) ⧸ Iunder ≃+* S ⧸ 𝔪S :=
      (Ideal.quotEquivOfEq hkerφ.symm).trans (RingHom.quotientKerEquivOfSurjective hφ_surj)
    have hdimLoc :
        ringKrullDim (Localization.AtPrime (maximalIdeal S)) =
          ringKrullDim (Localization.AtPrime pUnder) +
            ringKrullDim (Localization.AtPrime (maximalIdeal S) ⧸ Iunder) := by
      change
        ringKrullDim (Localization.AtPrime q.asIdeal) =
          ringKrullDim (Localization.AtPrime pUnder) +
            ringKrullDim
              ((Localization.AtPrime q.asIdeal) ⧸
                Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) pUnder)
      simpa [q, pUnder, Iunder] using
        ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_quotient_of_hasGoingDown
          (R := R) (S := S) q
    -- Rewrite the localized dimension formula back to the original local rings and closed fiber.
    calc
      ringKrullDim S = ringKrullDim (Localization.AtPrime (maximalIdeal S)) := by
        symm
        exact ringKrullDim_eq_of_ringEquiv eS.toRingEquiv
      _ = ringKrullDim (Localization.AtPrime pUnder) + ringKrullDim (Localization.AtPrime (maximalIdeal S) ⧸ Iunder) := by
        exact hdimLoc
      _ = ringKrullDim R + ringKrullDim (S ⧸ 𝔪S) := by
        rw [ringKrullDim_eq_of_ringEquiv eP.toRingEquiv, ringKrullDim_eq_of_ringEquiv eQ]
      _ = d + e := by
        rw [hdimR, hdimQ]
  -- The source-faithful generator count matches the dimension formula, so the regular-local
  -- criterion closes the proof.
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := S) ?_
  rw [hdimS]
  exact_mod_cast hspan_le

end
