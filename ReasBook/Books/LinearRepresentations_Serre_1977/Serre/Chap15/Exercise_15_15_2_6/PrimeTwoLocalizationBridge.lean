import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_2_6.Foundations

noncomputable section

universe u v w

local notation:max p " •ℤ " E => (Representation.primeIdeal p • (⊤ : Submodule ℤ E))

section ThompsonExercise

variable {G : Type u} [Group G]
variable {E : Type v} [AddCommGroup E] [Module ℤ E]

section IntegralLatticeAmbient

variable [Module.Free ℤ E] [Module.Finite ℤ E]

/-- Helper for Exercise 15-15.2-6: the canonical class of `x` in the prime-`2` reduction of
`ρ.primeStableLattice 2`. -/
def prime_two_reduction_class (ρ : Representation ℤ G E) (x : E) :
    (ρ.primeStableLattice 2).reduction :=
  Submodule.Quotient.mk
    ((⟨LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl) x 1,
      Submodule.mem_top⟩) : (ρ.primeStableLattice 2).toSubmodule)

attribute [local instance] Submodule.Quotient.module

/-- Helper for Exercise 15-15.2-6: restrict a mod-`2` endomorphism back to the underlying
`ℤ`-linear quotient action. -/
private abbrev prime_two_mod_two_quotient_restrictScalarsEnd :
    Module.End (ℤ ⧸ Representation.primeIdeal 2) (E ⧸ (2 •ℤ E)) →+*
      Module.End ℤ (E ⧸ (2 •ℤ E)) where
  toFun := LinearMap.restrictScalars ℤ
  map_one' := by
    ext x
    rfl
  map_mul' _ _ := by
    ext x
    rfl
  map_zero' := by
    ext x
    rfl
  map_add' _ _ := by
    ext x
    rfl

/-- Helper for Exercise 15-15.2-6: integer scalar actions commute on `E`. -/
private instance int_smulCommClass_on_E : SMulCommClass ℤ ℤ E where
  smul_comm a b z := by
    simp [smul_smul, mul_comm]

/-- Helper for Exercise 15-15.2-6: the quotient map `E → E / 2E` as a `ℤ`-linear map built from
the ambient integer action on the quotient. -/
private def prime_two_mod_two_quotient_linearMap : E →ₗ[ℤ] E ⧸ (2 •ℤ E) where
  -- Route correction: define the detector on the ambient quotient owner used by
  -- `LocalizedModule.lift`, and recover `ℤ`-linearity from the additive universal property.
  toFun := Submodule.Quotient.mk
  map_add' := by
    -- The quotient map is additive by construction.
    simp
  map_smul' := by
    intro m x
    -- View the quotient map as an additive morphism and upgrade its `zsmul` compatibility to
    -- `ℤ`-linearity via `map_intCast_smul`.
    let q : E →+ E ⧸ (2 •ℤ E) :=
      { toFun := Submodule.Quotient.mk
        map_zero' := by simp
        map_add' := by simp }
    simpa [q, RingHom.id_apply] using map_intCast_smul q ℤ ℤ m x

/-- Helper for Exercise 15-15.2-6: every denominator in the localization away from `(2)` acts
invertibly on `E / 2E`. -/
private theorem prime_two_denominator_isUnit_on_mod_two_quotient
    (s : (Representation.primeIdeal 2).primeCompl) :
    IsUnit ((algebraMap ℤ (Module.End ℤ (E ⧸ (2 •ℤ E)))) (s : ℤ)) := by
  letI : Field (ℤ ⧸ Representation.primeIdeal 2) :=
    Ideal.Quotient.field (Representation.primeIdeal 2)
  -- The class of an odd integer is nonzero in the residue field, hence a unit there.
  have hsq : IsUnit ((Ideal.Quotient.mk (Representation.primeIdeal 2)) (s : ℤ)) := by
    rw [isUnit_iff_ne_zero]
    intro hs0
    exact s.2 ((Ideal.Quotient.eq_zero_iff_mem).1 hs0)
  have hs_end :
      IsUnit ((algebraMap (ℤ ⧸ Representation.primeIdeal 2)
          (Module.End (ℤ ⧸ Representation.primeIdeal 2) (E ⧸ (2 •ℤ E))))
        ((Ideal.Quotient.mk (Representation.primeIdeal 2)) (s : ℤ))) :=
    hsq.map _
  let restrictScalarsEnd :
      Module.End (ℤ ⧸ Representation.primeIdeal 2) (E ⧸ (2 •ℤ E)) →+*
        Module.End ℤ (E ⧸ (2 •ℤ E)) :=
    { toFun := LinearMap.restrictScalars ℤ
      map_one' := by
        ext x
        rfl
      map_mul' _ _ := by
        ext x
        rfl
      map_zero' := by
        ext x
        rfl
      map_add' _ _ := by
        ext x
        rfl }
  -- Restrict the resulting unit endomorphism along the quotient-ring action to the `ℤ`-linear one.
  simpa [restrictScalarsEnd] using hs_end.map restrictScalarsEnd

/-- Helper for Exercise 15-15.2-6: the mod-`2` quotient is annihilated by multiplication by `2`.
-/
private theorem two_smul_eq_zero_on_prime_two_mod_two_quotient
    (q : E ⧸ (2 •ℤ E)) :
    (2 : ℤ) • q = 0 := by
  -- Reduce to a represented quotient class and rewrite scalar multiplication through `mk`.
  refine Quotient.inductionOn' q ?_
  intro y
  change Submodule.Quotient.mk ((2 : ℤ) • y) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  -- The represented element `2 • y` already lies in the defining submodule `2E`.
  have hspan :
      (2 : ℤ) • y ∈ Representation.primeIdeal 2 •
        Submodule.span ℤ ((⊤ : Submodule ℤ E) : Set E) := by
    rw [Submodule.mem_smul_span]
    exact Submodule.subset_span ⟨(2 : ℤ),
      show (2 : ℤ) ∈ Representation.primeIdeal 2 from by
        simpa [Representation.primeIdeal] using (Ideal.mem_span_singleton_self (2 : ℤ)),
      y,
      by trivial,
      int_smul_eq_zsmul (inferInstance : Module ℤ E) (2 : ℤ) y⟩
  simpa using hspan

/-- Helper for Exercise 15-15.2-6: scalar multiplication in the top stable lattice agrees with the
ambient localized scalar multiplication after forgetting the subtype. -/
private theorem top_stable_lattice_smul_subtype_eq
    (ρ : Representation ℤ G E)
    (a : Localization.AtPrime (Representation.primeIdeal 2))
    (z : (ρ.primeStableLattice 2).toSubmodule) :
    (((a • z : (ρ.primeStableLattice 2).toSubmodule) :
        (ρ.primeStableLattice 2).toSubmodule) :
      LocalizedModule.AtPrime (Representation.primeIdeal 2) E) =
      a • (z : LocalizedModule.AtPrime (Representation.primeIdeal 2) E) := by
  rfl

/-- Helper for Exercise 15-15.2-6: keep the localization detector on one fixed `ℤ`-linear
quotient-module structure so that the later quotient descent does not depend on elaboration
choosing a different codomain copy. -/
private noncomputable def prime_two_localized_detector_with_fixed_quotient_module :
    LocalizedModule.AtPrime (Representation.primeIdeal 2) E →ₗ[ℤ] E ⧸ (2 •ℤ E) :=
  -- Route correction: extend the canonical quotient map across localization by the bundled
  -- `LocalizedModule.lift`, so denominator-`1` computations become `lift_mk_one`.
  { toFun :=
      LocalizedModule.lift (S := (Representation.primeIdeal 2).primeCompl)
        prime_two_mod_two_quotient_linearMap
        prime_two_denominator_isUnit_on_mod_two_quotient
    map_add' := by
      intro z w
      simpa using
        (LocalizedModule.lift (S := (Representation.primeIdeal 2).primeCompl)
          prime_two_mod_two_quotient_linearMap
          prime_two_denominator_isUnit_on_mod_two_quotient).map_add z w
    map_smul' := by
      intro r z
      simpa using
        (LocalizedModule.lift (S := (Representation.primeIdeal 2).primeCompl)
          prime_two_mod_two_quotient_linearMap
          prime_two_denominator_isUnit_on_mod_two_quotient).map_smul r z }

/-- Helper for Exercise 15-15.2-6: the quotient map `E → E / 2E` extends across localization at
the prime ideal `(2)`. -/
noncomputable def prime_two_localized_to_mod_two_quotient :
    LocalizedModule.AtPrime (Representation.primeIdeal 2) E →ₗ[ℤ] E ⧸ (2 •ℤ E) :=
  prime_two_localized_detector_with_fixed_quotient_module

/-- Helper for Exercise 15-15.2-6: the localization comparison sends an integral vector to its
class modulo `2E`. -/
private theorem prime_two_localized_to_mod_two_quotient_mk_one (x : E) :
    prime_two_localized_to_mod_two_quotient
        (LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl) x 1) =
      Submodule.Quotient.mk x := by
  -- Compute the descended detector on a denominator-`1` representative by the localization
  -- universal property.
  simpa [prime_two_localized_to_mod_two_quotient,
    prime_two_localized_detector_with_fixed_quotient_module,
    prime_two_mod_two_quotient_linearMap] using
    (LocalizedModule.lift_mk_one (S := (Representation.primeIdeal 2).primeCompl)
      (g := prime_two_mod_two_quotient_linearMap)
      (h := prime_two_denominator_isUnit_on_mod_two_quotient) x)

/-- Helper for Exercise 15-15.2-6: multiplying a denominator-`1` localized class by the image of
`2` is the same as localizing the doubled integral vector. -/
private theorem prime_two_localized_smul_mk_one (y : E) :
    (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal 2)) (2 : ℤ)) •
        LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl) y 1 =
      LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl) ((2 : ℤ) • y) 1 := by
  -- Rewrite the ambient scalar as the denominator-`1` localization of `2`, then compare the two
  -- `ℤ`-smul conventions on `E` before applying `LocalizedModule.mk_smul_mk`.
  change
    Localization.mk (2 : ℤ) (1 : (Representation.primeIdeal 2).primeCompl) •
        LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl) y 1 =
      LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl) ((2 : ℤ) • y) 1
  rw [← int_smul_eq_zsmul (h := (inferInstance : Module ℤ E)) (n := (2 : ℤ)) (x := y)]
  simpa using
    (LocalizedModule.mk_smul_mk (S := (Representation.primeIdeal 2).primeCompl)
      (r := (2 : ℤ)) (m := y) (s := (1 : (Representation.primeIdeal 2).primeCompl))
      (t := (1 : (Representation.primeIdeal 2).primeCompl)))

/-- Helper for Exercise 15-15.2-6: after mapping `(2)` into the prime-`2` localization, the image
ideal is still generated by the image of `2`. -/
private theorem prime_two_map_eq_span_singleton :
    Ideal.map (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal 2)))
      (Representation.primeIdeal 2) =
    Ideal.span ({algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal 2)) (2 : ℤ)} :
      Set (Localization.AtPrime (Representation.primeIdeal 2))) := by
  -- The principal generator survives localization as the same principal generator.
  simpa [Representation.primeIdeal] using
    (Ideal.map_span (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal 2)))
      ({(2 : ℤ)} : Set ℤ))

/-- Helper for Exercise 15-15.2-6: the image of `2` belongs to the mapped prime-`2` ideal in the
localization ring. -/
private theorem algebraMap_two_mem_prime_two_map :
    algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal 2)) (2 : ℤ) ∈
      Ideal.map (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal 2)))
        (Representation.primeIdeal 2) := by
  -- This is the generator of the mapped principal ideal.
  exact Ideal.mem_map_of_mem _ (by
    simpa [Representation.primeIdeal] using Ideal.mem_span_singleton_self (2 : ℤ))

/-- Helper for Exercise 15-15.2-6: every element of the localized image of `(2)` is visibly a
multiple of `2` in the localization ring. -/
private theorem exists_algebraMap_two_mul_of_mem_prime_two_map
    {r : Localization.AtPrime (Representation.primeIdeal 2)}
    (hr : r ∈ Ideal.map (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal 2)))
      (Representation.primeIdeal 2)) :
    ∃ c : Localization.AtPrime (Representation.primeIdeal 2),
      r = algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal 2)) (2 : ℤ) * c := by
  rw [prime_two_map_eq_span_singleton] at hr
  rw [Ideal.mem_span_singleton] at hr
  rcases hr with ⟨c, rfl⟩
  exact ⟨c, rfl⟩

/-- Helper for Exercise 15-15.2-6: an integral vector lying in `2E` is literally a double in the
integral module. -/
private theorem exists_two_smul_eq_of_mem_two_mul
    {x : E} (hx : x ∈ (2 •ℤ E)) :
    ∃ y : E, x = (2 : ℤ) • y := by
  let doubledRange : Submodule ℤ E :=
    Submodule.map ((LinearMap.lsmul ℤ E) (2 : ℤ)) ⊤
  have hdouble :
      (2 •ℤ E) ≤ doubledRange := by
    -- Rewrite the ideal multiple as the bilinear image of the principal ideal and the top
    -- lattice, then factor each generator through visible multiplication by `2`.
    rw [show (2 •ℤ E) = Representation.primeIdeal 2 • (⊤ : Submodule ℤ E) by rfl]
    rw [Submodule.smul_eq_map₂, Submodule.map₂]
    refine iSup_le ?_
    intro r
    intro z hz
    rcases hz with ⟨y, -, rfl⟩
    have hr : (r : ℤ) ∈ Representation.primeIdeal 2 := r.property
    change (r : ℤ) ∈ Ideal.span ({(2 : ℤ)} : Set ℤ) at hr
    rw [Ideal.mem_span_singleton] at hr
    rcases hr with ⟨c, hc⟩
    refine ⟨c • y, by trivial, ?_⟩
    calc
      ((LinearMap.lsmul ℤ E) (2 : ℤ)) (c • y)
          = c • ((2 : ℤ) • y) := by
              -- First peel off the outer `c`-smul through the linear map, then bridge the inner
              -- `lsmul` value to the ambient `zsmul` notation.
              calc
                ((LinearMap.lsmul ℤ E) (2 : ℤ)) (c • y)
                    = c • (((LinearMap.lsmul ℤ E) (2 : ℤ)) y) := by
                        simpa only [LinearMap.map_smul_of_tower]
                _ = c • ((2 : ℤ) • y) := by
                      congr 1
                      rw [← Int.cast_smul_eq_zsmul (R := ℤ) (n := (2 : ℤ)) (b := y)]
                      simp [LinearMap.lsmul_apply]
      _ = (c * 2 : ℤ) • y := by
            simpa using (mul_zsmul y c 2).symm
      _ = (r : ℤ) • y := by
            rw [hc, mul_comm]
      _ = ((LinearMap.lsmul ℤ E) (r : ℤ)) y := by
            rw [← Int.cast_smul_eq_zsmul (R := ℤ) (n := r) (b := y)]
            simp [LinearMap.lsmul_apply]
  have hx_double : x ∈ doubledRange := hdouble hx
  rcases hx_double with ⟨y, -, hy⟩
  refine ⟨y, ?_⟩
  rw [← Int.cast_smul_eq_zsmul (R := ℤ) (n := (2 : ℤ)) (b := y)]
  simpa [doubledRange, LinearMap.lsmul_apply] using hy.symm

/-- Helper for Exercise 15-15.2-6: an integral vector in `2E` becomes a visible localized
`2`-multiple with denominator `1`. -/
private theorem localized_mk_eq_two_smul_mk_one_of_mem_two_mul
    {x : E} (hx : x ∈ (2 •ℤ E)) :
    ∃ y : E,
      LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl) x 1 =
        (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal 2)) (2 : ℤ)) •
          LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl) y 1 := by
  -- Rewrite the integral witness `x = 2 • y` through the denominator-`1` localization formula.
  rcases exists_two_smul_eq_of_mem_two_mul hx with ⟨y, rfl⟩
  refine ⟨y, ?_⟩
  simpa using (prime_two_localized_smul_mk_one (y := y)).symm

/-- Helper for Exercise 15-15.2-6: an integral vector lying in `2E` maps to the maximal-ideal
submodule of the canonical prime-`2` lattice. -/
private theorem localized_mk_mem_maximalIdealSubmodule_of_mem_two_mul
    (ρ : Representation ℤ G E) {x : E} (hx : x ∈ (2 •ℤ E)) :
    ((⟨LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl) x 1,
      Submodule.mem_top⟩) : (ρ.primeStableLattice 2).toSubmodule) ∈
      (ρ.primeStableLattice 2).maximalIdealSubmodule := by
  -- Read the subtype statement upstairs in the ambient localized module.
  rw [StableLattice.maximalIdealSubmodule, Submodule.mem_smul_top_iff]
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := Representation.primeIdeal 2)]
  -- Make the represented localization visibly a multiple of the image of `2`.
  rw [prime_two_map_eq_span_singleton, Submodule.ideal_span_singleton_smul]
  rcases localized_mk_eq_two_smul_mk_one_of_mem_two_mul hx with ⟨y, hy⟩
  rw [hy]
  refine ⟨LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl) y 1,
    by simpa [Representation.primeStableLattice], ?_⟩
  rfl

/-- Helper for Exercise 15-15.2-6: the localization detector kills a represented localized double.
-/
private theorem prime_two_localized_to_mod_two_quotient_mk_two_zero
    (m : E) (s : (Representation.primeIdeal 2).primeCompl) :
    prime_two_localized_to_mod_two_quotient
        (LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl)
          ((LinearMap.lsmul ℤ E (2 : ℤ)) m) s) = 0 := by
  -- Evaluate the localized detector on the represented localized class.
  change
    LocalizedModule.lift (S := (Representation.primeIdeal 2).primeCompl)
        prime_two_mod_two_quotient_linearMap
        prime_two_denominator_isUnit_on_mod_two_quotient
        (LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl)
          ((LinearMap.lsmul ℤ E (2 : ℤ)) m) s) = 0
  rw [LocalizedModule.lift_mk]
  -- Multiplication by `2` already kills every class in `E / 2E`, including the transported one.
  simpa [prime_two_mod_two_quotient_linearMap] using
    two_smul_eq_zero_on_prime_two_mod_two_quotient
      (q := ((prime_two_denominator_isUnit_on_mod_two_quotient s).unit⁻¹.val
        (prime_two_mod_two_quotient_linearMap m)))

/-- Helper for Exercise 15-15.2-6: the localization detector kills any visible localized
multiple of the image of `2`. -/
private theorem prime_two_localized_to_mod_two_quotient_eq_zero_of_two_smul
    (z : LocalizedModule.AtPrime (Representation.primeIdeal 2) E) :
    prime_two_localized_to_mod_two_quotient
        ((algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal 2)) (2 : ℤ)) • z) = 0 :=
  by
  -- Reduce the localized vector to a represented class and rewrite the visible `2`-multiple.
  refine LocalizedModule.induction_on
    (β := fun z =>
      prime_two_localized_to_mod_two_quotient
          ((algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal 2)) (2 : ℤ)) • z) = 0)
    ?_ z
  intro m s
  change
    prime_two_localized_to_mod_two_quotient
        ((Localization.mk (2 : ℤ) (1 : (Representation.primeIdeal 2).primeCompl)) •
          LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl) m s) = 0
  rw [LocalizedModule.mk_smul_mk]
  simpa using prime_two_localized_to_mod_two_quotient_mk_two_zero m s

/-- Helper for Exercise 15-15.2-6: the localization comparison kills the maximal-ideal multiple
inside the canonical prime-`2` lattice. -/
private theorem prime_two_localized_to_mod_two_quotient_eq_zero_of_mem_maximalIdeal
    (ρ : Representation ℤ G E)
    {z : (ρ.primeStableLattice 2).toSubmodule}
    (hz : z ∈ (ρ.primeStableLattice 2).maximalIdealSubmodule) :
    prime_two_localized_to_mod_two_quotient (z : LocalizedModule.AtPrime
        (Representation.primeIdeal 2) E) = 0 := by
  -- Rewrite `hz` in the ideal-smul form defining the maximal-ideal submodule.
  rw [StableLattice.maximalIdealSubmodule,
    ← Localization.AtPrime.map_eq_maximalIdeal (I := Representation.primeIdeal 2)] at hz
  -- Every generator coming from the mapped prime ideal is visibly a localized `2`-multiple.
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro a ha y hy
    rcases exists_algebraMap_two_mul_of_mem_prime_two_map ha with ⟨c, rfl⟩
    rw [top_stable_lattice_smul_subtype_eq, mul_smul]
    exact prime_two_localized_to_mod_two_quotient_eq_zero_of_two_smul
      (z := c • ((y : (ρ.primeStableLattice 2).toSubmodule) :
        LocalizedModule.AtPrime (Representation.primeIdeal 2) E))
  · intro y w hy hw
    simpa [map_add, hy, hw]

/-- Helper for Exercise 15-15.2-6: the detector on the lattice subtype kills the maximal-ideal
submodule, so it descends to the canonical prime-`2` reduction. -/
private theorem prime_two_localized_to_mod_two_quotient_ker_le
    (ρ : Representation ℤ G E) :
    Submodule.restrictScalars ℤ (ρ.primeStableLattice 2).maximalIdealSubmodule ≤
      (((prime_two_localized_to_mod_two_quotient).comp
        ((ρ.primeStableLattice 2).toSubmodule.subtype.restrictScalars ℤ))).ker := by
  -- The descended detector vanishes on every representative coming from the maximal-ideal
  -- multiple, so the quotient map factors through the reduction.
  intro z hz
  change prime_two_localized_to_mod_two_quotient
      ((z : (ρ.primeStableLattice 2).toSubmodule) : LocalizedModule.AtPrime
        (Representation.primeIdeal 2) E) = 0
  exact prime_two_localized_to_mod_two_quotient_eq_zero_of_mem_maximalIdeal (ρ := ρ) hz

/-- Helper for Exercise 15-15.2-6: the localization comparison descends to the canonical prime-`2`
reduction. -/
noncomputable def prime_two_reduction_to_mod_two_quotient (ρ : Representation ℤ G E) :
    (ρ.primeStableLattice 2).reduction → E ⧸ (2 •ℤ E) :=
  (Submodule.liftQ (Submodule.restrictScalars ℤ (ρ.primeStableLattice 2).maximalIdealSubmodule)
    ((prime_two_localized_to_mod_two_quotient).comp
      ((ρ.primeStableLattice 2).toSubmodule.subtype.restrictScalars ℤ))
    (prime_two_localized_to_mod_two_quotient_ker_le (ρ := ρ)) :
      (ρ.primeStableLattice 2).reduction →ₗ[ℤ] E ⧸ (2 •ℤ E))

/-- Helper for Exercise 15-15.2-6: the descended detector map sends the canonical reduction class
of an integral vector to its class in `E / 2E`. -/
private theorem prime_two_reduction_to_mod_two_quotient_apply_class
    (ρ : Representation ℤ G E) (x : E) :
    prime_two_reduction_to_mod_two_quotient (ρ := ρ)
        (prime_two_reduction_class (ρ := ρ) x) =
      Submodule.Quotient.mk x := by
  -- Evaluate the quotient descent on the represented reduction class and then compute the
  -- localization detector on the denominator-`1` representative.
  simpa [prime_two_reduction_to_mod_two_quotient, prime_two_reduction_class,
    prime_two_localized_to_mod_two_quotient_mk_one] using
    (Submodule.liftQ_apply
      (p := Submodule.restrictScalars ℤ (ρ.primeStableLattice 2).maximalIdealSubmodule)
      (f := (prime_two_localized_to_mod_two_quotient).comp
        ((ρ.primeStableLattice 2).toSubmodule.subtype.restrictScalars ℤ))
      (x := ((⟨LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl) x 1,
        Submodule.mem_top⟩) : (ρ.primeStableLattice 2).toSubmodule)))

/-- Helper for Exercise 15-15.2-6: the canonical class of `x` in the prime-`2` reduction vanishes
exactly when `x` already lies in `2E`. -/
theorem prime_two_reduction_class_eq_zero_iff_mem_two_mul
    (ρ : Representation ℤ G E) (x : E) :
    prime_two_reduction_class (ρ := ρ) x = 0 ↔ x ∈ (2 •ℤ E) := by
  constructor
  · intro hx
    -- Push the zero class through the descended detector to read it back in `E / 2E`.
    have hmap :
        (Submodule.Quotient.mk x : E ⧸ (2 •ℤ E)) =
          prime_two_reduction_to_mod_two_quotient (ρ := ρ) 0 := by
      simpa [prime_two_reduction_to_mod_two_quotient_apply_class] using
        congrArg (prime_two_reduction_to_mod_two_quotient (ρ := ρ)) hx
    have hmk : (Submodule.Quotient.mk x : E ⧸ (2 •ℤ E)) = 0 := by
      have hzero : prime_two_reduction_to_mod_two_quotient (ρ := ρ) 0 = 0 := by
        simpa [prime_two_reduction_class] using
          prime_two_reduction_to_mod_two_quotient_apply_class (ρ := ρ) (x := (0 : E))
      exact hmap.trans hzero
    exact (Submodule.Quotient.mk_eq_zero _).1 hmk
  · intro hx
    -- A vector already lying in `2E` represents the zero class in the canonical reduction.
    apply (Submodule.Quotient.mk_eq_zero _).2
    simpa [prime_two_reduction_class] using
      localized_mk_mem_maximalIdealSubmodule_of_mem_two_mul (ρ := ρ) hx

/-- Helper for Exercise 15-15.2-6: if the class of `x` is fixed modulo `2E`, then its canonical
prime-`2` reduction class is fixed under the reduction representation. -/
theorem prime_two_reduction_class_fixed_of_sub_mem_two_mul
    (ρ : Representation ℤ G E) (x : E)
    (hx_invariant : ∀ g : G, ρ g x - x ∈ (2 •ℤ E)) (g : G) :
    (ρ.primeStableLattice 2).reductionRepresentation g
        (prime_two_reduction_class (ρ := ρ) x) =
      prime_two_reduction_class (ρ := ρ) x := by
  -- Rewrite the reduced action on the represented class and compare the difference upstairs.
  unfold prime_two_reduction_class
  rw [StableLattice.reductionRepresentation_apply_mk]
  apply (Submodule.Quotient.eq _).2
  change
    (⟨LocalizedModule.map (Representation.primeIdeal 2).primeCompl (ρ g)
        (LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl) x 1),
      Submodule.mem_top⟩ : (ρ.primeStableLattice 2).toSubmodule) -
      ⟨LocalizedModule.mk (S := (Representation.primeIdeal 2).primeCompl) x 1,
        Submodule.mem_top⟩ ∈
      (ρ.primeStableLattice 2).maximalIdealSubmodule
  -- Identify the difference of the two represented classes with the class of `ρ g x - x`.
  convert localized_mk_mem_maximalIdealSubmodule_of_mem_two_mul
    (ρ := ρ) (hx_invariant g) using 1
  ext
  simp [LocalizedModule.map_mk, sub_eq_add_neg]

end IntegralLatticeAmbient

end ThompsonExercise
