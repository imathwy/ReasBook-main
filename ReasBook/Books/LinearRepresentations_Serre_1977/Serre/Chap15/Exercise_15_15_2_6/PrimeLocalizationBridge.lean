import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_6.Foundations

noncomputable section

universe u v

local notation:max p " •ℤ " E => (Representation.primeIdeal p • (⊤ : Submodule ℤ E))

section ThompsonExercise

variable {G : Type u} [Group G]
variable {E : Type v} [AddCommGroup E] [Module ℤ E]

section IntegralLatticeAmbient

variable [Module.Free ℤ E] [Module.Finite ℤ E]

attribute [local instance] Submodule.Quotient.module

/-- Helper for Exercise 15-15.2-6: the canonical class of an integral vector in the prime-`p`
reduction of `ρ.primeStableLattice p`. -/
def prime_reduction_class (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (x : E) :
    (ρ.primeStableLattice p).reduction :=
  Submodule.Quotient.mk
    ((⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1,
      Submodule.mem_top⟩) : (ρ.primeStableLattice p).toSubmodule)

/-- Helper for Exercise 15-15.2-6: canonical prime-reduction classes respect addition of
integral representatives. -/
@[simp] theorem prime_reduction_class_add
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (x y : E) :
    prime_reduction_class (ρ := ρ) p (x + y) =
      prime_reduction_class (ρ := ρ) p x + prime_reduction_class (ρ := ρ) p y := by
  unfold prime_reduction_class
  rw [← Submodule.Quotient.mk_add]
  congr 1
  ext
  simp

/-- Helper for Exercise 15-15.2-6: canonical prime-reduction classes respect negation of
integral representatives. -/
@[simp] theorem prime_reduction_class_neg
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (x : E) :
    prime_reduction_class (ρ := ρ) p (-x) =
      -prime_reduction_class (ρ := ρ) p x := by
  unfold prime_reduction_class
  rw [← Submodule.Quotient.mk_neg]
  congr 1
  ext
  simp

/-- Helper for Exercise 15-15.2-6: canonical prime-reduction classes respect the underlying
integer additive action. This is deliberately stated for the additive `ℤ`-action on the quotient,
not for the residue-field scalar action. -/
@[simp] theorem prime_reduction_class_zsmul
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (m : ℤ) (x : E) :
    prime_reduction_class (ρ := ρ) p (m • x) =
      m • prime_reduction_class (ρ := ρ) p x := by
  let q : E →+ (ρ.primeStableLattice p).reduction :=
    { toFun := prime_reduction_class (ρ := ρ) p
      map_zero' := by
        change prime_reduction_class (ρ := ρ) p (0 : E) = 0
        unfold prime_reduction_class
        apply (Submodule.Quotient.mk_eq_zero
          ((ρ.primeStableLattice p).maximalIdealSubmodule)).2
        convert Submodule.zero_mem ((ρ.primeStableLattice p).maximalIdealSubmodule) using 1
        ext
        simp
      map_add' := by
        intro a b
        exact prime_reduction_class_add (ρ := ρ) p a b }
  rw [← int_smul_eq_zsmul (h := (inferInstance : Module ℤ E)) (n := m) (x := x)]
  simpa [q, RingHom.id_apply] using map_intCast_smul q ℤ ℤ m x

/-- Helper for Exercise 15-15.2-6: integer scalar actions commute on `E`. -/
private instance int_smulCommClass_on_E_general : SMulCommClass ℤ ℤ E where
  smul_comm a b z := by
    simp [smul_smul, mul_comm]

/-- Helper for Exercise 15-15.2-6: the quotient map `E → E / pE` as a `ℤ`-linear map. -/
private def prime_mod_quotient_linearMap (p : ℕ) [Fact p.Prime] :
    E →ₗ[ℤ] E ⧸ (p •ℤ E) where
  toFun := Submodule.Quotient.mk
  map_add' := by simp
  map_smul' := by
    intro m x
    let q : E →+ E ⧸ (p •ℤ E) :=
      { toFun := Submodule.Quotient.mk
        map_zero' := by simp
        map_add' := by simp }
    simpa [q, RingHom.id_apply] using map_intCast_smul q ℤ ℤ m x

/-- Helper for Exercise 15-15.2-6: every denominator away from `(p)` acts invertibly on
`E / pE`. -/
private theorem prime_denominator_isUnit_on_mod_quotient
    (p : ℕ) [Fact p.Prime] (s : (Representation.primeIdeal p).primeCompl) :
    IsUnit ((algebraMap ℤ (Module.End ℤ (E ⧸ (p •ℤ E)))) (s : ℤ)) := by
  letI : Field (ℤ ⧸ Representation.primeIdeal p) :=
    Ideal.Quotient.field (Representation.primeIdeal p)
  have hsq : IsUnit ((Ideal.Quotient.mk (Representation.primeIdeal p)) (s : ℤ)) := by
    rw [isUnit_iff_ne_zero]
    intro hs0
    exact s.2 ((Ideal.Quotient.eq_zero_iff_mem).1 hs0)
  have hs_end :
      IsUnit ((algebraMap (ℤ ⧸ Representation.primeIdeal p)
          (Module.End (ℤ ⧸ Representation.primeIdeal p) (E ⧸ (p •ℤ E))))
        ((Ideal.Quotient.mk (Representation.primeIdeal p)) (s : ℤ))) :=
    hsq.map _
  let restrictScalarsEnd :
      Module.End (ℤ ⧸ Representation.primeIdeal p) (E ⧸ (p •ℤ E)) →+*
        Module.End ℤ (E ⧸ (p •ℤ E)) :=
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
  simpa [restrictScalarsEnd] using hs_end.map restrictScalarsEnd

/-- Helper for Exercise 15-15.2-6: the mod-`p` quotient is annihilated by multiplication by `p`. -/
private theorem prime_smul_eq_zero_on_mod_quotient
    (p : ℕ) [Fact p.Prime] (q : E ⧸ (p •ℤ E)) :
    (p : ℤ) • q = 0 := by
  refine Quotient.inductionOn' q ?_
  intro y
  change Submodule.Quotient.mk ((p : ℤ) • y) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  rw [show (p •ℤ E) = Representation.primeIdeal p • (⊤ : Submodule ℤ E) by rfl,
    Representation.primeIdeal, Submodule.ideal_span_singleton_smul]
  refine ⟨y, by simp, ?_⟩
  rw [← Int.cast_smul_eq_zsmul (R := ℤ) (n := (p : ℤ)) (b := y)]
  simp [LinearMap.lsmul_apply]

/-- Helper for Exercise 15-15.2-6: the integral action of `G` preserves the ordinary quotient
submodule `pE`. This is the source-facing mod-`p` quotient used by Serre before it is compared
with the canonical local-lattice reduction. -/
private theorem prime_mul_le_comap
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (g : G) :
    (p •ℤ E) ≤ (p •ℤ E).comap (ρ g) := by
  intro x hx
  rw [show (p •ℤ E) = Representation.primeIdeal p • (⊤ : Submodule ℤ E) by rfl] at hx ⊢
  rw [Representation.primeIdeal, Submodule.ideal_span_singleton_smul] at hx ⊢
  rcases hx with ⟨y, hy, rfl⟩
  refine ⟨ρ g y, by simp, ?_⟩
  simp

/-- Helper for Exercise 15-15.2-6: the action of one group element on the ordinary quotient
`E / pE`, first as an integral-linear map. The residue-field scalar structure is already present
on the quotient; this lighter map records the group action without forcing that scalar bridge at
every use site. -/
private noncomputable def prime_mod_quotient_action
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (g : G) :
    E ⧸ (p •ℤ E) →ₗ[ℤ] E ⧸ (p •ℤ E) :=
  Submodule.mapQ (p •ℤ E) (p •ℤ E) (ρ g) (prime_mul_le_comap ρ p g)

/-- Helper for Exercise 15-15.2-6: the reduced action sends the class of a vector to the class of
its integral translate. This keeps the quotient-constructor spelling out of later proofs. -/
private theorem prime_mod_quotient_action_apply_mk
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (g : G) (x : E) :
    prime_mod_quotient_action (ρ := ρ) p g
        (Submodule.Quotient.mk x : E ⧸ (p •ℤ E)) =
      Submodule.Quotient.mk (ρ g x) := by
  change Submodule.mapQ (p •ℤ E) (p •ℤ E) (ρ g) (prime_mul_le_comap ρ p g)
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x)
  rw [Submodule.mapQ_apply]

/-- Helper for Exercise 15-15.2-6: the ordinary quotient `E / pE` carries the mod-`p`
representation obtained by reducing the integral action. This is the representation appearing
explicitly in Serre's hypothesis. -/
noncomputable def prime_mod_quotient_representation
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    Representation ℤ G (E ⧸ (p •ℤ E)) where
  toFun g := prime_mod_quotient_action (ρ := ρ) p g
  map_one' := by
    ext x
    refine Quotient.inductionOn' x ?_
    intro y
    simpa using prime_mod_quotient_action_apply_mk (ρ := ρ) p 1 y
  map_mul' g h := by
    ext x
    refine Quotient.inductionOn' x ?_
    intro y
    change
      prime_mod_quotient_action (ρ := ρ) p (g * h)
          (Submodule.Quotient.mk y : E ⧸ (p •ℤ E)) =
        (prime_mod_quotient_action (ρ := ρ) p g *
            prime_mod_quotient_action (ρ := ρ) p h)
          (Submodule.Quotient.mk y : E ⧸ (p •ℤ E))
    rw [prime_mod_quotient_action_apply_mk]
    change Submodule.Quotient.mk ((ρ (g * h)) y) =
      prime_mod_quotient_action (ρ := ρ) p g
        (prime_mod_quotient_action (ρ := ρ) p h
          (Submodule.Quotient.mk y : E ⧸ (p •ℤ E)))
    rw [prime_mod_quotient_action_apply_mk]
    rw [prime_mod_quotient_action_apply_mk]
    simp [map_mul]

/-- Helper for Exercise 15-15.2-6: on represented classes, the ordinary mod-`p` quotient action is
the class of the integral action. -/
@[simp] theorem prime_mod_quotient_representation_apply_mk
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (g : G) (x : E) :
    prime_mod_quotient_representation (ρ := ρ) p g
        (Submodule.Quotient.mk x : E ⧸ (p •ℤ E)) =
      Submodule.Quotient.mk (ρ g x) := by
  rw [show prime_mod_quotient_representation (ρ := ρ) p g =
      prime_mod_quotient_action (ρ := ρ) p g by rfl]
  exact prime_mod_quotient_action_apply_mk (ρ := ρ) p g x

/-- Helper for Exercise 15-15.2-6: scalar multiplication in the top stable lattice agrees with the
ambient localized scalar multiplication after forgetting the subtype. -/
private theorem prime_top_stable_lattice_smul_subtype_eq
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime]
    (a : Localization.AtPrime (Representation.primeIdeal p))
    (z : (ρ.primeStableLattice p).toSubmodule) :
    (((a • z : (ρ.primeStableLattice p).toSubmodule) :
        (ρ.primeStableLattice p).toSubmodule) :
      LocalizedModule.AtPrime (Representation.primeIdeal p) E) =
      a • (z : LocalizedModule.AtPrime (Representation.primeIdeal p) E) := by
  rfl

/-- Helper for Exercise 15-15.2-6: the quotient map `E → E / pE` extends across localization at
the prime ideal `(p)`. -/
private noncomputable def prime_localized_to_mod_quotient
    (p : ℕ) [Fact p.Prime] :
    LocalizedModule.AtPrime (Representation.primeIdeal p) E →ₗ[ℤ] E ⧸ (p •ℤ E) :=
  { toFun :=
      LocalizedModule.lift (S := (Representation.primeIdeal p).primeCompl)
        (prime_mod_quotient_linearMap (E := E) p)
        (prime_denominator_isUnit_on_mod_quotient (E := E) p)
    map_add' := by
      intro z w
      simpa using
        (LocalizedModule.lift (S := (Representation.primeIdeal p).primeCompl)
          (prime_mod_quotient_linearMap (E := E) p)
          (prime_denominator_isUnit_on_mod_quotient (E := E) p)).map_add z w
    map_smul' := by
      intro r z
      simpa using
        (LocalizedModule.lift (S := (Representation.primeIdeal p).primeCompl)
          (prime_mod_quotient_linearMap (E := E) p)
          (prime_denominator_isUnit_on_mod_quotient (E := E) p)).map_smul r z }

/-- Helper for Exercise 15-15.2-6: the localization comparison sends an integral vector to its
class modulo `pE`. -/
private theorem prime_localized_to_mod_quotient_mk_one
    (p : ℕ) [Fact p.Prime] (x : E) :
    prime_localized_to_mod_quotient (E := E) p
        (LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1) =
      Submodule.Quotient.mk x := by
  simpa [prime_localized_to_mod_quotient, prime_mod_quotient_linearMap] using
    (LocalizedModule.lift_mk_one (S := (Representation.primeIdeal p).primeCompl)
      (g := prime_mod_quotient_linearMap (E := E) p)
      (h := prime_denominator_isUnit_on_mod_quotient (E := E) p) x)

/-- Helper for Exercise 15-15.2-6: multiplying a denominator-`1` localized class by the image of
`p` is the same as localizing the `p`-multiple of the integral vector. -/
private theorem prime_localized_smul_mk_one
    (p : ℕ) [Fact p.Prime] (y : E) :
    (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) (p : ℤ)) •
        LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) y 1 =
      LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) ((p : ℤ) • y) 1 := by
  change
    Localization.mk (p : ℤ) (1 : (Representation.primeIdeal p).primeCompl) •
        LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) y 1 =
      LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) ((p : ℤ) • y) 1
  rw [← int_smul_eq_zsmul (h := (inferInstance : Module ℤ E)) (n := (p : ℤ)) (x := y)]
  simpa using
    (LocalizedModule.mk_smul_mk (S := (Representation.primeIdeal p).primeCompl)
      (r := (p : ℤ)) (m := y) (s := (1 : (Representation.primeIdeal p).primeCompl))
      (t := (1 : (Representation.primeIdeal p).primeCompl)))

/-- Helper for Exercise 15-15.2-6: after mapping `(p)` into the prime-`p` localization, the image
ideal is still generated by the image of `p`. -/
private theorem prime_map_eq_span_singleton
    (p : ℕ) [Fact p.Prime] :
    Ideal.map (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)))
      (Representation.primeIdeal p) =
    Ideal.span ({algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) (p : ℤ)} :
      Set (Localization.AtPrime (Representation.primeIdeal p))) := by
  simpa [Representation.primeIdeal] using
    (Ideal.map_span (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)))
      ({(p : ℤ)} : Set ℤ))

/-- Helper for Exercise 15-15.2-6: every element of the localized image of `(p)` is visibly a
multiple of `p` in the localization ring. -/
private theorem exists_algebraMap_prime_mul_of_mem_prime_map
    (p : ℕ) [Fact p.Prime]
    {r : Localization.AtPrime (Representation.primeIdeal p)}
    (hr : r ∈ Ideal.map (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)))
      (Representation.primeIdeal p)) :
    ∃ c : Localization.AtPrime (Representation.primeIdeal p),
      r = algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) (p : ℤ) * c := by
  rw [prime_map_eq_span_singleton p] at hr
  rw [Ideal.mem_span_singleton] at hr
  rcases hr with ⟨c, rfl⟩
  exact ⟨c, rfl⟩

/-- Helper for Exercise 15-15.2-6: an integral vector lying in `pE` is literally a `p`-multiple in
the integral module. -/
private theorem exists_prime_smul_eq_of_mem_prime_mul
    (p : ℕ) [Fact p.Prime] {x : E} (hx : x ∈ (p •ℤ E)) :
    ∃ y : E, x = (p : ℤ) • y := by
  let primeRange : Submodule ℤ E :=
    Submodule.map ((LinearMap.lsmul ℤ E) (p : ℤ)) ⊤
  have hprime :
      (p •ℤ E) ≤ primeRange := by
    rw [show (p •ℤ E) = Representation.primeIdeal p • (⊤ : Submodule ℤ E) by rfl]
    rw [Submodule.smul_eq_map₂, Submodule.map₂]
    refine iSup_le ?_
    intro r
    intro z hz
    rcases hz with ⟨y, -, rfl⟩
    have hr : (r : ℤ) ∈ Representation.primeIdeal p := r.property
    change (r : ℤ) ∈ Ideal.span ({(p : ℤ)} : Set ℤ) at hr
    rw [Ideal.mem_span_singleton] at hr
    rcases hr with ⟨c, hc⟩
    refine ⟨c • y, by trivial, ?_⟩
    calc
      ((LinearMap.lsmul ℤ E) (p : ℤ)) (c • y)
          = c • ((p : ℤ) • y) := by
              calc
                ((LinearMap.lsmul ℤ E) (p : ℤ)) (c • y)
                    = c • (((LinearMap.lsmul ℤ E) (p : ℤ)) y) := by
                        simpa only [LinearMap.map_smul_of_tower]
                _ = c • ((p : ℤ) • y) := by
                      congr 1
                      rw [← Int.cast_smul_eq_zsmul (R := ℤ) (n := (p : ℤ)) (b := y)]
                      simp [LinearMap.lsmul_apply]
      _ = (c * (p : ℤ)) • y := by
            simpa using (mul_zsmul y c (p : ℤ)).symm
      _ = (r : ℤ) • y := by
            rw [hc, mul_comm]
      _ = ((LinearMap.lsmul ℤ E) (r : ℤ)) y := by
            rw [← Int.cast_smul_eq_zsmul (R := ℤ) (n := r) (b := y)]
            simp [LinearMap.lsmul_apply]
  have hx_prime : x ∈ primeRange := hprime hx
  rcases hx_prime with ⟨y, -, hy⟩
  refine ⟨y, ?_⟩
  rw [← Int.cast_smul_eq_zsmul (R := ℤ) (n := (p : ℤ)) (b := y)]
  simpa [primeRange, LinearMap.lsmul_apply] using hy.symm

/-- Helper for Exercise 15-15.2-6: an integral vector in `pE` becomes a visible localized
`p`-multiple with denominator `1`. -/
private theorem localized_mk_eq_prime_smul_mk_one_of_mem_prime_mul
    (p : ℕ) [Fact p.Prime] {x : E} (hx : x ∈ (p •ℤ E)) :
    ∃ y : E,
      LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1 =
        (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) (p : ℤ)) •
          LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) y 1 := by
  rcases exists_prime_smul_eq_of_mem_prime_mul (E := E) p hx with ⟨y, rfl⟩
  refine ⟨y, ?_⟩
  simpa using (prime_localized_smul_mk_one (E := E) p y).symm

/-- Helper for Exercise 15-15.2-6: an integral vector lying in `pE` maps to the maximal-ideal
submodule of the canonical prime-`p` lattice. -/
private theorem localized_mk_mem_maximalIdealSubmodule_of_mem_prime_mul
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] {x : E} (hx : x ∈ (p •ℤ E)) :
    ((⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1,
      Submodule.mem_top⟩) : (ρ.primeStableLattice p).toSubmodule) ∈
      (ρ.primeStableLattice p).maximalIdealSubmodule := by
  rw [StableLattice.maximalIdealSubmodule, Submodule.mem_smul_top_iff]
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := Representation.primeIdeal p)]
  rw [prime_map_eq_span_singleton p, Submodule.ideal_span_singleton_smul]
  rcases localized_mk_eq_prime_smul_mk_one_of_mem_prime_mul (E := E) p hx with ⟨y, hy⟩
  rw [hy]
  refine ⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) y 1,
    by simpa [Representation.primeStableLattice], ?_⟩
  rfl

/-- Helper for Exercise 15-15.2-6: an integral vector in `pE`, represented with an arbitrary
prime-local denominator, maps to the maximal-ideal submodule of the canonical prime-`p` lattice. -/
theorem localized_mk_mem_maximalIdealSubmodule_of_mem_prime_mul_denom
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime]
    {x : E} (s : (Representation.primeIdeal p).primeCompl) (hx : x ∈ (p •ℤ E)) :
    ((⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x s,
      Submodule.mem_top⟩) : (ρ.primeStableLattice p).toSubmodule) ∈
      (ρ.primeStableLattice p).maximalIdealSubmodule := by
  rw [StableLattice.maximalIdealSubmodule, Submodule.mem_smul_top_iff]
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := Representation.primeIdeal p)]
  rw [prime_map_eq_span_singleton p, Submodule.ideal_span_singleton_smul]
  rcases exists_prime_smul_eq_of_mem_prime_mul (E := E) p hx with ⟨y, rfl⟩
  refine ⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) y s,
    by simpa [Representation.primeStableLattice], ?_⟩
  change
    (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) (p : ℤ)) •
        LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) y s =
      LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) ((p : ℤ) • y) s
  change
    Localization.mk (p : ℤ) (1 : (Representation.primeIdeal p).primeCompl) •
        LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) y s =
      LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) ((p : ℤ) • y) s
  rw [← int_smul_eq_zsmul (h := (inferInstance : Module ℤ E)) (n := (p : ℤ)) (x := y)]
  simpa using
    (LocalizedModule.mk_smul_mk (S := (Representation.primeIdeal p).primeCompl)
      (r := (p : ℤ)) (m := y)
      (s := (1 : (Representation.primeIdeal p).primeCompl)) (t := s))

/-- Helper for Exercise 15-15.2-6: the localization detector kills a represented localized
`p`-multiple. -/
private theorem prime_localized_to_mod_quotient_mk_prime_zero
    (p : ℕ) [Fact p.Prime] (m : E) (s : (Representation.primeIdeal p).primeCompl) :
    prime_localized_to_mod_quotient (E := E) p
        (LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl)
          ((LinearMap.lsmul ℤ E (p : ℤ)) m) s) = 0 := by
  change
    LocalizedModule.lift (S := (Representation.primeIdeal p).primeCompl)
        (prime_mod_quotient_linearMap (E := E) p)
        (prime_denominator_isUnit_on_mod_quotient (E := E) p)
        (LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl)
          ((LinearMap.lsmul ℤ E (p : ℤ)) m) s) = 0
  rw [LocalizedModule.lift_mk]
  simpa [prime_mod_quotient_linearMap] using
    prime_smul_eq_zero_on_mod_quotient (E := E) p
      (q := ((prime_denominator_isUnit_on_mod_quotient (E := E) p s).unit⁻¹.val
        (prime_mod_quotient_linearMap (E := E) p m)))

/-- Helper for Exercise 15-15.2-6: the localization detector kills any visible localized multiple
of the image of `p`. -/
private theorem prime_localized_to_mod_quotient_eq_zero_of_prime_smul
    (p : ℕ) [Fact p.Prime]
    (z : LocalizedModule.AtPrime (Representation.primeIdeal p) E) :
    prime_localized_to_mod_quotient (E := E) p
        ((algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) (p : ℤ)) • z) = 0 := by
  refine LocalizedModule.induction_on
    (β := fun z =>
      prime_localized_to_mod_quotient (E := E) p
          ((algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) (p : ℤ)) • z) = 0)
    ?_ z
  intro m s
  change
    prime_localized_to_mod_quotient (E := E) p
        ((Localization.mk (p : ℤ) (1 : (Representation.primeIdeal p).primeCompl)) •
          LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) m s) = 0
  rw [LocalizedModule.mk_smul_mk]
  simpa using prime_localized_to_mod_quotient_mk_prime_zero (E := E) p m s

/-- Helper for Exercise 15-15.2-6: the localization comparison kills the maximal-ideal multiple
inside the canonical prime-`p` lattice. -/
private theorem prime_localized_to_mod_quotient_eq_zero_of_mem_maximalIdeal
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime]
    {z : (ρ.primeStableLattice p).toSubmodule}
    (hz : z ∈ (ρ.primeStableLattice p).maximalIdealSubmodule) :
    prime_localized_to_mod_quotient (E := E) p
        (z : LocalizedModule.AtPrime (Representation.primeIdeal p) E) = 0 := by
  rw [StableLattice.maximalIdealSubmodule,
    ← Localization.AtPrime.map_eq_maximalIdeal (I := Representation.primeIdeal p)] at hz
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro a ha y hy
    rcases exists_algebraMap_prime_mul_of_mem_prime_map p ha with ⟨c, rfl⟩
    rw [prime_top_stable_lattice_smul_subtype_eq, mul_smul]
    exact prime_localized_to_mod_quotient_eq_zero_of_prime_smul
      (E := E) p
      (z := c • ((y : (ρ.primeStableLattice p).toSubmodule) :
        LocalizedModule.AtPrime (Representation.primeIdeal p) E))
  · intro y w hy hw
    simpa [map_add, hy, hw]

/-- Helper for Exercise 15-15.2-6: the detector on the lattice subtype kills the maximal-ideal
submodule, so it descends to the canonical prime-`p` reduction. -/
private theorem prime_localized_to_mod_quotient_ker_le
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    Submodule.restrictScalars ℤ (ρ.primeStableLattice p).maximalIdealSubmodule ≤
      (((prime_localized_to_mod_quotient (E := E) p).comp
        ((ρ.primeStableLattice p).toSubmodule.subtype.restrictScalars ℤ))).ker := by
  intro z hz
  change prime_localized_to_mod_quotient (E := E) p
      ((z : (ρ.primeStableLattice p).toSubmodule) :
        LocalizedModule.AtPrime (Representation.primeIdeal p) E) = 0
  exact prime_localized_to_mod_quotient_eq_zero_of_mem_maximalIdeal (ρ := ρ) p hz

/-- Helper for Exercise 15-15.2-6: the localization comparison descends to the canonical prime-`p`
reduction. -/
noncomputable def prime_reduction_to_mod_quotient
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    (ρ.primeStableLattice p).reduction → E ⧸ (p •ℤ E) :=
  (Submodule.liftQ (Submodule.restrictScalars ℤ (ρ.primeStableLattice p).maximalIdealSubmodule)
    ((prime_localized_to_mod_quotient (E := E) p).comp
      ((ρ.primeStableLattice p).toSubmodule.subtype.restrictScalars ℤ))
    (prime_localized_to_mod_quotient_ker_le (ρ := ρ) p) :
      (ρ.primeStableLattice p).reduction →ₗ[ℤ] E ⧸ (p •ℤ E))

/-- Helper for Exercise 15-15.2-6: the descended detector map sends the canonical reduction class
of an integral vector to its class in `E / pE`. -/
@[simp] theorem prime_reduction_to_mod_quotient_apply_class
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (x : E) :
    prime_reduction_to_mod_quotient (ρ := ρ) p
        (prime_reduction_class (ρ := ρ) p x) =
      Submodule.Quotient.mk x := by
  simpa [prime_reduction_to_mod_quotient, prime_reduction_class,
    prime_localized_to_mod_quotient_mk_one] using
    (Submodule.liftQ_apply
      (p := Submodule.restrictScalars ℤ (ρ.primeStableLattice p).maximalIdealSubmodule)
      (f := (prime_localized_to_mod_quotient (E := E) p).comp
        ((ρ.primeStableLattice p).toSubmodule.subtype.restrictScalars ℤ))
      (x := ((⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1,
        Submodule.mem_top⟩) : (ρ.primeStableLattice p).toSubmodule)))

/-- Helper for Exercise 15-15.2-6: the comparison from the canonical prime-local reduction to
the source-facing ordinary quotient `E / pE` is surjective. -/
theorem prime_reduction_to_mod_quotient_surjective
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    Function.Surjective (prime_reduction_to_mod_quotient (ρ := ρ) p) := by
  intro q
  rcases Submodule.Quotient.mk_surjective (p •ℤ E) q with ⟨x, rfl⟩
  exact ⟨prime_reduction_class (ρ := ρ) p x, by simp⟩

/-- Helper for Exercise 15-15.2-6: the comparison from the canonical prime-local reduction to
the ordinary quotient `E / pE` is injective. -/
theorem prime_reduction_to_mod_quotient_injective
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    Function.Injective (prime_reduction_to_mod_quotient (ρ := ρ) p) := by
  let fLin :
      (ρ.primeStableLattice p).reduction →ₗ[ℤ] E ⧸ (p •ℤ E) :=
    (Submodule.liftQ (Submodule.restrictScalars ℤ (ρ.primeStableLattice p).maximalIdealSubmodule)
      ((prime_localized_to_mod_quotient (E := E) p).comp
        ((ρ.primeStableLattice p).toSubmodule.subtype.restrictScalars ℤ))
      (prime_localized_to_mod_quotient_ker_le (ρ := ρ) p) :
        (ρ.primeStableLattice p).reduction →ₗ[ℤ] E ⧸ (p •ℤ E))
  have hfLin :
      ∀ ξ, fLin ξ = prime_reduction_to_mod_quotient (ρ := ρ) p ξ := by
    intro ξ
    rfl
  have hker :
      ∀ ξ, fLin ξ = 0 → ξ = 0 := by
    intro ξ
    refine Quotient.inductionOn' ξ ?_
    intro z hz
    have hzlocal :
        prime_localized_to_mod_quotient (E := E) p
            ((z : (ρ.primeStableLattice p).toSubmodule) :
              LocalizedModule.AtPrime (Representation.primeIdeal p) E) = 0 := by
      simpa [fLin] using hz
    change
      (Submodule.Quotient.mk z :
        (ρ.primeStableLattice p).reduction) = 0
    refine LocalizedModule.induction_on
      (β := fun w =>
        prime_localized_to_mod_quotient (E := E) p w = 0 →
          (Submodule.Quotient.mk
            ((⟨w, Submodule.mem_top⟩) : (ρ.primeStableLattice p).toSubmodule) :
              (ρ.primeStableLattice p).reduction) = 0)
      ?_ ((z : (ρ.primeStableLattice p).toSubmodule) :
        LocalizedModule.AtPrime (Representation.primeIdeal p) E) hzlocal
    intro x s hs
    change
      LocalizedModule.lift (S := (Representation.primeIdeal p).primeCompl)
          (prime_mod_quotient_linearMap (E := E) p)
          (prime_denominator_isUnit_on_mod_quotient (E := E) p)
          (LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x s) = 0 at hs
    rw [LocalizedModule.lift_mk] at hs
    let q : E ⧸ (p •ℤ E) := prime_mod_quotient_linearMap (E := E) p x
    let u : (Module.End ℤ (E ⧸ (p •ℤ E)))ˣ :=
      (prime_denominator_isUnit_on_mod_quotient (E := E) p s).unit
    have hs' :
        (((u⁻¹ : (Module.End ℤ (E ⧸ (p •ℤ E)))ˣ) :
            Module.End ℤ (E ⧸ (p •ℤ E))) q) = 0 := by
      simpa [q, u] using hs
    have hx_zero :
        (prime_mod_quotient_linearMap (E := E) p x) = 0 := by
      change q = 0
      calc
        q = ((1 : Module.End ℤ (E ⧸ (p •ℤ E))) q) := rfl
        _ =
            (((u * u⁻¹ : (Module.End ℤ (E ⧸ (p •ℤ E)))ˣ) :
              Module.End ℤ (E ⧸ (p •ℤ E))) q) := by simp
        _ = ((u : Module.End ℤ (E ⧸ (p •ℤ E)))
              (((u⁻¹ : (Module.End ℤ (E ⧸ (p •ℤ E)))ˣ) :
                Module.End ℤ (E ⧸ (p •ℤ E))) q)) := rfl
        _ = 0 := by rw [hs']; simp
    have hx_mem : x ∈ (p •ℤ E) := by
      exact (Submodule.Quotient.mk_eq_zero (p •ℤ E)).1 (by
        simpa [prime_mod_quotient_linearMap] using hx_zero)
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact localized_mk_mem_maximalIdealSubmodule_of_mem_prime_mul_denom
      (ρ := ρ) p s hx_mem
  intro ξ η hξη
  rw [← sub_eq_zero]
  apply hker
  rw [map_sub]
  rw [hfLin ξ, hfLin η, hξη, sub_self]

/-- Helper for Exercise 15-15.2-6: every canonical prime-reduction class has an integral
representative. -/
theorem prime_reduction_class_surjective
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] :
    Function.Surjective (prime_reduction_class (ρ := ρ) p) := by
  intro ξ
  obtain ⟨x, hx⟩ :=
    Submodule.Quotient.mk_surjective (p •ℤ E)
      (prime_reduction_to_mod_quotient (ρ := ρ) p ξ)
  refine ⟨x, ?_⟩
  apply prime_reduction_to_mod_quotient_injective (ρ := ρ) p
  simpa [prime_reduction_to_mod_quotient_apply_class, hx]

/-- Helper for Exercise 15-15.2-6: the canonical class of `x` in the prime-`p` reduction vanishes
exactly when `x` already lies in `pE`. -/
theorem prime_reduction_class_eq_zero_iff_mem_prime_mul
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (x : E) :
    prime_reduction_class (ρ := ρ) p x = 0 ↔ x ∈ (p •ℤ E) := by
  constructor
  · intro hx
    have hmap :
        (Submodule.Quotient.mk x : E ⧸ (p •ℤ E)) =
          prime_reduction_to_mod_quotient (ρ := ρ) p 0 := by
      simpa [prime_reduction_to_mod_quotient_apply_class] using
        congrArg (prime_reduction_to_mod_quotient (ρ := ρ) p) hx
    have hmk : (Submodule.Quotient.mk x : E ⧸ (p •ℤ E)) = 0 := by
      have hzero : prime_reduction_to_mod_quotient (ρ := ρ) p 0 = 0 := by
        simpa [prime_reduction_class] using
          prime_reduction_to_mod_quotient_apply_class (ρ := ρ) p (x := (0 : E))
      exact hmap.trans hzero
    exact (Submodule.Quotient.mk_eq_zero _).1 hmk
  · intro hx
    apply (Submodule.Quotient.mk_eq_zero _).2
    simpa [prime_reduction_class] using
      localized_mk_mem_maximalIdealSubmodule_of_mem_prime_mul (ρ := ρ) p hx

/-- Helper for Exercise 15-15.2-6: equality of canonical prime-reduction classes is the same as
membership of the difference in `pE`. -/
theorem prime_reduction_class_eq_iff_sub_mem_prime_mul
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (x y : E) :
    prime_reduction_class (ρ := ρ) p x = prime_reduction_class (ρ := ρ) p y ↔
      x - y ∈ (p •ℤ E) := by
  constructor
  · intro hxy
    have hmem :
        ((⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1,
          Submodule.mem_top⟩ : (ρ.primeStableLattice p).toSubmodule) -
          ⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) y 1,
            Submodule.mem_top⟩) ∈
          (ρ.primeStableLattice p).maximalIdealSubmodule := by
      simpa [prime_reduction_class] using (Submodule.Quotient.eq _).1 hxy
    have hdiff :
        prime_reduction_class (ρ := ρ) p (x - y) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).2
      convert hmem using 1
      ext
      simp [sub_eq_add_neg]
    exact (prime_reduction_class_eq_zero_iff_mem_prime_mul (ρ := ρ) p (x - y)).1 hdiff
  · intro hxy
    have hdiff :
        prime_reduction_class (ρ := ρ) p (x - y) = 0 :=
      (prime_reduction_class_eq_zero_iff_mem_prime_mul (ρ := ρ) p (x - y)).2 hxy
    have hmem :
        (⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) (x - y) 1,
          Submodule.mem_top⟩ : (ρ.primeStableLattice p).toSubmodule) ∈
          (ρ.primeStableLattice p).maximalIdealSubmodule := by
      exact (Submodule.Quotient.mk_eq_zero _).1 (by simpa [prime_reduction_class] using hdiff)
    rw [← sub_eq_zero]
    apply (Submodule.Quotient.mk_eq_zero _).2
    convert hmem using 1
    ext
    simp [sub_eq_add_neg]

/-- Helper for Exercise 15-15.2-6: the reduced action sends the canonical class of an integral
vector to the canonical class of its image. -/
theorem prime_reduction_class_map
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] (g : G) (x : E) :
    (ρ.primeStableLattice p).reductionRepresentation g
        (prime_reduction_class (ρ := ρ) p x) =
      prime_reduction_class (ρ := ρ) p (ρ g x) := by
  unfold prime_reduction_class
  rw [StableLattice.reductionRepresentation_apply_mk]
  congr 1
  ext
  simp [Representation.localizedAtPrime, LocalizedModule.map_mk]

/-- Helper for Exercise 15-15.2-6: membership in the ordinary submodule `pE` is the same as
being an explicit integral `p`-multiple. -/
theorem mem_prime_mul_iff_exists_prime_smul
    (p : ℕ) [Fact p.Prime] (x : E) :
    x ∈ (p •ℤ E) ↔ ∃ y : E, x = (p : ℤ) • y := by
  constructor
  · exact exists_prime_smul_eq_of_mem_prime_mul (E := E) p
  · rintro ⟨y, rfl⟩
    rw [show (p •ℤ E) = Representation.primeIdeal p • (⊤ : Submodule ℤ E) by rfl,
      Representation.primeIdeal, Submodule.ideal_span_singleton_smul]
    refine ⟨y, by simp, ?_⟩
    rw [← Int.cast_smul_eq_zsmul (R := ℤ) (n := (p : ℤ)) (b := y)]
    simp [LinearMap.lsmul_apply]

/-- Helper for Exercise 15-15.2-6: every residue-field scalar acting on an integral canonical
prime-reduction class is represented by multiplication by some integer on the integral
representative. -/
theorem prime_reduction_class_residue_smul_exists_int
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime]
    (c : IsLocalRing.ResidueField (Localization.AtPrime (Representation.primeIdeal p)))
    (x : E) :
    ∃ m : ℤ,
      c • prime_reduction_class (ρ := ρ) p x =
        prime_reduction_class (ρ := ρ) p (m • x) := by
  let e :
      ℤ ⧸ Representation.primeIdeal p ≃+*
        Localization.AtPrime (Representation.primeIdeal p) ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime (Representation.primeIdeal p)) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal (Representation.primeIdeal p)
      (Localization.AtPrime (Representation.primeIdeal p))
  obtain ⟨m, hm⟩ := Ideal.Quotient.mk_surjective (I := Representation.primeIdeal p) (e.symm c)
  refine ⟨m, ?_⟩
  let z : (ρ.primeStableLattice p).toSubmodule :=
    ⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1,
      Submodule.mem_top⟩
  have hc :
      c =
        (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (Localization.AtPrime (Representation.primeIdeal p))))
          (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) m) := by
    calc
      c = e (e.symm c) := by simp [e]
      _ = e (Ideal.Quotient.mk (Representation.primeIdeal p) m) := by rw [hm]
      _ =
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal (Localization.AtPrime (Representation.primeIdeal p))))
            (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) m) := by
            simp [e]
  have hsmul :=
    (StableLattice.reduction_smul_mk
      (L := ρ.primeStableLattice p)
      (a := algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) m)
      (y := z))
  change c • (Submodule.Quotient.mk z : (ρ.primeStableLattice p).reduction) =
    prime_reduction_class (ρ := ρ) p (m • x)
  rw [hc]
  refine hsmul.trans ?_
  unfold prime_reduction_class
  congr 1
  ext
  change
    (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) m) •
        LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1 =
      LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) (m • x) 1
  change
    Localization.mk m (1 : (Representation.primeIdeal p).primeCompl) •
        LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1 =
      LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) (m • x) 1
  rw [← int_smul_eq_zsmul (h := (inferInstance : Module ℤ E)) (n := m) (x := x)]
  simpa using
    (LocalizedModule.mk_smul_mk (S := (Representation.primeIdeal p).primeCompl)
      (r := m) (m := x) (s := (1 : (Representation.primeIdeal p).primeCompl))
      (t := (1 : (Representation.primeIdeal p).primeCompl)))

end IntegralLatticeAmbient

end ThompsonExercise
