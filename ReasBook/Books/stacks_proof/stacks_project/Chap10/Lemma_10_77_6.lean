import Mathlib
import StacksProject_2024.Chap10.Definition_10_32_1
import StacksProject_2024.Chap10.Lemma_10_32_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {Pbar : Type v} [AddCommGroup Pbar] [Module (R ⧸ I) Pbar]

/-- Helper for Lemma 10.77.6: a finite projective module over a commutative ring is a direct
summand of a finite free module. -/
lemma exists_split_finite_free_of_finite_projective
    [Module.Finite (R ⧸ I) Pbar] [Module.Projective (R ⧸ I) Pbar] :
    ∃ n : ℕ,
      ∃ π : (Fin n → R ⧸ I) →ₗ[R ⧸ I] Pbar,
        ∃ ι : Pbar →ₗ[R ⧸ I] (Fin n → R ⧸ I),
          Function.Surjective π ∧ π.comp ι = LinearMap.id := by
  -- A finite projective module is a retract of a finite free module.
  obtain ⟨n, π, ι, hπsurj, -, hsplit⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (R := R ⧸ I) (M := Pbar)
  exact ⟨n, π, ι, hπsurj, hsplit⟩

/-- Helper for Lemma 10.77.6: a finitely generated subideal of a locally nilpotent ideal is
nilpotent. -/
lemma isNilpotent_of_fg_le_of_isLocallyNilpotent {J : Ideal R}
    (hJfg : J.FG) (hJI : J ≤ I) (hI : I.IsLocallyNilpotent) :
    IsNilpotent J := by
  -- Local nilpotence puts every element of `J` in the nilradical, so finite generation upgrades
  -- the elementwise nilpotence to nilpotence of the whole ideal.
  have hJrad : J ≤ Ideal.radical (⊥ : Ideal R) := by
    rw [Ideal.isLocallyNilpotent_iff] at hI
    intro x hx
    rcases hI x (hJI hx) with ⟨n, hn⟩
    rw [Ideal.mem_radical_iff]
    exact ⟨n, by simpa [Ideal.mem_bot] using hn⟩
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJrad hJfg
  refine ⟨n, ?_⟩
  exact le_bot_iff.mp (hn.trans bot_le)

/-- Helper for Lemma 10.77.6: the endomorphism attached to a split summand is idempotent. -/
lemma split_projector_isIdempotentElem
    {S : Type u} [Ring S] {P : Type v} [AddCommGroup P] [Module S P]
    {F : Type w} [AddCommGroup F] [Module S F]
    (i : P →ₗ[S] F) (s : F →ₗ[S] P) (hs : s.comp i = LinearMap.id) :
    IsIdempotentElem (i.comp s) := by
  -- The split relation collapses the middle composite in the square of the projector.
  rw [IsIdempotentElem]
  ext x
  have hmid : s (i (s x)) = s x := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hs (s x)
  exact congrArg i hmid

/-- Helper for Lemma 10.77.6: a split summand is linearly equivalent to the range of the
associated projector. -/
lemma projective_summand_linearEquiv_range_projector
    {S : Type u} [Ring S] {P : Type v} [AddCommGroup P] [Module S P]
    {F : Type w} [AddCommGroup F] [Module S F]
    (i : P →ₗ[S] F) (s : F →ₗ[S] P) (hs : s.comp i = LinearMap.id) :
    Nonempty (P ≃ₗ[S] LinearMap.range (i.comp s)) := by
  let iRange : P →ₗ[S] LinearMap.range (i.comp s) :=
    i.codRestrict (LinearMap.range (i.comp s)) fun x => by
      -- Every point of the summand is fixed by the associated projector.
      refine ⟨i x, ?_⟩
      simpa [LinearMap.comp_apply] using congrArg i (LinearMap.congr_fun hs x)
  refine ⟨LinearEquiv.ofBijective iRange ?_⟩
  constructor
  · intro x y hxy
    -- Applying the retraction to equal images recovers equality on the summand.
    have hxy' : i x = i y := congrArg Subtype.val hxy
    calc
      x = s (i x) := by simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hs x).symm
      _ = s (i y) := by rw [hxy']
      _ = y := by simpa [LinearMap.comp_apply] using LinearMap.congr_fun hs y
  · intro x
    -- Every point in the range is represented by projecting an ambient vector.
    rcases x with ⟨x, hx⟩
    rcases hx with ⟨y, rfl⟩
    refine ⟨s y, ?_⟩
    apply Subtype.ext
    simp [iRange, LinearMap.comp_apply]

/-- Helper for Lemma 10.77.6: reduce a finite free module coefficientwise modulo `I`. -/
abbrev finite_free_quotientMapLinear (n : ℕ) :
    (Fin n → R) →ₗ[R] (Fin n → R ⧸ I) :=
  { toFun := fun x i => Ideal.Quotient.mk I (x i)
    map_add' := by
      intro x y
      ext i
      rfl
    map_smul' := by
      intro r x
      ext i
      rfl }

/-- Helper for Lemma 10.77.6: coefficientwise reduction from a finite free `R`-module to the
corresponding quotient module is surjective. -/
lemma finite_free_quotient_reduction_surjective (n : ℕ) :
    Function.Surjective (finite_free_quotientMapLinear (R := R) (I := I) n) := by
  intro y
  classical
  refine ⟨fun i => Classical.choose (Ideal.Quotient.mk_surjective (I := I) (y i)), ?_⟩
  ext i
  exact Classical.choose_spec (Ideal.Quotient.mk_surjective (I := I) (y i))

/-- Helper for Lemma 10.77.6: membership in `J • ⊤` forces each coordinate to lie in `J`. -/
lemma coeff_mem_ideal_of_mem_ideal_smul_top
    {n : ℕ} {J : Ideal R} {x : Fin n → R}
    (hx : x ∈ J • (⊤ : Submodule R (Fin n → R))) (i : Fin n) :
    x i ∈ J := by
  -- Evaluating at one coordinate transports `J • ⊤` to `J`.
  have h_eval :
      (LinearMap.proj i : (Fin n → R) →ₗ[R] R) x ∈ J • (⊤ : Submodule R R) := by
    exact (Submodule.smul_top_le_comap_smul_top J (LinearMap.proj i)) hx
  simpa using h_eval

/-- Helper for Lemma 10.77.6: if every coordinate of a vector lies in `J`, then the vector lies
in `J • ⊤`. -/
lemma mem_ideal_smul_top_of_forall_coeff_mem
    {n : ℕ} {J : Ideal R} {x : Fin n → R}
    (hx : ∀ i, x i ∈ J) :
    x ∈ J • (⊤ : Submodule R (Fin n → R)) := by
  -- Expand the vector in the standard basis and place each basis term in `J • ⊤`.
  have hsum : x = ∑ i, x i • (Pi.single i (1 : R) : Fin n → R) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  rw [hsum]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.smul_mem_smul (hx i)
    (by simp : (Pi.single i (1 : R) : Fin n → R) ∈ (⊤ : Submodule R (Fin n → R)))

/-- Helper for Lemma 10.77.6: the coefficientwise reduction map on a finite free module has kernel
`I • ⊤`. -/
lemma finite_free_quotient_reduction_ker_eq_ideal_smul_top (n : ℕ) :
    LinearMap.ker (finite_free_quotientMapLinear (R := R) (I := I) n) =
      I • (⊤ : Submodule R (Fin n → R)) := by
  ext x
  constructor
  · intro hx
    -- Vanishing modulo `I` means every coefficient already lies in `I`.
    apply mem_ideal_smul_top_of_forall_coeff_mem (R := R) (J := I)
    intro i
    have hx0 :
        (finite_free_quotientMapLinear (R := R) (I := I) n x) i = 0 := by
      simpa [LinearMap.mem_ker] using congrArg (fun f => f i) (LinearMap.mem_ker.mp hx)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx0
  · intro hx
    -- If every coefficient lies in `I`, the whole vector dies in the quotient.
    rw [LinearMap.mem_ker]
    ext i
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (coeff_mem_ideal_of_mem_ideal_smul_top (R := R) (J := I) hx i)

/-- Helper for Lemma 10.77.6: if a lifted endomorphism reduces to an idempotent projector, then
its idempotency defect is killed by reduction modulo `I`. -/
lemma lifted_projector_defect_comp_eq_zero
    (n : ℕ)
    (ebarR : Module.End R (Fin n → R ⧸ I))
    (hebarR : ebarR.comp ebarR = ebarR)
    (e0 : Module.End R (Fin n → R))
    (he0 :
      (finite_free_quotientMapLinear (R := R) (I := I) n).comp e0 =
        (ebarR.comp (finite_free_quotientMapLinear (R := R) (I := I) n))) :
    (finite_free_quotientMapLinear (R := R) (I := I) n).comp (e0.comp e0 - e0) = 0 := by
  let qF : (Fin n → R) →ₗ[R] (Fin n → R ⧸ I) :=
    finite_free_quotientMapLinear (R := R) (I := I) n
  have hcomp : qF.comp (e0.comp e0) = (ebarR.comp ebarR).comp qF := by
    calc
      qF.comp (e0.comp e0) = (qF.comp e0).comp e0 := by rw [LinearMap.comp_assoc]
      _ = (ebarR.comp qF).comp e0 := by rw [he0]
      _ = ebarR.comp (qF.comp e0) := by rw [← LinearMap.comp_assoc]
      _ = ebarR.comp (ebarR.comp qF) := by rw [he0]
      _ = (ebarR.comp ebarR).comp qF := by rw [LinearMap.comp_assoc]
  -- The quotient projector is idempotent, so the lifted defect reduces to zero.
  calc
    qF.comp (e0.comp e0 - e0) = qF.comp (e0.comp e0) - qF.comp e0 := by
      rw [LinearMap.comp_sub]
    _ = (ebarR.comp ebarR).comp qF - ebarR.comp qF := by rw [hcomp, he0]
    _ = ebarR.comp qF - ebarR.comp qF := by rw [hebarR]
    _ = 0 := by
      ext x i
      simp

/-- Helper for Lemma 10.77.6: the finitely many defect coefficients generate a finitely generated
subideal of `I` controlling the entire image of the defect. -/
lemma exists_fg_subideal_controlling_projector_defect
    (n : ℕ)
    (d : Module.End R (Fin n → R))
    (hd :
      (finite_free_quotientMapLinear (R := R) (I := I) n).comp d = 0) :
    ∃ J : Ideal R, J ≤ I ∧ J.FG ∧ LinearMap.range d ≤ J • (⊤ : Submodule R (Fin n → R)) := by
  let coeff : Fin n × Fin n → R := fun ij => d ((Pi.single ij.2 (1 : R) : Fin n → R)) ij.1
  let J : Ideal R := Ideal.span (Set.range coeff)
  have hcoeff_mem_I : ∀ i j, coeff (i, j) ∈ I := by
    intro i j
    have hzero :
        (finite_free_quotientMapLinear (R := R) (I := I) n
          (d ((Pi.single j (1 : R) : Fin n → R)))) i = 0 := by
      have := LinearMap.congr_fun hd ((Pi.single j (1 : R) : Fin n → R))
      simpa [finite_free_quotientMapLinear, LinearMap.comp_apply] using congrArg (fun f => f i) this
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hJ_le : J ≤ I := by
    -- Every chosen generator already lies in `I`.
    refine Ideal.span_le.2 ?_
    rintro x ⟨⟨i, j⟩, rfl⟩
    exact hcoeff_mem_I i j
  have hJfg : J.FG := by
    -- The coefficient set is finite because there are only finitely many matrix entries.
    exact Submodule.fg_span (R := R) (s := Set.range coeff) (Set.finite_range coeff)
  have hcoeff_mem_J : ∀ i j, d ((Pi.single j (1 : R) : Fin n → R)) i ∈ J := by
    intro i j
    exact Ideal.subset_span ⟨(i, j), rfl⟩
  refine ⟨J, hJ_le, hJfg, ?_⟩
  intro x hx
  rcases hx with ⟨y, rfl⟩
  -- Expand the input in the standard basis and track the defect coefficientwise.
  have hsum : y = ∑ j, y j • (Pi.single j (1 : R) : Fin n → R) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  rw [hsum, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hvec : d ((Pi.single j (1 : R) : Fin n → R)) ∈ J • (⊤ : Submodule R (Fin n → R)) := by
    apply mem_ideal_smul_top_of_forall_coeff_mem (R := R) (J := J)
    intro i
    exact hcoeff_mem_J i j
  rw [map_smul]
  exact Submodule.smul_mem _ _ hvec

/-- Helper for Lemma 10.77.6: if the defect of a lifted projector reduces to zero modulo a
locally nilpotent ideal, then the defect itself is nilpotent. -/
lemma projector_defect_isNilpotent_of_isLocallyNilpotent
    (n : ℕ)
    (d : Module.End R (Fin n → R))
    (hd :
      (finite_free_quotientMapLinear (R := R) (I := I) n).comp d = 0)
    (hI : I.IsLocallyNilpotent) :
    IsNilpotent d := by
  obtain ⟨J, hJI, hJfg, hrange⟩ :=
    exists_fg_subideal_controlling_projector_defect (R := R) (I := I) n d hd
  have hJnil : IsNilpotent J :=
    isNilpotent_of_fg_le_of_isLocallyNilpotent (R := R) (I := I) hJfg hJI hI
  have hmap :
      ∀ {K : Ideal R} {x : Fin n → R},
        x ∈ K • (⊤ : Submodule R (Fin n → R)) →
          d x ∈ K • (J • (⊤ : Submodule R (Fin n → R))) := by
    intro K x hx
    -- Linearity lets us push `d` across a `K`-linear combination termwise.
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m hm
      have hdm : d m ∈ J • (⊤ : Submodule R (Fin n → R)) := hrange ⟨m, rfl⟩
      rw [map_smul]
      exact Submodule.smul_mem_smul hr hdm
    · intro y z hy hz
      simpa [map_add] using
        Submodule.add_mem (K • (J • (⊤ : Submodule R (Fin n → R)))) hy hz
  have hpow :
      ∀ m : ℕ, LinearMap.range (d ^ m) ≤ J ^ m • (⊤ : Submodule R (Fin n → R)) := by
    intro m
    induction m with
    | zero =>
        intro x hx
        rcases hx with ⟨y, rfl⟩
        rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
        simp
    | succ m ihm =>
        intro x hx
        rcases hx with ⟨y, rfl⟩
        have hy : (d ^ m) y ∈ J ^ m • (⊤ : Submodule R (Fin n → R)) := ihm ⟨y, rfl⟩
        have hy' : d ((d ^ m) y) ∈ J ^ m • (J • (⊤ : Submodule R (Fin n → R))) :=
          hmap (K := J ^ m) hy
        have hmul_le :
            J ^ m • (J • (⊤ : Submodule R (Fin n → R))) ≤
              (J ^ m * J) • (⊤ : Submodule R (Fin n → R)) := by
          intro z hz
          refine Submodule.smul_induction_on hz ?_ ?_
          · intro a ha z hz
            refine Submodule.smul_induction_on hz ?_ ?_
            · intro b hb w hw
              have hab : a * b ∈ J ^ m * J := Ideal.mul_mem_mul ha hb
              simpa [smul_smul, mul_assoc] using
                (Submodule.smul_mem_smul hab
                  (show w ∈ (⊤ : Submodule R (Fin n → R)) by simpa using hw))
            · intro u v hu hv
              simpa [smul_add] using Submodule.add_mem _ hu hv
          · intro u v hu hv
            exact Submodule.add_mem _ hu hv
        have hy'' : d ((d ^ m) y) ∈ (J ^ m * J) • (⊤ : Submodule R (Fin n → R)) := by
          exact hmul_le hy'
        have hy''' : d ((d ^ m) y) ∈ (J * J ^ m) • (⊤ : Submodule R (Fin n → R)) := by
          simpa [mul_comm] using hy''
        simpa [pow_succ', Module.End.mul_eq_comp] using hy'''
  obtain ⟨m, hm⟩ := hJnil
  refine ⟨m, ?_⟩
  apply LinearMap.ext
  intro x
  have hx : (d ^ m) x ∈ J ^ m • (⊤ : Submodule R (Fin n → R)) := hpow m ⟨x, rfl⟩
  have hx0 : (d ^ m) x = 0 := by
    simpa [hm] using hx
  simpa using hx0

/-- Helper for Lemma 10.77.6: once the defect reduces to zero modulo `I`, every correction term
with that defect as a left factor also reduces to zero. -/
lemma lifted_projector_defect_left_mul_comp_eq_zero
    (n : ℕ)
    (d t : Module.End R (Fin n → R))
    (hd :
      (finite_free_quotientMapLinear (R := R) (I := I) n).comp d = 0) :
    (finite_free_quotientMapLinear (R := R) (I := I) n).comp (d * t) = 0 := by
  let qF : (Fin n → R) →ₗ[R] (Fin n → R ⧸ I) :=
    finite_free_quotientMapLinear (R := R) (I := I) n
  -- The left factor already dies modulo `I`, so extra right composition does not matter.
  apply LinearMap.ext
  intro x
  ext i
  have hpoint : qF (d (t x)) = 0 := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hd (t x)
  simpa [qF, Module.End.mul_eq_comp, LinearMap.comp_apply] using congrArg (fun y => y i) hpoint

/-- Helper for Lemma 10.77.6: the image of an idempotent endomorphism of a free module is
projective. -/
lemma projective_of_idempotent_range
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Free R M]
    (p : Module.End R M) (hp : IsIdempotentElem p) :
    Module.Projective R (LinearMap.range p) := by
  let hpProj : LinearMap.IsProj (LinearMap.range p) p :=
    LinearMap.IsIdempotentElem.isProj_range _ hp
  -- The codomain restriction of the idempotent supplies a splitting of the range inclusion.
  exact Module.Projective.of_split (LinearMap.range p).subtype hpProj.codRestrict <| by
    ext x
    simpa using hpProj.codRestrict_apply_cod x

/-- Helper for Lemma 10.77.6: for the range of an idempotent endomorphism, ambient membership in
`I • ⊤` is equivalent to intrinsic membership in `I • ⊤` on the range. -/
lemma ideal_smul_top_comap_projector_range_eq
    {M : Type w} [AddCommGroup M] [Module R M]
    (p : Module.End R M)
    (hp : IsIdempotentElem p) :
    Submodule.comap (LinearMap.range p).subtype (I • (⊤ : Submodule R M)) =
      I • (⊤ : Submodule R (LinearMap.range p)) := by
  let hpProj : LinearMap.IsProj (LinearMap.range p) p :=
    LinearMap.IsIdempotentElem.isProj_range _ hp
  refine le_antisymm ?_ ?_
  · intro x hx
    -- Apply the range retraction to pull ambient `I`-multiples back into the range.
    have hx' : x.1 ∈ I • (⊤ : Submodule R M) := hx
    have hcod :
        hpProj.codRestrict x.1 ∈ I • (⊤ : Submodule R (LinearMap.range p)) := by
      exact (Submodule.smul_top_le_comap_smul_top I hpProj.codRestrict) hx'
    simpa using hcod
  · -- The subtype inclusion sends intrinsic `I`-multiples to ambient ones.
    exact Submodule.smul_top_le_comap_smul_top I (LinearMap.range p).subtype

/-- Helper for Lemma 10.77.6: after restricting scalars along `R → R ⧸ I`, the original
`R`-action agrees with the quotient-ring scalar action. -/
lemma ideal_scalar_action_eq_quotient_scalar_action
    {N : Type*} [AddCommGroup N] [Module (R ⧸ I) N] [Module R N]
    [IsScalarTower R (R ⧸ I) N]
    (r : R) (n : N) :
    r • n = ((Ideal.Quotient.mk I) r : R ⧸ I) • n := by
  -- Rewrite the restricted action through the quotient-ring scalar.
  calc
    r • n = r • ((1 : R ⧸ I) • n) := by simp
    _ = (r • (1 : R ⧸ I)) • n := by rw [smul_assoc]
    _ = ((Ideal.Quotient.mk I) r : R ⧸ I) • n := by
      change ((((Ideal.Quotient.mk I) r : R ⧸ I) * 1) : R ⧸ I) • n =
        ((Ideal.Quotient.mk I) r : R ⧸ I) • n
      simp

/-- Helper for Lemma 10.77.6: an `R`-linear equivalence between quotient modules already defined
over `R ⧸ I` automatically respects the quotient-ring scalar action. -/
lemma linearEquiv_map_smul_over_quotient
    {M : Type*} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
    [IsScalarTower R (R ⧸ I) M]
    {N : Type*} [AddCommGroup N] [Module (R ⧸ I) N] [Module R N]
    [IsScalarTower R (R ⧸ I) N]
    (e : M ≃ₗ[R] N) (c : R ⧸ I) (x : M) :
    e (c • x) = c • e x := by
  -- Reduce quotient scalars to representatives in `R` and use `R`-linearity.
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← ideal_scalar_action_eq_quotient_scalar_action (R := R) (I := I) r x]
  rw [e.map_smul]
  rw [ideal_scalar_action_eq_quotient_scalar_action (R := R) (I := I) r (e x)]

/-- Helper for Lemma 10.77.6: an `R`-linear equivalence between quotient modules already defined
over `R ⧸ I` upgrades to an `(R ⧸ I)`-linear equivalence. -/
def linearEquiv_over_quotient
    {M : Type*} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
    [IsScalarTower R (R ⧸ I) M]
    {N : Type*} [AddCommGroup N] [Module (R ⧸ I) N] [Module R N]
    [IsScalarTower R (R ⧸ I) N]
    (e : M ≃ₗ[R] N) : M ≃ₗ[R ⧸ I] N :=
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := linearEquiv_map_smul_over_quotient (R := R) (I := I) e }

/-- Helper for Lemma 10.77.6: an intertwining relation between idempotents identifies the quotient
of the lifted range with the quotient-projector range. -/
lemma quotient_projector_range_equiv_of_intertwining
    (n : ℕ)
    (e : Module.End R (Fin n → R))
    (he : IsIdempotentElem e)
    (ebar : Module.End (R ⧸ I) (Fin n → R ⧸ I))
    (hintertwine :
      (finite_free_quotientMapLinear (R := R) (I := I) n).comp e =
        (ebar.restrictScalars R).comp (finite_free_quotientMapLinear (R := R) (I := I) n)) :
    Nonempty (((LinearMap.range e) ⧸ (I • (⊤ : Submodule R (LinearMap.range e)))) ≃ₗ[R ⧸ I]
      LinearMap.range ebar) := by
  let qF : (Fin n → R) →ₗ[R] (Fin n → R ⧸ I) :=
    finite_free_quotientMapLinear (R := R) (I := I) n
  have hmem :
      ∀ x : LinearMap.range e,
        (qF.comp (LinearMap.range e).subtype) x ∈ LinearMap.range (ebar.restrictScalars R) := by
    intro x
    rcases x with ⟨x, hx⟩
    rcases hx with ⟨y, rfl⟩
    refine ⟨qF y, ?_⟩
    -- The intertwining relation identifies the reduction of `e y` with `ebar (qF y)`.
    simpa [qF, LinearMap.comp_apply] using (congrArg (fun f => f y) hintertwine).symm
  let g : LinearMap.range e →ₗ[R] LinearMap.range (ebar.restrictScalars R) :=
    show LinearMap.range e →ₗ[R] LinearMap.range (ebar.restrictScalars R) from
      LinearMap.codRestrict (LinearMap.range (ebar.restrictScalars R))
        (qF.comp (LinearMap.range e).subtype : LinearMap.range e →ₗ[R] Fin n → R ⧸ I)
        hmem
  have hsurj : Function.Surjective g := by
    -- Surjectivity comes from surjectivity of coefficientwise reduction on the ambient free module.
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨z, rfl⟩
    rcases finite_free_quotient_reduction_surjective (R := R) (I := I) n z with ⟨x, rfl⟩
    refine ⟨⟨e x, ⟨x, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change qF (e x) = ebar (qF x)
    simpa [qF, LinearMap.comp_apply] using congrArg (fun f => f x) hintertwine
  have hgker :
      LinearMap.ker g = LinearMap.ker (qF.comp (LinearMap.range e).subtype) := by
    -- Restricting the codomain does not change the kernel.
    simpa [g] using
      (LinearMap.ker_codRestrict (LinearMap.range (ebar.restrictScalars R))
        (qF.comp (LinearMap.range e).subtype) hmem)
  have hker : LinearMap.ker g = I • (⊤ : Submodule R (LinearMap.range e)) := by
    calc
      LinearMap.ker g = LinearMap.ker (qF.comp (LinearMap.range e).subtype) := hgker
      _ = Submodule.comap (LinearMap.range e).subtype (LinearMap.ker qF) := by
        rw [LinearMap.ker_comp]
      _ = Submodule.comap (LinearMap.range e).subtype (I • (⊤ : Submodule R (Fin n → R))) := by
        rw [finite_free_quotient_reduction_ker_eq_ideal_smul_top (R := R) (I := I) n]
      _ = I • (⊤ : Submodule R (LinearMap.range e)) := by
        exact ideal_smul_top_comap_projector_range_eq (R := R) (I := I) e he
  let eR :
      ((LinearMap.range e) ⧸ (I • (⊤ : Submodule R (LinearMap.range e)))) ≃ₗ[R]
        LinearMap.range (ebar.restrictScalars R) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hsurj)
  have eRange :
      LinearMap.range (ebar.restrictScalars R) ≃ₗ[R] LinearMap.range ebar := by
    -- Forgetting from `R ⧸ I` to `R` does not change the underlying range.
    simpa [LinearMap.range_restrictScalars] using
      ((Submodule.restrictScalarsEquiv (S := R) (p := LinearMap.range ebar)).restrictScalars R)
  exact ⟨linearEquiv_over_quotient (R := R) (I := I) (eR.trans eRange)⟩

-- Proof sketch: use the direct-summand description of finite projective modules over `R ⧸ I`
-- to realize `Pbar` as the image of an idempotent on a finite free quotient module, lift that
-- projector to the finite free `R`-module on the same basis, correct the lifted endomorphism to
-- an actual idempotent via Lemma `10.32.7`, and finally identify the quotient of the corrected
-- range with `Pbar`.
/-- Lemma 10.77.6: if `I` is a locally nilpotent ideal and `Pbar` is a finite projective
`R ⧸ I`-module, then there exists a finite projective `R`-module whose reduction modulo `I` is
isomorphic to `Pbar`. -/
@[stacks 0D47]
theorem exists_finite_projective_lift_of_isLocallyNilpotent
    [Module.Finite (R ⧸ I) Pbar] [Module.Projective (R ⧸ I) Pbar]
    (hI : I.IsLocallyNilpotent) :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Finite R P)
      (_ : Module.Projective R P),
      Nonempty ((P ⧸ (I • ⊤ : Submodule R P)) ≃ₗ[R ⧸ I] Pbar) := by
  obtain ⟨n, π, ι, -, hsplit⟩ :=
    exists_split_finite_free_of_finite_projective (R := R) (I := I) (Pbar := Pbar)
  let ebar : Module.End (R ⧸ I) (Fin n → R ⧸ I) := ι.comp π
  have hebar : IsIdempotentElem ebar := by
    -- The quotient-side projector comes from a splitting of the finite free cover.
    simpa [ebar] using
      (split_projector_isIdempotentElem
        (S := R ⧸ I) (P := Pbar) (F := Fin n → R ⧸ I) ι π hsplit)
  have hPbar_range : Nonempty (Pbar ≃ₗ[R ⧸ I] LinearMap.range ebar) := by
    -- The split summand is linearly equivalent to the projector range.
    simpa [ebar] using
      (projective_summand_linearEquiv_range_projector
        (S := R ⧸ I) (P := Pbar) (F := Fin n → R ⧸ I) ι π hsplit)
  let qF : (Fin n → R) →ₗ[R] (Fin n → R ⧸ I) :=
    finite_free_quotientMapLinear (R := R) (I := I) n
  have hqF : Function.Surjective qF :=
    finite_free_quotient_reduction_surjective (R := R) (I := I) n
  obtain ⟨e0, he0⟩ :=
    Module.projective_lifting_property qF ((ebar.restrictScalars R).comp qF) hqF
  let d : Module.End R (Fin n → R) := e0 ^ 2 - e0
  have hebarR_eq :
      (ebar.restrictScalars R).comp (ebar.restrictScalars R) = ebar.restrictScalars R := by
    simpa [IsIdempotentElem, pow_two, Module.End.mul_eq_comp] using
      congrArg (LinearMap.restrictScalars R) (show ebar * ebar = ebar from hebar)
  have hd_zero : qF.comp d = 0 := by
    -- The lifted idempotency defect already vanishes after reduction to `R ⧸ I`.
    simpa [qF, d, pow_two, Module.End.mul_eq_comp] using
      lifted_projector_defect_comp_eq_zero
        (R := R) (I := I) n (ebar.restrictScalars R) hebarR_eq e0 he0
  have hd_nilpotent : IsNilpotent d := by
    -- Local nilpotence on `I` upgrades the finitely generated coefficient defect ideal to a
    -- nilpotent ideal, which then kills a power of `d`.
    exact projector_defect_isNilpotent_of_isLocallyNilpotent
      (R := R) (I := I) n d hd_zero hI
  obtain ⟨q, hq⟩ :=
    exists_idempotent_eq_add_idempotency_defect_polynomial (A := Module.End R (Fin n → R)) e0
      hd_nilpotent
  let e : Module.End R (Fin n → R) := e0 + d * Polynomial.aeval e0 q
  have he : IsIdempotentElem e := by
    -- Lemma `10.32.7` corrects the lifted pre-projector to a genuine idempotent.
    simpa [e, d] using hq
  have hcorr_zero : qF.comp (d * Polynomial.aeval e0 q) = 0 := by
    -- Every correction term is left-divisible by the defect, so it still reduces to zero.
    simpa [qF] using
      lifted_projector_defect_left_mul_comp_eq_zero
        (R := R) (I := I) n d (Polynomial.aeval e0 q) hd_zero
  have he_intertwine : qF.comp e = (ebar.restrictScalars R).comp qF := by
    -- The correction term does not change the quotient projector because it is defect-divisible.
    change qF.comp (e0 + d * Polynomial.aeval e0 q) = (ebar.restrictScalars R).comp qF
    calc
      qF.comp (e0 + d * Polynomial.aeval e0 q) =
          qF.comp e0 + qF.comp (d * Polynomial.aeval e0 q) := by
            rw [LinearMap.comp_add]
      _ = (ebar.restrictScalars R).comp qF + 0 := by rw [he0, hcorr_zero]
      _ = (ebar.restrictScalars R).comp qF := by simp
  let P : Type u := LinearMap.range e
  let _ : AddCommGroup P := inferInstance
  let _ : Module R P := inferInstance
  let _ : Module.Finite R P := inferInstance
  let _ : Module.Projective R P := projective_of_idempotent_range (R := R) e he
  have hquot :
      (P ⧸ (I • ⊤ : Submodule R P)) ≃ₗ[R ⧸ I] LinearMap.range ebar :=
    by
      -- The first-isomorphism argument on the restricted quotient map identifies the two ranges.
      exact Classical.choice <| by
        simpa [P] using
          quotient_projector_range_equiv_of_intertwining
            (R := R) (I := I) n e he ebar he_intertwine
  rcases hPbar_range with ⟨ePbar⟩
  refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  -- Composing the range comparison with the stored quotient-side splitting finishes the lift.
  exact ⟨hquot.trans ePbar.symm⟩

end
