import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_77_6 (from Chap10) -/
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

/-! ### Lemma_10_77_7 (from Chap10) -/
universe u v

open CategoryTheory
open CategoryTheory.ShortComplex
open CategoryTheory.ShortComplex.ShortExact
open LinearMap

section

variable {R : Type u} [Ring R]
variable {I : Ideal R} [I.IsTwoSided]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- 
Domain triage:
- primary domain: projective modules over nilpotent thickenings;
- sampled owner declarations of the same kind:
  `Module.Projective`,
  `exists_projective_lift_of_projective_quotient_of_isNilpotent`,
  `LinearMap.quotientMapByIdeal`,
  `surjective_of_quotientMap_surjective_of_isNilpotent`;
- best owner abstraction: `Module.Projective R M`, with quotient comparisons handled through the
  canonical quotient-map API rather than a local wrapper;
- primitive data: the nilpotent two-sided ideal `I`, the module `M`, and projectivity of `M / IM`;
- derived API: a projective lift `P`, a comparison map `P → M`, and projectivity of `M`.

Layer classification:
- `source-facing`: the commutative flatness criterion in the second section;
- `core/canonical`: `Module.Projective`;
- `bridge/view`: the quotient-exact descent criterion below, used only as an internal reduction
  step from flatness to projectivity.
-/

private theorem quotientMapByIdeal_exact
    {N P Q : Type*}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (I : Ideal R) (f : N →ₗ[R] P) (g : P →ₗ[R] Q)
    (hExact : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (f.quotientMapByIdeal I) (g.quotientMapByIdeal I) := by
  intro y
  constructor
  · intro hx
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R P)) y
    change ((I • (⊤ : Submodule R Q)).mkQ (g x)) = 0 at hx
    have hx' : g x ∈ I • (⊤ : Submodule R Q) := by
      simpa using (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R Q))).mp hx
    have hxLift :
        ∃ y : P, y ∈ I • (⊤ : Submodule R P) ∧ g y = g x :=
      Submodule.smul_induction_on hx'
        (fun r hr z _ ↦ by
          obtain ⟨y, rfl⟩ := hg z
          refine ⟨r • y, ?_, by simp⟩
          exact Submodule.smul_mem_smul hr (by simp))
        (fun y z hy hz ↦ by
          rcases hy with ⟨y', hy', rfl⟩
          rcases hz with ⟨z', hz', rfl⟩
          exact ⟨y' + z', Submodule.add_mem _ hy' hz', by simp⟩)
    rcases hxLift with ⟨y, hyI, hy⟩
    have hxy : g (x - y) = 0 := by
      simp [hy]
    rcases (hExact (x - y)).mp hxy with ⟨n, hn⟩
    refine ⟨(I • (⊤ : Submodule R N)).mkQ n, ?_⟩
    change ((I • (⊤ : Submodule R P)).mkQ (f n)) = (I • (⊤ : Submodule R P)).mkQ x
    rw [hn]
    simpa using hyI
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R N)) x
    change ((I • (⊤ : Submodule R Q)).mkQ (g (f x))) = 0
    exact
      (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R Q))).2 <| by
        have hfx : g (f x) = 0 := by
          simpa [Function.comp] using congr_fun hExact.comp_eq_zero x
        rw [hfx]
        exact Submodule.zero_mem _

-- Proof sketch: lift the projective quotient module across `I`, use projectivity of the lift to
-- produce a comparison map `P → M` that is an isomorphism modulo `I`, obtain surjectivity of that
-- map by nilpotent Nakayama, and use the assumed exactness of reduction modulo `I` on short exact
-- sequences ending in `M` to kill its kernel modulo `I`. A second nilpotent Nakayama argument then
-- forces the kernel to vanish. This is an internal bridge from flatness to the public source-facing
-- theorem in the commutative section below.
private theorem projective_of_projective_quotient_of_isNilpotent_of_quotientExact_aux
    (hI : IsNilpotent I)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (hmodI :
      ∀ {N P : Type (max u v)} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
        (f : N →ₗ[R] P) (g : P →ₗ[R] M),
        Function.Injective f → Function.Surjective g → Function.Exact f g →
          Function.Injective (f.quotientMapByIdeal I)) :
    Module.Projective R M := by
  obtain ⟨P, _, _, e, hP⟩ :=
    exists_projective_lift_of_projective_quotient_of_isNilpotent hI hquot
  letI : Module.Projective R P := hP
  let gbar : P →ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
    (LinearEquiv.restrictScalars R e).toLinearMap.comp (I • (⊤ : Submodule R P)).mkQ
  obtain ⟨g, hg⟩ :=
    Module.projective_lifting_property (I • (⊤ : Submodule R M)).mkQ gbar
      (Submodule.mkQ_surjective _)
  have hsmul : I • (⊤ : Submodule R P) ≤ Submodule.comap g (I • (⊤ : Submodule R M)) :=
    Submodule.smul_top_le_comap_smul_top I g
  have hcomp :
      ((I • (⊤ : Submodule R P)).mapQ (I • (⊤ : Submodule R M)) g hsmul).comp
          (I • (⊤ : Submodule R P)).mkQ =
        (I • (⊤ : Submodule R M)).mkQ.comp g :=
    Submodule.mapQ_mkQ (I • (⊤ : Submodule R P)) (I • (⊤ : Submodule R M)) g
  have hgquot : g.quotientMapByIdeal I = (LinearEquiv.restrictScalars R e).toLinearMap := by
    apply DFunLike.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R P)) x
    simpa [LinearMap.quotientMapByIdeal, gbar] using
      DFunLike.congr_fun hcomp x |>.trans (DFunLike.congr_fun hg x)
  have hg_surj : Function.Surjective g := by
    apply surjective_of_quotientMap_surjective_of_isNilpotent I g
    · simpa [hgquot] using (LinearEquiv.restrictScalars R e).surjective
    · exact hI
  have hExact : Function.Exact (LinearMap.ker g).subtype g := by
    exact LinearMap.exact_subtype_ker_map g
  have hQuotExact :
      Function.Exact ((LinearMap.ker g).subtype.quotientMapByIdeal I) (g.quotientMapByIdeal I) :=
    quotientMapByIdeal_exact I (LinearMap.ker g).subtype g hExact hg_surj
  have hQuotSubtypeInj : Function.Injective ((LinearMap.ker g).subtype.quotientMapByIdeal I) :=
    hmodI (LinearMap.ker g).subtype g (LinearMap.ker g).injective_subtype hg_surj hExact
  have hQuotInj : Function.Injective (g.quotientMapByIdeal I) := by
    simpa [hgquot] using (LinearEquiv.restrictScalars R e).injective
  have hRangeBot : LinearMap.range ((LinearMap.ker g).subtype.quotientMapByIdeal I) = ⊥ := by
    rw [← LinearMap.exact_iff.mp hQuotExact, LinearMap.ker_eq_bot]
    exact hQuotInj
  have hQuotSubtypeZero : (LinearMap.ker g).subtype.quotientMapByIdeal I = 0 :=
    LinearMap.range_eq_bot.mp hRangeBot
  have hKerQuotSubsingleton :
      Subsingleton ((LinearMap.ker g) ⧸ (I • (⊤ : Submodule R (LinearMap.ker g)))) := by
    refine ⟨fun x y ↦ hQuotSubtypeInj ?_⟩
    simp [hQuotSubtypeZero]
  have hIKer : I • (⊤ : Submodule R (LinearMap.ker g)) = ⊤ := by
    rwa [Submodule.Quotient.subsingleton_iff] at hKerQuotSubsingleton
  have hKerSubsingleton : Subsingleton (LinearMap.ker g) :=
    subsingleton_of_ideal_smul_top_eq_top_of_isNilpotent I hIKer hI
  have hg_inj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.subsingleton_iff_eq_bot.mp hKerSubsingleton
  exact Module.Projective.of_equiv' (LinearEquiv.ofBijective g ⟨hg_inj, hg_surj⟩)

end

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]

private theorem quotientMapByIdeal_lTensor_naturality
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (f : N →ₗ[R] N') :
    f.quotientMapByIdeal I ∘ₗ TensorProduct.quotTensorEquivQuotSMul N I =
      TensorProduct.quotTensorEquivQuotSMul N' I ∘ₗ f.lTensor (R ⧸ I) := by
  apply TensorProduct.ext'
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [LinearMap.quotientMapByIdeal]

private theorem injective_of_ladder_linearEquiv
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    {f : A →ₗ[R] B} {g : A' →ₗ[R] B'} {e₁ : A ≃ₗ[R] A'} {e₂ : B ≃ₗ[R] B'}
    (h : g ∘ₗ e₁ = e₂ ∘ₗ f) (hf : Function.Injective f) :
    Function.Injective g := by
  intro x y hxy
  apply e₁.symm.injective
  apply hf
  apply e₂.injective
  calc
    e₂ (f (e₁.symm x)) = g x := by
      simpa using (LinearMap.congr_fun h (e₁.symm x)).symm
    _ = g y := hxy
    _ = e₂ (f (e₁.symm y)) := by
      simpa using LinearMap.congr_fun h (e₁.symm y)

private theorem quotientMapByIdeal_injective_of_exact_of_flat
    {N P : Type (max u v)}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) (g : P →ₗ[R] M)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hExact : Function.Exact f g) :
    Function.Injective (f.quotientMapByIdeal I) := by
  have hTensorInj : Function.Injective (f.lTensor (R ⧸ I)) := by
    simpa [lTensor_inj_iff_rTensor_inj] using
      lTensor_injective_of_exact_of_flat g hg f hf hExact (R ⧸ I)
  exact injective_of_ladder_linearEquiv (quotientMapByIdeal_lTensor_naturality f) hTensorInj

/-- Lemma 10.77.7: if `I` is a nilpotent ideal of a commutative ring `R`, `M / IM` is a
projective `R ⧸ I`-module, and `M` is flat over `R`, then `M` is projective over `R`. The owner
predicate is the canonical `Module.Projective R M`; the quotient-exact descent criterion used in
the proof is kept internal. -/
theorem projective_of_projective_quotient_of_isNilpotent_of_flat
    (hI : IsNilpotent I)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Projective R M := by
  refine projective_of_projective_quotient_of_isNilpotent_of_quotientExact_aux hI hquot ?_
  intro N _ _ P _ _ f g hf hg hExact
  exact quotientMapByIdeal_injective_of_exact_of_flat f g hf hg hExact

end

/-! ### Lemma_10_77_8 (from Chap10) -/
universe u v

section

variable {R : Type u} [Ring R]
variable {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided]
variable {P : Type v} [AddCommGroup P] [Module R P]

namespace LinearMap

/-- The map on quotients by `K • ⊤` induced by an `R`-linear map. This local abbreviation keeps
Lemma 10.77.8 source-faithful without importing later chapter API. -/
private abbrev quotientMapByIdeal
    {M : Type*} [AddCommGroup M] [Module R M]
    {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (K : Ideal R) [K.IsTwoSided] :
    M ⧸ (K • (⊤ : Submodule R M)) →ₗ[R] M' ⧸ (K • (⊤ : Submodule R M')) :=
  (K • (⊤ : Submodule R M)).mapQ (K • (⊤ : Submodule R M')) f
    (Submodule.smul_top_le_comap_smul_top K f)

/-- Helper for Lemma 10.77.8: the quotient map induced by `f` is also linear over the quotient
ring `R ⧸ K`. This is the scalar adapter needed before applying projectivity modulo `K`. -/
private abbrev quotientMapByIdeal_over_quotient
    {M : Type*} [AddCommGroup M] [Module R M]
    {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (K : Ideal R) [K.IsTwoSided] :
    M ⧸ (K • (⊤ : Submodule R M)) →ₗ[R ⧸ K] M' ⧸ (K • (⊤ : Submodule R M')) :=
  { toFun := f.quotientMapByIdeal K
    map_add' := by
      intro x y
      -- Work with quotient representatives so the induced additivity is visible to `simp`.
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (K • (⊤ : Submodule R M)) x
      obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (K • (⊤ : Submodule R M)) y
      simp [LinearMap.quotientMapByIdeal]
    map_smul' := by
      intro c x
      -- Unpack both the scalar and the quotient class to reduce to the defining quotient action.
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (K • (⊤ : Submodule R M)) x
      simp [LinearMap.quotientMapByIdeal, Module.Quotient.mk_smul_mk] }

end LinearMap

/-- Helper for Lemma 10.77.8: a surjective linear map induces a surjective map on compatible
quotients. -/
private theorem mapQ_surjective_of_surjective
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N)
    (hφ : Function.Surjective φ)
    (p : Submodule R M)
    (q : Submodule R N)
    (hpq : p ≤ Submodule.comap φ q) :
    Function.Surjective (p.mapQ q φ hpq) := by
  intro y
  -- Choose a representative in `N`, then lift it along the original surjection.
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective q y
  obtain ⟨x, rfl⟩ := hφ y
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  rfl

/-- Helper for Lemma 10.77.8: the canonical free cover `P →₀ R → P` is surjective. -/
private theorem canonical_free_cover_surjective :
    Function.Surjective (Finsupp.linearCombination R (id : P → P)) := by
  -- Every `x : P` is hit by the singleton basis vector at `x`.
  simpa using Finsupp.linearCombination_surjective R Function.surjective_id

/-- Helper for Lemma 10.77.8: the canonical free cover stays surjective after reducing modulo an
ideal. -/
private theorem canonical_free_cover_quotient_surjective
    (K : Ideal R) [K.IsTwoSided] :
    Function.Surjective ((Finsupp.linearCombination R (id : P → P)).quotientMapByIdeal K) := by
  -- Quotienting preserves surjectivity for the canonical free cover via `Submodule.mapQ`.
  simpa [LinearMap.quotientMapByIdeal] using
    (mapQ_surjective_of_surjective
      (Finsupp.linearCombination R (id : P → P))
      (canonical_free_cover_surjective (R := R) (P := P))
      (K • (⊤ : Submodule R (P →₀ R)))
      (K • (⊤ : Submodule R P))
      (Submodule.smul_top_le_comap_smul_top K (Finsupp.linearCombination R (id : P → P))))

/-- Helper for Lemma 10.77.8: an element of `K • P` comes from an element of `K • (P →₀ R)` under
the canonical free cover. -/
private theorem canonical_free_cover_preimage_mem_smul_top
    (K : Ideal R) [K.IsTwoSided]
    {x : P}
    (hx : x ∈ K • (⊤ : Submodule R P)) :
    ∃ y : P →₀ R,
      y ∈ K • (⊤ : Submodule R (P →₀ R)) ∧
        Finsupp.linearCombination R (id : P → P) y = x := by
  -- Follow the source proof: write an element of `K • P` as a sum of generators `r • m`, then
  -- lift each generator to the singleton basis vector in the canonical free module.
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m hm
    refine ⟨r • Finsupp.single m (1 : R), ?_, ?_⟩
    · have hsingle : Finsupp.single m (1 : R) ∈ (⊤ : Submodule R (P →₀ R)) := by
        simp
      exact Submodule.smul_mem_smul hr hsingle
    · -- The canonical free cover sends the singleton basis vector at `m` back to `m`.
      calc
        Finsupp.linearCombination R (id : P → P) (r • Finsupp.single m (1 : R))
            = r • Finsupp.linearCombination R (id : P → P) (Finsupp.single m (1 : R)) := by
                simp
        _ = r • m := by
              simp [Finsupp.linearCombination_single]
  · intro y z hy hz
    rcases hy with ⟨fy, hfy, hfy_eq⟩
    rcases hz with ⟨fz, hfz, hfz_eq⟩
    refine ⟨fy + fz, Submodule.add_mem _ hfy hfz, ?_⟩
    -- Additivity of the free cover glues the lifted summands.
    calc
      Finsupp.linearCombination R (id : P → P) (fy + fz)
          = Finsupp.linearCombination R (id : P → P) fy +
              Finsupp.linearCombination R (id : P → P) fz := by
                simp
      _ = y + z := by rw [hfy_eq, hfz_eq]

/-- Helper for Lemma 10.77.8: the overlap correction term inside `(I ⊔ J) • P` lifts to the
canonical free cover inside `(I ⊔ J) • (P →₀ R)`. -/
private theorem exists_overlap_correction_in_sup_smul
    {c : P →₀ R} {y : P}
    (hcy :
      Finsupp.linearCombination R (id : P → P) c - y ∈
        (I ⊔ J) • (⊤ : Submodule R P)) :
    ∃ e : P →₀ R,
      e ∈ (I ⊔ J) • (⊤ : Submodule R (P →₀ R)) ∧
        Finsupp.linearCombination R (id : P → P) e =
          Finsupp.linearCombination R (id : P → P) c - y := by
  -- This is exactly the source correction step, now named separately from later quotient transport.
  letI : (I ⊔ J).IsTwoSided := by
    refine ⟨?_⟩
    intro a b ha
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ha
    exact Submodule.mem_sup.mpr
      ⟨i * b, I.mul_mem_right _ hi, j * b, J.mul_mem_right _ hj, by rw [← add_mul, hij]⟩
  exact canonical_free_cover_preimage_mem_smul_top
    (R := R) (P := P) (K := I ⊔ J) hcy

/-- Helper for Lemma 10.77.8: if `P / KP` is projective over `R / K`, then the canonical free
cover admits a section modulo `K`. -/
private theorem exists_free_cover_section_of_projective_quotient
    (K : Ideal R) [K.IsTwoSided]
    (hPK : Module.Projective (R ⧸ K) (P ⧸ (K • (⊤ : Submodule R P)))) :
    ∃ s :
        P ⧸ (K • (⊤ : Submodule R P)) →ₗ[R ⧸ K]
          (P →₀ R) ⧸ (K • (⊤ : Submodule R (P →₀ R))),
      ((Finsupp.linearCombination R (id : P → P)).quotientMapByIdeal_over_quotient K).comp s =
        LinearMap.id := by
  let πK :
      (P →₀ R) ⧸ (K • (⊤ : Submodule R (P →₀ R))) →ₗ[R ⧸ K]
        P ⧸ (K • (⊤ : Submodule R P)) :=
    (Finsupp.linearCombination R (id : P → P)).quotientMapByIdeal_over_quotient K
  have hπK_surj : Function.Surjective πK := by
    -- Forgetting the quotient-ring scalar structure reduces to the already-proved `R`-linear
    -- surjectivity of the quotient free cover.
    simpa [πK, LinearMap.quotientMapByIdeal_over_quotient] using
      canonical_free_cover_quotient_surjective (R := R) (P := P) (K := K)
  letI : Module.Projective (R ⧸ K) (P ⧸ (K • (⊤ : Submodule R P))) := hPK
  -- Projectivity of `P / KP` now gives the desired right inverse over `R ⧸ K`.
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective πK
    (LinearMap.range_eq_top.2 hπK_surj)
  exact ⟨s, hs⟩

/-- Helper for Lemma 10.77.8: after choosing a section modulo `I`, the source proof's map reduced
modulo `K` is an honest `R`-linear section of the canonical free cover modulo `K`. -/
private theorem mod_i_section_descends_to_sup
    {K : Ideal R} [K.IsTwoSided]
    (hIK : I ≤ K)
    (fI :
      P ⧸ (I • (⊤ : Submodule R P)) →ₗ[R ⧸ I]
        (P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R))))
    (hfI :
      ((Finsupp.linearCombination R (id : P → P)).quotientMapByIdeal_over_quotient I).comp fI =
        LinearMap.id) :
    ∃ fK :
        P ⧸ (K • (⊤ : Submodule R P)) →ₗ[R]
          (P →₀ R) ⧸ (K • (⊤ : Submodule R (P →₀ R))),
      ((Finsupp.linearCombination R (id : P → P)).quotientMapByIdeal K).comp fK =
        LinearMap.id := by
  let π : (P →₀ R) →ₗ[R] P := Finsupp.linearCombination R (id : P → P)
  let pPI : Submodule R P := I • (⊤ : Submodule R P)
  let pPK : Submodule R P := K • (⊤ : Submodule R P)
  let pFI : Submodule R (P →₀ R) := I • (⊤ : Submodule R (P →₀ R))
  let pFK : Submodule R (P →₀ R) := K • (⊤ : Submodule R (P →₀ R))
  let hPIK : pPI ≤ pPK := by
    simpa [pPI, pPK] using
      (Submodule.smul_mono hIK (show (⊤ : Submodule R P) ≤ ⊤ by rfl))
  let hFIK : pFI ≤ pFK := by
    simpa [pFI, pFK] using
      (Submodule.smul_mono hIK (show (⊤ : Submodule R (P →₀ R)) ≤ ⊤ by rfl))
  let qPIK : P ⧸ pPI →ₗ[R] P ⧸ pPK := Submodule.factor hPIK
  let qFIK : (P →₀ R) ⧸ pFI →ₗ[R] (P →₀ R) ⧸ pFK := Submodule.factor hFIK
  let fIR : P ⧸ pPI →ₗ[R] (P →₀ R) ⧸ pFI := fI.restrictScalars R
  let raw : P →ₗ[R] (P →₀ R) ⧸ pFK := (qFIK.comp fIR).comp (Submodule.mkQ pPI)
  have hK_smul_zero :
      ∀ {r : R}, r ∈ K → ∀ z : (P →₀ R) ⧸ pFK, r • z = 0 := by
    intro r hr z
    -- Any scalar from `K` acts trivially on the quotient by `K • ⊤`.
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective pFK z
    change (Submodule.mkQ pFK) (r • y) = 0
    have hy : y ∈ (⊤ : Submodule R (P →₀ R)) := by
      simp
    have hmem : r • y ∈ pFK := by
      exact Submodule.smul_mem_smul hr hy
    exact (Submodule.Quotient.eq pFK).2 (by simpa using hmem)
  have hraw_ker : pPK ≤ LinearMap.ker raw := by
    intro x hx
    change raw x = 0
    -- The raw composite is `R`-linear, so generators `r • m` with `r ∈ K` already map to zero.
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m hm
      calc
        raw (r • m) = r • raw m := by simp [raw]
        _ = 0 := hK_smul_zero hr (raw m)
    · intro y z hy hz
      simpa [raw] using congrArg₂ (· + ·) hy hz
  have hπI_section : (π.quotientMapByIdeal I).comp fIR = LinearMap.id := by
    -- Forgetting the quotient-ring scalar structure leaves the same section identity.
    refine DFunLike.ext _ _ fun x ↦ ?_
    simpa [π, fIR, LinearMap.quotientMapByIdeal_over_quotient, LinearMap.quotientMapByIdeal] using
      LinearMap.congr_fun hfI x
  have hquot_comm :
      (π.quotientMapByIdeal K).comp qFIK = qPIK.comp (π.quotientMapByIdeal I) := by
    -- Both sides send a class modulo `I` to the class of `π` modulo `K`.
    refine DFunLike.ext _ _ fun x ↦ ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective pFI x
    rfl
  refine ⟨pPK.liftQ raw hraw_ker, ?_⟩
  have hcomp_mk :
      (((π.quotientMapByIdeal K).comp (pPK.liftQ raw hraw_ker)).comp (Submodule.mkQ pPK)) =
        Submodule.mkQ pPK := by
    -- Compose with `mkQ` so the identity reduces to the raw map on representatives.
    calc
      (((π.quotientMapByIdeal K).comp (pPK.liftQ raw hraw_ker)).comp (Submodule.mkQ pPK))
          = (π.quotientMapByIdeal K).comp raw := by
              ext x
              rfl
      _ = (((π.quotientMapByIdeal K).comp qFIK).comp fIR).comp (Submodule.mkQ pPI) := by
            rfl
      _ = ((qPIK.comp (π.quotientMapByIdeal I)).comp fIR).comp (Submodule.mkQ pPI) := by
            rw [hquot_comm]
      _ = (qPIK.comp ((π.quotientMapByIdeal I).comp fIR)).comp (Submodule.mkQ pPI) := by
            rw [← LinearMap.comp_assoc]
      _ = (qPIK.comp LinearMap.id).comp (Submodule.mkQ pPI) := by
            rw [hπI_section]
      _ = qPIK.comp (Submodule.mkQ pPI) := by
            rw [LinearMap.comp_id]
      _ = Submodule.mkQ pPK := by
            simpa [qPIK] using (Submodule.factor_comp_mk hPIK : qPIK.comp (Submodule.mkQ pPI) =
              Submodule.mkQ pPK)
  refine DFunLike.ext _ _ fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective pPK x
  exact LinearMap.congr_fun hcomp_mk y

/-- Helper for Lemma 10.77.8: the sum of two two-sided ideals is again two-sided. -/
private theorem isTwoSided_sup : (I ⊔ J).IsTwoSided := by
  refine ⟨?_⟩
  intro a b ha
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ha
  exact Submodule.mem_sup.mpr
    ⟨i * b, I.mul_mem_right _ hi, j * b, J.mul_mem_right _ hj, by rw [← add_mul, hij]⟩

/-- Helper for Lemma 10.77.8: compatible classes modulo `I` and `J` admit a common lift in `R`.
This is the coefficient-level Chinese-remainder step used later for the free-cover gluing. -/
private theorem exists_ring_lift_of_compatible_quotients
    [(I ⊔ J).IsTwoSided]
    {aI : R ⧸ I} {aJ : R ⧸ J}
    (hcompat :
      Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J) aI =
        Ideal.Quotient.factor (le_sup_right : J ≤ I ⊔ J) aJ) :
    ∃ r : R, Ideal.Quotient.mk I r = aI ∧ Ideal.Quotient.mk J r = aJ := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective aI
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective aJ
  -- Unpack compatibility in the quotient by `I ⊔ J` and split the discrepancy into `I`- and
  -- `J`-parts.
  change Ideal.Quotient.mk (I ⊔ J) x = Ideal.Quotient.mk (I ⊔ J) y at hcompat
  have hxy : x - y ∈ I ⊔ J := by
    exact
      (show Ideal.Quotient.mk (I ⊔ J) x = Ideal.Quotient.mk (I ⊔ J) y ↔ x - y ∈ I ⊔ J
        from Ideal.Quotient.eq).mp hcompat
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hxy
  refine ⟨x - i, ?_, ?_⟩
  · -- Correcting the `I`-representative by an element of `I` does not change its class modulo `I`.
    apply
      (show Ideal.Quotient.mk I (x - i) = Ideal.Quotient.mk I x ↔ (x - i) - x ∈ I
        from Ideal.Quotient.eq).2
    have hdiff : (x - i) - x = -i := by
      abel
    exact hdiff ▸ I.neg_mem hi
  · -- The same corrected element has the prescribed class modulo `J` because the discrepancy is `j`.
    apply
      (show Ideal.Quotient.mk J (x - i) = Ideal.Quotient.mk J y ↔ (x - i) - y ∈ J
        from Ideal.Quotient.eq).2
    have hdiff : (x - i) - y = j := by
      calc
        (x - i) - y = (x - y) - i := by abel
        _ = (i + j) - i := by rw [hij]
        _ = j := by abel
    exact hdiff ▸ hj

/-- Helper for Lemma 10.77.8: evaluating a vector in the canonical free cover at a basis index
sends membership in `K • ⊤` to membership in `K`. -/
private theorem coeff_mem_ideal_of_mem_smul_top
    (K : Ideal R) [K.IsTwoSided]
    {y : P →₀ R}
    (hy : y ∈ K • (⊤ : Submodule R (P →₀ R)))
    (p : P) :
    y p ∈ K := by
  -- Push the submodule-membership statement through coefficient evaluation.
  have h_eval :
      (Finsupp.lapply (R := R) (M := R) p) y ∈ K • (⊤ : Submodule R R) := by
    exact
      (Submodule.smul_top_le_comap_smul_top K (Finsupp.lapply (R := R) (M := R) p)) hy
  simpa using h_eval

/-- Helper for Lemma 10.77.8: when `I ∩ J = 0`, the paired quotient map on the canonical free
cover is injective. This is the coefficientwise separation needed for the final gluing inverse. -/
private theorem free_cover_pair_injective_of_inf_eq_bot
    (hIJ : I ⊓ J = ⊥) :
    let σ :
        (P →₀ R) →ₗ[R]
          (((P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R)))) ×
            ((P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))))) :=
        (Submodule.mkQ (I • (⊤ : Submodule R (P →₀ R)))).prod
          (Submodule.mkQ (J • (⊤ : Submodule R (P →₀ R))))
    Function.Injective σ := by
  let σ :
      (P →₀ R) →ₗ[R]
        (((P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R)))) ×
          ((P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))))) :=
      (Submodule.mkQ (I • (⊤ : Submodule R (P →₀ R)))).prod
        (Submodule.mkQ (J • (⊤ : Submodule R (P →₀ R))))
  change Function.Injective σ
  intro y z hyz
  refine Finsupp.ext fun p ↦ ?_
  -- Projecting the paired quotient equality gives congruent classes modulo `I` and modulo `J`.
  have hI :
      (Submodule.mkQ (I • (⊤ : Submodule R (P →₀ R)))) y =
        (Submodule.mkQ (I • (⊤ : Submodule R (P →₀ R)))) z := by
    simpa [σ] using congrArg Prod.fst hyz
  have hJ :
      (Submodule.mkQ (J • (⊤ : Submodule R (P →₀ R)))) y =
        (Submodule.mkQ (J • (⊤ : Submodule R (P →₀ R)))) z := by
    simpa [σ] using congrArg Prod.snd hyz
  have hyzI : y - z ∈ I • (⊤ : Submodule R (P →₀ R)) := by
    exact (Submodule.Quotient.eq _).mp hI
  have hyzJ : y - z ∈ J • (⊤ : Submodule R (P →₀ R)) := by
    exact (Submodule.Quotient.eq _).mp hJ
  -- Each coefficient of `y - z` lies in both ideals, hence vanishes by `I ⊓ J = 0`.
  have hpI : (y - z) p ∈ I :=
    coeff_mem_ideal_of_mem_smul_top (R := R) (P := P) (K := I) hyzI p
  have hpJ : (y - z) p ∈ J :=
    coeff_mem_ideal_of_mem_smul_top (R := R) (P := P) (K := J) hyzJ p
  have hpIJ : (y - z) p ∈ I ⊓ J := by
    exact ⟨hpI, hpJ⟩
  have hpzero : (y - z) p = 0 := by
    have : (y - z) p ∈ (⊥ : Ideal R) := by
      simpa [hIJ] using hpIJ
    simpa using this
  exact sub_eq_zero.mp hpzero

/-- Helper for Lemma 10.77.8: when `I ∩ J = 0`, the range-restriction of the paired quotient map
on the canonical free cover is bijective. The remaining source-faithful work is therefore only to
hit the compatible pairs inside that range. -/
private theorem free_cover_pair_rangeRestrict_bijective_of_inf_eq_bot
    (hIJ : I ⊓ J = ⊥) :
    let σ :
        (P →₀ R) →ₗ[R]
          (((P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R)))) ×
            ((P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))))) :=
        (Submodule.mkQ (I • (⊤ : Submodule R (P →₀ R)))).prod
          (Submodule.mkQ (J • (⊤ : Submodule R (P →₀ R))))
    Function.Bijective σ.rangeRestrict := by
  let σ :
      (P →₀ R) →ₗ[R]
        (((P →₀ R) ⧸ (I • (⊤ : Submodule R (P →₀ R)))) ×
          ((P →₀ R) ⧸ (J • (⊤ : Submodule R (P →₀ R))))) :=
      (Submodule.mkQ (I • (⊤ : Submodule R (P →₀ R)))).prod
        (Submodule.mkQ (J • (⊤ : Submodule R (P →₀ R))))
  have hσinj : Function.Injective σ := by
    -- Reuse the coefficientwise injectivity proof for the concrete paired quotient map.
    simpa [σ] using (free_cover_pair_injective_of_inf_eq_bot (R := R) (I := I) (J := J) (P := P) hIJ)
  change Function.Bijective σ.rangeRestrict
  constructor
  · intro y z hyz
    -- Forgetting the range subtype reduces to injectivity of the paired quotient map itself.
    exact hσinj (congrArg Subtype.val hyz)
  · -- Surjectivity is built into `rangeRestrict`.
    exact σ.surjective_rangeRestrict

/-- Helper for Lemma 10.77.8: if an endomorphism is the identity modulo `J`, then it fixes the
submodule `I • ⊤` whenever `I ∩ J = 0`. -/
private theorem eq_on_left_smul_top_of_right_quotient_identity
    (hIJ : I ⊓ J = ⊥)
    (a : P →ₗ[R] P)
    (hQJ :
      ∀ x : P,
        (Submodule.mkQ (J • (⊤ : Submodule R P))) (a x) =
          (Submodule.mkQ (J • (⊤ : Submodule R P))) x) :
    ∀ x ∈ (I • (⊤ : Submodule R P)), a x = x := by
  intro x hx
  -- Reduce to generators `r • m` with `r ∈ I`; the quotient hypothesis makes the error term lie
  -- in `J • ⊤`, so multiplying by `r` lands in `(I * J) • ⊤ = 0`.
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m _
    have hdiff :
        a m - m ∈ J • (⊤ : Submodule R P) := by
      exact (Submodule.Quotient.eq (J • (⊤ : Submodule R P))).mp (hQJ m)
    have hsmul :
        r • (a m - m) ∈ I • (J • (⊤ : Submodule R P)) := by
      exact Submodule.smul_mem_smul hr hdiff
    have hzeroSub : I • (J • (⊤ : Submodule R P)) = ⊥ := by
      apply le_antisymm
      · calc
          I • (J • (⊤ : Submodule R P)) = (I * J) • (⊤ : Submodule R P) := by
            simpa using (Submodule.mul_smul I J (⊤ : Submodule R P)).symm
          _ ≤ (I ⊓ J) • (⊤ : Submodule R P) := by
            simpa using
              (Submodule.smul_mono (N := (⊤ : Submodule R P)) Ideal.mul_le_inf le_rfl)
          _ = ⊥ := by simpa [hIJ]
      · exact bot_le
    have hsmul_zero : r • (a m - m) = 0 := by
      have : r • (a m - m) ∈ (⊥ : Submodule R P) := by
        simpa [hzeroSub] using hsmul
      simpa using this
    apply sub_eq_zero.mp
    calc
      a (r • m) - r • m = r • a m - r • m := by simp [map_smul]
      _ = r • (a m - m) := by rw [smul_sub]
      _ = 0 := hsmul_zero
  · intro y z hy hz
    -- The induction closes because the fixed-point condition is additive.
    simp [map_add, hy, hz]

/-- Helper for Lemma 10.77.8: an endomorphism that is the identity on a submodule and on the
quotient by that submodule is bijective. -/
private theorem bijective_of_id_on_submodule_and_quotient
    {M : Type*} [AddCommGroup M] [Module R M]
    (a : M →ₗ[R] M)
    (N : Submodule R M)
    (hN : ∀ x ∈ N, a x = x)
    (hQ : ∀ x : M, (Submodule.mkQ N) (a x) = (Submodule.mkQ N) x) :
    Function.Bijective a := by
  constructor
  · intro x y hxy
    have hxyQ : (Submodule.mkQ N) x = (Submodule.mkQ N) y := by
      calc
        (Submodule.mkQ N) x = (Submodule.mkQ N) (a x) := by simpa using (hQ x).symm
        _ = (Submodule.mkQ N) (a y) := by simpa [hxy]
        _ = (Submodule.mkQ N) y := by simpa using hQ y
    have hsub : x - y ∈ N := by
      exact (Submodule.Quotient.eq N).mp hxyQ
    have hfix : a (x - y) = x - y := hN (x - y) hsub
    have hz : a (x - y) = 0 := by
      simp [hxy]
    have : x - y = 0 := by simpa [hfix] using hz
    exact sub_eq_zero.mp this
  · intro y
    have hdiff : y - a y ∈ N := by
      exact (Submodule.Quotient.eq N).mp (hQ y).symm
    let n : N := ⟨y - a y, hdiff⟩
    refine ⟨y + n, ?_⟩
    -- Correct `y` by the discrepancy term living in `N`.
    calc
      a (y + n) = a y + a n := by simp [map_add]
      _ = a y + n := by rw [hN _ n.property]
      _ = y := by
        simp [n, sub_eq_add_neg, add_left_comm]

/-- Helper for Lemma 10.77.8: once the modulo `I` and modulo `J` splittings of the canonical free
cover are glued source-faithfully, the induced endomorphism of `P` is the identity modulo both
ideals. -/
private theorem exists_glued_free_cover_endomorphism
    (hIJ : I ⊓ J = ⊥)
    (hPI : Module.Projective (R ⧸ I) (P ⧸ (I • ⊤ : Submodule R P)))
    (hPJ : Module.Projective (R ⧸ J) (P ⧸ (J • ⊤ : Submodule R P))) :
    ∃ h : P →ₗ[R] (P →₀ R),
      let a : P →ₗ[R] P := (Finsupp.linearCombination R (id : P → P)).comp h
      (∀ x : P,
        (Submodule.mkQ (I • (⊤ : Submodule R P))) (a x) =
          (Submodule.mkQ (I • (⊤ : Submodule R P))) x) ∧
      (∀ x : P,
        (Submodule.mkQ (J • (⊤ : Submodule R P))) (a x) =
          (Submodule.mkQ (J • (⊤ : Submodule R P))) x) := by
  -- Route correction: the remaining obstruction is the overlap-compatible gluing step, not the
  -- automorphism tail after the endomorphism of `P` has been constructed.
  let K : Ideal R := I ⊔ J
  letI : K.IsTwoSided := by
    simpa [K] using (isTwoSided_sup (R := R) (I := I) (J := J))
  obtain ⟨fI, hfI⟩ :=
    exists_free_cover_section_of_projective_quotient (R := R) (P := P) (K := I) hPI
  obtain ⟨fK, hfK⟩ :=
    mod_i_section_descends_to_sup (R := R) (I := I) (P := P)
      (K := K) (show I ≤ K by exact le_sup_left) fI hfI
  obtain ⟨sJ, hsJ⟩ :=
    exists_free_cover_section_of_projective_quotient (R := R) (P := P) (K := J) hPJ
  -- Step 1 is now in place: the source proof has an explicit descended section modulo
  -- `K = I ⊔ J`, and we also have an auxiliary section modulo `J` available to correct on the
  -- overlap quotient.
  let _ := fI
  let _ := hfI
  let _ := fK
  let _ := hfK
  let _ := sJ
  let _ := hsJ
  let _ := hIJ
  let _ := K
  let _ :=
    free_cover_pair_rangeRestrict_bijective_of_inf_eq_bot (R := R) (P := P) (I := I) (J := J) hIJ
  -- The correction lemma now handles the only source-level lifting inside `K • P`, and the
  -- explicit descended section `fK` removes the earlier quotient-of-quotient ambiguity. The
  -- remaining work is exactly the overlap-compatible mod-`J` section and the final free-cover
  -- fiber-product gluing over `K = I ⊔ J`.
  -- TODO: define the overlap map `q : F/JF → F/KF ×_{P/KP} P/JP`, prove its surjectivity by
  -- correcting a chosen lift with `exists_overlap_correction_in_sup_smul`, use projectivity of
  -- `P/JP` to obtain an overlap-compatible section `gJ`, and then glue `(fI, gJ)` coefficientwise
  -- with `exists_ring_lift_of_compatible_quotients` to hit the paired quotient range.
  sorry

/-- Helper for Lemma 10.77.8: a glued lift whose induced endomorphism is the identity modulo `I`
and `J` already splits the canonical free cover of `P`. -/
private theorem projective_of_glued_free_cover_endomorphism
    (hIJ : I ⊓ J = ⊥)
    (h : P →ₗ[R] (P →₀ R))
    (hQI :
      ∀ x : P,
        (Submodule.mkQ (I • (⊤ : Submodule R P)))
          ((Finsupp.linearCombination R (id : P → P)).comp h x) =
            (Submodule.mkQ (I • (⊤ : Submodule R P))) x)
    (hQJ :
      ∀ x : P,
        (Submodule.mkQ (J • (⊤ : Submodule R P)))
          ((Finsupp.linearCombination R (id : P → P)).comp h x) =
            (Submodule.mkQ (J • (⊤ : Submodule R P))) x) :
    Module.Projective R P := by
  let π : (P →₀ R) →ₗ[R] P := Finsupp.linearCombination R (id : P → P)
  let a : P →ₗ[R] P := π.comp h
  have hfixI : ∀ x ∈ (I • (⊤ : Submodule R P)), a x = x := by
    -- The quotient identity modulo `J` forces the endomorphism to fix `IP`.
    exact eq_on_left_smul_top_of_right_quotient_identity hIJ a hQJ
  have hbij : Function.Bijective a := by
    -- Once `a` is the identity on `IP` and on `P / IP`, it is an automorphism.
    exact bijective_of_id_on_submodule_and_quotient a (I • (⊤ : Submodule R P)) hfixI hQI
  let e : P ≃ₗ[R] P := LinearEquiv.ofBijective a hbij
  let s : P →ₗ[R] (P →₀ R) := h.comp e.symm.toLinearMap
  have hs : π.comp s = LinearMap.id := by
    -- Correct the glued lift by the inverse of the resulting automorphism.
    ext x
    change a (e.symm x) = x
    exact e.apply_symm_apply x
  -- A split surjection from a free module exhibits `P` as projective.
  exact Module.Projective.of_split s π hs

/- 
Domain triage:
- primary domain: projective modules over a ring, glued from projective reductions modulo ideals;
- sampled owner-style declarations of the same kind:
  `Module.Projective.of_split`,
  `Module.Projective.iff_split_of_projective`,
  `Module.projective_of_localization_maximal`,
  `Ideal.pi_tensorProductMk_quotient_surjective`;
- owner abstraction: `Module.Projective R P`;
- primitive data: the ring `R`, module `P`, ideals `I`, `J` with `I ⊓ J = ⊥`, and projectivity of
  the two reductions modulo `I` and `J`;
- derived API: the resulting projectivity of `P`.

This item stays at the `source-facing` layer: it is a patching criterion whose natural public
conclusion is the owner predicate `Module.Projective`, not a renamed wrapper around an existing
owner theorem.
-/

-- Proof sketch: choose a surjection from a free `R`-module onto `P`, split it modulo `I` and
-- modulo `J` using the projectivity assumptions on the two quotients, and glue the two splittings
-- through the fiber-product description coming from `I ⊓ J = ⊥`. The resulting endomorphism of
-- `P` is the identity modulo `I` and modulo `J`, hence is an automorphism, so `P` is a direct
-- summand of a free module.
/-- Lemma 10.77.8: if ideals `I` and `J` of a ring `R` satisfy `I ∩ J = 0`, and the quotient
modules `P / IP` and `P / JP` are projective over `R / I` and `R / J` respectively, then `P` is a
projective `R`-module. -/
theorem projective_of_projective_quotients_of_inf_eq_bot (hIJ : I ⊓ J = ⊥)
    (hPI : Module.Projective (R ⧸ I) (P ⧸ (I • ⊤ : Submodule R P)))
    (hPJ : Module.Projective (R ⧸ J) (P ⧸ (J • ⊤ : Submodule R P))) :
    Module.Projective R P := by
  obtain ⟨h, hQI, hQJ⟩ := exists_glued_free_cover_endomorphism hIJ hPI hPJ
  -- Once the source-faithful gluing step is available, the rest is the stable automorphism
  -- correction proved in the helper above.
  exact projective_of_glued_free_cover_endomorphism hIJ h hQI hQJ

end
