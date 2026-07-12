import Mathlib
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import StacksProject_2024.Chap15.Definition_15_61_1
import StacksProject_2024.Chap10.Lemma_10_75_2
import StacksProject_2024.Chap10.Lemma_10_76_2
import StacksProject_2024.Chap15.Lemma_15_89_9
import StacksProject_2024.Chap15.Lemma_15_91_6
import StacksProject_2024.Chap15.Lemma_15_91_14

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/-- Helper for Lemma 15.91.15: mapping a range through a linear map is the range of the composite
map. -/
private theorem submodule_map_range_eq_range_comp
    {M N P : Type u}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    (LinearMap.range f).map g = LinearMap.range (g.comp f) := by
  -- Proof comment: unpack the definitions of `Submodule.map` and `LinearMap.range` on both
  -- directions and keep the same witness.
  ext z
  constructor
  · intro hz
    rcases Submodule.mem_map.1 hz with ⟨y, hy, rfl⟩
    rcases LinearMap.mem_range.1 hy with ⟨x, rfl⟩
    exact LinearMap.mem_range.2 ⟨x, rfl⟩
  · intro hz
    rcases LinearMap.mem_range.1 hz with ⟨x, rfl⟩
    exact Submodule.mem_map.2 ⟨f x, LinearMap.mem_range.2 ⟨x, rfl⟩, rfl⟩

/-- Helper for Lemma 15.91.15: a linear equivalence carrying one submodule onto another induces a
linear equivalence on the corresponding quotients. -/
private noncomputable def quotientLinearEquiv_of_submodule_map_eq
    {M N : Type u}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (P : Submodule R M) (Q : Submodule R N)
    (hPQ : P.map e.toLinearMap = Q) :
    (M ⧸ P) ≃ₗ[R] (N ⧸ Q) := by
  let hForward : P ≤ Submodule.comap e.toLinearMap Q := by
    intro x hx
    change e x ∈ Q
    rw [← hPQ]
    exact ⟨x, hx, rfl⟩
  let hBackward : Q ≤ Submodule.comap e.symm.toLinearMap P := by
    intro y hy
    change e.symm y ∈ P
    have hy' : y ∈ P.map e.toLinearMap := by
      simpa [hPQ] using hy
    rcases hy' with ⟨x, hx, rfl⟩
    simpa using hx
  let f : (M ⧸ P) →ₗ[R] (N ⧸ Q) := Submodule.mapQ P Q e.toLinearMap hForward
  let g : (N ⧸ Q) →ₗ[R] (M ⧸ P) := Submodule.mapQ Q P e.symm.toLinearMap hBackward
  -- Proof comment: both quotient maps are determined by their values on quotient generators.
  exact
    LinearEquiv.ofLinear f g
      (by
        apply LinearMap.ext
        intro q
        refine Quotient.inductionOn' q ?_
        intro x
        change f (g (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
        have hg :
            g (Submodule.Quotient.mk x) =
              (Submodule.Quotient.mk (e.symm x) : M ⧸ P) := by
          simpa [g] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ Q P e.symm.toLinearMap) x
        rw [hg]
        have hf :
            f (Submodule.Quotient.mk (e.symm x)) =
              (Submodule.Quotient.mk (e (e.symm x)) : N ⧸ Q) := by
          simpa [f] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ P Q e.toLinearMap) (e.symm x)
        rw [hf]
        simp)
      (by
        apply LinearMap.ext
        intro q
        refine Quotient.inductionOn' q ?_
        intro x
        change g (f (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
        have hf :
            f (Submodule.Quotient.mk x) =
              (Submodule.Quotient.mk (e x) : N ⧸ Q) := by
          simpa [f] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ P Q e.toLinearMap) x
        rw [hf]
        have hg :
            g (Submodule.Quotient.mk (e x)) =
              (Submodule.Quotient.mk (e.symm (e x)) : M ⧸ P) := by
          simpa [g] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ Q P e.symm.toLinearMap) (e x)
        rw [hg]
        simp)

/-- Helper for Lemma 15.91.15: after inverting `f`, every `f^∞`-torsion element of `M` dies, so
the localized torsion submodule is zero. -/
private theorem localized_fPowerTorsion_eq_bot
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    (Submodule.localized (p := Submonoid.powers f) (M[f^∞] : Submodule R M)) = ⊥ := by
  -- Proof comment: each generator of the localized torsion submodule already has a power of `f`
  -- killing its numerator, which is exactly the criterion for a localized class to be zero.
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_localized'] at hx
  rcases hx with ⟨m, hm, s, rfl⟩
  rw [Submodule.mem_torsion'_iff (Submonoid.powers f)] at hm
  rcases hm with ⟨t, ht⟩
  rw [IsLocalizedModule.mk'_eq_zero']
  exact ⟨t, ht⟩

/-- Helper for Lemma 15.91.15: quotienting by `f^∞`-torsion does not change the away
localization. -/
private noncomputable def away_quotientByFPowerTorsion_linearEquiv
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    LocalizedModule.Away f (M ⧸ (M[f^∞] : Submodule R M)) ≃ₗ[Localization.Away f]
      LocalizedModule.Away f M :=
  (localizedQuotientEquiv (Submonoid.powers f) (M[f^∞] : Submodule R M)).symm ≪≫ₗ
    (Submodule.localized (p := Submonoid.powers f) (M[f^∞] : Submodule R M)).quotEquivOfEqBot
      (localized_fPowerTorsion_eq_bot (R := R) M f)

/-- Helper for Lemma 15.91.15: the inverse localized quotient comparison sends a localized
quotient generator to the quotient class of the corresponding localized generator. -/
private theorem localizedQuotientEquiv_symm_apply_mk_local
    (M : Type u) [AddCommGroup M] [Module R M]
    (f : R) (K : Submodule R M) (x : M) :
    (localizedQuotientEquiv (Submonoid.powers f) K).symm
        (LocalizedModule.mk (Submodule.Quotient.mk x) (1 : Submonoid.powers f)) =
      Submodule.Quotient.mk
        (LocalizedModule.mk x (1 : Submonoid.powers f)) := by
  change
    (IsLocalizedModule.iso
      (Submonoid.powers f)
      (Submodule.toLocalizedQuotient' (Localization.Away f) (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M) K))
      ((IsLocalizedModule.iso (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ K))).symm
        (LocalizedModule.mk (Submodule.Quotient.mk x) 1)) =
      _
  have hs :
      (IsLocalizedModule.iso (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ K))).symm
        (LocalizedModule.mk (Submodule.Quotient.mk x) 1) =
        LocalizedModule.mk (Submodule.Quotient.mk x) 1 := by
    -- Proof comment: for the canonical localization owner, the localization isomorphism fixes
    -- the standard generator `mk x 1`.
    simpa using
      (IsLocalizedModule.iso_symm_apply
        (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ K))
        (Submodule.Quotient.mk x))
  rw [hs]
  -- Proof comment: the localized quotient map sends a quotient generator to the quotient class of
  -- the corresponding localized generator by construction.
  simpa [Submodule.toLocalizedQuotient, Submodule.toLocalizedQuotient'_mk] using
    (IsLocalizedModule.iso_apply_mk
      (Submonoid.powers f)
      (Submodule.toLocalizedQuotient' (Localization.Away f) (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M) K)
      (Submodule.Quotient.mk x))

/-- Helper for Lemma 15.91.15: the away-localization equivalence coming from killing
`f^∞`-torsion carries the canonical image of `M / M[f^∞]` into the canonical image of `M`. -/
private theorem away_quotientByFPowerTorsion_comp_mkLinearMap
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    let T : Submodule R M := (M[f^∞] : Submodule R M)
    (((away_quotientByFPowerTorsion_linearEquiv (R := R) M f).restrictScalars R).toLinearMap.comp
        (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ T))).comp T.mkQ =
      LocalizedModule.mkLinearMap (Submonoid.powers f) M := by
  intro T
  -- Proof comment: evaluate on `m : M`, first rewrite the inverse localized quotient comparison on
  -- the generator `mk (T.mkQ m) 1`, then collapse the final quotient by the already-proved
  -- localized-bottom equality.
  ext m
  change
    (Submodule.localized (p := Submonoid.powers f) T).quotEquivOfEqBot
        (localized_fPowerTorsion_eq_bot (R := R) M f)
        ((localizedQuotientEquiv (Submonoid.powers f) T).symm
          (LocalizedModule.mk (Submodule.Quotient.mk m) (1 : Submonoid.powers f))) =
      LocalizedModule.mk m (1 : Submonoid.powers f)
  rw [localizedQuotientEquiv_symm_apply_mk_local]
  simpa using
    (Submodule.quotEquivOfEqBot_apply_mk
      (p := Submodule.localized (p := Submonoid.powers f) T)
      (hp := localized_fPowerTorsion_eq_bot (R := R) M f)
      (x := LocalizedModule.mk m (1 : Submonoid.powers f)))

/-- Helper for Lemma 15.91.15: after quotienting by `f^∞`-torsion, the resulting module has no
nonzero `f^∞`-torsion left. -/
private theorem quotientByFPowerTorsion_fPowerTorsion_eq_bot
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    let T : Submodule R M := (M[f^∞] : Submodule R M)
    ((M ⧸ T)[f^∞] : Submodule R (M ⧸ T)) = ⊥ := by
  intro T
  -- Proof comment: if a class in `M / M[f^∞]` is still `f^∞`-torsion, then some power of `f`
  -- sends a representative into `M[f^∞]`; multiplying by the torsion witness already inside `T`
  -- shows the representative itself was torsion, hence the quotient class was zero.
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective T x
  rw [Submodule.mem_torsion'_iff (Submonoid.powers f)] at hx
  rcases hx with ⟨s, hs⟩
  have hs_mem :
      (s : R) • m ∈ T := by
    apply (Submodule.Quotient.mk_eq_zero T).1
    simpa using hs
  rw [Submodule.mem_torsion'_iff (Submonoid.powers f)] at hs_mem
  rcases hs_mem with ⟨t, ht⟩
  apply (Submodule.Quotient.mk_eq_zero T).2
  rw [Submodule.mem_torsion'_iff (Submonoid.powers f)]
  have ht' : ((t : R) * (s : R)) • m = 0 := by
    calc
      ((t : R) * (s : R)) • m = (t : R) • ((s : R) • m) := by rw [smul_smul]
      _ = 0 := ht
  refine ⟨t * s, ht'⟩

/-- Helper for Lemma 15.91.15: the canonical localization map on `M / M[f^∞]` is injective. -/
private theorem away_quotientByFPowerTorsion_mkLinearMap_injective
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    let T : Submodule R M := (M[f^∞] : Submodule R M)
    Function.Injective (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ T)) := by
  intro T
  -- Proof comment: the localization kernel is exactly the `f^∞`-torsion submodule, and the
  -- previous lemma shows that quotienting by `M[f^∞]` removes that kernel completely.
  exact LinearMap.ker_eq_bot.mp <| by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective T x
    have hx_tors :
        (Submodule.Quotient.mk m : M ⧸ T) ∈ ((M ⧸ T)[f^∞] : Submodule R (M ⧸ T)) := by
      rw [Submodule.mem_torsion'_iff (Submonoid.powers f)]
      rcases
          (LocalizedModule.mem_ker_mkLinearMap_iff
            (S := Submonoid.powers f)
            (m := (Submodule.Quotient.mk m : M ⧸ T))).1 hx with
        ⟨s, hs, hsx⟩
      exact ⟨⟨s, hs⟩, hsx⟩
    have hbot : ((M ⧸ T)[f^∞] : Submodule R (M ⧸ T)) = ⊥ :=
      quotientByFPowerTorsion_fPowerTorsion_eq_bot (R := R) M f
    rw [Submodule.eq_bot_iff] at hbot
    exact hbot (Submodule.Quotient.mk m) hx_tors

/-- Helper for Lemma 15.91.15: the canonical images of `M / M[f^∞]` and `M` correspond under the
away-localization equivalence. -/
private theorem away_quotientByFPowerTorsion_range_map_eq
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    let T : Submodule R M := (M[f^∞] : Submodule R M)
    (LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ T))).map
        (((away_quotientByFPowerTorsion_linearEquiv (R := R) M f).restrictScalars R).toLinearMap) =
      LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M) := by
  intro T
  -- Proof comment: rewrite the mapped range as the range of the composite, then use surjectivity
  -- of the quotient map `M → M / M[f^∞]`.
  rw [submodule_map_range_eq_range_comp]
  rw [← LinearMap.range_comp_of_range_eq_top
    (((away_quotientByFPowerTorsion_linearEquiv (R := R) M f).restrictScalars R).toLinearMap.comp
      (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ T)))
    (LinearMap.range_eq_top.2 (Submodule.mkQ_surjective T))]
  rw [away_quotientByFPowerTorsion_comp_mkLinearMap (R := R) M f]

/-- Helper for Lemma 15.91.15: quotienting `M` by its `f^∞`-torsion does not change the
source-facing cokernel `M_f / M`. -/
private noncomputable def cokernel_toLocalizationAway_quotient_equiv_mod_fPowerTorsion
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    let T : Submodule R M := (M[f^∞] : Submodule R M)
    (LocalizedModule.Away f (M ⧸ T) ⧸
        LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ T))) ≃ₗ[R]
      (LocalizedModule.Away f M ⧸
        LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M)) := by
  intro T
  let e : LocalizedModule.Away f (M ⧸ T) ≃ₗ[R] LocalizedModule.Away f M :=
    (away_quotientByFPowerTorsion_linearEquiv (R := R) M f).restrictScalars R
  -- Proof comment: now pass to quotients using the range comparison proved above.
  exact
    quotientLinearEquiv_of_submodule_map_eq
      e
      (LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ T)))
      (LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M))
      (away_quotientByFPowerTorsion_range_map_eq (R := R) M f)

/-- Helper for Lemma 15.91.15: the denominator `f^n` is a unit in the away localization. -/
private theorem toLocalizationAway_stageUnit_mem
    (f : R) (n : ℕ+) :
    f ^ (n : ℕ) ∈ Submonoid.powers f := by
  exact ⟨(n : ℕ), rfl⟩

/-- Helper for Lemma 15.91.15: the denominator `f^n` is a unit in the away localization. -/
private noncomputable def toLocalizationAway_stageUnit
    (f : R) (n : ℕ+) :
    (Localization.Away f)ˣ :=
  IsUnit.unit <|
    IsLocalization.map_units (Localization.Away f)
      ⟨f ^ (n : ℕ), toLocalizationAway_stageUnit_mem f n⟩

/-- Helper for Lemma 15.91.15: the chosen unit corresponding to the denominator `f^n` has
underlying scalar `f^n` in the away localization. -/
private theorem toLocalizationAway_stageUnit_val_eq_algebraMap
    (f : R) (n : ℕ+) :
    (((toLocalizationAway_stageUnit f n : (Localization.Away f)ˣ) : Localization.Away f)) =
      algebraMap R (Localization.Away f) (f ^ (n : ℕ)) := by
  -- Proof comment: this is the defining scalar of the localized unit produced from the element
  -- `f^n ∈ powers f`.
  simpa [toLocalizationAway_stageUnit] using
    (IsUnit.unit_spec <|
      IsLocalization.map_units (Localization.Away f)
        ⟨f ^ (n : ℕ), toLocalizationAway_stageUnit_mem f n⟩)

/-- Helper for Lemma 15.91.15: the source-faithful stage numerator map sends `x` to the localized
class `x / f^n`. -/
private noncomputable def toLocalizationAway_stageLinearMap
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) (n : ℕ+) :
    M →ₗ[R] LocalizedModule.Away f M :=
  let e : LocalizedModule.Away f M ≃ₗ[R] LocalizedModule.Away f M :=
    (LinearEquiv.smulOfUnit (toLocalizationAway_stageUnit f n)).symm.restrictScalars R
  LinearMap.comp e.toLinearMap (LocalizedModule.mkLinearMap (Submonoid.powers f) M)

/-- Helper for Lemma 15.91.15: on the image of multiplication by `f^n`, the stage numerator map
agrees with the canonical localization map with denominator `1`. -/
private theorem toLocalizationAway_stageLinearMap_lsmul
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) (n : ℕ+) (x : M) :
    toLocalizationAway_stageLinearMap (R := R) M f n ((f ^ (n : ℕ)) • x) =
      LocalizedModule.mk x (1 : Submonoid.powers f) := by
  -- Proof comment: after localizing, multiplication by `f^n` becomes the action of a unit, so
  -- dividing by that unit recovers the denominator-`1` generator.
  rw [toLocalizationAway_stageLinearMap, LinearMap.comp_apply, map_smul]
  rw [map_smul]
  have hu :
      (((toLocalizationAway_stageUnit f n : (Localization.Away f)ˣ) : Localization.Away f)) =
        algebraMap R (Localization.Away f) (f ^ (n : ℕ)) :=
    toLocalizationAway_stageUnit_val_eq_algebraMap (R := R) f n
  let z : LocalizedModule.Away f M :=
    ((LinearEquiv.smulOfUnit (toLocalizationAway_stageUnit f n)).symm.restrictScalars R)
      ((LocalizedModule.mkLinearMap (Submonoid.powers f) M) x)
  have hz :
      (algebraMap R (Localization.Away f) (f ^ (n : ℕ))) • z =
        LocalizedModule.mk x (1 : Submonoid.powers f) := by
    rw [← hu]
    change
      (LinearEquiv.smulOfUnit (toLocalizationAway_stageUnit f n))
          ((LinearEquiv.smulOfUnit (toLocalizationAway_stageUnit f n)).symm
            (LocalizedModule.mk x (1 : Submonoid.powers f))) =
        LocalizedModule.mk x (1 : Submonoid.powers f)
    exact
      (LinearEquiv.apply_symm_apply
        (LinearEquiv.smulOfUnit (toLocalizationAway_stageUnit f n))
        (LocalizedModule.mk x (1 : Submonoid.powers f)))
  calc
    (f ^ (n : ℕ)) • z = (algebraMap R (Localization.Away f) (f ^ (n : ℕ))) • z := by
      simpa [z] using
        (IsScalarTower.algebraMap_smul
          (R := R)
          (A := Localization.Away f)
          (M := LocalizedModule.Away f M)
          (r := f ^ (n : ℕ))
          (x := z)).symm
    _ = LocalizedModule.mk x (1 : Submonoid.powers f) := hz

/-- Helper for Lemma 15.91.15: after moving from stage `n` to a later stage `m`, the concrete
numerator map still represents the same class `x / f^n` in the away localization. -/
private theorem toLocalizationAway_stageLinearMap_transition
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    {n m : ℕ+} (hnm : n ≤ m) (x : M) :
    toLocalizationAway_stageLinearMap (R := R) M f m ((f ^ ((m : ℕ) - (n : ℕ))) • x) =
      toLocalizationAway_stageLinearMap (R := R) M f n x := by
  let u : (Localization.Away f)ˣ := toLocalizationAway_stageUnit f n
  have hnm' : (n : ℕ) ≤ (m : ℕ) := hnm
  -- Proof comment: multiply both sides by the unit `f^n`; both expressions become the same
  -- denominator-one localization class `x / 1`.
  apply (LinearEquiv.smulOfUnit u).injective
  calc
    ((u : Localization.Away f)) •
        toLocalizationAway_stageLinearMap (R := R) M f m ((f ^ ((m : ℕ) - (n : ℕ))) • x) =
      (algebraMap R (Localization.Away f) (f ^ (n : ℕ))) •
        toLocalizationAway_stageLinearMap (R := R) M f m ((f ^ ((m : ℕ) - (n : ℕ))) • x) := by
          rw [toLocalizationAway_stageUnit_val_eq_algebraMap (R := R) f n]
    _ =
      (f ^ (n : ℕ)) •
        toLocalizationAway_stageLinearMap (R := R) M f m ((f ^ ((m : ℕ) - (n : ℕ))) • x) := by
          simpa using
            (IsScalarTower.algebraMap_smul
              (R := R)
              (A := Localization.Away f)
              (M := LocalizedModule.Away f M)
              (r := f ^ (n : ℕ))
              (x := toLocalizationAway_stageLinearMap (R := R) M f m
                ((f ^ ((m : ℕ) - (n : ℕ))) • x)))
    _ =
      toLocalizationAway_stageLinearMap (R := R) M f m
        ((f ^ (n : ℕ)) • ((f ^ ((m : ℕ) - (n : ℕ))) • x)) := by
          rw [← map_smul]
    _ = toLocalizationAway_stageLinearMap (R := R) M f m ((f ^ (m : ℕ)) • x) := by
          rw [smul_smul, ← pow_add]
          simp [Nat.add_sub_of_le hnm']
    _ = LocalizedModule.mk x (1 : Submonoid.powers f) := by
          simpa [LocalizedModule.mkLinearMap_apply] using
            toLocalizationAway_stageLinearMap_lsmul (R := R) M f m x
    _ = toLocalizationAway_stageLinearMap (R := R) M f n ((f ^ (n : ℕ)) • x) := by
          simpa [LocalizedModule.mkLinearMap_apply] using
            (toLocalizationAway_stageLinearMap_lsmul (R := R) M f n x).symm
    _ = (f ^ (n : ℕ)) • toLocalizationAway_stageLinearMap (R := R) M f n x := by
          rw [map_smul]
    _ =
      (algebraMap R (Localization.Away f) (f ^ (n : ℕ))) •
        toLocalizationAway_stageLinearMap (R := R) M f n x := by
          simpa using
            (IsScalarTower.algebraMap_smul
              (R := R)
              (A := Localization.Away f)
              (M := LocalizedModule.Away f M)
              (r := f ^ (n : ℕ))
              (x := toLocalizationAway_stageLinearMap (R := R) M f n x)).symm
    _ = ((u : Localization.Away f)) • toLocalizationAway_stageLinearMap (R := R) M f n x := by
          rw [toLocalizationAway_stageUnit_val_eq_algebraMap (R := R) f n]

/-- Helper for Lemma 15.91.15: the concrete stage numerator map is literally the localized class
`x / f^n`. -/
private theorem toLocalizationAway_stageLinearMap_eq_mk
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) (n : ℕ+) (x : M) :
    toLocalizationAway_stageLinearMap (R := R) M f n x =
      LocalizedModule.mk x ⟨f ^ (n : ℕ), toLocalizationAway_stageUnit_mem f n⟩ := sorry

/-- Helper for Lemma 15.91.15: if `M → M_f` is injective, then the concrete source-faithful map
`x ↦ x / f^n` into the away localization is injective. -/
private theorem toLocalizationAway_stageLinearMap_injective_of_mkLinearMap_injective
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) (n : ℕ+)
    (hinj : Function.Injective (LocalizedModule.mkLinearMap (Submonoid.powers f) M)) :
    Function.Injective (toLocalizationAway_stageLinearMap (R := R) M f n) := by
  intro x y hxy
  have hsmul :
      toLocalizationAway_stageLinearMap (R := R) M f n ((f ^ (n : ℕ)) • x) =
        toLocalizationAway_stageLinearMap (R := R) M f n ((f ^ (n : ℕ)) • y) := by
    -- Proof comment: scale the equality by `f^n` so that both sides become denominator-`1`
    -- localization classes.
    simpa [map_smul] using congrArg (fun z ↦ (f ^ (n : ℕ)) • z) hxy
  have hmk :
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M) x =
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M) y := by
    -- Proof comment: after rewriting the scaled stage maps with the previous lemma, we are back
    -- to equality of the canonical localization images.
    calc
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M) x =
          toLocalizationAway_stageLinearMap (R := R) M f n ((f ^ (n : ℕ)) • x) := by
            simpa [LocalizedModule.mkLinearMap_apply] using
              (toLocalizationAway_stageLinearMap_lsmul (R := R) M f n x).symm
      _ =
          toLocalizationAway_stageLinearMap (R := R) M f n ((f ^ (n : ℕ)) • y) := hsmul
      _ = (LocalizedModule.mkLinearMap (Submonoid.powers f) M) y := by
            simpa [LocalizedModule.mkLinearMap_apply] using
              toLocalizationAway_stageLinearMap_lsmul (R := R) M f n y
  exact hinj hmk

/-- Helper for Lemma 15.91.15: the stage numerator map kills `f^n M` modulo the canonical image of
`M` in `M_f`. -/
private theorem toLocalizationAway_stageLinearMap_range_le
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) (n : ℕ+) :
    (LinearMap.range (LinearMap.lsmul R M (f ^ (n : ℕ)))).map
        (toLocalizationAway_stageLinearMap (R := R) M f n) ≤
      LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M) := by
  -- Proof comment: an element of `f^n M` is literally `(f^n) • x`, and the previous lemma sends
  -- its localized class to the image of `x` with denominator `1`.
  intro z hz
  rcases Submodule.mem_map.1 hz with ⟨y, hy, rfl⟩
  rcases LinearMap.mem_range.1 hy with ⟨x, rfl⟩
  refine LinearMap.mem_range.2 ⟨x, ?_⟩
  simpa [LinearMap.lsmul_apply] using
    (toLocalizationAway_stageLinearMap_lsmul (R := R) M f n x).symm

/-- Helper for Lemma 15.91.15: the source proof's stage map `M / f^n M → M_f / M` is the quotient
of the concrete numerator map `x ↦ x / f^n`. -/
private noncomputable def toLocalizationAway_cokernelStageMap
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) (n : ℕ+) :
    (M ⧸ LinearMap.range (LinearMap.lsmul R M (f ^ (n : ℕ)))) →ₗ[R]
      (LocalizedModule.Away f M ⧸
        LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M)) := by
  let P : Submodule R M := LinearMap.range (LinearMap.lsmul R M (f ^ (n : ℕ)))
  let Q : Submodule R (LocalizedModule.Away f M) :=
    LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
  have hPQ :
      P ≤ Submodule.comap (toLocalizationAway_stageLinearMap (R := R) M f n) Q := by
    intro x hx
    change toLocalizationAway_stageLinearMap (R := R) M f n x ∈ Q
    exact
      toLocalizationAway_stageLinearMap_range_le (R := R) M f n <|
        Submodule.mem_map.2 ⟨x, hx, rfl⟩
  -- Proof comment: `Submodule.mapQ` packages the well-defined quotient map once the image of
  -- `f^n M` is known to lie in the image of `M`.
  exact Submodule.mapQ P Q (toLocalizationAway_stageLinearMap (R := R) M f n) hPQ

/-- Helper for Lemma 15.91.15: on quotient generators, the stage map is literally the class of the
localized numerator `x / f^n`. -/
private theorem toLocalizationAway_cokernelStageMap_mk
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) (n : ℕ+) (x : M) :
    toLocalizationAway_cokernelStageMap (R := R) M f n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (toLocalizationAway_stageLinearMap (R := R) M f n x) := by
  -- Proof comment: this is the defining computation rule for `Submodule.mapQ`.
  let P : Submodule R M := LinearMap.range (LinearMap.lsmul R M (f ^ (n : ℕ)))
  let Q : Submodule R (LocalizedModule.Away f M) :=
    LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
  simpa [toLocalizationAway_cokernelStageMap, P, Q] using
    DFunLike.congr_fun
      (Submodule.mapQ_mkQ P Q (toLocalizationAway_stageLinearMap (R := R) M f n))
      x

/-- Helper for Lemma 15.91.15: multiplication by `f^(m-n)` sends the relation `f^n M` into the
later relation `f^m M`, so it induces the source-faithful transition map
`M / f^n M → M / f^m M`. -/
private theorem toLocalizationAway_cokernelStageTransition_le
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    {n m : ℕ+} (hnm : n ≤ m) :
    let Pn : Submodule R M := LinearMap.range (LinearMap.lsmul R M (f ^ (n : ℕ)))
    let Pm : Submodule R M := LinearMap.range (LinearMap.lsmul R M (f ^ (m : ℕ)))
    Pn ≤ Submodule.comap (LinearMap.lsmul R M (f ^ ((m : ℕ) - (n : ℕ)))) Pm := by
  intro Pn Pm
  have hnm' : (n : ℕ) ≤ (m : ℕ) := hnm
  -- Proof comment: a typical relation generator has the form `f^n • x`, and multiplying by the
  -- extra factor `f^(m-n)` turns it into `f^m • x`.
  intro x hx
  change (f ^ ((m : ℕ) - (n : ℕ))) • x ∈ Pm
  rcases LinearMap.mem_range.1 hx with ⟨y, rfl⟩
  refine LinearMap.mem_range.2 ⟨y, ?_⟩
  rw [LinearMap.lsmul_apply, LinearMap.lsmul_apply, smul_smul, ← pow_add]
  simp [Nat.sub_add_cancel hnm']

/-- Helper for Lemma 15.91.15: the source proof uses the transition maps
`M / f^n M → M / f^m M` induced by multiplication by `f^(m-n)` when `n ≤ m`. -/
private noncomputable def toLocalizationAway_cokernelStageTransition
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    {n m : ℕ+} (hnm : n ≤ m) :
    (M ⧸ LinearMap.range (LinearMap.lsmul R M (f ^ (n : ℕ)))) →ₗ[R]
      (M ⧸ LinearMap.range (LinearMap.lsmul R M (f ^ (m : ℕ)))) :=
  let Pn : Submodule R M := LinearMap.range (LinearMap.lsmul R M (f ^ (n : ℕ)))
  let Pm : Submodule R M := LinearMap.range (LinearMap.lsmul R M (f ^ (m : ℕ)))
  Submodule.mapQ
    Pn
    Pm
    (LinearMap.lsmul R M (f ^ ((m : ℕ) - (n : ℕ))))
    (toLocalizationAway_cokernelStageTransition_le (R := R) M f hnm)

/-- Helper for Lemma 15.91.15: on quotient generators, the stage transition map is induced by
multiplication by `f^(m-n)` on the numerator. -/
private theorem toLocalizationAway_cokernelStageTransition_mk
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    {n m : ℕ+} (hnm : n ≤ m) (x : M) :
    toLocalizationAway_cokernelStageTransition (R := R) M f hnm (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk ((f ^ ((m : ℕ) - (n : ℕ))) • x) :
        M ⧸ LinearMap.range (LinearMap.lsmul R M (f ^ (m : ℕ)))) := by
  -- Proof comment: this is the defining computation rule for `Submodule.mapQ`.
  let Pn : Submodule R M := LinearMap.range (LinearMap.lsmul R M (f ^ (n : ℕ)))
  let Pm : Submodule R M := LinearMap.range (LinearMap.lsmul R M (f ^ (m : ℕ)))
  simpa [toLocalizationAway_cokernelStageTransition, Pn, Pm] using
    DFunLike.congr_fun
      (Submodule.mapQ_mkQ
        Pn
        Pm
        (LinearMap.lsmul R M (f ^ ((m : ℕ) - (n : ℕ)))))
      x

/-- Helper for Lemma 15.91.15: the concrete stage maps `M / f^n M → M_f / M` are compatible with
the transition maps of the source proof on quotient generators. -/
private theorem toLocalizationAway_cokernelStageMap_comp_transition_mk
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    {n m : ℕ+} (hnm : n ≤ m) (x : M) :
    toLocalizationAway_cokernelStageMap (R := R) M f m
        (toLocalizationAway_cokernelStageTransition (R := R) M f hnm
          (Submodule.Quotient.mk x)) =
      toLocalizationAway_cokernelStageMap (R := R) M f n (Submodule.Quotient.mk x) := by
  -- Proof comment: rewrite both sides on quotient generators and then compare the localized
  -- numerators using the transition compatibility proved above.
  rw [toLocalizationAway_cokernelStageTransition_mk, toLocalizationAway_cokernelStageMap_mk,
    toLocalizationAway_cokernelStageMap_mk]
  apply congrArg Submodule.Quotient.mk
  exact toLocalizationAway_stageLinearMap_transition (R := R) M f hnm x

/-- Helper for Lemma 15.91.15: the concrete stage maps are compatible with the transition maps as
linear maps, not just on quotient generators. -/
private theorem toLocalizationAway_cokernelStageMap_comp_transition
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    {n m : ℕ+} (hnm : n ≤ m) :
    (toLocalizationAway_cokernelStageMap (R := R) M f m).comp
        (toLocalizationAway_cokernelStageTransition (R := R) M f hnm) =
      toLocalizationAway_cokernelStageMap (R := R) M f n := by
  -- Proof comment: both linear maps are determined by their values on quotient generators.
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro x
  exact toLocalizationAway_cokernelStageMap_comp_transition_mk (R := R) M f hnm x

/-- Helper for Lemma 15.91.15: if `M → M_f` is injective, then the induced stage map
`M / f^n M → M_f / M` is injective. -/
private theorem toLocalizationAway_cokernelStageMap_injective_of_mkLinearMap_injective
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) (n : ℕ+)
    (hinj : Function.Injective (LocalizedModule.mkLinearMap (Submonoid.powers f) M)) :
    Function.Injective (toLocalizationAway_cokernelStageMap (R := R) M f n) := by
  intro q₁ q₂ hq
  revert hq
  refine Quotient.inductionOn₂' q₁ q₂ ?_
  intro x y hq
  have hzero :
      toLocalizationAway_cokernelStageMap (R := R) M f n
          (Submodule.Quotient.mk (x - y)) = 0 := by
    -- Proof comment: reduce equality of two quotient classes to vanishing of their difference.
    calc
      toLocalizationAway_cokernelStageMap (R := R) M f n
          (Submodule.Quotient.mk (x - y))
          =
        toLocalizationAway_cokernelStageMap (R := R) M f n (Submodule.Quotient.mk x) -
          toLocalizationAway_cokernelStageMap (R := R) M f n (Submodule.Quotient.mk y) := by
            simp
      _ = 0 := sub_eq_zero.mpr hq
  have hstage_mem :
      toLocalizationAway_stageLinearMap (R := R) M f n (x - y) ∈
        LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M) := by
    -- Proof comment: vanishing in the quotient `M_f / M` means the localized numerator already
    -- comes from the canonical image of `M`.
    exact (Submodule.Quotient.mk_eq_zero _).1 <| by
      simpa [toLocalizationAway_cokernelStageMap_mk (R := R) M f n (x - y)] using hzero
  rcases LinearMap.mem_range.1 hstage_mem with ⟨z, hz⟩
  have hstage_eq :
      toLocalizationAway_stageLinearMap (R := R) M f n (x - y) =
        toLocalizationAway_stageLinearMap (R := R) M f n ((f ^ (n : ℕ)) • z) := by
    -- Proof comment: rewrite the range witness through the concrete stage-map formula on
    -- multiples of `f^n`.
    calc
      toLocalizationAway_stageLinearMap (R := R) M f n (x - y) =
          (LocalizedModule.mkLinearMap (Submonoid.powers f) M) z := hz.symm
      _ = toLocalizationAway_stageLinearMap (R := R) M f n ((f ^ (n : ℕ)) • z) := by
            simpa [LocalizedModule.mkLinearMap_apply] using
              (toLocalizationAway_stageLinearMap_lsmul (R := R) M f n z).symm
  have hxy :
      x - y = (f ^ (n : ℕ)) • z :=
    toLocalizationAway_stageLinearMap_injective_of_mkLinearMap_injective
      (R := R) M f n hinj hstage_eq
  exact (Submodule.Quotient.eq _).2 <| by
    refine LinearMap.mem_range.2 ⟨z, ?_⟩
    simpa [LinearMap.lsmul_apply] using hxy.symm

/-- Helper for Lemma 15.91.15: the source-facing target module is the quotient `M_f / M`
represented as a quotient by the range of the canonical localization map. -/
private abbrev toLocalizationAway_cokernelTarget
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    Type u :=
  LocalizedModule.Away f M ⧸
    LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M)

/-- Helper for Lemma 15.91.15: the source proof organizes the quotients `M / f^n M` into the
directed system indexed by positive integers. -/
private abbrev toLocalizationAway_cokernelStageFamily
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) (n : ℕ+) :
    Type u :=
  M ⧸ LinearMap.range (LinearMap.lsmul R M (f ^ (n : ℕ)))

/-- Helper for Lemma 15.91.15: the transition maps of the stage system are the quotient maps
induced by multiplication with the extra power of `f`. -/
private abbrev toLocalizationAway_cokernelStageSystemMap
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    {n m : ℕ+} (hnm : n ≤ m) :
    toLocalizationAway_cokernelStageFamily M f n →ₗ[R]
      toLocalizationAway_cokernelStageFamily M f m :=
  toLocalizationAway_cokernelStageTransition (R := R) M f hnm

/-- Helper for Lemma 15.91.15: the concrete transition maps form a directed system, so the
textbook stage filtration can be fed directly into `Module.DirectLimit`. -/
private instance toLocalizationAway_cokernelStageDirectedSystem
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    DirectedSystem
      (fun n : ℕ+ ↦ toLocalizationAway_cokernelStageFamily M f n)
      (fun _ _ hij ↦ toLocalizationAway_cokernelStageSystemMap M f hij) where
  map_self n x := by
    -- Proof comment: the identity transition is multiplication by `f^0 = 1`, hence the quotient
    -- class is unchanged.
    refine Quotient.inductionOn' x ?_
    intro y
    simpa [toLocalizationAway_cokernelStageSystemMap] using
      (toLocalizationAway_cokernelStageTransition_mk (R := R) M f (hnm := le_rfl) y)
  map_map := by
    intro i j k hij hjk x
    -- Proof comment: composing the stage transitions multiplies by `f^(j-i)` and then
    -- `f^(k-j)`, which is the same as multiplying once by `f^(k-i)`.
    refine Quotient.inductionOn' x ?_
    intro y
    change
      toLocalizationAway_cokernelStageTransition (R := R) M f hjk
          (toLocalizationAway_cokernelStageTransition (R := R) M f hij
            (Submodule.Quotient.mk y)) =
        toLocalizationAway_cokernelStageTransition (R := R) M f (hij.trans hjk)
          (Submodule.Quotient.mk y)
    rw [toLocalizationAway_cokernelStageTransition_mk (R := R) M f (hnm := hij) y]
    rw [toLocalizationAway_cokernelStageTransition_mk (R := R) M f (hnm := hjk)
      (((f ^ ((j : ℕ) - (k : ℕ))) • y))]
    rw [toLocalizationAway_cokernelStageTransition_mk (R := R) M f (hnm := hij.trans hjk) y]
    congr 1
    have hkj : (k : ℕ) ≤ (j : ℕ) := hij
    have hji : (j : ℕ) ≤ (i : ℕ) := hjk
    have hpow :
        ((i : ℕ) - (j : ℕ)) + ((j : ℕ) - (k : ℕ)) = (i : ℕ) - (k : ℕ) := by
      omega
    rw [smul_smul, ← pow_add, hpow]

/-- Helper for Lemma 15.91.15: the raw direct limit of the stage quotients maps to the target
quotient `M_f / M` by the concrete stage maps. -/
private noncomputable def toLocalizationAway_cokernelStage_directLimit_to_target
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    Module.DirectLimit
        (fun n : ℕ+ ↦ toLocalizationAway_cokernelStageFamily M f n)
        (fun i j hij ↦ toLocalizationAway_cokernelStageSystemMap M f hij) →ₗ[R]
      toLocalizationAway_cokernelTarget M f :=
  Module.DirectLimit.lift R ℕ+
    (fun n : ℕ+ ↦ toLocalizationAway_cokernelStageFamily M f n)
    (fun i j hij ↦ toLocalizationAway_cokernelStageSystemMap M f hij)
    (fun n ↦ toLocalizationAway_cokernelStageMap (R := R) M f n)
    (fun i j hij x ↦
      DFunLike.congr_fun
        (toLocalizationAway_cokernelStageMap_comp_transition (R := R) M f hij)
        x)

/-- Helper for Lemma 15.91.15: on a direct-limit generator, the comparison map to `M_f / M`
recovers the corresponding concrete stage map. -/
private theorem toLocalizationAway_cokernelStage_directLimit_to_target_of
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (n : ℕ+) (x : toLocalizationAway_cokernelStageFamily M f n) :
    toLocalizationAway_cokernelStage_directLimit_to_target (R := R) M f
        (Module.DirectLimit.of R ℕ+
          (fun n : ℕ+ ↦ toLocalizationAway_cokernelStageFamily M f n)
          (fun i j hij ↦ toLocalizationAway_cokernelStageSystemMap M f hij)
          n x) =
      toLocalizationAway_cokernelStageMap (R := R) M f n x := by
  -- Proof comment: this is the defining computation rule for `Module.DirectLimit.lift`.
  exact
    Module.DirectLimit.lift_of
      (R := R)
      (ι := ℕ+)
      (G := fun n : ℕ+ ↦ toLocalizationAway_cokernelStageFamily M f n)
      (f := fun i j hij ↦ toLocalizationAway_cokernelStageSystemMap M f hij)
      (P := toLocalizationAway_cokernelTarget M f)
      (g := fun n ↦ toLocalizationAway_cokernelStageMap (R := R) M f n)
      (Hg := fun i j hij x ↦
        DFunLike.congr_fun
          (toLocalizationAway_cokernelStageMap_comp_transition (R := R) M f hij)
          x)
      x

/-- Helper for Lemma 15.91.15: once `M → M_f` is injective, the raw direct limit of the stage
quotients is already the target quotient `M_f / M`. -/
private noncomputable def toLocalizationAway_cokernelStage_directLimit_linearEquiv_of_injective
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (hinj : Function.Injective (LocalizedModule.mkLinearMap (Submonoid.powers f) M)) :
    Module.DirectLimit
        (fun n : ℕ+ ↦ toLocalizationAway_cokernelStageFamily M f n)
        (fun i j hij ↦ toLocalizationAway_cokernelStageSystemMap M f hij) ≃ₗ[R]
      toLocalizationAway_cokernelTarget M f := sorry

/- Domain-style sampling:
* primary domain: Beauville-Laszlo glueing pairs and Tor-vanishing for the cokernel of
  `M → M_f`.
* sampled owner declarations:
  `IsBeauvilleLaszloGlueingPairAlong`,
  `Tor[R, p](N, M)`,
  `LocalizedModule.mkLinearMap`,
  `ModuleCat.cokernelIsoRangeQuotient`,
  `Tor`.
* owner abstraction: the source-facing quotient owner is the canonical module quotient
  `LocalizedModule.Away f M ⧸ range(M → M_f)`, while the chapter owner
  `IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f` supplies the Beauville-Laszlo
  hypotheses and the chapter owner notation `Tor[R, 1](R', -)` exposes the ambient canonical Tor
  object `Tor (ModuleCat R) 1`.
* primitive data: the algebra map `R → R'`, the element `f : R`, and the explicit `R`-module `M`.
* derived API: the Tor-vanishing conclusion for the canonical quotient `M_f / M`.
* triage: the quotient `LocalizedModule.Away f M ⧸ range(M → M_f)` is `source-facing`;
  `IsBeauvilleLaszloGlueingPairAlong`, `Tor`, and `IsZero` are `core/canonical`; and
  `ModuleCat.cokernelIsoRangeQuotient` is the supporting `bridge/view` identifying the
  categorical cokernel with the quotient model.
-/
-- Proof sketch: rewrite the categorical cokernel of `M → M_f` as the source-facing quotient
-- `M_f / M` via `ModuleCat.cokernelIsoRangeQuotient`, then replace that quotient by the filtered
-- colimit of the quotients `M / f^n M` after killing `f`-power torsion. Lemma `15.91.14` handles
-- the cyclic torsion case, and Lemma `15.89.9` identifies the relevant base changes needed to
-- descend from a free `R / R[f^∞]`-presentation to a general module.
/-- Lemma 15.91.15: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then for every
`R`-module `M` the first Tor group `Tor_1^R(R', \operatorname{Coker}(M → M_f))` vanishes. Lean
states this directly for the canonical quotient
`LocalizedModule.Away f M ⧸ range(M → M_f)`, with `ModuleCat.cokernelIsoRangeQuotient`
remaining only as the internal bridge from the categorical cokernel, and records the vanishing by
the canonical owner `IsZero` of the chapter Tor notation `Tor[R, 1](R', -)`. -/
theorem torOne_extension_cokernel_toLocalizationAway_isZero_of_glueingPair
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    IsZero (Tor[R, 1](R',
      LocalizedModule.Away f M ⧸
        LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M))) := by
  let _ : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f := hpair
  let T : Submodule R M := (M[f^∞] : Submodule R M)
  let Q : Type u := M ⧸ T
  let hQinj :
      Function.Injective (LocalizedModule.mkLinearMap (Submonoid.powers f) Q) :=
    away_quotientByFPowerTorsion_mkLinearMap_injective (R := R) M f
  let eCoker :
      (LocalizedModule.Away f Q ⧸
          LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) Q)) ≃ₗ[R]
        (LocalizedModule.Away f M ⧸
          LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M)) :=
    cokernel_toLocalizationAway_quotient_equiv_mod_fPowerTorsion (R := R) M f
  -- Proof comment: this is the first sentence of the source proof in Lean form. We replace `M`
  -- by `M / M[f^∞]`, and the previous equivalence shows that the target cokernel is unchanged.
  -- Route correction: the remaining blocker is now narrower and still source-faithful. The new
  -- stage-map lemmas now prove both transition compatibility and injectivity of every concrete
  -- map `Q / f^n Q → Q_f / Q` once `Q → Q_f` is injective. What remains is to package these
  -- established maps into the direct-limit/colimit identification
  -- `Q_f / Q ≃ colim_n Q / f^n Q` and then combine it with the stagewise Tor-vanishing package
  -- over `R / R[f^∞]`.
  let _ :=
    toLocalizationAway_cokernelStageMap_comp_transition_mk
      (R := R) Q f (show (1 : ℕ+) ≤ 1 from le_rfl) (0 : Q)
  let _ :=
    toLocalizationAway_cokernelStageMap_injective_of_mkLinearMap_injective
      (R := R) Q f (1 : ℕ+) hQinj
  let _ := hQinj
  let _ := eCoker
  -- TODO: package the proved transition compatibility and stagewise injectivity into the direct
  -- limit / colimit equivalence `Q_f / Q ≃ colim_n Q / f^n Q`, then combine it with the cyclic /
  -- free / general stagewise Tor-vanishing argument over `R / R[f^∞]`.
  sorry

end
