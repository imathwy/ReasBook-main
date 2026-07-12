import StacksProject_2024.Chap10.Lemma_10_24_5.GlueingComparisons

open CategoryTheory LinearMap LocalizedModule IsLocalizedModule

universe u v

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

local notation "Away" => LocalizedModule.Away

namespace AwayModuleGlueing

variable {f : Fin n → R} (glue : AwayModuleGlueing f)

/-- Helper for Lemma 10.24.5: the standard `(j,k)` target differential lifts the `j`-branch from
the `j`-th localization of the distinguished `i`-piece to the common `(j,k)` overlap. -/
noncomputable abbrev standard_target_left_lift
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    Away (f j) (glue.localModule i) →ₗ[R] Away (f j * f k) (glue.localModule i) :=
  LocalizedModule.lift (.powers (f j))
    (LocalizedModule.mkLinearMap (.powers (f j * f k)) (glue.localModule i))
    (fun x ↦ by
      rcases (Submonoid.mem_powers_iff x.1 (f j)).mp x.2 with ⟨n, hn⟩
      have hfj :
          IsUnit (algebraMap R (Module.End R (Away (f j * f k) (glue.localModule i))) (f j)) :=
        away_module_end_isUnit_of_dvd (glue.localModule i) (f j * f k) (f j) (dvd_mul_right _ _)
      simpa [map_pow, ← hn] using hfj.pow n)

/-- Helper for Lemma 10.24.5: the standard `(j,k)` target differential lifts the `k`-branch from
the `k`-th localization of the distinguished `i`-piece to the common `(j,k)` overlap. -/
noncomputable abbrev standard_target_right_lift
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    Away (f k) (glue.localModule i) →ₗ[R] Away (f j * f k) (glue.localModule i) :=
  LocalizedModule.lift (.powers (f k))
    (LocalizedModule.mkLinearMap (.powers (f j * f k)) (glue.localModule i))
    (fun x ↦ by
      rcases (Submonoid.mem_powers_iff x.1 (f k)).mp x.2 with ⟨n, hn⟩
      have hfk :
          IsUnit (algebraMap R (Module.End R (Away (f j * f k) (glue.localModule i))) (f k)) :=
        away_module_end_isUnit_of_dvd (glue.localModule i) (f j * f k) (f k) (dvd_mul_left _ _)
      simpa [map_pow, ← hn] using hfk.pow n)

/-- Helper for Lemma 10.24.5: powers of `f j` act invertibly on the standard left target
localization. -/
theorem standard_target_left_lift_powers_isUnit
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    ∀ x : Submonoid.powers (f j),
      IsUnit
        (algebraMap R
          (Module.End R (Away (f j * f k) (glue.localModule i))) x) := by
  -- Powers of `f j` divide the away element `f j * f k`, hence they act invertibly.
  intro x
  rcases (Submonoid.mem_powers_iff x.1 (f j)).mp x.2 with ⟨n, hn⟩
  have hfj :
      IsUnit (algebraMap R (Module.End R (Away (f j * f k) (glue.localModule i))) (f j)) :=
    away_module_end_isUnit_of_dvd (glue.localModule i) (f j * f k) (f j) (dvd_mul_right _ _)
  simpa [map_pow, ← hn] using hfj.pow n

/-- Helper for Lemma 10.24.5: the standard left branch lift sends a canonical generator to the
same canonical generator in the overlap localization. -/
theorem standard_target_left_lift_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule i) :
    glue.standard_target_left_lift i j k (LocalizedModule.mk x 1) =
      (LocalizedModule.mk x 1 : Away (f j * f k) (glue.localModule i)) := by
  -- Evaluate the localization lift on the canonical numerator `x / 1`.
  rw [AwayModuleGlueing.standard_target_left_lift]
  exact
    LocalizedModule.lift_mk_one
      (S := .powers (f j))
      (g := LocalizedModule.mkLinearMap (.powers (f j * f k)) (glue.localModule i))
      (h := glue.standard_target_left_lift_powers_isUnit i j k)
      (m := x)

/-- Helper for Lemma 10.24.5: every power of `f j` acts invertibly on the nested left target
localization used before collapsing the trivial `f i`-factor. -/
theorem standard_target_left_inner_lift_powers_isUnit
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    ∀ x : Submonoid.powers (f j),
      IsUnit
        (algebraMap R
          (Module.End R (Away (f j * f k) (Away (f i) (glue.localModule i)))) x) := by
  -- Any divisor of the away element acts invertibly on the corresponding away module, and powers
  -- of `f j` divide `f j * f k`.
  intro x
  rcases (Submonoid.mem_powers_iff x.1 (f j)).mp x.2 with ⟨n, hn⟩
  have hfj :
      IsUnit
        (algebraMap R
          (Module.End R (Away (f j * f k) (Away (f i) (glue.localModule i)))) (f j)) :=
    away_module_end_isUnit_of_dvd
      (Away (f i) (glue.localModule i)) (f j * f k) (f j) (dvd_mul_right _ _)
  simpa [map_pow, ← hn] using hfj.pow n

/-- Helper for Lemma 10.24.5: before collapsing the trivial `f i`-localization, the standard left
branch lift is just the usual localization lift on `Away (f i) (glue.localModule i)`. -/
noncomputable abbrev standard_target_left_inner_lift
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    Away (f j) (Away (f i) (glue.localModule i)) →ₗ[R]
      Away (f j * f k) (Away (f i) (glue.localModule i)) :=
  LocalizedModule.lift (.powers (f j))
    (LocalizedModule.mkLinearMap (.powers (f j * f k)) (Away (f i) (glue.localModule i)))
    (glue.standard_target_left_inner_lift_powers_isUnit i j k)

/-- Helper for Lemma 10.24.5: the inner left lift sends a canonical generator to the same
canonical generator in the overlap localization. -/
theorem standard_target_left_inner_lift_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : Away (f i) (glue.localModule i)) :
    glue.standard_target_left_inner_lift i j k (LocalizedModule.mk x 1) =
      (LocalizedModule.mk x 1 : Away (f j * f k) (Away (f i) (glue.localModule i))) := by
  -- Evaluate the nested localization lift on the canonical numerator `x / 1`.
  simpa [AwayModuleGlueing.standard_target_left_inner_lift] using
    (LocalizedModule.lift_mk_one
      (S := .powers (f j))
      (g := LocalizedModule.mkLinearMap (.powers (f j * f k))
        (Away (f i) (glue.localModule i)))
      (h := glue.standard_target_left_inner_lift_powers_isUnit i j k)
      (m := x))

/-- Helper for Lemma 10.24.5: collapsing the trivial `f i`-localization commutes with the
standard left branch lift after transporting the source along the same collapse equivalence. -/
theorem standard_target_left_lift_collapse_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (x : Away (f i) (glue.localModule i)) :
    (((awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm.toLinearMap).comp
        ((glue.standard_target_left_lift i j k).comp
          (awayLocalizeLinearEquiv (f j) (glue.localModuleAwayEquiv i)).toLinearMap))
      (LocalizedModule.mk x 1) =
        glue.standard_target_left_inner_lift i j k (LocalizedModule.mk x 1) := by
  -- Evaluate the comparison on a canonical numerator so each transport is handled by a dedicated
  -- generator lemma instead of a broad unfolding of the iterated-localization composite.
  simp only [LinearMap.comp_apply]
  calc
    (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm
        (glue.standard_target_left_lift i j k
          (awayLocalizeLinearEquiv (f j) (glue.localModuleAwayEquiv i) (LocalizedModule.mk x 1)))
        = (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm
            (glue.standard_target_left_lift i j k
              (LocalizedModule.mk (glue.localModuleAwayEquiv i x) 1)) := by
                rw [awayLocalizeLinearEquiv_apply_mk_one]
    _ = (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm
          (LocalizedModule.mk (glue.localModuleAwayEquiv i x) 1) := by
            rw [glue.standard_target_left_lift_apply_mk_one]
    _ = (LocalizedModule.mk ((glue.localModuleAwayEquiv i).symm (glue.localModuleAwayEquiv i x)) 1 :
          Away (f j * f k) (Away (f i) (glue.localModule i))) := by
            rw [awayLocalizeLinearEquiv_symm_apply_mk_one]
    _ = (LocalizedModule.mk x 1 :
          Away (f j * f k) (Away (f i) (glue.localModule i))) := by
          simpa using
            congrArg
              (fun y ↦
                (LocalizedModule.mk y 1 : Away (f j * f k) (Away (f i) (glue.localModule i))))
              ((glue.localModuleAwayEquiv i).symm_apply_apply x)
    _ = glue.standard_target_left_inner_lift i j k (LocalizedModule.mk x 1) := by
          symm
          exact glue.standard_target_left_inner_lift_apply_mk_one i j k x

/-- Helper for Lemma 10.24.5: collapsing the trivial `f i`-localization commutes with the
standard left branch lift after precomposing with the canonical generator map. -/
theorem standard_target_left_lift_collapse_natural
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    (((awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm.toLinearMap).comp
        ((glue.standard_target_left_lift i j k).comp
          (awayLocalizeLinearEquiv (f j) (glue.localModuleAwayEquiv i)).toLinearMap)).comp
      (LocalizedModule.mkLinearMap (.powers (f j)) (Away (f i) (glue.localModule i))) =
    (glue.standard_target_left_inner_lift i j k).comp
      (LocalizedModule.mkLinearMap (.powers (f j)) (Away (f i) (glue.localModule i))) := by
  -- The source localization is generated by canonical elements `x / 1`, so it suffices to compare
  -- the two composites on those generators.
  ext x
  simpa [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply] using
    glue.standard_target_left_lift_collapse_apply_mk_one i j k x

/-- Helper for Lemma 10.24.5: after stripping the outer collapse equivalence, the standard left
branch lift agrees with the inner localization lift. -/
theorem standard_target_left_lift_overlap_inner_normal_form
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (z : Away (f j) (Away (f i) (glue.localModule i))) :
    (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm
      (glue.standard_target_left_lift i j k
        (awayLocalizeLinearEquiv (f j) (glue.localModuleAwayEquiv i) z)) =
      glue.standard_target_left_inner_lift i j k z := by
  -- Recover the raw map equality from the precomposed naturality statement.
  have hmap :
      ((awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm.toLinearMap).comp
          ((glue.standard_target_left_lift i j k).comp
            (awayLocalizeLinearEquiv (f j) (glue.localModuleAwayEquiv i)).toLinearMap) =
        glue.standard_target_left_inner_lift i j k := by
    exact IsLocalizedModule.ext
      (S := .powers (f j))
      (f := LocalizedModule.mkLinearMap (.powers (f j)) (Away (f i) (glue.localModule i)))
      (map_unit := glue.standard_target_left_inner_lift_powers_isUnit i j k)
      (glue.standard_target_left_lift_collapse_natural i j k)
  exact LinearMap.congr_fun hmap z

/-- Helper for Lemma 10.24.5: the standard right branch lift sends a canonical generator to the
same canonical generator in the overlap localization. -/
theorem standard_target_right_lift_powers_isUnit
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    ∀ x : Submonoid.powers (f k),
      IsUnit
        (algebraMap R
          (Module.End R (Away (f j * f k) (glue.localModule i))) x) := by
  -- Powers of `f k` divide the away element `f j * f k`, hence they act invertibly.
  intro x
  rcases (Submonoid.mem_powers_iff x.1 (f k)).mp x.2 with ⟨n, hn⟩
  have hfk :
      IsUnit (algebraMap R (Module.End R (Away (f j * f k) (glue.localModule i))) (f k)) :=
    away_module_end_isUnit_of_dvd (glue.localModule i) (f j * f k) (f k) (dvd_mul_left _ _)
  simpa [map_pow, ← hn] using hfk.pow n

/-- Helper for Lemma 10.24.5: the standard right branch lift sends a canonical generator to the
same canonical generator in the overlap localization. -/
theorem standard_target_right_lift_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule i) :
    glue.standard_target_right_lift i j k (LocalizedModule.mk x 1) =
      (LocalizedModule.mk x 1 : Away (f j * f k) (glue.localModule i)) := by
  -- Evaluate the localization lift on the canonical numerator `x / 1`.
  simpa [AwayModuleGlueing.standard_target_right_lift] using
    (LocalizedModule.lift_mk_one
      (S := .powers (f k))
      (g := LocalizedModule.mkLinearMap (.powers (f j * f k)) (glue.localModule i))
      (h := glue.standard_target_right_lift_powers_isUnit i j k)
      (m := x))

/-- Helper for Lemma 10.24.5: every power of `f k` acts invertibly on the nested right target
localization used before collapsing the trivial `f i`-factor. -/
theorem standard_target_right_inner_lift_powers_isUnit
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    ∀ x : Submonoid.powers (f k),
      IsUnit
        (algebraMap R
          (Module.End R (Away (f j * f k) (Away (f i) (glue.localModule i)))) x) := by
  -- As on the left branch, powers of the relevant distinguished element divide the away element
  -- of the overlap localization, hence act by units.
  intro x
  rcases (Submonoid.mem_powers_iff x.1 (f k)).mp x.2 with ⟨n, hn⟩
  have hfk :
      IsUnit
        (algebraMap R
          (Module.End R (Away (f j * f k) (Away (f i) (glue.localModule i)))) (f k)) :=
    away_module_end_isUnit_of_dvd
      (Away (f i) (glue.localModule i)) (f j * f k) (f k) (dvd_mul_left _ _)
  simpa [map_pow, ← hn] using hfk.pow n

/-- Helper for Lemma 10.24.5: before collapsing the trivial `f i`-localization, the standard right
branch lift is just the usual localization lift on `Away (f i) (glue.localModule i)`. -/
noncomputable abbrev standard_target_right_inner_lift
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    Away (f k) (Away (f i) (glue.localModule i)) →ₗ[R]
      Away (f j * f k) (Away (f i) (glue.localModule i)) :=
  LocalizedModule.lift (.powers (f k))
    (LocalizedModule.mkLinearMap (.powers (f j * f k)) (Away (f i) (glue.localModule i)))
    (glue.standard_target_right_inner_lift_powers_isUnit i j k)

/-- Helper for Lemma 10.24.5: the inner right lift sends a canonical generator to the same
canonical generator in the overlap localization. -/
theorem standard_target_right_inner_lift_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : Away (f i) (glue.localModule i)) :
    glue.standard_target_right_inner_lift i j k (LocalizedModule.mk x 1) =
      (LocalizedModule.mk x 1 : Away (f j * f k) (Away (f i) (glue.localModule i))) := by
  -- Evaluate the nested right lift on the canonical numerator `x / 1`.
  simpa [AwayModuleGlueing.standard_target_right_inner_lift] using
    (LocalizedModule.lift_mk_one
      (S := .powers (f k))
      (g := LocalizedModule.mkLinearMap (.powers (f j * f k))
        (Away (f i) (glue.localModule i)))
      (h := glue.standard_target_right_inner_lift_powers_isUnit i j k)
      (m := x))

/-- Helper for Lemma 10.24.5: collapsing the trivial `f i`-localization commutes with the
standard right branch lift after transporting the source along the same collapse equivalence. -/
theorem standard_target_right_lift_collapse_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (x : Away (f i) (glue.localModule i)) :
    (((awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm.toLinearMap).comp
        ((glue.standard_target_right_lift i j k).comp
          (awayLocalizeLinearEquiv (f k) (glue.localModuleAwayEquiv i)).toLinearMap))
      (LocalizedModule.mk x 1) =
        glue.standard_target_right_inner_lift i j k (LocalizedModule.mk x 1) := by
  -- As on the left branch, evaluate on a canonical numerator so the transport chain is reduced to
  -- the previously isolated generator computations.
  simp only [LinearMap.comp_apply]
  calc
    (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm
        (glue.standard_target_right_lift i j k
          (awayLocalizeLinearEquiv (f k) (glue.localModuleAwayEquiv i) (LocalizedModule.mk x 1)))
        = (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm
            (glue.standard_target_right_lift i j k
              (LocalizedModule.mk (glue.localModuleAwayEquiv i x) 1)) := by
                rw [awayLocalizeLinearEquiv_apply_mk_one]
    _ = (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm
          (LocalizedModule.mk (glue.localModuleAwayEquiv i x) 1) := by
            rw [glue.standard_target_right_lift_apply_mk_one]
    _ = (LocalizedModule.mk ((glue.localModuleAwayEquiv i).symm (glue.localModuleAwayEquiv i x)) 1 :
          Away (f j * f k) (Away (f i) (glue.localModule i))) := by
            rw [awayLocalizeLinearEquiv_symm_apply_mk_one]
    _ = (LocalizedModule.mk x 1 :
          Away (f j * f k) (Away (f i) (glue.localModule i))) := by
          simpa using
            congrArg
              (fun y ↦
                (LocalizedModule.mk y 1 : Away (f j * f k) (Away (f i) (glue.localModule i))))
              ((glue.localModuleAwayEquiv i).symm_apply_apply x)
    _ = glue.standard_target_right_inner_lift i j k (LocalizedModule.mk x 1) := by
          symm
          exact glue.standard_target_right_inner_lift_apply_mk_one i j k x

/-- Helper for Lemma 10.24.5: collapsing the trivial `f i`-localization commutes with the
standard right branch lift after precomposing with the canonical generator map. -/
theorem standard_target_right_lift_collapse_natural
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    (((awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm.toLinearMap).comp
        ((glue.standard_target_right_lift i j k).comp
          (awayLocalizeLinearEquiv (f k) (glue.localModuleAwayEquiv i)).toLinearMap)).comp
      (LocalizedModule.mkLinearMap (.powers (f k)) (Away (f i) (glue.localModule i))) =
    (glue.standard_target_right_inner_lift i j k).comp
      (LocalizedModule.mkLinearMap (.powers (f k)) (Away (f i) (glue.localModule i))) := by
  -- The source localization is again generated by canonical elements `x / 1`, so compare the two
  -- composites only on those generators.
  ext x
  simpa [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply] using
    glue.standard_target_right_lift_collapse_apply_mk_one i j k x

/-- Helper for Lemma 10.24.5: after stripping the outer collapse equivalence, the standard right
branch lift agrees with the inner localization lift. -/
theorem standard_target_right_lift_overlap_inner_normal_form
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (z : Away (f k) (Away (f i) (glue.localModule i))) :
    (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm
      (glue.standard_target_right_lift i j k
        (awayLocalizeLinearEquiv (f k) (glue.localModuleAwayEquiv i) z)) =
      glue.standard_target_right_inner_lift i j k z := by
  -- Recover the raw map equality from the precomposed naturality statement.
  have hmap :
      ((awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm.toLinearMap).comp
          ((glue.standard_target_right_lift i j k).comp
            (awayLocalizeLinearEquiv (f k) (glue.localModuleAwayEquiv i)).toLinearMap) =
        glue.standard_target_right_inner_lift i j k := by
    exact IsLocalizedModule.ext
      (S := .powers (f k))
      (f := LocalizedModule.mkLinearMap (.powers (f k)) (Away (f i) (glue.localModule i)))
      (map_unit := glue.standard_target_right_inner_lift_powers_isUnit i j k)
      (glue.standard_target_right_lift_collapse_natural i j k)
  exact LinearMap.congr_fun hmap z

/-- Helper for Lemma 10.24.5: the inverse `(1,2)` triple-overlap transport sends a canonical
generator on the `j`-piece to the canonical overlap-transported generator on the `i`-piece. -/
theorem triple_overlap_hom12_symm_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule j) :
    ((awayModuleGlueingTripleOverlapHom12 f glue.localModule glue.overlapIso i j k).symm)
        (LocalizedModule.mk x 1) =
      (awayMulLinearEquiv (f i * f j) (f k) (glue.localModule i))
        (LocalizedModule.mk
          ((((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
            (LocalizedModule.mk x 1 : Away (f i * f j) (glue.localModule j)))) 1) := by
  -- Route correction: expose the inverse composite directly, so the left branch can be rewritten
  -- on canonical generators without broad unfolding through the whole target comparison.
  dsimp [awayModuleGlueingTripleOverlapHom12]
  simp only
  rw [awayMulLinearEquiv_symm_apply_mk_one, LocalizedModule.map_mk]
  simpa

/-- Helper for Lemma 10.24.5: the inverse `(1,3)` triple-overlap transport sends a canonical
generator on the `k`-piece to the canonical overlap-transported generator on the `i`-piece. -/
theorem triple_overlap_hom13_symm_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule k) :
    ((awayModuleGlueingTripleOverlapHom13 f glue.localModule glue.overlapIso i j k).symm)
        (LocalizedModule.mk x 1) =
      (awayEqLinearEquiv (glue.localModule i) (by ring)).symm
        ((awayMulLinearEquiv (f i * f k) (f j) (glue.localModule i))
          (LocalizedModule.mk
            ((((glue.overlapIso i k).toLinearEquiv.restrictScalars R).symm
              (LocalizedModule.mk x 1 : Away (f i * f k) (glue.localModule k)))) 1)) := by
  -- Route correction: normalize the inverse `(1,3)` branch before using the cocycle to replace
  -- the composite `(1,2)⁻¹ ∘ (2,3)⁻¹` with `(1,3)⁻¹`.
  dsimp [awayModuleGlueingTripleOverlapHom13]
  simp only
  rw [awayEqLinearEquiv_symm_apply_mk_one, awayMulLinearEquiv_symm_apply_mk_one,
    LocalizedModule.map_mk]
  simpa

/-- Helper for Lemma 10.24.5: the inverse of the `(2,3)` triple-overlap transport is the
explicit composite of the inverses of its three defining factors. -/
theorem triple_overlap_hom23_symm_apply
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (x : Away (f i * f j * f k) (glue.localModule k)) :
    ((awayModuleGlueingTripleOverlapHom23 f glue.localModule glue.overlapIso i j k).symm) x =
      let left :
          Away (f i * f j * f k) (glue.localModule j) ≃ₗ[R]
            Away (f j * f k * f i) (glue.localModule j) :=
        awayEqLinearEquiv (glue.localModule j) (by ring)
      let center :
          Away (f j * f k * f i) (glue.localModule j) ≃ₗ[R]
            Away (f j * f k * f i) (glue.localModule k) :=
        (awayMulLinearEquiv (f j * f k) (f i) (glue.localModule j)).symm.trans
          ((awayLocalizeLinearEquiv (f i) ((glue.overlapIso j k).toLinearEquiv.restrictScalars R)).trans
            (awayMulLinearEquiv (f j * f k) (f i) (glue.localModule k)))
      let right :
          Away (f j * f k * f i) (glue.localModule k) ≃ₗ[R]
            Away (f i * f j * f k) (glue.localModule k) :=
        awayEqLinearEquiv (glue.localModule k) (by ring)
      left.symm (center.symm (right.symm x)) := by
  -- Unfolding the abbrev exposes the inverse composite in exactly the required pointwise form.
  rfl

/-- Helper for Lemma 10.24.5: the inverse of the middle factor in the `(2,3)` triple-overlap
transport sends a canonical generator to the canonical overlap-transported generator. -/
theorem triple_overlap_hom23_center_symm_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule k) :
    let center :
        Away (f j * f k * f i) (glue.localModule j) ≃ₗ[R]
          Away (f j * f k * f i) (glue.localModule k) :=
      (awayMulLinearEquiv (f j * f k) (f i) (glue.localModule j)).symm.trans
        ((awayLocalizeLinearEquiv (f i) ((glue.overlapIso j k).toLinearEquiv.restrictScalars R)).trans
          (awayMulLinearEquiv (f j * f k) (f i) (glue.localModule k)))
    center.symm (LocalizedModule.mk x 1) =
      (awayMulLinearEquiv (f j * f k) (f i) (glue.localModule j))
        (LocalizedModule.mk
          ((((glue.overlapIso j k).toLinearEquiv.restrictScalars R).symm
            (LocalizedModule.mk x 1 : Away (f j * f k) (glue.localModule k)))) 1) := by
  -- Route correction: normalize the middle inverse transport on a canonical generator before
  -- composing it with the outer equality transports from the triple-overlap comparison.
  dsimp
  simp only
  rw [awayMulLinearEquiv_symm_apply_mk_one, LocalizedModule.map_mk]
  simpa

/-- Helper for Lemma 10.24.5: the outer inverse equality transport in the `(2,3)` triple-overlap
comparison is exactly the domain-reordering transport used in the localized target component. -/
theorem triple_overlap_hom23_outer_symm_eq_domain_transport
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
  let left :
      Away (f i * f j * f k) (glue.localModule j) ≃ₗ[R]
        Away (f j * f k * f i) (glue.localModule j) :=
      awayEqLinearEquiv (glue.localModule j) (by ring)
  left.symm =
      awayEqLinearEquiv (glue.localModule j)
        (AwayModuleGlueing.localized_target_component_domain_eq (f := f) i j k) := by
  -- Route correction: identify the outer equality transport once, so the right branch can use the
  -- normalized middle inverse without introducing another overlap-specific generator lemma.
  dsimp
  simpa [awayEqLinearEquiv_symm_eq] using
    awayEqLinearEquiv_congr
      (glue.localModule j)
      ((AwayModuleGlueing.localized_target_component_domain_eq (f := f) i j k).symm)
      (AwayModuleGlueing.localized_target_component_domain_eq (f := f) i j k)

/-- Helper for Lemma 10.24.5: the first two steps of the right target-component transport rewrite
the canonical `k`-branch generator into the common triple-overlap model. -/
theorem localized_target_component_transport_overlap_right_generator
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule k) :
    (awayEqLinearEquiv (glue.localModule j)
        (AwayModuleGlueing.localized_target_component_domain_eq (f := f) i j k))
      ((awayMulLinearEquiv (f j * f k) (f i) (glue.localModule j))
        (LocalizedModule.mk
          ((((glue.overlapIso j k).toLinearEquiv.restrictScalars R).symm
            (LocalizedModule.mk x 1 :
              Away (f j * f k) (glue.localModule k)))) 1)) =
      ((awayModuleGlueingTripleOverlapHom23 f glue.localModule glue.overlapIso i j k).symm)
        (LocalizedModule.mk x 1) := by
  -- Route correction: rewrite the explicit inverse `(2,3)` branch factor by factor, so the result
  -- is expressed using the same domain transport as the localized target component.
  rw [glue.triple_overlap_hom23_symm_apply]
  simp only
  rw [awayEqLinearEquiv_symm_apply_mk_one]
  rw [glue.triple_overlap_hom23_center_symm_apply_mk_one]
  rw [glue.triple_overlap_hom23_outer_symm_eq_domain_transport]

/-- Helper for Lemma 10.24.5: powers of the distinguished element `f i` remain invertible after
passing to the target-side overlap localization built on `Away (f i) (glue.localModule i)`. -/
theorem double_away_target_powers_isUnit
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    ∀ x : Submonoid.powers (f i),
      IsUnit
        (algebraMap R
          (Module.End R (Away (f j * f k) (Away (f i) (glue.localModule i)))) x) := by
  -- First note that `f i` is already inverted on the inner away module, then localize that unit
  -- action once more away from `f j * f k`.
  intro x
  have hx :
      IsUnit (algebraMap R (Module.End R (Away (f i) (glue.localModule i))) x) := by
    exact localizedModuleEnd_isUnit (.powers (f i)) (glue.localModule_powers_isUnit i x)
  exact localizedModuleEnd_isUnit (.powers (f j * f k)) hx

/-- Helper for Lemma 10.24.5: the left branch of the localized target comparison matches the
standard `j`-branch lift in the unit-case Cech differential. -/
noncomputable abbrev stripped_left_transport
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    Away (f j) (Away (f i) (glue.localModule i)) →ₗ[R]
      Away (f j * f k) (Away (f i) (glue.localModule i)) :=
  ((awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm.toLinearMap).comp
    (((awayEqLinearEquiv (glue.localModule i)
        (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k)).toLinearMap).comp
      (((awayMulLinearEquiv (f i * f j) (f k) (glue.localModule i)).toLinearMap).comp
        ((LocalizedModule.mkLinearMap (.powers (f k))
          (Away (f i * f j) (glue.localModule i))).comp
          (awayMulLinearEquiv (f i) (f j) (glue.localModule i)).toLinearMap)))

/-- Helper for Lemma 10.24.5: once the left branch is rewritten into the common iterated
localization model, the remaining transport is the canonical inner left lift. -/
theorem stripped_left_transport_eq_standard_target_left_inner_lift
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    (glue.stripped_left_transport i j k).comp
        (LocalizedModule.mkLinearMap (.powers (f j)) (Away (f i) (glue.localModule i))) =
      (glue.standard_target_left_inner_lift i j k).comp
        (LocalizedModule.mkLinearMap (.powers (f j)) (Away (f i) (glue.localModule i))) := by
  -- Route correction: normalize the iterated-localization transports on `x/1`, then collapse the
  -- two direct-localization routes to the common `Away (f i * (f j * f k))` model.
  ext x
  simp only [AwayModuleGlueing.stripped_left_transport, LinearMap.comp_apply,
    LocalizedModule.mkLinearMap_apply]
  have hinner :
      (awayMulLinearEquiv (f i) (f j) (glue.localModule i))
          (LocalizedModule.mk x 1) =
        awayDirectLocalizeLinearMap (f i) (f j) (glue.localModule i) x :=
    awayMulLinearEquiv_apply_mk_one_of_away (f i) (f j) (glue.localModule i) x
  have houter :
      (awayMulLinearEquiv (f i * f j) (f k) (glue.localModule i))
          (LocalizedModule.mk
            (awayDirectLocalizeLinearMap (f i) (f j) (glue.localModule i) x) 1) =
        awayDirectLocalizeLinearMap (f i * f j) (f k) (glue.localModule i)
          (awayDirectLocalizeLinearMap (f i) (f j) (glue.localModule i) x) :=
    awayMulLinearEquiv_apply_mk_one_of_away
      (f i * f j) (f k) (glue.localModule i)
      (awayDirectLocalizeLinearMap (f i) (f j) (glue.localModule i) x)
  have hcollapse :
      (awayEqLinearEquiv (glue.localModule i)
          (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k))
        (awayDirectLocalizeLinearMap (f i * f j) (f k) (glue.localModule i)
          (awayDirectLocalizeLinearMap (f i) (f j) (glue.localModule i) x)) =
      awayDirectLocalizeLinearMap (f i) (f j * f k) (glue.localModule i) x := by
    simpa [AwayModuleGlueing.localized_target_component_codomain_eq, LinearMap.comp_apply] using
      LinearMap.congr_fun
        (awayDirectLocalizeLinearMap_left_assoc (f i) (f j) (f k) (glue.localModule i)) x
  have hinner_mk :
      (LocalizedModule.mk
        ((awayMulLinearEquiv (f i) (f j) (glue.localModule i)) (LocalizedModule.mk x 1)) 1 :
        Away (f k) (Away (f i * f j) (glue.localModule i))) =
      LocalizedModule.mk
        (awayDirectLocalizeLinearMap (f i) (f j) (glue.localModule i) x) 1 := by
    simpa [hinner]
  calc
    (awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm
        ((awayEqLinearEquiv (glue.localModule i)
            (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k))
          ((awayMulLinearEquiv (f i * f j) (f k) (glue.localModule i))
            (LocalizedModule.mk
              ((awayMulLinearEquiv (f i) (f j) (glue.localModule i)) (LocalizedModule.mk x 1)) 1)))
        = (awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm
            ((awayEqLinearEquiv (glue.localModule i)
                (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k))
              ((awayMulLinearEquiv (f i * f j) (f k) (glue.localModule i))
                (LocalizedModule.mk
                  (awayDirectLocalizeLinearMap (f i) (f j) (glue.localModule i) x) 1))) := by
              rw [hinner_mk]
    _ = (awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm
          ((awayEqLinearEquiv (glue.localModule i)
              (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k))
            (awayDirectLocalizeLinearMap (f i * f j) (f k) (glue.localModule i)
              (awayDirectLocalizeLinearMap (f i) (f j) (glue.localModule i) x))) := by
            rw [houter]
    _ = (awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm
          (awayDirectLocalizeLinearMap (f i) (f j * f k) (glue.localModule i) x) := by
            rw [hcollapse]
    _ = (LocalizedModule.mk x 1 : Away (f j * f k) (Away (f i) (glue.localModule i))) := by
          rw [awayMulLinearEquiv_symm_apply_mk_one_of_away]
    _ = (glue.standard_target_left_inner_lift i j k) (LocalizedModule.mk x 1) := by
          symm
          exact glue.standard_target_left_inner_lift_apply_mk_one i j k x

/-- Helper for Lemma 10.24.5: the stripped left transport equals the standard inner left lift as a
map out of the `j`-localization of the distinguished `i`-piece. -/
theorem stripped_left_transport_eq_standard_target_left_inner
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    glue.stripped_left_transport i j k = glue.standard_target_left_inner_lift i j k := by
  -- Recover the raw map equality from the canonical-generator comparison on the `j`-localization.
  exact IsLocalizedModule.ext
    (S := .powers (f j))
    (f := LocalizedModule.mkLinearMap (.powers (f j)) (Away (f i) (glue.localModule i)))
    (map_unit := glue.standard_target_left_inner_lift_powers_isUnit i j k)
    (glue.stripped_left_transport_eq_standard_target_left_inner_lift i j k)

/-- Helper for Lemma 10.24.5: the left branch proof should compare the stripped transport with the
standard inner left lift as a map, not by adding more pointwise generator lemmas. -/
theorem localized_target_component_left_branch_normal_form
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule j) :
    (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm
      (glue.localized_target_component_equiv i j k
        (LocalizedModule.mk
          (LocalizedModule.mk x 1 : Away (f j * f k) (glue.localModule j)) 1)) =
      glue.stripped_left_transport i j k
        ((awayMulLinearEquiv (f i) (f j) (glue.localModule i)).symm
          (((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
            (LocalizedModule.mk x 1))) := by
  -- Route correction: rewrite only the `(1,2)` inverse branch on the canonical generator, then
  -- cancel the outer collapse to expose exactly the stripped transport chain.
  simp only [AwayModuleGlueing.localized_target_component_equiv, LinearEquiv.trans_apply]
  rw [LinearEquiv.symm_apply_apply, awayMulLinearEquiv_apply_mk_mk,
    awayEqLinearEquiv_apply_mk_one, glue.triple_overlap_hom12_symm_apply_mk_one]
  simp only [AwayModuleGlueing.stripped_left_transport, LinearMap.comp_apply,
    LocalizedModule.mkLinearMap_apply]
  have hcancel :
      (awayMulLinearEquiv (f i) (f j) (glue.localModule i))
          ((awayMulLinearEquiv (f i) (f j) (glue.localModule i)).symm
            (((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
              (LocalizedModule.mk x 1))) =
        (((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
          (LocalizedModule.mk x 1)) := by
    exact (awayMulLinearEquiv (f i) (f j) (glue.localModule i)).apply_symm_apply _
  have hcancel_mk :
      (LocalizedModule.mk
        ((awayMulLinearEquiv (f i) (f j) (glue.localModule i))
          ((awayMulLinearEquiv (f i) (f j) (glue.localModule i)).symm
            (((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
              (LocalizedModule.mk x 1)))) 1 :
        Away (f k) (Away (f i * f j) (glue.localModule i))) =
      LocalizedModule.mk
        (((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
          (LocalizedModule.mk x 1)) 1 := by
    simpa [hcancel]
  have hcancel_apply :
      (awayMulLinearEquiv (f i * f j) (f k) (glue.localModule i))
          (LocalizedModule.mk
            ((awayMulLinearEquiv (f i) (f j) (glue.localModule i))
              ((awayMulLinearEquiv (f i) (f j) (glue.localModule i)).symm
                (((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
                  (LocalizedModule.mk x 1)))) 1) =
        (awayMulLinearEquiv (f i * f j) (f k) (glue.localModule i))
          (LocalizedModule.mk
            (((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
              (LocalizedModule.mk x 1)) 1) := by
    exact congrArg (awayMulLinearEquiv (f i * f j) (f k) (glue.localModule i)) hcancel_mk
  exact congrArg
      (fun z ↦
        (awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm
          ((awayEqLinearEquiv (glue.localModule i)
              (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k)) z))
      hcancel_apply.symm

/-- Helper for Lemma 10.24.5: the left target branch is the standard `j`-branch lift after the
outer collapse transport is normalized. -/
theorem localized_target_component_equiv_apply_left_branch_generator
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule j) :
    glue.localized_target_component_equiv i j k
      (LocalizedModule.mk
        (LocalizedModule.mk x 1 : Away (f j * f k) (glue.localModule j)) 1) =
      glue.standard_target_left_lift i j k
        (glue.local_piece_overlap_equiv i j (LocalizedModule.mk x 1)) := by
  -- Compare both sides after removing the outer collapse equivalence from the target.
  exact (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm.injective <| by
    rw [glue.localized_target_component_left_branch_normal_form]
    rw [glue.local_piece_overlap_equiv_apply_mk_one]
    rw [LinearMap.congr_fun (glue.stripped_left_transport_eq_standard_target_left_inner i j k)]
    exact (glue.standard_target_left_lift_overlap_inner_normal_form i j k _).symm

/-- Helper for Lemma 10.24.5: the right branch of the localized target comparison matches the
standard `k`-branch lift in the unit-case Cech differential. -/
noncomputable abbrev stripped_right_transport
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    Away (f k) (Away (f i) (glue.localModule i)) →ₗ[R]
      Away (f j * f k) (Away (f i) (glue.localModule i)) :=
  ((awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm.toLinearMap).comp
    (((awayEqLinearEquiv (glue.localModule i)
        (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k)).toLinearMap).comp
      (((awayEqLinearEquiv (glue.localModule i)
          (by ring : f i * f j * f k = f i * f k * f j)).symm.toLinearMap).comp
        (((awayMulLinearEquiv (f i * f k) (f j) (glue.localModule i)).toLinearMap).comp
          ((LocalizedModule.mkLinearMap (.powers (f j))
            (Away (f i * f k) (glue.localModule i))).comp
            (awayMulLinearEquiv (f i) (f k) (glue.localModule i)).toLinearMap))))

/-- Helper for Lemma 10.24.5: once the right branch is rewritten into the common iterated
localization model, the remaining transport is the canonical inner right lift. -/
theorem stripped_right_transport_eq_standard_target_right_inner_lift
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    (glue.stripped_right_transport i j k).comp
        (LocalizedModule.mkLinearMap (.powers (f k)) (Away (f i) (glue.localModule i))) =
      (glue.standard_target_right_inner_lift i j k).comp
        (LocalizedModule.mkLinearMap (.powers (f k)) (Away (f i) (glue.localModule i))) := by
  -- Route correction: normalize the two iterated-localization transports on `x/1`, then use the
  -- explicit permutation-plus-reassociation comparison of the direct localization routes.
  ext x
  simp only [AwayModuleGlueing.stripped_right_transport, LinearMap.comp_apply,
    LocalizedModule.mkLinearMap_apply]
  have hinner :
      (awayMulLinearEquiv (f i) (f k) (glue.localModule i))
          (LocalizedModule.mk x 1) =
        awayDirectLocalizeLinearMap (f i) (f k) (glue.localModule i) x :=
    awayMulLinearEquiv_apply_mk_one_of_away (f i) (f k) (glue.localModule i) x
  have houter :
      (awayMulLinearEquiv (f i * f k) (f j) (glue.localModule i))
          (LocalizedModule.mk
            (awayDirectLocalizeLinearMap (f i) (f k) (glue.localModule i) x) 1) =
        awayDirectLocalizeLinearMap (f i * f k) (f j) (glue.localModule i)
          (awayDirectLocalizeLinearMap (f i) (f k) (glue.localModule i) x) :=
    awayMulLinearEquiv_apply_mk_one_of_away
      (f i * f k) (f j) (glue.localModule i)
      (awayDirectLocalizeLinearMap (f i) (f k) (glue.localModule i) x)
  have hcollapse :
      (awayEqLinearEquiv (glue.localModule i)
          (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k))
        ((awayEqLinearEquiv (glue.localModule i)
            (by ring : f i * f j * f k = f i * f k * f j)).symm
          (awayDirectLocalizeLinearMap (f i * f k) (f j) (glue.localModule i)
            (awayDirectLocalizeLinearMap (f i) (f k) (glue.localModule i) x))) =
      awayDirectLocalizeLinearMap (f i) (f j * f k) (glue.localModule i) x := by
    simpa [AwayModuleGlueing.localized_target_component_codomain_eq, LinearMap.comp_apply] using
      LinearMap.congr_fun
        (awayDirectLocalizeLinearMap_right_assoc (f i) (f j) (f k) (glue.localModule i)) x
  have hinner_mk :
      (LocalizedModule.mk
        ((awayMulLinearEquiv (f i) (f k) (glue.localModule i)) (LocalizedModule.mk x 1)) 1 :
        Away (f j) (Away (f i * f k) (glue.localModule i))) =
      LocalizedModule.mk
        (awayDirectLocalizeLinearMap (f i) (f k) (glue.localModule i) x) 1 := by
    simpa [hinner]
  calc
    (awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm
        ((awayEqLinearEquiv (glue.localModule i)
            (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k))
          ((awayEqLinearEquiv (glue.localModule i)
              (by ring : f i * f j * f k = f i * f k * f j)).symm
            ((awayMulLinearEquiv (f i * f k) (f j) (glue.localModule i))
              (LocalizedModule.mk
                ((awayMulLinearEquiv (f i) (f k) (glue.localModule i)) (LocalizedModule.mk x 1)) 1)))) =
        (awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm
          ((awayEqLinearEquiv (glue.localModule i)
              (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k))
            ((awayEqLinearEquiv (glue.localModule i)
                (by ring : f i * f j * f k = f i * f k * f j)).symm
              ((awayMulLinearEquiv (f i * f k) (f j) (glue.localModule i))
                (LocalizedModule.mk
                  (awayDirectLocalizeLinearMap (f i) (f k) (glue.localModule i) x) 1)))) := by
            rw [hinner_mk]
    _ = (awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm
          ((awayEqLinearEquiv (glue.localModule i)
              (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k))
            ((awayEqLinearEquiv (glue.localModule i)
                (by ring : f i * f j * f k = f i * f k * f j)).symm
              (awayDirectLocalizeLinearMap (f i * f k) (f j) (glue.localModule i)
                (awayDirectLocalizeLinearMap (f i) (f k) (glue.localModule i) x)))) := by
            rw [houter]
    _ = (awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm
          (awayDirectLocalizeLinearMap (f i) (f j * f k) (glue.localModule i) x) := by
            rw [hcollapse]
    _ = (LocalizedModule.mk x 1 : Away (f j * f k) (Away (f i) (glue.localModule i))) := by
          rw [awayMulLinearEquiv_symm_apply_mk_one_of_away]
    _ = (glue.standard_target_right_inner_lift i j k) (LocalizedModule.mk x 1) := by
          symm
          exact glue.standard_target_right_inner_lift_apply_mk_one i j k x

/-- Helper for Lemma 10.24.5: the stripped right transport equals the standard inner right lift as
a map out of the `k`-localization of the distinguished `i`-piece. -/
theorem stripped_right_transport_eq_standard_target_right_inner
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    glue.stripped_right_transport i j k = glue.standard_target_right_inner_lift i j k := by
  -- Recover the raw map equality from the canonical-generator comparison on the `k`-localization.
  exact IsLocalizedModule.ext
    (S := .powers (f k))
    (f := LocalizedModule.mkLinearMap (.powers (f k)) (Away (f i) (glue.localModule i)))
    (map_unit := glue.standard_target_right_inner_lift_powers_isUnit i j k)
    (glue.stripped_right_transport_eq_standard_target_right_inner_lift i j k)

/-- Helper for Lemma 10.24.5: the right branch proof should compare the stripped transport with
the standard inner right lift as a map, after one cocycle replacement. -/
theorem localized_target_component_right_branch_normal_form
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule k) :
    (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm
      (glue.localized_target_component_equiv i j k
        (LocalizedModule.mk
          ((((glue.overlapIso j k).toLinearEquiv.restrictScalars R).symm
            (LocalizedModule.mk x 1 : Away (f j * f k) (glue.localModule k)))) 1)) =
      glue.stripped_right_transport i j k
        ((awayMulLinearEquiv (f i) (f k) (glue.localModule i)).symm
          (((glue.overlapIso i k).toLinearEquiv.restrictScalars R).symm
            (LocalizedModule.mk x 1))) := by
  -- Route correction: rewrite the right branch through the `(2,3)` inverse, replace the cocycle
  -- suffix by the `(1,3)` inverse, and then cancel the outer collapse.
  simp only [AwayModuleGlueing.localized_target_component_equiv, LinearEquiv.trans_apply]
  rw [LinearEquiv.symm_apply_apply]
  rw [glue.localized_target_component_transport_overlap_right_generator]
  rw [glue.triple_overlap_inverse_cocycle]
  rw [glue.triple_overlap_hom13_symm_apply_mk_one]
  simp only [AwayModuleGlueing.stripped_right_transport, LinearMap.comp_apply,
    LocalizedModule.mkLinearMap_apply]
  have hcancel :
      (awayMulLinearEquiv (f i) (f k) (glue.localModule i))
          ((awayMulLinearEquiv (f i) (f k) (glue.localModule i)).symm
            (((glue.overlapIso i k).toLinearEquiv.restrictScalars R).symm
              (LocalizedModule.mk x 1))) =
        (((glue.overlapIso i k).toLinearEquiv.restrictScalars R).symm
          (LocalizedModule.mk x 1)) := by
    exact (awayMulLinearEquiv (f i) (f k) (glue.localModule i)).apply_symm_apply _
  have hcancel_mk :
      (LocalizedModule.mk
        ((awayMulLinearEquiv (f i) (f k) (glue.localModule i))
          ((awayMulLinearEquiv (f i) (f k) (glue.localModule i)).symm
            (((glue.overlapIso i k).toLinearEquiv.restrictScalars R).symm
              (LocalizedModule.mk x 1)))) 1 :
        Away (f j) (Away (f i * f k) (glue.localModule i))) =
      LocalizedModule.mk
        (((glue.overlapIso i k).toLinearEquiv.restrictScalars R).symm
          (LocalizedModule.mk x 1)) 1 := by
    simpa [hcancel]
  have hcancel_apply :
      (awayMulLinearEquiv (f i * f k) (f j) (glue.localModule i))
          (LocalizedModule.mk
            ((awayMulLinearEquiv (f i) (f k) (glue.localModule i))
              ((awayMulLinearEquiv (f i) (f k) (glue.localModule i)).symm
                (((glue.overlapIso i k).toLinearEquiv.restrictScalars R).symm
                  (LocalizedModule.mk x 1)))) 1) =
        (awayMulLinearEquiv (f i * f k) (f j) (glue.localModule i))
          (LocalizedModule.mk
            (((glue.overlapIso i k).toLinearEquiv.restrictScalars R).symm
              (LocalizedModule.mk x 1)) 1) := by
    exact congrArg (awayMulLinearEquiv (f i * f k) (f j) (glue.localModule i)) hcancel_mk
  exact congrArg
      (fun z ↦
        (awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm
          ((awayEqLinearEquiv (glue.localModule i)
              (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k))
            ((awayEqLinearEquiv (glue.localModule i)
                (by ring : f i * f j * f k = f i * f k * f j)).symm z)))
      hcancel_apply.symm

/-- Helper for Lemma 10.24.5: the right target branch is the standard `k`-branch lift after the
outer collapse transport is normalized. -/
theorem localized_target_component_equiv_apply_right_branch_generator
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule k) :
    glue.localized_target_component_equiv i j k
      (LocalizedModule.mk
        ((((glue.overlapIso j k).toLinearEquiv.restrictScalars R).symm
          (LocalizedModule.mk x 1 : Away (f j * f k) (glue.localModule k)))) 1) =
      glue.standard_target_right_lift i j k
        (glue.local_piece_overlap_equiv i k (LocalizedModule.mk x 1)) := by
  -- Compare both sides after removing the outer collapse equivalence from the target.
  exact (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm.injective <| by
    rw [glue.localized_target_component_right_branch_normal_form]
    rw [glue.local_piece_overlap_equiv_apply_mk_one]
    rw [LinearMap.congr_fun (glue.stripped_right_transport_eq_standard_target_right_inner i j k)]
    exact (glue.standard_target_right_lift_overlap_inner_normal_form i j k _).symm


end AwayModuleGlueing

end
