import Mathlib
import stacks_project.Chap10.Lemma_10_101_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] [Algebra R R']
variable {I : Ideal R}
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: commutative algebra of flatness over nilpotent thickenings and injective base
  change;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `flat_quotient_comap_map_sq_of_flat_mod_ideal_and_flat_baseChange`,
  `flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes`,
  `Module.Flat.baseChange`;
- best owner abstraction: the canonical flatness predicate `Module.Flat`, with Chapter 10's
  quotient-flatness and nilpotent-ideal owners supplying the source-facing criterion;
- primitive data: the rings `R`, `R'`, the `R`-algebra structure on `R'`, the ideal `I`, and the
  `R`-module `M`;
- derived API: the flatness hypotheses on `M / IM` and `R' ⊗[R] M`, and the resulting flatness
  of `M`.

Layering:
- this item is `source-facing`: it is the textbook nilpotent-ideal criterion under an injective
  base change;
- its proof should reuse the `core/canonical` owners above rather than introduce any parallel
  flatness wrapper or alternate owner object;
- no additional `bridge/view` declaration is needed in this file.
-/

-- Proof sketch: define recursively the ideals `I₁ = I` and
-- `I_{n + 1} = comap φ ((map φ I_n)^2)` for `φ = algebraMap R R'`. Lemma `10.101.4` shows by
-- induction that each quotient `M / I_n M` is flat over `R / I_n`. Since `I` is nilpotent, the
-- images `φ(I_n)` eventually vanish; injectivity of `φ` then gives `I_n = 0` for some `n`, so the
-- flat quotient criterion yields flatness of `M` over `R`.
/-- Helper for Lemma 10.101.5: the source-proof iteration of contracted squares. -/
def iterated_contracted_square (I : Ideal R) : ℕ → Ideal R
  | 0 => I
  | n + 1 =>
      Ideal.comap (algebraMap R R')
        (Ideal.map (algebraMap R R') ((iterated_contracted_square I n) ^ 2))

/-- Helper for Lemma 10.101.5: each stage of the contracted-square iteration has flat quotient. -/
lemma flat_quotient_iterated_contracted_square
    (hflat_mod_ideal : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (hflat_baseChange : Module.Flat R' (R' ⊗[R] M)) :
    ∀ n : ℕ,
      Module.Flat (R ⧸ iterated_contracted_square (R := R) (R' := R') I n)
        (M ⧸ ((iterated_contracted_square (R := R) (R' := R') I n) •
          (⊤ : Submodule R M))) := by
  intro n
  induction n with
  | zero =>
      -- The initial stage is exactly the given flat quotient modulo `I`.
      simpa [iterated_contracted_square] using hflat_mod_ideal
  | succ n ih =>
      -- The induction step is Lemma `10.101.4` applied to the current stage ideal.
      simpa [iterated_contracted_square] using
        flat_quotient_comap_map_sq_of_flat_mod_ideal_and_flat_baseChange
          (R := R) (R' := R') (M := M)
          (I := iterated_contracted_square (R := R) (R' := R') I n)
          ih hflat_baseChange

/-- Helper for Lemma 10.101.5: every stage image is bounded by the corresponding doubled power
of the initial image ideal. -/
lemma map_iterated_contracted_square_le_image_pow_two_pow :
    ∀ n : ℕ,
      Ideal.map (algebraMap R R')
          (iterated_contracted_square (R := R) (R' := R') I n) ≤
        (Ideal.map (algebraMap R R') I) ^ (2 ^ n) := by
  intro n
  induction n with
  | zero =>
      -- At the initial stage, the estimate is the identity `φ(I) ≤ φ(I)`.
      simpa [iterated_contracted_square]
  | succ n ih =>
      -- One step of the recursion maps into the square of the previous image, so the exponent
      -- doubles.
      calc
        Ideal.map (algebraMap R R')
            (iterated_contracted_square (R := R) (R' := R') I (n + 1))
            ≤ Ideal.map (algebraMap R R')
                ((iterated_contracted_square (R := R) (R' := R') I n) ^ 2) := by
                  simpa [iterated_contracted_square] using
                    (Ideal.map_comap_le
                      (f := algebraMap R R')
                      (K := Ideal.map (algebraMap R R')
                        ((iterated_contracted_square (R := R) (R' := R') I n) ^ 2)))
        _ = (Ideal.map (algebraMap R R')
              (iterated_contracted_square (R := R) (R' := R') I n)) ^ 2 := by
              rw [Ideal.map_pow]
        _ ≤ ((Ideal.map (algebraMap R R') I) ^ (2 ^ n)) ^ 2 := by
              simpa [pow_two] using mul_le_mul ih ih
        _ = (Ideal.map (algebraMap R R') I) ^ (2 ^ (n + 1)) := by
              rw [pow_two, ← pow_add]
              congr 1
              rw [Nat.pow_succ]
              omega

/-- Helper for Lemma 10.101.5: the elementary exponent bound needed to compare nilpotence with the
doubling sequence from the source proof. -/
lemma nat_le_two_pow_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- The induction adds one on the left while doubling the right-hand side.
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left Nat.one_le_two_pow _
        _ = 2 ^ n * 2 := by rw [← two_mul, Nat.mul_comm]
        _ = 2 ^ (n + 1) := by rw [Nat.pow_succ]

/-- Helper for Lemma 10.101.5: the contracted-square iteration reaches the zero ideal once the
initial ideal is nilpotent and the algebra map is injective. -/
lemma exists_iterated_contracted_square_eq_bot
    (hI : IsNilpotent I) (hinj : Function.Injective (algebraMap R R')) :
    ∃ n : ℕ, iterated_contracted_square (R := R) (R' := R') I n = ⊥ := by
  obtain ⟨k, hk⟩ := hI
  have hk_bot : I ^ k = ⊥ := by
    simpa using hk
  have hmap_pow_bot : (Ideal.map (algebraMap R R') I) ^ k = ⊥ := by
    -- Mapping preserves powers, so nilpotence of `I` descends to the image ideal.
    simpa [Ideal.map_pow] using
      congrArg (Ideal.map (algebraMap R R')) hk_bot
  have hlarge_pow_bot : (Ideal.map (algebraMap R R') I) ^ (2 ^ k) = ⊥ := by
    -- Any later power is contained in the vanishing power.
    refine le_antisymm ?_ bot_le
    exact (Ideal.pow_le_pow_right (nat_le_two_pow_self k)).trans (le_of_eq hmap_pow_bot)
  have hstage_map_bot :
      Ideal.map (algebraMap R R')
        (iterated_contracted_square (R := R) (R' := R') I k) = ⊥ := by
    -- The image estimate now lands inside the zero power found above.
    refine le_antisymm ?_ bot_le
    exact
      (map_iterated_contracted_square_le_image_pow_two_pow
        (R := R) (R' := R') (I := I) k).trans (le_of_eq hlarge_pow_bot)
  have hstage_le_bot :
      iterated_contracted_square (R := R) (R' := R') I k ≤ ⊥ := by
    -- Injectivity identifies the kernel of `R → R'` with `⊥`, so vanishing of the mapped ideal
    -- forces vanishing of the source ideal.
    have hstage_le_ker :
        iterated_contracted_square (R := R) (R' := R') I k ≤
          RingHom.ker (algebraMap R R') :=
      (Ideal.map_eq_bot_iff_le_ker (algebraMap R R')).mp hstage_map_bot
    have hker_bot : RingHom.ker (algebraMap R R') = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot (algebraMap R R')).mp hinj
    simpa [hker_bot] using hstage_le_ker
  exact ⟨k, le_antisymm hstage_le_bot bot_le⟩

/-- Helper for Lemma 10.101.5: flatness of the quotient by the zero ideal is flatness of the
original module. -/
lemma flat_of_flat_quotient_bot
    (hflat :
      Module.Flat (R ⧸ (⊥ : Ideal R))
        (M ⧸ (((⊥ : Ideal R)) • (⊤ : Submodule R M)))) :
    Module.Flat R M := by
  have hflat_ring_quot : Module.Flat R (R ⧸ (⊥ : Ideal R)) := by
    -- The quotient ring by `⊥` is canonically the original ring.
    exact Module.Flat.of_linearEquiv (AlgEquiv.quotientBot R R).toLinearEquiv
  have hflat_quot_as_R :
      Module.Flat R (M ⧸ (((⊥ : Ideal R)) • (⊤ : Submodule R M))) := by
    -- Transitivity converts flatness over `R / 0` to flatness over `R`.
    letI : Module.Flat R (R ⧸ (⊥ : Ideal R)) := hflat_ring_quot
    letI :
        Module.Flat (R ⧸ (⊥ : Ideal R))
          (M ⧸ (((⊥ : Ideal R)) • (⊤ : Submodule R M))) := hflat
    exact Module.Flat.trans R (R ⧸ (⊥ : Ideal R))
      (M ⧸ (((⊥ : Ideal R)) • (⊤ : Submodule R M)))
  have hsmul_bot : ((⊥ : Ideal R) • (⊤ : Submodule R M)) = ⊥ := by
    simp
  -- The module quotient by `0` is canonically `M`.
  letI : Module.Flat R (M ⧸ (((⊥ : Ideal R)) • (⊤ : Submodule R M))) := hflat_quot_as_R
  exact Module.Flat.of_linearEquiv
    ((((⊥ : Ideal R) • (⊤ : Submodule R M)).quotEquivOfEqBot hsmul_bot).symm)

/-- Lemma 10.101.5: if `I` is nilpotent, `R → R'` is injective, `M / IM` is flat over `R / I`,
and the base change `R' ⊗[R] M` is flat over `R'`, then `M` is flat over `R`. -/
theorem flat_of_nilpotent_ideal_of_injective_algebraMap_of_flat_mod_ideal_and_flat_baseChange
    (hI : IsNilpotent I) (hinj : Function.Injective (algebraMap R R'))
    (hflat_mod_ideal : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (hflat_baseChange : Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat R M := by
  obtain ⟨n, hn⟩ :=
    exists_iterated_contracted_square_eq_bot
      (R := R) (R' := R') (I := I) hI hinj
  have hflat_stage :
      Module.Flat (R ⧸ iterated_contracted_square (R := R) (R' := R') I n)
        (M ⧸ ((iterated_contracted_square (R := R) (R' := R') I n) •
          (⊤ : Submodule R M))) :=
    flat_quotient_iterated_contracted_square
      (R := R) (R' := R') (M := M) (I := I)
      hflat_mod_ideal hflat_baseChange n
  have hflat_bot_quot :
      Module.Flat (R ⧸ (⊥ : Ideal R))
        (M ⧸ (((⊥ : Ideal R)) • (⊤ : Submodule R M))) := by
    -- At the vanishing stage, the inductive flat quotient is exactly the quotient by zero.
    exact hn ▸ hflat_stage
  -- Transport the final zero-stage quotient flatness back to the original module.
  exact flat_of_flat_quotient_bot (R := R) (M := M) hflat_bot_quot

end
