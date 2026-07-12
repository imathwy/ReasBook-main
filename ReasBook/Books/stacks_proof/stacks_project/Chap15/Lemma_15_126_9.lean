import Mathlib
import StacksProject_2024.Chap10.Lemma_10_19_1
import StacksProject_2024.Chap15.Lemma_15_126_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Source/core/bridge triage:
-- * source-facing: the lemma asserts stability of a system of parameters whose distinguished
--   first entry is the prescribed element `f`;
-- * core/canonical: the owner abstractions are `IsSystemOfParameters`, `parameterIdeal`, and the
--   canonical ordered family `Fin.cons f y`;
-- * bridge/view: the previous existential packaging by a family `x`, an index `i`, and an
--   equality `x i = f` was only a coordinate-level presentation of the same ordered family, so it
--   should be replaced by the owner-level `Fin.cons` form already used in Lemma `15.126.3`.
-- Proof sketch: apply Lemma `15.126.3` to choose a tail `y` such that `Fin.cons f y` is a system
-- of parameters. Since its parameter ideal is an ideal of definition, Lemma `10.32.5` gives a
-- power of the maximal ideal contained in that parameter ideal. For `h` in that power, write `h`
-- modulo the chosen parameter family so that replacing the head entry `f` by `f + h` does not
-- change the generated ideal. Equality of parameter ideals then gives both the perturbed
-- system-of-parameters statement and the equality of quotient lengths.
-- Lemma 15.126.9 proves the source-facing perturbation stability statement by comparing the two
-- parameter ideals before transporting the system-of-parameters and quotient-length conclusions.
/-- Helper for Lemma 15.126.9: adjoining a distinguished head generator splits the parameter ideal
into the head singleton span and the tail parameter ideal. -/
private theorem parameterIdeal_cons {d : ℕ} (f : maximalIdeal R) (y : Fin d → maximalIdeal R) :
    parameterIdeal (Fin.cons f y) =
      Ideal.span ({(f : R)} : Set R) ⊔ parameterIdeal y := by
  have hrange :
      Set.range (fun i : Fin (d + 1) ↦ (((Fin.cons f y : Fin (d + 1) → maximalIdeal R) i) : R)) =
        insert (f : R) (Set.range fun i : Fin d ↦ (y i : R)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨j, rfl⟩
    · intro hx
      rcases hx with rfl | hx
      · exact ⟨0, rfl⟩
      · rcases hx with ⟨j, rfl⟩
        exact ⟨j.succ, rfl⟩
  -- Rewrite the ordered family as a singleton inserted into the tail range.
  rw [parameterIdeal_eq_span, parameterIdeal_eq_span, hrange, Ideal.span_insert]

/-- Helper for Lemma 15.126.9: a power containment `𝔪^n ≤ I` upgrades to
`𝔪^(n + 1) ≤ 𝔪 * I`. -/
private theorem maximalIdeal_pow_succ_le_mul_parameterIdeal_of_pow_le
    {I : Ideal R} {n : ℕ} (hn : maximalIdeal R ^ n ≤ I) :
    maximalIdeal R ^ (n + 1) ≤ maximalIdeal R * I := by
  -- Peel off one maximal-ideal factor and use monotonicity on the right factor.
  rw [pow_succ']
  exact Ideal.mul_mono_right hn

/-- Helper for Lemma 15.126.9: an element of `𝔪 * parameterIdeal (Fin.cons f y)` splits into a
maximal-ideal multiple of the head parameter plus a remainder already in the tail ideal. -/
private theorem exists_head_tail_decomposition_of_mem_mul_parameterIdeal_cons
    {d : ℕ} (f : maximalIdeal R) (y : Fin d → maximalIdeal R) {x : R}
    (hx : x ∈ maximalIdeal R * parameterIdeal (Fin.cons f y)) :
    ∃ a : maximalIdeal R, ∃ b : R, b ∈ parameterIdeal y ∧ x = (a : R) * (f : R) + b := by
  have hxSplit :
      x ∈ maximalIdeal R * Ideal.span ({(f : R)} : Set R) ⊔
        maximalIdeal R * parameterIdeal y := by
    -- Expand the full parameter ideal into its head and tail pieces before distributing.
    rw [parameterIdeal_cons, Ideal.mul_sup] at hx
    simpa using hx
  rcases Submodule.mem_sup.mp hxSplit with ⟨u, hu, v, hv, huv⟩
  -- Normalize the principal-factor product into pointwise smul so the coefficient can be read off.
  rw [Ideal.mul_comm] at hu
  change u ∈ Ideal.span ({(f : R)} : Set R) • maximalIdeal R at hu
  rw [Submodule.ideal_span_singleton_smul] at hu
  rcases (Submodule.mem_smul_pointwise_iff_exists u (f : R) (maximalIdeal R)).1 hu with
    ⟨a, ha, hua⟩
  have hbtail : v ∈ parameterIdeal y := by
    exact (Ideal.mul_le_left : maximalIdeal R * parameterIdeal y ≤ parameterIdeal y) hv
  have hua' : u = (f : R) * a := by
    simpa [smul_eq_mul] using hua.symm
  refine ⟨⟨a, ha⟩, v, hbtail, ?_⟩
  calc
    x = u + v := huv.symm
    _ = (f : R) * a + v := by rw [hua']
    _ = (a : R) * (f : R) + v := by rw [mul_comm]

/-- Helper for Lemma 15.126.9: perturbing the distinguished head parameter by an element of
`𝔪 * parameterIdeal (Fin.cons f y)` does not change the generated parameter ideal. -/
private theorem parameterIdeal_cons_head_perturb_eq_of_mem_mul
    {d : ℕ} (f h : maximalIdeal R) (y : Fin d → maximalIdeal R)
    (hh : (h : R) ∈ maximalIdeal R * parameterIdeal (Fin.cons f y)) :
    parameterIdeal (Fin.cons (f + h) y) = parameterIdeal (Fin.cons f y) := by
  let I : Ideal R := parameterIdeal (Fin.cons f y)
  let J : Ideal R := parameterIdeal (Fin.cons (f + h) y)
  have hI :
      I = Ideal.span ({(f : R)} : Set R) ⊔ parameterIdeal y := by
    simpa [I] using parameterIdeal_cons (R := R) f y
  have hJ :
      J =
        Ideal.span ({(((f + h : maximalIdeal R) : R))} : Set R) ⊔ parameterIdeal y := by
    simpa [J] using parameterIdeal_cons (R := R) (f + h) y
  rcases exists_head_tail_decomposition_of_mem_mul_parameterIdeal_cons (R := R) f y hh with
    ⟨a, b, hb, hdecomp⟩
  have hJac : maximalIdeal R ≤ Ring.jacobson R := by
    simpa [Ideal.jacobson_bot] using
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  have hunit : IsUnit (1 + (a : R)) := by
    exact
      (ideal_le_ring_jacobson_iff_isUnit_one_add (R := R) (I := maximalIdeal R)).1 hJac
        a a.property
  have htail_le_I : parameterIdeal y ≤ I := by
    rw [hI]
    exact le_sup_right
  have htail_le_J : parameterIdeal y ≤ J := by
    rw [hJ]
    exact le_sup_right
  have hfI : (f : R) ∈ I := by
    rw [hI]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self (f : R))
  have hbI : b ∈ I := htail_le_I hb
  have hheadI : (((f + h : maximalIdeal R) : R)) ∈ I := by
    change (f : R) + (h : R) ∈ I
    have hrewrite : (f : R) + (h : R) = (1 + (a : R)) * (f : R) + b := by
      rw [hdecomp]
      ring
    rw [hrewrite]
    exact I.add_mem (I.mul_mem_left _ hfI) hbI
  have hheadJ : (((f + h : maximalIdeal R) : R)) ∈ J := by
    rw [hJ]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self (((f + h : maximalIdeal R) : R)))
  have hbJ : b ∈ J := htail_le_J hb
  have hscaled_fJ : (1 + (a : R)) * (f : R) ∈ J := by
    have htmp : ((((f + h : maximalIdeal R) : R)) - b) ∈ J := by
      exact J.sub_mem hheadJ hbJ
    have hrewrite : ((((f + h : maximalIdeal R) : R)) - b) = (1 + (a : R)) * (f : R) := by
      change (f : R) + (h : R) - b = (1 + (a : R)) * (f : R)
      rw [hdecomp]
      ring
    rw [hrewrite] at htmp
    exact htmp
  rcases hunit with ⟨u, hu⟩
  have hscaled_u : ((↑u : R) * (f : R)) ∈ J := by
    simpa [hu] using hscaled_fJ
  have hfJ : (f : R) ∈ J := by
    have hmul : ((↑u⁻¹ : R) * ((↑u : R) * (f : R))) ∈ J := by
      exact J.mul_mem_left _ hscaled_u
    simpa [mul_assoc] using hmul
  have hJI : J ≤ I := by
    rw [hJ]
    refine sup_le ?_ htail_le_I
    exact (Ideal.span_singleton_le_iff_mem I).2 hheadI
  have hIJ : I ≤ J := by
    rw [hI]
    refine sup_le ?_ htail_le_J
    exact (Ideal.span_singleton_le_iff_mem J).2 hfJ
  exact le_antisymm hJI hIJ

/-- Helper for Lemma 15.126.9: once the parameter ideals agree, both the
system-of-parameters clause and the quotient length transport across that equality. -/
private theorem isSystemOfParameters_and_length_eq_of_parameterIdeal_eq {d : ℕ}
    (x y : Fin d → maximalIdeal R) (hx : IsSystemOfParameters x)
    (hxy : parameterIdeal x = parameterIdeal y) :
    IsSystemOfParameters y ∧
      Module.length R (R ⧸ parameterIdeal x) =
        Module.length R (R ⧸ parameterIdeal y) := by
  constructor
  · -- Keep the dimension clause and rewrite only the ideal-of-definition clause.
    rw [isSystemOfParameters_iff] at hx ⊢
    exact ⟨hx.1, hxy ▸ hx.2⟩
  · -- Equal quotient ideals produce linearly equivalent quotient modules, hence equal lengths.
    exact LinearEquiv.length_eq (Submodule.quotEquivOfEq _ _ hxy)

/-- Lemma 15.126.9: write `dim R = d + 1`. If `f : maximalIdeal R` avoids every minimal prime of
`R`, then there exist `d` further parameters and an exponent `n` such that the ordered family
`Fin.cons f y` is a system of parameters, and every perturbation of the distinguished head entry by
an element of `(maximalIdeal R)^(n + 1)` again yields a system of parameters with the same
quotient length. -/
@[stacks 0BWY]
theorem exists_systemOfParameters_stable_under_highOrder_perturbation_of_not_mem_minimalPrimes
    {d : ℕ} (hdim : ringKrullDim R = d.succ) (f : maximalIdeal R)
    (hmin : ∀ p ∈ minimalPrimes R, (f : R) ∉ p) :
    ∃ y : Fin d → maximalIdeal R, ∃ n : ℕ,
      IsSystemOfParameters (Fin.cons f y) ∧
        ∀ h : maximalIdeal R, ((h : R) ∈ maximalIdeal R ^ (n + 1)) →
          IsSystemOfParameters (Fin.cons (f + h) y) ∧
            Module.length R (R ⧸ parameterIdeal (Fin.cons f y)) =
              Module.length R (R ⧸ parameterIdeal (Fin.cons (f + h) y)) := by
  rcases
    exists_systemOfParameters_cons_mem_maximalIdeal_pow_of_not_mem_minimalPrimes
      (R := R) (d := d) (k := 1) hdim f hmin with
    ⟨y, hy, _hyPow⟩
  have hpow :
      ∃ n : ℕ, maximalIdeal R ^ n ≤ parameterIdeal (Fin.cons f y) := by
    have hdef : (parameterIdeal (Fin.cons f y)).IsIdealOfDefinition := hy.2
    rw [Ideal.IsIdealOfDefinition] at hdef
    exact Ideal.exists_pow_le_of_le_radical_of_fg hdef.symm.le
      (show (maximalIdeal R).FG from Ideal.fg_of_isNoetherianRing (maximalIdeal R))
  rcases hpow with ⟨n, hn⟩
  refine ⟨y, n, hy, ?_⟩
  intro h hh
  have hhMul : (h : R) ∈ maximalIdeal R * parameterIdeal (Fin.cons f y) := by
    exact
      maximalIdeal_pow_succ_le_mul_parameterIdeal_of_pow_le (R := R)
        (I := parameterIdeal (Fin.cons f y)) hn hh
  have hparam :
      parameterIdeal (Fin.cons (f + h) y) = parameterIdeal (Fin.cons f y) := by
    -- Route correction: compare parameter ideals first, then transport both conclusions.
    exact parameterIdeal_cons_head_perturb_eq_of_mem_mul (R := R) f h y hhMul
  rcases
    isSystemOfParameters_and_length_eq_of_parameterIdeal_eq
      (R := R) (Fin.cons f y) (Fin.cons (f + h) y) hy hparam.symm with
    ⟨hpert, hlen⟩
  exact ⟨hpert, hlen⟩

end
