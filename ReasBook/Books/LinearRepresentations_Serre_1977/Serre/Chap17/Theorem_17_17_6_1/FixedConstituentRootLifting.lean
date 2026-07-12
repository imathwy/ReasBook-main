import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.FixedConstituentDeterminantSubgroup

universe u v w x

open scoped TensorProduct

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable [CharP (IsLocalRing.ResidueField A) p]
variable {h : ℕ}
variable {G : Type v} [Group G] [Finite G]
variable {V : Type x} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]

local notation "k" => IsLocalRing.ResidueField A
private noncomputable instance theorem171761TargetModule : Module A V :=
  Module.compHom V (algebraMap A k)
private instance theorem171761TargetScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.6-1: a prime-to-`p` torsion unit in the coefficient ring that reduces
to `1` is already `1`. This is the uniqueness input behind the principal-unit correction in the
determinant-normalization step. -/
theorem unit_eq_one_of_pow_eq_one_of_residue_eq_one
    (hp : Nat.Prime p)
    {u : Aˣ} {n : ℕ} (hn : Nat.Coprime p n)
    (hu : ((u : A) ^ n) = 1)
    (hres : IsLocalRing.residue A (u : A) = 1) :
    u = 1 := by
  let s : A := ∑ i ∈ Finset.range n, (u : A) ^ i
  have hn_not_dvd : ¬ p ∣ n := hp.coprime_iff_not_dvd.mp hn
  have hn_cast_ne : ((n : ℕ) : k) ≠ 0 :=
    (NeZero.of_not_dvd (R := k) hn_not_dvd).out
  have hs_res : IsLocalRing.residue A s = (n : k) := by
    -- Reducing the geometric sum termwise collapses every term to `1`.
    calc
      IsLocalRing.residue A s
          = ∑ i ∈ Finset.range n,
              IsLocalRing.residue A ((u : A) ^ i) := by
                simp [s]
      _ = ∑ i ∈ Finset.range n, (1 : k) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [map_pow]
            simpa [hres]
      _ = (n : k) := by
            simp
  have hs_unit : IsUnit s := by
    have hs_res_ne : IsLocalRing.residue A s ≠ 0 := by
      simpa [hs_res] using hn_cast_ne
    have hs_not_mem : s ∉ IsLocalRing.maximalIdeal A := by
      intro hs_mem
      exact hs_res_ne ((IsLocalRing.residue_eq_zero_iff s).2 hs_mem)
    exact (IsLocalRing.notMem_maximalIdeal).1 hs_not_mem
  have hgeom : s * ((u : A) - 1) = 0 := by
    -- The geometric-series identity closes because the chosen power of `u` is `1`.
    simpa [s, hu] using (geom_sum_mul (u : A) n)
  have hsub : (u : A) - 1 = 0 := by
    exact (IsUnit.mul_right_eq_zero hs_unit).1 hgeom
  apply Units.ext
  exact sub_eq_zero.mp hsub

/-- Helper for Theorem 17-17.6-1: if a unit reduces to `1`, then it has a `d`-th root whenever
`d` is prime to `p`. This isolates the Hensel step needed to remove the principal-unit part of a
determinant class before constructing the finite cover `G₂`. -/
theorem exists_dth_root_of_unit_of_residue_eq_one
    (hp : Nat.Prime p)
    {u : Aˣ} {d : ℕ} (hdcop : Nat.Coprime p d)
    (hres : IsLocalRing.residue A (u : A) = 1) :
    ∃ a : Aˣ, a ^ d = u := by
  have hd_ne : d ≠ 0 := by
    intro hd0
    have hp_one : p = 1 := by
      simpa [hd0] using hdcop
    exact hp.ne_one hp_one
  let f : Polynomial A := Polynomial.X ^ d - Polynomial.C (u : A)
  have hf_monic : f.Monic := by
    simpa [f] using (Polynomial.monic_X_pow_sub_C (a := (u : A)) hd_ne)
  have hTFAE := HenselianLocalRing.TFAE A
  have hresidue_lift :
      ∀ f : Polynomial A, f.Monic → ∀ a₀ : k,
        Polynomial.aeval a₀ f = 0 → Polynomial.aeval a₀ (Polynomial.derivative f) ≠ 0 →
          ∃ a : A, f.IsRoot a ∧ IsLocalRing.residue A a = a₀ := by
    -- Use the residue-field formulation of Hensel's lemma packaged in mathlib's local-ring TFAE.
    exact (List.TFAE.out hTFAE 0 1).mp (show HenselianLocalRing A from inferInstance)
  have hroot0 : Polynomial.aeval (1 : k) f = 0 := by
    -- The residue point `1` is a simple root of `X^d - u`.
    simpa [Polynomial.aeval_def, f, hres, sub_eq_zero] using (show (1 : k) ^ d = 1 by simp)
  have hderiv_ne : Polynomial.aeval (1 : k) (Polynomial.derivative f) ≠ 0 := by
    have hd_not_dvd : ¬ p ∣ d := hp.coprime_iff_not_dvd.mp hdcop
    have hd_cast_ne : ((d : ℕ) : k) ≠ 0 := (NeZero.of_not_dvd (R := k) hd_not_dvd).out
    -- The derivative of `X^d - u` at `1` is exactly `d`.
    rw [show Polynomial.aeval (1 : k) (Polynomial.derivative f) = ((d : ℕ) : k) by
          rw [show Polynomial.derivative f =
              Polynomial.derivative (Polynomial.X ^ d) by
                simp [f]]
          rw [Polynomial.derivative_X_pow]
          simp]
    exact hd_cast_ne
  obtain ⟨a, ha_root, ha_res⟩ := hresidue_lift f hf_monic (1 : k) hroot0 hderiv_ne
  have ha_pow : a ^ d = (u : A) := by
    -- Unfold the Hensel root back to the concrete power equation.
    have hroot_eq : a ^ d - (u : A) = 0 := by
      simpa [f, Polynomial.IsRoot.def] using Polynomial.IsRoot.def.mp ha_root
    exact sub_eq_zero.mp hroot_eq
  have ha_unit : IsUnit a := by
    have hpow_unit : IsUnit (a ^ d) := ha_pow ▸ u.isUnit
    exact (isUnit_pow_iff hd_ne).1 hpow_unit
  refine ⟨ha_unit.unit, ?_⟩
  -- Repackage the scalar root as an equality in the unit group.
  apply Units.ext
  simpa [ha_unit.unit_spec] using ha_pow

/-- Helper for Theorem 17-17.6-1: the Hensel lift in the principal-unit case may be chosen with
residue equal to `1`. This is the version needed when a later scalar correction must preserve a
fixed residue-field root of unity. -/
theorem exists_dth_root_of_unit_of_residue_eq_one_with_residue
    (hp : Nat.Prime p)
    {u : Aˣ} {d : ℕ} (hdcop : Nat.Coprime p d)
    (hres : IsLocalRing.residue A (u : A) = 1) :
    ∃ a : Aˣ, a ^ d = u ∧ IsLocalRing.residue A (a : A) = 1 := by
  have hd_ne : d ≠ 0 := by
    intro hd0
    have hp_one : p = 1 := by
      simpa [hd0] using hdcop
    exact hp.ne_one hp_one
  let f : Polynomial A := Polynomial.X ^ d - Polynomial.C (u : A)
  have hf_monic : f.Monic := by
    simpa [f] using (Polynomial.monic_X_pow_sub_C (a := (u : A)) hd_ne)
  have hTFAE := HenselianLocalRing.TFAE A
  have hresidue_lift :
      ∀ f : Polynomial A, f.Monic → ∀ a₀ : k,
        Polynomial.aeval a₀ f = 0 → Polynomial.aeval a₀ (Polynomial.derivative f) ≠ 0 →
          ∃ a : A, f.IsRoot a ∧ IsLocalRing.residue A a = a₀ := by
    -- Use the residue-field formulation of Hensel's lemma exactly as in the principal-unit root
    -- lemma, but now keep the residue output because the later roots-of-unity lift uses it.
    exact (List.TFAE.out hTFAE 0 1).mp (show HenselianLocalRing A from inferInstance)
  have hroot0 : Polynomial.aeval (1 : k) f = 0 := by
    -- The residue point `1` is again a simple root of `X^d - u`.
    simpa [Polynomial.aeval_def, f, hres, sub_eq_zero] using (show (1 : k) ^ d = 1 by simp)
  have hderiv_ne : Polynomial.aeval (1 : k) (Polynomial.derivative f) ≠ 0 := by
    have hd_not_dvd : ¬ p ∣ d := hp.coprime_iff_not_dvd.mp hdcop
    have hd_cast_ne : ((d : ℕ) : k) ≠ 0 := (NeZero.of_not_dvd (R := k) hd_not_dvd).out
    -- The derivative at the Hensel point is the nonzero scalar `d`.
    rw [show Polynomial.aeval (1 : k) (Polynomial.derivative f) = ((d : ℕ) : k) by
          rw [show Polynomial.derivative f =
              Polynomial.derivative (Polynomial.X ^ d) by
                simp [f]]
          rw [Polynomial.derivative_X_pow]
          simp]
    exact hd_cast_ne
  obtain ⟨a, ha_root, ha_res⟩ := hresidue_lift f hf_monic (1 : k) hroot0 hderiv_ne
  have ha_pow : a ^ d = (u : A) := by
    -- Unfold the Hensel root back to the concrete power equation.
    have hroot_eq : a ^ d - (u : A) = 0 := by
      simpa [f, Polynomial.IsRoot.def] using Polynomial.IsRoot.def.mp ha_root
    exact sub_eq_zero.mp hroot_eq
  have ha_unit : IsUnit a := by
    have hpow_unit : IsUnit (a ^ d) := ha_pow ▸ u.isUnit
    exact (isUnit_pow_iff hd_ne).1 hpow_unit
  refine ⟨ha_unit.unit, ?_, ?_⟩
  · -- Repackage the scalar root as an equality in the unit group.
    apply Units.ext
    simpa [ha_unit.unit_spec] using ha_pow
  · -- The Hensel witness was chosen over the residue point `1`, so the unit lift keeps residue
    -- `1`.
    simpa [ha_unit.unit_spec] using ha_res

/-- Helper for Theorem 17-17.6-1: a residue-field root of unity of order prime to `p` lifts to an
actual unit root of unity in `A`. This is the algebraic input behind Serre's determinant
normalization after enlarging the coefficient field. -/
theorem lift_roots_of_unity_unit_of_coprime_char
    (hp : Nat.Prime p)
    {n : ℕ} (hncop : Nat.Coprime p n)
    (ξ : rootsOfUnity n k) :
    ∃ ζ : Aˣ, ζ ^ n = 1 ∧ Units.map (IsLocalRing.residue A).toMonoidHom ζ = (ξ : kˣ) := by
  obtain ⟨ξLift, hξLift⟩ :=
    IsLocalRing.surjective_units_map_of_local_ringHom
      (IsLocalRing.residue A)
      (IsLocalRing.residue_surjective (R := A))
      (by infer_instance) (ξ : kˣ)
  let u : Aˣ := ξLift ^ n
  have hu_res : IsLocalRing.residue A (u : A) = 1 := by
    -- The chosen lift has the same `n`-th residue power as `ξ`, which is already `1`.
    have hmap_u : Units.map (IsLocalRing.residue A).toMonoidHom u = 1 := by
      calc
        Units.map (IsLocalRing.residue A).toMonoidHom u =
            (Units.map (IsLocalRing.residue A).toMonoidHom ξLift) ^ n := by
              simp [u, MonoidHom.map_pow]
        _ = (ξ : kˣ) ^ n := by rw [hξLift]
        _ = 1 := by
              exact Subtype.property ξ
    simpa using congrArg (fun z : kˣ ↦ (z : k)) hmap_u
  obtain ⟨a, ha_pow, ha_res⟩ :=
    exists_dth_root_of_unit_of_residue_eq_one_with_residue
      (A := A) (p := p) hp hncop hu_res
  refine ⟨ξLift * a⁻¹, ?_, ?_⟩
  · -- Divide the arbitrary lift by the principal-unit correction to get a literal `n`-torsion
    -- unit upstairs.
    calc
      (ξLift * a⁻¹) ^ n = ξLift ^ n * (a⁻¹) ^ n := by
        simp [mul_pow]
      _ = u * (u⁻¹) := by
        rw [inv_pow]
        rw [ha_pow]
      _ = 1 := by simp
  · -- The correction has residue `1`, so the final unit still reduces to the original root of
    -- unity `ξ`.
    have hmap_a : Units.map (IsLocalRing.residue A).toMonoidHom a = 1 := by
      apply Units.ext
      simpa using ha_res
    calc
      Units.map (IsLocalRing.residue A).toMonoidHom (ξLift * a⁻¹) =
          Units.map (IsLocalRing.residue A).toMonoidHom ξLift *
            (Units.map (IsLocalRing.residue A).toMonoidHom a)⁻¹ := by
              simp
      _ = (ξ : kˣ) * 1⁻¹ := by rw [hξLift, hmap_a]
      _ = (ξ : kˣ) := by simp

/-- Helper for Theorem 17-17.6-1: if a unit has residue equal to a `d`-th power in `kˣ`, then it
is already a literal `d`-th power in `Aˣ`. This packages the source-faithful two-step upgrade:
first lift the residue root to `Aˣ`, then remove the remaining principal-unit error by Hensel. -/
theorem exists_dth_root_of_unit_of_residue_eq_dth_power
    (hp : Nat.Prime p)
    {u : Aˣ} {d : ℕ} (hdcop : Nat.Coprime p d)
    (hres : ∃ b : kˣ, Units.map (IsLocalRing.residue A).toMonoidHom u = b ^ d) :
    ∃ a : Aˣ, a ^ d = u := by
  obtain ⟨b, hb⟩ := hres
  obtain ⟨bLift, hbLift⟩ :=
    IsLocalRing.surjective_units_map_of_local_ringHom
      (IsLocalRing.residue A)
      (IsLocalRing.residue_surjective (R := A))
      (by infer_instance) b
  let u₀ : Aˣ := u * bLift⁻¹ ^ d
  have hu₀_res : IsLocalRing.residue A (u₀ : A) = 1 := by
    -- After lifting the residue root `b`, the remaining quotient is a principal unit.
    have hmap :
        Units.map (IsLocalRing.residue A).toMonoidHom u₀ =
          Units.map (IsLocalRing.residue A).toMonoidHom u *
            (Units.map (IsLocalRing.residue A).toMonoidHom bLift⁻¹) ^ d := by
      simp [u₀, map_mul, MonoidHom.map_pow]
    have hbLift_inv :
        Units.map (IsLocalRing.residue A).toMonoidHom bLift⁻¹ = b⁻¹ := by
      simpa using congrArg Inv.inv hbLift
    have hunit_eq : Units.map (IsLocalRing.residue A).toMonoidHom u₀ = 1 := by
      calc
        Units.map (IsLocalRing.residue A).toMonoidHom u₀ =
            Units.map (IsLocalRing.residue A).toMonoidHom u *
              (Units.map (IsLocalRing.residue A).toMonoidHom bLift⁻¹) ^ d := hmap
        _ = b ^ d * (b⁻¹) ^ d := by rw [hb, hbLift_inv]
        _ = 1 := by simp [mul_comm]
    simpa using congrArg (fun z : kˣ ↦ (z : k)) hunit_eq
  obtain ⟨a₀, ha₀⟩ :=
    exists_dth_root_of_unit_of_residue_eq_one
      (A := A) (p := p) hp hdcop hu₀_res
  refine ⟨a₀ * bLift, ?_⟩
  -- Multiply the Hensel root of the principal-unit quotient by the lifted residue root.
  calc
    (a₀ * bLift) ^ d = a₀ ^ d * bLift ^ d := by simp [mul_pow]
    _ = u₀ * bLift ^ d := by rw [ha₀]
    _ = u * (bLift⁻¹ ^ d * bLift ^ d) := by
          simp [u₀, mul_assoc, mul_left_comm, mul_comm]
    _ = u := by simp

/-- Helper for Theorem 17-17.6-1: the determinants of the chosen section elements in Serre's
literal transport cover `G₁ → G` are multiplicative up to a `d`-th power, where
`d = finrank_A(P_S)`. This packages the cocycle discrepancy into the scalar kernel `Aˣ`. -/
theorem fixed_constituent_section_det_mul_eq_unit_pow
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S)
    (s t : G) :
    ∃ a : Aˣ,
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          ((fixed_constituent_transport_total_space_section
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (s * t)).2) =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            ((fixed_constituent_transport_total_space_section
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2) *
          fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            ((fixed_constituent_transport_total_space_section
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift t).2) *
          a ^ Module.finrank A P_S := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let ucomp :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (s * t) :=
    fixed_constituent_transport_fiber_comp
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 (sec t).2
  obtain ⟨a, ha⟩ :=
    fixed_constituent_transport_fiber_det_eq_section_det_mul_unit_pow_of_kernel_scalar
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
      (s * t) ucomp
  have hcomp :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) ucomp =
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 *
          fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec t).2 := by
    -- The section product in `G₁` is just composition of transport operators, so determinants
    -- multiply in the usual way.
    simpa [ucomp, mul_comm, mul_left_comm, mul_assoc] using
      fixed_constituent_transport_fiber_det_comp
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 (sec t).2
  refine ⟨a⁻¹, ?_⟩
  -- Cancel the scalar discrepancy on the right to rewrite the chosen section determinant.
  calc
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec (s * t)).2 =
      (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec (s * t)).2 *
        a ^ Module.finrank A P_S) * (a⁻¹) ^ Module.finrank A P_S := by
          simp [mul_assoc]
    _ =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) ucomp *
        (a⁻¹) ^ Module.finrank A P_S := by
          rw [ha]
    _ =
      (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 *
        fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec t).2) *
        (a⁻¹) ^ Module.finrank A P_S := by
          rw [hcomp]
    _ =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 *
        fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec t).2 *
        (a⁻¹) ^ Module.finrank A P_S := by
          ac_rfl

/-- Helper for Theorem 17-17.6-1: the determinant of the chosen section at `s ^ n` differs from
the `n`-th power of the determinant at `s` by a `d`-th power. This is the source-faithful
torsion statement modulo scalar determinants coming from the kernel `U₁ = Aˣ`. -/
theorem fixed_constituent_section_det_pow_eq_unit_pow
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S)
    (s : G) :
    ∀ n : ℕ,
      ∃ a : Aˣ,
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            ((fixed_constituent_transport_total_space_section
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift (s ^ n)).2) =
          fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              ((fixed_constituent_transport_total_space_section
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2) ^ n *
            a ^ Module.finrank A P_S := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  intro n
  induction n with
  | zero =>
      obtain ⟨a, ha⟩ :=
        fixed_constituent_transport_fiber_det_eq_section_det_mul_unit_pow_of_kernel_scalar
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
          (1 : G) (fixed_constituent_transport_fiber_one
            (A := A) (G := G) (I := I) (ρA_I := ρA_I))
      refine ⟨a⁻¹, ?_⟩
      -- At `n = 0`, compare the chosen section at `1` with the literal identity in `U₁`.
      calc
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec (s ^ 0)).2 =
          fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec 1).2 := by
                exact congrArg
                  (fun g : G =>
                    fixed_constituent_transport_fiber_det
                      (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec g).2)
                  (pow_zero s)
        _ =
          (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec 1).2 *
            a ^ Module.finrank A P_S) * (a⁻¹) ^ Module.finrank A P_S := by
              simp [mul_assoc]
        _ =
          fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)
              (fixed_constituent_transport_fiber_one
                (A := A) (G := G) (I := I) (ρA_I := ρA_I)) *
            (a⁻¹) ^ Module.finrank A P_S := by
              rw [ha]
        _ = (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ 0 *
            (a⁻¹) ^ Module.finrank A P_S := by
              change LinearEquiv.det (LinearEquiv.refl A P_S) *
                  (a⁻¹) ^ Module.finrank A P_S =
                (fixed_constituent_transport_fiber_det
                    (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ 0 *
                  (a⁻¹) ^ Module.finrank A P_S
              simp
  | succ n ihn =>
      obtain ⟨a, ha⟩ := ihn
      obtain ⟨b, hb⟩ :=
        fixed_constituent_section_det_mul_eq_unit_pow
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
          (s ^ n) s
      refine ⟨a * b, ?_⟩
      -- The cocycle statement for `(s ^ n, s)` closes the induction after combining the two
      -- scalar discrepancies.
      calc
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec (s ^ n.succ)).2 =
          fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec (s ^ n)).2 *
            fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 *
            b ^ Module.finrank A P_S := by
              rw [pow_succ]
              simpa [sec] using hb
        _ =
          ((fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ n *
            a ^ Module.finrank A P_S) *
            fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 *
            b ^ Module.finrank A P_S := by
              rw [ha]
        _ =
          (fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ n.succ *
            (a * b) ^ Module.finrank A P_S := by
              rw [pow_succ, mul_pow]
              ac_rfl

/-- Helper for Theorem 17-17.6-1: every chosen section determinant has exponent dividing
`Nat.card G` modulo `d`-th powers. This is the uniform finite-torsion owner needed before the
remaining residue-subgroup construction. -/
theorem fixed_constituent_section_det_pow_card_eq_unit_pow
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S)
    (s : G) :
    ∃ a : Aˣ,
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          ((fixed_constituent_transport_total_space_section
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2) ^
        Nat.card G =
      a ^ Module.finrank A P_S := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  obtain ⟨a, ha⟩ :=
    fixed_constituent_section_det_pow_eq_unit_pow
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
      s (Nat.card G)
  obtain ⟨b, hb⟩ :=
    fixed_constituent_section_det_pow_eq_unit_pow
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel
      s 0
  have hcard :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec 1).2 =
        (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ Nat.card G *
          a ^ Module.finrank A P_S := by
    -- Rewrite `s ^ |G|` to `1` in the general power-comparison lemma.
    have ha' := ha
    rw [pow_card_eq_one' (x := s)] at ha'
    simpa [sec] using ha'
  have hone :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec 1).2 =
        b ^ Module.finrank A P_S := by
    -- The `n = 0` case shows that the determinant at `1` is itself already a `d`-th power.
    have hb' := hb
    rw [pow_zero] at hb'
    simpa [sec] using hb'
  refine ⟨b * a⁻¹, ?_⟩
  -- Subtract the `d`-th power discrepancy contributed by the chosen section at `1`.
  calc
    (fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ Nat.card G =
      ((fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ Nat.card G *
        a ^ Module.finrank A P_S) * (a⁻¹) ^ Module.finrank A P_S := by
          simp [mul_assoc]
    _ =
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec 1).2 *
        (a⁻¹) ^ Module.finrank A P_S := by
          rw [← hcard]
    _ = b ^ Module.finrank A P_S * (a⁻¹) ^ Module.finrank A P_S := by
          rw [hone]
    _ = (b * a⁻¹) ^ Module.finrank A P_S := by
          rw [mul_pow]

/-- Helper for Theorem 17-17.6-1: after reducing a chosen section determinant to the residue
field and quotienting by `d`-th powers, the resulting class is killed by `Nat.card G`. This is
the quotient-level torsion statement available from the already proved determinant-power identity.
-/
theorem section_determinant_class_pow_card_eq_one_mod_dth_powers
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S)
    (s : G) :
    let d := Module.finrank A P_S
    let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
    let sec :=
      fixed_constituent_transport_total_space_section
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    (QuotientGroup.mk' Qd
      (Units.map (IsLocalRing.residue A).toMonoidHom
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2))) ^
      Nat.card G = 1 := by
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  obtain ⟨a, ha⟩ :=
    fixed_constituent_section_det_pow_card_eq_unit_pow
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel s
  -- Rewrite the quotient power using the already proved `d`-th-power identity upstairs in `Aˣ`.
  have hres :
      Units.map (IsLocalRing.residue A).toMonoidHom
        ((fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^ Nat.card G) =
        (Units.map (IsLocalRing.residue A).toMonoidHom a) ^ d := by
    simpa [d] using congrArg (Units.map (IsLocalRing.residue A).toMonoidHom) ha
  have hclass_one :
      QuotientGroup.mk' Qd
        (Units.map (IsLocalRing.residue A).toMonoidHom
          ((fixed_constituent_transport_fiber_det
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2) ^
            Nat.card G)) =
        1 := by
    rw [hres]
    -- The right-hand side is trivial in the quotient because it lies in the `d`-th-power subgroup.
    change QuotientGroup.mk' Qd
        ((powMonoidHom d : kˣ →* kˣ) (Units.map (IsLocalRing.residue A).toMonoidHom a)) =
      1
    exact
      (QuotientGroup.eq_one_iff
        ((powMonoidHom d : kˣ →* kˣ) (Units.map (IsLocalRing.residue A).toMonoidHom a))).2
        ⟨Units.map (IsLocalRing.residue A).toMonoidHom a, rfl⟩
  simpa [map_pow] using hclass_one

/-- Helper for Theorem 17-17.6-1: reduce the determinant of the chosen section element in Serre's
transport cover to its class modulo `d`-th powers in the residue-field units. This gives the
literal section-side generator family for the candidate subgroup that will later define `G₂`. -/
noncomputable def fixed_constituent_section_determinant_class
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    G → (kˣ ⧸ ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)) :=
  fun s ↦
    QuotientGroup.mk'
      ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
      (Units.map (IsLocalRing.residue A).toMonoidHom
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          ((fixed_constituent_transport_total_space_section
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s).2)))

/-- Helper for Theorem 17-17.6-1: reduce an element of Serre's determinant subgroup `C` to the
same residue-field quotient modulo `d`-th powers. This is the second generator family for the
explicit candidate subgroup containing the determinant-normalization data. -/
noncomputable def fixed_constituent_determinant_subgroup_residue_class
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I →
      (kˣ ⧸ ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)) :=
  fun c ↦
    QuotientGroup.mk'
      ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
      (Units.map (IsLocalRing.residue A).toMonoidHom (c : Aˣ))

/-- Helper for Theorem 17-17.6-1: the first explicit approximation to Serre's finite subgroup is
the subgroup of the residue-field quotient generated by the chosen section determinant classes and
the image of the determinant subgroup `C`. The remaining blocker is to prove this candidate is
cyclic of order prime to `p`. -/
noncomputable def fixed_constituent_projective_extension_candidate_subgroup
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    Subgroup (kˣ ⧸ ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)) :=
  Subgroup.closure
    (Set.range
        (fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) ∪
      Set.range
        (fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I))

end

end Representation
