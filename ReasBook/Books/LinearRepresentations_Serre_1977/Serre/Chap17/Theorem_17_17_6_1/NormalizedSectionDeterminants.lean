import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_6_1.ShiftedCycleTransport

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

-- Route correction: the generic kernel-reduction API now lives upstream in
-- `KernelReductionComparison.lean`, so this file keeps only the later normalized-determinant
-- corollaries built from that shared transport lemma family.

/-- Helper for Theorem 17-17.6-1: if two elements of the same transport fiber induce the same
reduction map on the fixed constituent, then the determinant of their kernel ratio reduces to `1`.
This isolates the principal-unit conclusion from the still-open task of identifying the correct
same-fiber comparison in the normalized determinant branch. -/
theorem fixed_constituent_transport_fiber_ratio_det_residue_eq_one_of_equal_reduction
    [IsAlgClosed k]
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    {s : G}
    (u v :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s)
    (hred : red_S.comp u.toLinearMap = red_S.comp v.toLinearMap) :
    Units.map (residueUnitHom (A := A))
        (fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_transport_fiber_ratio
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v)) = 1 := by
  have hratio_comp :=
    fixed_constituent_transport_fiber_ratio_comp_right
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v
  have hratio_red :
      red_S.comp
          (fixed_constituent_transport_fiber_ratio
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v).toLinearMap =
        red_S := by
    ext y
    let x := v.symm.toLinearMap y
    have hvx : v.toLinearMap x = y := v.toLinearEquiv.apply_symm_apply y
    have hcomp_x :=
      LinearMap.congr_fun hratio_comp x
    have hred_x :=
      LinearMap.congr_fun hred x
    exact congrArg (fun z : Sbar.toSubmodule => (z : V)) <|
      calc
        red_S
            ((fixed_constituent_transport_fiber_ratio
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v).toLinearMap y) =
          red_S
            ((fixed_constituent_transport_fiber_ratio
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v).toLinearMap
              (v.toLinearMap x)) := by
            rw [hvx]
        _ = red_S (u.toLinearMap x) := by
            rw [← hcomp_x]
            rfl
        _ = red_S (v.toLinearMap x) := by
            simpa [LinearMap.comp_apply] using hred_x
        _ = red_S y := by
            rw [hvx]
  exact
    fixed_constituent_transport_fiber_det_residue_eq_one_of_reduction_eq_id
      (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
        (fixed_constituent_transport_fiber_ratio
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v)
        hratio_red

/-- Helper for Theorem 17-17.6-1: over an algebraically closed residue field, a quotient class
killed by `n` modulo `d`-th powers has a representative among the `n`-th roots of unity. -/
theorem quotient_powRangeClass_mem_rootsOfUnity_image
    [IsAlgClosed k]
    {d n : ℕ} (hn : n ≠ 0)
    (x : kˣ) :
    let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
    (QuotientGroup.mk' Qd x) ^ n = 1 →
      QuotientGroup.mk' Qd x ∈ (rootsOfUnity n k).map (QuotientGroup.mk' Qd) := by
  intro Qd hx
  have hxmem : x ^ n ∈ Qd := by
    rw [← map_pow (QuotientGroup.mk' Qd) x n] at hx
    exact (QuotientGroup.eq_one_iff (N := Qd) (x ^ n)).mp hx
  obtain ⟨y, hy⟩ := hxmem
  change y ^ d = x ^ n at hy
  obtain ⟨c0, hc0⟩ := IsAlgClosed.exists_pow_nat_eq (y : k) (Nat.pos_of_ne_zero hn)
  have hc0_ne : c0 ≠ 0 := by
    intro hc0_zero
    have hy_zero : (y : k) = 0 := by
      simpa [hc0_zero, pow_eq_zero_iff, hn] using hc0.symm
    exact y.ne_zero hy_zero
  let c : kˣ := Units.mk0 c0 hc0_ne
  have hc : c ^ n = y := by
    apply Units.ext
    simpa [c] using hc0
  let ζ : kˣ := x * (c ^ d)⁻¹
  have hζ_pow : ζ ^ n = 1 := by
    calc
      ζ ^ n = x ^ n * ((c ^ d)⁻¹) ^ n := by
        simp [ζ, mul_pow]
      _ = y ^ d * ((c ^ d) ^ n)⁻¹ := by
        rw [← hy, inv_pow]
      _ = y ^ d * ((c ^ n) ^ d)⁻¹ := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = y ^ d * (y ^ d)⁻¹ := by
        rw [hc]
      _ = 1 := mul_inv_cancel _
  refine ⟨ζ, ?_, ?_⟩
  · simpa [mem_rootsOfUnity] using hζ_pow
  · rw [QuotientGroup.mk'_eq_mk']
    refine ⟨c ^ d, ?_, ?_⟩
    · exact ⟨c, rfl⟩
    · simp [ζ, mul_assoc]

/-- Helper for Theorem 17-17.6-1: every chosen section determinant class has a representative
among the `|G|`-th roots of unity after quotienting by `d`-th powers. -/
theorem section_determinant_class_mem_card_rootsOfUnity_image
    [IsAlgClosed k]
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
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
    (s : G) :
    let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s ∈
        (rootsOfUnity (Nat.card G) k).map (QuotientGroup.mk' Qd) := by
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let x : kˣ :=
    Units.map (IsLocalRing.residue A).toMonoidHom
      (fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2)
  have hkernel :
      ∀ u :
        fixed_constituent_transport_fiber
          (A := A) (G := G) I ρA_I (1 : G),
        ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S := by
    intro u
    exact
      fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
        (A := A) (G := G) (I := I) ρA_I
        (fun f ↦
          fixed_constituent_lift_equivariant_endomorphism_scalar
            (A := A) (G := G) (V := V) hp I hIcop (ρ := ρ) (Sbar := Sbar)
            hSbar_irred
            ρA_I red_S hLiftSbar f)
        u
  have hpow : (QuotientGroup.mk' Qd x) ^ Nat.card G = 1 := by
    simpa [d, Qd, sec, x] using
      section_determinant_class_pow_card_eq_one_mod_dth_powers
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift hkernel s
  have hmem :=
    quotient_powRangeClass_mem_rootsOfUnity_image
      (A := A) (d := d) (n := Nat.card G) (Nat.card_pos (α := G)).ne' x hpow
  simpa [fixed_constituent_section_determinant_class, d, Qd, sec, x] using hmem

/-- Helper for Theorem 17-17.6-1: once the normalized `|G|`-cycle in the kernel fiber reduces to
the identity on `S̄`, the chosen section determinant class is already represented by an actual
`|G|`-th root of unity in the residue field. This separates the scalar-to-roots-of-unity bridge
from the still-open cycle-reduction induction. -/
theorem normalized_section_determinant_class_mem_card_rootsOfUnity_image
    [IsAlgClosed k]
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
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
    (s : G)
    (hcycle_id :
      fixed_constituent_endAlgHom
          (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
          ρA_I red_S hLiftSbar
          (fixed_constituent_transport_kernel_intertwiningEnd
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (fixed_constituent_section_card_cycle_kernel
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s)) =
        Representation.IntertwiningMap.id Sbar.toRepresentation) :
    let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s ∈
        (rootsOfUnity (Nat.card G) k).map (QuotientGroup.mk' Qd) := by
  exact
    section_determinant_class_mem_card_rootsOfUnity_image
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s

/-- Helper for Theorem 17-17.6-1: the missing source-faithful bridge is that each chosen section
determinant class already lands in the common `lcm`-bounded roots-of-unity subgroup. This is the
section-family analogue of the already closed determinant-subgroup normalization above. -/
theorem section_determinant_class_mem_lcm_rootsOfUnity_image
    [IsAlgClosed k]
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
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
    (s : G) :
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
    fixed_constituent_section_determinant_class
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s ∈
        (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd) := by
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
  have hbase :
      fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s ∈
        (rootsOfUnity (Nat.card G) k).map (QuotientGroup.mk' Qd) := by
    simpa [Qd] using
      section_determinant_class_mem_card_rootsOfUnity_image
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s
  have hle :
      (rootsOfUnity (Nat.card G) k).map (QuotientGroup.mk' Qd) ≤
        (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd) := by
    exact
      Subgroup.map_mono
        (rootsOfUnity_le_of_dvd (Nat.dvd_lcm_left (Nat.card G) (Nat.card C)))
  exact hle hbase

/-- Helper for Theorem 17-17.6-1: once both explicit generator families are known to lie in the
same bounded roots-of-unity subgroup, the candidate subgroup `N̄` is contained in that subgroup
by a single closure argument. This isolates the closure step from the remaining section-side
normalization and final projective-cover packaging. -/
theorem candidate_subgroup_le_rootsOfUnity_lcm_image
    [IsAlgClosed k]
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
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
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
    let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd)
    fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
        Dbar := by
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
    let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map
      (QuotientGroup.mk' Qd)
    rw [fixed_constituent_projective_extension_candidate_subgroup, Subgroup.closure_le]
    rintro x (⟨s, rfl⟩ | ⟨c, rfl⟩)
    · exact
        section_determinant_class_mem_lcm_rootsOfUnity_image
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
          hTransportLift s
    · exact
        determinant_subgroup_residue_class_mem_lcm_rootsOfUnity_image
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) c

/-- Helper for Theorem 17-17.6-1: the image of a nonzero roots-of-unity subgroup under the
residue-unit quotient map is finite. -/
theorem rootsOfUnity_quotient_image_finite
    {n : ℕ} (hn : n ≠ 0)
    (Q : Subgroup kˣ) :
    Finite ((rootsOfUnity n k).map (QuotientGroup.mk' Q)) := by
  letI : NeZero n := ⟨hn⟩
  refine Set.finite_coe_iff.mpr ?_
  refine
    (Set.finite_range
      (fun ζ : rootsOfUnity n k => QuotientGroup.mk' Q (ζ : kˣ))).subset ?_
  intro y hy
  change y ∈ Subgroup.map (QuotientGroup.mk' Q) (rootsOfUnity n k) at hy
  rw [Subgroup.mem_map] at hy
  obtain ⟨ζ, hζ, rfl⟩ := hy
  exact ⟨⟨ζ, hζ⟩, rfl⟩

/-- Helper for Theorem 17-17.6-1: the explicit candidate subgroup in the residue-field quotient is
already finite, because it is a finitely generated torsion subgroup of a commutative group. This
closes the finiteness half of Serre's determinant-normalization stage before cyclicity is imposed.
-/
theorem fixed_constituent_projective_extension_candidate_finite
    [IsAlgClosed k]
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
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
        Finite
          (fixed_constituent_projective_extension_candidate_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) := by
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
    let n := Nat.lcm (Nat.card G) (Nat.card C)
    let Dbar := (rootsOfUnity n k).map (QuotientGroup.mk' Qd)
    let Candidate :=
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    have hn : n ≠ 0 := by
      exact
        (Nat.lcm_pos
          (Nat.card_pos (α := G))
          (Nat.card_pos (α := C))).ne'
    have hDbarFinite : Finite Dbar := by
      exact rootsOfUnity_quotient_image_finite (A := A) hn Qd
    have hle : Candidate ≤ Dbar := by
      simpa [Candidate, Dbar, n, C, Qd] using
        candidate_subgroup_le_rootsOfUnity_lcm_image
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
          hTransportLift
    refine Finite.of_injective (fun x : Candidate => (⟨x.1, hle x.2⟩ : Dbar)) ?_
    intro x y hxy
    apply Subtype.ext
    have hval :
        ((⟨x.1, hle x.2⟩ : Dbar) : kˣ ⧸ Qd) =
          ((⟨y.1, hle y.2⟩ : Dbar) : kˣ ⧸ Qd) :=
      congrArg (fun z : Dbar => (z : kˣ ⧸ Qd)) hxy
    simpa using hval

/-- Helper for Theorem 17-17.6-1: the explicit residue-quotient candidate subgroup is torsion
because it is finite after determinant normalization. -/
theorem fixed_constituent_projective_extension_candidate_isTorsion
    [IsAlgClosed k]
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
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
      Monoid.IsTorsion
        (fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) := by
  have :
      Finite
        (fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) :=
    fixed_constituent_projective_extension_candidate_finite
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  exact isTorsion_of_finite

/-- Helper for Theorem 17-17.6-1: once Serre's determinant normalization produces an actual
finite subgroup `D ≤ kˣ`, cyclicity is automatic because `D` embeds in the multiplicative group of
the residue field. This isolates the later cyclicity step from the current quotient-to-upstairs
lifting blocker. -/
  theorem finite_subgroup_of_residue_units_isCyclic
      (D : Subgroup kˣ) [Finite D] :
      IsCyclic D := by
    infer_instance

/-- Helper for Theorem 17-17.6-1: in characteristic `p`, the only `p`-th root of unity in the
residue field is `1`. This is the local reduced-ring input behind the prime-to-`p` cardinal bound
for Serre's canonical bounded-exponent subgroup `D`. -/
  theorem roots_of_unity_prime_eq_bot
      (hp : Nat.Prime p) :
      rootsOfUnity p k = ⊥ := by
    letI : Fact p.Prime := ⟨hp⟩
    ext ζ
    rw [mem_rootsOfUnity, Subgroup.mem_bot]
    constructor
    · intro hζ
      apply Units.ext
      have hζ_pow : (ζ : k) ^ p = 1 := by
        simpa using congrArg (fun u : kˣ ↦ (u : k)) hζ
      have hsub_pow : ((ζ : k) - 1) ^ p = 0 := by
        rw [sub_pow_char, hζ_pow, one_pow, sub_self]
      have hsub : (ζ : k) - 1 = 0 :=
        (pow_eq_zero_iff hp.ne_zero).mp hsub_pow
      exact sub_eq_zero.mp hsub
    · intro hζ
      rw [hζ]
      simp

/-- Helper for Theorem 17-17.6-1: for nonzero `n`, the canonical subgroup of `n`-th roots of
unity in the residue field has order prime to `p`. This is Serre's closing prime-to-`p` control
once the determinant classes are placed inside a bounded-exponent subgroup
`D := rootsOfUnity n k`. -/
  theorem roots_of_unity_card_coprime_charP
      (hp : Nat.Prime p)
      {n : ℕ}
      (hn : n ≠ 0) :
      Nat.Coprime p (Nat.card (rootsOfUnity n k)) := by
    letI : Fact p.Prime := ⟨hp⟩
    letI : NeZero n := ⟨hn⟩
    rw [hp.coprime_iff_not_dvd]
    intro hdiv
    have hdiv_fintype :
        p ∣ Fintype.card (rootsOfUnity n k) := by
      have hcard :
          Nat.card (rootsOfUnity n k) = Fintype.card (rootsOfUnity n k) :=
        Nat.card_eq_fintype_card (α := rootsOfUnity n k)
      exact hcard ▸ hdiv
    obtain ⟨ζ, hζ_order⟩ :=
      exists_prime_orderOf_dvd_card (G := rootsOfUnity n k) p hdiv_fintype
    have hζ_pow_subgroup : ζ ^ p = 1 := by
      rw [← hζ_order]
      exact pow_orderOf_eq_one ζ
    have hζ_pow_units : (ζ : kˣ) ^ p = 1 := by
      exact congrArg (fun z : rootsOfUnity n k ↦ (z : kˣ)) hζ_pow_subgroup
    have hζ_mem_prime : (ζ : kˣ) ∈ rootsOfUnity p k := by
      simpa [mem_rootsOfUnity] using hζ_pow_units
    have hζ_units_one : (ζ : kˣ) = 1 := by
      have hmem_bot : (ζ : kˣ) ∈ (⊥ : Subgroup kˣ) := by
        simpa [roots_of_unity_prime_eq_bot (A := A) hp] using hζ_mem_prime
      simpa using hmem_bot
    have hζ_one : ζ = 1 := by
      apply Subtype.ext
      exact hζ_units_one
    have hp_eq_one : p = 1 := by
      calc
        p = orderOf ζ := hζ_order.symm
        _ = orderOf (1 : rootsOfUnity n k) := by rw [hζ_one]
        _ = 1 := orderOf_one
    exact hp.ne_one hp_eq_one

end

end Representation
