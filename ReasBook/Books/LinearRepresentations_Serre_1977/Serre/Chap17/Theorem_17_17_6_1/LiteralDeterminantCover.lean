import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.KernelDeterminantRoots

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

/-- Helper for Theorem 17-17.6-1: the identity element of Serre's transport total space has
determinant in the determinant subgroup `C`. -/
private theorem fixed_constituent_literal_determinant_cover_one_mem
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (1 : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I).2 ∈
      fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I := by
  -- The identity in the total space is the identity transport, whose determinant is `1 ∈ C`.
  rw [fixed_constituent_transport_total_space_one]
  have hdet :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          (fixed_constituent_transport_fiber_one
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)) =
        1 := by
    simp [fixed_constituent_transport_fiber_det, fixed_constituent_transport_fiber_one,
      Representation.Equiv.mk]
    change LinearEquiv.det (LinearEquiv.refl A P_S) = 1
    exact LinearEquiv.det_refl
  rw [hdet]
  exact
    (fixed_constituent_determinant_subgroup
      (A := A) (G := G) (I := I) ρA_I).one_mem

/-- Helper for Theorem 17-17.6-1: Serre's determinant condition is closed under multiplication
in the transport total space. -/
private theorem fixed_constituent_literal_determinant_cover_mul_mem
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {g h : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I}
    (hg :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.2 ∈
        fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I)
    (hh :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) h.2 ∈
        fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) (g * h).2 ∈
      fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I := by
  -- Multiplication in `G₁` composes fibers, so determinants multiply in the order `det h * det g`.
  rw [fixed_constituent_transport_total_space_mul_eq]
  dsimp [fixed_constituent_transport_total_space_mul]
  rw [fixed_constituent_transport_fiber_det_comp]
  exact
    (fixed_constituent_determinant_subgroup
      (A := A) (G := G) (I := I) ρA_I).mul_mem hh hg

/-- Helper for Theorem 17-17.6-1: Serre's determinant condition is closed under inversion in the
transport total space. -/
private theorem fixed_constituent_literal_determinant_cover_inv_mem
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {g : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I}
    (hg :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.2 ∈
        fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I) :
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) (g⁻¹).2 ∈
      fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I := by
  -- The inverse in `G₁` uses the inverse fiber operator, whose determinant is the inverse unit.
  change
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_inv
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.2) ∈
      fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  rw [fixed_constituent_transport_fiber_det_inv]
  exact
    (fixed_constituent_determinant_subgroup
      (A := A) (G := G) (I := I) ρA_I).inv_mem hg

/-- Helper for Theorem 17-17.6-1: Serre's literal determinant-normalized cover is the subgroup of
the total transport space cut out by the source condition `det(t) ∈ C`. This names the source
object that the later finite cover should use, instead of rebuilding it ad hoc inside the kernel
proof. -/
noncomputable def fixed_constituent_literal_determinant_cover_local
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    Subgroup (fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) :=
  { carrier :=
      { g |
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.2 ∈
          fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I }
    one_mem' :=
      fixed_constituent_literal_determinant_cover_one_mem
        (A := A) (G := G) (I := I) ρA_I
    mul_mem' :=
      fun hg hh =>
        fixed_constituent_literal_determinant_cover_mul_mem
          (A := A) (G := G) (I := I) ρA_I hg hh
    inv_mem' :=
      fun hg =>
        fixed_constituent_literal_determinant_cover_inv_mem
          (A := A) (G := G) (I := I) ρA_I hg }

/-- Helper for Theorem 17-17.6-1: every Hall-kernel generator already lies in the literal
determinant cover, because its determinant is one of the defining generators of `C`. -/
theorem fixed_constituent_embed_hall_kernel_mem_literal_determinant_cover_local
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (x : I) :
    (⟨(x : G),
        fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) x⟩ :
      fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) ∈
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I := by
  change
    fixed_constituent_transport_fiber_det
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) x) ∈
      fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  rw [fixed_constituent_transport_fiber_det_of_hall_kernel_element]
  exact Subgroup.subset_closure ⟨x, rfl⟩

/-- Helper for Theorem 17-17.6-1: the quotienting subgroup `I₂ ≤ G₂` is already contained in the
literal determinant cover. This closes the Hall-kernel branch of the future source-faithful
replacement `G₂(det)` before the normalized-section branch is added. -/
theorem fixed_constituent_generated_cover_hall_kernel_subgroup_mem_literal_determinant_cover_local
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
    (y :
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) :
    (((y : fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) :
        fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) ∈
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I) := by
  rcases y.2 with ⟨x, hx⟩
  rw [← hx]
  exact
    fixed_constituent_embed_hall_kernel_mem_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I x

/-- Helper for Theorem 17-17.6-1: restricting the total-space projection `G₁ → G` to Serre's
literal determinant cover gives the source-faithful projection `G₂(det) → G`. This packages the
literal owner before quotienting by the Hall-kernel image. -/
noncomputable def fixed_constituent_literal_determinant_cover_proj_hom
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I →* G :=
  (fixed_constituent_transport_total_space_proj_hom
    (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
    (Subgroup.subtype
      (fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I))

/-- Helper for Theorem 17-17.6-1: a scalar unit gives a point of the kernel transport fiber
whose determinant is the scalar raised to the fixed lifted constituent rank. -/
private theorem exists_fixed_constituent_scalar_transport_fiber_one_det
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (a : Aˣ) :
    ∃ u : fixed_constituent_transport_fiber (A := A) (G := G) I ρA_I (1 : G),
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u =
        a ^ Module.finrank A P_S := by
  refine ⟨?_, ?_⟩
  · refine Representation.Equiv.mk (a • LinearEquiv.refl A P_S) ?_
    intro g
    ext x
    simp
  · change LinearEquiv.det (a • LinearEquiv.refl A P_S) = a ^ Module.finrank A P_S
    exact linearEquiv_det_unit_smul_refl (A := A) (M := P_S) a

/-- Helper for Theorem 17-17.6-1: if the chosen section determinant class at `s` already matches
one class coming from Serre's determinant subgroup `C`, then a single scalar kernel correction
moves the chosen section value into the literal determinant cover over `s`. This isolates the
exact adjustment step needed before proving surjectivity of `G₂(det) → G`. -/
theorem section_value_mem_literal_determinant_cover_with_det_eq
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (hdcop : Nat.Coprime p (Module.finrank A P_S))
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
    (c :
      fixed_constituent_determinant_subgroup
        (A := A) (G := G) (I := I) ρA_I)
    (hclass :
      fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s =
        fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I c) :
    ∃ g :
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I,
      fixed_constituent_literal_determinant_cover_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g = s ∧
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.1.2 = c := by
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let detSec : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let res : Aˣ →* kˣ := Units.map (IsLocalRing.residue A).toMonoidHom
  have hclassQ :
      QuotientGroup.mk' Qd (res detSec) =
        QuotientGroup.mk' Qd (res (c : Aˣ)) := by
    simpa only [fixed_constituent_section_determinant_class,
      fixed_constituent_determinant_subgroup_residue_class, sec, detSec, Qd, d, res]
      using hclass
  have hratio_mem : res (c : Aˣ) / res detSec ∈ Qd := by
    exact (QuotientGroup.eq_iff_div_mem).mp hclassQ.symm
  obtain ⟨b, hb⟩ := hratio_mem
  have hratio_res :
      res ((c : Aˣ) * detSec⁻¹) = b ^ d := by
    calc
      res ((c : Aˣ) * detSec⁻¹) = res (c : Aˣ) * (res detSec)⁻¹ := by
        simp [res]
      _ = res (c : Aˣ) / res detSec := rfl
      _ = b ^ d := by
        simpa [Qd, d] using hb.symm
  obtain ⟨a, ha_pow⟩ :=
    exists_dth_root_of_unit_of_residue_eq_dth_power
      (A := A) (p := p) (u := (c : Aˣ) * detSec⁻¹) (d := d)
      hp hdcop ⟨b, hratio_res⟩
  obtain ⟨scalarFiber, hscalar_det⟩ :=
    exists_fixed_constituent_scalar_transport_fiber_one_det
      (A := A) (G := G) (I := I) ρA_I a
  let scalarTotal :
      fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I :=
    ⟨1, scalarFiber⟩
  let gRaw :
      fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I :=
    scalarTotal * sec s
  have hgRaw_det :
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) gRaw.2 =
        (c : Aˣ) := by
    calc
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) gRaw.2 =
          fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2 *
          fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) scalarFiber := by
            simpa [gRaw, scalarTotal, fixed_constituent_transport_total_space_mul_eq]
              using fixed_constituent_transport_fiber_det_comp
                (A := A) (G := G) (I := I) (ρA_I := ρA_I)
                scalarFiber (sec s).2
      _ = detSec * a ^ d := by
            simp [detSec, d, hscalar_det]
      _ = detSec * ((c : Aˣ) * detSec⁻¹) := by
            rw [ha_pow]
      _ = (c : Aˣ) := by
            simp [mul_left_comm]
  have hgRaw_mem :
      gRaw ∈ fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I := by
    change
      fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) gRaw.2 ∈
        fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    rw [hgRaw_det]
    exact c.property
  let g :
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I :=
    ⟨gRaw, hgRaw_mem⟩
  refine ⟨g, ?_, ?_⟩
  · change gRaw.1 = s
    simpa [gRaw, scalarTotal, fixed_constituent_transport_total_space_mul_eq,
      fixed_constituent_transport_total_space_mul, fixed_constituent_transport_total_space_proj,
      sec] using
      fixed_constituent_transport_total_space_proj_section
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s
  · simpa [g] using hgRaw_det

/-- Helper for Theorem 17-17.6-1: if the chosen section determinant class at `s` already matches
one class coming from Serre's determinant subgroup `C`, then a single scalar kernel correction
moves the chosen section value into the literal determinant cover over `s`. This isolates the
exact adjustment step needed before proving surjectivity of `G₂(det) → G`. -/
theorem section_value_mem_literal_determinant_cover_of_section_class_eq
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (hdcop : Nat.Coprime p (Module.finrank A P_S))
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
    (c :
      fixed_constituent_determinant_subgroup
        (A := A) (G := G) (I := I) ρA_I)
    (hclass :
      fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s =
        fixed_constituent_determinant_subgroup_residue_class
          (A := A) (G := G) (I := I) ρA_I c) :
    ∃ g :
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I,
      fixed_constituent_literal_determinant_cover_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g = s := by
  obtain ⟨g, hg_proj, _⟩ :=
    section_value_mem_literal_determinant_cover_with_det_eq
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred hdcop ρA_I red_S hLiftSbar hTransport hTransportLift
      s c hclass
  exact ⟨g, hg_proj⟩

/-- Helper for Theorem 17-17.6-1: once every chosen section determinant class is known to come
from Serre's determinant subgroup `C`, the literal determinant-cover projection `G₂(det) → G` is
surjective by applying the previous scalar-adjustment step fiberwise. This leaves the remaining
literal-cover pivot blocked only on proving the section-class equality itself. -/
theorem
    fixed_constituent_literal_determinant_cover_proj_surjective_of_section_class_lands_in_determinant_subgroup
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (hdcop : Nat.Coprime p (Module.finrank A P_S))
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
    (hsection :
      ∀ s : G,
        ∃ c :
          fixed_constituent_determinant_subgroup
            (A := A) (G := G) (I := I) ρA_I,
          fixed_constituent_section_determinant_class
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s =
            fixed_constituent_determinant_subgroup_residue_class
              (A := A) (G := G) (I := I) ρA_I c) :
    Function.Surjective
      (fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)) := by
  intro s
  obtain ⟨c, hclass⟩ := hsection s
  exact
    section_value_mem_literal_determinant_cover_of_section_class_eq
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred hdcop ρA_I red_S hLiftSbar hTransport hTransportLift
      s c hclass

/-- Helper for Theorem 17-17.6-1: the literal Hall-kernel embedding `I → G₁` already lands in
the determinant-normalized cover, so it cod-restricts to Serre's literal owner `G₂(det)`. -/
noncomputable def fixed_constituent_literal_determinant_cover_embed_hall_kernel
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    I →*
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I :=
  MonoidHom.codRestrict
    (fixed_constituent_transport_total_space_embed_hall_kernel
      (A := A) (G := G) (I := I) (ρA_I := ρA_I))
    (fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I)
    (fun x ↦
      fixed_constituent_embed_hall_kernel_mem_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I x)

/-- Helper for Theorem 17-17.6-1: after cod-restricting to the literal determinant cover, the
embedded Hall-kernel point still projects to the original Hall-kernel element in `G`. -/
@[simp] private theorem fixed_constituent_literal_determinant_cover_proj_apply_embed_hall_kernel
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (x : I) :
    fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_literal_determinant_cover_embed_hall_kernel
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) x) =
      x := by
  rfl

/-- Helper for Theorem 17-17.6-1: Serre's literal subgroup `I₂(det) ≤ G₂(det)` is the range of
the Hall-kernel embedding into the determinant-normalized cover. This isolates the literal owner
that the remaining quotient package should use. -/
noncomputable def fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    Subgroup
      (fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I) :=
  (fixed_constituent_literal_determinant_cover_embed_hall_kernel
    (A := A) (G := G) (I := I) (ρA_I := ρA_I)).range

omit [HenselianLocalRing A] [CharP (IsLocalRing.ResidueField A) p] [Finite G] in
/-- Helper for Theorem 17-17.6-1: transport-fiber elements over equal group elements are
heterogeneously equal when their underlying maps on the fixed lift carrier agree. -/
private theorem fixed_constituent_literal_transport_fiber_heq_of_apply_eq
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s t : G} (hst : s = t)
    {u : fixed_constituent_transport_fiber (A := A) (G := G) I ρA_I s}
    {v : fixed_constituent_transport_fiber (A := A) (G := G) I ρA_I t}
    (h : ∀ z : P_S, u z = v z) :
    HEq u v := by
  subst t
  apply heq_of_eq
  ext z
  exact h z

/-- Helper for Theorem 17-17.6-1: the embedded Hall-kernel copy in the transport total space is
stable under conjugation, with conjugation computed on the ambient group coordinate. -/
private theorem fixed_constituent_transport_total_space_conj_embed_hall_kernel_of_coe_eq
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (g : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I)
    (x y : I)
    (hy : (y : G) = g.1 * (x : G) * g.1⁻¹) :
    g * fixed_constituent_transport_total_space_embed_hall_kernel
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x * g⁻¹ =
      fixed_constituent_transport_total_space_embed_hall_kernel
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) y := by
  apply Sigma.ext
  · exact hy.symm
  · refine fixed_constituent_literal_transport_fiber_heq_of_apply_eq I ρA_I hy.symm ?_
    intro z
    change
      (fixed_constituent_transport_fiber_comp
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_fiber_comp
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
          g.2
          (fixed_constituent_transport_fiber_of_hall_kernel_element
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) x))
        (fixed_constituent_transport_fiber_inv
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.2)) z =
      (fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) y) z
    unfold fixed_constituent_transport_fiber_comp
    rw [Representation.Equiv.trans_apply]
    rw [Representation.Equiv.trans_apply]
    unfold fixed_constituent_transport_fiber_inv
    unfold fixed_constituent_transport_fiber_of_hall_kernel_element
    simp only [Representation.Equiv.mk_apply, LinearEquiv.ofBijective_apply]
    change g.2 ((ρA_I x) (g.2.symm z)) = (ρA_I y) z
    have hy_symm : (MulEquiv.symm (MulAut.conjNormal g.1)) y = x := by
      ext
      simp [hy, mul_assoc]
    have happly : g.2 (g.2.symm z) = z := by
      exact Representation.Equiv.apply_symm_apply g.2 z
    have hraw := LinearMap.congr_fun (g.2.isIntertwining' y) (g.2.symm z)
    have h :
        g.2 ((ρA_I x) (g.2.symm z)) =
          (ρA_I y) (g.2 (g.2.symm z)) := by
      simpa [hy_symm] using hraw
    rw [happly] at h
    exact h

/-- Helper for Theorem 17-17.6-1: the Hall-kernel range inside the literal determinant cover is
normal, so the literal quotient `G₂(det) / I₂(det)` is available. -/
instance fixed_constituent_literal_determinant_cover_hall_kernel_subgroup_normal
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    (fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
      (A := A) (G := G) (I := I) ρA_I).Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  rcases hn with ⟨x, rfl⟩
  have y_mem : g.1.1 * (x : G) * g.1.1⁻¹ ∈ I :=
    Subgroup.Normal.conj_mem (H := I) inferInstance (x : G) x.property g.1.1
  let y : I := ⟨g.1.1 * (x : G) * g.1.1⁻¹, y_mem⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  symm
  change
    g.1 * fixed_constituent_transport_total_space_embed_hall_kernel
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) x * g.1⁻¹ =
    fixed_constituent_transport_total_space_embed_hall_kernel
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) y
  exact
    fixed_constituent_transport_total_space_conj_embed_hall_kernel_of_coe_eq
      (A := A) (G := G) (I := I) ρA_I g.1 x y rfl

/-- Helper for Theorem 17-17.6-1: the literal determinant-cover projection to `G` descends to
`G / I` and kills the embedded Hall-kernel range on the nose. This is the quotient-side owner
map that the remaining source-faithful package should descend through. -/
theorem fixed_constituent_literal_determinant_cover_hall_kernel_subgroup_le_ker_proj_to_quotient
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
        (A := A) (G := G) (I := I) ρA_I ≤
      ((QuotientGroup.mk' I).comp
        (fixed_constituent_literal_determinant_cover_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I))).ker := by
  rintro y ⟨x, rfl⟩
  change QuotientGroup.mk' I (x : G) = 1
  exact (QuotientGroup.eq_one_iff (x : G)).2 x.2

/-- Helper for Theorem 17-17.6-1: Serre's literal projection `G₂(det) → G` descends through the
embedded Hall-kernel range to a quotient map `G₂(det) / I₂(det) → G / I`. This isolates the
formal quotient owner used in the literal-cover pivot before any finite-kernel analysis. -/
noncomputable def fixed_constituent_literal_determinant_cover_proj_to_quotient
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    (fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I ⧸
      fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
        (A := A) (G := G) (I := I) ρA_I) →* G ⧸ I :=
  QuotientGroup.lift
    (fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
      (A := A) (G := G) (I := I) ρA_I)
    ((QuotientGroup.mk' I).comp
      (fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)))
    (fixed_constituent_literal_determinant_cover_hall_kernel_subgroup_le_ker_proj_to_quotient
      (A := A) (G := G) (I := I) ρA_I)

/-- Helper for Theorem 17-17.6-1: if the literal determinant cover already surjects onto `G`,
then the descended quotient map `G₂(det) / I₂(det) → G / I` is surjective as well. This closes
the purely formal descent step of the literal-cover pivot independently of the harder kernel
analysis. -/
theorem fixed_constituent_literal_determinant_cover_proj_to_quotient_surjective_of_proj_surjective
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (hproj_surj :
      Function.Surjective
        (fixed_constituent_literal_determinant_cover_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I))) :
    Function.Surjective
      (fixed_constituent_literal_determinant_cover_proj_to_quotient
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)) := by
  have hproj_to_quotient_surj :
      Function.Surjective
        (((QuotientGroup.mk' I).comp
          (fixed_constituent_literal_determinant_cover_proj_hom
            (A := A) (G := G) (I := I) (ρA_I := ρA_I))) :
          fixed_constituent_literal_determinant_cover_local
            (A := A) (G := G) (I := I) ρA_I →* G ⧸ I) := by
    intro q
    rcases QuotientGroup.mk'_surjective I q with ⟨s, rfl⟩
    obtain ⟨g, hg⟩ := hproj_surj s
    refine ⟨g, ?_⟩
    exact congrArg (QuotientGroup.mk' I) hg
  exact
    QuotientGroup.lift_surjective_of_surjective
      (fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
        (A := A) (G := G) (I := I) ρA_I)
      ((QuotientGroup.mk' I).comp
        (fixed_constituent_literal_determinant_cover_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)))
      hproj_to_quotient_surj
      (fixed_constituent_literal_determinant_cover_hall_kernel_subgroup_le_ker_proj_to_quotient
        (A := A) (G := G) (I := I) ρA_I)

/-- Helper for Theorem 17-17.6-1: once every chosen section determinant class is known to come
from Serre's determinant subgroup `C`, the literal determinant-cover quotient map
`G₂(det) / I₂(det) → G / I` is already surjective. This packages the exact literal-cover pivot
requested by the current source-faithful fallback route before any kernel analysis on
`ker(pi₂(det))`. -/
theorem
    fixed_constituent_literal_determinant_cover_proj_to_quotient_surjective_of_section_class_lands_in_determinant_subgroup
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (hdcop : Nat.Coprime p (Module.finrank A P_S))
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
    (hsection :
      ∀ s : G,
        ∃ c :
          fixed_constituent_determinant_subgroup
            (A := A) (G := G) (I := I) ρA_I,
          fixed_constituent_section_determinant_class
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s =
            fixed_constituent_determinant_subgroup_residue_class
              (A := A) (G := G) (I := I) ρA_I c) :
    Function.Surjective
      (fixed_constituent_literal_determinant_cover_proj_to_quotient
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)) := by
  exact
    fixed_constituent_literal_determinant_cover_proj_to_quotient_surjective_of_proj_surjective
      (A := A) (G := G) (I := I) ρA_I
      (fixed_constituent_literal_determinant_cover_proj_surjective_of_section_class_lands_in_determinant_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred hdcop ρA_I red_S hLiftSbar hTransport
        hTransportLift hsection)

/-- Helper for Theorem 17-17.6-1: surjectivity of the literal determinant-cover projection gives
the first-isomorphism equivalence `((G₂(det) / I₂(det)) / ker(pi₂(det))) ≃ G / I`. This packages
the quotient-kernel part of Serre's literal finite cover independently of the later cyclicity and
coprimality analysis on the kernel. -/
noncomputable def fixed_constituent_literal_determinant_cover_kernel_quotient_equiv_of_proj_surjective
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (hproj_surj :
      Function.Surjective
        (fixed_constituent_literal_determinant_cover_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I))) :
    (((fixed_constituent_literal_determinant_cover_local
          (A := A) (G := G) (I := I) ρA_I) ⧸
        (fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
          (A := A) (G := G) (I := I) ρA_I)) ⧸
      (fixed_constituent_literal_determinant_cover_proj_to_quotient
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).ker) ≃* (G ⧸ I) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (fixed_constituent_literal_determinant_cover_proj_to_quotient
      (A := A) (G := G) (I := I) (ρA_I := ρA_I))
    (fixed_constituent_literal_determinant_cover_proj_to_quotient_surjective_of_proj_surjective
      (A := A) (G := G) (I := I) ρA_I hproj_surj)

end

end Representation
