import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_6_1.SameFiberScalarAdjustments

/-!
This module contains the source-faithful kernel control for Serre's literal determinant cover.
The generated-cover kernel route only gives quotient-level determinant control, while the literal
cover carries the actual condition `det(t) ∈ C`.
-/

universe u v w x

open scoped TensorProduct

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable [CharP (IsLocalRing.ResidueField A) p]
variable {G : Type v} [Group G] [Finite G]
variable {V : Type x} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable [IsAlgClosed (IsLocalRing.ResidueField A)]

local notation "k" => IsLocalRing.ResidueField A
private noncomputable instance theorem171761TargetModule : Module A V :=
  Module.compHom V (algebraMap A k)
private instance theorem171761TargetScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.6-1: an element of the actual kernel of Serre's literal determinant
cover projection is a scalar point whose scalar has `d`-th power in the determinant subgroup
`C`. -/
theorem literal_determinant_cover_kernel_scalar_exists
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
    (z :
      (fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).ker) :
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let d := Module.finrank A P_S
    ∃ a : C.comap (powMonoidHom d : Aˣ →* Aˣ),
      z.1.1.2.toLinearEquiv = (a : Aˣ) • LinearEquiv.refl A P_S := by
  dsimp
  let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  let d := Module.finrank A P_S
  let pi :=
    fixed_constituent_literal_determinant_cover_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  have hz_proj : z.1.1.1 = 1 := by
    have hz : pi z.1 = 1 := z.2
    simpa [pi, fixed_constituent_literal_determinant_cover_proj_hom,
      fixed_constituent_transport_total_space_proj_hom,
      fixed_constituent_transport_total_space_proj] using hz
  cases hraw : z.1.1 with
  | mk s u =>
      have hs : s = 1 := by
        simpa [hraw] using hz_proj
      subst s
      have hscalar :
          ∀ f : ρA_I.IntertwiningMap ρA_I,
            ∃ a : A, f = a • Representation.IntertwiningMap.id ρA_I := by
        intro f
        exact
          fixed_constituent_lift_equivariant_endomorphism_scalar
            (A := A) (G := G) (V := V) hp I hIcop (ρ := ρ) (Sbar := Sbar)
            hSbar_irred ρA_I red_S hLiftSbar f
      obtain ⟨a, ha⟩ :=
        fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
          (A := A) (G := G) (I := I) ρA_I hscalar u
      have hdet_mem : fixed_constituent_transport_fiber_det
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u ∈ C := by
        simpa [C, hraw] using z.1.2
      have ha_mem : a ^ d ∈ C := by
        rw [← fixed_constituent_transport_kernel_det_eq_unit_pow
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) ha]
        exact hdet_mem
      exact ⟨⟨a, ha_mem⟩, ha⟩

/-- Helper for Theorem 17-17.6-1: the scalar attached to an actual literal-cover kernel element,
viewed in Serre's determinant-root subgroup. -/
noncomputable def literal_determinant_cover_kernel_scalar
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
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let d := Module.finrank A P_S
    (fixed_constituent_literal_determinant_cover_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).ker →
      C.comap (powMonoidHom d : Aˣ →* Aˣ) :=
  fun z ↦
    Classical.choose
      (literal_determinant_cover_kernel_scalar_exists
        (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar z)

/-- Helper for Theorem 17-17.6-1: the scalar chosen for an actual literal-cover kernel element
has the expected underlying transport operator. -/
theorem literal_determinant_cover_kernel_scalar_spec
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
    (z :
      (fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).ker) :
    z.1.1.2.toLinearEquiv =
      ((literal_determinant_cover_kernel_scalar
        (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar z : _) : Aˣ) •
        LinearEquiv.refl A P_S := by
  simpa [literal_determinant_cover_kernel_scalar] using
    Classical.choose_spec
      (literal_determinant_cover_kernel_scalar_exists
        (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar z)

/-- Helper for Theorem 17-17.6-1: multiplication in the actual literal-cover projection kernel
composes the underlying transport operators in Serre's total-space order. -/
theorem literal_determinant_cover_kernel_toLinearEquiv_mul
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (z₁ z₂ :
      (fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).ker) :
    (z₁ * z₂).1.1.2.toLinearEquiv =
      z₂.1.1.2.toLinearEquiv.trans z₁.1.1.2.toLinearEquiv := by
  change
    ((z₁.1 * z₂.1 :
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I).1.2.toLinearEquiv) =
      z₂.1.1.2.toLinearEquiv.trans z₁.1.1.2.toLinearEquiv
  change
    ((z₁.1.1 * z₂.1.1 :
      fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I).2.toLinearEquiv) =
      z₂.1.1.2.toLinearEquiv.trans z₁.1.1.2.toLinearEquiv
  rw [fixed_constituent_transport_total_space_mul_eq]
  change
    (fixed_constituent_transport_fiber_comp
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      z₁.1.1.2 z₂.1.1.2).toLinearEquiv =
      z₂.1.1.2.toLinearEquiv.trans z₁.1.1.2.toLinearEquiv
  rfl

/-- Helper for Theorem 17-17.6-1: the scalar attached to a literal-cover kernel element is
unique once the fixed lift has positive rank. -/
theorem literal_determinant_cover_kernel_scalar_unique
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
    (z :
      (fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).ker)
    {a b : Aˣ}
    (ha : z.1.1.2.toLinearEquiv = a • LinearEquiv.refl A P_S)
    (hb : z.1.1.2.toLinearEquiv = b • LinearEquiv.refl A P_S) :
    a = b := by
  have hfinrank_ne_zero : Module.finrank A P_S ≠ 0 :=
    fixed_constituent_lift_finrank_ne_zero
      (A := A) (G := G) (I := I) hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
  have hfinrank_pos : 0 < Module.finrank A P_S :=
    Nat.pos_of_ne_zero hfinrank_ne_zero
  letI : Nontrivial P_S := Module.nontrivial_of_finrank_pos (R := A) hfinrank_pos
  exact unit_smul_linearEquiv_refl_injective (A := A) (M := P_S) (ha.symm.trans hb)

/-- Helper for Theorem 17-17.6-1: literal-cover kernel fibers over equal group elements are
heterogeneously equal when their underlying linear equivalences agree. -/
theorem literal_determinant_cover_transport_fiber_heq_of_toLinearEquiv_eq
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s t : G} (hst : s = t)
    {u : fixed_constituent_transport_fiber (A := A) (G := G) I ρA_I s}
    {v : fixed_constituent_transport_fiber (A := A) (G := G) I ρA_I t}
    (h : u.toLinearEquiv = v.toLinearEquiv) :
    HEq u v := by
  subst t
  apply heq_of_eq
  exact Equiv.toLinearEquiv_injective h

/-- Helper for Theorem 17-17.6-1: the scalar extraction from Serre's actual literal-cover
projection kernel is a homomorphism into the determinant-root subgroup. -/
noncomputable def literal_determinant_cover_kernel_scalar_hom
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
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let d := Module.finrank A P_S
    (fixed_constituent_literal_determinant_cover_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).ker →*
      C.comap (powMonoidHom d : Aˣ →* Aˣ) := by
  dsimp
  let scalar :=
    literal_determinant_cover_kernel_scalar
      (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
  refine
    { toFun := scalar
      map_one' := ?_
      map_mul' := ?_ }
  · apply Subtype.ext
    have hscalar :
        (1 :
          (fixed_constituent_literal_determinant_cover_proj_hom
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)).ker).1.1.2.toLinearEquiv =
          ((scalar 1 : _) : Aˣ) • LinearEquiv.refl A P_S := by
      simpa [scalar] using
        literal_determinant_cover_kernel_scalar_spec
          (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
          (1 :
            (fixed_constituent_literal_determinant_cover_proj_hom
              (A := A) (G := G) (I := I) (ρA_I := ρA_I)).ker)
    have hone :
        (1 :
          (fixed_constituent_literal_determinant_cover_proj_hom
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)).ker).1.1.2.toLinearEquiv =
          (1 : Aˣ) • LinearEquiv.refl A P_S := by
      change
        (fixed_constituent_transport_fiber_one
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)).toLinearEquiv =
          (1 : Aˣ) • LinearEquiv.refl A P_S
      ext x
      simp [fixed_constituent_transport_fiber_one]
    exact
      literal_determinant_cover_kernel_scalar_unique
        (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
        (1 :
          (fixed_constituent_literal_determinant_cover_proj_hom
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)).ker)
        hscalar hone
  · intro z₁ z₂
    apply Subtype.ext
    have h₁ :
        z₁.1.1.2.toLinearEquiv =
          ((scalar z₁ : _) : Aˣ) • LinearEquiv.refl A P_S := by
      simpa [scalar] using
        literal_determinant_cover_kernel_scalar_spec
          (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar z₁
    have h₂ :
        z₂.1.1.2.toLinearEquiv =
          ((scalar z₂ : _) : Aˣ) • LinearEquiv.refl A P_S := by
      simpa [scalar] using
        literal_determinant_cover_kernel_scalar_spec
          (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar z₂
    have h₁₂ :
        (z₁ * z₂).1.1.2.toLinearEquiv =
          ((scalar (z₁ * z₂) : _) : Aˣ) • LinearEquiv.refl A P_S := by
      simpa [scalar] using
        literal_determinant_cover_kernel_scalar_spec
          (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar (z₁ * z₂)
    have hprod :
        (z₁ * z₂).1.1.2.toLinearEquiv =
          (((scalar z₁ : _) : Aˣ) * ((scalar z₂ : _) : Aˣ)) •
            LinearEquiv.refl A P_S := by
      calc
        (z₁ * z₂).1.1.2.toLinearEquiv =
            z₂.1.1.2.toLinearEquiv.trans z₁.1.1.2.toLinearEquiv := by
              exact
                literal_determinant_cover_kernel_toLinearEquiv_mul
                  (A := A) (G := G) (I := I) ρA_I z₁ z₂
        _ =
            (((scalar z₂ : _) : Aˣ) • LinearEquiv.refl A P_S).trans
              (((scalar z₁ : _) : Aˣ) • LinearEquiv.refl A P_S) := by
              rw [h₂, h₁]
        _ =
            (((scalar z₂ : _) : Aˣ) * ((scalar z₁ : _) : Aˣ)) •
              LinearEquiv.refl A P_S := by
              exact
                unit_smul_linearEquiv_refl_trans
                  (A := A) ((scalar z₂ : _) : Aˣ) ((scalar z₁ : _) : Aˣ)
        _ =
            (((scalar z₁ : _) : Aˣ) * ((scalar z₂ : _) : Aˣ)) •
              LinearEquiv.refl A P_S := by
              rw [mul_comm]
    exact
      literal_determinant_cover_kernel_scalar_unique
        (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
        (z₁ * z₂) h₁₂ hprod

/-- Helper for Theorem 17-17.6-1: the scalar homomorphism on the actual literal-cover projection
kernel is injective. -/
theorem literal_determinant_cover_kernel_scalar_hom_injective
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
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    Function.Injective
      (literal_determinant_cover_kernel_scalar_hom
        (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar) := by
  intro z₁ z₂ hscalar
  apply Subtype.ext
  apply Subtype.ext
  have hz₁_proj :
      (fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)) z₁.1 = 1 := z₁.2
  have hz₂_proj :
      (fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)) z₂.1 = 1 := z₂.2
  have hproj : z₁.1.1.1 = z₂.1.1.1 := by
    simpa [fixed_constituent_literal_determinant_cover_proj_hom,
      fixed_constituent_transport_total_space_proj_hom,
      fixed_constituent_transport_total_space_proj] using hz₁_proj.trans hz₂_proj.symm
  apply Sigma.ext hproj
  have hunit :
      ((literal_determinant_cover_kernel_scalar_hom
        (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar z₁ : _) : Aˣ) =
      ((literal_determinant_cover_kernel_scalar_hom
        (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar z₂ : _) : Aˣ) := by
    exact congrArg Subtype.val hscalar
  have hlin₁ :
      z₁.1.1.2.toLinearEquiv =
        ((literal_determinant_cover_kernel_scalar_hom
          (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar z₁ : _) : Aˣ) •
          LinearEquiv.refl A P_S := by
    simpa [literal_determinant_cover_kernel_scalar_hom] using
      literal_determinant_cover_kernel_scalar_spec
        (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar z₁
  have hlin₂ :
      z₂.1.1.2.toLinearEquiv =
        ((literal_determinant_cover_kernel_scalar_hom
          (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar z₂ : _) : Aˣ) •
          LinearEquiv.refl A P_S := by
    simpa [literal_determinant_cover_kernel_scalar_hom] using
      literal_determinant_cover_kernel_scalar_spec
        (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar z₂
  refine
    literal_determinant_cover_transport_fiber_heq_of_toLinearEquiv_eq
      (A := A) (G := G) (I := I) ρA_I hproj ?_
  calc
    z₁.1.1.2.toLinearEquiv =
        ((literal_determinant_cover_kernel_scalar_hom
          (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar z₁ : _) : Aˣ) •
          LinearEquiv.refl A P_S := hlin₁
    _ =
        ((literal_determinant_cover_kernel_scalar_hom
          (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar z₂ : _) : Aˣ) •
          LinearEquiv.refl A P_S := by rw [hunit]
    _ = z₂.1.1.2.toLinearEquiv := hlin₂.symm

/-- Helper for Theorem 17-17.6-1: an element of the actual projection kernel in Serre's
literal determinant cover gives an element of the quotient kernel after applying
`G₂(det) → G₂(det) / I₂(det)`. -/
theorem literal_determinant_cover_kernel_mk_mem_quotient_kernel
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    let G2 :=
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I
    let I2 :=
      fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
        (A := A) (G := G) (I := I) ρA_I
    let pi2 : G2 ⧸ I2 →* G ⧸ I :=
      fixed_constituent_literal_determinant_cover_proj_to_quotient
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
    let pi : G2 →* G :=
      fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
    ∀ z : pi.ker, QuotientGroup.mk' I2 z.1 ∈ pi2.ker := by
  dsimp
  let G2 :=
    fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I
  let I2 :=
    fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
      (A := A) (G := G) (I := I) ρA_I
  let pi2 : G2 ⧸ I2 →* G ⧸ I :=
    fixed_constituent_literal_determinant_cover_proj_to_quotient
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  let pi : G2 →* G :=
    fixed_constituent_literal_determinant_cover_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  intro z
  change pi2 (QuotientGroup.mk' I2 z.1) = 1
  have hmk_one : QuotientGroup.mk' I (pi z.1) = 1 := by
    rw [z.2]
    exact (QuotientGroup.eq_one_iff (1 : G)).2 I.one_mem
  simpa [pi2, fixed_constituent_literal_determinant_cover_proj_to_quotient, pi, I2] using
    hmk_one

/-- Helper for Theorem 17-17.6-1: quotienting by the embedded Hall kernel restricts to a
homomorphism from the actual literal-cover projection kernel to Serre's literal quotient kernel.
-/
noncomputable def literal_determinant_cover_kernel_to_quotient_kernel_hom
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    let G2 :=
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I
    let I2 :=
      fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
        (A := A) (G := G) (I := I) ρA_I
    let pi2 : G2 ⧸ I2 →* G ⧸ I :=
      fixed_constituent_literal_determinant_cover_proj_to_quotient
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
    let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
    let pi : G2 →* G :=
      fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
    pi.ker →* Nbar :=
  let G2 :=
    fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I
  let I2 :=
    fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
      (A := A) (G := G) (I := I) ρA_I
  let pi2 : G2 ⧸ I2 →* G ⧸ I :=
    fixed_constituent_literal_determinant_cover_proj_to_quotient
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  let pi : G2 →* G :=
    fixed_constituent_literal_determinant_cover_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  MonoidHom.codRestrict
    ((QuotientGroup.mk' I2).comp (Subgroup.subtype pi.ker))
    pi2.ker
    (literal_determinant_cover_kernel_mk_mem_quotient_kernel
      (A := A) (G := G) (I := I) ρA_I)

/-- Helper for Theorem 17-17.6-1: the restricted quotient map from the literal projection kernel
to Serre's literal quotient kernel is bijective. -/
theorem literal_determinant_cover_kernel_to_quotient_kernel_bijective
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    Function.Bijective
      (literal_determinant_cover_kernel_to_quotient_kernel_hom
        (A := A) (G := G) (I := I) ρA_I) := by
  let G2 :=
    fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I
  let I2 :=
    fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
      (A := A) (G := G) (I := I) ρA_I
  let pi2 : G2 ⧸ I2 →* G ⧸ I :=
    fixed_constituent_literal_determinant_cover_proj_to_quotient
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  let pi : G2 →* G :=
    fixed_constituent_literal_determinant_cover_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  let toNbar :=
    literal_determinant_cover_kernel_to_quotient_kernel_hom
      (A := A) (G := G) (I := I) ρA_I
  constructor
  · intro z₁ z₂ h
    apply Subtype.ext
    have hmk :
        QuotientGroup.mk' I2 z₁.1 = QuotientGroup.mk' I2 z₂.1 := by
      exact congrArg Subtype.val h
    have hdiff_mem : z₁.1⁻¹ * z₂.1 ∈ I2 := by
      exact (QuotientGroup.eq).1 (by simpa [QuotientGroup.mk'_apply] using hmk)
    rcases hdiff_mem with ⟨x, hx⟩
    have hproj_diff : pi (z₁.1⁻¹ * z₂.1) = 1 := by
      have hz₁ : pi z₁.1 = 1 := z₁.2
      have hz₂ : pi z₂.1 = 1 := z₂.2
      simp [hz₁, hz₂]
    have hproj_embed :
        pi
            (fixed_constituent_literal_determinant_cover_embed_hall_kernel
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) x) =
          x := by
      rfl
    have hx_val : (x : G) = 1 := by
      rw [hx] at hproj_embed
      rw [hproj_diff] at hproj_embed
      exact hproj_embed.symm
    have hx_one : x = 1 := Subtype.ext hx_val
    have hdiff_one : z₁.1⁻¹ * z₂.1 = 1 := by
      rw [← hx, hx_one]
      simp
    exact (inv_mul_eq_one).1 hdiff_one
  · intro q
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective I2 q.1
    have hmk_ker : pi2 (QuotientGroup.mk' I2 g) = 1 := by
      rw [hg]
      exact q.2
    have hproj_mk_one : QuotientGroup.mk' I (pi g) = 1 := by
      simpa [pi2, fixed_constituent_literal_determinant_cover_proj_to_quotient, pi, I2] using
        hmk_ker
    have hproj_mem : pi g ∈ I := by
      exact (QuotientGroup.eq_one_iff (pi g)).1 hproj_mk_one
    let x : I := ⟨pi g, hproj_mem⟩
    have hnorm : pi (g *
        (fixed_constituent_literal_determinant_cover_embed_hall_kernel
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) x)⁻¹) = 1 := by
      have hproj_embed :
          pi
              (fixed_constituent_literal_determinant_cover_embed_hall_kernel
                (A := A) (G := G) (I := I) (ρA_I := ρA_I) x) =
            x := by
        rfl
      simp [x, hproj_embed]
    let z : pi.ker :=
      ⟨g *
          (fixed_constituent_literal_determinant_cover_embed_hall_kernel
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) x)⁻¹,
        hnorm⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change QuotientGroup.mk' I2 z.1 = q.1
    have hx_mem :
        fixed_constituent_literal_determinant_cover_embed_hall_kernel
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) x ∈ I2 := by
      exact ⟨x, rfl⟩
    have hx_mk_one :
        QuotientGroup.mk' I2
            (fixed_constituent_literal_determinant_cover_embed_hall_kernel
              (A := A) (G := G) (I := I) (ρA_I := ρA_I) x) =
          1 := by
      exact (QuotientGroup.eq_one_iff _).2 hx_mem
    calc
      QuotientGroup.mk' I2 z.1 =
          QuotientGroup.mk' I2 g *
            (QuotientGroup.mk' I2
              (fixed_constituent_literal_determinant_cover_embed_hall_kernel
                (A := A) (G := G) (I := I) (ρA_I := ρA_I) x))⁻¹ := by
            simp [z]
      _ = q.1 := by
            simpa [hx_mk_one] using hg

/-- Helper for Theorem 17-17.6-1: the actual literal projection kernel is identified with
Serre's literal quotient kernel by quotienting by the embedded Hall kernel and normalizing
representatives back over `1 ∈ G`. -/
noncomputable def literal_determinant_cover_kernel_equiv_quotient_kernel
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    let G2 :=
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I
    let I2 :=
      fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
        (A := A) (G := G) (I := I) ρA_I
    let pi2 : G2 ⧸ I2 →* G ⧸ I :=
      fixed_constituent_literal_determinant_cover_proj_to_quotient
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
    let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
    let pi : G2 →* G :=
      fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
    pi.ker ≃* Nbar :=
  MulEquiv.ofBijective
    (literal_determinant_cover_kernel_to_quotient_kernel_hom
      (A := A) (G := G) (I := I) ρA_I)
    (literal_determinant_cover_kernel_to_quotient_kernel_bijective
      (A := A) (G := G) (I := I) ρA_I)

end

end Representation
