import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.BoundedGeneratorKernelControl

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

/-- Helper for Theorem 17-17.6-1: the canonical chosen-section operator
`v ↦ ρ(s)(f((transportedSubrepresentation_rep_equiv_local_c17 ρ S̄ s).symm v))`
already lands in the transported multiplicity space. This isolates the genuine source-faithful
closure step before the arbitrary fiber correction is inserted. -/
theorem fixed_isotypic_cover_section_action_postcompose_precompose_isIntertwining
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G)
    (f : fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :
    Representation.IsIntertwiningMap
      (transportedSubrepresentation ρ Sbar s).toRepresentation
      (ρ.comp I.subtype)
      ((ρ s).comp
        ((f : Sbar.toSubmodule →ₗ[k] V).comp
          (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).symm.toLinearMap)) := by
  refine Representation.IsIntertwiningMap.mk ?_
  intro a x
  let e := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s
  have he :
      e.symm.toLinearMap ((transportedSubrepresentation ρ Sbar s).toRepresentation a x) =
        Sbar.toRepresentation ((MulAut.conjNormal s⁻¹).toMonoidHom a)
          (e.symm.toLinearMap x) := by
    have he0 := congrArg
      (fun L : (transportedSubrepresentation ρ Sbar s).toSubmodule →ₗ[k] Sbar.toSubmodule =>
        L x)
      (e.symm.toIntertwiningMap.isIntertwining' a)
    simpa [LinearMap.comp_apply] using he0
  have hf :
      f (Sbar.toRepresentation ((MulAut.conjNormal s⁻¹).toMonoidHom a)
          (e.symm.toLinearMap x)) =
        ρ (((MulAut.conjNormal s⁻¹).toMonoidHom a : I) : G)
          (f (e.symm.toLinearMap x)) := by
    exact Representation.IntertwiningMap.isIntertwining
      Sbar.toRepresentation (ρ.comp I.subtype) f
      ((MulAut.conjNormal s⁻¹).toMonoidHom a) (e.symm.toLinearMap x)
  let y := f (e.symm.toLinearMap x)
  calc
    ρ s (f (e.symm.toLinearMap
        ((transportedSubrepresentation ρ Sbar s).toRepresentation a x)))
        = ρ s (f (Sbar.toRepresentation ((MulAut.conjNormal s⁻¹).toMonoidHom a)
            (e.symm.toLinearMap x))) := by
            rw [he]
    _ = ρ s (ρ (((MulAut.conjNormal s⁻¹).toMonoidHom a : I) : G) y) := by
          rw [hf]
    _ = ρ (s * (((MulAut.conjNormal s⁻¹).toMonoidHom a : I) : G)) y := by
          exact
            (LinearMap.congr_fun
              (ρ.map_mul s (((MulAut.conjNormal s⁻¹).toMonoidHom a : I) : G)) y).symm
    _ = ρ ((a : G) * s) y := by
          congr 1
          simp [mul_assoc]
    _ = ρ (a : G) (ρ s y) := by
          exact LinearMap.congr_fun (ρ.map_mul (a : G) s) y

/-- Helper for Theorem 17-17.6-1: the inverse chosen-section operator
`v ↦ ρ(s⁻¹)(f((transportedSubrepresentation_rep_equiv_local_c17 ρ S̄ s) v))`
already lands back in the fixed multiplicity space. This is the inverse source-side map for the
explicit section action before the final chosen transport is applied. -/
theorem fixed_isotypic_cover_section_inverse_postcompose_precompose_isIntertwining
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G)
    (f :
      fixed_isotypic_multiplicity_space
        (I := I) (ρ := ρ) (transportedSubrepresentation ρ Sbar s)) :
    Representation.IsIntertwiningMap
      Sbar.toRepresentation
      (ρ.comp I.subtype)
      ((ρ s⁻¹).comp
        ((f : (transportedSubrepresentation ρ Sbar s).toSubmodule →ₗ[k] V).comp
          (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap)) := by
  refine Representation.IsIntertwiningMap.mk ?_
  intro a x
  let e := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s
  let b : I := (MulAut.conjNormal s).toMonoidHom a
  have he :
      e.toLinearMap (Sbar.toRepresentation a x) =
        (transportedSubrepresentation ρ Sbar s).toRepresentation b
          (e.toLinearMap x) := by
    -- The transport equivalence intertwines the conjugated `I`-action; choosing
    -- `b = s a s⁻¹` turns that conjugated source action back into `a`.
    have he0 := congrArg
      (fun L : Sbar.toSubmodule →ₗ[k] (transportedSubrepresentation ρ Sbar s).toSubmodule =>
        L x)
      (e.toIntertwiningMap.isIntertwining' b)
    simpa [LinearMap.comp_apply, b] using he0
  have hf :
      f ((transportedSubrepresentation ρ Sbar s).toRepresentation b
          (e.toLinearMap x)) =
        ρ (b : G) (f (e.toLinearMap x)) := by
    exact Representation.IntertwiningMap.isIntertwining
      (transportedSubrepresentation ρ Sbar s).toRepresentation (ρ.comp I.subtype) f
      b (e.toLinearMap x)
  let y := f (e.toLinearMap x)
  calc
    ρ s⁻¹ (f (e.toLinearMap (Sbar.toRepresentation a x)))
        = ρ s⁻¹
            (f ((transportedSubrepresentation ρ Sbar s).toRepresentation b
              (e.toLinearMap x))) := by
            rw [he]
    _ = ρ s⁻¹ (ρ (b : G) y) := by
          rw [hf]
    _ = ρ (s⁻¹ * (b : G)) y := by
          exact (LinearMap.congr_fun (ρ.map_mul s⁻¹ (b : G)) y).symm
    _ = ρ ((a : G) * s⁻¹) y := by
          congr 1
          simp [b, mul_assoc]
    _ = ρ (a : G) (ρ s⁻¹ y) := by
          exact LinearMap.congr_fun (ρ.map_mul (a : G) s⁻¹) y

/-- Helper for Theorem 17-17.6-1: the forward chosen-section operator as an element of the
transported multiplicity space. -/
noncomputable def fixed_isotypic_cover_section_action_to_transport_map
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G)
    (f : fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :
    fixed_isotypic_multiplicity_space
      (I := I) (ρ := ρ) (transportedSubrepresentation ρ Sbar s) :=
  ((ρ s).comp
    ((f : Sbar.toSubmodule →ₗ[k] V).comp
      (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).symm.toLinearMap))
    |>.intertwiningMap_of_isIntertwiningMap
      (transportedSubrepresentation ρ Sbar s).toRepresentation
      (ρ.comp I.subtype)
      (fixed_isotypic_cover_section_action_postcompose_precompose_isIntertwining
        (I := I) (ρ := ρ) (Sbar := Sbar) s f).isIntertwining

/-- Helper for Theorem 17-17.6-1: the inverse chosen-section operator as an element of the fixed
multiplicity space. -/
noncomputable def fixed_isotypic_cover_section_action_from_transport_map
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G)
    (f :
      fixed_isotypic_multiplicity_space
        (I := I) (ρ := ρ) (transportedSubrepresentation ρ Sbar s)) :
    fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar :=
  ((ρ s⁻¹).comp
    ((f : (transportedSubrepresentation ρ Sbar s).toSubmodule →ₗ[k] V).comp
      (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap))
    |>.intertwiningMap_of_isIntertwiningMap
      Sbar.toRepresentation
      (ρ.comp I.subtype)
      (fixed_isotypic_cover_section_inverse_postcompose_precompose_isIntertwining
        (I := I) (ρ := ρ) (Sbar := Sbar) s f).isIntertwining

/-- Helper for Theorem 17-17.6-1: the forward chosen-section map evaluates by transporting the
source vector back to `S̄`, applying the multiplicity map, and then applying `ρ s`. -/
@[simp] theorem fixed_isotypic_cover_section_action_to_transport_map_apply
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G)
    (f : fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)
    (x : (transportedSubrepresentation ρ Sbar s).toSubmodule) :
    fixed_isotypic_cover_section_action_to_transport_map
        (I := I) (ρ := ρ) Sbar s f x =
      ρ s (f ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).symm.toLinearMap x)) :=
  rfl

/-- Helper for Theorem 17-17.6-1: the underlying linear map of the forward chosen-section map has
the same explicit evaluation formula. -/
@[simp] theorem fixed_isotypic_cover_section_action_to_transport_map_toLinearMap_apply
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G)
    (f : fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)
    (x : (transportedSubrepresentation ρ Sbar s).toSubmodule) :
    (fixed_isotypic_cover_section_action_to_transport_map
        (I := I) (ρ := ρ) Sbar s f).toLinearMap x =
      ρ s (f ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).symm.toLinearMap x)) :=
  rfl

/-- Helper for Theorem 17-17.6-1: the inverse chosen-section map evaluates by transporting the
source vector to the transported constituent, applying the multiplicity map, and then applying
`ρ s⁻¹`. -/
@[simp] theorem fixed_isotypic_cover_section_action_from_transport_map_apply
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G)
    (f :
      fixed_isotypic_multiplicity_space
        (I := I) (ρ := ρ) (transportedSubrepresentation ρ Sbar s))
    (x : Sbar.toSubmodule) :
    fixed_isotypic_cover_section_action_from_transport_map
        (I := I) (ρ := ρ) Sbar s f x =
      ρ s⁻¹ (f ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap x)) :=
  rfl

/-- Helper for Theorem 17-17.6-1: the underlying linear map of the inverse chosen-section map has
the same explicit evaluation formula. -/
@[simp] theorem fixed_isotypic_cover_section_action_from_transport_map_toLinearMap_apply
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G)
    (f :
      fixed_isotypic_multiplicity_space
        (I := I) (ρ := ρ) (transportedSubrepresentation ρ Sbar s))
    (x : Sbar.toSubmodule) :
    (fixed_isotypic_cover_section_action_from_transport_map
        (I := I) (ρ := ρ) Sbar s f).toLinearMap x =
      ρ s⁻¹ (f ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap x)) :=
  rfl

/-- Helper for Theorem 17-17.6-1: the forward chosen-section operator is additive. -/
theorem fixed_isotypic_cover_section_action_to_transport_map_add
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G)
    (f g : fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :
    fixed_isotypic_cover_section_action_to_transport_map
        (I := I) (ρ := ρ) Sbar s (f + g) =
      fixed_isotypic_cover_section_action_to_transport_map
          (I := I) (ρ := ρ) Sbar s f +
        fixed_isotypic_cover_section_action_to_transport_map
          (I := I) (ρ := ρ) Sbar s g := by
  -- Extensionality reduces additivity to pointwise additivity of the underlying linear maps.
  apply Representation.IntertwiningMap.ext
  ext x
  let y := (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).symm.toLinearMap x
  calc
    (fixed_isotypic_cover_section_action_to_transport_map
        (I := I) (ρ := ρ) Sbar s (f + g)).toLinearMap x =
        ρ s ((f + g) y) := by
          rw [fixed_isotypic_cover_section_action_to_transport_map_toLinearMap_apply]
    _ = ρ s (f y + g y) := by
          rfl
    _ = ρ s (f y) + ρ s (g y) := by
          exact (ρ s).map_add (f y) (g y)
    _ =
        ((fixed_isotypic_cover_section_action_to_transport_map
            (I := I) (ρ := ρ) Sbar s f +
          fixed_isotypic_cover_section_action_to_transport_map
            (I := I) (ρ := ρ) Sbar s g).toLinearMap) x := by
          rw [Representation.IntertwiningMap.add_toLinearMap]
          rw [LinearMap.add_apply]
          rw [fixed_isotypic_cover_section_action_to_transport_map_toLinearMap_apply,
            fixed_isotypic_cover_section_action_to_transport_map_toLinearMap_apply]

/-- Helper for Theorem 17-17.6-1: the forward chosen-section operator is `k`-linear. -/
theorem fixed_isotypic_cover_section_action_to_transport_map_smul
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G)
    (a : k)
    (f : fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :
    fixed_isotypic_cover_section_action_to_transport_map
        (I := I) (ρ := ρ) Sbar s (a • f) =
      a • fixed_isotypic_cover_section_action_to_transport_map
        (I := I) (ρ := ρ) Sbar s f := by
  -- Extensionality reduces scalar compatibility to pointwise linearity of `ρ s`.
  apply Representation.IntertwiningMap.ext
  ext x
  let y := (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).symm.toLinearMap x
  calc
    (fixed_isotypic_cover_section_action_to_transport_map
        (I := I) (ρ := ρ) Sbar s (a • f)).toLinearMap x =
        ρ s ((a • f) y) := by
          rw [fixed_isotypic_cover_section_action_to_transport_map_toLinearMap_apply]
    _ = ρ s (a • f y) := by
          rfl
    _ = a • ρ s (f y) := by
          exact (ρ s).map_smul a (f y)
    _ =
        ((a • fixed_isotypic_cover_section_action_to_transport_map
          (I := I) (ρ := ρ) Sbar s f).toLinearMap) x := by
          rw [Representation.IntertwiningMap.toLinearMap_smul]
          rw [LinearMap.smul_apply]
          rw [fixed_isotypic_cover_section_action_to_transport_map_toLinearMap_apply]

/-- Helper for Theorem 17-17.6-1: the inverse chosen-section operator is additive. -/
theorem fixed_isotypic_cover_section_action_from_transport_map_add
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G)
    (f g :
      fixed_isotypic_multiplicity_space
        (I := I) (ρ := ρ) (transportedSubrepresentation ρ Sbar s)) :
    fixed_isotypic_cover_section_action_from_transport_map
        (I := I) (ρ := ρ) Sbar s (f + g) =
      fixed_isotypic_cover_section_action_from_transport_map
          (I := I) (ρ := ρ) Sbar s f +
        fixed_isotypic_cover_section_action_from_transport_map
          (I := I) (ρ := ρ) Sbar s g := by
  -- The inverse operator has the same pointwise additivity after applying `ρ s⁻¹`.
  apply Representation.IntertwiningMap.ext
  ext x
  let y := (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap x
  calc
    (fixed_isotypic_cover_section_action_from_transport_map
        (I := I) (ρ := ρ) Sbar s (f + g)).toLinearMap x =
        ρ s⁻¹ ((f + g) y) := by
          rw [fixed_isotypic_cover_section_action_from_transport_map_toLinearMap_apply]
    _ = ρ s⁻¹ (f y + g y) := by
          rfl
    _ = ρ s⁻¹ (f y) + ρ s⁻¹ (g y) := by
          exact (ρ s⁻¹).map_add (f y) (g y)
    _ =
        ((fixed_isotypic_cover_section_action_from_transport_map
            (I := I) (ρ := ρ) Sbar s f +
          fixed_isotypic_cover_section_action_from_transport_map
            (I := I) (ρ := ρ) Sbar s g).toLinearMap) x := by
          rw [Representation.IntertwiningMap.add_toLinearMap]
          rw [LinearMap.add_apply]
          rw [fixed_isotypic_cover_section_action_from_transport_map_toLinearMap_apply,
            fixed_isotypic_cover_section_action_from_transport_map_toLinearMap_apply]

/-- Helper for Theorem 17-17.6-1: the inverse chosen-section operator is `k`-linear. -/
theorem fixed_isotypic_cover_section_action_from_transport_map_smul
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G)
    (a : k)
    (f :
      fixed_isotypic_multiplicity_space
        (I := I) (ρ := ρ) (transportedSubrepresentation ρ Sbar s)) :
    fixed_isotypic_cover_section_action_from_transport_map
        (I := I) (ρ := ρ) Sbar s (a • f) =
      a • fixed_isotypic_cover_section_action_from_transport_map
        (I := I) (ρ := ρ) Sbar s f := by
  -- The inverse operator is scalar-compatible because each representation operator is linear.
  apply Representation.IntertwiningMap.ext
  ext x
  let y := (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s).toLinearMap x
  calc
    (fixed_isotypic_cover_section_action_from_transport_map
        (I := I) (ρ := ρ) Sbar s (a • f)).toLinearMap x =
        ρ s⁻¹ ((a • f) y) := by
          rw [fixed_isotypic_cover_section_action_from_transport_map_toLinearMap_apply]
    _ = ρ s⁻¹ (a • f y) := by
          rfl
    _ = a • ρ s⁻¹ (f y) := by
          exact (ρ s⁻¹).map_smul a (f y)
    _ =
        ((a • fixed_isotypic_cover_section_action_from_transport_map
          (I := I) (ρ := ρ) Sbar s f).toLinearMap) x := by
          rw [Representation.IntertwiningMap.toLinearMap_smul]
          rw [LinearMap.smul_apply]
          rw [fixed_isotypic_cover_section_action_from_transport_map_toLinearMap_apply]

/-- Helper for Theorem 17-17.6-1: the forward chosen-section operator as a linear map from the
fixed multiplicity space to the transported one. -/
noncomputable def fixed_isotypic_cover_section_action_to_transport_linearMap
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G) :
    fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar →ₗ[k]
      fixed_isotypic_multiplicity_space
        (I := I) (ρ := ρ) (transportedSubrepresentation ρ Sbar s) where
  toFun := fixed_isotypic_cover_section_action_to_transport_map (I := I) (ρ := ρ) Sbar s
  map_add' := fixed_isotypic_cover_section_action_to_transport_map_add
    (I := I) (ρ := ρ) Sbar s
  map_smul' := fixed_isotypic_cover_section_action_to_transport_map_smul
    (I := I) (ρ := ρ) Sbar s

/-- Helper for Theorem 17-17.6-1: the inverse chosen-section operator as a linear map from the
transported multiplicity space back to the fixed one. -/
noncomputable def fixed_isotypic_cover_section_action_from_transport_linearMap
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G) :
    fixed_isotypic_multiplicity_space
        (I := I) (ρ := ρ) (transportedSubrepresentation ρ Sbar s) →ₗ[k]
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar where
  toFun := fixed_isotypic_cover_section_action_from_transport_map (I := I) (ρ := ρ) Sbar s
  map_add' := fixed_isotypic_cover_section_action_from_transport_map_add
    (I := I) (ρ := ρ) Sbar s
  map_smul' := fixed_isotypic_cover_section_action_from_transport_map_smul
    (I := I) (ρ := ρ) Sbar s

/-- Helper for Theorem 17-17.6-1: the forward chosen-section operator cancels its inverse on the
transported multiplicity space. -/
theorem fixed_isotypic_cover_section_action_to_from_transport_linearMap
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G) :
    (fixed_isotypic_cover_section_action_to_transport_linearMap
        (I := I) (ρ := ρ) Sbar s).comp
      (fixed_isotypic_cover_section_action_from_transport_linearMap
        (I := I) (ρ := ρ) Sbar s) =
      LinearMap.id := by
  -- The two source transports cancel, and `ρ s` cancels `ρ s⁻¹` by the representation law.
  apply LinearMap.ext
  intro f
  apply Representation.IntertwiningMap.ext
  ext x
  let e := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s
  have hcancel : e.toLinearMap (e.symm.toLinearMap x) = x := by
    simpa using e.apply_symm_apply x
  rw [LinearMap.comp_apply]
  dsimp [fixed_isotypic_cover_section_action_to_transport_linearMap,
    fixed_isotypic_cover_section_action_from_transport_linearMap]
  calc
    (fixed_isotypic_cover_section_action_to_transport_map
          (I := I) (ρ := ρ) Sbar s
          (fixed_isotypic_cover_section_action_from_transport_map
            (I := I) (ρ := ρ) Sbar s f)).toLinearMap x =
        fixed_isotypic_cover_section_action_to_transport_map
          (I := I) (ρ := ρ) Sbar s
          (fixed_isotypic_cover_section_action_from_transport_map
            (I := I) (ρ := ρ) Sbar s f) x := by
        rfl
    _ = ρ s
        ((fixed_isotypic_cover_section_action_from_transport_map
          (I := I) (ρ := ρ) Sbar s f) (e.symm.toLinearMap x)) := by
        rw [fixed_isotypic_cover_section_action_to_transport_map_apply]
    _ = ρ s (ρ s⁻¹ (f (e.toLinearMap (e.symm.toLinearMap x)))) := by
        rw [fixed_isotypic_cover_section_action_from_transport_map_apply]
    _ = ρ s (ρ s⁻¹ (f x)) := by
        rw [hcancel]
    _ = ρ (s * s⁻¹) (f x) := by
      exact (LinearMap.congr_fun (ρ.map_mul s s⁻¹) (f x)).symm
    _ = f x := by
      simp

/-- Helper for Theorem 17-17.6-1: the inverse chosen-section operator cancels the forward one on
the fixed multiplicity space. -/
theorem fixed_isotypic_cover_section_action_from_to_transport_linearMap
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G) :
    (fixed_isotypic_cover_section_action_from_transport_linearMap
        (I := I) (ρ := ρ) Sbar s).comp
      (fixed_isotypic_cover_section_action_to_transport_linearMap
        (I := I) (ρ := ρ) Sbar s) =
      LinearMap.id := by
  -- The opposite cancellation uses the same two identities in reverse order.
  apply LinearMap.ext
  intro f
  apply Representation.IntertwiningMap.ext
  ext x
  let e := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s
  have hcancel : e.symm.toLinearMap (e.toLinearMap x) = x := by
    simpa using e.symm_apply_apply x
  rw [LinearMap.comp_apply]
  dsimp [fixed_isotypic_cover_section_action_to_transport_linearMap,
    fixed_isotypic_cover_section_action_from_transport_linearMap]
  calc
    (fixed_isotypic_cover_section_action_from_transport_map
          (I := I) (ρ := ρ) Sbar s
          (fixed_isotypic_cover_section_action_to_transport_map
            (I := I) (ρ := ρ) Sbar s f)).toLinearMap x =
        fixed_isotypic_cover_section_action_from_transport_map
          (I := I) (ρ := ρ) Sbar s
          (fixed_isotypic_cover_section_action_to_transport_map
            (I := I) (ρ := ρ) Sbar s f) x := by
        rfl
    _ = ρ s⁻¹
        ((fixed_isotypic_cover_section_action_to_transport_map
          (I := I) (ρ := ρ) Sbar s f) (e.toLinearMap x)) := by
        rw [fixed_isotypic_cover_section_action_from_transport_map_apply]
    _ = ρ s⁻¹ (ρ s (f (e.symm.toLinearMap (e.toLinearMap x)))) := by
        rw [fixed_isotypic_cover_section_action_to_transport_map_apply]
    _ = ρ s⁻¹ (ρ s (f x)) := by
        rw [hcancel]
    _ = ρ (s⁻¹ * s) (f x) := by
      exact (LinearMap.congr_fun (ρ.map_mul s⁻¹ s) (f x)).symm
    _ = f x := by
      simp

/-- Helper for Theorem 17-17.6-1: the chosen-section operator is a linear equivalence from the
fixed multiplicity space to the transported multiplicity space. -/
noncomputable def fixed_isotypic_cover_section_action_to_transport_linearEquiv
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (s : G) :
    fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar ≃ₗ[k]
      fixed_isotypic_multiplicity_space
        (I := I) (ρ := ρ) (transportedSubrepresentation ρ Sbar s) :=
  LinearEquiv.ofLinear
    (fixed_isotypic_cover_section_action_to_transport_linearMap
      (I := I) (ρ := ρ) Sbar s)
    (fixed_isotypic_cover_section_action_from_transport_linearMap
      (I := I) (ρ := ρ) Sbar s)
    (fixed_isotypic_cover_section_action_to_from_transport_linearMap
      (I := I) (ρ := ρ) Sbar s)
    (fixed_isotypic_cover_section_action_from_to_transport_linearMap
      (I := I) (ρ := ρ) Sbar s)

/-- Helper for Theorem 17-17.6-1: Serre's first missing object in the fixed-constituent branch is
the explicit upstairs operator of a cover element `g ∈ G₂` on the multiplicity space
`F = Hom^I(S̄, V)`. Naming it separately keeps the transport/coercion frontier out of the quotient
construction `τ`. -/
noncomputable def fixed_isotypic_cover_section_action_linearEquiv
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
    fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar ≃ₗ[k]
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar :=
  (fixed_isotypic_cover_section_action_to_transport_linearEquiv
      (I := I) (ρ := ρ) Sbar s).trans
    (transported_fixed_isotypic_multiplicity_space_linearEquiv
      (I := I) (ρ := ρ) Sbar s (hTransport s).some)

/-- Helper for Theorem 17-17.6-1: Serre's first missing object in the fixed-constituent branch is
the explicit upstairs operator of a cover element `g ∈ G₂` on the multiplicity space
`F = Hom^I(S̄, V)`. Naming it separately keeps the transport/coercion frontier out of the quotient
construction `τ`. -/
noncomputable def fixed_isotypic_cover_action_linearEquiv
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
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    G2 →
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar ≃ₗ[k]
        fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar :=
  fun g ↦
    -- Route correction: follow Serre's source-faithful factorization. First apply the chosen
    -- section action over `g.1.1`, then insert the source correction comparing the arbitrary
    -- fiber component `g.1.2` with the chosen section.
    (fixed_isotypic_cover_section_action_linearEquiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      g.1.1).trans
      ((fixed_isotypic_cover_source_correction_multiplicity_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        g.1.1 g.1.2))

/-- Helper for Theorem 17-17.6-1: the reduction equivalence attached to the literal identity
fiber is the canonical transport comparison over `1`. -/
theorem fixed_constituent_transport_fiber_reduction_equiv_identity
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
    fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 : G)
        (fixed_constituent_transport_fiber_one
          (A := A) (G := G) (I := I) ρA_I) =
      transportedSubrepresentation_rep_equiv_local_one (I := I) (ρ := ρ) Sbar := by
  apply
    fixed_constituent_transport_fiber_reduction_equiv_unique
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (fixed_constituent_transport_fiber_one
        (A := A) (G := G) (I := I) ρA_I)
  · exact
      fixed_constituent_transport_fiber_reduction_equiv_spec
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 : G)
        (fixed_constituent_transport_fiber_one
          (A := A) (G := G) (I := I) ρA_I)
  · let e := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (1 : G)
    ext z
    have hlin :
        (transportedSubrepresentation_rep_equiv_local_one
            (I := I) (ρ := ρ) Sbar).toLinearMap (red_S z) =
          e.toLinearMap (red_S z) := by
      apply Subtype.ext
      calc
        (transportedSubrepresentation ρ Sbar (1 : G)).toSubmodule.subtype
            ((transportedSubrepresentation_rep_equiv_local_one
              (I := I) (ρ := ρ) Sbar).toLinearMap (red_S z)) =
          ρ (1 : G) (Sbar.toSubmodule.subtype (red_S z)) := by
            exact
              transportedSubrepresentation_rep_equiv_local_one_subtype_apply
                (I := I) (ρ := ρ) Sbar (red_S z)
        _ =
          (transportedSubrepresentation ρ Sbar (1 : G)).toSubmodule.subtype
            (e.toLinearMap (red_S z)) := by
            exact
              (LinearMap.congr_fun
                (transportedSubrepresentation_rep_equiv_local_subtype
                  (I := I) (ρ := ρ) (Sbar := Sbar) (1 : G))
                (red_S z)).symm
    simpa [fixed_constituent_transport_fiber_one, Representation.Equiv.mk, e] using hlin

/-- Helper for Theorem 17-17.6-1: at the identity base point, Serre's chosen-section operator on
the multiplicity space is exactly the inverse of the source-correction operator attached to the
literal identity fiber. This isolates the `g = 1` normalization of the future `G₂`-action before
the full cocycle coherence is checked. -/
theorem fixed_isotypic_cover_section_action_linearEquiv_one
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
    fixed_isotypic_cover_section_action_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 : G) =
      (fixed_isotypic_cover_source_correction_multiplicity_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (1 : G)
      (fixed_constituent_transport_fiber_one
        (A := A) (G := G) (I := I) ρA_I)).symm := by
  rw [fixed_isotypic_cover_source_correction_multiplicity_linearEquiv,
    fixed_isotypic_cover_source_correction_equiv,
    fixed_constituent_transport_fiber_reduction_equiv_identity
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift]
  ext f x
  let e := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (1 : G)
  let e₀ := transportedSubrepresentation_rep_equiv_local_one (I := I) (ρ := ρ) Sbar
  have hforward_same : ∀ z : Sbar.toSubmodule, e₀.toLinearMap z = e.toLinearMap z := by
    intro z
    apply Subtype.ext
    calc
      (transportedSubrepresentation ρ Sbar (1 : G)).toSubmodule.subtype
          (e₀.toLinearMap z) =
        ρ (1 : G) (Sbar.toSubmodule.subtype z) := by
          exact
            transportedSubrepresentation_rep_equiv_local_one_subtype_apply
              (I := I) (ρ := ρ) Sbar z
      _ =
        (transportedSubrepresentation ρ Sbar (1 : G)).toSubmodule.subtype
          (e.toLinearMap z) := by
          exact
            (LinearMap.congr_fun
              (transportedSubrepresentation_rep_equiv_local_subtype
                (I := I) (ρ := ρ) (Sbar := Sbar) (1 : G))
              z).symm
  have hinv_same :
      ∀ y : (transportedSubrepresentation ρ Sbar (1 : G)).toSubmodule,
        e.symm.toLinearMap y = e₀.symm.toLinearMap y := by
    intro y
    apply e.toLinearEquiv.injective
    calc
      e.toLinearMap (e.symm.toLinearMap y) = y := by
        simpa using e.apply_symm_apply y
      _ = e₀.toLinearMap (e₀.symm.toLinearMap y) := by
        exact (e₀.apply_symm_apply y).symm
      _ = e.toLinearMap (e₀.symm.toLinearMap y) := by
        rw [hforward_same]
  change
    fixed_isotypic_cover_section_action_to_transport_map
        (I := I) (ρ := ρ) Sbar (1 : G) f
        ((hTransport (1 : G)).some.toLinearMap x) =
      f (((e₀.trans ((hTransport (1 : G)).some.symm)).symm) x)
  rw [fixed_isotypic_cover_section_action_to_transport_map_apply]
  rw [hinv_same]
  have harg :
      (((e₀.trans ((hTransport (1 : G)).some.symm)).symm) x) =
        e₀.symm.toLinearMap ((hTransport (1 : G)).some.toLinearMap x) := by
    change
      ((e₀.toLinearEquiv.trans ((hTransport (1 : G)).some.symm.toLinearEquiv)).symm) x =
        e₀.toLinearEquiv.symm (((hTransport (1 : G)).some.toLinearEquiv) x)
    rw [LinearEquiv.symm_trans_apply]
    have hsame :
        (((hTransport (1 : G)).some.symm.toLinearEquiv).symm) x =
          ((hTransport (1 : G)).some.toLinearEquiv) x := by
      apply ((hTransport (1 : G)).some.symm.toLinearEquiv).injective
      calc
        ((hTransport (1 : G)).some.symm.toLinearEquiv)
            (((hTransport (1 : G)).some.symm.toLinearEquiv).symm x) = x := by
          exact LinearEquiv.apply_symm_apply
            ((hTransport (1 : G)).some.symm.toLinearEquiv) x
        _ =
          ((hTransport (1 : G)).some.symm.toLinearEquiv)
            (((hTransport (1 : G)).some.toLinearEquiv) x) := by
          simpa using ((hTransport (1 : G)).some.symm_apply_apply x).symm
    exact congrArg e₀.toLinearEquiv.symm hsame
  rw [harg]
  simp

/-- Helper for Theorem 17-17.6-1: once the explicit upstairs operator is named, the only group-law
data needed to build Serre's cover representation is the normalization at `1`. This keeps the
representation packaging independent of the later quotient descent. -/
theorem fixed_isotypic_cover_action_toLinearMap_one
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
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    (fixed_isotypic_cover_action_linearEquiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (1 : G2)).toLinearMap =
      LinearMap.id := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  change
    (fixed_isotypic_cover_action_linearEquiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (1 : G2)).toLinearMap =
      LinearMap.id
  rw [fixed_isotypic_cover_action_linearEquiv]
  have hG2one :
      ((1 : G2) :
        fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) =
        ⟨1,
          fixed_constituent_transport_fiber_one
            (A := A) (G := G) (I := I) ρA_I⟩ := by
    rw [← fixed_constituent_transport_total_space_one
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)]
    rfl
  rw [hG2one]
  rw [fixed_isotypic_cover_section_action_linearEquiv_one
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift]
  let C :=
    fixed_isotypic_cover_source_correction_multiplicity_linearEquiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (1 : G)
      (fixed_constituent_transport_fiber_one
        (A := A) (G := G) (I := I) ρA_I)
  ext f x
  change ((C.symm.trans C) f).toLinearMap x = (LinearMap.id f).toLinearMap x
  exact congrArg (fun y => y.toLinearMap x) (C.apply_symm_apply f)

/-- Helper for Theorem 17-17.6-1: the explicit cover operator evaluates by first reducing the
chosen lift-side fiber element and then applying the ambient `G`-action on the target. -/
theorem fixed_isotypic_cover_action_linearEquiv_apply
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
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ (g : G2)
      (f : fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)
      (x : Sbar.toSubmodule),
      ((fixed_isotypic_cover_action_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        g) f).toLinearMap x =
        ρ g.1.1
          (f ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar g.1.1).symm.toLinearMap
            ((fixed_constituent_transport_fiber_reduction_equiv
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
              hTransportLift g.1.1 g.1.2).toLinearMap x))) := by
  dsimp only
  intro g f x
  let h := (hTransport g.1.1).some
  let r :=
    fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
      hTransportLift g.1.1 g.1.2
  rw [fixed_isotypic_cover_action_linearEquiv,
    fixed_isotypic_cover_section_action_linearEquiv,
    fixed_isotypic_cover_source_correction_multiplicity_linearEquiv,
    fixed_isotypic_cover_source_correction_equiv]
  simp [transported_fixed_isotypic_multiplicity_space_linearEquiv,
    fixed_isotypic_multiplicity_space_precompose_linearEquiv,
    fixed_isotypic_cover_section_action_to_transport_linearEquiv,
    fixed_isotypic_cover_section_action_to_transport_linearMap]
  change
    fixed_isotypic_cover_section_action_to_transport_map
        (I := I) (ρ := ρ) Sbar g.1.1 f
        (h.toLinearMap (h.symm.toLinearMap (r.toLinearMap x))) =
      ρ g.1.1
        (f ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar g.1.1).symm.toLinearMap
          (r.toLinearMap x)))
  have hcancel :
      h.toLinearMap (h.symm.toLinearMap (r.toLinearMap x)) = r.toLinearMap x := by
    simpa using h.apply_symm_apply (r.toLinearMap x)
  rw [hcancel]
  rw [fixed_isotypic_cover_section_action_to_transport_map_apply]

/-- Helper for Theorem 17-17.6-1: the source correction attached to a lift-side transport
fiber element sends the reduction of a lifted vector to the reduction of the inverse transported
lifted vector. -/
theorem fixed_constituent_transport_fiber_source_correction_apply_red
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
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s)
    (z : P_S) :
    let e := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s
    let r :=
      fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        s u
    e.symm.toLinearMap (r.toLinearMap (red_S z)) =
      red_S (u.symm.toLinearMap z) := by
  dsimp only
  let e := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s
  let r :=
    fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s u
  apply e.toLinearEquiv.injective
  have hspec :=
    fixed_constituent_transport_fiber_reduction_equiv_spec
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift s u
  have hspec_z := LinearMap.congr_fun hspec (u.symm.toLinearMap z)
  have hcancel : u.toLinearMap (u.symm.toLinearMap z) = z := by
    exact u.toLinearEquiv.apply_symm_apply z
  calc
    e.toLinearMap (e.symm.toLinearMap (r.toLinearMap (red_S z))) =
        r.toLinearMap (red_S z) := by
          simpa using e.apply_symm_apply (r.toLinearMap (red_S z))
    _ = r.toLinearMap (red_S (u.toLinearMap (u.symm.toLinearMap z))) := by
          rw [hcancel]
    _ = e.toLinearMap (red_S (u.symm.toLinearMap z)) := by
          simpa [LinearMap.comp_apply, e, r] using hspec_z

/-- Helper for Theorem 17-17.6-1: source corrections compose contravariantly with the
lift-side transport-fiber product. -/
theorem fixed_constituent_transport_fiber_source_correction_comp_apply
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
    {s t : G}
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s)
    (v :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I t)
    (x : Sbar.toSubmodule) :
    let euv := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (s * t)
    let ruv :=
      fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (s * t)
        (fixed_constituent_transport_fiber_comp
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v)
    let eu := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar s
    let ru :=
      fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        s u
    let ev := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar t
    let rv :=
      fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        t v
    euv.symm.toLinearMap (ruv.toLinearMap x) =
      ev.symm.toLinearMap (rv.toLinearMap (eu.symm.toLinearMap (ru.toLinearMap x))) := by
  dsimp only
  letI : Module (MonoidAlgebra A I) P_S := representationCarrierGroupAlgebraModule ρA_I
  letI : IsScalarTower A (MonoidAlgebra A I) P_S :=
    representationCarrierGroupAlgebraIsScalarTower ρA_I
  letI : Module (MonoidAlgebra k I) Sbar.toSubmodule :=
    representationCarrierGroupAlgebraModule Sbar.toRepresentation
  letI : IsScalarTower k (MonoidAlgebra k I) Sbar.toSubmodule :=
    representationCarrierGroupAlgebraIsScalarTower Sbar.toRepresentation
  have hred : red_S.IsResidueFieldReduction I := by
    simpa using hLiftSbar
  obtain ⟨z, hz⟩ :=
    fixed_constituent_reduction_surjective (A := A) (H := I) hred x
  rw [← hz]
  rw [fixed_constituent_transport_fiber_source_correction_apply_red
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    (s * t)
    (fixed_constituent_transport_fiber_comp
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) u v) z]
  rw [fixed_constituent_transport_fiber_source_correction_apply_red
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    s u z]
  rw [fixed_constituent_transport_fiber_source_correction_apply_red
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    t v (u.symm.toLinearMap z)]
  rfl

omit [HenselianLocalRing A] [Finite G] in
/-- Helper for Theorem 17-17.6-1: the inverse of the transport fiber attached to a Hall-kernel
element is the lifted inverse Hall-kernel action on the fixed constituent lift. -/
theorem fixed_constituent_transport_fiber_hall_kernel_symm_apply
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (x : I)
    (z : P_S) :
    (fixed_constituent_transport_fiber_of_hall_kernel_element
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) x).symm.toLinearMap z =
      ρA_I x⁻¹ z := by
  let u :=
    fixed_constituent_transport_fiber_of_hall_kernel_element
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
  apply u.toLinearEquiv.injective
  calc
    u.toLinearMap (u.symm.toLinearMap z) = z := by
      simpa using u.apply_symm_apply z
    _ = ρA_I x (ρA_I x⁻¹ z) := by
      simp
    _ = u.toLinearMap (ρA_I x⁻¹ z) := by
      simp [u, fixed_constituent_transport_fiber_of_hall_kernel_element]

omit [Finite G] [FiniteDimensional k V] in
/-- Helper for Theorem 17-17.6-1: the residue map of the fixed lift intertwines the lifted
Hall-kernel action with the fixed constituent action. -/
theorem fixed_constituent_lift_reduction_rep_apply
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (x : I)
    (z : P_S) :
    red_S (ρA_I x z) = Sbar.toRepresentation x (red_S z) := by
  letI : Module (MonoidAlgebra A I) P_S := representationCarrierGroupAlgebraModule ρA_I
  letI : IsScalarTower A (MonoidAlgebra A I) P_S :=
    representationCarrierGroupAlgebraIsScalarTower ρA_I
  letI : Module (MonoidAlgebra k I) Sbar.toSubmodule :=
    representationCarrierGroupAlgebraModule Sbar.toRepresentation
  letI : IsScalarTower k (MonoidAlgebra k I) Sbar.toSubmodule :=
    representationCarrierGroupAlgebraIsScalarTower Sbar.toRepresentation
  have hred : red_S.IsResidueFieldReduction I := by
    simpa using hLiftSbar
  have hmap := LinearMap.IsResidueFieldReduction.map_monoidAlgebra_of hred x z
  have hsource : (MonoidAlgebra.of A I x) • z = ρA_I x z := by
    change (ρA_I.asAlgebraHom (MonoidAlgebra.of A I x)) z = ρA_I x z
    rw [Representation.asAlgebraHom_of]
  have htarget :
      (MonoidAlgebra.of k I x) • red_S z =
        Sbar.toRepresentation x (red_S z) := by
    change (Sbar.toRepresentation.asAlgebraHom (MonoidAlgebra.of k I x)) (red_S z) =
      Sbar.toRepresentation x (red_S z)
    rw [Representation.asAlgebraHom_of]
  rwa [hsource, htarget] at hmap

/-- Helper for Theorem 17-17.6-1: the source correction attached to an embedded Hall-kernel
element is exactly the inverse Hall-kernel action on the fixed constituent. -/
theorem fixed_constituent_transport_fiber_source_correction_hall_kernel_apply
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
    (x : I)
    (y : Sbar.toSubmodule) :
    let e := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (x : G)
    let r :=
      fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (x : G)
        (fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) x)
    e.symm.toLinearMap (r.toLinearMap y) =
      Sbar.toRepresentation x⁻¹ y := by
  dsimp only
  letI : Module (MonoidAlgebra A I) P_S := representationCarrierGroupAlgebraModule ρA_I
  letI : IsScalarTower A (MonoidAlgebra A I) P_S :=
    representationCarrierGroupAlgebraIsScalarTower ρA_I
  letI : Module (MonoidAlgebra k I) Sbar.toSubmodule :=
    representationCarrierGroupAlgebraModule Sbar.toRepresentation
  letI : IsScalarTower k (MonoidAlgebra k I) Sbar.toSubmodule :=
    representationCarrierGroupAlgebraIsScalarTower Sbar.toRepresentation
  have hred : red_S.IsResidueFieldReduction I := by
    simpa using hLiftSbar
  obtain ⟨z, hz⟩ :=
    fixed_constituent_reduction_surjective (A := A) (H := I) hred y
  rw [← hz]
  rw [fixed_constituent_transport_fiber_source_correction_apply_red
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    (x : G)
    (fixed_constituent_transport_fiber_of_hall_kernel_element
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) x) z]
  rw [fixed_constituent_transport_fiber_hall_kernel_symm_apply
    (A := A) (G := G) (I := I) ρA_I x z]
  rw [fixed_constituent_lift_reduction_rep_apply
    (A := A) (G := G) (V := V) I ρ Sbar ρA_I red_S hLiftSbar x⁻¹ z]

/-- Helper for Theorem 17-17.6-1: after the identity case is split off, the remaining coherence
for the upstairs action is the literal multiplication rule on `G₂`. This isolates the cocycle
frontier from the quotient package. -/
theorem fixed_isotypic_cover_action_toLinearMap_mul
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
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ g h : G2,
      (fixed_isotypic_cover_action_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (g * h)).toLinearMap =
        (fixed_isotypic_cover_action_linearEquiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          g).toLinearMap *
          (fixed_isotypic_cover_action_linearEquiv
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
            h).toLinearMap := by
  dsimp only
  intro g h
  apply LinearMap.ext
  intro f
  apply Representation.IntertwiningMap.ext
  ext x
  rw [Module.End.mul_apply]
  let cgx :=
    (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar g.1.1).symm.toLinearMap
      ((fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
        hTransportLift g.1.1 g.1.2).toLinearMap x)
  let chcgx :=
    (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar h.1.1).symm.toLinearMap
      ((fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
        hTransportLift h.1.1 h.1.2).toLinearMap cgx)
  let cghx :=
    (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (g.1.1 * h.1.1)).symm.toLinearMap
      ((fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
        hTransportLift (g.1.1 * h.1.1)
        (fixed_constituent_transport_fiber_comp
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.1.2 h.1.2)).toLinearMap x)
  have hsource : cghx = chcgx := by
    simpa [cghx, chcgx, cgx] using
      fixed_constituent_transport_fiber_source_correction_comp_apply
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
        hTransportLift g.1.2 h.1.2 x
  have hgh :
      ((fixed_isotypic_cover_action_linearEquiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          (g * h)) f).toLinearMap x =
        ρ (g.1.1 * h.1.1) (f cghx) := by
    simpa [cghx, fixed_constituent_transport_total_space_mul_eq,
      fixed_constituent_transport_total_space_mul] using
      fixed_isotypic_cover_action_linearEquiv_apply
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (g * h) f x
  have hg :
      ((fixed_isotypic_cover_action_linearEquiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          g)
          ((fixed_isotypic_cover_action_linearEquiv
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
            h) f)).toLinearMap x =
        ρ g.1.1
          (((fixed_isotypic_cover_action_linearEquiv
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
            h) f).toLinearMap cgx) := by
    simpa [cgx] using
      fixed_isotypic_cover_action_linearEquiv_apply
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        g
        ((fixed_isotypic_cover_action_linearEquiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          h) f) x
  have hh :
      ((fixed_isotypic_cover_action_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        h) f).toLinearMap cgx =
        ρ h.1.1 (f chcgx) := by
    simpa [chcgx, cgx] using
      fixed_isotypic_cover_action_linearEquiv_apply
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        h f cgx
  calc
    ((fixed_isotypic_cover_action_linearEquiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          (g * h)) f).toLinearMap x =
        ρ (g.1.1 * h.1.1) (f cghx) := hgh
    _ = ρ (g.1.1 * h.1.1) (f chcgx) := by
          rw [hsource]
    _ = ρ g.1.1 (ρ h.1.1 (f chcgx)) := by
          exact LinearMap.congr_fun (ρ.map_mul g.1.1 h.1.1) (f chcgx)
    _ =
        ρ g.1.1
          (((fixed_isotypic_cover_action_linearEquiv
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
            h) f).toLinearMap cgx) := by
          rw [hh]
    _ =
        ((fixed_isotypic_cover_action_linearEquiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          g)
          ((fixed_isotypic_cover_action_linearEquiv
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
            h) f)).toLinearMap x := hg.symm

/-- Helper for Theorem 17-17.6-1: once the operator and its group law are separated out, Serre's
upstairs cover action on `F = Hom^I(S̄, V)` is an ordinary representation of `G₂`. This freezes
the pre-quotient object before proving that `I₂` acts trivially. -/
noncomputable def fixed_isotypic_cover_representation
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
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    Representation k G2 (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :=
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  { toFun := fun g ↦
      (fixed_isotypic_cover_action_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        g).toLinearMap
    map_one' :=
      fixed_isotypic_cover_action_toLinearMap_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    map_mul' :=
      fixed_isotypic_cover_action_toLinearMap_mul
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift }

/-- Helper for Theorem 17-17.6-1: Serre's Hall-kernel subgroup `I₂ ≤ G₂` should act trivially on
the upstairs multiplicity-space representation before the quotient `τ` is defined. Isolating this
fact leaves `Representation.ofQuotient` as a purely formal step. -/
theorem fixed_isotypic_cover_action_isTrivial_on_hall_kernel
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
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let I2 :=
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let coverRep :=
      fixed_isotypic_cover_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    Representation.IsTrivial (coverRep.comp I2.subtype) := by
  dsimp only
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let coverRep :=
    fixed_isotypic_cover_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  refine Representation.IsTrivial.mk ?_
  intro y
  rcases y with ⟨g, hg⟩
  rcases hg with ⟨x, rfl⟩
  let gx :=
    fixed_constituent_generated_cover_embed_hall_kernel
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift x
  apply LinearMap.ext
  intro f
  apply Representation.IntertwiningMap.ext
  ext z
  let source :=
    (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (x : G)).symm.toLinearMap
      ((fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (x : G)
        (fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) x)).toLinearMap z)
  have hsource : source = Sbar.toRepresentation x⁻¹ z := by
    exact
      fixed_constituent_transport_fiber_source_correction_hall_kernel_apply
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift x z
  have happly_raw :
      ((fixed_isotypic_cover_action_linearEquiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          gx) f).toLinearMap z =
        ρ (x : G) (f source) := by
    simpa [gx, fixed_constituent_generated_cover_embed_hall_kernel,
      fixed_constituent_transport_total_space_embed_hall_kernel, source] using
      fixed_isotypic_cover_action_linearEquiv_apply
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        gx f z
  have happly :
      ((fixed_isotypic_cover_action_linearEquiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          gx) f).toLinearMap z =
        ρ (x : G) (f (Sbar.toRepresentation x⁻¹ z)) := by
    calc
      ((fixed_isotypic_cover_action_linearEquiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          gx) f).toLinearMap z =
          ρ (x : G) (f source) := happly_raw
      _ = ρ (x : G) (f (Sbar.toRepresentation x⁻¹ z)) := by
            rw [hsource]
  have hf :
      f (Sbar.toRepresentation x⁻¹ z) =
        ρ (((x⁻¹ : I) : G)) (f z) := by
    exact
      Representation.IntertwiningMap.isIntertwining
        Sbar.toRepresentation (ρ.comp I.subtype) f x⁻¹ z
  change ((fixed_isotypic_cover_action_linearEquiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      gx) f).toLinearMap z = f.toLinearMap z
  calc
    ((fixed_isotypic_cover_action_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        gx) f).toLinearMap z =
        ρ (x : G) (f (Sbar.toRepresentation x⁻¹ z)) := happly
    _ = ρ (x : G) (ρ (((x⁻¹ : I) : G)) (f z)) := by
          rw [hf]
    _ = ρ ((x : G) * (((x⁻¹ : I) : G))) (f z) := by
          exact (LinearMap.congr_fun (ρ.map_mul (x : G) (((x⁻¹ : I) : G))) (f z)).symm
    _ = f z := by
          simp

/-- Helper for Theorem 17-17.6-1: Serre's multiplicity space `F = Hom^I(S̄, V)` carries a natural
`G₂ / I₂`-action once the transport action of `G₂` on `S̄` and `V` is descended through the
embedded Hall kernel. This isolates the quotient-module construction `τ`. -/
noncomputable def fixed_isotypic_multiplicity_space_quotient_representation
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
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
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let I2 :=
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    Representation k (G2 ⧸ I2) (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :=
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let coverRep :=
    fixed_isotypic_cover_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  letI : Representation.IsTrivial (coverRep.comp I2.subtype) :=
    fixed_isotypic_cover_action_isTrivial_on_hall_kernel
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  coverRep.ofQuotient I2

/-- Helper for Theorem 17-17.6-1: once the explicit upstairs multiplicity-space action of `G₂`
is known to be irreducible, irreducibility descends formally to Serre's quotient module
`τ = F / I₂` because the Hall kernel `I₂` already acts trivially. This isolates the purely
quotient-theoretic step from the remaining tensor-evaluation argument upstairs. -/
theorem fixed_isotypic_multiplicity_space_quotient_irreducible_of_cover_irreducible
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
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
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let I2 :=
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let coverRep :=
      fixed_isotypic_cover_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    Representation.IsIrreducible coverRep →
      let tau :=
        fixed_isotypic_multiplicity_space_quotient_representation
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
          hTransportLift
      Representation.IsIrreducible tau := by
  dsimp
  intro hcover
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let coverRep :=
    fixed_isotypic_cover_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  letI : Representation.IsTrivial (coverRep.comp I2.subtype) :=
    fixed_isotypic_cover_action_isTrivial_on_hall_kernel
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  letI : coverRep.IsIrreducible := hcover
  simpa [fixed_isotypic_multiplicity_space_quotient_representation, G2, I2, coverRep] using
    isIrreducible_of_ofQuotient_of_isTrivial_c17 coverRep I2

/-- Helper for Theorem 17-17.6-1: pulling back the original irreducible representation `ρ` along
Serre's surjective finite-cover projection `π : G₂ → G` preserves irreducibility. This isolates
the formal cover-side target of the future tensor-evaluation equivalence `S̄ ⊗ F ≃ ρ.comp π`. -/
theorem fixed_constituent_generated_cover_comp_irreducible
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    [ρ.IsIrreducible]
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
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi : G2 →* G :=
      (fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)
    Representation.IsIrreducible (ρ.comp pi) := by
  dsimp
  exact
    isIrreducible_comp_of_surjective
      ((fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype
          (fixed_constituent_generated_cover_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))
      (fixed_constituent_generated_cover_proj_surjective
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
      ρ

/-- Helper for Theorem 17-17.6-1: the fixed constituent's isotypic subrepresentation is the
whole restricted Hall-kernel representation when the owner isotypic component is top. -/
theorem fixed_isotypic_isotypicSubrepresentation_toSubmodule_eq_top
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤) :
    let ρI : Representation k I V := ρ.comp I.subtype
    (ρI.isotypicSubrepresentation Sbar.toRepresentation).toSubmodule = ⊤ := by
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
  let σ : Representation k I Sbar.toSubmodule := Sbar.toRepresentation
  letI : Module (MonoidAlgebra k I) Sbar.toSubmodule := σ.instModuleMonoidAlgebraAsModule
  letI : Module (MonoidAlgebra k I) σ.asModule := σ.instModuleMonoidAlgebraAsModule
  have hcarrier :
      @isotypicComponent (MonoidAlgebra k I) V Sbar.toSubmodule
        inferInstance inferInstance inferInstance inferInstance
        σ.instModuleMonoidAlgebraAsModule =
        @isotypicComponent (MonoidAlgebra k I) V σ.asModule
          inferInstance inferInstance inferInstance inferInstance
          σ.instModuleMonoidAlgebraAsModule := by
    let e : Sbar.toSubmodule ≃ₗ[MonoidAlgebra k I] σ.asModule := LinearEquiv.refl _ _
    exact @LinearEquiv.isotypicComponent_eq
      (MonoidAlgebra k I) V Sbar.toSubmodule σ.asModule
      inferInstance inferInstance inferInstance inferInstance inferInstance
      σ.instModuleMonoidAlgebraAsModule σ.instModuleMonoidAlgebraAsModule e
  have howner :
      @isotypicComponent (MonoidAlgebra k I) V σ.asModule
        inferInstance inferInstance inferInstance inferInstance
        σ.instModuleMonoidAlgebraAsModule =
        @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
          inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module := by
    exact
      @LinearEquiv.isotypicComponent_eq
        (MonoidAlgebra k I) V σ.asModule Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance inferInstance
        σ.instModuleMonoidAlgebraAsModule Sbar.asSubmodule.module
        (subrepresentation_owner_intrinsic_linearEquiv_local_c17 (ρ := ρI) Sbar)
  ext x
  constructor
  · intro _
    trivial
  · intro _
    have hxOwner :
        x ∈ @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
          inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module := by
      simpa [hSbar_top]
    have hxCarrier :
        x ∈ @isotypicComponent (MonoidAlgebra k I) V Sbar.toSubmodule
          inferInstance inferInstance inferInstance inferInstance
          σ.instModuleMonoidAlgebraAsModule := by
      simpa [hcarrier, howner] using hxOwner
    simpa [Representation.isotypicSubrepresentation, ρI, σ] using hxCarrier

/-- Helper for Theorem 17-17.6-1: the Hall-kernel order is invertible in the residue field when
it is prime to the residue characteristic. -/
theorem fixed_isotypic_hall_card_ne_zero
    (hp : Nat.Prime p)
    (I : Subgroup G)
    (hIcop : Nat.Coprime p (Nat.card I)) :
    (Nat.card I : k) ≠ 0 := by
  have hI_not_dvd : ¬ p ∣ Nat.card I := hp.coprime_iff_not_dvd.mp hIcop
  letI : NeZero (Nat.card I : k) := NeZero.of_not_dvd k hI_not_dvd
  exact NeZero.ne (Nat.card I : k)

/-- Helper for Theorem 17-17.6-1: Chapter 2's tensor-evaluation map is bijective for the fixed
irreducible constituent. -/
theorem fixed_isotypic_tensor_evaluation_bijective
    [IsAlgClosed k]
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible) :
    let ρI : Representation k I V := ρ.comp I.subtype
    Function.Bijective (ρI.isotypicTensorEvaluation Sbar.toRepresentation).toLinearMap := by
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Sbar.toRepresentation.IsIrreducible := hSbar_irred
  letI : Invertible (Nat.card I : k) :=
    invertibleOfNonzero (fixed_isotypic_hall_card_ne_zero (A := A) hp I hIcop)
  exact
    isotypicTensorEvaluation_bijective
      (ρ := ρI) (σ := Sbar.toRepresentation)

/-- Helper for Theorem 17-17.6-1: forgetting the explicit `G₂`-action, Chapter 2 already gives
the linear equivalence `Hom^I(S̄, V) ⊗ S̄ ≃ V` once the `S̄`-isotypic component is all of `V`.
This isolates the purely linear part of Serre's tensor step from the later equivariance
packaging. -/
noncomputable def fixed_isotypic_tensor_evaluation_linearEquiv
    [IsAlgClosed k]
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤) :
    (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar ⊗[k] Sbar.toSubmodule) ≃ₗ[k] V :=
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Invertible (Nat.card I : k) :=
    invertibleOfNonzero (fixed_isotypic_hall_card_ne_zero (A := A) hp I hIcop)
  (LinearEquiv.ofBijective
      (ρI.isotypicTensorEvaluation Sbar.toRepresentation).toLinearMap
      (fixed_isotypic_tensor_evaluation_bijective
        (A := A) hp I hIcop ρ Sbar hSbar_irred)).trans
    ((LinearEquiv.ofEq
        (ρI.isotypicSubrepresentation Sbar.toRepresentation).toSubmodule
        (⊤ : Submodule k V)
        (fixed_isotypic_isotypicSubrepresentation_toSubmodule_eq_top
          (I := I) (ρ := ρ) (Sbar := Sbar) hSbar_top)).trans
      Submodule.topEquiv)

end

end Representation
