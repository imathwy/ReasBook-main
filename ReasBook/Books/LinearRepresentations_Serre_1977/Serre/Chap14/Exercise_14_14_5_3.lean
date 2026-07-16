import LinearRepresentations_Serre_1977.Serre.Chap14.Exercise_14_14_5_3.Index
import LinearRepresentations_Serre_1977.Serre.Chap14.Exercise_14_14_5_3.ProjectiveOwner

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MonoidAlgebra

universe u v w x

noncomputable section

variable {k : Type u} [Field k]
variable {G : Type v} [Group G] [Finite G]
variable {E : Type w} [AddCommGroup E] [Module k E] [Module k[G] E] [IsScalarTower k k[G] E]
variable {F : Type x} [AddCommGroup F] [Module k F] [Module k[G] F] [IsScalarTower k k[G] F]

/-- Exercise 14-14.5-3: if `E` is a projective `k[G]`-module, then the spaces of
`k[G]`-linear maps `E → F` and `F → E` have the same dimension over `k`. -/
theorem finrank_hom_eq_finrank_hom_swap_of_projective
    [Module.Projective k[G] E]
    [FiniteDimensional k E] [FiniteDimensional k F] :
    Module.finrank k (E →ₗ[k[G]] F) = Module.finrank k (F →ₗ[k[G]] E) :=
by
  -- Route correction: follow Serre's source proof literally through the internal-Hom
  -- representation `ρ := Hom(E,F)`, rather than switching to the trace-pairing shortcut.
  letI : Module k (RestrictScalars k k[G] E) :=
    restrictScalars_module (k := k) (G := G) E
  letI : Module k (RestrictScalars k k[G] F) :=
    restrictScalars_module (k := k) (G := G) F
  letI : Module k (RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F) :=
    wrapped_restrictScalars_linHom_module (k := k) (G := G) E F
  letI : Module k (RestrictScalars k k[G] F →ₗ[k] RestrictScalars k k[G] E) :=
    wrapped_restrictScalars_linHom_module (k := k) (G := G) F E
  let ρEF := ofModule_linHom_rep (k := k) (G := G) E F
  -- Package projectivity so that Exercise 14-14.5-2 applies directly to the frozen owner.
  have hproj : Module.Projective k[G] ρEF.asModule := by
    simpa [ρEF, ofModule_linHom_rep_rfl] using
      linHom_projective_of_projective_source (k := k) (G := G) (E := E) (F := F)
  -- This is the core equality supplied by Exercise 14-14.5-2.
  have hcore := by
    letI := @FiniteDimensional.of_injective k
      (RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F)
      inferInstance
      inferInstance
      (wrapped_restrictScalars_linHom_module (k := k) (G := G) E F)
      (E →ₗ[k] F)
      inferInstance
      inferInstance
      (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F)).toLinearMap
      (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F)).injective
    exact @Representation.finrank_invariants_eq_finrank_dual_invariants_of_projective
      k inferInstance G inferInstance
      (RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F)
      inferInstance
      (wrapped_restrictScalars_linHom_module (k := k) (G := G) E F)
      ρEF inferInstance inferInstance hproj
  -- The left invariant space is exactly `Hom_G(E,F)`.
  have hleftIntertwining :=
    (@Representation.invariantsEquivIntertwiningMap k G
      (RestrictScalars k k[G] E) (RestrictScalars k k[G] F)
      inferInstance inferInstance inferInstance
      (restrictScalars_module (k := k) (G := G) E)
      inferInstance
      (restrictScalars_module (k := k) (G := G) F)
      (Representation.ofModule (k := k) (G := G) E)
      (Representation.ofModule (k := k) (G := G) F)).finrank_eq
  -- The source-facing bridge from intertwining maps to `k[G]`-linear maps is already packaged.
  have hleftLinear :=
    ofModule_intertwining_finrank_eq (k := k) (G := G) (E := E) (F := F)
  have hleft := by
    simpa [ρEF, ofModule_linHom_rep_rfl] using hleftIntertwining.trans hleftLinear
  -- The dual internal-Hom owner is identified with the swapped internal-Hom representation.
  have hrightSwap :=
    (@invariantsCongr k inferInstance G inferInstance
      (Module.Dual k (RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F))
      inferInstance inferInstance
      (RestrictScalars k k[G] F →ₗ[k] RestrictScalars k k[G] E)
      inferInstance
      (wrapped_restrictScalars_linHom_module (k := k) (G := G) F E)
      ρEF.dual
      (ofModule_linHom_rep (k := k) (G := G) F E)
      (dual_linHom_ofModule_equiv_linHom_swap
        (k := k) (G := G) (E := E) (F := F))).finrank_eq
  -- Once swapped, the same intertwining/Hom bridge identifies the right-hand side with
  -- `Hom_G(F,E)`.
  have hrightIntertwining :=
    (@Representation.invariantsEquivIntertwiningMap k G
      (RestrictScalars k k[G] F) (RestrictScalars k k[G] E)
      inferInstance inferInstance inferInstance
      (restrictScalars_module (k := k) (G := G) F)
      inferInstance
      (restrictScalars_module (k := k) (G := G) E)
      (Representation.ofModule (k := k) (G := G) F)
      (Representation.ofModule (k := k) (G := G) E)).finrank_eq
  have hrightLinear :=
    ofModule_intertwining_finrank_eq (k := k) (G := G) (E := F) (F := E)
  have hrightStep := by
    simpa [ofModule_linHom_rep_rfl] using hrightIntertwining.trans hrightLinear
  have hright := by
    simpa [ρEF] using hrightSwap.trans hrightStep
  -- Compose the two source-faithful bridge identifications with Exercise 14-14.5-2.
  exact hleft.symm.trans (hcore.trans hright)

end
