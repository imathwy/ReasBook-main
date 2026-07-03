import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_5_3.TraceDuality

open scoped MonoidAlgebra

universe u v w x

noncomputable section

variable {k : Type u} [Field k]
variable {G : Type v} [Group G] [Finite G]
variable {E : Type w} [AddCommGroup E] [Module k E] [Module k[G] E] [IsScalarTower k k[G] E]
variable {F : Type x} [AddCommGroup F] [Module k F] [Module k[G] F] [IsScalarTower k k[G] F]

/-- Helper for Exercise 14-14.5-3: restate the ambient `k`-module structure on the exact
finite-free internal-Hom owner so later projectivity packaging can refer to this carrier
directly, without detouring through an abbreviation. -/
instance finite_free_internal_hom_exact_module (n : ℕ) :
    Module k
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
        (Representation.ofModule (k := k) (G := G) F)).asModule) :=
  ofModule_linHom_asModule_module (k := k) (G := G) (M := Fin n → k[G]) (N := F)

/-- Helper for Exercise 14-14.5-3: the finite-free source case is closed by a single application
of Lemma `14-14.4-1` to the frozen internal-Hom owner. -/
theorem linHom_projective_of_finite_free_source
    [Fintype G]
    [FiniteDimensional k F]
    (n : ℕ) :
    Module.Projective k[G]
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
        (Representation.ofModule (k := k) (G := G) F)).asModule) :=
by
  -- Apply the Maschke criterion on the exact frozen internal-Hom owner.
  let ρ :=
    Representation.linHom
      (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
      (Representation.ofModule (k := k) (G := G) F)
  let hAdd : AddCommGroup ρ.asModule :=
    ofModule_linHom_asModule_addCommGroup (k := k) (G := G) (M := Fin n → k[G]) (N := F)
  let hMod : Module k ρ.asModule :=
    ofModule_linHom_asModule_module (k := k) (G := G) (M := Fin n → k[G]) (N := F)
  let hGMod : Module k[G] ρ.asModule := by
    infer_instance
  let hTower : IsScalarTower k k[G] ρ.asModule :=
    ofModule_linHom_asModule_isScalarTower (k := k) (G := G) (M := Fin n → k[G]) (N := F)
  let hDec : DecidableEq G := Classical.decEq G
  let hiff :=
    @projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
      k inferInstance G inferInstance inferInstance
      ρ.asModule
      hAdd hMod hGMod hTower
  exact hiff.2 <| by
    refine ⟨finite_free_internal_hom_owner_projective_over_k_exact
      (k := k) (G := G) (F := F) n, ?_⟩
    refine ⟨linHom_precompose_picker_end (k := k) (G := G) (F := F) n, ?_⟩
    -- The established textbook average is exactly `sumOfConjugates` on this frozen owner.
    apply DFunLike.ext
    intro h
    exact
      (@textbook_average_eq_sumOfConjugates k inferInstance G inferInstance inferInstance
        ρ.asModule hAdd hMod hGMod hTower hDec
        (linHom_precompose_picker_end (k := k) (G := G) (F := F) n) h).symm.trans <|
        by
          simpa [ρ] using
            linHom_precompose_picker_end_textbook_average
              (k := k) (G := G) (F := F) (n := n) h

/-- Helper for Exercise 14-14.5-3: the split finite-free presentation can be used only through
its retraction identity when descending projectivity of the internal-Hom owner. -/
theorem finite_free_split_maps_of_projective
    [Module.Projective k[G] E] [FiniteDimensional k E] :
    ∃ (n : ℕ) (f : (Fin n → k[G]) →ₗ[k[G]] E) (g : E →ₗ[k[G]] Fin n → k[G]),
      f.comp g = LinearMap.id := by
  -- The retract identity is the only part of the finite-free presentation used downstream.
  obtain ⟨n, f, g, _, _, hfg⟩ :=
    finite_free_split_of_projective (k := k) (G := G) (E := E)
  exact ⟨n, f, g, hfg⟩

/-- Helper for Exercise 14-14.5-3: if the source `k[G]`-module is projective, then the owner
module of the internal-Hom representation is projective. -/
theorem linHom_projective_of_projective_source
    [Module.Projective k[G] E]
    [FiniteDimensional k E] [FiniteDimensional k F] :
    Module.Projective k[G]
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) E)
        (Representation.ofModule (k := k) (G := G) F)).asModule) :=
by
  -- Realize `E` as a retract of a finite free module and descend projectivity along the induced
  -- split on internal-Hom owners.
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨n, f, g, hfg⟩ :=
    finite_free_split_maps_of_projective (k := k) (G := G) (E := E)
  have hff :
      Module.Projective k[G]
        ((Representation.linHom
          (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
          (Representation.ofModule (k := k) (G := G) F)).asModule) :=
    linHom_projective_of_finite_free_source (k := k) (G := G) (F := F) n
  exact
    linHom_projective_of_split_source
      (k := k) (G := G) (E := E) (F := F) (P := Fin n → k[G]) f g hfg hff

end
