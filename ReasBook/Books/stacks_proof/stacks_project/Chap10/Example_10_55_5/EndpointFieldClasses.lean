import stacks_proof.stacks_project.Chap10.Example_10_55_5.RestrictionTransport

noncomputable section

open scoped TensorProduct

universe u

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Example 10.55.5: if an `R`-module factors through the endpoint field, finite
generation over `R` already implies finite generation over `k`. -/
theorem equal_endpoint_moduleFinite_over_field
    (V : Type u) [AddCommGroup V] [Module k V] [Module R V]
    [IsScalarTower R k V] [SMulCommClass R k V] [Module.Finite R V] :
    Module.Finite k V := by
  classical
  have hR : Module.Finite R V := inferInstance
  rw [Module.finite_def, Submodule.fg_def] at hR ⊢
  rcases hR with ⟨s, hsFinite, hsTop⟩
  refine ⟨s, hsFinite, ?_⟩
  -- The same generators span over `k`, because the `R`-action already factors through `k`.
  have hspan :
      Submodule.span R s ≤ (Submodule.span k s).restrictScalars R := by
    refine Submodule.span_le.2 ?_
    intro x hx
    exact Submodule.subset_span hx
  rw [Submodule.eq_top_iff']
  intro v
  have hvTop : v ∈ (⊤ : Submodule R V) := by
    simp
  have hv :
      v ∈ (Submodule.span k s).restrictScalars R := by
    have htop :
        (⊤ : Submodule R V) ≤ (Submodule.span k s).restrictScalars R := by
      simpa [hsTop] using hspan
    exact htop hvTop
  exact hv

/-- Helper for Example 10.55.5: the Grothendieck class of a product of finite `R`-modules is the
sum of the two classes. -/
theorem equal_endpoint_finiteGrothendieckGroupOf_prod
    (M N : FGModuleCat R) :
    finiteGrothendieckGroupOf R (FGModuleCat.of R (M.obj × N.obj)) =
      finiteGrothendieckGroupOf R M + finiteGrothendieckGroupOf R N := by
  let S : CategoryTheory.ShortComplex (FGModuleCat R) :=
    { X₁ := M
      X₂ := FGModuleCat.of R (M.obj × N.obj)
      X₃ := N
      f := FGModuleCat.ofHom (LinearMap.inl R M.obj N.obj)
      g := FGModuleCat.ofHom (LinearMap.snd R M.obj N.obj)
      zero := by
        -- The split product row has zero composite on the nose.
        ext x
        rfl }
  have hS : (S.map (ModuleCat.isFG R).ι).ShortExact := by
    -- This is the standard split exact sequence `0 → M → M × N → N → 0`.
    refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
    · intro x
      constructor
      · intro hx
        refine ⟨x.1, ?_⟩
        exact Prod.ext rfl (by simpa using hx.symm)
      · rintro ⟨m, rfl⟩
        rfl
    · intro x y hxy
      exact congrArg Prod.fst hxy
    · intro y
      refine ⟨(0, y), ?_⟩
      rfl
  -- Apply the defining Grothendieck relation to the split row.
  simpa [S, finiteGrothendieckGroupOf] using
    ModulePropertyK0.of_shortExact R S hS

/-- Helper for Example 10.55.5: the endpoint-supported free module `k^(n+1)` splits as
`k × k^n`. -/
noncomputable def equal_endpoint_field_power_succ_linearEquiv (n : ℕ) :
    (Fin (n + 1) → k) ≃ₗ[R] k × (Fin n → k) :=
  (LinearEquiv.piCongrLeft R (fun _ ↦ k) (finSuccEquiv n)) ≪≫ₗ
    LinearEquiv.piOptionEquivProd R

/-- Helper for Example 10.55.5: the split form of `k^(n+1)` yields a canonical isomorphism in
`FGModuleCat R`. -/
noncomputable def equal_endpoint_field_power_succ_fgModuleIso (n : ℕ) :
    FGModuleCat.of R (Fin (n + 1) → k) ≅ FGModuleCat.of R (k × (Fin n → k)) :=
  -- Package the explicit head-tail decomposition as an isomorphism in the finite-module category.
  CategoryTheory.ObjectProperty.isoMk (P := ModuleCat.isFG R)
    ((equal_endpoint_field_power_succ_linearEquiv (k := k) n).toModuleIso)

/-- Helper for Example 10.55.5: the zero endpoint-supported power `k^0` is the zero module. -/
noncomputable def equal_endpoint_field_power_zero_fgModuleIso :
    FGModuleCat.of R (Fin 0 → k) ≅ FGModuleCat.of R PUnit :=
  -- The source induction starts with the trivial vector space `k^0`, which is a zero module.
  CategoryTheory.ObjectProperty.isoMk (P := ModuleCat.isFG R)
    ((LinearEquiv.ofSubsingleton (Fin 0 → k) PUnit).toModuleIso)

/-- Helper for Example 10.55.5: the split product class formula specialized to the fixed
endpoint-supported factors `k` and `k^n`. -/
theorem equal_endpoint_prod_class_eq_sum_stable (n : ℕ) :
    finiteGrothendieckGroupOf R (FGModuleCat.of R ((k × (Fin n → k)) : Type u)) =
      finiteGrothendieckGroupOf R (FGModuleCat.of R (k : Type u)) +
        finiteGrothendieckGroupOf R (FGModuleCat.of R ((Fin n → k) : Type u)) := by
  let S : CategoryTheory.ShortComplex (FGModuleCat R) :=
    { X₁ := FGModuleCat.of R (k : Type u)
      X₂ := FGModuleCat.of R ((k × (Fin n → k)) : Type u)
      X₃ := FGModuleCat.of R ((Fin n → k) : Type u)
      f := FGModuleCat.ofHom (LinearMap.inl R (k : Type u) ((Fin n → k) : Type u))
      g := FGModuleCat.ofHom (LinearMap.snd R (k : Type u) ((Fin n → k) : Type u))
      zero := by
        -- The specialized split row still has zero composite on the nose.
        ext x
        rfl }
  have hS : (S.map (ModuleCat.isFG R).ι).ShortExact := by
    -- The concrete row `0 → k → k × k^n → k^n → 0` is split exact.
    refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
    · intro x
      constructor
      · intro hx
        refine ⟨x.1, ?_⟩
        exact Prod.ext rfl (by simpa using hx.symm)
      · rintro ⟨a, rfl⟩
        rfl
    · intro x y hxy
      exact congrArg Prod.fst hxy
    · intro y
      refine ⟨(0, y), ?_⟩
      rfl
  -- Apply the Grothendieck relation to this specialized split exact sequence.
  simpa [S, finiteGrothendieckGroupOf] using ModulePropertyK0.of_shortExact R S hS

/-- Helper for Example 10.55.5: the endpoint-supported free `k`-vector space `k^n` contributes
`n [k]` in `K'_0(R)`. -/
theorem equal_endpoint_field_power_class_eq_zsmul_field_class
    (n : ℕ) :
    finiteGrothendieckGroupOf R (FGModuleCat.of R (Fin n → k)) =
      n • finiteGrothendieckGroupOf R (FGModuleCat.of R k) := by
  have hZeroClass : finiteGrothendieckGroupOf R (FGModuleCat.of R PUnit) = 0 := by
    -- The zero object contributes the zero class in `K'_0(R)`.
    simpa [finiteGrothendieckGroupOf] using
      (@ModulePropertyK0.of_zero (equal_endpoint_poly_subring k) _
        (ModuleCat.isFG (equal_endpoint_poly_subring k))
        (equal_endpoint_isFG_zero (k := k)))
  induction n with
  | zero =>
      have hIso :
          ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R (Fin 0 → k)) =
            ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R PUnit) := by
        -- The source induction starts by replacing `k^0` with the zero module.
        exact (@ModulePropertyK0.of_iso R _ (ModuleCat.isFG R)
          (equal_endpoint_isFG_zero (k := k))
          _ _
          (equal_endpoint_field_power_zero_fgModuleIso (k := k)) :
            ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R (Fin 0 → k)) =
              ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R PUnit))
      calc
        finiteGrothendieckGroupOf R (FGModuleCat.of R (Fin 0 → k)) =
            finiteGrothendieckGroupOf R (FGModuleCat.of R PUnit) := by
              simpa [finiteGrothendieckGroupOf] using hIso
        _ = 0 := hZeroClass
        _ = 0 • finiteGrothendieckGroupOf R (FGModuleCat.of R k) := by simp
  | succ n ih =>
      have hIso :
          ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R (Fin (n + 1) → k)) =
            ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R (k × (Fin n → k))) := by
        -- The source decomposition identifies `k^(n+1)` with `k × k^n`.
        exact (@ModulePropertyK0.of_iso R _ (ModuleCat.isFG R)
          (equal_endpoint_isFG_zero (k := k))
          _ _
          (equal_endpoint_field_power_succ_fgModuleIso (k := k) n) :
            ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R (Fin (n + 1) → k)) =
              ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R (k × (Fin n → k))))
      calc
        finiteGrothendieckGroupOf R (FGModuleCat.of R (Fin (n + 1) → k)) =
            finiteGrothendieckGroupOf R (FGModuleCat.of R (k × (Fin n → k))) := by
              simpa [finiteGrothendieckGroupOf] using hIso
        _ = finiteGrothendieckGroupOf R (FGModuleCat.of R k) +
              finiteGrothendieckGroupOf R (FGModuleCat.of R (Fin n → k)) := by
              simpa using equal_endpoint_prod_class_eq_sum_stable (k := k) n
        _ = finiteGrothendieckGroupOf R (FGModuleCat.of R k) +
              n • finiteGrothendieckGroupOf R (FGModuleCat.of R k) := by
              rw [ih]
        _ = (n + 1) • finiteGrothendieckGroupOf R (FGModuleCat.of R k) := by
              simpa [succ_nsmul, add_comm, add_left_comm, add_assoc]

/-- Helper for Example 10.55.5: any finite `R`-module whose action factors through
`equal_endpoint_eval k : R → k` has zero class in `K'_0(R)`. -/
theorem equal_endpoint_endpoint_supported_class_eq_zero
    (V : Type u) [AddCommGroup V] [Module k V] [Module R V]
    [IsScalarTower R k V] [SMulCommClass R k V] [Module.Finite R V] :
    finiteGrothendieckGroupOf R (FGModuleCat.of R V) = 0 := by
  let _ : Module.Finite k V :=
    equal_endpoint_moduleFinite_over_field (k := k) (V := V)
  let n := Module.finrank k V
  let e : V ≃ₗ[R] (Fin n → k) :=
    LinearEquiv.restrictScalars R
      ((Module.finBasis k V).repr ≪≫ₗ Finsupp.linearEquivFunOnFinite k k (Fin n))
  let _ : Module.Finite k (Fin n → k) := by infer_instance
  let _ : Module.Finite R (Fin n → k) := by
    exact Module.Finite.trans k (Fin n → k)
  have hIso :
      ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R V) =
        ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R (Fin n → k)) := by
    -- After upgrading to a finite-dimensional `k`-vector space, choose a finite basis and
    -- transport the resulting `k`-linear equivalence to an `R`-linear one via scalar restriction.
    exact (@ModulePropertyK0.of_iso R _ (ModuleCat.isFG R)
      (equal_endpoint_isFG_zero (k := k))
      _ _
      (CategoryTheory.ObjectProperty.isoMk (P := ModuleCat.isFG R) e.toModuleIso) :
          ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R V) =
            ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R (Fin n → k)))
  calc
    finiteGrothendieckGroupOf R (FGModuleCat.of R V) =
        finiteGrothendieckGroupOf R (FGModuleCat.of R (Fin n → k)) := by
          simpa [finiteGrothendieckGroupOf, n, e] using hIso
    _ = n • finiteGrothendieckGroupOf R (FGModuleCat.of R k) := by
          exact equal_endpoint_field_power_class_eq_zsmul_field_class (k := k) n
    _ = 0 := by
          rw [equal_endpoint_field_class_eq_zero]
          simp

/-- Helper for Example 10.55.5: tensoring a finite `R`-module with the endpoint field produces an
finite `R`-module on the literal tensor owner used later. -/
theorem equal_endpoint_tensor_field_module_finite
    (M : FGModuleCat R) :
    Module.Finite R (k ⊗[R] ↑M.obj) := by
  -- The tensor product of two finite modules over the base ring is finite over that base ring.
  infer_instance

end
