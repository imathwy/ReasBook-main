import StacksProject_2024.Chap10.Example_10_55_5.Noetherian

noncomputable section

open scoped TensorProduct CategoryTheory

universe u

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Chap10 Example 10 55 5: the generic rank of a finite projective module over the
equal-endpoint ring, computed after base change to the fraction field. -/
noncomputable def equalEndpointProjectiveRank (M : FiniteProjectiveModuleCat R) : ℤ :=
  let _ : Module.Finite R M.obj := M.property.1
  (Module.finrank (FractionRing R) ((FractionRing R) ⊗[R] M.obj) : ℤ)

/-- Helper for Chap10 Example 10 55 5: the first tensorized map in a finite-projective short
complex after base change to the fraction field. -/
noncomputable abbrev equal_endpoint_projective_fractionRing_tensor_f
    (S : CategoryTheory.ShortComplex (FiniteProjectiveModuleCat R)) :
    ModuleCat.of (FractionRing R)
        ((FractionRing R) ⊗[R] (S.map (finiteProjectiveModuleProperty R).ι).X₁) ⟶
      ModuleCat.of (FractionRing R)
        ((FractionRing R) ⊗[R] (S.map (finiteProjectiveModuleProperty R).ι).X₂) :=
  let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (finiteProjectiveModuleProperty R).ι
  ModuleCat.ofHom (LinearMap.lTensor (FractionRing R) U.f.hom)

/-- Helper for Chap10 Example 10 55 5: the second tensorized map in a finite-projective short
complex after base change to the fraction field. -/
noncomputable abbrev equal_endpoint_projective_fractionRing_tensor_g
    (S : CategoryTheory.ShortComplex (FiniteProjectiveModuleCat R)) :
    ModuleCat.of (FractionRing R)
        ((FractionRing R) ⊗[R] (S.map (finiteProjectiveModuleProperty R).ι).X₂) ⟶
      ModuleCat.of (FractionRing R)
        ((FractionRing R) ⊗[R] (S.map (finiteProjectiveModuleProperty R).ι).X₃) :=
  let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (finiteProjectiveModuleProperty R).ι
  ModuleCat.ofHom (LinearMap.lTensor (FractionRing R) U.g.hom)

/-- Helper for Chap10 Example 10 55 5: after tensoring a finite-projective short complex with the
fraction field, the two induced maps still compose to zero. -/
theorem equal_endpoint_projective_fractionRing_tensor_zero
    (S : CategoryTheory.ShortComplex (FiniteProjectiveModuleCat R)) :
    equal_endpoint_projective_fractionRing_tensor_f (k := k) S ≫
      equal_endpoint_projective_fractionRing_tensor_g (k := k) S = 0 := by
  -- Tensoring keeps the composite zero because `lTensor` respects linear-map composition.
  apply ModuleCat.hom_ext
  let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (finiteProjectiveModuleProperty R).ι
  let hzero : U.g.hom.comp U.f.hom = 0 := by
    ext x
    simpa [LinearMap.comp_apply] using U.moduleCat_zero_apply x
  apply LinearMap.ext
  intro x
  change
    ((LinearMap.lTensor (FractionRing R) U.g.hom).comp
      (LinearMap.lTensor (FractionRing R) U.f.hom)) x = 0
  simpa [LinearMap.comp_apply, LinearMap.lTensor_comp] using
    LinearMap.congr_fun (congrArg (LinearMap.lTensor (FractionRing R)) hzero) x

/-- Helper for Chap10 Example 10 55 5: tensor a finite-projective short complex with the fraction
field of the equal-endpoint ring. -/
noncomputable def equal_endpoint_projective_fractionRing_tensor_shortComplex
    (S : CategoryTheory.ShortComplex (FiniteProjectiveModuleCat R)) :
    CategoryTheory.ShortComplex (ModuleCat (FractionRing R)) :=
  let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (finiteProjectiveModuleProperty R).ι
  { X₁ := ModuleCat.of (FractionRing R) ((FractionRing R) ⊗[R] U.X₁)
    X₂ := ModuleCat.of (FractionRing R) ((FractionRing R) ⊗[R] U.X₂)
    X₃ := ModuleCat.of (FractionRing R) ((FractionRing R) ⊗[R] U.X₃)
    f := equal_endpoint_projective_fractionRing_tensor_f (k := k) S
    g := equal_endpoint_projective_fractionRing_tensor_g (k := k) S
    zero := equal_endpoint_projective_fractionRing_tensor_zero (k := k) S }

/-- Helper for Chap10 Example 10 55 5: fraction-field base change preserves short exactness of
finite-projective short complexes over the equal-endpoint ring. -/
theorem equal_endpoint_projective_fractionRing_tensor_shortExact
    (S : CategoryTheory.ShortComplex (FiniteProjectiveModuleCat R))
    (hS : (S.map (finiteProjectiveModuleProperty R).ι).ShortExact) :
    (equal_endpoint_projective_fractionRing_tensor_shortComplex (k := k) S).ShortExact := by
  let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (finiteProjectiveModuleProperty R).ι
  -- Work in `ModuleCat` after tensoring so exactness, injectivity, and surjectivity can be read
  -- on the underlying linear maps.
  refine ModuleCat.shortComplex_shortExact
      (equal_endpoint_projective_fractionRing_tensor_shortComplex (k := k) S) ?_ ?_ ?_
  · have hExactBase : Function.Exact U.f.hom U.g.hom := by
      exact (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact U).1 hS.exact
    simpa [equal_endpoint_projective_fractionRing_tensor_shortComplex, U] using
      (Module.Flat.lTensor_exact (FractionRing R) hExactBase)
  · have hf : Function.Injective U.f.hom := by
      simpa [U] using hS.moduleCat_injective_f
    simpa [equal_endpoint_projective_fractionRing_tensor_shortComplex, U] using
      (Module.Flat.lTensor_preserves_injective_linearMap
        (M := FractionRing R) U.f.hom hf)
  · have hg : Function.Surjective U.g.hom := by
      simpa [U] using hS.moduleCat_surjective_g
    simpa [equal_endpoint_projective_fractionRing_tensor_shortComplex, U] using
      (LinearMap.lTensor_surjective (FractionRing R) hg)

/-- Helper for Chap10 Example 10 55 5: projective generic rank is additive on short exact
sequences. -/
theorem equalEndpointProjectiveRank_respects_shortExact
    (S : CategoryTheory.ShortComplex (FiniteProjectiveModuleCat R))
    (hS : (S.map (finiteProjectiveModuleProperty R).ι).ShortExact) :
    equalEndpointProjectiveRank k S.X₂ =
      equalEndpointProjectiveRank k S.X₁ + equalEndpointProjectiveRank k S.X₃ := by
  let T : CategoryTheory.ShortComplex (ModuleCat (FractionRing R)) :=
    equal_endpoint_projective_fractionRing_tensor_shortComplex (k := k) S
  have hT : T.ShortExact := by
    simpa [T] using equal_endpoint_projective_fractionRing_tensor_shortExact (k := k) S hS
  -- The tensorized objects are finite-dimensional vector spaces over the fraction field.
  let _ : Module.Finite (FractionRing R) T.X₁ := by
    let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (finiteProjectiveModuleProperty R).ι
    let _ : Module.Finite R U.X₁ := by
      simpa [U] using (inferInstance : Module.Finite R S.X₁.obj)
    simpa [T, U, equal_endpoint_projective_fractionRing_tensor_shortComplex] using
      (inferInstance : Module.Finite (FractionRing R) ((FractionRing R) ⊗[R] U.X₁))
  let _ : Module.Finite (FractionRing R) T.X₃ := by
    let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (finiteProjectiveModuleProperty R).ι
    let _ : Module.Finite R U.X₃ := by
      simpa [U] using (inferInstance : Module.Finite R S.X₃.obj)
    simpa [T, U, equal_endpoint_projective_fractionRing_tensor_shortComplex] using
      (inferInstance : Module.Finite (FractionRing R) ((FractionRing R) ⊗[R] U.X₃))
  let _ : Module.Finite (FractionRing R) T.X₂ := by
    let U : CategoryTheory.ShortComplex (ModuleCat R) := S.map (finiteProjectiveModuleProperty R).ι
    let _ : Module.Finite R U.X₂ := by
      simpa [U] using (inferInstance : Module.Finite R S.X₂.obj)
    simpa [T, U, equal_endpoint_projective_fractionRing_tensor_shortComplex] using
      (inferInstance : Module.Finite (FractionRing R) ((FractionRing R) ⊗[R] U.X₂))
  let _ : Module.Free (FractionRing R) T.X₁ :=
    Module.Free.of_divisionRing (FractionRing R) T.X₁
  let _ : Module.Free (FractionRing R) T.X₃ :=
    Module.Free.of_divisionRing (FractionRing R) T.X₃
  let _ : Module.Free (FractionRing R) T.X₂ :=
    Module.Free.of_divisionRing (FractionRing R) T.X₂
  have hfinrank :
      Module.finrank (FractionRing R) T.X₂ =
        Module.finrank (FractionRing R) T.X₁ + Module.finrank (FractionRing R) T.X₃ := by
    simpa [T] using
      (ModuleCat.free_shortExact_finrank_add (S := T) hT rfl rfl)
  let _ : Module.Free (FractionRing R) ((FractionRing R) ⊗[R] S.X₁.obj) :=
    Module.Free.of_divisionRing (FractionRing R) ((FractionRing R) ⊗[R] S.X₁.obj)
  let _ : Module.Free (FractionRing R) ((FractionRing R) ⊗[R] S.X₂.obj) :=
    Module.Free.of_divisionRing (FractionRing R) ((FractionRing R) ⊗[R] S.X₂.obj)
  let _ : Module.Free (FractionRing R) ((FractionRing R) ⊗[R] S.X₃.obj) :=
    Module.Free.of_divisionRing (FractionRing R) ((FractionRing R) ⊗[R] S.X₃.obj)
  -- Cast the vector-space finrank identity to the integer-valued K0 rank invariant.
  simpa [equalEndpointProjectiveRank, T, Nat.cast_add] using
    congrArg (fun n : ℕ ↦ (n : ℤ)) hfinrank

/-- Helper for Chap10 Example 10 55 5: finite-projective Grothendieck relations lie in the
kernel of projective generic rank. -/
theorem equalEndpointProjectiveRelations_le_ker_rank :
    modulePropertyK0Relations R (finiteProjectiveModuleProperty R) ≤
      (FreeAbelianGroup.lift (equalEndpointProjectiveRank k)).ker := by
  rw [modulePropertyK0Relations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    FreeAbelianGroup.lift (equalEndpointProjectiveRank k)
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  have hrank :
      equalEndpointProjectiveRank k S.X₂ =
        equalEndpointProjectiveRank k S.X₁ + equalEndpointProjectiveRank k S.X₃ :=
    equalEndpointProjectiveRank_respects_shortExact (k := k) S hS
  -- The rank identity kills the defining K0 relation.
  rw [hrank]
  abel

/-- Helper for Chap10 Example 10 55 5: the generic-rank homomorphism on projective K0 of the
equal-endpoint ring. -/
noncomputable def equalEndpointProjectiveRankMap :
    projectiveGrothendieckGroup R →+ ℤ :=
  ModulePropertyK0.lift R (equalEndpointProjectiveRank k)
    (equalEndpointProjectiveRelations_le_ker_rank k)

/-- Helper for Chap10 Example 10 55 5: projective generic rank evaluates on K0 generator classes
by tensoring with the fraction field. -/
theorem equalEndpointProjectiveRankMap_apply_of
    (M : FiniteProjectiveModuleCat R) :
    equalEndpointProjectiveRankMap k (projectiveGrothendieckGroupOf R M) =
      equalEndpointProjectiveRank k M := by
  -- The quotient lift agrees with the generator-level rank functional.
  simpa using ModulePropertyK0.lift_of R
    (equalEndpointProjectiveRank k)
    (equalEndpointProjectiveRelations_le_ker_rank k)
    M

end
