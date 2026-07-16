import stacks_proof.stacks_project.Chap10.Example_10_55_5.PolynomialEvaluation

noncomputable section

open scoped TensorProduct

universe u

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Example 10.55.5: the standard pair
`k[X] --(· X)→ k[X] --ev₀→ k` is exact. -/
theorem polynomial_mul_X_eval_zero_exact :
    Function.Exact
      (fun q : Polynomial k ↦ q * Polynomial.X)
      (fun p : Polynomial k ↦ polynomial_eval_zero (k := k) p) := by
  intro p
  constructor
  · intro hp
    -- Vanishing at `0` is the same as divisibility by `X`.
    change polynomial_eval_zero (k := k) p = 0 at hp
    have hp' : p.coeff 0 = 0 := by
      simpa [polynomial_eval_zero] using hp
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr hp'
    refine ⟨q, ?_⟩
    simpa [mul_comm] using hq.symm
  · rintro ⟨q, rfl⟩
    -- Multiples of `X` vanish under evaluation at `0`.
    simp [polynomial_eval_zero]

/-- Helper for Example 10.55.5: multiplication by `X` on `k[X]` is injective. -/
theorem polynomial_mul_X_injective :
    Function.Injective (fun q : Polynomial k ↦ q * Polynomial.X) := by
  intro p q hp
  -- `k[X]` is a domain, so right multiplication by the nonzero polynomial `X` cancels.
  exact mul_right_cancel₀ Polynomial.X_ne_zero hp

/-- Helper for Example 10.55.5: evaluation at `0` on `k[X]` is surjective. -/
theorem polynomial_eval_zero_surjective :
    Function.Surjective (fun p : Polynomial k ↦ polynomial_eval_zero (k := k) p) := by
  intro a
  refine ⟨Polynomial.C a, ?_⟩
  -- Constant polynomials realize every scalar in the target field.
  simp [polynomial_eval_zero]

/-- Helper for Example 10.55.5: endpoint evaluation is the restriction of `ev₀ : k[X] → k` to the
equal-endpoint subring. -/
theorem equal_endpoint_eval_eq_polynomial_eval_zero (r : R) :
    equal_endpoint_eval k r =
      polynomial_eval_zero (k := k) (algebraMap R (Polynomial k) r) := by
  -- Both ring maps are `eval₀` composed with the inclusion `R ↪ k[X]`.
  rfl

/-- Helper for Example 10.55.5: the `R`-module on `k` obtained by restricting scalars from
`k[X]` acts by endpoint evaluation. -/
theorem equal_endpoint_restrictScalars_eval_zero_smul (r : R) (a : k) :
    let _ : Module R k := Module.restrictScalars R (Polynomial k) k
    let _ : IsScalarTower R (Polynomial k) k := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    (r • a : k) = equal_endpoint_eval k r * a := by
  -- The restricted action uses `ev₀` on the image of `r` inside `k[X]`.
  rw [show (r • a : k) =
      polynomial_eval_zero (k := k) (algebraMap R (Polynomial k) r) * a by rfl]
  rw [equal_endpoint_eval_eq_polynomial_eval_zero]

/-- Helper for Example 10.55.5: the `k[X]`-module `k = k[X]/(X)` is torsion, with `X` killing every
element. -/
theorem polynomial_eval_zero_isTorsion :
    Module.IsTorsion (Polynomial k) k := by
  intro a
  by_cases ha : a = 0
  · refine ⟨⟨1, mem_nonZeroDivisors_iff_ne_zero.2 one_ne_zero⟩, ?_⟩
    simpa [ha]
  · refine ⟨⟨Polynomial.X, mem_nonZeroDivisors_iff_ne_zero.2 Polynomial.X_ne_zero⟩, ?_⟩
    -- The distinguished polynomial `X` acts by `0` under evaluation at `0`.
    change polynomial_eval_zero (k := k) Polynomial.X * a = 0
    simp [polynomial_eval_zero]

/-- Helper for Example 10.55.5: the generic rank of `k[X]/(X)` over `k[X]` is zero. -/
theorem equal_endpoint_polynomial_torsion_tensor_finrank_zero :
    (Module.finrank (FractionRing (Polynomial k))
      ((FractionRing (Polynomial k)) ⊗[Polynomial k] k) : ℤ) = 0 := by
  let K := FractionRing (Polynomial k)
  let T : Type u := K ⊗[Polynomial k] k
  have hrank : Module.rank K T = 0 := by
    -- Base change to the fraction field preserves rank, and the source module is torsion.
    calc
      Module.rank K T = Module.rank (Polynomial k) k := by
        simpa [K, T] using (TensorProduct.isBaseChange (Polynomial k) k K).rank_eq
      _ = 0 := by
        have htors : Module.IsTorsion (Polynomial k) k :=
          polynomial_eval_zero_isTorsion (k := k)
        exact (rank_eq_zero_iff_isTorsion).2 htors
  have hfinrank :
      Module.finrank K T = 0 :=
    let _ : Module.Free K T := Module.Free.of_divisionRing K T
    Module.finrank_eq_zero_of_rank_eq_zero hrank
  rw [hfinrank]
  norm_num

/-- Helper for Example 10.55.5: the class of `k[X]/(X)` vanishes in `K'_0(k[X])`. -/
theorem equal_endpoint_polynomial_field_class_eq_zero :
    finiteGrothendieckGroupOf (Polynomial k) (FGModuleCat.of (Polynomial k) k) = 0 := by
  -- The earlier PID computation identifies `K'_0(k[X])` with generic rank.
  apply (finiteGrothendieckGroup_pidEquiv (Polynomial k)).injective
  change finiteGrothendieckGroup_pidRankMap (Polynomial k)
      (finiteGrothendieckGroupOf (Polynomial k) (FGModuleCat.of (Polynomial k) k)) = 0
  rw [finiteGrothendieckGroup_pidRankMap_apply_of]
  exact equal_endpoint_polynomial_torsion_tensor_finrank_zero (k := k)

/-- Helper for Example 10.55.5: the zero `R`-module represents the zero object in
`FGModuleCat R`. -/
theorem equal_endpoint_isFG_zero :
    ModuleCat.isFG R (ModuleCat.of R PUnit) := by
  -- The zero module is finitely generated over every ring.
  rw [ModuleCat.isFG_iff]
  infer_instance

/-- Helper for Example 10.55.5: the identity map on `k` is `R`-linear from the restricted
evaluation-at-`0` action to the endpoint-evaluation action. -/
theorem equal_endpoint_restrictScalars_eval_zero_linear_map_smul
    (r : R)
    (a : (ModuleCat.restrictScalars (algebraMap R (Polynomial k))).obj
      (ModuleCat.of (Polynomial k) k)) :
    (AddEquiv.refl k) (r • a) = (r • (AddEquiv.refl k a) : k) := by
  -- The restricted action is exactly endpoint evaluation, so the identity map is linear.
  simpa using equal_endpoint_restrictScalars_eval_zero_smul (k := k) r a

/-- Helper for Example 10.55.5: the restricted evaluation-at-`0` module on `k` is canonically the
same `R`-module as the endpoint-evaluation module. -/
noncomputable def equal_endpoint_restrictScalars_eval_zero_moduleIso :
    (ModuleCat.restrictScalars (algebraMap R (Polynomial k))).obj (ModuleCat.of (Polynomial k) k) ≅
      ModuleCat.of R k :=
  (show ↑((ModuleCat.restrictScalars (algebraMap R (Polynomial k))).obj
      (ModuleCat.of (Polynomial k) k)) ≃ₗ[R] k from
    { __ := AddEquiv.refl k
      map_smul' := equal_endpoint_restrictScalars_eval_zero_linear_map_smul (k := k) }).toModuleIso

/-- Helper for Example 10.55.5: the packaged restricted object of a finite `k[X]`-module is still
finitely generated over `R`. -/
theorem equal_endpoint_restrictScalars_isFG
    (M : FGModuleCat (Polynomial k)) :
    ModuleCat.isFG R (ModuleCat.of R ↑M.obj) := by
  -- Descend finite generation along the inclusion `R ↪ k[X]` on the literal carrier owner.
  let _ : Module R M.obj := Module.restrictScalars R (Polynomial k) M.obj
  let _ : IsScalarTower R (Polynomial k) M.obj := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let hiff : Module.Finite R M.obj ↔ Module.Finite (Polynomial k) M.obj :=
    Module.Finite.iff_of_finite
  rw [ModuleCat.isFG_iff]
  exact hiff.2 M.property

/-- Helper for Example 10.55.5: after restricting scalars along `R ↪ k[X]`, a finite
`k[X]`-module is still finite over `R`. -/
theorem equal_endpoint_restrictScalars_module_finite
    (M : FGModuleCat (Polynomial k)) : Module.Finite R ↑M := by
  -- The finite `k[X]`-module stays finite after restricting scalars along `R → k[X]`.
  let _ : Module R M.obj := Module.restrictScalars R (Polynomial k) M.obj
  let _ : IsScalarTower R (Polynomial k) M.obj := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let hiff : Module.Finite R M.obj ↔ Module.Finite (Polynomial k) M.obj :=
    Module.Finite.iff_of_finite
  exact hiff.2 M.property

/-- Helper for Example 10.55.5: a finite `k[X]`-module defines a canonical finite `R`-module by
restriction of scalars along `R ↪ k[X]`. -/
noncomputable abbrev equal_endpoint_restrictScalars_object
    (M : FGModuleCat (Polynomial k)) : FGModuleCat R :=
  -- Package the literal carrier `M.obj` with its restricted `R`-action once and for all.
  let _ : Module R M.obj := Module.restrictScalars R (Polynomial k) M.obj
  let _ : IsScalarTower R (Polynomial k) M.obj := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module.Finite R M.obj := equal_endpoint_restrictScalars_module_finite (k := k) M
  FGModuleCat.of R M.obj

/-- Helper for Example 10.55.5: the restricted `k[X]`-module `k = k[X]/(X)` is the same finite
`R`-module as the endpoint-evaluation module. -/
noncomputable def equal_endpoint_restrictScalars_eval_zero_fgModuleIso :
    equal_endpoint_restrictScalars_object (k := k) (FGModuleCat.of (Polynomial k) k) ≅
      FGModuleCat.of R k :=
  -- The source owner is the literal restricted `R`-module on `k`, so the identity map upgrades
  -- the ambient module isomorphism to the finite-module category.
  CategoryTheory.ObjectProperty.isoMk (P := ModuleCat.isFG R)
    ((show
        ↑(equal_endpoint_restrictScalars_object (k := k) (FGModuleCat.of (Polynomial k) k)) ≃ₗ[R] k
      from
        { __ := AddEquiv.refl k
          map_smul' := fun r a ↦
            equal_endpoint_restrictScalars_eval_zero_smul (k := k) r a }).toModuleIso)

/-- Helper for Example 10.55.5: restricting scalars along `R ↪ k[X]` sends the Grothendieck
relations for finite `k[X]`-modules to zero in `K'_0(R)`. -/
theorem equal_endpoint_relations_le_ker_restrictScalars :
    modulePropertyK0Relations (Polynomial k) (ModuleCat.isFG (Polynomial k)) ≤
      (FreeAbelianGroup.lift fun M : FGModuleCat (Polynomial k) ↦
        finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) M)).ker := by
  rw [modulePropertyK0Relations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    FreeAbelianGroup.lift
        (fun M : FGModuleCat (Polynomial k) ↦
          finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) M))
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  let U : CategoryTheory.ShortComplex (ModuleCat (Polynomial k)) :=
    S.map (ModuleCat.isFG (Polynomial k)).ι
  have hU : U.ShortExact := by
    -- Forgetting the finiteness predicate recovers the original short exact sequence in
    -- `ModuleCat (k[X])`.
    simpa [U] using hS
  have hExact :
      Function.Exact (S.f.hom.hom.restrictScalars R) (S.g.hom.hom.restrictScalars R) := by
    -- Restriction of scalars preserves the exact pair on the underlying functions.
    simpa [U] using
      (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact U).mp hU.exact
  have hf_injective : Function.Injective (S.f.hom.hom.restrictScalars R) := by
    -- Injectivity of the first map is unaffected by restriction of scalars.
    simpa [U] using hU.moduleCat_injective_f
  have hg_surjective : Function.Surjective (S.g.hom.hom.restrictScalars R) := by
    -- Surjectivity of the second map is unaffected by restriction of scalars.
    simpa [U] using hU.moduleCat_surjective_g
  let _ : Module R S.X₁.obj := Module.restrictScalars R (Polynomial k) S.X₁.obj
  let _ : Module R S.X₂.obj := Module.restrictScalars R (Polynomial k) S.X₂.obj
  let _ : Module R S.X₃.obj := Module.restrictScalars R (Polynomial k) S.X₃.obj
  let _ : IsScalarTower R (Polynomial k) S.X₁.obj :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower R (Polynomial k) S.X₂.obj :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower R (Polynomial k) S.X₃.obj :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module.Finite R S.X₁.obj :=
    equal_endpoint_restrictScalars_module_finite (k := k) S.X₁
  let _ : Module.Finite R S.X₂.obj :=
    equal_endpoint_restrictScalars_module_finite (k := k) S.X₂
  let _ : Module.Finite R S.X₃.obj :=
    equal_endpoint_restrictScalars_module_finite (k := k) S.X₃
  let T : CategoryTheory.ShortComplex (FGModuleCat R) :=
    { X₁ := equal_endpoint_restrictScalars_object (k := k) S.X₁
      X₂ := equal_endpoint_restrictScalars_object (k := k) S.X₂
      X₃ := equal_endpoint_restrictScalars_object (k := k) S.X₃
      f := FGModuleCat.ofHom (S.f.hom.hom.restrictScalars R)
      g := FGModuleCat.ofHom (S.g.hom.hom.restrictScalars R)
      zero := by
        ext x
        change S.g.hom (S.f.hom x) = 0
        simpa using congrFun hExact.comp_eq_zero x }
  have hT : (T.map (ModuleCat.isFG R).ι).ShortExact := by
    -- Repackage the restricted sequence as a short exact sequence in `FGModuleCat R`.
    refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
    · simpa [T] using hExact
    · simpa [T] using hf_injective
    · simpa [T] using hg_surjective
  have hrel :
      finiteGrothendieckGroupOf R T.X₂ =
        finiteGrothendieckGroupOf R T.X₁ +
          finiteGrothendieckGroupOf R T.X₃ := by
    -- The defining Grothendieck relation now applies over the smaller ring `R`.
    simpa [finiteGrothendieckGroupOf] using
      ModulePropertyK0.of_shortExact R T hT
  -- Rewrite the relation into the subgroup-generator form `[X₂] - [X₁] - [X₃] = 0`.
  have hzero :
      finiteGrothendieckGroupOf R T.X₂ -
        finiteGrothendieckGroupOf R T.X₁ -
        finiteGrothendieckGroupOf R T.X₃ = 0 := by
    rw [hrel]
    abel
  simpa [T] using hzero

/-- Helper for Example 10.55.5: restriction of scalars along `R ↪ k[X]` induces the canonical map
`K'_0(k[X]) → K'_0(R)`. -/
noncomputable def equal_endpoint_finiteGrothendieckGroup_restrictScalars :
    finiteGrothendieckGroup (Polynomial k) →+ finiteGrothendieckGroup R :=
  ModulePropertyK0.lift (Polynomial k)
    (fun M : FGModuleCat (Polynomial k) ↦
      finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) M))
    (equal_endpoint_relations_le_ker_restrictScalars (k := k))

/-- Helper for Example 10.55.5: the restriction-of-scalars map sends a generator class to the class
of the restricted module. -/
theorem equal_endpoint_finiteGrothendieckGroup_restrictScalars_apply_of
    (M : FGModuleCat (Polynomial k)) :
    equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k)
        (finiteGrothendieckGroupOf (Polynomial k) M) =
      finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) M) := by
  -- The quotient lift agrees with its defining generator formula.
  simpa using ModulePropertyK0.lift_of (Polynomial k)
    (fun N : FGModuleCat (Polynomial k) ↦
      finiteGrothendieckGroupOf R (equal_endpoint_restrictScalars_object (k := k) N))
    (equal_endpoint_relations_le_ker_restrictScalars (k := k))
    M

/-- Helper for Example 10.55.5: evaluating the restriction-of-scalars map on the polynomial field
class lands in the class of the restricted `ev₀` module before any endpoint rewrite. -/
theorem equal_endpoint_restrictScalars_eval_zero_source_class :
    equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k)
        (finiteGrothendieckGroupOf (Polynomial k) (FGModuleCat.of (Polynomial k) k)) =
      finiteGrothendieckGroupOf R
        (equal_endpoint_restrictScalars_object (k := k) (FGModuleCat.of (Polynomial k) k)) := by
  -- This is the generator formula for the restriction-of-scalars homomorphism at the specific
  -- module `k[X]/(X)`.
  simpa using
    equal_endpoint_finiteGrothendieckGroup_restrictScalars_apply_of (k := k)
      (FGModuleCat.of (Polynomial k) k)

/-- Helper for Example 10.55.5: restricting the polynomial-side class of `k[X]/(X)` gives the
endpoint field class over `R`. -/
theorem equal_endpoint_restrictScalars_eval_zero_class :
    equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k)
        (finiteGrothendieckGroupOf (Polynomial k) (FGModuleCat.of (Polynomial k) k)) =
      finiteGrothendieckGroupOf R (FGModuleCat.of R k) := by
  -- First evaluate the restriction map on the generator class, then rewrite by the canonical
  -- identity-on-vectors `R`-linear isomorphism from the restricted `ev₀` action to endpoint
  -- evaluation.
  calc
    equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k)
        (finiteGrothendieckGroupOf (Polynomial k) (FGModuleCat.of (Polynomial k) k)) =
      finiteGrothendieckGroupOf R
        (equal_endpoint_restrictScalars_object (k := k) (FGModuleCat.of (Polynomial k) k)) := by
          exact equal_endpoint_restrictScalars_eval_zero_source_class (k := k)
    _ = finiteGrothendieckGroupOf R (FGModuleCat.of R k) := by
      -- Rewrite the restricted `ev₀` module to the endpoint-evaluation module by the canonical
      -- identity-on-vectors `R`-linear isomorphism.
      have hIso :
          ModulePropertyK0.of R (ModuleCat.isFG R)
              (equal_endpoint_restrictScalars_object (k := k) (FGModuleCat.of (Polynomial k) k)) =
            ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R k) := by
        exact (@ModulePropertyK0.of_iso R _ (ModuleCat.isFG R)
          (equal_endpoint_isFG_zero (k := k))
          _ _
          (equal_endpoint_restrictScalars_eval_zero_fgModuleIso (k := k)) :
            ModulePropertyK0.of R (ModuleCat.isFG R)
                (equal_endpoint_restrictScalars_object (k := k) (FGModuleCat.of (Polynomial k) k)) =
              ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R k))
      simpa [finiteGrothendieckGroupOf] using hIso

/-- Helper for Example 10.55.5: the endpoint field class vanishes in `K'_0(R)`. -/
theorem equal_endpoint_field_class_eq_zero :
    finiteGrothendieckGroupOf R (FGModuleCat.of R k) = 0 := by
  -- Apply the stabilized restriction-of-scalars map to the polynomial-side vanishing class and then
  -- rewrite the restricted generator by the canonical endpoint-evaluation module isomorphism.
  calc
    finiteGrothendieckGroupOf R (FGModuleCat.of R k) =
      equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k)
        (finiteGrothendieckGroupOf (Polynomial k) (FGModuleCat.of (Polynomial k) k)) := by
          symm
          exact equal_endpoint_restrictScalars_eval_zero_class (k := k)
    _ = equal_endpoint_finiteGrothendieckGroup_restrictScalars (k := k) 0 := by
          rw [equal_endpoint_polynomial_field_class_eq_zero (k := k)]
    _ = 0 := by
          simp [equal_endpoint_finiteGrothendieckGroup_restrictScalars]


end
