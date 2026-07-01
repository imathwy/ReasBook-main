import Serre.Chap14.Exercise_14_14_5_3.RepresentationBridge

open scoped MonoidAlgebra

universe u v w x

noncomputable section

variable {k : Type u} [Field k]
variable {G : Type v} [Group G] [Finite G]
variable {E : Type w} [AddCommGroup E] [Module k E] [Module k[G] E] [IsScalarTower k k[G] E]
variable {F : Type x} [AddCommGroup F] [Module k F] [Module k[G] F] [IsScalarTower k k[G] F]

/-- Helper for Exercise 14-14.5-3: summing the inverse-indexed singleton contributions recovers
the original coefficient at `h`. -/
lemma sum_single_inv_eval [Fintype G] (z : k[G]) (h : G) :
    ∑ g : G, (MonoidAlgebra.single g⁻¹ (z g⁻¹)) h = z h := by
  -- Only the term indexed by `h⁻¹` contributes to the coefficient at `h`.
  rw [Finset.sum_eq_single h⁻¹]
  · simp
  · intro g _ hne
    have hg_ne : h ≠ g⁻¹ := by
      -- Rewriting `g⁻¹ = h` would force `g = h⁻¹`, contradicting the chosen off-diagonal term.
      intro hEq
      apply hne
      calc
        g = (g⁻¹)⁻¹ := by simp
        _ = h⁻¹ := by rw [hEq]
    simp [Finsupp.single_eq_of_ne hg_ne]
  · intro hh
    exact False.elim (hh (show h⁻¹ ∈ (Finset.univ : Finset G) by simp))

/-- Helper for Exercise 14-14.5-3: summing the singleton decomposition of a group-algebra element
recovers the original coefficient function. -/
lemma sum_single_eval [Fintype G] (z : k[G]) (h : G) :
    ∑ g : G, (MonoidAlgebra.single g (z g)) h = z h := by
  -- Only the term indexed by `h` contributes to the coefficient at `h`.
  rw [Finset.sum_eq_single h]
  · simp
  · intro g _ hg
    simpa [hg]
  · intro hh
    exact False.elim (hh (show h ∈ (Finset.univ : Finset G) by simp))

/-- Helper for Exercise 14-14.5-3: the coordinatewise coefficient-at-`1` picker on the finite free
source has the expected averaged evaluation formula. -/
lemma finite_free_source_picker_average_eval
    [Fintype G]
    (n : ℕ) (y : Fin n → k[G]) (i : Fin n) (h : G) :
    ∑ g : G, (MonoidAlgebra.single g⁻¹ (((MonoidAlgebra.single g (1 : k)) • y) i 1)) h =
      (y i) h := by
  -- Multiplying by `single g` shifts the coefficient at `1` to the coefficient at `g⁻¹`.
  simpa [MonoidAlgebra.single_mul_apply] using
    sum_single_inv_eval (k := k) (G := G) (z := y i) (h := h)

/-- Helper for Exercise 14-14.5-3: the finite free source admits the coordinatewise projector to
the coefficient of `1`. -/
noncomputable def finite_free_source_picker_fun (n : ℕ) :
    RestrictScalars k k[G] (Fin n → k[G]) → RestrictScalars k k[G] (Fin n → k[G]) :=
  fun y i ↦ MonoidAlgebra.single 1 (y i 1)

/-- Helper for Exercise 14-14.5-3: away from the distinguished coefficient `1`, the coordinate
picker vanishes. -/
lemma finite_free_source_picker_fun_apply_ne_one
    (n : ℕ) (y : RestrictScalars k k[G] (Fin n → k[G])) (i : Fin n) {h : G} (hh : h ≠ 1) :
    finite_free_source_picker_fun (k := k) (G := G) n y i h = 0 := by
  -- The picker keeps only the coefficient at `1`.
  simp [finite_free_source_picker_fun, hh]

/-- Helper for Exercise 14-14.5-3: two restricted-scalars vectors in the finite free source are
equal once they agree at coefficient `1` in every coordinate and both vanish away from `1`. -/
lemma finite_free_source_picker_fun_ext
    (n : ℕ) (u v : RestrictScalars k k[G] (Fin n → k[G]))
    (h_one : ∀ i, u i 1 = v i 1)
    (hu : ∀ i {h : G}, h ≠ 1 → u i h = 0)
    (hv : ∀ i {h : G}, h ≠ 1 → v i h = 0) :
    u = v := by
  -- Compare the two vectors coordinatewise, splitting into the distinguished coefficient and the
  -- vanishing off-diagonal coefficients.
  funext i
  apply Finsupp.ext
  intro h
  by_cases hh : h = 1
  · simpa [hh] using h_one i
  · rw [hu i hh, hv i hh]

/-- Helper for Exercise 14-14.5-3: the restricted `k`-scalar action on the finite free source acts
coordinatewise through the algebra map `k → k[G]`. -/
lemma finite_free_source_restrictScalars_smul_apply
    (n : ℕ) (a : k) (y : RestrictScalars k k[G] (Fin n → k[G])) (i : Fin n) :
    (a • y) i = algebraMap k k[G] a • y i := by
  -- Unpack the restricted scalar action through `RestrictScalars.addEquiv` and then evaluate at
  -- the chosen coordinate.
  change
    (RestrictScalars.addEquiv k k[G] (Fin n → k[G]) (a • y)) i =
      (algebraMap k k[G] a • RestrictScalars.addEquiv k k[G] (Fin n → k[G]) y) i
  exact congrArg
    (fun f : Fin n → k[G] => f i)
    (RestrictScalars.addEquiv_map_smul (R := k) (S := k[G]) (M := Fin n → k[G]) a y)

/-- Helper for Exercise 14-14.5-3: the coordinate picker preserves addition. -/
lemma finite_free_source_picker_fun_map_add
    (n : ℕ) (y z : RestrictScalars k k[G] (Fin n → k[G])) :
    finite_free_source_picker_fun (k := k) (G := G) n (y + z) =
      finite_free_source_picker_fun (k := k) (G := G) n y +
        finite_free_source_picker_fun (k := k) (G := G) n z := by
  -- Compare the two finitely supported functions at coefficient `1` and use vanishing away from
  -- `1` to recover equality of the whole vectors.
  refine finite_free_source_picker_fun_ext (k := k) (G := G) n
    (u := finite_free_source_picker_fun (k := k) (G := G) n (y + z))
    (v := finite_free_source_picker_fun (k := k) (G := G) n y +
      finite_free_source_picker_fun (k := k) (G := G) n z) ?_ ?_ ?_
  · intro i
    calc
      (finite_free_source_picker_fun (k := k) (G := G) n (y + z) i) 1
        = ((y + z) i) 1 := by simp [finite_free_source_picker_fun]
      _ = (y i) 1 + (z i) 1 := Finsupp.add_apply (y i) (z i) 1
      _ = ((finite_free_source_picker_fun (k := k) (G := G) n y +
          finite_free_source_picker_fun (k := k) (G := G) n z) i) 1 := by
            change (y i) 1 + (z i) 1 =
              (MonoidAlgebra.single (1 : G) (y i 1) + MonoidAlgebra.single (1 : G) (z i 1)) 1
            simp
  · intro i h hh
    exact finite_free_source_picker_fun_apply_ne_one (k := k) (G := G) n (y + z) i hh
  · intro i h hh
    have hy0 :=
      finite_free_source_picker_fun_apply_ne_one (k := k) (G := G) n y i hh
    have hz0 :=
      finite_free_source_picker_fun_apply_ne_one (k := k) (G := G) n z i hh
    calc
      ((finite_free_source_picker_fun (k := k) (G := G) n y +
          finite_free_source_picker_fun (k := k) (G := G) n z) i) h
        = (finite_free_source_picker_fun (k := k) (G := G) n y i) h +
            (finite_free_source_picker_fun (k := k) (G := G) n z i) h := by
              rfl
      _ = 0 := by rw [hy0, hz0]; simp

/-- Helper for Exercise 14-14.5-3: the coordinate picker is `k`-linear. -/
lemma finite_free_source_picker_fun_map_smul
    (n : ℕ) (a : k) (y : RestrictScalars k k[G] (Fin n → k[G])) :
    finite_free_source_picker_fun (k := k) (G := G) n (a • y) =
      a • finite_free_source_picker_fun (k := k) (G := G) n y := by
  -- Route correction: instead of coefficientwise ad hoc rewrites, use the support-at-`1`
  -- extensionality lemma and compare only the distinguished coefficient.
  refine finite_free_source_picker_fun_ext (k := k) (G := G) n
    (u := finite_free_source_picker_fun (k := k) (G := G) n (a • y))
    (v := a • finite_free_source_picker_fun (k := k) (G := G) n y) ?_ ?_ ?_
  · intro i
    have hsmul :=
      finite_free_source_restrictScalars_smul_apply (k := k) (G := G) n a y i
    calc
      (finite_free_source_picker_fun (k := k) (G := G) n (a • y) i) 1
        = ((a • y) i) 1 := by simp [finite_free_source_picker_fun]
      _ = a * y i 1 := by
            simpa [Algebra.smul_def, MonoidAlgebra.single_mul_apply] using
              congrArg (fun z : k[G] => z 1) hsmul
      _ = ((a • finite_free_source_picker_fun (k := k) (G := G) n y) i) 1 := by
            have hpicker :=
              finite_free_source_restrictScalars_smul_apply
                (k := k) (G := G) n a
                (finite_free_source_picker_fun (k := k) (G := G) n y) i
            simpa [finite_free_source_picker_fun, Algebra.smul_def,
              MonoidAlgebra.single_mul_apply] using
              (congrArg (fun z : k[G] => z 1) hpicker).symm
  · intro i h hh
    exact finite_free_source_picker_fun_apply_ne_one (k := k) (G := G) n (a • y) i hh
  · intro i h hh
    have hy0 :=
      finite_free_source_picker_fun_apply_ne_one (k := k) (G := G) n y i hh
    have hpicker :=
      finite_free_source_restrictScalars_smul_apply
        (k := k) (G := G) n a
        (finite_free_source_picker_fun (k := k) (G := G) n y) i
    calc
      ((a • finite_free_source_picker_fun (k := k) (G := G) n y) i) h
        = a • ((finite_free_source_picker_fun (k := k) (G := G) n y i) h) := by
            simpa [Algebra.smul_def, MonoidAlgebra.single_mul_apply] using
              congrArg (fun z : k[G] => z h) hpicker
      _ = 0 := by rw [hy0]; simp

/-- Helper for Exercise 14-14.5-3: the finite free source admits the coordinatewise projector to
the coefficient of `1` as a `k`-linear endomorphism. -/
noncomputable def finite_free_source_picker (n : ℕ) :
    Module.End k (RestrictScalars k k[G] (Fin n → k[G])) :=
  { toFun := finite_free_source_picker_fun (k := k) (G := G) n
    map_add' := finite_free_source_picker_fun_map_add (k := k) (G := G) n
    map_smul' := finite_free_source_picker_fun_map_smul (k := k) (G := G) n }

/-- Helper for Exercise 14-14.5-3: the finite free source picker keeps only the coefficient at `1`
in each coordinate. -/
@[simp] lemma finite_free_source_picker_apply
    (n : ℕ) (y : Fin n → k[G]) (i : Fin n) :
    finite_free_source_picker (k := k) (G := G) n y i = MonoidAlgebra.single 1 (y i 1) := by
  rfl

/-- Helper for Exercise 14-14.5-3: on the owner module of the internal-Hom representation with
finite free source, averaging precomposition by the coefficient-at-`1` picker gives the identity.
-/
noncomputable def linHom_precompose_picker_end
    (n : ℕ) :
    Module.End k
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
        (Representation.ofModule (k := k) (G := G) F)).asModule) :=
  let ρfree :=
    Representation.linHom
      (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
      (Representation.ofModule (k := k) (G := G) F)
  let precompose :
      Module.End k
        (RestrictScalars k k[G] (Fin n → k[G]) →ₗ[k] RestrictScalars k k[G] F) :=
    LinearMap.lcomp k (RestrictScalars k k[G] F)
      (finite_free_source_picker (k := k) (G := G) n)
  ρfree.asModuleEquiv.symm.toLinearMap.comp (precompose.comp ρfree.asModuleEquiv.toLinearMap)

/-- Helper for Exercise 14-14.5-3: after applying the coefficient-at-`1` projector to each
translate of a finite free source vector, summing the resulting coefficients recovers the original
coordinate. -/
lemma finite_free_source_picker_average_translate_apply
    [Fintype G]
    (n : ℕ) (y : Fin n → k[G]) (i : Fin n) (h : G) :
    ∑ g : G,
        (MonoidAlgebra.single g⁻¹
          ((finite_free_source_picker (k := k) (G := G) n
            (MonoidAlgebra.single g (1 : k) • y) i) 1)) h =
      y i h := by
  -- This is exactly the coordinatewise averaging computation already established for the finite
  -- free source picker.
  simpa [finite_free_source_picker_apply] using
    finite_free_source_picker_average_eval (k := k) (G := G) (n := n) (y := y) (i := i) (h := h)

/-- Helper for Exercise 14-14.5-3: the source coefficient can be rewritten as the averaged picker
expression used in the finite-free internal-Hom calculation. -/
lemma finite_free_source_picker_average_translate_apply_symm
    [Fintype G]
    (n : ℕ) (y : Fin n → k[G]) (i : Fin n) (h : G) :
    y i h =
      ∑ g : G,
        (MonoidAlgebra.single g⁻¹
          ((finite_free_source_picker (k := k) (G := G) n
            (MonoidAlgebra.single g (1 : k) • y) i) 1)) h := by
  -- This is just the previously established averaging identity read in the reverse direction.
  symm
  exact finite_free_source_picker_average_translate_apply
    (k := k) (G := G) (n := n) (y := y) (i := i) (h := h)

/-- Helper for Exercise 14-14.5-3: after converting the owner module of the internal-Hom
representation back to ordinary linear maps, `linHom_precompose_picker_end` is literally
precomposition by the finite free source picker. -/
@[simp] lemma linHom_precompose_picker_end_apply
    (n : ℕ)
    (h :
      (Representation.linHom
        (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
        (Representation.ofModule (k := k) (G := G) F)).asModule) :
    (Representation.linHom
      (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
      (Representation.ofModule (k := k) (G := G) F)).asModuleEquiv
        (linHom_precompose_picker_end (k := k) (G := G) (F := F) n h) =
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
        (Representation.ofModule (k := k) (G := G) F)).asModuleEquiv h).comp
          (finite_free_source_picker (k := k) (G := G) n) := by
  rfl

/-- Helper for Exercise 14-14.5-3: the owner module of the internal-Hom representation attached
to two `ofModule` representations is the ordinary `k`-linear Hom space between the restricted
scalars of the underlying `k[G]`-modules. -/
noncomputable abbrev ofModule_linHom_asModuleLinearEquiv
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Type*) [AddCommGroup N] [Module k N] [Module k[G] N] [IsScalarTower k k[G] N] :
    ((Representation.linHom
      (Representation.ofModule (k := k) (G := G) M)
      (Representation.ofModule (k := k) (G := G) N)).asModule) ≃ₗ[k]
        (RestrictScalars k k[G] M →ₗ[k] RestrictScalars k k[G] N) :=
  (Representation.linHom
    (Representation.ofModule (k := k) (G := G) M)
    (Representation.ofModule (k := k) (G := G) N)).asModuleEquiv

/-- Helper for Exercise 14-14.5-3: freeze the internal-Hom representation attached to two
`k[G]`-modules so later projectivity and duality arguments can refer to a stable owner type. -/
noncomputable abbrev ofModule_linHom_rep
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Type*) [AddCommGroup N] [Module k N] [Module k[G] N] [IsScalarTower k k[G] N] :
    Representation k G (RestrictScalars k k[G] M →ₗ[k] RestrictScalars k k[G] N) :=
  Representation.linHom
    (Representation.ofModule (k := k) (G := G) M)
    (Representation.ofModule (k := k) (G := G) N)

/-- Helper for Exercise 14-14.5-3: the owner of the frozen internal-Hom representation inherits
its additive-group structure from the canonical internal-Hom owner. -/
instance ofModule_linHom_rep_asModule_addCommGroup
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Type*) [AddCommGroup N] [Module k N] [Module k[G] N] [IsScalarTower k k[G] N] :
    AddCommGroup ((ofModule_linHom_rep (k := k) (G := G) M N).asModule) := by
  delta ofModule_linHom_rep
  infer_instance

/-- Helper for Exercise 14-14.5-3: the owner of the frozen internal-Hom representation carries
the ambient `k`-module structure. -/
instance ofModule_linHom_rep_asModule_module
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Type*) [AddCommGroup N] [Module k N] [Module k[G] N] [IsScalarTower k k[G] N] :
    Module k ((ofModule_linHom_rep (k := k) (G := G) M N).asModule) :=
  ofModule_linHom_asModule_module (k := k) (G := G) (M := M) (N := N)

/-- Helper for Exercise 14-14.5-3: the owner of the frozen internal-Hom representation has
compatible `k`- and `k[G]`-scalar actions. -/
instance ofModule_linHom_rep_asModule_isScalarTower
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (N : Type*) [AddCommGroup N] [Module k N] [Module k[G] N] [IsScalarTower k k[G] N] :
    IsScalarTower k k[G] ((ofModule_linHom_rep (k := k) (G := G) M N).asModule) := by
  delta ofModule_linHom_rep
  infer_instance

/-- Helper for Exercise 14-14.5-3: the frozen internal-Hom representation still acts by the
usual conjugation formula on wrapped `k`-linear maps. -/
@[simp] lemma ofModule_linHom_rep_apply
    (g : G)
    (u : RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F) :
    ofModule_linHom_rep (k := k) (G := G) E F g u =
      ((Representation.ofModule (k := k) (G := G) F) g).comp
        (u.comp ((Representation.ofModule (k := k) (G := G) E) g⁻¹)) := by
  rfl

/-- Helper for Exercise 14-14.5-3: after acting by a basis element of `k[G]`, the finite free
picker still records only the coefficient at `1` in each coordinate. -/
@[simp] lemma finite_free_source_picker_smul_apply
    (n : ℕ) (g : G) (y : Fin n → k[G]) (i : Fin n) :
    finite_free_source_picker (k := k) (G := G) n (MonoidAlgebra.single g (1 : k) • y) i =
      MonoidAlgebra.single 1 (((MonoidAlgebra.single g (1 : k)) • y) i 1) := by
  rfl

/-- Helper for Exercise 14-14.5-3: on an `ofModule` representation, the action of `g` is scalar
multiplication by `single g`. -/
@[simp] lemma ofModule_apply_eq_single_smul
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (g : G) (x : RestrictScalars k k[G] M) :
    (Representation.ofModule (k := k) (G := G) M g) x =
      MonoidAlgebra.single g (1 : k) • x := by
  -- Unfold the `ofModule` action through its algebra map; on the underlying module this is
  -- exactly scalar multiplication by the group-algebra basis element `single g 1`.
  simpa [Representation.asAlgebraHom_single] using
    (Representation.ofModule_asAlgebraHom_apply_apply
      (k := k) (G := G) (M := M) (r := MonoidAlgebra.single g (1 : k)) (m := x))

/-- Helper for Exercise 14-14.5-3: the owner of the internal-Hom representation with finite free
source is projective over the base field. -/
theorem internal_hom_owner_projective_over_k
    [FiniteDimensional k F]
    (n : ℕ) :
    Module.Projective k
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
        (Representation.ofModule (k := k) (G := G) F)).asModule) := by
  -- Build projectivity on the ambient wrapped Hom space from a vector-space basis, then transport
  -- it back to the internal-Hom owner through the canonical owner equivalence.
  have hproj :
      Module.Projective k
        (RestrictScalars k k[G] (Fin n → k[G]) →ₗ[k] RestrictScalars k k[G] F) := by
    let b :=
      @Module.Basis.ofVectorSpace k
        (RestrictScalars k k[G] (Fin n → k[G]) →ₗ[k] RestrictScalars k k[G] F)
        (show DivisionRing k from inferInstance)
        (restrictScalars_linearMap_addCommGroup (k := k) (G := G) (M := Fin n → k[G]) (N := F))
        (restrictScalars_linearMap_module (k := k) (G := G) (M := Fin n → k[G]) (N := F))
    exact Module.Projective.of_basis b
  letI :
      Module.Projective k
        (RestrictScalars k k[G] (Fin n → k[G]) →ₗ[k] RestrictScalars k k[G] F) :=
    hproj
  let e :=
    ofModule_linHom_asModuleLinearEquiv (k := k) (G := G) (Fin n → k[G]) F
  exact Module.Projective.of_equiv' e.symm

/-- Helper for Exercise 14-14.5-3: freeze the internal-Hom owner in the finite free source case
so the averaging criterion can be applied to a stable carrier. -/
noncomputable abbrev finite_free_internal_hom_owner (n : ℕ) :=
  (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModule

/-- Helper for Exercise 14-14.5-3: the frozen finite-free internal-Hom owner carries the
transported `k`-module structure. -/
instance finite_free_internal_hom_owner_module (n : ℕ) :
    Module k (finite_free_internal_hom_owner (k := k) (G := G) (F := F) n) :=
  ofModule_linHom_asModule_module (k := k) (G := G) (M := Fin n → k[G]) (N := F)

/-- Helper for Exercise 14-14.5-3: the frozen finite-free internal-Hom owner retains the
underlying additive-group structure of the internal-Hom owner. -/
instance finite_free_internal_hom_owner_addCommGroup (n : ℕ) :
    AddCommGroup (finite_free_internal_hom_owner (k := k) (G := G) (F := F) n) := by
  delta finite_free_internal_hom_owner
  infer_instance

/-- Helper for Exercise 14-14.5-3: the frozen finite-free internal-Hom owner inherits its
canonical `k[G]`-module structure. -/
instance finite_free_internal_hom_owner_groupAlgebraModule (n : ℕ) :
    Module k[G] (finite_free_internal_hom_owner (k := k) (G := G) (F := F) n) := by
  delta finite_free_internal_hom_owner
  infer_instance

/-- Helper for Exercise 14-14.5-3: the ambient `k`- and `k[G]`-actions on the frozen finite-free
internal-Hom owner are compatible. -/
instance finite_free_internal_hom_owner_isScalarTower (n : ℕ) :
    IsScalarTower k k[G] (finite_free_internal_hom_owner (k := k) (G := G) (F := F) n) := by
  -- Reuse the exact internal-Hom scalar-tower bridge on the unfrozen owner.
  delta finite_free_internal_hom_owner
  exact
    ofModule_linHom_asModule_isScalarTower (k := k) (G := G)
      (M := Fin n → k[G]) (N := F)

/-- Helper for Exercise 14-14.5-3: view the picker-precomposition endomorphism directly on the
frozen finite-free internal-Hom owner. -/
noncomputable abbrev linHom_precompose_picker_end_on_owner (n : ℕ) :
    Module.End k (finite_free_internal_hom_owner (k := k) (G := G) (F := F) n) :=
  linHom_precompose_picker_end (k := k) (G := G) (F := F) n

/-- Helper for Exercise 14-14.5-3: the frozen owner endomorphism is definitionally the original
picker-precomposition operator. -/
@[simp] theorem linHom_precompose_picker_end_on_owner_eq
    (n : ℕ) :
    linHom_precompose_picker_end_on_owner (k := k) (G := G) (F := F) n =
      linHom_precompose_picker_end (k := k) (G := G) (F := F) n := rfl

/-- Helper for Exercise 14-14.5-3: for each fixed coordinate in the finite free source, the
averaged translated picker recovers the original coefficient function on `G`. -/
lemma finite_free_source_picker_average_translate_coordinate
    [Fintype G]
    (n : ℕ) :
    ∀ y : Fin n → k[G], ∀ i : Fin n,
      (fun h : G ↦
        ∑ g : G,
          (MonoidAlgebra.single g⁻¹
            ((finite_free_source_picker (k := k) (G := G) n
              (MonoidAlgebra.single g (1 : k) • y) i) 1)) h) =
        y i := by
  intro y i
  -- This is the coefficientwise averaging identity restated as an equality of functions on `G`.
  ext h
  exact
    finite_free_source_picker_average_translate_apply
      (k := k) (G := G) (n := n) (y := y) (i := i) (h := h)

/-- Helper for Exercise 14-14.5-3: for a fixed coordinate of the finite free source, the averaged
translated picker recovers the original group-algebra element. -/
lemma finite_free_source_picker_average_translate_coordinate_eq
    [Fintype G]
    (n : ℕ) (y : Fin n → k[G]) (i : Fin n) :
    (fun h : G ↦
      ∑ g : G,
        (MonoidAlgebra.single g⁻¹
          ((finite_free_source_picker (k := k) (G := G) n
            (MonoidAlgebra.single g (1 : k) • y) i) 1)) h) =
      y i := by
  exact
    finite_free_source_picker_average_translate_coordinate
      (k := k) (G := G) (n := n) y i

/-- Helper for Exercise 14-14.5-3: summing the translated coefficient-at-`1` projectors recovers
the original finite free source vector. -/
lemma finite_free_source_picker_average_translate
    [Fintype G]
    (n : ℕ) (y : Fin n → k[G]) :
    ∑ g : G,
      MonoidAlgebra.single g⁻¹ (1 : k) •
        finite_free_source_picker (k := k) (G := G) n
          (MonoidAlgebra.single g (1 : k) • y) = y := by
  -- Compare both sides at each coordinate and each group element, where the established
  -- coefficientwise averaging formula applies directly.
  funext i
  apply Finsupp.ext
  intro h
  let evih : RestrictScalars k k[G] (Fin n → k[G]) →ₗ[k] k :=
    { toFun := fun z ↦ z i h
      map_add' := by
        intro z w
        rfl
      map_smul' := by
        intro a z
        change (algebraMap k k[G] a • z i) h = a * (z i) h
        simp [Algebra.smul_def, MonoidAlgebra.single_mul_apply] }
  calc
    ((∑ g : G,
        MonoidAlgebra.single g⁻¹ (1 : k) •
          finite_free_source_picker (k := k) (G := G) n
            (MonoidAlgebra.single g (1 : k) • y)) i) h
      = evih
          (∑ g : G,
            MonoidAlgebra.single g⁻¹ (1 : k) •
              finite_free_source_picker (k := k) (G := G) n
                (MonoidAlgebra.single g (1 : k) • y)) := by
          rfl
    _ = ∑ g : G,
          evih
            (MonoidAlgebra.single g⁻¹ (1 : k) •
              finite_free_source_picker (k := k) (G := G) n
                (MonoidAlgebra.single g (1 : k) • y)) := by
          simpa [evih] using
            (evih.map_sum fun g : G =>
              MonoidAlgebra.single g⁻¹ (1 : k) •
                finite_free_source_picker (k := k) (G := G) n
                  (MonoidAlgebra.single g (1 : k) • y))
    _ = ∑ g : G,
          (MonoidAlgebra.single g⁻¹
            ((finite_free_source_picker (k := k) (G := G) n
              (MonoidAlgebra.single g (1 : k) • y) i) 1)) h := by
          refine Finset.sum_congr rfl ?_
          intro g _
          calc
            evih
                (MonoidAlgebra.single g⁻¹ (1 : k) •
                  finite_free_source_picker (k := k) (G := G) n
                    (MonoidAlgebra.single g (1 : k) • y))
              = (MonoidAlgebra.single g⁻¹
                  (((MonoidAlgebra.single g (1 : k) • y) i) 1)) h := by
                    change
                      (MonoidAlgebra.single g⁻¹ (1 : k) •
                        (finite_free_source_picker (k := k) (G := G) n
                          (MonoidAlgebra.single g (1 : k) • y) i)) h =
                        (MonoidAlgebra.single g⁻¹
                          (((MonoidAlgebra.single g (1 : k) • y) i) 1)) h
                    rw [finite_free_source_picker_apply]
                    simp [Algebra.smul_def, MonoidAlgebra.single_mul_apply]
            _ = (MonoidAlgebra.single g⁻¹
                  ((finite_free_source_picker (k := k) (G := G) n
                    (MonoidAlgebra.single g (1 : k) • y) i) 1)) h := by
                  simp [finite_free_source_picker_apply]
    _ = y i h := by
      exact
        finite_free_source_picker_average_translate_apply
          (k := k) (G := G) (n := n) (y := y) (i := i) (h := h)

/-- Helper for Exercise 14-14.5-3: the same averaging identity holds after evaluating at a fixed
coordinate and a fixed group element. -/
lemma finite_free_source_picker_average_translate_pointwise
    [Fintype G]
    (n : ℕ) (y : Fin n → k[G]) (i : Fin n) (h : G) :
    ((∑ g : G,
        MonoidAlgebra.single g⁻¹ (1 : k) •
          finite_free_source_picker (k := k) (G := G) n
            (MonoidAlgebra.single g (1 : k) • y)) i) h =
      y i h := by
  -- After evaluating the vector-valued sum at `i` and `h`, the finite free picker contributes the
  -- coefficient-at-`1` term from the already established vector-valued averaging identity.
  simpa using
    congrArg
      (fun z : Fin n → k[G] => z i h)
      (finite_free_source_picker_average_translate (k := k) (G := G) (n := n) (y := y))

/-- Helper for Exercise 14-14.5-3: the finite free source picker also satisfies the textbook
averaging formula with the outside translate indexed by `g`. -/
lemma finite_free_source_picker_textbook_average
    [Fintype G]
    (n : ℕ) (y : Fin n → k[G]) :
    ∑ g : G,
      MonoidAlgebra.single g (1 : k) •
        finite_free_source_picker (k := k) (G := G) n
          (MonoidAlgebra.single g⁻¹ (1 : k) • y) = y := by
  -- Evaluate the sum at each coordinate and group element, where only the matching singleton
  -- term contributes.
  funext i
  apply Finsupp.ext
  intro h
  let evih : RestrictScalars k k[G] (Fin n → k[G]) →ₗ[k] k :=
    { toFun := fun z ↦ z i h
      map_add' := by
        intro z w
        rfl
      map_smul' := by
        intro a z
        change (algebraMap k k[G] a • z i) h = a * (z i) h
        simp [Algebra.smul_def, MonoidAlgebra.single_mul_apply] }
  calc
    ((∑ g : G,
        MonoidAlgebra.single g (1 : k) •
          finite_free_source_picker (k := k) (G := G) n
            (MonoidAlgebra.single g⁻¹ (1 : k) • y)) i) h
      = evih
          (∑ g : G,
            MonoidAlgebra.single g (1 : k) •
              finite_free_source_picker (k := k) (G := G) n
                (MonoidAlgebra.single g⁻¹ (1 : k) • y)) := by
          rfl
    _ = ∑ g : G,
          evih
            (MonoidAlgebra.single g (1 : k) •
              finite_free_source_picker (k := k) (G := G) n
                (MonoidAlgebra.single g⁻¹ (1 : k) • y)) := by
          simpa [evih] using
            (evih.map_sum fun g : G =>
              MonoidAlgebra.single g (1 : k) •
                finite_free_source_picker (k := k) (G := G) n
                  (MonoidAlgebra.single g⁻¹ (1 : k) • y))
    _ = ∑ g : G, (MonoidAlgebra.single g ((y i) g)) h := by
          refine Finset.sum_congr rfl ?_
          intro g _
          change
            (MonoidAlgebra.single g (1 : k) •
                finite_free_source_picker (k := k) (G := G) n
                  (MonoidAlgebra.single g⁻¹ (1 : k) • y) i) h =
              (MonoidAlgebra.single g ((y i) g)) h
          rw [finite_free_source_picker_smul_apply]
          simp [Algebra.smul_def, MonoidAlgebra.single_mul_apply]
    _ = y i h := sum_single_eval (k := k) (G := G) (z := y i) (h := h)

/-- Helper for Exercise 14-14.5-3: after transporting the frozen internal-Hom owner through
`asModuleEquiv`, scalar multiplication by `single g` becomes the expected conjugation action on
the source variable. -/
lemma linHom_owner_single_smul_as_conjugation_precompose
    [Fintype G]
    (n : ℕ) (g : G)
    (h : finite_free_internal_hom_owner (k := k) (G := G) (F := F) n)
    (y : Fin n → k[G]) :
    (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv
        (MonoidAlgebra.single g (1 : k) • h) y =
      MonoidAlgebra.single g (1 : k) •
        ((ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv h
          (MonoidAlgebra.single g⁻¹ (1 : k) • y)) := by
  -- Evaluate the owner action through `asModuleEquiv`; on the frozen internal-Hom owner this is
  -- exactly the conjugation action on ordinary linear maps.
  calc
    (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv
        (MonoidAlgebra.single g (1 : k) • h) y
      = ((ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asAlgebraHom
          (MonoidAlgebra.single g (1 : k))
          ((ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv h)) y := by
          exact
            congrArg
              (fun u :
                RestrictScalars k k[G] (Fin n → k[G]) →ₗ[k] RestrictScalars k k[G] F ↦ u y)
              (Representation.asModuleEquiv_map_smul
                (ρ := ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F)
                (r := MonoidAlgebra.single g (1 : k))
                (x := h))
    _ = (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F g)
          ((ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv h) y := by
          simp [Representation.asAlgebraHom_single_one]
    _ = ((Representation.ofModule (k := k) (G := G) F) g)
          (((ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv h)
            (((Representation.ofModule (k := k) (G := G) (Fin n → k[G])) g⁻¹) y)) := by
          rfl
    _ = MonoidAlgebra.single g (1 : k) •
          ((ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv h
            (MonoidAlgebra.single g⁻¹ (1 : k) • y)) := by
          rw [ofModule_apply_eq_single_smul, ofModule_apply_eq_single_smul]
          rfl

/-- Helper for Exercise 14-14.5-3: after passing to the exact internal-Hom owner, each textbook
averaging summand acts by precomposing with the corresponding translated finite-free picker. -/
lemma linHom_precompose_picker_average_summand_apply
    [Fintype G]
    (n : ℕ) (g : G)
    (h :
      (Representation.linHom
        (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
        (Representation.ofModule (k := k) (G := G) F)).asModule)
    (y : Fin n → k[G]) :
    (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv
      (MonoidAlgebra.single g (1 : k) •
        linHom_precompose_picker_end (k := k) (G := G) (F := F) n
          (MonoidAlgebra.single g⁻¹ (1 : k) • h)) y =
      (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv h
        (MonoidAlgebra.single g (1 : k) •
          finite_free_source_picker (k := k) (G := G) n
            (MonoidAlgebra.single g⁻¹ (1 : k) • y)) := by
  -- First move the outer owner action across `asModuleEquiv`, then rewrite the inner
  -- endomorphism as precomposition by the finite-free picker.
  calc
    (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv
        (MonoidAlgebra.single g (1 : k) •
          linHom_precompose_picker_end (k := k) (G := G) (F := F) n
            (MonoidAlgebra.single g⁻¹ (1 : k) • h)) y
      = MonoidAlgebra.single g (1 : k) •
          ((ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv
            (linHom_precompose_picker_end (k := k) (G := G) (F := F) n
              (MonoidAlgebra.single g⁻¹ (1 : k) • h))
            (MonoidAlgebra.single g⁻¹ (1 : k) • y)) := by
          simpa using
            linHom_owner_single_smul_as_conjugation_precompose
              (k := k) (G := G) (F := F) (n := n) (g := g)
              (h := linHom_precompose_picker_end (k := k) (G := G) (F := F) n
                (MonoidAlgebra.single g⁻¹ (1 : k) • h))
              (y := y)
    _ = MonoidAlgebra.single g (1 : k) •
          ((ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv
            (MonoidAlgebra.single g⁻¹ (1 : k) • h)
            (finite_free_source_picker (k := k) (G := G) n
              (MonoidAlgebra.single g⁻¹ (1 : k) • y))) := by
          simp [linHom_precompose_picker_end_apply]
    _ = MonoidAlgebra.single g (1 : k) •
          (MonoidAlgebra.single g⁻¹ (1 : k) •
            ((ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv h
              (MonoidAlgebra.single g (1 : k) •
                finite_free_source_picker (k := k) (G := G) n
                  (MonoidAlgebra.single g⁻¹ (1 : k) • y)))) := by
          simpa using
            congrArg (fun z : RestrictScalars k k[G] F ↦ MonoidAlgebra.single g (1 : k) • z)
              (linHom_owner_single_smul_as_conjugation_precompose
              (k := k) (G := G) (F := F) (n := n) (g := g⁻¹)
              (h := h)
              (y := finite_free_source_picker (k := k) (G := G) n
                (MonoidAlgebra.single g⁻¹ (1 : k) • y)))
    _ = (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv h
          (MonoidAlgebra.single g (1 : k) •
            finite_free_source_picker (k := k) (G := G) n
              (MonoidAlgebra.single g⁻¹ (1 : k) • y)) := by
          simpa [MonoidAlgebra.one_def, smul_smul, MonoidAlgebra.single_mul_single] using
            (one_smul k[G]
              (((ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv h)
                (MonoidAlgebra.single g (1 : k) •
                  finite_free_source_picker (k := k) (G := G) n
                    (MonoidAlgebra.single g⁻¹ (1 : k) • y))))

/-- Helper for Exercise 14-14.5-3: the translated textbook average of the finite-free picker
precomposition endomorphism is the identity on the exact internal-Hom owner. -/
lemma linHom_precompose_picker_end_textbook_average
    [Fintype G]
    (n : ℕ)
    (h :
      (Representation.linHom
        (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
        (Representation.ofModule (k := k) (G := G) F)).asModule) :
    ∑ g : G,
      MonoidAlgebra.single g (1 : k) •
        linHom_precompose_picker_end (k := k) (G := G) (F := F) n
          (MonoidAlgebra.single g⁻¹ (1 : k) • h) = h := by
  -- Route correction: prove equality on the frozen owner by applying `asModuleEquiv` and
  -- reducing every averaged summand to the already established source-side textbook average.
  apply (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv.injective
  ext y
  calc
    (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv
        (∑ g : G,
          MonoidAlgebra.single g (1 : k) •
            linHom_precompose_picker_end (k := k) (G := G) (F := F) n
              (MonoidAlgebra.single g⁻¹ (1 : k) • h)) y
      = ∑ g : G,
          (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv
            (MonoidAlgebra.single g (1 : k) •
              linHom_precompose_picker_end (k := k) (G := G) (F := F) n
                (MonoidAlgebra.single g⁻¹ (1 : k) • h)) y := by
          simpa using
            congrArg
              (fun z :
                RestrictScalars k k[G] (Fin n → k[G]) →ₗ[k]
                  RestrictScalars k k[G] F ↦ z y)
              ((ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv.map_sum
                (fun g : G ↦
                  MonoidAlgebra.single g (1 : k) •
                    linHom_precompose_picker_end (k := k) (G := G) (F := F) n
                      (MonoidAlgebra.single g⁻¹ (1 : k) • h)))
    _ = ∑ g : G,
          (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv h
            (MonoidAlgebra.single g (1 : k) •
              finite_free_source_picker (k := k) (G := G) n
                (MonoidAlgebra.single g⁻¹ (1 : k) • y)) := by
          refine Finset.sum_congr rfl ?_
          intro g _
          exact linHom_precompose_picker_average_summand_apply
            (k := k) (G := G) (F := F) (n := n) (g := g) (h := h) (y := y)
    _ = ((ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv h)
          (∑ g : G,
            MonoidAlgebra.single g (1 : k) •
              finite_free_source_picker (k := k) (G := G) n
                (MonoidAlgebra.single g⁻¹ (1 : k) • y)) := by
          symm
          simpa using
            (((ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv h).map_sum
              (fun g : G ↦
                MonoidAlgebra.single g (1 : k) •
                  finite_free_source_picker (k := k) (G := G) n
                    (MonoidAlgebra.single g⁻¹ (1 : k) • y)))
    _ = (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv h y := by
          simpa using
            congrArg
              ((ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv h)
              (finite_free_source_picker_textbook_average (k := k) (G := G) (n := n) (y := y))

/-- Helper for Exercise 14-14.5-3: after transporting the textbook average of
`linHom_precompose_picker_end` through `asModuleEquiv` and evaluating at a source vector, the
result is unchanged. -/
lemma linHom_precompose_picker_end_textbook_average_eval
    [Fintype G]
    (n : ℕ)
    (h :
      (Representation.linHom
        (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
        (Representation.ofModule (k := k) (G := G) F)).asModule)
    (y : Fin n → k[G]) :
    (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv
        (∑ g : G,
          MonoidAlgebra.single g (1 : k) •
            linHom_precompose_picker_end (k := k) (G := G) (F := F) n
              (MonoidAlgebra.single g⁻¹ (1 : k) • h)) y =
      (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv h y := by
  -- This is the established textbook average, read through the owner equivalence and evaluated at
  -- a single source vector.
  exact
    congrArg
      (fun z :
        (Representation.linHom
          (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
          (Representation.ofModule (k := k) (G := G) F)).asModule ↦
        (ofModule_linHom_rep (k := k) (G := G) (Fin n → k[G]) F).asModuleEquiv z y)
      (linHom_precompose_picker_end_textbook_average
        (k := k) (G := G) (F := F) (n := n) h)

/-- Helper for Exercise 14-14.5-3: the frozen finite-free internal-Hom owner is already
projective over the base field `k`. -/
theorem finite_free_internal_hom_owner_projective_over_k
    [FiniteDimensional k F]
    (n : ℕ) :
    Module.Projective k (finite_free_internal_hom_owner (k := k) (G := G) (F := F) n) := by
  -- This simply records the existing base-field projectivity result on the frozen owner alias so
  -- later Maschke packaging can target a stable carrier.
  simpa [finite_free_internal_hom_owner] using
    internal_hom_owner_projective_over_k (k := k) (G := G) (F := F) n

/-- Helper for Exercise 14-14.5-3: the frozen owner alias is definitionally the exact internal-Hom
owner with finite free source. -/
@[simp] lemma finite_free_internal_hom_owner_rfl
    (n : ℕ) :
    finite_free_internal_hom_owner (k := k) (G := G) (F := F) n =
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
        (Representation.ofModule (k := k) (G := G) F)).asModule) := by
  rfl

/-- Helper for Exercise 14-14.5-3: the exact internal-Hom owner with finite free source is already
projective over the base field `k`. -/
theorem finite_free_internal_hom_owner_projective_over_k_exact
    [FiniteDimensional k F]
    (n : ℕ) :
    Module.Projective k
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) (Fin n → k[G]))
        (Representation.ofModule (k := k) (G := G) F)).asModule) := by
  -- This freezes the exact owner type used in the Maschke step without reopening the alias.
  simpa [finite_free_internal_hom_owner] using
    finite_free_internal_hom_owner_projective_over_k (k := k) (G := G) (F := F) n

end
