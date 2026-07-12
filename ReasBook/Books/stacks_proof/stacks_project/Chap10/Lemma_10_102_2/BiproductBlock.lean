import StacksProject_2024.Chap10.Lemma_10_102_2.Basic

open CategoryTheory CategoryTheory.Limits ChainComplex Matrix

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

namespace FiniteFreeComplex

variable {e : ℕ}
/-- Helper for Lemma 10.102.2: once the normalized middle differential has zero off-diagonal
components and identity on the distinguished rank-one summand, it is exactly the biproduct map
of its tail component and the identity. -/
theorem eq_biprod_map_tail_identity_of_components
    {X₁ Y₁ Y₂ : ModuleCat R}
    (F : biprod X₁ Y₂ ⟶ biprod Y₁ Y₂)
    (h_inl_snd : biprod.inl ≫ F ≫ biprod.snd = 0)
    (h_inr_fst : biprod.inr ≫ F ≫ biprod.fst = 0)
    (h_inr_snd : biprod.inr ≫ F ≫ biprod.snd = 𝟙 Y₂) :
    F = biprod.map (biprod.inl ≫ F ≫ biprod.fst) (𝟙 Y₂) := by
  -- Compare the two maps on the two source summands separately.
  refine biprod.hom_ext' F (biprod.map (biprod.inl ≫ F ≫ biprod.fst) (𝟙 Y₂)) ?_ ?_
  · -- On the tail summand, the first component is tautological and the second vanishes.
    refine biprod.hom_ext _ _ ?_ ?_
    · simp
    · simpa [Category.assoc] using h_inl_snd
  · -- On the distinguished head summand, the tail component vanishes and the head is the identity.
    refine biprod.hom_ext _ _ ?_ ?_
    · simpa [Category.assoc] using h_inr_fst
    · simpa [Category.assoc] using h_inr_snd

/-- Helper for Lemma 10.102.2: the explicit `ModuleCat` product comparison sends the binary
biproduct to the usual first projection. -/
theorem biprodIsoProd_hom_comp_fst (M N : ModuleCat R) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.fst R M N) = biprod.fst := by
  -- This is the left component equation of the limit-point uniqueness isomorphism.
  simpa [ModuleCat.binaryProductLimitCone_cone_π_app_left] using
    IsLimit.conePointUniqueUpToIso_hom_comp
      (BinaryBiproduct.isLimit M N) (ModuleCat.binaryProductLimitCone M N).isLimit
      (Discrete.mk WalkingPair.left)

/-- Helper for Lemma 10.102.2: the explicit `ModuleCat` product comparison sends the binary
biproduct to the usual second projection. -/
theorem biprodIsoProd_hom_comp_snd (M N : ModuleCat R) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.snd R M N) = biprod.snd := by
  -- This is the right component equation of the same uniqueness isomorphism.
  simpa [ModuleCat.binaryProductLimitCone_cone_π_app_right] using
    IsLimit.conePointUniqueUpToIso_hom_comp
      (BinaryBiproduct.isLimit M N) (ModuleCat.binaryProductLimitCone M N).isLimit
      (Discrete.mk WalkingPair.right)

/-- Helper for Lemma 10.102.2: under the explicit product model of a biproduct, the left summand
is the usual product inclusion into the first factor. -/
theorem biprodIsoProd_inl_hom (M N : ModuleCat R) :
    biprod.inl ≫ (ModuleCat.biprodIsoProd M N).hom =
      ModuleCat.ofHom (LinearMap.inl R M N) := by
  -- Compare the two maps after applying the explicit first and second projections.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change ((biprod.inl ≫ (ModuleCat.biprodIsoProd M N).hom ≫
        ModuleCat.ofHom (LinearMap.fst R M N)).hom x) = x
    simp [biprodIsoProd_hom_comp_fst]
  · change ((biprod.inl ≫ (ModuleCat.biprodIsoProd M N).hom ≫
        ModuleCat.ofHom (LinearMap.snd R M N)).hom x) = 0
    simp [biprodIsoProd_hom_comp_snd]

/-- Helper for Lemma 10.102.2: under the explicit product model of a biproduct, the right summand
is the usual product inclusion into the second factor. -/
theorem biprodIsoProd_inr_hom (M N : ModuleCat R) :
    biprod.inr ≫ (ModuleCat.biprodIsoProd M N).hom =
      ModuleCat.ofHom (LinearMap.inr R M N) := by
  -- Again compare on the two explicit product projections.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  apply Prod.ext
  · change ((biprod.inr ≫ (ModuleCat.biprodIsoProd M N).hom ≫
        ModuleCat.ofHom (LinearMap.fst R M N)).hom y) = 0
    simp [biprodIsoProd_hom_comp_fst]
  · change ((biprod.inr ≫ (ModuleCat.biprodIsoProd M N).hom ≫
        ModuleCat.ofHom (LinearMap.snd R M N)).hom y) = y
    simp [biprodIsoProd_hom_comp_snd]

/-- Helper for Lemma 10.102.2: the explicit product comparison sends an element of the left
biproduct summand to the corresponding pair with zero second component. -/
theorem biprodIsoProd_hom_inl_apply (M N : ModuleCat R) (x : M) :
    ((ModuleCat.biprodIsoProd M N).hom.hom) ((biprod.inl : M ⟶ biprod M N).hom x) = (x, 0) := by
  -- Evaluate the morphism-level identification of `biprod.inl` with the usual product inclusion.
  simpa using congrArg (fun g : M ⟶ ModuleCat.of R (M × N) => g.hom x) (biprodIsoProd_inl_hom
    (R := R) M N)

/-- Helper for Lemma 10.102.2: the explicit product comparison sends an element of the right
biproduct summand to the corresponding pair with zero first component. -/
theorem biprodIsoProd_hom_inr_apply (M N : ModuleCat R) (y : N) :
    ((ModuleCat.biprodIsoProd M N).hom.hom) ((biprod.inr : N ⟶ biprod M N).hom y) = (0, y) := by
  -- This is the pointwise form of the right-summand/product-inclusion compatibility.
  simpa using congrArg (fun g : N ⟶ ModuleCat.of R (M × N) => g.hom y) (biprodIsoProd_inr_hom
    (R := R) M N)

/-- Helper for Lemma 10.102.2: the inverse of the head-tail biproduct splitting sends an element
of the left summand to the explicit tail-plus-zero vector. -/
theorem splitOffUnitModuleIso_inv_inl_apply
    (ns : ℕ) (x : Fin ns → R) :
    ((splitOffUnitModuleIso (R := R) ns).inv.hom)
        ((biprod.inl :
          ModuleCat.of R (Fin ns → R) ⟶
            biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))).hom x) =
      (splitOffUnitLinearEquiv (R := R) ns).symm (x, 0) := by
  -- Unfold the composite isomorphism once so the explicit product comparison can be evaluated.
  change
    ((splitOffUnitLinearEquiv (R := R) ns).symm.toLinearMap)
      (((ModuleCat.biprodIsoProd
          (ModuleCat.of R (Fin ns → R))
          (ModuleCat.of R (Fin 1 → R))).hom.hom)
        ((biprod.inl :
          ModuleCat.of R (Fin ns → R) ⟶
            biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))).hom x)) =
      (splitOffUnitLinearEquiv (R := R) ns).symm (x, 0)
  -- The left summand becomes the pair `(x, 0)` in the explicit product model.
  rw [biprodIsoProd_hom_inl_apply]
  rfl

/-- Helper for Lemma 10.102.2: the inverse of the head-tail biproduct splitting sends an element
of the right summand to the explicit zero-plus-head vector. -/
theorem splitOffUnitModuleIso_inv_inr_apply
    (ns : ℕ) (y : Fin 1 → R) :
    ((splitOffUnitModuleIso (R := R) ns).inv.hom)
        ((biprod.inr :
          ModuleCat.of R (Fin 1 → R) ⟶
            biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))).hom y) =
      (splitOffUnitLinearEquiv (R := R) ns).symm (0, y) := by
  -- Unfold the same composite isomorphism and evaluate the right summand in the product model.
  change
    ((splitOffUnitLinearEquiv (R := R) ns).symm.toLinearMap)
      (((ModuleCat.biprodIsoProd
          (ModuleCat.of R (Fin ns → R))
          (ModuleCat.of R (Fin 1 → R))).hom.hom)
        ((biprod.inr :
          ModuleCat.of R (Fin 1 → R) ⟶
            biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))).hom y)) =
      (splitOffUnitLinearEquiv (R := R) ns).symm (0, y)
  -- The right summand becomes the pair `(0, y)`.
  rw [biprodIsoProd_hom_inr_apply]
  rfl

/-- Helper for Lemma 10.102.2: the inverse explicit product comparison identifies the first
projection from the biproduct with the ordinary product projection. -/
theorem biprodIsoProd_inv_comp_fst (M N : ModuleCat R) :
    (ModuleCat.biprodIsoProd M N).inv ≫ biprod.fst =
      ModuleCat.ofHom (LinearMap.fst R M N) := by
  -- Compose the known formula for the forward comparison with the inverse isomorphism on the left.
  simpa [Category.assoc] using
    congrArg (fun k ↦ (ModuleCat.biprodIsoProd M N).inv ≫ k)
      (biprodIsoProd_hom_comp_fst (R := R) M N)

/-- Helper for Lemma 10.102.2: the inverse explicit product comparison identifies the second
projection from the biproduct with the ordinary product projection. -/
theorem biprodIsoProd_inv_comp_snd (M N : ModuleCat R) :
    (ModuleCat.biprodIsoProd M N).inv ≫ biprod.snd =
      ModuleCat.ofHom (LinearMap.snd R M N) := by
  -- This is the same calculation for the second product projection.
  simpa [Category.assoc] using
    congrArg (fun k ↦ (ModuleCat.biprodIsoProd M N).inv ≫ k)
      (biprodIsoProd_hom_comp_snd (R := R) M N)

/-- Helper for Lemma 10.102.2: composing the head-tail biproduct splitting with the tail
projection just reads off the tail coordinates of the linear equivalence. -/
theorem splitOffUnitModuleIso_hom_comp_fst (n : ℕ) :
    (splitOffUnitModuleIso (R := R) n).hom ≫ biprod.fst =
      ModuleCat.ofHom
        ((LinearMap.fst R (Fin n → R) (Fin 1 → R)).comp
          (splitOffUnitLinearEquiv (R := R) n).toLinearMap) := by
  -- Unfold the composite isomorphism and rewrite the biproduct projection via the explicit
  -- product model.
  change
    ((splitOffUnitLinearEquiv (R := R) n).toModuleIso.hom ≫
        (ModuleCat.biprodIsoProd
          (ModuleCat.of R (Fin n → R))
          (ModuleCat.of R (Fin 1 → R))).inv) ≫ biprod.fst =
      _
  rw [Category.assoc, biprodIsoProd_inv_comp_fst (R := R)]
  rfl

/-- Helper for Lemma 10.102.2: composing the head-tail biproduct splitting with the head
projection just reads off the distinguished head coordinate of the linear equivalence. -/
theorem splitOffUnitModuleIso_hom_comp_snd (n : ℕ) :
    (splitOffUnitModuleIso (R := R) n).hom ≫ biprod.snd =
      ModuleCat.ofHom
        ((LinearMap.snd R (Fin n → R) (Fin 1 → R)).comp
          (splitOffUnitLinearEquiv (R := R) n).toLinearMap) := by
  -- The second projection is handled by the same explicit-product comparison.
  change
    ((splitOffUnitLinearEquiv (R := R) n).toModuleIso.hom ≫
        (ModuleCat.biprodIsoProd
          (ModuleCat.of R (Fin n → R))
          (ModuleCat.of R (Fin 1 → R))).inv) ≫ biprod.snd =
      _
  rw [Category.assoc, biprodIsoProd_inv_comp_snd (R := R)]
  rfl

/-- Helper for Lemma 10.102.2: after splitting off the distinguished head coordinates on source
and target, the normalized middle differential is already block diagonal with identity on the
rank-one head summand. -/
theorem normalized_middle_diff_is_biprod_map_tail_identity
    {ns nt : ℕ}
    (f : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (hhead : f (Pi.single 0 (1 : R)) = Pi.single 0 1)
    (htail : ∀ j : Fin ns, (f (Pi.single j.succ (1 : R))) 0 = 0) :
    let F :
      biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)) ⟶
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)) :=
      (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
        (splitOffUnitModuleIso (R := R) nt).hom
    F = biprod.map (biprod.inl ≫ F ≫ biprod.fst) (𝟙 _) := by
  let F :
      biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)) ⟶
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)) :=
    (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
      (splitOffUnitModuleIso (R := R) nt).hom
  -- Compare the normalized map on the left and right summands separately.
  have h_inl_snd : biprod.inl ≫ F ≫ biprod.snd = 0 := by
    -- On the left summand, the source-side adapter reduces to a tail-plus-zero vector, so the
    -- head output vanishes by the normalized basis formula with `y = 0`.
    have hsnd :
        biprod.inl ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            (splitOffUnitModuleIso (R := R) nt).hom ≫ biprod.snd =
          biprod.inl ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            ModuleCat.ofHom
              ((LinearMap.snd R (Fin nt → R) (Fin 1 → R)).comp
                (splitOffUnitLinearEquiv (R := R) nt).toLinearMap) := by
      -- Rewrite the target head projection through the explicit product model of the biproduct.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            biprod.inl ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫ k)
          (splitOffUnitModuleIso_hom_comp_snd (R := R) nt)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    ext j
    fin_cases j
    change
      ((biprod.inl ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            (splitOffUnitModuleIso (R := R) nt).hom ≫ biprod.snd).hom x) 0 = 0
    rw [hsnd]
    change
      (((LinearMap.snd R (Fin nt → R) (Fin 1 → R)).comp
            (splitOffUnitLinearEquiv (R := R) nt).toLinearMap)
          (f (((splitOffUnitModuleIso (R := R) ns).inv.hom)
            (((biprod.inl :
              ModuleCat.of R (Fin ns → R) ⟶
                biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))).hom x)))) ) 0 = 0
    rw [splitOffUnitModuleIso_inv_inl_apply (R := R) (ns := ns) (x := x)]
    simpa [LinearMap.comp_apply] using
      congrArg (fun g : Fin 1 → R => g 0)
        (split_off_unit_linear_equiv_apply_head_of_normalized_map
          (R := R) f hhead htail x 0)
  have h_inr_fst : biprod.inr ≫ F ≫ biprod.fst = 0 := by
    -- On the right summand, the source-side adapter is the pure head vector; after applying `f`
    -- and the head normalization, the codomain tail factor is therefore zero.
    have hfst :
        biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            (splitOffUnitModuleIso (R := R) nt).hom ≫ biprod.fst =
          biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            ModuleCat.ofHom
              ((LinearMap.fst R (Fin nt → R) (Fin 1 → R)).comp
                (splitOffUnitLinearEquiv (R := R) nt).toLinearMap) := by
      -- Rewrite the target tail projection through the same explicit product comparison.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫ k)
          (splitOffUnitModuleIso_hom_comp_fst (R := R) nt)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    ext k
    change
      ((biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            (splitOffUnitModuleIso (R := R) nt).hom ≫ biprod.fst).hom y) k = 0
    rw [hfst]
    change
      (((LinearMap.fst R (Fin nt → R) (Fin 1 → R)).comp
            (splitOffUnitLinearEquiv (R := R) nt).toLinearMap)
          (f (((splitOffUnitModuleIso (R := R) ns).inv.hom)
            (((biprod.inr :
              ModuleCat.of R (Fin 1 → R) ⟶
                biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))).hom y)))) ) k = 0
    rw [splitOffUnitModuleIso_inv_inr_apply (R := R) (ns := ns) (y := y)]
    have hsource :
        (splitOffUnitLinearEquiv (R := R) ns).symm (0, y) = Pi.single 0 (y 0) := by
      -- With zero tail coordinates, the inverse splitting is the pure head basis vector.
      rw [split_off_unit_linear_equiv_symm_eq_head_tail_sum (R := R) ns 0 y]
      simp
    have hsource_smul :
        (Pi.single 0 (y 0) : Fin (ns + 1) → R) = (y 0) • (Pi.single 0 (1 : R) : Fin (ns + 1) → R) := by
      ext j
      by_cases hj : j = 0
      · subst hj
        simp
      · simp [Pi.single_eq_of_ne hj]
    rw [hsource, hsource_smul, map_smul, hhead]
    simp [splitOffUnitLinearEquiv_apply_tail]
  have h_inr_snd : biprod.inr ≫ F ≫ biprod.snd = 𝟙 _ := by
    -- The same pure-head input keeps the rank-one summand unchanged under the normalized map.
    have hsnd :
        biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            (splitOffUnitModuleIso (R := R) nt).hom ≫ biprod.snd =
          biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            ModuleCat.ofHom
              ((LinearMap.snd R (Fin nt → R) (Fin 1 → R)).comp
                (splitOffUnitLinearEquiv (R := R) nt).toLinearMap) := by
      -- Again rewrite the target head projection through the explicit product comparison.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫ k)
          (splitOffUnitModuleIso_hom_comp_snd (R := R) nt)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    ext j
    fin_cases j
    change
      ((biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            (splitOffUnitModuleIso (R := R) nt).hom ≫ biprod.snd).hom y) 0 = y 0
    rw [hsnd]
    change
      (((LinearMap.snd R (Fin nt → R) (Fin 1 → R)).comp
            (splitOffUnitLinearEquiv (R := R) nt).toLinearMap)
          (f (((splitOffUnitModuleIso (R := R) ns).inv.hom)
            (((biprod.inr :
              ModuleCat.of R (Fin 1 → R) ⟶
                biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))).hom y)))) ) 0 = y 0
    rw [splitOffUnitModuleIso_inv_inr_apply (R := R) (ns := ns) (y := y)]
    simpa [LinearMap.comp_apply] using
      congrArg (fun g : Fin 1 → R => g 0)
        (split_off_unit_linear_equiv_apply_head_of_normalized_map
          (R := R) f hhead htail 0 y)
  -- Those three component computations are exactly the hypotheses of the abstract biproduct
  -- packaging lemma.
  exact eq_biprod_map_tail_identity_of_components (R := R) F h_inl_snd h_inr_fst h_inr_snd

/-- Helper for Lemma 10.102.2: once the middle differential is block diagonal in the head-tail
coordinates, the upper adjacent differential lands in the source tail summand. -/
theorem upper_adjacent_diff_factors_through_tail_of_split_middle
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R))
    (hmid :
      eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom =
        biprod.map tailDiff (𝟙 _)) :
    D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ (D.termIso i.succ).hom ≫ eSource.hom =
      (D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ (D.termIso i.succ).hom ≫ eSource.hom ≫
          biprod.fst) ≫
        biprod.inl := by
  let upper :=
    D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ (D.termIso i.succ).hom ≫ eSource.hom
  have hdiff :
      (D.termIso i.succ).hom ≫ ModuleCat.ofHom (D.diffAt i) =
        D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom := by
    -- Expand `diffAt` once and cancel the adjacent coordinate isomorphisms.
    change
      (D.termIso i.succ).hom ≫
          (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 ≫
            (D.termIso i.castSucc).hom =
        D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom
    simp [Category.assoc]
  have hmid_snd :
      eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.snd = biprod.snd := by
    -- The block-diagonal middle differential acts as the identity on the split head summand.
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ biprod.snd) hmid
  have hupper_snd : upper ≫ biprod.snd = 0 := by
    have hdd :
        D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ D.toChainComplex.d (i.1 + 1) i.1 ≫
            (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.snd =
          0 := by
      -- This is exactly `d ≫ d = 0`, postcomposed with the remaining coordinate maps.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ≫ (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.snd)
          (D.toChainComplex.d_comp_d (i.1 + 2) (i.1 + 1) i.1)
    have hupper_comp :
        D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ (D.termIso i.succ).hom ≫
            ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.snd =
          0 := by
      -- Rewrite the middle differential through `diffAt` before applying the previous `d ≫ d`.
      have hrewrite :
          D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ (D.termIso i.succ).hom ≫
              ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.snd =
            D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
              D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom ≫
                eTarget.hom ≫ biprod.snd := by
        simpa [Category.assoc] using congrArg
          (fun k ↦ D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ k ≫ eTarget.hom ≫ biprod.snd)
          hdiff
      exact hrewrite.trans hdd
    -- Reinsert the block-diagonal middle differential and then invoke `d ≫ d = 0`.
    calc
      upper ≫ biprod.snd =
          upper ≫ (eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.snd) := by
            rw [hmid_snd]
      _ = D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ (D.termIso i.succ).hom ≫
            ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.snd := by
            simp [upper, Category.assoc]
      _ = 0 := hupper_comp
  -- Once the second component vanishes, the incoming map factors through the tail summand.
  apply biprod.hom_ext
  · simp [upper, Category.assoc]
  · simpa [upper, Category.assoc] using hupper_snd

/-- Helper for Lemma 10.102.2: once the middle differential is block diagonal in the head-tail
coordinates, the lower adjacent differential annihilates the target head summand. -/
theorem lower_adjacent_diff_factors_through_tail_of_split_middle
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R))
    (hmid :
      eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom =
        biprod.map tailDiff (𝟙 _)) :
    eTarget.inv ≫ (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 (i.1 - 1) =
      biprod.fst ≫
        (biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
          D.toChainComplex.d i.1 (i.1 - 1)) := by
  let lower :=
    eTarget.inv ≫ (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 (i.1 - 1)
  have hdiff :
      ModuleCat.ofHom (D.diffAt i) ≫ (D.termIso i.castSucc).inv =
        (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 := by
    -- Expand `diffAt` once and cancel the target-side coordinate isomorphism.
    change
      (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 ≫
          (D.termIso i.castSucc).hom ≫ (D.termIso i.castSucc).inv =
        (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1
    simp [Category.assoc]
  have hmid_inr :
      (biprod.inr :
          ModuleCat.of R (Fin 1 → R) ⟶
            biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫
          eTarget.inv =
        biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) := by
    -- The split head basis vector on the target side comes from the split head basis vector on
    -- the source side because the head block of the middle differential is the identity.
    have hmid_inr_aux :
        biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) =
          (biprod.inr :
            ModuleCat.of R (Fin 1 → R) ⟶
              biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫
            eTarget.inv := by
      calc
      biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) =
          biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫
            eTarget.inv := by
            simp [Category.assoc]
      _ = biprod.inr ≫ biprod.map tailDiff (𝟙 _) ≫ eTarget.inv := by
            simpa [Category.assoc] using congrArg
              (fun k :
                biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)) ⟶
                  biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)) =>
                  (biprod.inr :
                    ModuleCat.of R (Fin 1 → R) ⟶
                      biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))) ≫
                    k ≫ eTarget.inv)
              hmid
      _ = (biprod.inr :
            ModuleCat.of R (Fin 1 → R) ⟶
              biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫
            eTarget.inv := by
            simp [Category.assoc]
    exact hmid_inr_aux.symm
  have hlower_inr :
      (biprod.inr :
          ModuleCat.of R (Fin 1 → R) ⟶
            biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫
          lower = 0 := by
    have hdd :
        biprod.inr ≫ eSource.inv ≫ (D.termIso i.succ).inv ≫
            D.toChainComplex.d (i.1 + 1) i.1 ≫ D.toChainComplex.d i.1 (i.1 - 1) =
          0 := by
      -- This is the same `d ≫ d = 0`, now precomposed with the split source-head injection.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            (biprod.inr :
              ModuleCat.of R (Fin 1 → R) ⟶
                biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))) ≫
              eSource.inv ≫ (D.termIso i.succ).inv ≫ k)
          (D.toChainComplex.d_comp_d (i.1 + 1) i.1 (i.1 - 1))
    have hlower_comp :
        biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫
            (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 (i.1 - 1) =
          0 := by
      -- Rewrite the middle differential through `diffAt` before invoking the precomposed
      -- `d ≫ d = 0` identity.
      have hrewrite :
          biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫
              (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 (i.1 - 1) =
            biprod.inr ≫ eSource.inv ≫ (D.termIso i.succ).inv ≫
              D.toChainComplex.d (i.1 + 1) i.1 ≫ D.toChainComplex.d i.1 (i.1 - 1) := by
        simpa [Category.assoc] using congrArg
          (fun k ↦ biprod.inr ≫ eSource.inv ≫ k ≫ D.toChainComplex.d i.1 (i.1 - 1))
          hdiff
      exact hrewrite.trans hdd
    -- After rewriting the target head injection through the middle differential, `d ≫ d = 0`
    -- kills the resulting composite.
    calc
      (biprod.inr :
          ModuleCat.of R (Fin 1 → R) ⟶
            biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫
          lower =
          biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫
            (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 (i.1 - 1) := by
            change
              ((biprod.inr :
                  ModuleCat.of R (Fin 1 → R) ⟶
                    biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫
                  eTarget.inv) ≫ (D.termIso i.castSucc).inv ≫
                D.toChainComplex.d i.1 (i.1 - 1) =
              (biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i)) ≫
                (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 (i.1 - 1)
            rw [hmid_inr]
      _ = 0 := hlower_comp
  -- Vanishing on the source-side head summand is equivalent to factoring through `biprod.fst`.
  apply biprod.hom_ext'
  · simp [lower, Category.assoc]
  · simpa [lower, Category.assoc] using hlower_inr

/-- Helper for Lemma 10.102.2: the lower adjacent factorization may be used at any index
`j` whose successor is the split target degree. -/
theorem lower_adjacent_diff_factors_through_tail_of_split_middle_of_eq
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R))
    (hmid :
      eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom =
        biprod.map tailDiff (𝟙 _))
    {j : ℕ}
    (hLower : j + 1 = i.1) :
    eTarget.inv ≫ (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 j =
      biprod.fst ≫
        (biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
          D.toChainComplex.d i.1 j) := by
  -- Convert the arbitrary lower index to the canonical predecessor used by the owner theorem.
  have hj : j = i.1 - 1 := by
    omega
  subst j
  -- The canonical lower factorization now applies without exposing any extra transport.
  exact lower_adjacent_diff_factors_through_tail_of_split_middle
    (R := R) (D := D) (i := i) (eSource := eSource) (eTarget := eTarget)
    (tailDiff := tailDiff) hmid

/-- Helper for Lemma 10.102.2: after projecting to the target tail summand and reincluding it,
the lower adjacent differential is unchanged. -/
theorem lower_adjacent_tail_projection_comp_eq
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R))
    (hmid :
      eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom =
        biprod.map tailDiff (𝟙 _))
    {j : ℕ}
    (hLower : j + 1 = i.1) :
    (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.fst ≫ biprod.inl ≫
        eTarget.inv ≫ (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 j =
      D.toChainComplex.d i.1 j := by
  -- Precompose the lower factorization with the inverse coordinate change, which cancels the
  -- target split and leaves the original lower adjacent map.
  have hfac :=
    lower_adjacent_diff_factors_through_tail_of_split_middle_of_eq
      (R := R) (D := D) (i := i) (eSource := eSource) (eTarget := eTarget)
      (tailDiff := tailDiff) hmid hLower
  simpa [Category.assoc] using
    (congrArg (fun m ↦ (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ m) hfac).symm

/-- Helper for Lemma 10.102.2: once the middle differential is block diagonal in the head-tail
coordinates, the upper adjacent differential lands in the source tail summand and the lower
adjacent differential annihilates the target head summand. -/
theorem adjacent_maps_respect_tail_split_of_normalized_middle
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R))
    (hmid :
      eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom =
        biprod.map tailDiff (𝟙 _)) :
    D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.snd =
        0 ∧
      (biprod.inr :
          ModuleCat.of R (Fin 1 → R) ⟶
            biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫
          eTarget.inv ≫ (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 (i.1 - 1) =
        0 := by
  constructor
  · -- The upper factorization lemma packages the first vanishing component directly.
    have hupper :=
      upper_adjacent_diff_factors_through_tail_of_split_middle
        (R := R) (D := D) (i := i) (eSource := eSource) (eTarget := eTarget)
        (tailDiff := tailDiff) hmid
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ biprod.snd) hupper
  · -- The lower factorization lemma packages the second vanishing component directly.
    have hlower :=
      lower_adjacent_diff_factors_through_tail_of_split_middle
        (R := R) (D := D) (i := i) (eSource := eSource) (eTarget := eTarget)
        (tailDiff := tailDiff) hmid
    simpa [Category.assoc] using congrArg
      (fun k ↦
        (biprod.inr :
          ModuleCat.of R (Fin 1 → R) ⟶
            biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫ k)
      hlower


end FiniteFreeComplex

end
