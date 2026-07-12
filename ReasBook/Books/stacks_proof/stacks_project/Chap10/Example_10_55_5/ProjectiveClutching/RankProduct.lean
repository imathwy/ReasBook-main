import StacksProject_2024.Chap10.Example_10_55_5.ProjectiveClutching.AbstractRankProduct

noncomputable section

universe u v w

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Chap10 Example 10 55 5: the free rank-one finite-projective module over the
equal-endpoint ring. -/
abbrev equalEndpointProjectiveFreeModule : FiniteProjectiveModuleCat.{u, u} R :=
  ⟨ModuleCat.of R R, ⟨inferInstance, inferInstance⟩⟩

/-- Helper for Chap10 Example 10 55 5: the `K₀` class of the free rank-one projective module. -/
abbrev equalEndpointProjectiveFreeClass : projectiveGrothendieckGroup.{u, u} R :=
  projectiveGrothendieckGroupOf.{u, u} R (equalEndpointProjectiveFreeModule k)

/-- Helper for Chap10 Example 10 55 5: the free rank-one projective class has generic rank one. -/
theorem equalEndpointProjectiveRankMap_freeClass :
    equalEndpointProjectiveRankMap.{u, u} k (equalEndpointProjectiveFreeClass k) = 1 := by
  -- The class evaluates by the generator formula, and the fraction-field base change of `R`
  -- itself is one-dimensional over the fraction field.
  rw [equalEndpointProjectiveFreeClass, equalEndpointProjectiveRankMap_apply_of]
  simp [equalEndpointProjectiveRank, equalEndpointProjectiveFreeModule, Module.finrank_self]

/-- Helper for Chap10 Example 10 55 5: the direct product of two finite-projective modules over
the equal-endpoint ring, packaged in the finite-projective subcategory. -/
abbrev equalEndpointProjectiveProductModule
    (M N : FiniteProjectiveModuleCat.{u, u} R) : FiniteProjectiveModuleCat.{u, u} R :=
  ⟨ModuleCat.of R (M.obj × N.obj), ⟨inferInstance, inferInstance⟩⟩

/-- Helper for Chap10 Example 10 55 5: the `K₀` class of a direct product of finite-projective
modules is the sum of the classes of the two factors. -/
theorem equalEndpointProjectiveClass_prod
    (M N : FiniteProjectiveModuleCat.{u, u} R) :
    projectiveGrothendieckGroupOf R (equalEndpointProjectiveProductModule k M N) =
      projectiveGrothendieckGroupOf R M + projectiveGrothendieckGroupOf R N := by
  let P := finiteProjectiveModuleProperty R
  let S : CategoryTheory.ShortComplex P.FullSubcategory :=
    { X₁ := M
      X₂ := equalEndpointProjectiveProductModule k M N
      X₃ := N
      f := CategoryTheory.ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.inl R M.obj N.obj))
      g := CategoryTheory.ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.snd R M.obj N.obj))
      zero := by
        -- The projection kills the left inclusion in the split product sequence.
        apply CategoryTheory.ObjectProperty.hom_ext
        ext x
        rfl }
  let T : CategoryTheory.ShortComplex (ModuleCat R) :=
    { X₁ := M.obj
      X₂ := ModuleCat.of R (M.obj × N.obj)
      X₃ := N.obj
      f := ModuleCat.ofHom (LinearMap.inl R M.obj N.obj)
      g := ModuleCat.ofHom (LinearMap.snd R M.obj N.obj)
      zero := by
        -- The same zero-composite calculation after forgetting to `ModuleCat`.
        ext x
        rfl }
  have hT : T.ShortExact := by
    -- The product sequence is split exact: the kernel of the second projection is the image of
    -- the first inclusion, and the projection has the evident section.
    refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
    · intro x
      constructor
      · intro hx
        refine ⟨x.1, ?_⟩
        ext
        · rfl
        · simpa using hx.symm
      · rintro ⟨m, rfl⟩
        rfl
    · intro m m' hmm'
      exact congrArg Prod.fst hmm'
    · intro n
      refine ⟨(0, n), ?_⟩
      rfl
  have hS : (S.map P.ι).ShortExact := by
    -- Forgetting the finite-projective full-subcategory structure recovers the split exact
    -- product row in `ModuleCat`.
    simpa [S, T, equalEndpointProjectiveProductModule] using hT
  -- Apply the defining short-exact relation in projective `K₀`.
  simpa [S, equalEndpointProjectiveProductModule] using
    ModulePropertyK0.of_shortExact R S hS

/-- Helper for Chap10 Example 10 55 5: an isomorphism between product packages transports the
split product formula in projective `K₀`. -/
theorem equalEndpointProjectiveClass_prod_eq_of_iso
    {M₁ N₁ M₂ N₂ : FiniteProjectiveModuleCat.{u, u} R}
    (e :
      equalEndpointProjectiveProductModule k M₁ N₁ ≅
        equalEndpointProjectiveProductModule k M₂ N₂) :
    projectiveGrothendieckGroupOf R M₁ + projectiveGrothendieckGroupOf R N₁ =
      projectiveGrothendieckGroupOf R M₂ + projectiveGrothendieckGroupOf R N₂ := by
  have h0 : finiteProjectiveModuleProperty R (ModuleCat.of R PUnit) := by
    -- The zero module supplies the base object required by projective `K₀` isomorphism
    -- invariance.
    exact ⟨inferInstance, inferInstance⟩
  have hprod :
      projectiveGrothendieckGroupOf R (equalEndpointProjectiveProductModule k M₁ N₁) =
        projectiveGrothendieckGroupOf R (equalEndpointProjectiveProductModule k M₂ N₂) := by
    -- Transport the product object class across the supplied finite-projective isomorphism.
    exact (@ModulePropertyK0.of_iso R _ (finiteProjectiveModuleProperty R) h0
      (equalEndpointProjectiveProductModule k M₁ N₁)
      (equalEndpointProjectiveProductModule k M₂ N₂)
      e)
  -- Rewrite both product object classes by the split product formula.
  calc
    projectiveGrothendieckGroupOf R M₁ + projectiveGrothendieckGroupOf R N₁ =
        projectiveGrothendieckGroupOf R (equalEndpointProjectiveProductModule k M₁ N₁) := by
      exact (equalEndpointProjectiveClass_prod (k := k) M₁ N₁).symm
    _ = projectiveGrothendieckGroupOf R (equalEndpointProjectiveProductModule k M₂ N₂) := hprod
    _ = projectiveGrothendieckGroupOf R M₂ + projectiveGrothendieckGroupOf R N₂ := by
      exact equalEndpointProjectiveClass_prod (k := k) M₂ N₂

/-- Helper for Chap10 Example 10 55 5: the free rank-one class gives an integer-rank section. -/
noncomputable def equalEndpointProjectiveRankSection :
    ℤ →+ projectiveGrothendieckGroup.{u, u} R :=
  zmultiplesHom _ (equalEndpointProjectiveFreeClass k)

/-- Helper for Chap10 Example 10 55 5: the projective rank section is concretely integer
multiplication by the free rank-one class. -/
theorem equalEndpointProjectiveRankSection_apply (n : ℤ) :
    equalEndpointProjectiveRankSection k n =
      n • equalEndpointProjectiveFreeClass k := by
  -- Unfold the `ℤ`-generated homomorphism once so later proofs can rewrite through a named
  -- normal form instead of reopening the section definition.
  rfl

/-- Helper for Chap10 Example 10 55 5: the integer-rank section is right-inverse to projective
generic rank. -/
theorem equalEndpointProjectiveRankSection_comp :
    (equalEndpointProjectiveRankMap.{u, u} k).comp (equalEndpointProjectiveRankSection k) =
      AddMonoidHom.id ℤ := by
  -- A homomorphism out of `ℤ` is determined by `1`, where the free rank-one class has rank `1`.
  apply AddMonoidHom.ext_int
  rw [AddMonoidHom.comp_apply]
  change equalEndpointProjectiveRankMap.{u, u} k (equalEndpointProjectiveFreeClass k) = 1
  exact equalEndpointProjectiveRankMap_freeClass k

/-- Helper for Chap10 Example 10 55 5: applying generic projective rank to the free-class section
recovers the input integer. -/
theorem equalEndpointProjectiveRankSection_rank (n : ℤ) :
    equalEndpointProjectiveRankMap.{u, u} k (equalEndpointProjectiveRankSection k n) = n := by
  -- Evaluate the already-proved right-inverse identity at the chosen integer.
  simpa [AddMonoidHom.comp_apply] using
    DFunLike.congr_fun (equalEndpointProjectiveRankSection_comp k) n

/-- Helper for Chap10 Example 10 55 5: once the rank kernel is identified with line classes, the
split rank section assembles the product decomposition. -/
theorem equalEndpointProjectiveRankProduct_exists_of_kernel_equiv
    (hkernel : Additive kˣ ≃+ (equalEndpointProjectiveRankMap.{u, u} k).ker) :
    ∃ e : projectiveGrothendieckGroup.{u, u} R ≃+ Additive kˣ × ℤ,
      (AddMonoidHom.snd (Additive kˣ) ℤ).comp e.toAddMonoidHom =
        equalEndpointProjectiveRankMap.{u, u} k := by
  -- Apply the abstract split-kernel product decomposition to the generic-rank homomorphism.
  exact addEquivProductOfRankSplit
    (G := projectiveGrothendieckGroup.{u, u} R)
    (A := Additive kˣ)
    (r := equalEndpointProjectiveRankMap.{u, u} k)
    (s := equalEndpointProjectiveRankSection k)
    (equalEndpointProjectiveRankSection_comp k)
    hkernel

/-- Helper for Chap10 Example 10 55 5: the rank-kernel classification directly supplies the
explicit equal-endpoint class and coordinate maps. -/
theorem equalEndpointProjectiveRankProductData_exists_of_kernel_equiv
    (hkernel : Additive kˣ ≃+ (equalEndpointProjectiveRankMap.{u, u} k).ker) :
    ∃ (classMap : Additive kˣ × ℤ →+ projectiveGrothendieckGroup.{u, u} R)
      (coordMap : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ × ℤ),
      coordMap.comp classMap = AddMonoidHom.id (Additive kˣ × ℤ) ∧
        classMap.comp coordMap = AddMonoidHom.id (projectiveGrothendieckGroup.{u, u} R) ∧
        (equalEndpointProjectiveRankMap.{u, u} k).comp classMap =
          AddMonoidHom.snd (Additive kˣ) ℤ := by
  -- This is the specialized formal bridge from a Milnor rank-kernel equivalence to product data.
  exact rankProductDataOfRankKernelEquiv
    (r := equalEndpointProjectiveRankMap.{u, u} k)
    (s := equalEndpointProjectiveRankSection k)
    (equalEndpointProjectiveRankSection_comp k)
    hkernel

/-- Helper for Chap10 Example 10 55 5: explicit class and coordinate maps with two-sided inverse
identities and the expected rank on the class map assemble the projective product decomposition. -/
theorem equalEndpointProjectiveRankProduct_exists_of_productData
    (hmaps :
      ∃ (classMap : Additive kˣ × ℤ →+ projectiveGrothendieckGroup.{u, u} R)
        (coordMap : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ × ℤ),
        coordMap.comp classMap = AddMonoidHom.id (Additive kˣ × ℤ) ∧
          classMap.comp coordMap = AddMonoidHom.id (projectiveGrothendieckGroup.{u, u} R) ∧
          (equalEndpointProjectiveRankMap.{u, u} k).comp classMap =
            AddMonoidHom.snd (Additive kˣ) ℤ) :
    ∃ e : projectiveGrothendieckGroup.{u, u} R ≃+ Additive kˣ × ℤ,
      (AddMonoidHom.snd (Additive kˣ) ℤ).comp e.toAddMonoidHom =
        equalEndpointProjectiveRankMap.{u, u} k := by
  rcases hmaps with ⟨classMap, coordMap, hleft, hright, hrankClass⟩
  -- The product equivalence is now purely formal: the coordinate map is bijective and its
  -- second coordinate is transported from the class-map rank computation.
  exact addEquivRankProductOfTwoSidedInverseWithRankOnClassMap
    (r := equalEndpointProjectiveRankMap.{u, u} k)
    (classMap := classMap)
    (coordMap := coordMap)
    hleft hright hrankClass

/-- Helper for Chap10 Example 10 55 5: any equal-endpoint product decomposition yields the
explicit class and coordinate maps used by the determinant-rank route. -/
theorem equalEndpointProjectiveRankProductData_exists_of_product
    (hprod :
      ∃ e : projectiveGrothendieckGroup.{u, u} R ≃+ Additive kˣ × ℤ,
        (AddMonoidHom.snd (Additive kˣ) ℤ).comp e.toAddMonoidHom =
          equalEndpointProjectiveRankMap.{u, u} k) :
    ∃ (classMap : Additive kˣ × ℤ →+ projectiveGrothendieckGroup.{u, u} R)
      (coordMap : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ × ℤ),
      coordMap.comp classMap = AddMonoidHom.id (Additive kˣ × ℤ) ∧
        classMap.comp coordMap = AddMonoidHom.id (projectiveGrothendieckGroup.{u, u} R) ∧
        (equalEndpointProjectiveRankMap.{u, u} k).comp classMap =
          AddMonoidHom.snd (Additive kˣ) ℤ := by
  rcases hprod with ⟨e, he⟩
  -- This specializes the abstract product-data bridge to the equal-endpoint generic-rank map.
  exact rankProductDataOfAddEquiv
    (r := equalEndpointProjectiveRankMap.{u, u} k)
    (e := e)
    he


end
