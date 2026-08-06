import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap12.Definition_12_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap12.Definition_12_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap12.Definition_12_3_3

open CategoryTheory
open HomologicalComplex
open scoped MonoidalCategory

-- Semantic recall via `lean_leansearch`: the tensor-interval formulation uses the canonical
-- tensor-product API `X ⊗ Y`, `tensorHom`, and `rightUnitor`, while
-- `ChainComplex.fromSingle₀Equiv` packages the endpoint inclusions into `intervalChainComplex`.

noncomputable section

variable {X X' : ChainComplex (ModuleCat ℤ) ℕ}

/-- The endpoint inclusion `[0] : ℤ[0] ⟶ I`. -/
def intervalChainComplexPointZeroMap :
    (ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ) ⟶ intervalChainComplex :=
  (ChainComplex.fromSingle₀Equiv intervalChainComplex (ModuleCat.of ℤ ℤ)).symm
    (ModuleCat.ofHom ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).prod 0))

/-- `intervalChainComplexPointZeroMap` sends the degree-`0` generator of `ℤ[0]` to `[0]`. -/
@[simp]
theorem intervalChainComplexPointZeroMap_spec :
    (ChainComplex.fromSingle₀Equiv intervalChainComplex (ModuleCat.of ℤ ℤ))
        intervalChainComplexPointZeroMap =
      ModuleCat.ofHom ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).prod 0) := by
  simp [intervalChainComplexPointZeroMap]

/-- Helper for Lemma 12.3.4: the degree-`0` component of the left endpoint inclusion is the
linear map selecting `[0]`. -/
@[simp]
theorem intervalChainComplexPointZeroMap_f_zero :
    intervalChainComplexPointZeroMap.f 0 =
      ModuleCat.ofHom ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).prod 0) := by
  -- `fromSingle₀Equiv` identifies a map out of `ℤ[0]` with its degree-`0` component.
  simp [intervalChainComplexPointZeroMap]

/-- Helper for Lemma 12.3.4: the left endpoint inclusion has no positive-degree components. -/
@[simp]
theorem intervalChainComplexPointZeroMap_f_succ (n : ℕ) :
    intervalChainComplexPointZeroMap.f (n + 1) = 0 := by
  -- The source is concentrated in degree `0`, so every higher component vanishes.
  simp [intervalChainComplexPointZeroMap]

/-- The endpoint inclusion `[1] : ℤ[0] ⟶ I`. -/
def intervalChainComplexPointOneMap :
    (ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ) ⟶ intervalChainComplex :=
  (ChainComplex.fromSingle₀Equiv intervalChainComplex (ModuleCat.of ℤ ℤ)).symm
    (ModuleCat.ofHom (((0 : ℤ →ₗ[ℤ] ℤ).prod (LinearMap.id : ℤ →ₗ[ℤ] ℤ))))

/-- `intervalChainComplexPointOneMap` sends the degree-`0` generator of `ℤ[0]` to `[1]`. -/
@[simp]
theorem intervalChainComplexPointOneMap_spec :
    (ChainComplex.fromSingle₀Equiv intervalChainComplex (ModuleCat.of ℤ ℤ))
        intervalChainComplexPointOneMap =
      ModuleCat.ofHom (((0 : ℤ →ₗ[ℤ] ℤ).prod (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) := by
  simp [intervalChainComplexPointOneMap]

/-- Helper for Lemma 12.3.4: the degree-`0` component of the right endpoint inclusion is the
linear map selecting `[1]`. -/
@[simp]
theorem intervalChainComplexPointOneMap_f_zero :
    intervalChainComplexPointOneMap.f 0 =
      ModuleCat.ofHom ((0 : ℤ →ₗ[ℤ] ℤ).prod (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) := by
  -- `fromSingle₀Equiv` packages the endpoint inclusion by the linear map on degree `0`.
  simp [intervalChainComplexPointOneMap]

/-- Helper for Lemma 12.3.4: the right endpoint inclusion has no positive-degree components. -/
@[simp]
theorem intervalChainComplexPointOneMap_f_succ (n : ℕ) :
    intervalChainComplexPointOneMap.f (n + 1) = 0 := by
  -- The single complex source still forces higher components to be zero.
  simp [intervalChainComplexPointOneMap]

/-- Restriction of `h : X ⊗ I ⟶ X'` along the left endpoint inclusion `[0]`. -/
abbrev tensorIntervalEndpointZero (h : X ⊗ intervalChainComplex ⟶ X') : X ⟶ X' :=
  (rightUnitor X).inv ≫ tensorHom (𝟙 X) intervalChainComplexPointZeroMap ≫ h

/-- `tensorIntervalEndpointZero` is the composite through the right unitor and `[0]`. -/
@[simp]
theorem tensorIntervalEndpointZero_def (h : X ⊗ intervalChainComplex ⟶ X') :
    tensorIntervalEndpointZero h =
      (rightUnitor X).inv ≫ tensorHom (𝟙 X) intervalChainComplexPointZeroMap ≫ h := rfl

/-- Restriction of `h : X ⊗ I ⟶ X'` along the right endpoint inclusion `[1]`. -/
abbrev tensorIntervalEndpointOne (h : X ⊗ intervalChainComplex ⟶ X') : X ⟶ X' :=
  (rightUnitor X).inv ≫ tensorHom (𝟙 X) intervalChainComplexPointOneMap ≫ h

/-- `tensorIntervalEndpointOne` is the composite through the right unitor and `[1]`. -/
@[simp]
theorem tensorIntervalEndpointOne_def (h : X ⊗ intervalChainComplex ⟶ X') :
    tensorIntervalEndpointOne h =
      (rightUnitor X).inv ≫ tensorHom (𝟙 X) intervalChainComplexPointOneMap ≫ h := rfl

variable {f g : X ⟶ X'}

/-- A tensor-interval chain map extends `f` and `g` when its endpoint restrictions recover them. -/
def IsTensorIntervalExtension (f g : X ⟶ X') (h : X ⊗ intervalChainComplex ⟶ X') : Prop :=
  tensorIntervalEndpointZero h = f ∧ tensorIntervalEndpointOne h = g

/-- `IsTensorIntervalExtension f g h` means that `h` restricts to `f` at `[0]` and `g` at `[1]`. -/
theorem isTensorIntervalExtension_iff (h : X ⊗ intervalChainComplex ⟶ X') :
    IsTensorIntervalExtension f g h ↔
      tensorIntervalEndpointZero h = f ∧ tensorIntervalEndpointOne h = g :=
  Iff.rfl

/-- The subtype of tensor-interval chain maps whose endpoint restrictions are `f` and `g`. -/
abbrev TensorIntervalExtension (f g : X ⟶ X') :=
  { h : X ⊗ intervalChainComplex ⟶ X' // IsTensorIntervalExtension f g h }

namespace IsTensorIntervalExtension

/-- The left endpoint restriction of a tensor-interval extension recovers `f`. -/
theorem left_eq {h : X ⊗ intervalChainComplex ⟶ X'} (hh : IsTensorIntervalExtension f g h) :
    tensorIntervalEndpointZero h = f :=
  hh.1

/-- The right endpoint restriction of a tensor-interval extension recovers `g`. -/
theorem right_eq {h : X ⊗ intervalChainComplex ⟶ X'} (hh : IsTensorIntervalExtension f g h) :
    tensorIntervalEndpointOne h = g :=
  hh.2

end IsTensorIntervalExtension

namespace TensorIntervalExtension

/-- The left endpoint restriction of a tensor-interval extension recovers `f`. -/
theorem left_eq (h : TensorIntervalExtension f g) : tensorIntervalEndpointZero h.1 = f :=
  h.2.left_eq

/-- The right endpoint restriction of a tensor-interval extension recovers `g`. -/
theorem right_eq (h : TensorIntervalExtension f g) : tensorIntervalEndpointOne h.1 = g :=
  h.2.right_eq

end TensorIntervalExtension

/-- The tensor-interval extension associated to a chain homotopy `s : Homotopy f g`. -/
noncomputable def tensorIntervalExtensionOfHomotopyApp (s : Homotopy f g) (j : ℕ) :
    (X ⊗ intervalChainComplex).X j ⟶ X'.X j :=
  mapBifunctorDesc (fun i₁ i₂ h ↦ by
      cases i₂ with
      | zero =>
          subst h
          exact
            (𝟙 (X.X i₁) ⊗ₘ
                ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
              (ρ_ (X.X i₁)).hom ≫ f.f i₁
              +
              (𝟙 (X.X i₁) ⊗ₘ
                ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
              (ρ_ (X.X i₁)).hom ≫ g.f i₁
      | succ i₂ =>
          cases i₂ with
          | zero =>
              -- Route correction: the edge summand must carry the tensor sign `(-1)^i`.
              exact (ComplexShape.down ℕ).ε i₁ • ((ρ_ (X.X i₁)).hom ≫ s.hom i₁ j)
          | succ i₂ =>
              exact 0)

/-- Helper for Lemma 12.3.4: on the visible edge summand in total degree `1`, the tensor
differential has only the `D₂` contribution after postcomposition with a chain-map component. -/
theorem tensorEdgeSummand_d_zero_postcompose
    (φ : (X ⊗ intervalChainComplex).X 0 ⟶ X'.X 0) :
    ιTensorObj X intervalChainComplex 0 1 1 rfl ≫
      (X ⊗ intervalChainComplex).d 1 0 ≫ φ =
        (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (0, 1) •
          ((X.X 0 ◁ intervalChainComplex.d 1 0) ≫
            ιTensorObj X intervalChainComplex 0 0 0 (by simp))) ≫
          φ := by
  -- Rewrite the tensor differential into its visible `D₁` and `D₂` branches on the edge summand.
  have hd :
      (X ⊗ intervalChainComplex).d 1 0 =
        (HomologicalComplex.mapBifunctor X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)).d 1 0 := rfl
  rw [hd, HomologicalComplex.mapBifunctor.d_eq X intervalChainComplex
    (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) 1 0,
    ← Category.assoc, Preadditive.comp_add, Preadditive.add_comp]
  rw [Category.assoc, Category.assoc]
  have hD₁ :
      ιTensorObj X intervalChainComplex 0 1 1 rfl ≫
          HomologicalComplex.mapBifunctor.D₁ X intervalChainComplex
            (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) 1 0 ≫
            φ =
        HomologicalComplex.mapBifunctor.d₁ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) 0 1 0 ≫
            φ := by
    -- The `ι_D₁` computation exposes the `d₁` branch in the exact postcomposed spelling needed.
    simpa [HomologicalComplex.ιTensorObj, Category.assoc] using
      congrArg
        (fun t ↦ t ≫ φ)
        (HomologicalComplex.mapBifunctor.ι_D₁ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) 1 0 0 1 rfl)
  have hD₂ :
      ιTensorObj X intervalChainComplex 0 1 1 rfl ≫
          HomologicalComplex.mapBifunctor.D₂ X intervalChainComplex
            (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) 1 0 ≫
            φ =
        HomologicalComplex.mapBifunctor.d₂ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) 0 1 0 ≫
            φ := by
    -- The `ι_D₂` computation exposes the interval-boundary branch in the same spelling world.
    simpa [HomologicalComplex.ιTensorObj, Category.assoc] using
      congrArg
        (fun t ↦ t ≫ φ)
        (HomologicalComplex.mapBifunctor.ι_D₂ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) 1 0 0 1 rfl)
  rw [hD₁, hD₂]
  have hleft :
      HomologicalComplex.mapBifunctor.d₁ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) 0 1 0 ≫
            φ =
        0 := by
    -- In degree `0`, the `X`-boundary branch vanishes because there is no predecessor degree.
    rw [HomologicalComplex.mapBifunctor.d₁_eq_zero X intervalChainComplex
      (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) 0 1 0]
    · exact CategoryTheory.Limits.zero_comp
    · simp [ComplexShape.down_Rel]
  have hIntervalRel : (ComplexShape.down ℕ).Rel 1 0 := by
    simp [ComplexShape.down_Rel]
  have hright :
      HomologicalComplex.mapBifunctor.d₂ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) 0 1 0 ≫
            φ =
        (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (0, 1) •
          ((X.X 0 ◁ intervalChainComplex.d 1 0) ≫
            ιTensorObj X intervalChainComplex 0 0 0 (by simp))) ≫
          φ := by
    -- The interval differential contributes exactly the degree-`0` visible summand.
    rw [HomologicalComplex.mapBifunctor.d₂_eq X intervalChainComplex
      (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) 0 hIntervalRel 0 rfl]
    have hmap :
        ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).obj (X.X 0)).map
            (intervalChainComplex.d 1 0) =
          X.X 0 ◁ intervalChainComplex.d 1 0 := rfl
    rw [hmap]
    -- Re-express the visible inclusion in the tensor-specialized spelling.
    rw [HomologicalComplex.ιTensorObj]
    rfl
  rw [hleft, hright]
  exact zero_add _

/-- Helper for Lemma 12.3.4: on the visible edge summand in total degree `n + 2`, the tensor
differential splits into the `D₁` branch from `X` and the `D₂` branch from the interval. -/
theorem tensorEdgeSummand_d_succ_postcompose
    (n : ℕ) (φ : (X ⊗ intervalChainComplex).X (n + 1) ⟶ X'.X (n + 1)) :
    ιTensorObj X intervalChainComplex (n + 1) 1 (n + 2) rfl ≫
      (X ⊗ intervalChainComplex).d (n + 2) (n + 1) ≫ φ =
        (ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (n + 1, 1) •
          ((X.d (n + 1) n ▷ intervalChainComplex.X 1) ≫
            ιTensorObj X intervalChainComplex n 1 (n + 1) rfl)) ≫
          φ +
        (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (n + 1, 1) •
          ((X.X (n + 1) ◁ intervalChainComplex.d 1 0) ≫
            ιTensorObj X intervalChainComplex (n + 1) 0 (n + 1) (by simp))) ≫
          φ := by
  -- Rewrite the tensor differential into its visible `D₁` and `D₂` branches on the edge summand.
  have hd :
      (X ⊗ intervalChainComplex).d (n + 2) (n + 1) =
        (HomologicalComplex.mapBifunctor X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)).d (n + 2)
          (n + 1) := rfl
  rw [hd, HomologicalComplex.mapBifunctor.d_eq X intervalChainComplex
    (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 2) (n + 1),
    ← Category.assoc, Preadditive.comp_add, Preadditive.add_comp]
  rw [Category.assoc, Category.assoc]
  have hD₁ :
      ιTensorObj X intervalChainComplex (n + 1) 1 (n + 2) rfl ≫
          HomologicalComplex.mapBifunctor.D₁ X intervalChainComplex
            (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 2)
            (n + 1) ≫
            φ =
        HomologicalComplex.mapBifunctor.d₁ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 1) 1
          (n + 1) ≫
            φ := by
    -- The `ι_D₁` computation isolates the contribution from the differential of `X`.
    simpa [HomologicalComplex.ιTensorObj, Category.assoc] using
      congrArg
        (fun t ↦ t ≫ φ)
        (HomologicalComplex.mapBifunctor.ι_D₁ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 2)
          (n + 1) (n + 1) 1 rfl)
  have hD₂ :
      ιTensorObj X intervalChainComplex (n + 1) 1 (n + 2) rfl ≫
          HomologicalComplex.mapBifunctor.D₂ X intervalChainComplex
            (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 2)
            (n + 1) ≫
            φ =
        HomologicalComplex.mapBifunctor.d₂ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 1) 1
          (n + 1) ≫
            φ := by
    -- The `ι_D₂` computation isolates the contribution from the interval boundary.
    simpa [HomologicalComplex.ιTensorObj, Category.assoc] using
      congrArg
        (fun t ↦ t ≫ φ)
        (HomologicalComplex.mapBifunctor.ι_D₂ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 2)
          (n + 1) (n + 1) 1 rfl)
  have hXRel : (ComplexShape.down ℕ).Rel (n + 1) n := by
    simp [ComplexShape.down_Rel]
  have hIntervalRel : (ComplexShape.down ℕ).Rel 1 0 := by
    simp [ComplexShape.down_Rel]
  rw [hD₁, hD₂]
  have hleft :
      HomologicalComplex.mapBifunctor.d₁ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 1) 1
          (n + 1) ≫
            φ =
        (ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (n + 1, 1) •
          ((X.d (n + 1) n ▷ intervalChainComplex.X 1) ≫
            ιTensorObj X intervalChainComplex n 1 (n + 1) rfl)) ≫
          φ := by
    -- The `X`-boundary branch lands in the visible `(n,1)` summand.
    rw [HomologicalComplex.mapBifunctor.d₁_eq X intervalChainComplex
      (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) hXRel 1
      (n + 1) rfl]
    have hmap :
        ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).map (X.d (n + 1) n)).app
            (intervalChainComplex.X 1) =
          X.d (n + 1) n ▷ intervalChainComplex.X 1 := rfl
    rw [hmap]
    -- Re-express the visible inclusion in the tensor-specialized spelling.
    rw [HomologicalComplex.ιTensorObj]
    rfl
  have hright :
      HomologicalComplex.mapBifunctor.d₂ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 1) 1
          (n + 1) ≫
            φ =
        (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (n + 1, 1) •
          ((X.X (n + 1) ◁ intervalChainComplex.d 1 0) ≫
            ιTensorObj X intervalChainComplex (n + 1) 0 (n + 1) (by simp))) ≫
          φ := by
    -- The interval-boundary branch lands in the visible `(n+1,0)` summand.
    rw [HomologicalComplex.mapBifunctor.d₂_eq X intervalChainComplex
      (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 1)
      hIntervalRel (n + 1) rfl]
    have hmap :
        ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).obj (X.X (n + 1))).map
            (intervalChainComplex.d 1 0) =
          X.X (n + 1) ◁ intervalChainComplex.d 1 0 := rfl
    rw [hmap]
    -- Re-express the visible inclusion in the tensor-specialized spelling.
    rw [HomologicalComplex.ιTensorObj]
    rfl
  rw [hleft, hright]

/-- Helper for Lemma 12.3.4: exposing the interval degree-`0` summand of
`tensorIntervalExtensionOfHomotopyApp` returns the endpoint interpolation branch. -/
theorem ιTensorObj_tensorIntervalExtensionOfHomotopyApp_zeroSummand
    (s : Homotopy f g) (i : ℕ) :
    ιTensorObj X intervalChainComplex i 0 i (by simp) ≫
      tensorIntervalExtensionOfHomotopyApp s i =
        (𝟙 (X.X i) ⊗ₘ
            ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
          (ρ_ (X.X i)).hom ≫ f.f i
          +
        (𝟙 (X.X i) ⊗ₘ
            ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
          (ρ_ (X.X i)).hom ≫ g.f i := by
  -- Exposing the visible degree-`0` summand returns exactly the branch chosen in
  -- `tensorIntervalExtensionOfHomotopyApp`.
  simpa [tensorIntervalExtensionOfHomotopyApp] using
    (HomologicalComplex.ι_mapBifunctorDesc
      (K₁ := X) (K₂ := intervalChainComplex)
      (F := MonoidalCategory.curriedTensor (ModuleCat ℤ)) (c := ComplexShape.down ℕ)
      (j := i)
      (f := fun i₁ i₂ h ↦ by
        cases i₂ with
        | zero =>
            subst h
            exact
              (𝟙 (X.X i₁) ⊗ₘ
                  ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
                (ρ_ (X.X i₁)).hom ≫ f.f i₁
                +
              (𝟙 (X.X i₁) ⊗ₘ
                  ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
                (ρ_ (X.X i₁)).hom ≫ g.f i₁
        | succ i₂ =>
            cases i₂ with
            | zero =>
                exact (ComplexShape.down ℕ).ε i₁ • ((ρ_ (X.X i₁)).hom ≫ s.hom i₁ i)
            | succ i₂ =>
                exact 0)
      i 0 (by simp))

/-- Helper for Lemma 12.3.4: exposing the interval degree-`1` summand of
`tensorIntervalExtensionOfHomotopyApp` returns the signed homotopy component. -/
theorem ιTensorObj_tensorIntervalExtensionOfHomotopyApp_edgeSummand
    (s : Homotopy f g) (i : ℕ) :
    ιTensorObj X intervalChainComplex i 1 (i + 1) rfl ≫
      tensorIntervalExtensionOfHomotopyApp s (i + 1) =
        (ComplexShape.down ℕ).ε i • ((ρ_ (X.X i)).hom ≫ s.hom i (i + 1)) := by
  -- Exposing the visible edge summand returns exactly the branch chosen in
  -- `tensorIntervalExtensionOfHomotopyApp`.
  rw [HomologicalComplex.ιTensorObj]
  change
    HomologicalComplex.ιMapBifunctor X intervalChainComplex
        (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) i 1 (i + 1) rfl ≫
      tensorIntervalExtensionOfHomotopyApp s (i + 1) =
        (ComplexShape.down ℕ).ε i • ((ρ_ (X.X i)).hom ≫ s.hom i (i + 1))
  rw [tensorIntervalExtensionOfHomotopyApp]
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp

/-- Helper for Lemma 12.3.4: on the visible degree-`0` summand, only the `D₁` part of the tensor
differential survives after postcomposition with a chain-map component. -/
theorem tensorZeroSummand_d_succ_postcompose
    (n : ℕ) (φ : (X ⊗ intervalChainComplex).X n ⟶ X'.X n) :
    ιTensorObj X intervalChainComplex (n + 1) 0 (n + 1) rfl ≫
      (X ⊗ intervalChainComplex).d (n + 1) n ≫ φ =
        ((X.d (n + 1) n ▷ intervalChainComplex.X 0) ≫
          ιTensorObj X intervalChainComplex n 0 n rfl) ≫
        φ := by
  -- Rewrite the tensor differential into `D₁ + D₂` and note that the interval contribution is zero
  -- on degree `0`.
  have hd :
      (X ⊗ intervalChainComplex).d (n + 1) n =
        (HomologicalComplex.mapBifunctor X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)).d (n + 1) n := rfl
  rw [hd, HomologicalComplex.mapBifunctor.d_eq X intervalChainComplex
    (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 1) n,
    ← Category.assoc, Preadditive.comp_add, Preadditive.add_comp]
  rw [Category.assoc, Category.assoc]
  have hD₁ :
      ιTensorObj X intervalChainComplex (n + 1) 0 (n + 1) rfl ≫
          HomologicalComplex.mapBifunctor.D₁ X intervalChainComplex
            (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 1) n ≫
            φ =
        HomologicalComplex.mapBifunctor.d₁ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 1) 0 n ≫
            φ := by
    -- The `ι_D₁` computation isolates the differential of `X`.
    simpa [HomologicalComplex.ιTensorObj, Category.assoc] using
      congrArg
        (fun t ↦ t ≫ φ)
        (HomologicalComplex.mapBifunctor.ι_D₁ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 1) n
          (n + 1) 0 rfl)
  have hD₂ :
      ιTensorObj X intervalChainComplex (n + 1) 0 (n + 1) rfl ≫
          HomologicalComplex.mapBifunctor.D₂ X intervalChainComplex
            (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 1) n ≫
            φ =
        HomologicalComplex.mapBifunctor.d₂ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 1) 0 n ≫
            φ := by
    -- The `ι_D₂` computation isolates the interval differential contribution.
    simpa [HomologicalComplex.ιTensorObj, Category.assoc] using
      congrArg
        (fun t ↦ t ≫ φ)
        (HomologicalComplex.mapBifunctor.ι_D₂ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 1) n
          (n + 1) 0 rfl)
  have hXRel : (ComplexShape.down ℕ).Rel (n + 1) n := by
    simp [ComplexShape.down_Rel]
  have hNoInterval :
      ¬ (ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0) := by
    simp [ComplexShape.down_Rel]
  rw [hD₁, hD₂]
  have hleft :
      HomologicalComplex.mapBifunctor.d₁ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 1) 0 n ≫
            φ =
        ((X.d (n + 1) n ▷ intervalChainComplex.X 0) ≫
          ιTensorObj X intervalChainComplex n 0 n rfl) ≫
        φ := by
    -- The `X`-boundary branch lands in the visible `(n,0)` summand with sign `1`.
    rw [HomologicalComplex.mapBifunctor.d₁_eq X intervalChainComplex
      (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) hXRel 0 n rfl]
    have hmap :
        ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).map (X.d (n + 1) n)).app
            (intervalChainComplex.X 0) =
          X.d (n + 1) n ▷ intervalChainComplex.X 0 := rfl
    rw [hmap, HomologicalComplex.ιTensorObj]
    have hε₁ :
        ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (n + 1, 0) = 1 := rfl
    rw [hε₁]
    apply ModuleCat.hom_ext
    ext x
    rw [one_smul]
    rfl
  have hright :
      HomologicalComplex.mapBifunctor.d₂ X intervalChainComplex
          (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 1) 0 n ≫
            φ =
        0 := by
    -- The interval complex has no outgoing differential from degree `0`.
    rw [HomologicalComplex.mapBifunctor.d₂_eq_zero X intervalChainComplex
      (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (n + 1) 0 n
      hNoInterval]
    exact CategoryTheory.Limits.zero_comp
  rw [hleft, hright]
  exact add_zero _

/-- Helper for Lemma 12.3.4: evaluating the componentwise chain-map equation on an element gives
the expected differential identity on module elements. -/
theorem chainMapComm_apply {Y Y' : ChainComplex (ModuleCat ℤ) ℕ}
    (u : Y ⟶ Y') (i j : ℕ) (x : Y.X i) :
    (Y'.d i j) (u.f i x) = (u.f j) ((Y.d i j) x) := by
  -- Re-express the statement as evaluation of the chain-map equation `u.comm i j`.
  change ((u.f i ≫ Y'.d i j) : Y.X i ⟶ Y'.X j) x =
    ((Y.d i j ≫ u.f j) : Y.X i ⟶ Y'.X j) x
  exact congrArg (fun t : Y.X i ⟶ Y'.X j => t x) (u.comm i j)

/-- Helper for Lemma 12.3.4: the first projection branch on a degree-`0` tensor summand keeps
the first coefficient. -/
theorem rightUnitor_hom_whiskerLeft_fst_apply {A : ModuleCat ℤ} (x : A) (a b : ℤ) :
    (ρ_ A).hom
        ((A ◁ ModuleCat.ofHom
            (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ))
          (x ⊗ₜ[ℤ] (a, b))) =
      a • x := by
  change
    (ρ_ A).hom
        (x ⊗ₜ[ℤ] ((LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (a, b))) =
      a • x
  rw [ModuleCat.MonoidalCategory.rightUnitor_hom_apply]
  rw [show ((LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (a, b)) = a by rfl]
  exact (int_smul_eq_zsmul (h := inferInstance) (n := a) (x := x)).trans rfl

/-- Helper for Lemma 12.3.4: the second projection branch on a degree-`0` tensor summand keeps
the second coefficient. -/
theorem rightUnitor_hom_whiskerLeft_snd_apply {A : ModuleCat ℤ} (x : A) (a b : ℤ) :
    (ρ_ A).hom
        ((A ◁ ModuleCat.ofHom
            (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ))
          (x ⊗ₜ[ℤ] (a, b))) =
      b • x := by
  change
    (ρ_ A).hom
        (x ⊗ₜ[ℤ] ((LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (a, b))) =
      b • x
  rw [ModuleCat.MonoidalCategory.rightUnitor_hom_apply]
  rw [show ((LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (a, b)) = b by rfl]
  exact (int_smul_eq_zsmul (h := inferInstance) (n := b) (x := x)).trans rfl

/-- Helper for Lemma 12.3.4: the right unitor sends `x ⊗ n` to the scalar multiple `n • x`. -/
theorem rightUnitor_hom_apply_int {A : ModuleCat ℤ} (x : A) (n : ℤ) :
    (ρ_ A).hom (x ⊗ₜ[ℤ] n) = n • x := by
  rw [ModuleCat.MonoidalCategory.rightUnitor_hom_apply]
  exact (int_smul_eq_zsmul (h := inferInstance) (n := n) (x := x)).trans rfl

/-- Helper for Lemma 12.3.4: left whiskering in the first tensor factor applies the morphism to
the left tensor entry of a pure tensor. -/
theorem whiskerLeft_apply_tmul {A B C : ModuleCat ℤ}
    (u : A ⟶ B) (x : A) (z : C) :
    ((u ▷ C) : A ⊗ C ⟶ B ⊗ C) (x ⊗ₜ[ℤ] z) = u x ⊗ₜ[ℤ] z := by
  simp

/-- Helper for Lemma 12.3.4: right whiskering in the second tensor factor applies the morphism to
the right tensor entry of a pure tensor. -/
theorem whiskerRight_apply_tmul {A B C : ModuleCat ℤ}
    (u : B ⟶ C) (x : A) (z : B) :
    ((A ◁ u) : A ⊗ B ⟶ A ⊗ C) (x ⊗ₜ[ℤ] z) = x ⊗ₜ[ℤ] u z := by
  simp

/-- Helper for Lemma 12.3.4: the unique nonzero interval differential sends `n` to `(n, -n)`. -/
theorem intervalChainComplex_d_one_zero_apply (n : ℤ) :
    (intervalChainComplex.d 1 0) n = ((n, -n) : intervalChainComplex.X 0) := by
  rw [intervalChainComplex_d_one_zero]
  rfl

/-- Helper for Lemma 12.3.4: the degree-`1` interval coefficient acts on any `ModuleCat ℤ`
object by the usual `ℤ`-scalar multiplication. -/
theorem intervalEdge_smul_eq_zsmul {A : ModuleCat ℤ} (m : intervalChainComplex.X 1) (y : A) :
    m • y = (m : ℤ) • y := by
  rfl

/-- Helper for Lemma 12.3.4: the usual `ℤ`-scalar multiplication on a `ModuleCat ℤ` object agrees
with the degree-`1` interval scalar action. -/
theorem intervalEdge_zsmul_eq_smul {A : ModuleCat ℤ} (m : intervalChainComplex.X 1) (y : A) :
    ((m : ℤ) • y) = m • y := by
  rfl

/-- Helper for Lemma 12.3.4: the explicit degree-`0` branch of
`tensorIntervalExtensionOfHomotopyApp` evaluates on `(a, b)` as the endpoint interpolation
`a • f + b • g`. -/
theorem tensorIntervalExtensionOfHomotopyApp_zeroSummand_apply_pair
    (s : Homotopy f g) (i : ℕ) (x : X.X i) (a b : ℤ) :
    (ιTensorObj X intervalChainComplex i 0 i (by simp) ≫
        tensorIntervalExtensionOfHomotopyApp s i)
        (x ⊗ₜ[ℤ] ((a, b) : intervalChainComplex.X 0)) =
      a • (f.f i x) + b • (g.f i x) := by
  rw [ιTensorObj_tensorIntervalExtensionOfHomotopyApp_zeroSummand]
  change
    (f.f i).hom
        ((ρ_ (X.X i)).hom
          ((X.X i ◁ ModuleCat.ofHom
              (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ))
            (x ⊗ₜ[ℤ] (a, b)))) +
      (g.f i).hom
        ((ρ_ (X.X i)).hom
          ((X.X i ◁ ModuleCat.ofHom
              (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ))
            (x ⊗ₜ[ℤ] (a, b)))) =
      a • (f.f i x) + b • (g.f i x)
  rw [rightUnitor_hom_whiskerLeft_fst_apply, rightUnitor_hom_whiskerLeft_snd_apply]
  simp

/-- Helper for Lemma 12.3.4: the degree-`0` branch of
`tensorIntervalExtensionOfHomotopyApp` sends the boundary pair `((m, -m))` to the endpoint
difference `m • f - m • g`. -/
theorem tensorIntervalExtensionOfHomotopyApp_zeroSummand_apply_edgePair
    (s : Homotopy f g) (i : ℕ) (x : X.X i) (m : ℤ) :
    (ιTensorObj X intervalChainComplex i 0 i (by simp) ≫
        tensorIntervalExtensionOfHomotopyApp s i)
        (x ⊗ₜ[ℤ] ((m, -m) : intervalChainComplex.X 0)) =
      m • (f.f i x) - m • (g.f i x) := by
  -- Specialize the pair formula to the interval boundary pair `((m, -m))`.
  simpa [sub_eq_add_neg] using
    tensorIntervalExtensionOfHomotopyApp_zeroSummand_apply_pair
      (X := X) (X' := X') (f := f) (g := g) (s := s) (i := i) (x := x) (a := m) (b := -m)

/-- Helper for Lemma 12.3.4: the explicit degree-`1` branch of
`tensorIntervalExtensionOfHomotopyApp` sends `x ⊗ n` to the signed scalar multiple of
`s.hom i (i + 1)`. -/
theorem tensorIntervalExtensionOfHomotopyApp_edgeSummand_apply
    (s : Homotopy f g) (i : ℕ) (x : X.X i) (n : ℤ) :
    (ιTensorObj X intervalChainComplex i 1 (i + 1) rfl ≫
        tensorIntervalExtensionOfHomotopyApp s (i + 1))
        (x ⊗ₜ[ℤ] n) =
      (ComplexShape.down ℕ).ε i • (s.hom i (i + 1) ((n : ℤ) • x)) := by
  rw [ιTensorObj_tensorIntervalExtensionOfHomotopyApp_edgeSummand]
  change
    (ComplexShape.down ℕ).ε i •
        ((s.hom i (i + 1)).hom ((ρ_ (X.X i)).hom (x ⊗ₜ[ℤ] n))) =
      (ComplexShape.down ℕ).ε i • (s.hom i (i + 1) ((n : ℤ) • x))
  rw [rightUnitor_hom_apply_int]

/-- Helper for Lemma 12.3.4: in degree `0`, the homotopy identity rewrites as
`d' (s x) = f x - g x`. -/
theorem homotopyCommZero_apply_sub (s : Homotopy f g) (x : X.X 0) :
    X'.d 1 0 (s.hom 0 1 x) = f.f 0 x - g.f 0 x := by
  have hs := s.comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at hs
  have hx := congrArg (fun t : X.X 0 ⟶ X'.X 0 => t x) hs
  have hsum : X'.d 1 0 (s.hom 0 1 x) + g.f 0 x = f.f 0 x := by
    simpa [HomologicalComplex.comp_f, add_assoc, add_left_comm, add_comm] using hx.symm
  calc
    X'.d 1 0 (s.hom 0 1 x) = X'.d 1 0 (s.hom 0 1 x) + g.f 0 x - g.f 0 x := by
      abel
    _ = f.f 0 x - g.f 0 x := by rw [hsum]

/-- Helper for Lemma 12.3.4: in positive degree, the homotopy identity rewrites as
`d' (s x) = f x - s (d x) - g x`. -/
theorem homotopyCommSucc_apply_sub (s : Homotopy f g) (n : ℕ) (x : X.X (n + 1)) :
    X'.d (n + 2) (n + 1) (s.hom (n + 1) (n + 2) x) =
      f.f (n + 1) x - s.hom n (n + 1) (X.d (n + 1) n x) - g.f (n + 1) x := by
  have hs := s.comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hs
  have hx := congrArg (fun t : X.X (n + 1) ⟶ X'.X (n + 1) => t x) hs
  have hsum :
      X'.d (n + 2) (n + 1) (s.hom (n + 1) (n + 2) x) +
          s.hom n (n + 1) (X.d (n + 1) n x) +
            g.f (n + 1) x =
        f.f (n + 1) x := by
    simpa [HomologicalComplex.comp_f, add_assoc, add_left_comm, add_comm] using hx.symm
  calc
    X'.d (n + 2) (n + 1) (s.hom (n + 1) (n + 2) x) =
        X'.d (n + 2) (n + 1) (s.hom (n + 1) (n + 2) x) +
          s.hom n (n + 1) (X.d (n + 1) n x) +
            g.f (n + 1) x -
              s.hom n (n + 1) (X.d (n + 1) n x) -
                g.f (n + 1) x := by
      abel
    _ = f.f (n + 1) x - s.hom n (n + 1) (X.d (n + 1) n x) - g.f (n + 1) x := by
      rw [hsum]

/-- Helper for Lemma 12.3.4: evaluating the successor-edge postcompose formula on `x ⊗ m`
exposes the `D₁` and `D₂` branches in the exact elementwise spelling used later in the proof. -/
theorem tensorEdgeSummand_d_succ_postcompose_apply_int_split
    (n : ℕ) (φ : (X ⊗ intervalChainComplex).X (n + 1) ⟶ X'.X (n + 1))
    (x : X.X (n + 1)) (m : ℤ) :
    ((ιTensorObj X intervalChainComplex (n + 1) 1 (n + 2) rfl ≫
          (X ⊗ intervalChainComplex).d (n + 2) (n + 1) ≫ φ)
        (x ⊗ₜ[ℤ] m)) =
      ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (n + 1, 1) •
        ((ιTensorObj X intervalChainComplex n 1 (n + 1) rfl ≫ φ)
          (X.d (n + 1) n x ⊗ₜ[ℤ] m)) +
      ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (n + 1, 1) •
        ((ιTensorObj X intervalChainComplex (n + 1) 0 (n + 1) (by simp) ≫ φ)
          (x ⊗ₜ[ℤ] ((m, -m) : intervalChainComplex.X 0))) := by
  -- Evaluate the morphism-level successor-boundary formula on the pure tensor `x ⊗ m`.
  have hpost :=
    congrArg
      (fun t : X.X (n + 1) ⊗ intervalChainComplex.X 1 ⟶ X'.X (n + 1) ↦
        t (x ⊗ₜ[ℤ] m))
      (tensorEdgeSummand_d_succ_postcompose
        (X := X) (X' := X') (n := n) (φ := φ))
  -- Normalize only the whiskered differentials and the interval boundary.
  simpa [whiskerLeft_apply_tmul, whiskerRight_apply_tmul,
    intervalChainComplex_d_one_zero_apply] using hpost



/-- Helper for Lemma 12.3.4: the `1 → 0` component of
`tensorIntervalExtensionOfHomotopyApp s` satisfies the chain-map equation. -/
theorem tensorIntervalExtensionOfHomotopyApp_comm_zero
    (s : Homotopy f g) :
    tensorIntervalExtensionOfHomotopyApp s 1 ≫ X'.d 1 0 =
      (X ⊗ intervalChainComplex).d 1 0 ≫
        tensorIntervalExtensionOfHomotopyApp s 0 := by
  -- Compare the two morphisms on the visible tensor summands in total degree `1`.
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i i₂ hij
  cases i₂ with
  | zero =>
      have hi : i = 1 := by
        simpa using hij
      subst i
      cases hij
      -- On the `(1,0)` summand, both sides are the degree-`0` interpolation followed by the
      -- chain-map identities for `f` and `g`.
      change
        ιTensorObj X intervalChainComplex 1 0 1 rfl ≫ tensorIntervalExtensionOfHomotopyApp s 1 ≫
            X'.d 1 0 =
          ιTensorObj X intervalChainComplex 1 0 1 rfl ≫ (X ⊗ intervalChainComplex).d 1 0 ≫
            tensorIntervalExtensionOfHomotopyApp s 0
      rw [← Category.assoc]
      rw [tensorZeroSummand_d_succ_postcompose
        (X := X) (X' := X') (n := 0) (φ := tensorIntervalExtensionOfHomotopyApp s 0)]
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x z
      rcases z with ⟨a, b⟩
      change
        X'.d 1 0
            ((ιTensorObj X intervalChainComplex 1 0 1 rfl ≫
                  tensorIntervalExtensionOfHomotopyApp s 1)
              (x ⊗ₜ[ℤ] ((a, b) : intervalChainComplex.X 0))) =
          (((X.d 1 0 ▷ intervalChainComplex.X 0) ≫
                ιTensorObj X intervalChainComplex 0 0 0 rfl ≫
                  tensorIntervalExtensionOfHomotopyApp s 0)
            (x ⊗ₜ[ℤ] ((a, b) : intervalChainComplex.X 0)))
      have hleft :=
        congrArg
          (X'.d 1 0)
          (tensorIntervalExtensionOfHomotopyApp_zeroSummand_apply_pair
            (X := X) (X' := X') (f := f) (g := g) (s := s) (i := 1) (x := x)
            (a := a) (b := b))
      have hright :=
        tensorIntervalExtensionOfHomotopyApp_zeroSummand_apply_pair
          (X := X) (X' := X') (f := f) (g := g) (s := s) (i := 0)
          (x := X.d 1 0 x) (a := a) (b := b)
      rw [hleft]
      change
        X'.d 1 0 (a • f.f 1 x + b • g.f 1 x) =
          (ιTensorObj X intervalChainComplex 0 0 0 rfl ≫ tensorIntervalExtensionOfHomotopyApp s 0)
            (X.d 1 0 x ⊗ₜ[ℤ] ((a, b) : intervalChainComplex.X 0))
      rw [hright]
      -- Route correction: keep the edge/boundary coefficients in ambient `ℤ` and use the
      -- chain-map identities only after both sides are in the same scalar spelling.
      simp [LinearMap.map_add, map_zsmul,
        chainMapComm_apply (u := f) (i := 1) (j := 0) (x := x),
        chainMapComm_apply (u := g) (i := 1) (j := 0) (x := x)]
  | succ i₂ =>
      cases i₂ with
      | zero =>
          have hi : i = 0 := by
            simpa using hij
          subst i
          cases hij
          -- On the `(0,1)` edge summand, the tensor boundary is exactly the chain-homotopy
          -- identity evaluated on the interval generator.
          change
            ιTensorObj X intervalChainComplex 0 1 1 rfl ≫ tensorIntervalExtensionOfHomotopyApp s 1 ≫
                X'.d 1 0 =
              ιTensorObj X intervalChainComplex 0 1 1 rfl ≫ (X ⊗ intervalChainComplex).d 1 0 ≫
                tensorIntervalExtensionOfHomotopyApp s 0
          rw [← Category.assoc]
          rw [tensorEdgeSummand_d_zero_postcompose
            (X := X) (X' := X') (φ := tensorIntervalExtensionOfHomotopyApp s 0)]
          rw [show ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (ComplexShape.down ℕ) (0, 1) = 1 by rfl]
          rw [one_smul]
          apply ModuleCat.MonoidalCategory.tensor_ext
          intro x m
          change
            X'.d 1 0
                ((ιTensorObj X intervalChainComplex 0 1 1 rfl ≫
                      tensorIntervalExtensionOfHomotopyApp s 1)
                  (x ⊗ₜ[ℤ] m)) =
              (((X.X 0 ◁ intervalChainComplex.d 1 0) ≫
                    ιTensorObj X intervalChainComplex 0 0 0 (by simp) ≫
                      tensorIntervalExtensionOfHomotopyApp s 0)
                (x ⊗ₜ[ℤ] m))
          have hedge :=
            congrArg
              (X'.d 1 0)
              (tensorIntervalExtensionOfHomotopyApp_edgeSummand_apply
                (X := X) (X' := X') (f := f) (g := g) (s := s) (i := 0) (x := x)
                (n := m))
          rw [hedge]
          rw [show (ComplexShape.down ℕ).ε 0 = 1 by
            simp]
          rw [one_smul]
          have hboundary :
              (((X.X 0 ◁ intervalChainComplex.d 1 0) ≫
                    ιTensorObj X intervalChainComplex 0 0 0 (by simp) ≫
                      tensorIntervalExtensionOfHomotopyApp s 0)
                  (x ⊗ₜ[ℤ] m)) =
                (ιTensorObj X intervalChainComplex 0 0 0 (by simp) ≫
                    tensorIntervalExtensionOfHomotopyApp s 0)
                  (x ⊗ₜ[ℤ] intervalChainComplex.d 1 0 m) := by
            simpa [Function.comp_apply] using
              congrArg
                (fun z ↦
                  (ιTensorObj X intervalChainComplex 0 0 0 (by simp) ≫
                    tensorIntervalExtensionOfHomotopyApp s 0) z)
                (whiskerRight_apply_tmul
                  (A := X.X 0) (u := intervalChainComplex.d 1 0) (x := x) (z := m))
          rw [hboundary]
          rw [intervalChainComplex_d_one_zero_apply]
          rw [tensorIntervalExtensionOfHomotopyApp_zeroSummand_apply_edgePair
            (X := X) (X' := X') (f := f) (g := g) (s := s) (i := 0) (x := x) (m := m)]
          let mz : ℤ := m
          have hzeroScaled :=
            congrArg
              (fun y ↦ mz • y)
              (homotopyCommZero_apply_sub
                (X := X) (X' := X') (f := f) (g := g) (s := s) (x := x))
          simpa [mz, map_zsmul, zsmul_sub] using hzeroScaled
      | succ k =>
          -- Higher interval degrees are trivial, so both visible branch maps are zero.
          apply ModuleCat.MonoidalCategory.tensor_ext
          intro x z
          have hz : z = 0 := by
            funext t
            exact Fin.elim0 t
          subst hz
          simp [tensorIntervalExtensionOfHomotopyApp]

/-- Helper for Lemma 12.3.4: the `(n + 2) → (n + 1)` component of
`tensorIntervalExtensionOfHomotopyApp s` satisfies the chain-map equation. -/
theorem tensorIntervalExtensionOfHomotopyApp_comm_succ
    (s : Homotopy f g) (n : ℕ) :
    tensorIntervalExtensionOfHomotopyApp s (n + 2) ≫ X'.d (n + 2) (n + 1) =
      (X ⊗ intervalChainComplex).d (n + 2) (n + 1) ≫
        tensorIntervalExtensionOfHomotopyApp s (n + 1) := by
  -- Compare the two morphisms on the visible tensor summands in total degree `n + 2`.
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i i₂ hij
  cases i₂ with
  | zero =>
      have hi : i = n + 2 := by
        simpa using hij
      subst i
      cases hij
      -- The degree-`0` interval branch is just the endpoint interpolation transported by `d_X`.
      change
        ιTensorObj X intervalChainComplex (n + 2) 0 (n + 2) rfl ≫
            tensorIntervalExtensionOfHomotopyApp s (n + 2) ≫ X'.d (n + 2) (n + 1) =
          ιTensorObj X intervalChainComplex (n + 2) 0 (n + 2) rfl ≫
            (X ⊗ intervalChainComplex).d (n + 2) (n + 1) ≫
              tensorIntervalExtensionOfHomotopyApp s (n + 1)
      rw [← Category.assoc]
      rw [tensorZeroSummand_d_succ_postcompose
        (X := X) (X' := X') (n := n + 1) (φ := tensorIntervalExtensionOfHomotopyApp s (n + 1))]
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x z
      rcases z with ⟨a, b⟩
      change
        X'.d (n + 2) (n + 1)
            ((ιTensorObj X intervalChainComplex (n + 2) 0 (n + 2) rfl ≫
                  tensorIntervalExtensionOfHomotopyApp s (n + 2))
              (x ⊗ₜ[ℤ] ((a, b) : intervalChainComplex.X 0))) =
          (((X.d (n + 2) (n + 1) ▷ intervalChainComplex.X 0) ≫
                ιTensorObj X intervalChainComplex (n + 1) 0 (n + 1) rfl ≫
                  tensorIntervalExtensionOfHomotopyApp s (n + 1))
            (x ⊗ₜ[ℤ] ((a, b) : intervalChainComplex.X 0)))
      have hleft :=
        congrArg
          (X'.d (n + 2) (n + 1))
          (tensorIntervalExtensionOfHomotopyApp_zeroSummand_apply_pair
            (X := X) (X' := X') (f := f) (g := g) (s := s) (i := n + 2) (x := x)
            (a := a) (b := b))
      have hright :=
        tensorIntervalExtensionOfHomotopyApp_zeroSummand_apply_pair
          (X := X) (X' := X') (f := f) (g := g) (s := s) (i := n + 1)
          (x := X.d (n + 2) (n + 1) x) (a := a) (b := b)
      rw [hleft]
      change
        X'.d (n + 2) (n + 1) (a • f.f (n + 2) x + b • g.f (n + 2) x) =
          (ιTensorObj X intervalChainComplex (n + 1) 0 (n + 1) rfl ≫
              tensorIntervalExtensionOfHomotopyApp s (n + 1))
            (X.d (n + 2) (n + 1) x ⊗ₜ[ℤ] ((a, b) : intervalChainComplex.X 0))
      rw [hright]
      simp [LinearMap.map_add, map_zsmul,
        chainMapComm_apply (u := f) (i := n + 2) (j := n + 1) (x := x),
        chainMapComm_apply (u := g) (i := n + 2) (j := n + 1) (x := x)]
  | succ i₂ =>
      cases i₂ with
      | zero =>
          have hi : i = n + 1 := by
            simpa using hij
          subst i
          cases hij
          -- The edge branch is the chain-homotopy identity evaluated on `x ⊗ m`.
          apply ModuleCat.MonoidalCategory.tensor_ext
          intro x m
          change
            X'.d (n + 2) (n + 1)
                ((ιTensorObj X intervalChainComplex (n + 1) 1 (n + 2) rfl ≫
                      tensorIntervalExtensionOfHomotopyApp s (n + 2))
                  (x ⊗ₜ[ℤ] m)) =
              ((ιTensorObj X intervalChainComplex (n + 1) 1 (n + 2) rfl ≫
                    (X ⊗ intervalChainComplex).d (n + 2) (n + 1) ≫
                      tensorIntervalExtensionOfHomotopyApp s (n + 1))
                (x ⊗ₜ[ℤ] m))
          rw [tensorEdgeSummand_d_succ_postcompose_apply_int_split
            (X := X) (X' := X') (n := n) (φ := tensorIntervalExtensionOfHomotopyApp s (n + 1))
            (x := x) (m := m)]
          have hedge :=
            congrArg
              (X'.d (n + 2) (n + 1))
              (tensorIntervalExtensionOfHomotopyApp_edgeSummand_apply
                (X := X) (X' := X') (f := f) (g := g) (s := s) (i := n + 1) (x := x)
                (n := m))
          rw [hedge]
          rw [Units.smul_def, map_zsmul]
          rw [tensorIntervalExtensionOfHomotopyApp_edgeSummand_apply
            (X := X) (X' := X') (f := f) (g := g) (s := s) (i := n)
            (x := X.d (n + 1) n x) (n := m)]
          rw [tensorIntervalExtensionOfHomotopyApp_zeroSummand_apply_edgePair
            (X := X) (X' := X') (f := f) (g := g) (s := s) (i := n + 1) (x := x) (m := m)]
          have hε :
              (ComplexShape.down ℕ).ε n =
                -(ComplexShape.down ℕ).ε (n + 1) := by
            simpa [ComplexShape.down_Rel] using
              (ComplexShape.ε_succ (c := ComplexShape.down ℕ)
                (p := n + 1) (q := n) (by simp [ComplexShape.down_Rel]))
          rw [show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (ComplexShape.down ℕ) (n + 1, 1) = 1 by rfl]
          rw [one_smul]
          rw [show ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (ComplexShape.down ℕ) (n + 1, 1) = (ComplexShape.down ℕ).ε (n + 1) by rfl]
          let mz : ℤ := m
          have hsuccScaled :=
            congrArg
              (fun y ↦
                (↑((ComplexShape.down ℕ).ε (n + 1)) : ℤ) • (mz • y))
              (homotopyCommSucc_apply_sub
                (X := X) (X' := X') (f := f) (g := g) (s := s) (n := n) (x := x))
          -- Route correction: rewrite the successor sign once, then let the linear maps absorb
          -- the ambient `ℤ`-scalars before finishing by additive normalization.
          rw [hε]
          rcases Int.units_eq_one_or ((ComplexShape.down ℕ).ε (n + 1)) with he | he
          · simp [he, mz, Units.smul_def, map_zsmul, zsmul_sub] at hsuccScaled ⊢
            rw [hsuccScaled]
            abel
          · simp [he, mz, Units.smul_def, map_zsmul, zsmul_sub] at hsuccScaled ⊢
            rw [hsuccScaled]
            abel
      | succ k =>
          -- Higher interval degrees are trivial, so the corresponding visible summands vanish.
          apply ModuleCat.MonoidalCategory.tensor_ext
          intro x z
          have hz : z = 0 := by
            funext t
            exact Fin.elim0 t
          subst hz
          simp [tensorIntervalExtensionOfHomotopyApp]

/-- The components of `tensorIntervalExtensionOfHomotopyApp` commute with the differential. -/
theorem tensorIntervalExtensionOfHomotopyApp_comm (s : Homotopy f g) :
    ∀ i j, (ComplexShape.down ℕ).Rel i j →
      tensorIntervalExtensionOfHomotopyApp s i ≫ X'.d i j =
        (X ⊗ intervalChainComplex).d i j ≫
          tensorIntervalExtensionOfHomotopyApp s j := by
  intro i j hij
  cases i with
  | zero =>
      exfalso
      simp [ComplexShape.down_Rel] at hij
  | succ i =>
      cases i with
      | zero =>
          have hj : j = 0 := by simpa [ComplexShape.down_Rel] using hij
          subst hj
          -- The `1 → 0` differential is the exceptional boundary case.
          exact tensorIntervalExtensionOfHomotopyApp_comm_zero
            (X := X) (X' := X') (f := f) (g := g) s
      | succ n =>
          have hj : j = n + 1 := by simpa [ComplexShape.down_Rel] using hij
          subst hj
          -- Every positive-degree differential is a successor case.
          exact tensorIntervalExtensionOfHomotopyApp_comm_succ
            (X := X) (X' := X') (f := f) (g := g) s n

/-- The chain map underlying the tensor-interval extension associated to `s : Homotopy f g`. -/
noncomputable def tensorIntervalExtensionOfHomotopyHom (s : Homotopy f g) :
    X ⊗ intervalChainComplex ⟶ X' where
  f := tensorIntervalExtensionOfHomotopyApp s
  comm' := tensorIntervalExtensionOfHomotopyApp_comm s

/-- Helper for Lemma 12.3.4: the degree-`i` component of `(rightUnitor X).inv` is the canonical
degree-`0` tensor-unit summand inclusion. -/
theorem rightUnitorInv_f_eqZeroSummand (i : ℕ) :
    (rightUnitor X).inv.f i =
      (ρ_ (X.X i)).inv ≫ X.X i ◁ 𝟙 (𝟙_ (ModuleCat ℤ)) ≫
        ιTensorObj X ((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) i 0 i
          (by simp) := by
  -- Re-express the chain-level right unitor component by the explicit degree-`0` summand formula.
  change (rightUnitor' X).inv i = _
  simpa using (HomologicalComplex.rightUnitor'_inv (K := X) i)

/-- Helper for Lemma 12.3.4: precomposing with the degree-`0` tensor-unit summand pushes an
endpoint map `u` through `tensorHom (𝟙 X) u` onto the interval degree-`0` summand. -/
theorem tensorEndpointMap_assoc
    (u : (ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ) ⟶ intervalChainComplex)
    (k : X ⊗ intervalChainComplex ⟶ X') (i : ℕ) :
    ιTensorObj X ((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) i 0 i (by simp) ≫
      (tensorHom (𝟙 X) u).f i ≫
      k.f i =
      ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).map (𝟙 (X.X i))).app
          (((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).X 0) ≫
        ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).obj (X.X i)).map (u.f 0) ≫
          ιTensorObj X intervalChainComplex i 0 i (by simp) ≫
            k.f i := by
  -- This is the degreewise `ι_mapBifunctorMap_assoc` computation specialized to `tensorHom`.
  simpa [HomologicalComplex.ιTensorObj, tensorHom] using
    (HomologicalComplex.ι_mapBifunctorMap_assoc (f₁ := 𝟙 X) (f₂ := u)
      (F := MonoidalCategory.curriedTensor (ModuleCat ℤ)) (c := ComplexShape.down ℕ)
      (i₁ := i) (i₂ := 0) (j := i) (by simp)
      (k.f i))

/-- Helper for Lemma 12.3.4: exposing the interval degree-`0` summand of the forward tensor
extension recovers the endpoint branch used in the `mapBifunctorDesc` definition. -/
theorem ιTensorObj_tensorIntervalExtensionOfHomotopyHom_f_zeroSummand
    (s : Homotopy f g) (i : ℕ) :
    ιTensorObj X intervalChainComplex i 0 i (by simp) ≫
      (tensorIntervalExtensionOfHomotopyHom s).f i =
        (𝟙 (X.X i) ⊗ₘ
            ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
          (ρ_ (X.X i)).hom ≫ f.f i
          +
        (𝟙 (X.X i) ⊗ₘ
            ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
          (ρ_ (X.X i)).hom ≫ g.f i := by
  -- Exposing the visible degree-`0` summand removes the total-complex transport from the branch.
  simpa [tensorIntervalExtensionOfHomotopyHom, tensorIntervalExtensionOfHomotopyApp] using
    (HomologicalComplex.ι_mapBifunctorDesc
      (K₁ := X) (K₂ := intervalChainComplex)
      (F := MonoidalCategory.curriedTensor (ModuleCat ℤ)) (c := ComplexShape.down ℕ)
      (j := i)
      (f := fun i₁ i₂ h ↦ by
        cases i₂ with
        | zero =>
            subst h
            exact
              (𝟙 (X.X i₁) ⊗ₘ
                  ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
                (ρ_ (X.X i₁)).hom ≫ f.f i₁
                +
                (𝟙 (X.X i₁) ⊗ₘ
                  ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
                (ρ_ (X.X i₁)).hom ≫ g.f i₁
        | succ i₂ =>
            cases i₂ with
            | zero =>
                exact (ComplexShape.down ℕ).ε i₁ • ((ρ_ (X.X i₁)).hom ≫ s.hom i₁ i)
            | succ i₂ =>
                exact 0)
      i 0 (by simp))

/-- Helper for Lemma 12.3.4: `ιTensorObj` is the tensor-specialized spelling of
`ιMapBifunctor`. -/
theorem ιTensorObj_eq_ιMapBifunctor (i₁ i₂ j : ℕ) (h : i₁ + i₂ = j) :
    ιTensorObj X intervalChainComplex i₁ i₂ j h =
      HomologicalComplex.ιMapBifunctor X intervalChainComplex
        (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) i₁ i₂ j h := by
  -- `ιTensorObj` is defined as the tensor-product abbreviation of `ιMapBifunctor`.
  rfl

/-- Helper for Lemma 12.3.4: exposing the interval degree-`1` summand of the forward tensor
extension recovers the signed homotopy component on the forward chain map. -/
theorem ιTensorObj_tensorIntervalExtensionOfHomotopyHom_f_edgeSummand
    (s : Homotopy f g) (i : ℕ) :
    ιTensorObj X intervalChainComplex i 1 (i + 1) rfl ≫
      (tensorIntervalExtensionOfHomotopyHom s).f (i + 1) =
        (ComplexShape.down ℕ).ε i • ((ρ_ (X.X i)).hom ≫ s.hom i (i + 1)) := by
  -- Route correction: keep the `(i,1)` branch in the exact `mapBifunctorDesc` normal form so
  -- `ι_mapBifunctorDesc` can expose the signed homotopy term without extra transport.
  rw [ιTensorObj_eq_ιMapBifunctor (X := X) (i₁ := i) (i₂ := 1) (j := i + 1) rfl]
  change
    HomologicalComplex.ιMapBifunctor X intervalChainComplex
        (MonoidalCategory.curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) i 1 (i + 1) rfl ≫
      tensorIntervalExtensionOfHomotopyApp s (i + 1) =
        (ComplexShape.down ℕ).ε i • ((ρ_ (X.X i)).hom ≫ s.hom i (i + 1))
  rw [tensorIntervalExtensionOfHomotopyApp]
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp

/-- Helper for Lemma 12.3.4: at the left endpoint `(1, 0)`, the first projection branch reduces
to the original tensor factor. -/
theorem rightUnitor_hom_whiskerLeft_fst_oneZero {A : ModuleCat ℤ} (x : A) :
    (ρ_ A).hom
        ((A ◁ ModuleCat.ofHom
            (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ))
          (x ⊗ₜ[ℤ] (1, 0))) =
      x := by
  -- Rewrite directly to the pure-tensor normal form so the right unitor sees the endpoint scalar.
  change
    (ρ_ A).hom
        (x ⊗ₜ[ℤ] ((LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (1, 0))) =
      x
  rw [ModuleCat.MonoidalCategory.rightUnitor_hom_apply]
  rw [show ((LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (1, 0)) = 1 by rfl]
  exact (int_smul_eq_zsmul (h := inferInstance) (n := (1 : ℤ)) (x := x)).trans (one_zsmul x)

/-- Helper for Lemma 12.3.4: at the left endpoint `(1, 0)`, the second projection branch
vanishes. -/
theorem rightUnitor_hom_whiskerLeft_snd_oneZero {A : ModuleCat ℤ} (x : A) :
    (ρ_ A).hom
        ((A ◁ ModuleCat.ofHom
            (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ))
          (x ⊗ₜ[ℤ] (1, 0))) =
      0 := by
  -- Rewrite directly to the pure-tensor normal form so the zero endpoint coefficient is explicit.
  change
    (ρ_ A).hom
        (x ⊗ₜ[ℤ] ((LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (1, 0))) =
      0
  rw [ModuleCat.MonoidalCategory.rightUnitor_hom_apply]
  rw [show ((LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (1, 0)) = 0 by rfl]
  exact (int_smul_eq_zsmul (h := inferInstance) (n := (0 : ℤ)) (x := x)).trans (zero_zsmul x)

/-- Helper for Lemma 12.3.4: at the right endpoint `(0, 1)`, the first projection branch
vanishes. -/
theorem rightUnitor_hom_whiskerLeft_fst_zeroOne {A : ModuleCat ℤ} (x : A) :
    (ρ_ A).hom
        ((A ◁ ModuleCat.ofHom
            (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ))
          (x ⊗ₜ[ℤ] (0, 1))) =
      0 := by
  -- Rewrite directly to the pure-tensor normal form so the zero endpoint coefficient is explicit.
  change
    (ρ_ A).hom
        (x ⊗ₜ[ℤ] ((LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (0, 1))) =
      0
  rw [ModuleCat.MonoidalCategory.rightUnitor_hom_apply]
  rw [show ((LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (0, 1)) = 0 by rfl]
  exact (int_smul_eq_zsmul (h := inferInstance) (n := (0 : ℤ)) (x := x)).trans (zero_zsmul x)

/-- Helper for Lemma 12.3.4: at the right endpoint `(0, 1)`, the second projection branch reduces
to the original tensor factor. -/
theorem rightUnitor_hom_whiskerLeft_snd_zeroOne {A : ModuleCat ℤ} (x : A) :
    (ρ_ A).hom
        ((A ◁ ModuleCat.ofHom
            (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ))
          (x ⊗ₜ[ℤ] (0, 1))) =
      x := by
  -- Rewrite directly to the pure-tensor normal form so the right unitor sees the endpoint scalar.
  change
    (ρ_ A).hom
        (x ⊗ₜ[ℤ] ((LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (0, 1))) =
      x
  rw [ModuleCat.MonoidalCategory.rightUnitor_hom_apply]
  rw [show ((LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (0, 1)) = 1 by rfl]
  exact (int_smul_eq_zsmul (h := inferInstance) (n := (1 : ℤ)) (x := x)).trans (one_zsmul x)


/-- Helper for Lemma 12.3.4: a linear map out of `intervalChainComplex.X 0` is determined by its
values on `[0]` and `[1]`. -/
theorem intervalChainComplexZeroLinear_apply_pair {A : ModuleCat ℤ}
    (ℓ : intervalChainComplex.X 0 ⟶ A) (a b : ℤ) :
    ℓ ((a, b) : intervalChainComplex.X 0) =
      a • ℓ intervalChainComplexPointZero + b • ℓ intervalChainComplexPointOne := by
  -- Rewrite the pair `(a,b)` in the basis `[0],[1]` before applying linearity.
  have hpair :
      ((a, b) : intervalChainComplex.X 0) =
        a • intervalChainComplexPointZero + b • intervalChainComplexPointOne := by
    change ((a, b) : ℤ × ℤ) =
      a • ((1, 0) : ℤ × ℤ) + b • ((0, 1) : ℤ × ℤ)
    simp
  rw [hpair]
  simp

/-- Helper for Lemma 12.3.4: the curried tensor composite carrying an endpoint map `u`
rewrites the generator `x ⊗ 1` to `x ⊗ u(1)`. -/
theorem curriedTensorMap_apply_one {A B : ModuleCat ℤ}
    (u : ModuleCat.of ℤ ℤ ⟶ B) (x : A) :
    ((((MonoidalCategory.curriedTensor (ModuleCat ℤ)).map (𝟙 A)).app (ModuleCat.of ℤ ℤ)) ≫
        ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).obj A).map u)
        (x ⊗ₜ[ℤ] (1 : ℤ)) =
      x ⊗ₜ[ℤ] u.hom 1 := by
  -- Unfold the curried tensor composite only through the standard `ModuleCat` tensor API.
  simpa using (ModuleCat.MonoidalCategory.tensorHom_tmul (𝟙 A) u x (1 : ℤ))


/-- Helper for Lemma 12.3.4: the visible degree-`0` summand of a tensor-interval extension sends
`x ⊗ [0]` to `f x`. -/
theorem tensorIntervalExtension_zeroSummand_apply_pointZero
    (h : TensorIntervalExtension f g) (i : ℕ) (x : X.X i) :
    (ιTensorObj X intervalChainComplex i 0 i (by simp) ≫ h.1.f i)
        (x ⊗ₜ[ℤ] intervalChainComplexPointZero) =
      (f.f i) x := by
  -- Route correction: normalize the endpoint restriction through the generic `x ⊗ 1` bridge
  -- before identifying the visible degree-`0` basis vector `[0]`.
  have hleft := congrArg (fun t ↦ t.f i) (TensorIntervalExtension.left_eq (h := h))
  rw [tensorIntervalEndpointZero_def] at hleft
  simp only [HomologicalComplex.comp_f] at hleft
  rw [rightUnitorInv_f_eqZeroSummand (X := X) i] at hleft
  let p := (ρ_ (X.X i)).inv ≫ X.X i ◁ 𝟙 (𝟙_ (ModuleCat ℤ))
  change p ≫
      ιTensorObj X ((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) i 0 i (by simp) ≫
        (tensorHom (𝟙 X) intervalChainComplexPointZeroMap).f i ≫ h.1.f i =
      f.f i at hleft
  have hleft_apply := congrArg (fun t ↦ t x) hleft
  have hleft_apply' :
      (ιTensorObj X ((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) i 0 i
          (by simp) ≫
        (tensorHom (𝟙 X) intervalChainComplexPointZeroMap).f i ≫ h.1.f i)
          (x ⊗ₜ[ℤ] (1 : ℤ)) =
        (f.f i) x := by
    -- Evaluating the right unitor inverse on `x` produces the pure tensor `x ⊗ 1`.
    simpa [p] using hleft_apply
  have hendpoint_apply :=
    congrArg
      (fun t ↦ t (x ⊗ₜ[ℤ] (1 : ℤ)))
      (tensorEndpointMap_assoc (X := X) (X' := X') (u := intervalChainComplexPointZeroMap)
        (k := h.1) i)
  have hvisible :
      ((((MonoidalCategory.curriedTensor (ModuleCat ℤ)).map (𝟙 (X.X i))).app
          (((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).X 0)) ≫
        ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).obj (X.X i)).map
            (intervalChainComplexPointZeroMap.f 0) ≫
          ιTensorObj X intervalChainComplex i 0 i (by simp) ≫ h.1.f i)
          (x ⊗ₜ[ℤ] (1 : ℤ)) =
        (f.f i) x := by
    -- The endpoint equation now lives on the pure tensor `x ⊗ 1`.
    exact hendpoint_apply.symm.trans hleft_apply'
  simpa [intervalChainComplexPointZero, intervalChainComplexPointZeroMap_f_zero] using
    ((curriedTensorMap_apply_one (u := intervalChainComplexPointZeroMap.f 0) (x := x) |>
      congrArg (fun z ↦ (ιTensorObj X intervalChainComplex i 0 i (by simp) ≫ h.1.f i) z)).symm.trans
        hvisible)

/-- Helper for Lemma 12.3.4: the visible degree-`0` summand of a tensor-interval extension sends
`x ⊗ [1]` to `g x`. -/
theorem tensorIntervalExtension_zeroSummand_apply_pointOne
    (h : TensorIntervalExtension f g) (i : ℕ) (x : X.X i) :
    (ιTensorObj X intervalChainComplex i 0 i (by simp) ≫ h.1.f i)
        (x ⊗ₜ[ℤ] intervalChainComplexPointOne) =
      (g.f i) x := by
  -- Route correction: normalize the endpoint restriction through the generic `x ⊗ 1` bridge
  -- before identifying the visible degree-`0` basis vector `[1]`.
  have hright := congrArg (fun t ↦ t.f i) (TensorIntervalExtension.right_eq (h := h))
  rw [tensorIntervalEndpointOne_def] at hright
  simp only [HomologicalComplex.comp_f] at hright
  rw [rightUnitorInv_f_eqZeroSummand (X := X) i] at hright
  let p := (ρ_ (X.X i)).inv ≫ X.X i ◁ 𝟙 (𝟙_ (ModuleCat ℤ))
  change p ≫
      ιTensorObj X ((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) i 0 i (by simp) ≫
        (tensorHom (𝟙 X) intervalChainComplexPointOneMap).f i ≫ h.1.f i =
      g.f i at hright
  have hright_apply := congrArg (fun t ↦ t x) hright
  have hright_apply' :
      (ιTensorObj X ((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) i 0 i
          (by simp) ≫
        (tensorHom (𝟙 X) intervalChainComplexPointOneMap).f i ≫ h.1.f i)
          (x ⊗ₜ[ℤ] (1 : ℤ)) =
        (g.f i) x := by
    -- Evaluating the right unitor inverse on `x` produces the pure tensor `x ⊗ 1`.
    simpa [p] using hright_apply
  have hendpoint_apply :=
    congrArg
      (fun t ↦ t (x ⊗ₜ[ℤ] (1 : ℤ)))
      (tensorEndpointMap_assoc (X := X) (X' := X') (u := intervalChainComplexPointOneMap)
        (k := h.1) i)
  have hvisible :
      ((((MonoidalCategory.curriedTensor (ModuleCat ℤ)).map (𝟙 (X.X i))).app
          (((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).X 0)) ≫
        ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).obj (X.X i)).map
            (intervalChainComplexPointOneMap.f 0) ≫
          ιTensorObj X intervalChainComplex i 0 i (by simp) ≫ h.1.f i)
          (x ⊗ₜ[ℤ] (1 : ℤ)) =
        (g.f i) x := by
    -- The endpoint equation now lives on the pure tensor `x ⊗ 1`.
    exact hendpoint_apply.symm.trans hright_apply'
  simpa [intervalChainComplexPointOne, intervalChainComplexPointOneMap_f_zero] using
    ((curriedTensorMap_apply_one (u := intervalChainComplexPointOneMap.f 0) (x := x) |>
      congrArg (fun z ↦ (ιTensorObj X intervalChainComplex i 0 i (by simp) ≫ h.1.f i) z)).symm.trans
        hvisible)

/-- Helper for Lemma 12.3.4: the visible degree-`0` summand of a tensor-interval extension is
linear in the interval variable, so its value on `(a,b)` is determined by the endpoint values. -/
theorem tensorIntervalExtension_zeroSummand_apply_pair
    (h : TensorIntervalExtension f g) (i : ℕ) (x : X.X i) (a b : ℤ) :
    (ιTensorObj X intervalChainComplex i 0 i (by simp) ≫ h.1.f i)
        (x ⊗ₜ[ℤ] ((a, b) : intervalChainComplex.X 0)) =
      a • (f.f i x) + b • (g.f i x) := by
  -- Route correction: curry in the interval variable so `intervalChainComplexZeroLinear_apply_pair`
  -- does the `(a,b)` decomposition without any tensor-scalar transport.
  let ℓ : intervalChainComplex.X 0 ⟶ X'.X i :=
    ModuleCat.ofHom
      (((ιTensorObj X intervalChainComplex i 0 i (by simp) ≫ h.1.f i).hom).comp
        ((TensorProduct.mk ℤ (X.X i) (intervalChainComplex.X 0)) x))
  have hpair := intervalChainComplexZeroLinear_apply_pair (ℓ := ℓ) a b
  have hzero : ℓ intervalChainComplexPointZero = (f.f i) x := by
    -- The left endpoint formula identifies the first basis vector `[0]`.
    simpa [ℓ] using tensorIntervalExtension_zeroSummand_apply_pointZero
      (X := X) (X' := X') (f := f) (g := g) h i x
  have hone : ℓ intervalChainComplexPointOne = (g.f i) x := by
    -- The right endpoint formula identifies the second basis vector `[1]`.
    simpa [ℓ] using tensorIntervalExtension_zeroSummand_apply_pointOne
      (X := X) (X' := X') (f := f) (g := g) h i x
  -- Substituting the endpoint values finishes the arbitrary pair computation.
  calc
    (ιTensorObj X intervalChainComplex i 0 i (by simp) ≫ h.1.f i)
        (x ⊗ₜ[ℤ] ((a, b) : intervalChainComplex.X 0)) =
      ℓ ((a, b) : intervalChainComplex.X 0) := by
        change
          (ModuleCat.Hom.hom (ιTensorObj X intervalChainComplex i 0 i (by simp) ≫ h.1.f i))
              (((TensorProduct.mk ℤ (X.X i) (intervalChainComplex.X 0)) x)
                ((a, b) : intervalChainComplex.X 0)) =
            ℓ ((a, b) : intervalChainComplex.X 0)
        rfl
    _ = a • ℓ intervalChainComplexPointZero + b • ℓ intervalChainComplexPointOne := hpair
    _ = a • (f.f i x) + b • (g.f i x) := by rw [hzero, hone]

/-- Helper for Lemma 12.3.4: the endpoint restrictions of a tensor-interval extension determine
its entire degree-`0` visible summand. -/
theorem tensorIntervalExtension_zeroSummand_ofEndpoints
    (h : TensorIntervalExtension f g) (i : ℕ) :
    ιTensorObj X intervalChainComplex i 0 i (by simp) ≫ h.1.f i =
      (𝟙 (X.X i) ⊗ₘ
          ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
        (ρ_ (X.X i)).hom ≫ f.f i
        +
      (𝟙 (X.X i) ⊗ₘ
          ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
        (ρ_ (X.X i)).hom ≫ g.f i := by
  -- Route correction: prove equality on pure tensors and use the curried degree-`0` formula
  -- instead of transporting scalars across the visible tensor carrier.
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x z
  rcases z with ⟨a, b⟩
  -- The left-hand side is already the endpoint interpolation formula on `(a,b)`.
  rw [tensorIntervalExtension_zeroSummand_apply_pair
    (X := X) (X' := X') (f := f) (g := g) (h := h) (i := i) (x := x) (a := a) (b := b)]
  -- The explicit right-hand side evaluates to the same linear combination.
  change
    a • (f.f i x) + b • (g.f i x) =
      (f.f i).hom
          ((ρ_ (X.X i)).hom
            ((X.X i ◁ ModuleCat.ofHom
                (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ))
              (x ⊗ₜ[ℤ] (a, b)))) +
        (g.f i).hom
          ((ρ_ (X.X i)).hom
            ((X.X i ◁ ModuleCat.ofHom
                (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ))
              (x ⊗ₜ[ℤ] (a, b))))
  rw [rightUnitor_hom_whiskerLeft_fst_apply, rightUnitor_hom_whiskerLeft_snd_apply]
  simp

/-- The chain map `tensorIntervalExtensionOfHomotopyHom s` extends `f` and `g` along the
tensor-interval endpoints. -/
theorem tensorIntervalExtensionOfHomotopyHom_isTensorIntervalExtension (s : Homotopy f g) :
    IsTensorIntervalExtension f g (tensorIntervalExtensionOfHomotopyHom s) := by
  constructor
  · apply HomologicalComplex.hom_ext
    intro i
    -- Compute the left endpoint by exposing the right unitor and then pushing `[0]` through
    -- the tensor bifunctor map onto the interval degree-`0` summand.
    rw [tensorIntervalEndpointZero_def]
    simp only [HomologicalComplex.comp_f]
    rw [rightUnitorInv_f_eqZeroSummand (X := X) i]
    let p := (ρ_ (X.X i)).inv ≫ X.X i ◁ 𝟙 (𝟙_ (ModuleCat ℤ))
    change p ≫
        ιTensorObj X ((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) i 0 i (by simp) ≫
          (tensorHom (𝟙 X) intervalChainComplexPointZeroMap).f i ≫
            (tensorIntervalExtensionOfHomotopyHom s).f i =
      f.f i
    calc
      p ≫
          ιTensorObj X ((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) i 0 i
              (by simp) ≫
            (tensorHom (𝟙 X) intervalChainComplexPointZeroMap).f i ≫
              (tensorIntervalExtensionOfHomotopyHom s).f i =
          p ≫
            (ιTensorObj X ((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) i 0 i
                (by simp) ≫
              (tensorHom (𝟙 X) intervalChainComplexPointZeroMap).f i ≫
                (tensorIntervalExtensionOfHomotopyHom s).f i) := by
            rfl
      _ =
          p ≫
            (((MonoidalCategory.curriedTensor (ModuleCat ℤ)).map (𝟙 (X.X i))).app
                (((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).X 0) ≫
              ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).obj (X.X i)).map
                  (intervalChainComplexPointZeroMap.f 0) ≫
                ιTensorObj X intervalChainComplex i 0 i (by simp) ≫
                  (tensorIntervalExtensionOfHomotopyHom s).f i) := by
            simpa using congrArg (fun t ↦ p ≫ t)
              (tensorEndpointMap_assoc (X := X) (X' := X') (u := intervalChainComplexPointZeroMap)
                (k := tensorIntervalExtensionOfHomotopyHom s) i)
      _ =
          p ≫
            (((MonoidalCategory.curriedTensor (ModuleCat ℤ)).map (𝟙 (X.X i))).app
                (((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).X 0) ≫
              ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).obj (X.X i)).map
                  (ModuleCat.ofHom ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).prod 0)) ≫
                ιTensorObj X intervalChainComplex i 0 i (by simp) ≫
                  (tensorIntervalExtensionOfHomotopyHom s).f i) := by
            rfl
      _ =
          p ≫
            (((MonoidalCategory.curriedTensor (ModuleCat ℤ)).map (𝟙 (X.X i))).app
                (((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).X 0) ≫
              ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).obj (X.X i)).map
                  (ModuleCat.ofHom ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).prod 0)) ≫
                ((𝟙 (X.X i) ⊗ₘ
                    ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
                  (ρ_ (X.X i)).hom ≫ f.f i
                  +
                  (𝟙 (X.X i) ⊗ₘ
                    ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
                  (ρ_ (X.X i)).hom ≫ g.f i)) := by
            -- Replace the exposed interval branch by the explicit degree-`0` formula.
            simpa [Category.assoc] using
              congrArg
                (fun t ↦
                  p ≫
                    (((MonoidalCategory.curriedTensor (ModuleCat ℤ)).map (𝟙 (X.X i))).app
                        (((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).X 0) ≫
                      ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).obj (X.X i)).map
                          (ModuleCat.ofHom ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).prod 0)) ≫
                        t))
                (ιTensorObj_tensorIntervalExtensionOfHomotopyHom_f_zeroSummand
                  (X := X) (X' := X') (f := f) (g := g) s i)
      _ = f.f i := by
            -- The `[0]` endpoint kills the `[1]` branch and leaves the `[0]` branch unchanged.
            apply ModuleCat.hom_ext
            ext x
            -- Evaluate the endpoint composite on a pure tensor so only the `[0]` branch remains.
            simp only [ChainComplex.single₀_obj_zero, MonoidalCategory.curriedTensor_obj_obj,
              CategoryTheory.Functor.map_id, NatTrans.id_app,
              MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.id_tensorHom,
              Preadditive.comp_add, ModuleCat.hom_add, ModuleCat.hom_comp,
              LinearMap.comp_id_moduleCat, LinearMap.add_apply, LinearMap.coe_comp,
              Function.comp_apply]
            change
              (f.f i).hom
                  ((ρ_ (X.X i)).hom
                    ((X.X i ◁ ModuleCat.ofHom
                        (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ))
                      (x ⊗ₜ[ℤ] (1, 0)))) +
                (g.f i).hom
                  ((ρ_ (X.X i)).hom
                    ((X.X i ◁ ModuleCat.ofHom
                        (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ))
                      (x ⊗ₜ[ℤ] (1, 0)))) =
              (f.f i).hom x
            rw [rightUnitor_hom_whiskerLeft_fst_oneZero,
              rightUnitor_hom_whiskerLeft_snd_oneZero]
            simp
  · apply HomologicalComplex.hom_ext
    intro i
    -- Compute the right endpoint by the same summandwise reduction, now with the map selecting
    -- the `[1]` generator in degree `0`.
    rw [tensorIntervalEndpointOne_def]
    simp only [HomologicalComplex.comp_f]
    rw [rightUnitorInv_f_eqZeroSummand (X := X) i]
    let p := (ρ_ (X.X i)).inv ≫ X.X i ◁ 𝟙 (𝟙_ (ModuleCat ℤ))
    change p ≫
        ιTensorObj X ((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) i 0 i (by simp) ≫
          (tensorHom (𝟙 X) intervalChainComplexPointOneMap).f i ≫
            (tensorIntervalExtensionOfHomotopyHom s).f i =
      g.f i
    calc
      p ≫
          ιTensorObj X ((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) i 0 i
              (by simp) ≫
            (tensorHom (𝟙 X) intervalChainComplexPointOneMap).f i ≫
              (tensorIntervalExtensionOfHomotopyHom s).f i =
          p ≫
            (ιTensorObj X ((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) i 0 i
                (by simp) ≫
              (tensorHom (𝟙 X) intervalChainComplexPointOneMap).f i ≫
                (tensorIntervalExtensionOfHomotopyHom s).f i) := by
            simp
      _ =
          p ≫
            (((MonoidalCategory.curriedTensor (ModuleCat ℤ)).map (𝟙 (X.X i))).app
                (((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).X 0) ≫
              ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).obj (X.X i)).map
                  (intervalChainComplexPointOneMap.f 0) ≫
                ιTensorObj X intervalChainComplex i 0 i (by simp) ≫
                  (tensorIntervalExtensionOfHomotopyHom s).f i) := by
            simpa using congrArg (fun t ↦ p ≫ t)
              (tensorEndpointMap_assoc (X := X) (X' := X') (u := intervalChainComplexPointOneMap)
                (k := tensorIntervalExtensionOfHomotopyHom s) i)
      _ =
          p ≫
            (((MonoidalCategory.curriedTensor (ModuleCat ℤ)).map (𝟙 (X.X i))).app
                (((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).X 0) ≫
              ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).obj (X.X i)).map
                  (ModuleCat.ofHom ((0 : ℤ →ₗ[ℤ] ℤ).prod (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) ≫
                ιTensorObj X intervalChainComplex i 0 i (by simp) ≫
                  (tensorIntervalExtensionOfHomotopyHom s).f i) := by
            rfl
      _ =
          p ≫
            (((MonoidalCategory.curriedTensor (ModuleCat ℤ)).map (𝟙 (X.X i))).app
                (((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).X 0) ≫
              ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).obj (X.X i)).map
                  (ModuleCat.ofHom ((0 : ℤ →ₗ[ℤ] ℤ).prod (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) ≫
                ((𝟙 (X.X i) ⊗ₘ
                    ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
                  (ρ_ (X.X i)).hom ≫ f.f i
                  +
                  (𝟙 (X.X i) ⊗ₘ
                    ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
                  (ρ_ (X.X i)).hom ≫ g.f i)) := by
            -- Replace the visible degree-`0` summand before selecting the right endpoint.
            simpa [Category.assoc] using
              congrArg
                (fun t ↦
                  p ≫
                    (((MonoidalCategory.curriedTensor (ModuleCat ℤ)).map (𝟙 (X.X i))).app
                        (((ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).X 0) ≫
                      ((MonoidalCategory.curriedTensor (ModuleCat ℤ)).obj (X.X i)).map
                          (ModuleCat.ofHom
                            ((0 : ℤ →ₗ[ℤ] ℤ).prod (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) ≫
                        t))
                (ιTensorObj_tensorIntervalExtensionOfHomotopyHom_f_zeroSummand
                  (X := X) (X' := X') (f := f) (g := g) s i)
      _ = g.f i := by
            -- The `[1]` endpoint kills the `[0]` branch and leaves the `[1]` branch unchanged.
            apply ModuleCat.hom_ext
            ext x
            -- Evaluate the endpoint composite on a pure tensor so only the `[1]` branch remains.
            simp
            change
              (f.f i).hom
                  ((ρ_ (X.X i)).hom
                    ((X.X i ◁ ModuleCat.ofHom
                        (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ))
                      (x ⊗ₜ[ℤ] (0, 1)))) +
                (g.f i).hom
                  ((ρ_ (X.X i)).hom
                    ((X.X i ◁ ModuleCat.ofHom
                        (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ))
                      (x ⊗ₜ[ℤ] (0, 1)))) =
              (g.f i).hom x
            have hfst := rightUnitor_hom_whiskerLeft_fst_zeroOne (A := X.X i) x
            have hsnd := rightUnitor_hom_whiskerLeft_snd_zeroOne (A := X.X i) x
            simpa [hfst, hsnd]

/-- The tensor-interval extension associated to a chain homotopy `s : Homotopy f g`. -/
noncomputable def tensorIntervalExtensionOfHomotopy (s : Homotopy f g) :
    TensorIntervalExtension f g :=
  ⟨tensorIntervalExtensionOfHomotopyHom s,
    tensorIntervalExtensionOfHomotopyHom_isTensorIntervalExtension s⟩

/-- The left endpoint of `tensorIntervalExtensionOfHomotopy s` is `f`. -/
theorem tensorIntervalExtensionOfHomotopy_left_eq (s : Homotopy f g) :
    tensorIntervalEndpointZero (tensorIntervalExtensionOfHomotopy s).1 = f :=
  (tensorIntervalExtensionOfHomotopy s).2.left_eq

/-- The right endpoint of `tensorIntervalExtensionOfHomotopy s` is `g`. -/
theorem tensorIntervalExtensionOfHomotopy_right_eq (s : Homotopy f g) :
    tensorIntervalEndpointOne (tensorIntervalExtensionOfHomotopy s).1 = g :=
  (tensorIntervalExtensionOfHomotopy s).2.right_eq

/-- Helper for Lemma 12.3.4: the degree-`1` visible summand of `tensorIntervalExtensionOfHomotopy`
is the signed homotopy component in the exact subtype-facing normal form used by the left
inverse. -/
theorem ιTensorObj_tensorIntervalExtensionOfHomotopy_f_edgeSummand
    (s : Homotopy f g) (i : ℕ) :
    ιTensorObj X intervalChainComplex i 1 (i + 1) rfl ≫
      (tensorIntervalExtensionOfHomotopy s).1.f (i + 1) =
        (ComplexShape.down ℕ).ε i • ((ρ_ (X.X i)).hom ≫ s.hom i (i + 1)) := by
  -- The subtype wrapper is definitionally transparent, so the hom-level edge formula applies.
  simpa [tensorIntervalExtensionOfHomotopy] using
    (ιTensorObj_tensorIntervalExtensionOfHomotopyHom_f_edgeSummand
      (X := X) (X' := X') (f := f) (g := g) s i)

/-- The chain homotopy extracted from a tensor-interval extension `h`. -/
noncomputable def homotopyOfTensorIntervalExtensionHom
    (h : TensorIntervalExtension f g) (i j : ℕ) : X.X i ⟶ X'.X j :=
  if hij : j = i + 1 then
    -- Route correction: use the same tensor sign as the forward construction.
    (ComplexShape.down ℕ).ε i •
      ((ρ_ (X.X i)).inv ≫
      ιTensorObj X intervalChainComplex i 1 j hij.symm ≫ h.1.f j
      )
  else
    0

/-- Helper for Lemma 12.3.4: on the diagonal `j = i + 1`, the extracted homotopy is the signed
edge summand of the tensor-interval map. -/
theorem homotopyOfTensorIntervalExtensionHom_diag
    (h : TensorIntervalExtension f g) (i : ℕ) :
    homotopyOfTensorIntervalExtensionHom h i (i + 1) =
      (ComplexShape.down ℕ).ε i •
        ((ρ_ (X.X i)).inv ≫
          ιTensorObj X intervalChainComplex i 1 (i + 1) rfl ≫ h.1.f (i + 1)) := by
  -- On the diagonal, the defining `if` picks exactly the signed edge summand.
  simp [homotopyOfTensorIntervalExtensionHom]

/-- Helper for Lemma 12.3.4: evaluating the visible edge summand of a tensor-interval extension
on the generator `1` recovers the extracted homotopy up to the standard tensor sign. -/
theorem edgeSummand_apply_one_eq_signed_homotopy
    (h : TensorIntervalExtension f g) (i : ℕ) (x : X.X i) :
    (ιTensorObj X intervalChainComplex i 1 (i + 1) rfl ≫ h.1.f (i + 1))
        (x ⊗ₜ[ℤ] (1 : ℤ)) =
      (ComplexShape.down ℕ).ε i • homotopyOfTensorIntervalExtensionHom h i (i + 1) x := by
  have hdiag :=
    congrArg (fun t ↦ (ComplexShape.down ℕ).ε i • t)
      (homotopyOfTensorIntervalExtensionHom_diag
        (X := X) (X' := X') (f := f) (g := g) (h := h) i)
  have happly :=
    congrArg (fun t : X.X i ⟶ X'.X (i + 1) => t x) hdiag
  simpa [ModuleCat.MonoidalCategory.rightUnitor_inv_apply, smul_smul,
    ComplexShape.ε_down_ℕ, mul_assoc, mul_left_comm, mul_comm] using happly.symm

/-- Helper for Lemma 12.3.4: evaluating the degree-`0` edge boundary on `x ⊗ [I]` gives the
endpoint difference `f x - g x`. -/
theorem tensorEdgeSummand_d_zero_postcompose_apply_one
    (h : TensorIntervalExtension f g) (x : X.X 0) :
    ((ιTensorObj X intervalChainComplex 0 1 1 rfl ≫
          (X ⊗ intervalChainComplex).d 1 0 ≫ h.1.f 0)
        (x ⊗ₜ[ℤ] (1 : ℤ))) =
      f.f 0 x - g.f 0 x := by
  -- Evaluate the exposed edge-boundary identity on the generator `[I]`.
  have hpost :=
    congrArg
      (fun t : X.X 0 ⊗ intervalChainComplex.X 1 ⟶ X'.X 0 ↦
        t (x ⊗ₜ[ℤ] (1 : ℤ)))
      (tensorEdgeSummand_d_zero_postcompose
        (X := X) (X' := X') (φ := h.1.f 0))
  calc
    ((ιTensorObj X intervalChainComplex 0 1 1 rfl ≫
          (X ⊗ intervalChainComplex).d 1 0 ≫ h.1.f 0)
        (x ⊗ₜ[ℤ] (1 : ℤ))) =
      ((ιTensorObj X intervalChainComplex 0 0 0 rfl ≫ h.1.f 0)
        (x ⊗ₜ[ℤ] ((1, -1) : intervalChainComplex.X 0))) := by
        simpa [whiskerRight_apply_tmul, intervalChainComplex_d_one_zero_apply] using hpost
    _ = f.f 0 x - g.f 0 x := by
        rw [tensorIntervalExtension_zeroSummand_apply_pair]
        simp [sub_eq_add_neg]

/-- Helper for Lemma 12.3.4: the evaluated `D₁` branch of the successor edge boundary is the
signed predecessor homotopy term. -/
theorem tensorEdgeSuccessorD1_apply_one
    (h : TensorIntervalExtension f g) (n : ℕ) (x : X.X (n + 1)) :
    (ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (n + 1, 1) •
      ((ιTensorObj X intervalChainComplex n 1 (n + 1) rfl ≫ h.1.f (n + 1))
        (X.d (n + 1) n x ⊗ₜ[ℤ] (1 : ℤ)))) =
      (ComplexShape.down ℕ).ε n •
        homotopyOfTensorIntervalExtensionHom h n (n + 1) (X.d (n + 1) n x) := by
  -- The `D₁` branch is exactly the extracted predecessor homotopy term.
  rw [show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (n + 1, 1) = 1 by rfl]
  rw [edgeSummand_apply_one_eq_signed_homotopy
    (X := X) (X' := X') (f := f) (g := g) (h := h) (i := n) (x := X.d (n + 1) n x)]
  simp

/-- Helper for Lemma 12.3.4: the evaluated `D₂` branch of the successor edge boundary is the
signed endpoint difference term. -/
theorem tensorEdgeSuccessorD2_apply_pairOneNegOne
    (h : TensorIntervalExtension f g) (n : ℕ) (x : X.X (n + 1)) :
    (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (n + 1, 1) •
      ((ιTensorObj X intervalChainComplex (n + 1) 0 (n + 1) (by simp) ≫ h.1.f (n + 1))
        (x ⊗ₜ[ℤ] ((1, -1) : intervalChainComplex.X 0)))) =
      (ComplexShape.down ℕ).ε (n + 1) •
        (f.f (n + 1) x - g.f (n + 1) x) := by
  -- The `D₂` branch is the visible degree-`0` endpoint interpolation evaluated at `(1,-1)`.
  rw [show ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (n + 1, 1) = (ComplexShape.down ℕ).ε (n + 1) by rfl]
  rw [tensorIntervalExtension_zeroSummand_apply_pair
    (X := X) (X' := X') (f := f) (g := g) (h := h) (i := n + 1) (x := x)
    (a := 1) (b := -1)]
  simp [sub_eq_add_neg]

/-- Helper for Lemma 12.3.4: evaluating the positive-degree edge boundary on `x ⊗ [I]` separates
the previous homotopy term from the endpoint difference term. -/
theorem tensorEdgeSummand_d_succ_postcompose_apply_one
    (h : TensorIntervalExtension f g) (n : ℕ) (x : X.X (n + 1)) :
    ((ιTensorObj X intervalChainComplex (n + 1) 1 (n + 2) rfl ≫
          (X ⊗ intervalChainComplex).d (n + 2) (n + 1) ≫ h.1.f (n + 1))
        (x ⊗ₜ[ℤ] (1 : ℤ))) =
      (ComplexShape.down ℕ).ε n •
        homotopyOfTensorIntervalExtensionHom h n (n + 1) (X.d (n + 1) n x) +
      (ComplexShape.down ℕ).ε (n + 1) •
        (f.f (n + 1) x - g.f (n + 1) x) := by
  -- Evaluate the exposed `D₁ + D₂` formula at the generator `[I] = 1`.
  calc
    ((ιTensorObj X intervalChainComplex (n + 1) 1 (n + 2) rfl ≫
          (X ⊗ intervalChainComplex).d (n + 2) (n + 1) ≫ h.1.f (n + 1))
        (x ⊗ₜ[ℤ] (1 : ℤ))) =
      ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (n + 1, 1) •
        ((ιTensorObj X intervalChainComplex n 1 (n + 1) rfl ≫ h.1.f (n + 1))
          (X.d (n + 1) n x ⊗ₜ[ℤ] (1 : ℤ))) +
      ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (n + 1, 1) •
        ((ιTensorObj X intervalChainComplex (n + 1) 0 (n + 1) (by simp) ≫ h.1.f (n + 1))
          (x ⊗ₜ[ℤ] ((1, -1) : intervalChainComplex.X 0))) := by
            simpa using tensorEdgeSummand_d_succ_postcompose_apply_int_split
              (X := X) (X' := X') (n := n) (φ := h.1.f (n + 1))
              (x := x) (m := (1 : ℤ))
    _ =
      (ComplexShape.down ℕ).ε n •
        homotopyOfTensorIntervalExtensionHom h n (n + 1) (X.d (n + 1) n x) +
      (ComplexShape.down ℕ).ε (n + 1) •
        (f.f (n + 1) x - g.f (n + 1) x) := by
          rw [tensorEdgeSuccessorD1_apply_one
            (X := X) (X' := X') (f := f) (g := g) (h := h) (n := n) (x := x)]
          rw [tensorEdgeSuccessorD2_apply_pairOneNegOne
            (X := X) (X' := X') (f := f) (g := g) (h := h) (n := n) (x := x)]

/-- Helper for Lemma 12.3.4: the degree-`0` component of the extracted homotopy satisfies the
rearranged identity `d' (s x) = f x - g x`. -/
theorem homotopyOfTensorIntervalExtensionHom_comm_zero_apply_sub
    (h : TensorIntervalExtension f g) (x : X.X 0) :
    X'.d 1 0 (homotopyOfTensorIntervalExtensionHom h 0 1 x) =
      f.f 0 x - g.f 0 x := by
  -- Evaluate the chain-map equation on the visible edge generator `x ⊗ [I]`.
  have hcomm :
      ιTensorObj X intervalChainComplex 0 1 1 rfl ≫ h.1.f 1 ≫ X'.d 1 0 =
        ιTensorObj X intervalChainComplex 0 1 1 rfl ≫
          (X ⊗ intervalChainComplex).d 1 0 ≫ h.1.f 0 := by
    have hpre :=
      congrArg
        (fun t : (X ⊗ intervalChainComplex).X 1 ⟶ X'.X 0 ↦
          ιTensorObj X intervalChainComplex 0 1 1 rfl ≫ t)
        (h.1.comm 1 0)
    simpa [Category.assoc] using hpre
  have happly :=
    congrArg
      (fun t : X.X 0 ⊗ intervalChainComplex.X 1 ⟶ X'.X 0 ↦
        t (x ⊗ₜ[ℤ] (1 : ℤ)))
      hcomm
  have hedge :=
    congrArg
      (X'.d 1 0)
      (edgeSummand_apply_one_eq_signed_homotopy
        (X := X) (X' := X') (f := f) (g := g) (h := h) 0 x)
  calc
    X'.d 1 0 (homotopyOfTensorIntervalExtensionHom h 0 1 x) =
      X'.d 1 0
        ((ιTensorObj X intervalChainComplex 0 1 1 rfl ≫ h.1.f 1)
          (x ⊗ₜ[ℤ] (1 : ℤ))) := by
        symm
        simpa [ComplexShape.ε_down_ℕ] using hedge
    _ =
      ((ιTensorObj X intervalChainComplex 0 1 1 rfl ≫
            (X ⊗ intervalChainComplex).d 1 0 ≫ h.1.f 0)
          (x ⊗ₜ[ℤ] (1 : ℤ))) := happly
    _ = f.f 0 x - g.f 0 x := tensorEdgeSummand_d_zero_postcompose_apply_one
      (X := X) (X' := X') (f := f) (g := g) h x

/-- Helper for Lemma 12.3.4: multiplying the signed endpoint expression by the same visible sign
collapses the two sign factors and recovers `-a + b`. -/
theorem edgeSignCancel {A : ModuleCat ℤ} (n : ℕ) (a b : A) :
    (ComplexShape.down ℕ).ε (n + 1) •
        (-(ComplexShape.down ℕ).ε (n + 1) • a + (ComplexShape.down ℕ).ε (n + 1) • b) =
      -a + b := by
  -- Split on the only two possible signs `1` and `-1` for an integer unit.
  rcases Int.units_eq_one_or ((ComplexShape.down ℕ).ε (n + 1)) with h | h <;>
    simp [h, Units.smul_def] <;> abel

/-- Helper for Lemma 12.3.4: the positive-degree component of the extracted homotopy satisfies the
rearranged identity `d' (s x) = - s (d x) + (f x - g x)`. -/
theorem homotopyOfTensorIntervalExtensionHom_comm_succ_apply
    (h : TensorIntervalExtension f g) (n : ℕ) (x : X.X (n + 1)) :
    X'.d (n + 2) (n + 1)
        (homotopyOfTensorIntervalExtensionHom h (n + 1) (n + 2) x) =
      -homotopyOfTensorIntervalExtensionHom h n (n + 1) (X.d (n + 1) n x) +
        (f.f (n + 1) x - g.f (n + 1) x) := by
  have hcomm :
      ιTensorObj X intervalChainComplex (n + 1) 1 (n + 2) rfl ≫ h.1.f (n + 2) ≫
          X'.d (n + 2) (n + 1) =
        ιTensorObj X intervalChainComplex (n + 1) 1 (n + 2) rfl ≫
          (X ⊗ intervalChainComplex).d (n + 2) (n + 1) ≫ h.1.f (n + 1) := by
    -- Precompose the chain-map equation with the visible edge summand.
    have hpre :=
      congrArg
        (fun t : (X ⊗ intervalChainComplex).X (n + 2) ⟶ X'.X (n + 1) ↦
          ιTensorObj X intervalChainComplex (n + 1) 1 (n + 2) rfl ≫ t)
        (h.1.comm (n + 2) (n + 1))
    simpa [Category.assoc] using hpre
  have happly :=
    congrArg
      (fun t : X.X (n + 1) ⊗ intervalChainComplex.X 1 ⟶ X'.X (n + 1) ↦
        t (x ⊗ₜ[ℤ] (1 : ℤ)))
      hcomm
  have hedge :
      ((ιTensorObj X intervalChainComplex (n + 1) 1 (n + 2) rfl ≫
            h.1.f (n + 2) ≫ X'.d (n + 2) (n + 1))
          (x ⊗ₜ[ℤ] (1 : ℤ))) =
        (ComplexShape.down ℕ).ε (n + 1) •
          X'.d (n + 2) (n + 1)
            (homotopyOfTensorIntervalExtensionHom h (n + 1) (n + 2) x) := by
    -- The visible edge term is the extracted homotopy up to the standard tensor sign.
    change X'.d (n + 2) (n + 1)
        ((ιTensorObj X intervalChainComplex (n + 1) 1 (n + 2) rfl ≫ h.1.f (n + 2))
          (x ⊗ₜ[ℤ] (1 : ℤ))) =
      (ComplexShape.down ℕ).ε (n + 1) •
        X'.d (n + 2) (n + 1)
          (homotopyOfTensorIntervalExtensionHom h (n + 1) (n + 2) x)
    rw [edgeSummand_apply_one_eq_signed_homotopy
      (X := X) (X' := X') (f := f) (g := g) (h := h) (i := n + 1) (x := x)]
    simp
  have hsigned :
      (ComplexShape.down ℕ).ε (n + 1) •
        X'.d (n + 2) (n + 1)
          (homotopyOfTensorIntervalExtensionHom h (n + 1) (n + 2) x) =
      (ComplexShape.down ℕ).ε n •
          homotopyOfTensorIntervalExtensionHom h n (n + 1) (X.d (n + 1) n x) +
        (ComplexShape.down ℕ).ε (n + 1) •
          (f.f (n + 1) x - g.f (n + 1) x) := by
    calc
      (ComplexShape.down ℕ).ε (n + 1) •
          X'.d (n + 2) (n + 1)
            (homotopyOfTensorIntervalExtensionHom h (n + 1) (n + 2) x) =
        ((ιTensorObj X intervalChainComplex (n + 1) 1 (n + 2) rfl ≫
              h.1.f (n + 2) ≫ X'.d (n + 2) (n + 1))
            (x ⊗ₜ[ℤ] (1 : ℤ))) := by
              symm
              exact hedge
      _ =
        ((ιTensorObj X intervalChainComplex (n + 1) 1 (n + 2) rfl ≫
              (X ⊗ intervalChainComplex).d (n + 2) (n + 1) ≫ h.1.f (n + 1))
            (x ⊗ₜ[ℤ] (1 : ℤ))) := happly
      _ =
        (ComplexShape.down ℕ).ε n •
            homotopyOfTensorIntervalExtensionHom h n (n + 1) (X.d (n + 1) n x) +
          (ComplexShape.down ℕ).ε (n + 1) •
            (f.f (n + 1) x - g.f (n + 1) x) := tensorEdgeSummand_d_succ_postcompose_apply_one
              (X := X) (X' := X') (f := f) (g := g) (h := h) (n := n) (x := x)
  have hε :
      (ComplexShape.down ℕ).ε n =
        -(ComplexShape.down ℕ).ε (n + 1) := by
    simpa [ComplexShape.down_Rel] using
      (ComplexShape.ε_succ (c := ComplexShape.down ℕ)
        (p := n + 1) (q := n) (by simp [ComplexShape.down_Rel]))
  -- Multiply once more by the visible sign to recover the unsigned homotopy identity.
  rw [hε] at hsigned
  have hmult :=
    congrArg
      (fun y : X'.X (n + 1) => (ComplexShape.down ℕ).ε (n + 1) • y)
      hsigned
  calc
    X'.d (n + 2) (n + 1) (homotopyOfTensorIntervalExtensionHom h (n + 1) (n + 2) x) =
      (ComplexShape.down ℕ).ε (n + 1) •
        (-(ComplexShape.down ℕ).ε (n + 1) •
            homotopyOfTensorIntervalExtensionHom h n (n + 1) (X.d (n + 1) n x) +
          (ComplexShape.down ℕ).ε (n + 1) •
            (f.f (n + 1) x - g.f (n + 1) x)) := by
              simpa [ComplexShape.ε_down_ℕ, sub_eq_add_neg, smul_smul, Int.units_mul_self,
                one_smul, mul_assoc, mul_left_comm, mul_comm] using hmult
    _ = -homotopyOfTensorIntervalExtensionHom h n (n + 1) (X.d (n + 1) n x) +
          (f.f (n + 1) x - g.f (n + 1) x) := by
            -- Use the dedicated visible-sign cancellation lemma instead of distributing units
            -- by hand through the additive expression.
            simpa using edgeSignCancel (n := n)
              (a := homotopyOfTensorIntervalExtensionHom h n (n + 1) (X.d (n + 1) n x))
              (b := f.f (n + 1) x - g.f (n + 1) x)

/-- `homotopyOfTensorIntervalExtensionHom h` vanishes away from the `j = i + 1` diagonal. -/
theorem homotopyOfTensorIntervalExtensionHom_zero (h : TensorIntervalExtension f g) :
    ∀ i j, ¬ (ComplexShape.down ℕ).Rel j i →
      homotopyOfTensorIntervalExtensionHom h i j = 0 := by
  intro i j hji
  -- The extracted homotopy is defined by an `if` on the same diagonal relation.
  by_cases hij : j = i + 1
  · exfalso
    exact hji hij.symm
  · simp [homotopyOfTensorIntervalExtensionHom, hij]

/-- `homotopyOfTensorIntervalExtensionHom h` satisfies the homotopy identity. -/
theorem homotopyOfTensorIntervalExtensionHom_comm (h : TensorIntervalExtension f g) :
    ∀ i,
      f.f i =
        dNext i (homotopyOfTensorIntervalExtensionHom h) +
          prevD i (homotopyOfTensorIntervalExtensionHom h) +
            g.f i := by
  intro i
  cases i with
  | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      ext x
      have hd :=
        homotopyOfTensorIntervalExtensionHom_comm_zero_apply_sub
          (X := X) (X' := X') (f := f) (g := g) (h := h) x
      have hd' :=
        congrArg (fun y : X'.X 0 => y + g.f 0 x) hd
      -- Add back the endpoint term `g x` to recover the degree-`0` homotopy identity.
      simpa [HomologicalComplex.comp_f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using hd'.symm
  | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      ext x
      have hd :=
        homotopyOfTensorIntervalExtensionHom_comm_succ_apply
          (X := X) (X' := X') (f := f) (g := g) (h := h) n x
      have hd' :=
        congrArg
          (fun y : X'.X (n + 1) =>
            y + homotopyOfTensorIntervalExtensionHom h n (n + 1) (X.d (n + 1) n x) +
              g.f (n + 1) x)
          hd
      -- Add back the previous homotopy term and the endpoint `g x` to recover the usual
      -- positive-degree homotopy identity.
      simpa [HomologicalComplex.comp_f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using hd'.symm

/-- The chain homotopy extracted from a tensor-interval extension `h`. -/
noncomputable def homotopyOfTensorIntervalExtension (h : TensorIntervalExtension f g) :
    Homotopy f g where
  hom := homotopyOfTensorIntervalExtensionHom h
  zero := homotopyOfTensorIntervalExtensionHom_zero h
  comm := homotopyOfTensorIntervalExtensionHom_comm h

/-- Lemma 12.3.4: chain homotopies `s : Homotopy f g` are equivalent to chain maps
`h : X ⊗ I ⟶ X'` whose restrictions along `X ⊗ [0]` and `X ⊗ [1]` are `f` and `g`. -/
theorem homotopyEquivTensorIntervalExtension_left_inv :
    Function.LeftInverse
      (homotopyOfTensorIntervalExtension : TensorIntervalExtension f g → Homotopy f g)
      (tensorIntervalExtensionOfHomotopy : Homotopy f g → TensorIntervalExtension f g) := by
  intro s
  refine Homotopy.ext ?_
  funext i j
  simp only [homotopyOfTensorIntervalExtension]
  by_cases hij : j = i + 1
  · subst hij
    -- Compare the diagonal component through the extracted edge summand.
    rw [homotopyOfTensorIntervalExtensionHom_diag]
    have hEdge :=
      congrArg
        (fun t ↦ (ComplexShape.down ℕ).ε i • ((ρ_ (X.X i)).inv ≫ t))
        (ιTensorObj_tensorIntervalExtensionOfHomotopy_f_edgeSummand
          (X := X) (X' := X') (f := f) (g := g) (s := s) i)
    simpa [Category.assoc] using hEdge.trans (by
      simp only [Linear.comp_units_smul, smul_smul, Iso.inv_hom_id_assoc, Int.units_mul_self,
        one_smul])
  · -- Away from the diagonal both homotopies vanish, so only the zero API is needed.
    rw [homotopyOfTensorIntervalExtensionHom_zero
      (h := tensorIntervalExtensionOfHomotopy s) (i := i) (j := j)
      (by
        intro hji
        exact hij hji.symm)]
    rw [s.zero i j (by
      intro hji
      exact hij hji.symm)]

/-- The tensor-interval extension and extracted homotopy constructions are mutually inverse on
tensor-interval extensions. -/
theorem homotopyEquivTensorIntervalExtension_right_inv :
    Function.RightInverse
      (homotopyOfTensorIntervalExtension : TensorIntervalExtension f g → Homotopy f g)
      (tensorIntervalExtensionOfHomotopy : Homotopy f g → TensorIntervalExtension f g) := by
  intro h
  -- Compare the underlying chain maps summandwise on the visible tensor decomposition.
  apply Subtype.ext
  apply HomologicalComplex.hom_ext
  intro j
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i i₂ hij
  cases i₂ with
  | zero =>
      subst hij
      -- The degree-`0` branch is determined entirely by the endpoint restrictions.
      have hzeroSummand :
          ιTensorObj X intervalChainComplex i 0 i (by simp) ≫
              (tensorIntervalExtensionOfHomotopy (homotopyOfTensorIntervalExtension h)).1.f i =
            (𝟙 (X.X i) ⊗ₘ
                ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
              (ρ_ (X.X i)).hom ≫ f.f i
              +
            (𝟙 (X.X i) ⊗ₘ
                ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ : (ℤ × ℤ) →ₗ[ℤ] ℤ)) ≫
              (ρ_ (X.X i)).hom ≫ g.f i := by
        simpa [tensorIntervalExtensionOfHomotopy] using
          (ιTensorObj_tensorIntervalExtensionOfHomotopyHom_f_zeroSummand
            (X := X) (X' := X') (f := f) (g := g)
            (s := homotopyOfTensorIntervalExtension h) i)
      exact hzeroSummand.trans
        (tensorIntervalExtension_zeroSummand_ofEndpoints
          (X := X) (X' := X') (f := f) (g := g) h i).symm
  | succ i₂ =>
      cases i₂ with
      | zero =>
          subst hij
          -- The degree-`1` branch recovers the extracted signed homotopy component.
          change
            ιTensorObj X intervalChainComplex i 1 (i + 1) rfl ≫
                (tensorIntervalExtensionOfHomotopy (homotopyOfTensorIntervalExtension h)).1.f
                  (i + 1) =
              ιTensorObj X intervalChainComplex i 1 (i + 1) rfl ≫ h.1.f (i + 1)
          rw [ιTensorObj_tensorIntervalExtensionOfHomotopy_f_edgeSummand
            (X := X) (X' := X') (f := f) (g := g)
            (s := homotopyOfTensorIntervalExtension h) i]
          change
            (ComplexShape.down ℕ).ε i •
                ((ρ_ (X.X i)).hom ≫ homotopyOfTensorIntervalExtensionHom h i (i + 1)) =
              ιTensorObj X intervalChainComplex i 1 (i + 1) rfl ≫ h.1.f (i + 1)
          rw [homotopyOfTensorIntervalExtensionHom_diag
            (X := X) (X' := X') (f := f) (g := g) (h := h) i]
          simp only [Linear.comp_units_smul, smul_smul, Iso.hom_inv_id_assoc,
            Int.units_mul_self, one_smul]
          rfl
      | succ k =>
          -- Higher interval degrees are the trivial `Fin 0` carrier, so both summand maps vanish.
          apply ModuleCat.MonoidalCategory.tensor_ext
          intro x z
          have hz : z = 0 := by
            funext t
            exact Fin.elim0 t
          subst hz
          simp [tensorIntervalExtensionOfHomotopy, tensorIntervalExtensionOfHomotopyHom,
            tensorIntervalExtensionOfHomotopyApp]

/-- Lemma 12.3.4: chain homotopies `s : Homotopy f g` are equivalent to chain maps
`h : X ⊗ I ⟶ X'` whose restrictions along `X ⊗ [0]` and `X ⊗ [1]` are `f` and `g`. -/
noncomputable def homotopyEquivTensorIntervalExtension (f g : X ⟶ X') :
    Homotopy f g ≃ TensorIntervalExtension f g where
  toFun := tensorIntervalExtensionOfHomotopy
  invFun := homotopyOfTensorIntervalExtension
  left_inv := homotopyEquivTensorIntervalExtension_left_inv
  right_inv := homotopyEquivTensorIntervalExtension_right_inv

/-- `homotopyEquivTensorIntervalExtension f g` sends a homotopy to its tensor-interval extension. -/
@[simp]
theorem homotopyEquivTensorIntervalExtension_apply (s : Homotopy f g) :
    homotopyEquivTensorIntervalExtension f g s = tensorIntervalExtensionOfHomotopy s := rfl
