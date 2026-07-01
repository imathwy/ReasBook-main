import Mathlib

open CategoryTheory
open CategoryTheory.Limits
open HomogeneousIdeal
open scoped DirectSum TensorProduct

universe u

noncomputable section

section

/- Domain triage:
* `source-facing`: Lemma `10.98.4` says that when the canonical comparison from the
  `I`-adic completion of a graded module `M` to the inverse limit of a graded inverse system
  `(G_n)` is an isomorphism, then each induced degreewise map `M_d → lim_n G_{n,d}` is an
  isomorphism, for a homogeneous ideal `I` contained in the irrelevant ideal `𝒜₊`.
* `core/canonical` owners: the graded-module owners `DirectSum.Decomposition` and
  `SetLike.GradedSMul`, the degree-zero owner ring `𝒜 0`, the inverse-limit owner `limit G_`, the
  canonical projections `limit.π`, the quotient-lift owner `Submodule.liftQ`, the completion
  coordinates `AdicCompletion.eval`, and the canonical irrelevant ideal `𝒜₊`.
* `bridge/view`: the degreewise inverse system `d ↦ (G_{n,d})` and the induced comparison
  `M_d → lim_n G_{n,d}` are derived from the owner data. Each homogeneous piece is viewed
  canonically as an `A₀ = 𝒜 0`-submodule by restricting scalars to degree zero, rather than as an
  `A`-submodule.

Relevant owner declarations sampled for this refinement:
* `DirectSum.Decomposition`
* `SetLike.GradedSMul`
* `SetLike.GradeZero.instCommRing`
* `Module.restrictScalars`
* `CategoryTheory.Limits.limit.lift`
* `CategoryTheory.Limits.limit.π`
* `Submodule.liftQ`
* `AdicCompletion.eval`
* `AdicCompletion.ofTensorProduct`

Primitive data are the graded module `M`, the graded inverse system `G_`, its degree-preserving
transition maps, the compatible family `φ_n : M → G_n`, and the stagewise annihilation
`I^n G_n = 0` together with the source-side relevance hypothesis `I ≤ 𝒜₊`. The completion
comparison, the tensor-product comparison, and all degreewise systems/maps are derived API and are
defined canonically below. -/

local instance : AddAction ℕ ℤ := AddAction.compHom ℤ Int.ofNatHom.toAddMonoidHom

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule A A) [GradedRing 𝒜]
variable {M : Type u} [AddCommGroup M] [Module A M]

local instance degreeZeroModule (X : Type u) [AddCommGroup X] [Module A X] :
    Module (𝒜 0) X :=
  Module.restrictScalars (𝒜 0) A X

private theorem pow_smul_top_le_ker_stageMap
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (hGI :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (n : ℕ+) :
    I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A M) ≤ LinearMap.ker (φ n) := by
  intro x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y hy
    change (φ n) (a • y) = 0
    have hmem :
        a • (φ n y) ∈ I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) :=
      Submodule.smul_mem_smul ha (by simp)
    have hzero : a • φ n y = 0 := by
      simpa [hGI n] using hmem
    simpa using hzero
  · intro x y hx hy
    exact LinearMap.mem_ker.2 <| by
      simp [LinearMap.mem_ker.1 hx, LinearMap.mem_ker.1 hy]

/-- The canonical factorization `M / I^n M → G_n` induced by `φ_n`, using that `I^n` annihilates
the `n`th stage. -/
private abbrev completionStageMap
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (hGI :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (n : ℕ+) :
    M ⧸ (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A M)) →ₗ[A]
      G_.obj (OrderDual.toDual n) :=
  (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A M)).liftQ (φ n)
    (pow_smul_top_le_ker_stageMap 𝒜 I G_ hGI φ n)

private theorem completionStageMap_compat
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (hGI :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (hφn :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        (G_.map f).hom ∘ₗ φ (OrderDual.ofDual i) = φ (OrderDual.ofDual j))
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    (G_.map f).hom ∘ₗ completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual i) =
      completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual j) ∘ₗ
        AdicCompletion.transitionMap I.toIdeal M
          ((show ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) from
            (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f))) := by
  ext x
  change
    (G_.map f).hom
        ((completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual i))
          (Submodule.Quotient.mk x)) =
      (completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual j))
        (Submodule.Quotient.mk x)
  simpa [completionStageMap] using congrArg (fun g ↦ g x) (hφn f)

/-- The canonical comparison `AdicCompletion I M → lim_n G_n` induced by the compatible family
`φ_n : M → G_n`. -/
abbrev completionComparison
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (hGI :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (hφn :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        (G_.map f).hom ∘ₗ φ (OrderDual.ofDual i) = φ (OrderDual.ofDual j)) :
    ModuleCat.of A (AdicCompletion I.toIdeal M) ⟶ limit G_ :=
  limit.lift G_
    { pt := ModuleCat.of A (AdicCompletion I.toIdeal M)
      π :=
        { app := fun n ↦
            ModuleCat.ofHom <|
              completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual n) ∘ₗ
                AdicCompletion.eval I.toIdeal M ((OrderDual.ofDual n : ℕ+) : ℕ)
          naturality := by
            intro i j f
            ext x
            let hle :
                ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) :=
              show ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) from
                (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f)
            let xi := AdicCompletion.eval I.toIdeal M ((OrderDual.ofDual i : ℕ+) : ℕ) x
            have hcompat :
                (G_.map f).hom ((completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual i)) xi) =
                  (completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual j))
                    (AdicCompletion.transitionMap I.toIdeal M hle xi) := by
              exact congrArg (fun g ↦ g xi) (completionStageMap_compat 𝒜 I G_ hGI φ hφn f)
            exact
              (congrArg
                (completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual j))
                (x.property hle)).symm.trans hcompat.symm } }

/-- The canonical tensor-product comparison
`AdicCompletion I.toIdeal A ⊗[A] M → lim_n G_n`, obtained by composing
`AdicCompletion.ofTensorProduct I.toIdeal M` with `completionComparison`. -/
abbrev tensorProductComparison
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (hGI :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (hφn :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        (G_.map f).hom ∘ₗ φ (OrderDual.ofDual i) = φ (OrderDual.ofDual j)) :
    ModuleCat.of A (AdicCompletion I.toIdeal A ⊗[A] M) ⟶ limit G_ :=
  ModuleCat.ofHom <|
    (completionComparison 𝒜 I G_ hGI φ hφn).hom ∘ₗ
      LinearMap.restrictScalars A (AdicCompletion.ofTensorProduct I.toIdeal M)

/-- A homogeneous degree piece, viewed canonically as a module over the degree-zero ring
`A₀ = 𝒜 0`. -/
private def degreeZeroPiece
    {X : Type u} [AddCommGroup X] [Module A X]
    (ℬ : ℤ → Submodule ℤ X) [SetLike.GradedSMul 𝒜 ℬ]
    (d : ℤ) :
    Submodule (𝒜 0) X where
  carrier := ℬ d
  zero_mem' := (ℬ d).zero_mem
  add_mem' := fun hx hy ↦ (ℬ d).add_mem hx hy
  smul_mem' := by
    intro a x hx
    change ((a : A) • x) ∈ ℬ d
    simpa using (SetLike.GradedSMul.smul_mem a.2 hx : ((a : A) • x) ∈ ℬ (0 +ᵥ d))

/-- The canonical inverse system formed by the degree-`d` graded pieces `G_{n,d}`. -/
def degreewiseSystem
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (h𝒢 :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j) (d : ℤ)
        {x : G_.obj i}, x ∈ 𝒢 (OrderDual.ofDual i) d →
          (G_.map f).hom x ∈ 𝒢 (OrderDual.ofDual j) d)
    (d : ℤ) :
    OrderDual ℕ+ ⥤ ModuleCat.{u} (𝒜 0) where
  obj n := ModuleCat.of (𝒜 0) (degreeZeroPiece 𝒜 (𝒢 (OrderDual.ofDual n)) d)
  map {i j} f := ModuleCat.ofHom
    { toFun := fun x ↦ ⟨(G_.map f).hom x.1, h𝒢 f d x.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change (G_.map f).hom (x.1 + y.1) = (G_.map f).hom x.1 + (G_.map f).hom y.1
        exact (G_.map f).hom.map_add x.1 y.1
      map_smul' := by
        intro a x
        apply Subtype.ext
        change (G_.map f).hom ((a : A) • x.1) = (a : A) • (G_.map f).hom x.1
        exact (G_.map f).hom.map_smul (a : A) x.1 }
  map_id i := by
    ext x
    change (G_.map (𝟙 i)).hom x.1 = x.1
    simp
  map_comp f g := by
    ext x
    change (G_.map (f ≫ g)).hom x.1 = (G_.map g).hom ((G_.map f).hom x.1)
    simp

/-- The canonical map `M_d → lim_n G_{n,d}` induced by the compatible degree-preserving family
`φ_n : M → G_n`. -/
abbrev degreewiseLimitMap
    (𝓜 : ℤ → Submodule ℤ M)
    [SetLike.GradedSMul 𝒜 𝓜]
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (h𝒢 :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j) (d : ℤ)
        {x : G_.obj i}, x ∈ 𝒢 (OrderDual.ofDual i) d →
          (G_.map f).hom x ∈ 𝒢 (OrderDual.ofDual j) d)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (hφn :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        (G_.map f).hom ∘ₗ φ (OrderDual.ofDual i) = φ (OrderDual.ofDual j))
    (hφ :
      ∀ n d {x : M}, x ∈ 𝓜 d → φ n x ∈ 𝒢 n d)
    (d : ℤ) :
    ModuleCat.of (𝒜 0) (degreeZeroPiece 𝒜 𝓜 d) ⟶ limit (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) :=
  limit.lift (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d)
    { pt := ModuleCat.of (𝒜 0) (degreeZeroPiece 𝒜 𝓜 d)
      π :=
        { app := fun n ↦
            ModuleCat.ofHom
              { toFun := fun x ↦ ⟨φ (OrderDual.ofDual n) x.1, hφ (OrderDual.ofDual n) d x.2⟩
                map_add' := by
                  intro x y
                  apply Subtype.ext
                  change φ (OrderDual.ofDual n) (x.1 + y.1) =
                    φ (OrderDual.ofDual n) x.1 + φ (OrderDual.ofDual n) y.1
                  exact (φ (OrderDual.ofDual n)).map_add x.1 y.1
                map_smul' := by
                  intro a x
                  apply Subtype.ext
                  change φ (OrderDual.ofDual n) ((a : A) • x.1) =
                    (a : A) • φ (OrderDual.ofDual n) x.1
                  exact (φ (OrderDual.ofDual n)).map_smul (a : A) x.1 }
          naturality := by
            intro i j f
            ext x
            exact Subtype.ext <|
              (congrArg (fun g ↦ g x.1) (hφn f)).symm } }

@[simp] theorem degreewiseLimitMap_π
    (𝓜 : ℤ → Submodule ℤ M)
    [SetLike.GradedSMul 𝒜 𝓜]
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (h𝒢 :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j) (d : ℤ)
        {x : G_.obj i}, x ∈ 𝒢 (OrderDual.ofDual i) d →
          (G_.map f).hom x ∈ 𝒢 (OrderDual.ofDual j) d)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (hφn :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        (G_.map f).hom ∘ₗ φ (OrderDual.ofDual i) = φ (OrderDual.ofDual j))
    (hφ :
      ∀ n d {x : M}, x ∈ 𝓜 d → φ n x ∈ 𝒢 n d)
    (d : ℤ) (n : ℕ+) :
    degreewiseLimitMap 𝒜 𝓜 G_ 𝒢 h𝒢 φ hφn hφ d ≫
        limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n) =
      ModuleCat.ofHom
        { toFun := fun x ↦ ⟨φ n x.1, hφ n d x.2⟩
          map_add' := by
            intro x y
            apply Subtype.ext
            change φ n (x.1 + y.1) = φ n x.1 + φ n y.1
            exact (φ n).map_add x.1 y.1
          map_smul' := by
            intro a x
            apply Subtype.ext
            change φ n ((a : A) • x.1) = (a : A) • φ n x.1
            exact (φ n).map_smul (a : A) x.1 } := by
  simp [degreewiseLimitMap]

/-- Helper for Lemma 10.98.4: the degree-`d` piece of one stage maps into the ambient stage after
restricting scalars from `A` to `A₀ = 𝒜 0`. -/
private abbrev degreewiseStageSubtype
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (d : ℤ) (n : ℕ+) :
    ModuleCat.of (𝒜 0) (degreeZeroPiece 𝒜 (𝒢 n) d) ⟶
      (ModuleCat.restrictScalars (algebraMap (𝒜 0) A)).obj (G_.obj (OrderDual.toDual n)) :=
  ModuleCat.ofHom
    (X := degreeZeroPiece 𝒜 (𝒢 n) d)
    (Y := (ModuleCat.restrictScalars (algebraMap (𝒜 0) A)).obj (G_.obj (OrderDual.toDual n)))
    (degreeZeroPiece 𝒜 (𝒢 n) d).subtype

/-- Helper for Lemma 10.98.4: forgetting the degree-`d` inverse limit into the ambient inverse
limit commutes with every stage projection after restricting scalars to `A₀ = 𝒜 0`. -/
noncomputable def degreewise_limit_forget_restrictScalars
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (h𝒢 :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j) (d : ℤ)
        {x : G_.obj i}, x ∈ 𝒢 (OrderDual.ofDual i) d →
          (G_.map f).hom x ∈ 𝒢 (OrderDual.ofDual j) d)
    (d : ℤ) :
    limit (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) ⟶
      (ModuleCat.restrictScalars (algebraMap (𝒜 0) A)).obj (limit G_) :=
  limit.lift (G_ ⋙ ModuleCat.restrictScalars (algebraMap (𝒜 0) A))
    { pt := limit (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d)
      π :=
        { app := fun n ↦
            limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) n ≫
              degreewiseStageSubtype 𝒜 G_ 𝒢 d (OrderDual.ofDual n)
          naturality := by
            intro i j f
            apply ModuleCat.hom_ext
            ext x
            exact congrArg Subtype.val <|
              (congrArg (fun g ↦ g.hom x) (limit.w (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) f)).symm } } ≫
    (preservesLimitIso (ModuleCat.restrictScalars (algebraMap (𝒜 0) A)) G_).inv

@[simp, reassoc]
theorem degreewise_limit_forget_restrictScalars_π
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (h𝒢 :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j) (d : ℤ)
        {x : G_.obj i}, x ∈ 𝒢 (OrderDual.ofDual i) d →
          (G_.map f).hom x ∈ 𝒢 (OrderDual.ofDual j) d)
    (d : ℤ) (n : ℕ+) :
    degreewise_limit_forget_restrictScalars 𝒜 G_ 𝒢 h𝒢 d ≫
        (ModuleCat.restrictScalars (algebraMap (𝒜 0) A)).map (limit.π G_ (OrderDual.toDual n)) =
      limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n) ≫
        degreewiseStageSubtype 𝒜 G_ 𝒢 d n := by
  -- The forget map is a `limit.lift` followed by the inverse preserved-limit comparison, so the
  -- stage projection is exactly the defining cone leg.
  rw [degreewise_limit_forget_restrictScalars, Category.assoc]
  erw [preservesLimitIso_inv_π]
  exact limit.lift_π _ _

/-- Helper for Lemma 10.98.4: an element of an inverse limit of modules is zero once all stage
coordinates vanish. -/
private theorem limit_eq_zero_of_π_eq_zero
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    {z : ↑(limit G_)}
    (hz : ∀ n : ℕ+, (limit.π G_ (OrderDual.toDual n)).hom z = 0) :
    z = 0 := by
  let f : ModuleCat.of A A ⟶ limit G_ := ModuleCat.ofHom
    { toFun := fun r ↦ r • z
      map_add' := by
        intro r s
        exact add_smul r s z
      map_smul' := by
        intro a r
        simpa using (smul_assoc a r z) }
  have hf : f = 0 := by
    -- Compare the two maps to the limit stagewise; every coordinate vanishes by hypothesis.
    apply limit.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have hz' : (limit.π G_ n).hom z = 0 := by
      simpa using hz (OrderDual.ofDual n)
    calc
      (limit.π G_ n).hom ((ModuleCat.ofHom
          { toFun := fun r ↦ r • z
            map_add' := by
              intro r s
              exact add_smul r s z
            map_smul' := by
              intro a r
              simpa using (smul_assoc a r z) }).hom a) =
          (limit.π G_ n).hom (a • z) := by
            rfl
      _ = a • (limit.π G_ n).hom z := by
            rw [LinearMap.map_smul]
      _ = a • 0 := by
            rw [hz']
      _ = (0 : G_.obj n) := by simp
      _ = (ModuleCat.Hom.hom (0 ≫ limit.π G_ n)) a := by simp
  -- Evaluate the resulting equality at `1 : A` to recover the original element.
  have h1 := congrArg (fun g : ModuleCat.of A A ⟶ limit G_ ↦ g.hom (1 : A)) hf
  change (1 : A) • z = 0 at h1
  simpa using h1

/-- Helper for Lemma 10.98.4: on a pure tensor `1 ⊗ m`, the `n`th stage of the tensor-product
comparison is exactly `φₙ m`. -/
@[simp] private theorem tensorProductComparison_π_one_tmul
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (hGI :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (hφn :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        (G_.map f).hom ∘ₗ φ (OrderDual.ofDual i) = φ (OrderDual.ofDual j))
    (n : ℕ+) (m : M) :
    (limit.π G_ (OrderDual.toDual n)).hom
        ((tensorProductComparison 𝒜 I G_ hGI φ hφn).hom
          ((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] m)) =
      φ n m := by
  -- The `n`th projection of the tensor comparison is the `n`th completion stage map; on
  -- `1 ⊗ m`, the completion coordinate is exactly `Submodule.Quotient.mk m`.
  change
    (limit.π G_ (OrderDual.toDual n)).hom
      ((completionComparison 𝒜 I G_ hGI φ hφn).hom
        ((AdicCompletion.ofTensorProduct I.toIdeal M) ((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] m))) =
      φ n m
  let x : AdicCompletion I.toIdeal M :=
    (AdicCompletion.ofTensorProduct I.toIdeal M) ((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] m)
  have hπ :
      completionComparison 𝒜 I G_ hGI φ hφn ≫ limit.π G_ (OrderDual.toDual n) =
        ModuleCat.ofHom
          (completionStageMap 𝒜 I G_ hGI φ n ∘ₗ
            AdicCompletion.eval I.toIdeal M ((n : ℕ+) : ℕ)) := by
    rw [completionComparison]
    simpa using
      (limit.lift_π
        (c :=
          { pt := ModuleCat.of A (AdicCompletion I.toIdeal M)
            π :=
              { app := fun n ↦
                  ModuleCat.ofHom <|
                    completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual n) ∘ₗ
                      AdicCompletion.eval I.toIdeal M ((OrderDual.ofDual n : ℕ+) : ℕ)
                naturality := by
                  intro i j f
                  ext x
                  let hle :
                      ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) :=
                    show ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) from
                      (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f)
                  let xi := AdicCompletion.eval I.toIdeal M ((OrderDual.ofDual i : ℕ+) : ℕ) x
                  have hcompat :
                      (G_.map f).hom ((completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual i)) xi) =
                        (completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual j))
                          (AdicCompletion.transitionMap I.toIdeal M hle xi) := by
                    exact congrArg (fun g ↦ g xi) (completionStageMap_compat 𝒜 I G_ hGI φ hφn f)
                  exact
                    (congrArg
                      (completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual j))
                      (x.property hle)).symm.trans hcompat.symm } })
        (j := OrderDual.toDual n))
  have hπx := congrArg (fun f : ModuleCat.of A (AdicCompletion I.toIdeal M) ⟶ G_.obj (OrderDual.toDual n) ↦ f.hom x) hπ
  dsimp [x] at hπx
  simpa [x, completionStageMap] using hπx

/-- Helper for Lemma 10.98.4: on a pure tensor coming from `A`, the `n`th stage of the
tensor-product comparison is `φₙ (a • m)`. -/
@[simp] private theorem tensorProductComparison_π_of_of_tmul
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (hGI :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (hφn :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        (G_.map f).hom ∘ₗ φ (OrderDual.ofDual i) = φ (OrderDual.ofDual j))
    (a : A) (n : ℕ+) (m : M) :
    (limit.π G_ (OrderDual.toDual n)).hom
        ((tensorProductComparison 𝒜 I G_ hGI φ hφn).hom
          ((AdicCompletion.of I.toIdeal A a) ⊗ₜ[A] m)) =
      φ n (a • m) := by
  -- Rewrite the scalar tensor as `1 ⊗ (a • m)` and then use the base `1 ⊗ -` computation.
  have htmul :
      (AdicCompletion.of I.toIdeal A a) ⊗ₜ[A] m =
        (1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] (a • m) := by
    calc
      (AdicCompletion.of I.toIdeal A a) ⊗ₜ[A] m =
          (algebraMap A (AdicCompletion I.toIdeal A) a) ⊗ₜ[A] m := by
            rfl
      _ = ((a : A) • (1 : AdicCompletion I.toIdeal A)) ⊗ₜ[A] m := by
            rw [Algebra.smul_def, mul_one]
      _ = (1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] (a • m) := by
            simpa using
              (TensorProduct.smul_tmul
                (R := A) (r := a) (m := (1 : AdicCompletion I.toIdeal A)) (n := m))
  rw [htmul]
  simpa using tensorProductComparison_π_one_tmul
    (𝒜 := 𝒜) (I := I) (G_ := G_) (hGI := hGI) (φ := φ) (hφn := hφn) (n := n) (m := a • m)

/-- Helper for Lemma 10.98.4: a degreewise kernel element maps to zero under the ambient
tensor-product comparison on `1 ⊗ z`. -/
private theorem tensorProductComparison_eq_zero_of_degreewise_zero
    (I : HomogeneousIdeal 𝒜)
    (𝓜 : ℤ → Submodule ℤ M)
    [SetLike.GradedSMul 𝒜 𝓜]
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (h𝒢 :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j) (d : ℤ)
        {x : G_.obj i}, x ∈ 𝒢 (OrderDual.ofDual i) d →
          (G_.map f).hom x ∈ 𝒢 (OrderDual.ofDual j) d)
    (hGI :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (hφn :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        (G_.map f).hom ∘ₗ φ (OrderDual.ofDual i) = φ (OrderDual.ofDual j))
    (hφ :
      ∀ n d {x : M}, x ∈ 𝓜 d → φ n x ∈ 𝒢 n d)
    (d : ℤ)
    (z : degreeZeroPiece 𝒜 𝓜 d)
    (hz : (degreewiseLimitMap 𝒜 𝓜 G_ 𝒢 h𝒢 φ hφn hφ d).hom z = 0) :
    (tensorProductComparison 𝒜 I G_ hGI φ hφn).hom
        ((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] z.1) = 0 := by
  -- The degreewise kernel hypothesis says every stage value `φₙ z` vanishes in the ambient
  -- system, so the inverse-limit element is zero by stagewise extensionality.
  apply limit_eq_zero_of_π_eq_zero (G_ := G_)
  intro n
  have hstage : φ n z.1 = 0 := by
    -- Project the degreewise limit equation to stage `n` and then forget the subtype wrapper.
    have hπ0 :
        (limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom
            ((degreewiseLimitMap 𝒜 𝓜 G_ 𝒢 h𝒢 φ hφn hφ d).hom z) =
          0 := by
      simpa using congrArg
        (fun w ↦
          (limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom w)
        hz
    have hπ' :
        ((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom
            ((degreewiseLimitMap 𝒜 𝓜 G_ 𝒢 h𝒢 φ hφn hφ d).hom z)).1 =
          0 :=
      congrArg Subtype.val hπ0
    have hπmap :
        ((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom
            ((degreewiseLimitMap 𝒜 𝓜 G_ 𝒢 h𝒢 φ hφn hφ d).hom z)).1 =
          φ n z.1 := by
      exact congrArg
        (fun f :
          ModuleCat.of (𝒜 0) (degreeZeroPiece 𝒜 𝓜 d) ⟶
            ModuleCat.of (𝒜 0) (degreeZeroPiece 𝒜 (𝒢 n) d) ↦
          (f.hom z).1)
        (degreewiseLimitMap_π
          (𝒜 := 𝒜) (𝓜 := 𝓜) (G_ := G_) (𝒢 := 𝒢) (h𝒢 := h𝒢) (φ := φ)
          (hφn := hφn) (hφ := hφ) (d := d) (n := n))
    calc
      φ n z.1 =
          ((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom
              ((degreewiseLimitMap 𝒜 𝓜 G_ 𝒢 h𝒢 φ hφn hφ d).hom z)).1 := by
            exact hπmap.symm
      _ = 0 := hπ'
  -- The ambient tensor comparison has the same stage values on `1 ⊗ z`, so each projection is
  -- zero as well.
  rw [tensorProductComparison_π_one_tmul, hstage]

/-- Helper for Lemma 10.98.4: if `1 ⊗ z` vanishes in the ambient tensor product, then the same
vanishing already occurs after restricting to a finitely generated submodule containing `z`. -/
private theorem exists_fg_submodule_one_tmul_eq_zero
    (I : HomogeneousIdeal 𝒜)
    {z : M}
    (hz : ((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] z) = 0) :
    ∃ P : Submodule A M, P.FG ∧
      ∃ hzP : z ∈ P,
        ((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] (⟨z, hzP⟩ : P)) = 0 := by
  let P₀ : Submodule A M := Submodule.span A ({z} : Set M)
  have hzP₀ : z ∈ P₀ := Submodule.subset_span (by simp)
  have hP₀fg : P₀.FG := by
    simpa [P₀] using (Submodule.fg_span_singleton (R := A) z)
  let t : P₀ ⊗[A] AdicCompletion I.toIdeal A :=
    (⟨z, hzP₀⟩ : P₀) ⊗ₜ[A] (1 : AdicCompletion I.toIdeal A)
  have hcomm_zero :
      (z ⊗ₜ[A] (1 : AdicCompletion I.toIdeal A) :
        M ⊗[A] AdicCompletion I.toIdeal A) = 0 := by
    -- Commute the factors so that the direct-limit finite-support descent theorem can act on the
    -- module factor.
    simpa using congrArg (TensorProduct.comm A (AdicCompletion I.toIdeal A) M) hz
  have ht_zero :
      LinearMap.rTensor (AdicCompletion I.toIdeal A) P₀.subtype t = 0 := by
    simpa [t] using hcomm_zero
  obtain ⟨P, hP₀P, hPfg, htP_zero⟩ :=
    TensorProduct.eq_zero_of_fg_of_subtype_eq_zero
      (R := A) (M := M) (N := AdicCompletion I.toIdeal A)
      (P := P₀) (hP := hP₀fg) (t := t) ht_zero
  have hzP : z ∈ P := hP₀P hzP₀
  have hz_tensor_zero_right :
      ((⟨z, hzP⟩ : P) ⊗ₜ[A] (1 : AdicCompletion I.toIdeal A)) = 0 := by
    -- The enlarged finitely generated submodule carries the same vanishing relation.
    simpa [t] using htP_zero
  have hz_tensor_zero :
      ((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] (⟨z, hzP⟩ : P)) = 0 := by
    -- Commute back to the source-facing `1 ⊗ z` orientation.
    simpa using congrArg (TensorProduct.comm A P (AdicCompletion I.toIdeal A)) hz_tensor_zero_right
  exact ⟨P, hPfg, hzP, hz_tensor_zero⟩

/-- Helper for Lemma 10.98.4: after the finite-support descent, decompose a finite generating
family into homogeneous pieces so that `1 ⊗ z` already vanishes on a finite homogeneous span. -/
private theorem exists_homogeneous_span_one_tmul_eq_zero
    (I : HomogeneousIdeal 𝒜)
    (𝓜 : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜]
    {d : ℤ} (z : degreeZeroPiece 𝒜 𝓜 d)
    (hz : ((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] z.1) = 0) :
    ∃ s : Finset M,
      (∀ x ∈ s, SetLike.IsHomogeneousElem 𝓜 x) ∧
        ∃ hzspan : z.1 ∈ Submodule.span A (s : Set M),
          ((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A]
            (⟨z.1, hzspan⟩ : Submodule.span A (s : Set M))) = 0 := by
  classical
  obtain ⟨P, hPfg, hzP, hzeroP⟩ :=
    exists_fg_submodule_one_tmul_eq_zero (𝒜 := 𝒜) (I := I) (z := z.1) hz
  obtain ⟨S, hSfinite, hSspan⟩ := Submodule.fg_def.mp hPfg
  let t : Finset M := hSfinite.toFinset
  let s : Finset M :=
    t.biUnion fun y =>
      (DirectSum.decompose 𝓜 y).support.image fun i => (DirectSum.decompose 𝓜 y i : M)
  have hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝓜 x := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨y, -, hx⟩
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact ⟨i, (DirectSum.decompose 𝓜 y i).2⟩
  have hspanP : P ≤ Submodule.span A (s : Set M) := by
    rw [← hSspan]
    refine Submodule.span_le.mpr ?_
    intro y hyS
    have hyt : y ∈ t := by
      simpa [t] using hyS
    -- Replace each chosen finite generator by the sum of its homogeneous components.
    rw [← DirectSum.sum_support_decompose 𝓜 y]
    refine Submodule.sum_mem _ fun i hi => ?_
    exact Submodule.subset_span <|
      Finset.mem_biUnion.mpr ⟨y, hyt, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  have hzspan : z.1 ∈ Submodule.span A (s : Set M) := hspanP hzP
  have hzero_span :
      ((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A]
        (⟨z.1, hzspan⟩ : Submodule.span A (s : Set M))) = 0 := by
    -- Push the finite-support relation from `P` into the homogeneous span generated by the
    -- decomposed finite family.
    have hmap :
        ((Submodule.inclusion hspanP).lTensor (AdicCompletion I.toIdeal A))
            (((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] (⟨z.1, hzP⟩ : P))) =
          ((Submodule.inclusion hspanP).lTensor (AdicCompletion I.toIdeal A)) 0 := by
      exact congrArg ((Submodule.inclusion hspanP).lTensor (AdicCompletion I.toIdeal A)) hzeroP
    simpa using hmap
  exact ⟨s, hs_homogeneous, hzspan, hzero_span⟩

/-- Helper for Lemma 10.98.4: if `1 ⊗ z` already vanishes in `AdicCompletion(I) ⊗ P`, then after
evaluating the completion factor at stage `n` the class of `z` in `P / I^n P` is zero. -/
private theorem quotient_mk_eq_zero_of_one_tmul_zero_stage
    (I : HomogeneousIdeal 𝒜)
    {P : Submodule A M} {z : P}
    (hz : ((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] z) = 0)
    (n : ℕ+) :
    (Submodule.Quotient.mk z :
      P ⧸ (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A P))) = 0 := by
  let e :
      (A ⧸ (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A A))) ≃ₗ[A] (A ⧸ (I.toIdeal ^ (n : ℕ))) :=
    Submodule.quotEquivOfEq _ _ (by
      simpa using (Ideal.smul_top_eq_map (I.toIdeal ^ (n : ℕ))))
  have hstage :
      (((AdicCompletion.eval I.toIdeal A (n : ℕ)).rTensor P)
          ((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] z) :
        (A ⧸ (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A A))) ⊗[A] P) = 0 := by
    -- Evaluate the completion factor at stage `n`; the vanishing relation survives by functoriality
    -- of tensoring with the fixed module `P`.
    simpa using congrArg (((AdicCompletion.eval I.toIdeal A (n : ℕ)).rTensor P)) hz
  have hstage' :
      ((e.rTensor P)
          (((AdicCompletion.eval I.toIdeal A (n : ℕ)).rTensor P)
            ((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] z)) :
        (A ⧸ (I.toIdeal ^ (n : ℕ))) ⊗[A] P) = 0 := by
    -- Identify the module quotient `A / (I^n • ⊤)` with the ring quotient `A / I^n` before
    -- invoking the tensor/quotient comparison.
    simpa [e] using congrArg (e.rTensor P) hstage
  have hcomm :
      (z ⊗ₜ[A] (Ideal.Quotient.mk (I.toIdeal ^ (n : ℕ)) (1 : A)) :
        P ⊗[A] (A ⧸ (I.toIdeal ^ (n : ℕ)))) = 0 := by
    -- Commute the tensor factors so the quotient-tensor equivalence can read this as a quotient
    -- statement in the module factor.
    simpa using
      congrArg (TensorProduct.comm A (A ⧸ (I.toIdeal ^ (n : ℕ))) P) hstage'
  have hmk :
      (TensorProduct.mk A P (A ⧸ (I.toIdeal ^ (n : ℕ)))).flip
          (Ideal.Quotient.mk (I.toIdeal ^ (n : ℕ)) (1 : A)) z = 0 := by
    -- Repackage the pure tensor in the exact shape consumed by
    -- `tensorQuotEquivQuotSMul_comp_mk`.
    simpa using hcomm
  have hmap :
      (Submodule.Quotient.mk z :
        P ⧸ (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A P))) = 0 := by
    -- Apply the quotient-tensor comparison on the reoriented pure tensor `z ⊗ 1`.
    calc
      (Submodule.Quotient.mk z :
          P ⧸ (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A P))) =
          TensorProduct.tensorQuotEquivQuotSMul P (I.toIdeal ^ (n : ℕ))
            (((TensorProduct.mk A P (A ⧸ (I.toIdeal ^ (n : ℕ)))).flip 1) z) := by
              symm
              exact congrArg
                (fun f :
                  P →ₗ[A] P ⧸ (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A P)) => f z)
                (TensorProduct.tensorQuotEquivQuotSMul_comp_mk
                  (M := P) (I := I.toIdeal ^ (n : ℕ)))
      _ = TensorProduct.tensorQuotEquivQuotSMul P (I.toIdeal ^ (n : ℕ)) 0 := by
            simpa using hmk
      _ = 0 := by simp
  exact hmap

/-- Helper for Lemma 10.98.4: a chosen homogeneous degree witness for a homogeneous element of
`M`. -/
private noncomputable def homogeneousDegree
    (𝓜 : ℤ → Submodule ℤ M) [DirectSum.Decomposition 𝓜]
    (x : M) (hx : SetLike.IsHomogeneousElem 𝓜 x) : ℤ :=
  Classical.choose hx

/-- Helper for Lemma 10.98.4: the chosen degree witness places the element in the corresponding
graded piece. -/
private theorem homogeneousDegree_mem
    (𝓜 : ℤ → Submodule ℤ M) [DirectSum.Decomposition 𝓜]
    (x : M) (hx : SetLike.IsHomogeneousElem 𝓜 x) :
    x ∈ 𝓜 (homogeneousDegree 𝓜 x hx) :=
  Classical.choose_spec hx

/-- Helper for Lemma 10.98.4: a homogeneous element equals its chosen homogeneous component. -/
private theorem decompose_homogeneousDegree_eq
    (𝓜 : ℤ → Submodule ℤ M) [DirectSum.Decomposition 𝓜]
    (x : M) (hx : SetLike.IsHomogeneousElem 𝓜 x) :
    DirectSum.decompose 𝓜 x (homogeneousDegree 𝓜 x hx) = x := by
  simpa using DirectSum.decompose_of_mem_same 𝓜 (homogeneousDegree_mem 𝓜 x hx)

/-- Helper for Lemma 10.98.4: every power of a homogeneous ideal remains homogeneous. -/
private theorem ideal_pow_isHomogeneous
    (I : HomogeneousIdeal 𝒜) (n : ℕ) :
    (I.toIdeal ^ n).IsHomogeneous 𝒜 := by
  induction n with
  | zero =>
      simpa using (Ideal.IsHomogeneous.top (𝒜 := 𝒜))
  | succ n ih =>
      -- The source route only needs homogeneity to pass to every graded component of `I^n`.
      simpa [pow_succ] using Ideal.IsHomogeneous.mul (𝒜 := 𝒜) ih I.isHomogeneous

/-- Helper for Lemma 10.98.4: the cutoff `Int.toNat (d - m) + 1` pushes every degree contribution
strictly above `d` once the module degree is at least `m`. -/
private theorem target_degree_lt_of_cutoff_le
    {m d e : ℤ} {i : ℕ}
    (hm : m ≤ e)
    (hi : Int.toNat (d - m) + 1 ≤ i) :
    d < (i : ℤ) + e := by
  have hi' : (((Int.toNat (d - m) + 1 : ℕ) : ℤ)) ≤ i := by
    exact_mod_cast hi
  by_cases hdm : 0 ≤ d - m
  · have hi'' : (d - m : ℤ) + 1 ≤ i := by
      calc
        (d - m : ℤ) + 1 = (((Int.toNat (d - m) : ℕ) : ℤ) + 1) := by
          rw [Int.toNat_of_nonneg hdm]
        _ = (((Int.toNat (d - m) + 1 : ℕ) : ℤ)) := by norm_num
        _ ≤ i := hi'
    linarith
  · have hdm' : d < m := by linarith
    have hpos : (0 : ℤ) < (((Int.toNat (d - m) + 1 : ℕ) : ℤ)) := by
      norm_num
    linarith

/-- Helper for Lemma 10.98.4: because `I ≤ 𝒜₊`, every element of `I^n` has no homogeneous part in
degrees `< n`. -/
private theorem decompose_pow_mem_eq_zero_of_lt
    (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ 𝒜₊)
    {n j : ℕ} {r : A}
    (hr : r ∈ I.toIdeal ^ n)
    (hj : j < n) :
    ((DirectSum.decompose 𝒜 r j : 𝒜 j) : A) = 0 := by
  classical
  have hvanish :
      ∀ {k : ℕ} {x : A}, x ∈ I.toIdeal ^ k →
        ∀ t < k, ((DirectSum.decompose 𝒜 x t : 𝒜 t) : A) = 0 := by
    intro k x hx
    refine Submodule.pow_induction_on_left'
        (M := I.toIdeal)
        (C := fun k x _ =>
          ∀ t < k, ((DirectSum.decompose 𝒜 x t : 𝒜 t) : A) = 0) ?_ ?_ ?_ hx
    · intro a t ht
      exact (Nat.not_lt_zero _ ht).elim
    · intro x y k hx hy hx_zero hy_zero t ht
      simpa [DirectSum.decompose_add, hx_zero t ht, hy_zero t ht]
    · intro m hm k x hx hx_zero t ht
      have hm0 : ((DirectSum.decompose 𝒜 m 0 : 𝒜 0) : A) = 0 := by
        have hm_irrelevant : m ∈ 𝒜₊ := hI hm
        have hproj0 : GradedRing.proj 𝒜 0 m = 0 := by
          simpa [HomogeneousIdeal.mem_irrelevant_iff] using hm_irrelevant
        simpa [GradedRing.proj_apply] using hproj0
      -- Expand the left factor into homogeneous pieces and use the induction hypothesis on the
      -- shifted degree of the right factor.
      rw [← DirectSum.sum_support_decompose 𝒜 m, Finset.sum_mul, DirectSum.decompose_sum]
      have hsum_zero :
          (∑ i ∈ (DirectSum.decompose 𝒜 m).support,
              (DirectSum.decompose 𝒜 ((((DirectSum.decompose 𝒜 m) i : 𝒜 i) : A) * x) t : 𝒜 t)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        by_cases hi0 : i = 0
        · subst hi0
          apply Subtype.ext
          simpa [hm0]
        · by_cases hit : i ≤ t
          · have hlt : t - i < k := by
              omega
            apply Subtype.ext
            rw [DirectSum.coe_decompose_mul_of_left_mem_of_le (𝒜 := 𝒜)
              (a := (((DirectSum.decompose 𝒜 m i : 𝒜 i) : A))) (b := x)
              (i := i) (n := t) (a_mem := SetLike.coe_mem _) hit]
            simp [hx_zero (t - i) hlt]
          · apply Subtype.ext
            simpa using
              (DirectSum.coe_decompose_mul_of_left_mem_of_not_le (𝒜 := 𝒜)
                (a := (((DirectSum.decompose 𝒜 m i : 𝒜 i) : A))) (b := x)
                (i := i) (n := t) (a_mem := SetLike.coe_mem _) hit)
      simpa using congrArg (fun z : 𝒜 t ↦ (z : A)) hsum_zero
  exact hvanish hr j hj

/-- Helper for Lemma 10.98.4: an `I^(d-m+1)`-coefficient cannot contribute to degree `d` when it
acts on a homogeneous vector whose degree is at least `m`. -/
private theorem decompose_pow_smul_homogeneous_eq_zero_of_degree_lower_bound
    (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ 𝒜₊)
    (𝓜 : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜]
    {m d : ℤ}
    {y : M} (hy : SetLike.IsHomogeneousElem 𝓜 y)
    (hm : m ≤ homogeneousDegree 𝓜 y hy)
    {r : A}
    (hr : r ∈ I.toIdeal ^ (Int.toNat (d - m) + 1)) :
    ((DirectSum.decompose 𝓜 (r • y) d : 𝓜 d) : M) = 0 := by
  classical
  let e : ℤ := homogeneousDegree 𝓜 y hy
  have hy_mem : y ∈ 𝓜 e := homogeneousDegree_mem 𝓜 y hy
  have hr_decomp :
      ∀ i, (DirectSum.decompose 𝒜 r i : A) ∈ I.toIdeal ^ (Int.toNat (d - m) + 1) :=
    (Ideal.IsHomogeneous.mem_iff (𝒜 := 𝒜)
      (I := I.toIdeal ^ (Int.toNat (d - m) + 1))
      (ideal_pow_isHomogeneous (𝒜 := 𝒜) I (Int.toNat (d - m) + 1))).1 hr
  have hsum_smul :
      r • y =
        ∑ i ∈ (DirectSum.decompose 𝒜 r).support,
          (((DirectSum.decompose 𝒜 r i : 𝒜 i) : A) • y) := by
    calc
      r • y =
          (∑ i ∈ (DirectSum.decompose 𝒜 r).support,
            (((DirectSum.decompose 𝒜 r i : 𝒜 i) : A))) • y := by
              simpa using congrArg (fun a : A ↦ a • y) (DirectSum.sum_support_decompose 𝒜 r).symm
      _ =
          ∑ i ∈ (DirectSum.decompose 𝒜 r).support,
            (((DirectSum.decompose 𝒜 r i : 𝒜 i) : A) • y) := by
              rw [Finset.sum_smul]
  -- Expand the scalar into homogeneous pieces; low-degree pieces vanish inside `I^(d-m+1)`,
  -- while high-degree pieces shift the module degree strictly above `d`.
  rw [hsum_smul, DirectSum.decompose_sum]
  have happly :
      (((∑ i ∈ (DirectSum.decompose 𝒜 r).support,
          DirectSum.decompose 𝓜 ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y)) d : 𝓜 d)) =
        ∑ i ∈ (DirectSum.decompose 𝒜 r).support,
          (DirectSum.decompose 𝓜 ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y) d : 𝓜 d) := by
    simpa using
      (DFinsupp.finset_sum_apply
        ((DirectSum.decompose 𝒜 r).support)
        (fun i ↦ DirectSum.decompose 𝓜 ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y))
        d)
  rw [happly]
  have hsum_zero :
      (∑ i ∈ (DirectSum.decompose 𝒜 r).support,
          (DirectSum.decompose 𝓜 ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y) d : 𝓜 d)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    by_cases hii : i < Int.toNat (d - m) + 1
    · have hzero :
          ((DirectSum.decompose 𝒜 r i : 𝒜 i) : A) = 0 :=
        by
          simpa using
            (decompose_pow_mem_eq_zero_of_lt (𝒜 := 𝒜) (I := I) hI
              (r := (((DirectSum.decompose 𝒜 r i : 𝒜 i) : A))) (hr_decomp i) hii)
      apply Subtype.ext
      simpa [hzero]
    · have hige : Int.toNat (d - m) + 1 ≤ i := Nat.le_of_not_gt hii
      have hlt : d < (i : ℤ) + e :=
        target_degree_lt_of_cutoff_le (m := m) (d := d) (e := e) hm hige
      have hsmul : (((DirectSum.decompose 𝒜 r i : 𝒜 i) : A) • y) ∈ 𝓜 (i +ᵥ e) :=
        SetLike.GradedSMul.smul_mem (SetLike.coe_mem _) hy_mem
      apply Subtype.ext
      simpa using
        (DirectSum.decompose_of_mem_ne 𝓜 hsmul (by
          change ((i : ℤ) + e) ≠ d
          exact ne_of_gt hlt))
  exact congrArg (fun z : 𝓜 d ↦ (z : M)) hsum_zero

/-- Helper for Lemma 10.98.4: after fixing a lower bound on the generator degrees, a coefficient in
`I^(d-m+1)` kills the degree-`d` component of every vector in the homogeneous span. -/
private theorem decompose_pow_smul_span_eq_zero_of_degree_lower_bound
    (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ 𝒜₊)
    (𝓜 : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜]
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝓜 x)
    (m d : ℤ)
    (hs_lower :
      ∀ x, ∀ hx : x ∈ s, m ≤ homogeneousDegree 𝓜 x (hs_homogeneous x hx))
    {y : M}
    (hy : y ∈ Submodule.span A (s : Set M))
    {r : A}
    (hr : r ∈ I.toIdeal ^ (Int.toNat (d - m) + 1)) :
    ((DirectSum.decompose 𝓜 (r • y) d : 𝓜 d) : M) = 0 := by
  have hspan :
      ∀ {y : M}, y ∈ Submodule.span A (s : Set M) →
        ∀ {r : A}, r ∈ I.toIdeal ^ (Int.toNat (d - m) + 1) →
          ((DirectSum.decompose 𝓜 (r • y) d : 𝓜 d) : M) = 0 := by
    refine Submodule.span_induction
      (p := fun y _ =>
        ∀ {r : A}, r ∈ I.toIdeal ^ (Int.toNat (d - m) + 1) →
          ((DirectSum.decompose 𝓜 (r • y) d : 𝓜 d) : M) = 0) ?_ ?_ ?_ ?_
    · intro x hx r hr'
      exact decompose_pow_smul_homogeneous_eq_zero_of_degree_lower_bound
        (𝒜 := 𝒜) (I := I) (hI := hI) (𝓜 := 𝓜)
        (y := x) (hy := hs_homogeneous x hx) (m := m) (d := d)
        (hm := hs_lower x hx) hr'
    · intro r hr'
      simp
    · intro y z hy' hz' hy_zero hz_zero r hr'
      simpa [smul_add, DirectSum.decompose_add, hy_zero hr', hz_zero hr']
    · intro a y hy' hy_zero r hr'
      have har : a * r ∈ I.toIdeal ^ (Int.toNat (d - m) + 1) := Ideal.mul_mem_left _ _ hr'
      simpa [smul_smul, mul_assoc, mul_comm, mul_left_comm] using hy_zero har
  exact hspan hy hr

/-- Helper for Lemma 10.98.4: the degree-`d` component of any element in
`I^(d-m+1) • span(s)` vanishes once all generators of `s` have degree at least `m`. -/
private theorem decompose_pow_smul_span_mem_of_degree_lower_bound
    (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ 𝒜₊)
    (𝓜 : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜]
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝓜 x)
    (m d : ℤ)
    (hs_lower :
      ∀ x, ∀ hx : x ∈ s, m ≤ homogeneousDegree 𝓜 x (hs_homogeneous x hx))
    {z : M}
    (hz :
      z ∈ I.toIdeal ^ (Int.toNat (d - m) + 1) • Submodule.span A (s : Set M)) :
    ((DirectSum.decompose 𝓜 z d : 𝓜 d) : M) = 0 := by
  -- Route correction: once the coefficient-side cutoff lemma is available, the source proof's
  -- remaining span step is the direct `smul_induction_on` reduction.
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro r hr y hy
    exact decompose_pow_smul_span_eq_zero_of_degree_lower_bound
      (𝒜 := 𝒜) (I := I) (hI := hI) (𝓜 := 𝓜)
      (s := s) hs_homogeneous m d hs_lower hy hr
  · intro y z hy_zero hz_zero
    simpa [DirectSum.decompose_add, hy_zero, hz_zero]

/-- Helper for Lemma 10.98.4: a homogeneous degree-`d` element lying in
`I^(d-m+1) • span(s)` must vanish once the generators of `s` all have degree at least `m`. -/
private theorem eq_zero_of_homogeneous_mem_pow_smul_span_of_degree_lower_bound
    (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ 𝒜₊)
    (𝓜 : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜]
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝓜 x)
    (m d : ℤ)
    (hs_lower :
      ∀ x, ∀ hx : x ∈ s, m ≤ homogeneousDegree 𝓜 x (hs_homogeneous x hx))
    {z : degreeZeroPiece 𝒜 𝓜 d}
    (hz :
      z.1 ∈ I.toIdeal ^ (Int.toNat (d - m) + 1) • Submodule.span A (s : Set M)) :
    z.1 = 0 := by
  -- The ambient degree-`d` component of `z` is `z` itself, so the previous vanishing lemma closes
  -- the homogeneous case without any further quotient algebra.
  have hcomponent :
      ((DirectSum.decompose 𝓜 z.1 d : 𝓜 d) : M) = 0 :=
    decompose_pow_smul_span_mem_of_degree_lower_bound
      (𝒜 := 𝒜) (I := I) (hI := hI) (𝓜 := 𝓜)
      (s := s) hs_homogeneous m d hs_lower hz
  simpa [DirectSum.decompose_of_mem_same 𝓜 z.2] using hcomponent

/-- Helper for Lemma 10.98.4: low-degree vanishing visible at stage `B + 1` can be represented at
every stage by an honest coefficient in `A` with the same vanishing. -/
private theorem completion_tail_low_degree_representatives
    (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ 𝒜₊)
    {tail : AdicCompletion I.toIdeal A} {B : ℕ} {a_succ : A}
    (h_succ :
      AdicCompletion.eval I.toIdeal A (B + 1) tail = Submodule.Quotient.mk a_succ)
    (hvanish : ∀ j, j ≤ B → ((DirectSum.decompose 𝒜 a_succ j : 𝒜 j) : A) = 0) :
    ∀ n : ℕ+, ∃ a_n : A,
      AdicCompletion.eval I.toIdeal A (n : ℕ) tail = Submodule.Quotient.mk a_n ∧
        ∀ j, j ≤ B → ((DirectSum.decompose 𝒜 a_n j : 𝒜 j) : A) = 0 := by
  intro n
  by_cases hn : (n : ℕ) ≤ B + 1
  · refine ⟨a_succ, ?_, hvanish⟩
    -- For stages `n ≤ B + 1`, the same representative already works after applying the
    -- transition map from stage `B + 1` down to `n`.
    calc
      AdicCompletion.eval I.toIdeal A (n : ℕ) tail =
        AdicCompletion.transitionMap I.toIdeal A hn
          (AdicCompletion.eval I.toIdeal A (B + 1) tail) := by
            symm
            simpa using
              (AdicCompletion.transitionMap_comp_eval_apply
                (I := I.toIdeal) (M := A) (m := (n : ℕ)) (n := B + 1) hn tail)
      _ = AdicCompletion.transitionMap I.toIdeal A hn (Submodule.Quotient.mk a_succ) := by
            rw [h_succ]
      _ = Submodule.Quotient.mk a_succ := by
            simp [AdicCompletion.transitionMap]
  · obtain ⟨a_n, ha_n⟩ := Submodule.Quotient.mk_surjective
      (I.toIdeal ^ ((n : ℕ)) • (⊤ : Submodule A A))
      (AdicCompletion.eval I.toIdeal A (n : ℕ) tail)
    refine ⟨a_n, ha_n.symm, ?_⟩
    intro j hj
    have hBn : B + 1 ≤ (n : ℕ) := Nat.le_of_not_ge hn
    have hquot :
        (Submodule.Quotient.mk a_n :
          A ⧸ (I.toIdeal ^ (B + 1) • (⊤ : Submodule A A))) =
        Submodule.Quotient.mk a_succ := by
      -- Compare the stage-`n` representative with the stage-`B + 1` representative inside the
      -- smaller quotient.
      calc
        (Submodule.Quotient.mk a_n :
            A ⧸ (I.toIdeal ^ (B + 1) • (⊤ : Submodule A A))) =
          AdicCompletion.transitionMap I.toIdeal A hBn
            (Submodule.Quotient.mk a_n :
              A ⧸ (I.toIdeal ^ ((n : ℕ)) • (⊤ : Submodule A A))) := by
                simp [AdicCompletion.transitionMap]
        _ = AdicCompletion.transitionMap I.toIdeal A hBn
            (AdicCompletion.eval I.toIdeal A (n : ℕ) tail) := by
              rw [ha_n.symm]
        _ = AdicCompletion.eval I.toIdeal A (B + 1) tail := by
              simpa using
                (AdicCompletion.transitionMap_comp_eval_apply
                  (I := I.toIdeal) (M := A) (m := B + 1) (n := (n : ℕ)) hBn tail)
        _ = Submodule.Quotient.mk a_succ := h_succ
    have hdiff_mem_smul :
        a_n - a_succ ∈ I.toIdeal ^ (B + 1) • (⊤ : Submodule A A) := by
      exact (Submodule.Quotient.eq _).1 hquot
    have hdiff_mem :
        a_n - a_succ ∈ I.toIdeal ^ (B + 1) := by
      simpa [Ideal.smul_top_eq_map] using hdiff_mem_smul
    have hdiff_zero :
        ((DirectSum.decompose 𝒜 (a_n - a_succ) j : 𝒜 j) : A) = 0 := by
      exact decompose_pow_mem_eq_zero_of_lt (𝒜 := 𝒜) (I := I) hI hdiff_mem (Nat.lt_succ_of_le hj)
    have hdecompose_sub :
        ((DirectSum.decompose 𝒜 (a_n - a_succ) j : 𝒜 j) : A) =
          ((DirectSum.decompose 𝒜 a_n j : 𝒜 j) : A) -
            ((DirectSum.decompose 𝒜 a_succ j : 𝒜 j) : A) := by
      exact congrArg (fun z : 𝒜 j ↦ (z : A)) <|
        congrArg (fun f ↦ f j) (DirectSum.decompose_sub 𝒜 a_n a_succ)
    have hcomponent_diff :
        ((DirectSum.decompose 𝒜 a_n j : 𝒜 j) : A) -
            ((DirectSum.decompose 𝒜 a_succ j : 𝒜 j) : A) = 0 := by
      simpa [hdecompose_sub] using hdiff_zero
    calc
      ((DirectSum.decompose 𝒜 a_n j : 𝒜 j) : A) =
        ((DirectSum.decompose 𝒜 a_n j : 𝒜 j) : A) -
          ((DirectSum.decompose 𝒜 a_succ j : 𝒜 j) : A) := by
            rw [hvanish j hj, sub_zero]
      _ = 0 := hcomponent_diff

/-- Helper for Lemma 10.98.4: a ring element splits into its degrees `< B`, exactly `B`, and the
remaining tail with no degree `≤ B` part. -/
private theorem ring_element_split_at_degree
    (a : A) (B : ℕ) :
    ∃ a_lt : A, ∃ a_eqB : 𝒜 B, ∃ a_tail : A,
      a = a_lt + (a_eqB : A) + a_tail ∧
        (∀ j, B ≤ j → ((DirectSum.decompose 𝒜 a_lt j : 𝒜 j) : A) = 0) ∧
        (∀ j, j ≤ B → ((DirectSum.decompose 𝒜 a_tail j : 𝒜 j) : A) = 0) := by
  classical
  let a_lt : A := ∑ i ∈ Finset.range B, (((DirectSum.decompose 𝒜 a i : 𝒜 i) : A))
  let a_eqB : 𝒜 B := DirectSum.decompose 𝒜 a B
  let a_tail : A := a - a_lt - (a_eqB : A)
  have hdecompose_a_lt_eq :
      ∀ {j : ℕ}, j < B → DirectSum.decompose 𝒜 a_lt j = DirectSum.decompose 𝒜 a j := by
    intro j hj
    -- Only the `j`th term survives in the truncated low-degree sum.
    have happly :
        DirectSum.decompose 𝒜 a_lt j =
          ∑ i ∈ Finset.range B,
            DirectSum.decompose 𝒜 ((((DirectSum.decompose 𝒜 a i : 𝒜 i) : A))) j := by
      dsimp [a_lt]
      simpa using
        (DFinsupp.finset_sum_apply
          (Finset.range B)
          (fun i ↦ DirectSum.decompose 𝒜 ((((DirectSum.decompose 𝒜 a i : 𝒜 i) : A))))
          j)
    rw [happly, Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj)]
    · apply Subtype.ext
      simpa using
        (DirectSum.decompose_of_mem_same 𝒜
          (SetLike.coe_mem (DirectSum.decompose 𝒜 a j)))
    · intro i hi hij
      simpa using
        (DirectSum.decompose_of_mem_ne 𝒜 (SetLike.coe_mem (DirectSum.decompose 𝒜 a i)) hij)
  have hdecompose_a_lt_zero :
      ∀ {j : ℕ}, B ≤ j → ((DirectSum.decompose 𝒜 a_lt j : 𝒜 j) : A) = 0 := by
    intro j hj
    -- Every term in the truncated low-degree sum lands in a degree different from `j`.
    dsimp [a_lt]
    rw [DirectSum.decompose_sum]
    have hsum_zero :
        (∑ i ∈ Finset.range B,
            DirectSum.decompose 𝒜 ((((DirectSum.decompose 𝒜 a i : 𝒜 i) : A))) j : 𝒜 j) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      apply Subtype.ext
      have hi_lt : i < B := Finset.mem_range.mp hi
      have hij : i ≠ j := by
        exact ne_of_lt (lt_of_lt_of_le hi_lt hj)
      simpa using
        (DirectSum.decompose_of_mem_ne 𝒜 (SetLike.coe_mem (DirectSum.decompose 𝒜 a i)) hij)
    simpa using congrArg (fun z : 𝒜 j ↦ (z : A)) hsum_zero
  refine ⟨a_lt, a_eqB, a_tail, ?_, ?_, ?_⟩
  · -- The chosen tail is exactly the remainder after removing the `< B` and `= B` parts.
    dsimp [a_tail]
    abel
  · intro j hj
    exact hdecompose_a_lt_zero hj
  · intro j hj
    by_cases hj_lt : j < B
    · have hsub₁ :
          ((DirectSum.decompose 𝒜 (a - a_lt) j : 𝒜 j) : A) =
            ((DirectSum.decompose 𝒜 a j : 𝒜 j) : A) -
              ((DirectSum.decompose 𝒜 a_lt j : 𝒜 j) : A) := by
        exact congrArg (fun z : 𝒜 j ↦ (z : A)) <|
          congrArg (fun f ↦ f j) (DirectSum.decompose_sub 𝒜 a a_lt)
      have hsub₂ :
          ((DirectSum.decompose 𝒜 a_tail j : 𝒜 j) : A) =
            ((DirectSum.decompose 𝒜 (a - a_lt) j : 𝒜 j) : A) -
              ((DirectSum.decompose 𝒜 ((a_eqB : 𝒜 B) : A) j : 𝒜 j) : A) := by
        exact congrArg (fun z : 𝒜 j ↦ (z : A)) <|
          congrArg (fun f ↦ f j) (DirectSum.decompose_sub 𝒜 (a - a_lt) ((a_eqB : 𝒜 B) : A))
      have hdecompose_eqB :
          ((DirectSum.decompose 𝒜 ((a_eqB : 𝒜 B) : A) j : 𝒜 j) : A) = 0 := by
        have hBj : B ≠ j := Ne.symm (Nat.ne_of_lt hj_lt)
        simpa using
          (DirectSum.decompose_of_mem_ne 𝒜 (SetLike.coe_mem a_eqB) hBj)
      -- In degrees `< B`, the low part reproduces the original coefficient and the exact-degree
      -- term disappears.
      calc
        ((DirectSum.decompose 𝒜 a_tail j : 𝒜 j) : A) =
            ((DirectSum.decompose 𝒜 (a - a_lt) j : 𝒜 j) : A) -
              ((DirectSum.decompose 𝒜 ((a_eqB : 𝒜 B) : A) j : 𝒜 j) : A) := hsub₂
        _ = (((DirectSum.decompose 𝒜 a j : 𝒜 j) : A) -
              ((DirectSum.decompose 𝒜 a_lt j : 𝒜 j) : A)) -
              ((DirectSum.decompose 𝒜 ((a_eqB : 𝒜 B) : A) j : 𝒜 j) : A) := by
                rw [hsub₁]
        _ = 0 := by
              rw [hdecompose_a_lt_eq hj_lt, hdecompose_eqB]
              abel
    · have hj_eq : j = B := le_antisymm hj (Nat.le_of_not_gt hj_lt)
      subst j
      have hsub₁ :
          ((DirectSum.decompose 𝒜 (a - a_lt) B : 𝒜 B) : A) =
            ((DirectSum.decompose 𝒜 a B : 𝒜 B) : A) -
              ((DirectSum.decompose 𝒜 a_lt B : 𝒜 B) : A) := by
        exact congrArg (fun z : 𝒜 B ↦ (z : A)) <|
          congrArg (fun f ↦ f B) (DirectSum.decompose_sub 𝒜 a a_lt)
      have hsub₂ :
          ((DirectSum.decompose 𝒜 a_tail B : 𝒜 B) : A) =
            ((DirectSum.decompose 𝒜 (a - a_lt) B : 𝒜 B) : A) -
              ((DirectSum.decompose 𝒜 ((a_eqB : 𝒜 B) : A) B : 𝒜 B) : A) := by
        exact congrArg (fun z : 𝒜 B ↦ (z : A)) <|
          congrArg (fun f ↦ f B) (DirectSum.decompose_sub 𝒜 (a - a_lt) ((a_eqB : 𝒜 B) : A))
      have hdecompose_a_lt_B :
          ((DirectSum.decompose 𝒜 a_lt B : 𝒜 B) : A) = 0 :=
        hdecompose_a_lt_zero le_rfl
      have hdecompose_eqB :
          ((DirectSum.decompose 𝒜 ((a_eqB : 𝒜 B) : A) B : 𝒜 B) : A) = (a_eqB : A) := by
        simpa using congrArg (fun z : 𝒜 B ↦ (z : A)) <|
          (DirectSum.decompose_of_mem_same 𝒜 (SetLike.coe_mem a_eqB))
      -- In degree `B`, the middle term cancels the original `B`th coefficient exactly.
      calc
        ((DirectSum.decompose 𝒜 a_tail B : 𝒜 B) : A) =
            ((DirectSum.decompose 𝒜 (a - a_lt) B : 𝒜 B) : A) -
              ((DirectSum.decompose 𝒜 ((a_eqB : 𝒜 B) : A) B : 𝒜 B) : A) := hsub₂
        _ = (((DirectSum.decompose 𝒜 a B : 𝒜 B) : A) -
              ((DirectSum.decompose 𝒜 a_lt B : 𝒜 B) : A)) -
              ((DirectSum.decompose 𝒜 ((a_eqB : 𝒜 B) : A) B : 𝒜 B) : A) := by
                rw [hsub₁]
        _ = 0 := by
              rw [hdecompose_a_lt_B, hdecompose_eqB]
              simp [a_eqB]

/-- Helper for Lemma 10.98.4: every completion coefficient admits a stage-`B + 1` representative
split into `< B`, exactly `B`, and tail pieces. -/
private theorem completion_split_below_degree_stageSucc
    (I : HomogeneousIdeal 𝒜)
    (f' : AdicCompletion I.toIdeal A) (B : ℕ) :
    ∃ a_lt : A, ∃ a_eqB : 𝒜 B, ∃ a_tail : A,
      AdicCompletion.eval I.toIdeal A (B + 1)
          (f' - AdicCompletion.of I.toIdeal A (a_lt + (a_eqB : A))) =
        Submodule.Quotient.mk a_tail ∧
        (∀ j, B ≤ j → ((DirectSum.decompose 𝒜 a_lt j : 𝒜 j) : A) = 0) ∧
        (∀ j, j ≤ B → ((DirectSum.decompose 𝒜 a_tail j : 𝒜 j) : A) = 0) := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
    (I.toIdeal ^ (B + 1) • (⊤ : Submodule A A))
    (AdicCompletion.eval I.toIdeal A (B + 1) f')
  obtain ⟨a_lt, a_eqB, a_tail, hsplit, hlt, htail⟩ :=
    ring_element_split_at_degree (𝒜 := 𝒜) a B
  refine ⟨a_lt, a_eqB, a_tail, ?_, hlt, htail⟩
  have hdiff : a - (a_lt + (a_eqB : A)) = a_tail := by
    rw [hsplit]
    abel
  -- Evaluate the completion coefficient at stage `B + 1` and rewrite by the chosen
  -- representative-level split.
  calc
    AdicCompletion.eval I.toIdeal A (B + 1)
        (f' - AdicCompletion.of I.toIdeal A (a_lt + (a_eqB : A))) =
      AdicCompletion.eval I.toIdeal A (B + 1) f' -
        AdicCompletion.eval I.toIdeal A (B + 1)
          (AdicCompletion.of I.toIdeal A (a_lt + (a_eqB : A))) := by
            rw [map_sub]
    _ = Submodule.Quotient.mk a -
        Submodule.Quotient.mk (a_lt + (a_eqB : A)) := by
          rw [ha, AdicCompletion.eval_of, Submodule.mkQ_apply]
    _ = Submodule.Quotient.mk (a - (a_lt + (a_eqB : A))) := by
          rfl
    _ = Submodule.Quotient.mk a_tail := by
          rw [hdiff]

/-- Helper for Lemma 10.98.4: a coefficient supported in degrees `< Int.toNat (d - d₀)` cannot
contribute to degree `d` when acting on a homogeneous vector of degree `d₀`. -/
private theorem decompose_smul_eq_zero_of_support_lt_cutoff
    {X : Type u} [AddCommGroup X] [Module A X]
    (ℬ : ℤ → Submodule ℤ X)
    [DirectSum.Decomposition ℬ] [SetLike.GradedSMul 𝒜 ℬ]
    {d₀ d : ℤ} {x : X} (hx : x ∈ ℬ d₀)
    (hd : d₀ ≤ d)
    {a_lt : A}
    (hsupport :
      ∀ j, Int.toNat (d - d₀) ≤ j → ((DirectSum.decompose 𝒜 a_lt j : 𝒜 j) : A) = 0) :
    ((DirectSum.decompose ℬ (a_lt • x) d : ℬ d) : X) = 0 := by
  classical
  have hnonneg : 0 ≤ d - d₀ := sub_nonneg.mpr hd
  -- Expand the coefficient into homogeneous pieces; every surviving piece has degree `< d - d₀`
  -- and therefore shifts `x` away from degree `d`.
  let s : Finset ℕ := (DirectSum.decompose 𝒜 a_lt).support
  have happly :
      (DirectSum.decompose ℬ
          (∑ i ∈ s, (((DirectSum.decompose 𝒜 a_lt i : 𝒜 i) : A) • x)) d : ℬ d) =
        ∑ i ∈ s, (DirectSum.decompose ℬ ((((DirectSum.decompose 𝒜 a_lt i : 𝒜 i) : A) • x)) d : ℬ d) := by
    simpa [s] using
      (DFinsupp.finset_sum_apply
        s
        (fun i ↦ DirectSum.decompose ℬ ((((DirectSum.decompose 𝒜 a_lt i : 𝒜 i) : A) • x)))
        d)
  rw [← DirectSum.sum_support_decompose 𝒜 a_lt, Finset.sum_smul]
  rw [show
      (DirectSum.decompose ℬ
          (∑ i ∈ (DirectSum.decompose 𝒜 a_lt).support,
            (((DirectSum.decompose 𝒜 a_lt i : 𝒜 i) : A) • x)) d : ℬ d) =
        ∑ i ∈ (DirectSum.decompose 𝒜 a_lt).support,
          (DirectSum.decompose ℬ ((((DirectSum.decompose 𝒜 a_lt i : 𝒜 i) : A) • x)) d : ℬ d) by
        simpa [s] using happly]
  have hsum_zero :
      (∑ i ∈ (DirectSum.decompose 𝒜 a_lt).support,
          (DirectSum.decompose ℬ ((((DirectSum.decompose 𝒜 a_lt i : 𝒜 i) : A) • x)) d : ℬ d)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    by_cases hige : Int.toNat (d - d₀) ≤ i
    · have hzero : ((DirectSum.decompose 𝒜 a_lt i : 𝒜 i) : A) = 0 := hsupport i hige
      apply Subtype.ext
      simp [hzero]
    · have hi_lt_nat : i < Int.toNat (d - d₀) := Nat.lt_of_not_ge hige
      have hi_lt : (i : ℤ) < d - d₀ := by
        have hi_lt' : (i : ℤ) < (((Int.toNat (d - d₀) : ℕ) : ℤ)) := by
          exact_mod_cast hi_lt_nat
        simpa [Int.toNat_of_nonneg hnonneg] using hi_lt'
      have hsmul :
          (((DirectSum.decompose 𝒜 a_lt i : 𝒜 i) : A) • x) ∈ ℬ (i +ᵥ d₀) :=
        SetLike.GradedSMul.smul_mem (SetLike.coe_mem (DirectSum.decompose 𝒜 a_lt i)) hx
      apply Subtype.ext
      simpa using
        (DirectSum.decompose_of_mem_ne ℬ hsmul (by
          change ((i : ℤ) + d₀) ≠ d
          linarith))
  simpa using congrArg (fun z : ℬ d ↦ (z : X)) hsum_zero

/-- Helper for Lemma 10.98.4: a coefficient whose stage representatives have no homogeneous parts
in degrees `≤ Int.toNat (d - d₀)` cannot contribute to degree `d`. -/
private theorem decompose_smul_eq_zero_of_support_gt_cutoff
    {X : Type u} [AddCommGroup X] [Module A X]
    (ℬ : ℤ → Submodule ℤ X)
    [DirectSum.Decomposition ℬ] [SetLike.GradedSMul 𝒜 ℬ]
    {d₀ d : ℤ} {x : X} (hx : x ∈ ℬ d₀)
    (hd : d₀ ≤ d)
    {a_hi : A}
    (hsupport :
      ∀ j, j ≤ Int.toNat (d - d₀) → ((DirectSum.decompose 𝒜 a_hi j : 𝒜 j) : A) = 0) :
    ((DirectSum.decompose ℬ (a_hi • x) d : ℬ d) : X) = 0 := by
  classical
  have hnonneg : 0 ≤ d - d₀ := sub_nonneg.mpr hd
  -- After expanding the coefficient, the low degrees are zero by hypothesis and every remaining
  -- homogeneous piece has degree `> d - d₀`, so it overshoots degree `d`.
  let s : Finset ℕ := (DirectSum.decompose 𝒜 a_hi).support
  have happly :
      (DirectSum.decompose ℬ
          (∑ i ∈ s, (((DirectSum.decompose 𝒜 a_hi i : 𝒜 i) : A) • x)) d : ℬ d) =
        ∑ i ∈ s, (DirectSum.decompose ℬ ((((DirectSum.decompose 𝒜 a_hi i : 𝒜 i) : A) • x)) d : ℬ d) := by
    simpa [s] using
      (DFinsupp.finset_sum_apply
        s
        (fun i ↦ DirectSum.decompose ℬ ((((DirectSum.decompose 𝒜 a_hi i : 𝒜 i) : A) • x)))
        d)
  rw [← DirectSum.sum_support_decompose 𝒜 a_hi, Finset.sum_smul]
  rw [show
      (DirectSum.decompose ℬ
          (∑ i ∈ (DirectSum.decompose 𝒜 a_hi).support,
            (((DirectSum.decompose 𝒜 a_hi i : 𝒜 i) : A) • x)) d : ℬ d) =
        ∑ i ∈ (DirectSum.decompose 𝒜 a_hi).support,
          (DirectSum.decompose ℬ ((((DirectSum.decompose 𝒜 a_hi i : 𝒜 i) : A) • x)) d : ℬ d) by
        simpa [s] using happly]
  have hsum_zero :
      (∑ i ∈ (DirectSum.decompose 𝒜 a_hi).support,
          (DirectSum.decompose ℬ ((((DirectSum.decompose 𝒜 a_hi i : 𝒜 i) : A) • x)) d : ℬ d)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    by_cases hi_le : i ≤ Int.toNat (d - d₀)
    · have hzero : ((DirectSum.decompose 𝒜 a_hi i : 𝒜 i) : A) = 0 := hsupport i hi_le
      apply Subtype.ext
      simp [hzero]
    · have hi_gt_nat : Int.toNat (d - d₀) < i := Nat.lt_of_not_ge hi_le
      have hi_gt : d - d₀ < (i : ℤ) := by
        have hi_gt' : (((Int.toNat (d - d₀) : ℕ) : ℤ)) < (i : ℤ) := by
          exact_mod_cast hi_gt_nat
        simpa [Int.toNat_of_nonneg hnonneg] using hi_gt'
      have hsmul :
          (((DirectSum.decompose 𝒜 a_hi i : 𝒜 i) : A) • x) ∈ ℬ (i +ᵥ d₀) :=
        SetLike.GradedSMul.smul_mem (SetLike.coe_mem (DirectSum.decompose 𝒜 a_hi i)) hx
      apply Subtype.ext
      simpa using
        (DirectSum.decompose_of_mem_ne ℬ hsmul (by
          change ((i : ℤ) + d₀) ≠ d
          linarith))
  simpa using congrArg (fun z : ℬ d ↦ (z : X)) hsum_zero

/-- Helper for Lemma 10.98.4: a finite tensor sum can be refined by decomposing each module term
into its homogeneous pieces. -/
private theorem sum_tmul_eq_sum_homogeneous_tmul
    (I : HomogeneousIdeal 𝒜)
    (𝓜 : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition 𝓜]
    [∀ i : ℤ, DecidableEq (𝓜 i)]
    {k : ℕ}
    (a : Fin k → AdicCompletion I.toIdeal A)
    (m : Fin k → M) :
    (∑ j, a j ⊗ₜ[A] m j) =
      Finset.sum (Finset.univ.sigma (fun j ↦ (DirectSum.decompose 𝓜 (m j)).support))
        (fun p ↦ a p.1 ⊗ₜ[A] ((DirectSum.decompose 𝓜 (m p.1) p.2 : 𝓜 p.2) : M)) := by
  -- Rewrite each module term as the sum of its homogeneous components, then flatten the resulting
  -- double sum along the sigma-indexed support.
  calc
    (∑ j, a j ⊗ₜ[A] m j) =
        (Finset.univ.sum fun j ↦
          Finset.sum ((DirectSum.decompose 𝓜 (m j)).support)
            (fun i ↦ a j ⊗ₜ[A] ((DirectSum.decompose 𝓜 (m j) i : 𝓜 i) : M))) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hmj :
              m j =
                Finset.sum ((DirectSum.decompose 𝓜 (m j)).support)
                  (fun i : ℤ ↦ ((DirectSum.decompose 𝓜 (m j) i : 𝓜 i) : M)) := by
            symm
            exact DirectSum.sum_support_decompose 𝓜 (m j)
          conv_lhs => rw [hmj]
          rw [TensorProduct.tmul_sum]
    _ =
        Finset.sum (Finset.univ.sigma (fun j ↦ (DirectSum.decompose 𝓜 (m j)).support))
          (fun p ↦ a p.1 ⊗ₜ[A] ((DirectSum.decompose 𝓜 (m p.1) p.2 : 𝓜 p.2) : M)) := by
            simpa using
              (Finset.sum_sigma'
                (s := Finset.univ)
                (t := fun j ↦ (DirectSum.decompose 𝓜 (m j)).support)
                (f := fun j i ↦ a j ⊗ₜ[A] ((DirectSum.decompose 𝓜 (m j) i : 𝓜 i) : M)))

/-- Helper for Lemma 10.98.4: a chosen stage representative of a completion coefficient computes
the corresponding stage of the tensor-product comparison on a pure tensor. -/
@[simp] private theorem tensorProductComparison_π_tmul_of_eval_eq
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (hGI :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (hφn :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        (G_.map f).hom ∘ₗ φ (OrderDual.ofDual i) = φ (OrderDual.ofDual j))
    (n : ℕ+) {f' : AdicCompletion I.toIdeal A} {a : A} {x : M}
    (h_eval : AdicCompletion.eval I.toIdeal A (n : ℕ) f' = Submodule.Quotient.mk a) :
    (limit.π G_ (OrderDual.toDual n)).hom
        ((tensorProductComparison 𝒜 I G_ hGI φ hφn).hom (f' ⊗ₜ[A] x)) =
      φ n (a • x) := by
  -- Project to stage `n`, rewrite the pure tensor through `AdicCompletion.ofTensorProduct`, and
  -- then identify the quotient coefficient using the chosen representative `a`.
  change
    (limit.π G_ (OrderDual.toDual n)).hom
      ((completionComparison 𝒜 I G_ hGI φ hφn).hom
        ((AdicCompletion.ofTensorProduct I.toIdeal M) (f' ⊗ₜ[A] x))) =
      φ n (a • x)
  let y : AdicCompletion I.toIdeal M :=
    (AdicCompletion.ofTensorProduct I.toIdeal M) (f' ⊗ₜ[A] x)
  have hπ :
      completionComparison 𝒜 I G_ hGI φ hφn ≫ limit.π G_ (OrderDual.toDual n) =
        ModuleCat.ofHom
          (completionStageMap 𝒜 I G_ hGI φ n ∘ₗ
            AdicCompletion.eval I.toIdeal M ((n : ℕ+) : ℕ)) := by
    rw [completionComparison]
    simpa using
      (limit.lift_π
        (c :=
          { pt := ModuleCat.of A (AdicCompletion I.toIdeal M)
            π :=
              { app := fun n ↦
                  ModuleCat.ofHom <|
                    completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual n) ∘ₗ
                      AdicCompletion.eval I.toIdeal M ((OrderDual.ofDual n : ℕ+) : ℕ)
                naturality := by
                  intro i j f
                  ext x
                  let hle :
                      ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) :=
                    show ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) from
                      (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f)
                  let xi := AdicCompletion.eval I.toIdeal M ((OrderDual.ofDual i : ℕ+) : ℕ) x
                  have hcompat :
                      (G_.map f).hom ((completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual i)) xi) =
                        (completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual j))
                          (AdicCompletion.transitionMap I.toIdeal M hle xi) := by
                    exact congrArg (fun g ↦ g xi) (completionStageMap_compat 𝒜 I G_ hGI φ hφn f)
                  exact
                    (congrArg
                      (completionStageMap 𝒜 I G_ hGI φ (OrderDual.ofDual j))
                      (x.property hle)).symm.trans hcompat.symm } })
        (j := OrderDual.toDual n))
  have hπy := congrArg
    (fun f : ModuleCat.of A (AdicCompletion I.toIdeal M) ⟶ G_.obj (OrderDual.toDual n) ↦ f.hom y)
    hπ
  have hy_eval :
      AdicCompletion.eval I.toIdeal M (n : ℕ) y =
        (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A M)).mkQ (a • x) := by
    -- The pure tensor maps to `f' • of x`, whose `n`th coordinate is the action of the
    -- stage-`n` quotient class of `f'` on the class of `x`.
    calc
      AdicCompletion.eval I.toIdeal M (n : ℕ) y =
          AdicCompletion.eval I.toIdeal M (n : ℕ)
            (f' • AdicCompletion.of I.toIdeal M x) := by
              simp [y, AdicCompletion.ofTensorProduct_tmul]
      _ = AdicCompletion.eval I.toIdeal A (n : ℕ) f' •
            AdicCompletion.eval I.toIdeal M (n : ℕ) (AdicCompletion.of I.toIdeal M x) := by
              rfl
      _ = (Submodule.Quotient.mk a) •
            ((I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A M)).mkQ x) := by
            rw [h_eval, AdicCompletion.eval_of]
      _ = (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A M)).mkQ (a • x) := by
            rfl
  -- Collapse the quotient lift defining `completionStageMap`.
  calc
    (limit.π G_ (OrderDual.toDual n)).hom
        ((completionComparison 𝒜 I G_ hGI φ hφn).hom y) =
      (completionStageMap 𝒜 I G_ hGI φ n)
        (AdicCompletion.eval I.toIdeal M (n : ℕ) y) := by
          simpa [y] using hπy
    _ = (completionStageMap 𝒜 I G_ hGI φ n)
        ((I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A M)).mkQ (a • x)) := by
          rw [hy_eval]
    _ = φ n (a • x) := by
          simp [completionStageMap]

/-- Helper for Lemma 10.98.4: if a homogeneous vector lies in degree `d₀ > d`, then no scalar
multiple can contribute to degree `d`. -/
private theorem decompose_smul_eq_zero_of_lt_module_degree
    {X : Type u} [AddCommGroup X] [Module A X]
    (ℬ : ℤ → Submodule ℤ X)
    [DirectSum.Decomposition ℬ] [SetLike.GradedSMul 𝒜 ℬ]
    {d₀ d : ℤ} {x : X} (hx : x ∈ ℬ d₀)
    (hd : d < d₀)
    (a : A) :
    ((DirectSum.decompose ℬ (a • x) d : ℬ d) : X) = 0 := by
  classical
  -- Expand the scalar into homogeneous pieces; every summand has degree `i + d₀` with `i ≥ 0`,
  -- hence it lies strictly above the target degree `d`.
  let s : Finset ℕ := (DirectSum.decompose 𝒜 a).support
  have happly :
      (DirectSum.decompose ℬ
          (∑ i ∈ s, (((DirectSum.decompose 𝒜 a i : 𝒜 i) : A) • x)) d : ℬ d) =
        ∑ i ∈ s, (DirectSum.decompose ℬ ((((DirectSum.decompose 𝒜 a i : 𝒜 i) : A) • x)) d : ℬ d) := by
    simpa [s] using
      (DFinsupp.finset_sum_apply
        s
        (fun i ↦ DirectSum.decompose ℬ ((((DirectSum.decompose 𝒜 a i : 𝒜 i) : A) • x)))
        d)
  rw [← DirectSum.sum_support_decompose 𝒜 a, Finset.sum_smul]
  rw [show
      (DirectSum.decompose ℬ
          (∑ i ∈ (DirectSum.decompose 𝒜 a).support,
            (((DirectSum.decompose 𝒜 a i : 𝒜 i) : A) • x)) d : ℬ d) =
        ∑ i ∈ (DirectSum.decompose 𝒜 a).support,
          (DirectSum.decompose ℬ ((((DirectSum.decompose 𝒜 a i : 𝒜 i) : A) • x)) d : ℬ d) by
        simpa [s] using happly]
  have hsum_zero :
      (∑ i ∈ (DirectSum.decompose 𝒜 a).support,
          (DirectSum.decompose ℬ ((((DirectSum.decompose 𝒜 a i : 𝒜 i) : A) • x)) d : ℬ d)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hsmul :
        (((DirectSum.decompose 𝒜 a i : 𝒜 i) : A) • x) ∈ ℬ (i +ᵥ d₀) :=
      SetLike.GradedSMul.smul_mem (SetLike.coe_mem (DirectSum.decompose 𝒜 a i)) hx
    apply Subtype.ext
    simpa using
      (DirectSum.decompose_of_mem_ne ℬ hsmul (by
        change ((i : ℤ) + d₀) ≠ d
        have hi_nonneg : 0 ≤ (i : ℤ) := by exact_mod_cast Nat.zero_le i
        linarith))
  simpa using congrArg (fun z : ℬ d ↦ (z : X)) hsum_zero

/-- Helper for Lemma 10.98.4: equality in the degreewise inverse limit can be checked on the
underlying values of all stage projections. -/
private theorem degreewise_limit_ext_of_stagewise_val_eq
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (h𝒢 :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j) (d : ℤ)
        {x : G_.obj i}, x ∈ 𝒢 (OrderDual.ofDual i) d →
          (G_.map f).hom x ∈ 𝒢 (OrderDual.ofDual j) d)
    (d : ℤ)
    {u v : ↑(limit (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d))}
    (h :
      ∀ n : ℕ+,
        (((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom u).1) =
          (((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom v).1)) :
    u = v := by
  -- Use the concrete-category limit extensionality principle; the stage hypotheses already give
  -- equality of the projected degree-`d` subtype elements.
  exact Concrete.limit_ext (F := degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) u v (fun n ↦ by
    apply Subtype.ext
    simpa using h (OrderDual.ofDual n))

/-- Helper for Lemma 10.98.4: if a homogeneous module summand has degree strictly larger than
the target degree, then every stage of the ambient tensor comparison has zero degree-`d`
component on the corresponding pure tensor. -/
private theorem decompose_tensor_stage_eq_zero_of_lt_module_degree
    (I : HomogeneousIdeal 𝒜)
    (𝓜 : ℤ → Submodule ℤ M)
    [SetLike.GradedSMul 𝒜 𝓜]
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, DirectSum.Decomposition (𝒢 n)]
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (hGI :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (hφn :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        (G_.map f).hom ∘ₗ φ (OrderDual.ofDual i) = φ (OrderDual.ofDual j))
    (hφ :
      ∀ n d {x : M}, x ∈ 𝓜 d → φ n x ∈ 𝒢 n d)
    {d₀ d : ℤ} {x : M}
    (hx : x ∈ 𝓜 d₀)
    (hd : d < d₀)
    (f' : AdicCompletion I.toIdeal A)
    (n : ℕ+) :
    ((DirectSum.decompose (𝒢 n)
        ((limit.π G_ (OrderDual.toDual n)).hom
          ((tensorProductComparison 𝒜 I G_ hGI φ hφn).hom (f' ⊗ₜ[A] x))) d : 𝒢 n d) :
        G_.obj (OrderDual.toDual n)) = 0 := by
  obtain ⟨a_n, ha_n⟩ := Submodule.Quotient.mk_surjective
    (I.toIdeal ^ ((n : ℕ)) • (⊤ : Submodule A A))
    (AdicCompletion.eval I.toIdeal A (n : ℕ) f')
  have hstage :
      (limit.π G_ (OrderDual.toDual n)).hom
          ((tensorProductComparison 𝒜 I G_ hGI φ hφn).hom (f' ⊗ₜ[A] x)) =
        φ n (a_n • x) := by
    exact tensorProductComparison_π_tmul_of_eval_eq
      (𝒜 := 𝒜) (I := I) (G_ := G_) (hGI := hGI) (φ := φ) (hφn := hφn)
      (n := n) (f' := f') (a := a_n) (x := x) ha_n.symm
  have hxG : φ n x ∈ 𝒢 n d₀ := hφ n d₀ hx
  -- Replace the stage value by a scalar multiple of a homogeneous vector and then apply the
  -- already established degree-inequality vanishing lemma.
  rw [hstage]
  simpa [LinearMap.map_smul] using
    (decompose_smul_eq_zero_of_lt_module_degree
      (𝒜 := 𝒜) (ℬ := 𝒢 n) (x := φ n x) (hx := hxG) (hd := hd) a_n)

/-- Helper for Lemma 10.98.4: after splitting a completion coefficient into low-degree, middle,
and tail pieces at the cutoff `d - d₀`, only the middle degree contributes to the degree-`d`
stage of the ambient tensor comparison. -/
private theorem decompose_tensor_stage_eq_middle_of_cutoff
    (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ 𝒜₊)
    (𝓜 : ℤ → Submodule ℤ M)
    [SetLike.GradedSMul 𝒜 𝓜]
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, DirectSum.Decomposition (𝒢 n)]
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (hGI :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (hφn :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        (G_.map f).hom ∘ₗ φ (OrderDual.ofDual i) = φ (OrderDual.ofDual j))
    (hφ :
      ∀ n d {x : M}, x ∈ 𝓜 d → φ n x ∈ 𝒢 n d)
    {d₀ d : ℤ} {x : M}
    (hx : x ∈ 𝓜 d₀)
    (hd : d₀ ≤ d)
    (f' : AdicCompletion I.toIdeal A)
    {a_lt : A}
    {a_eq : 𝒜 (Int.toNat (d - d₀))}
    {a_tail : A}
    (h_split :
      AdicCompletion.eval I.toIdeal A (Int.toNat (d - d₀) + 1)
          (f' - AdicCompletion.of I.toIdeal A (a_lt + (a_eq : A))) =
        Submodule.Quotient.mk a_tail)
    (h_lt :
      ∀ j, Int.toNat (d - d₀) ≤ j → ((DirectSum.decompose 𝒜 a_lt j : 𝒜 j) : A) = 0)
    (h_tail :
      ∀ j, j ≤ Int.toNat (d - d₀) → ((DirectSum.decompose 𝒜 a_tail j : 𝒜 j) : A) = 0)
    (n : ℕ+) :
    ((DirectSum.decompose (𝒢 n)
        ((limit.π G_ (OrderDual.toDual n)).hom
          ((tensorProductComparison 𝒜 I G_ hGI φ hφn).hom (f' ⊗ₜ[A] x))) d : 𝒢 n d) :
        G_.obj (OrderDual.toDual n)) =
      φ n ((a_eq : A) • x) := by
  let B : ℕ := Int.toNat (d - d₀)
  let tail : AdicCompletion I.toIdeal A :=
    f' - AdicCompletion.of I.toIdeal A (a_lt + (a_eq : A))
  obtain ⟨a_n, ha_n, ha_n_support⟩ :=
    completion_tail_low_degree_representatives
      (𝒜 := 𝒜) (I := I) (hI := hI) (tail := tail) (B := B)
      (a_succ := a_tail) h_split h_tail n
  have htail_def : tail = f' - AdicCompletion.of I.toIdeal A (a_lt + (a_eq : A)) := rfl
  have hsplit_completion :
      f' = AdicCompletion.of I.toIdeal A (a_lt + (a_eq : A)) + tail := by
    dsimp [tail]
    abel
  have h_eval_total :
      AdicCompletion.eval I.toIdeal A (n : ℕ) f' =
        Submodule.Quotient.mk (a_lt + (a_eq : A) + a_n) := by
    -- Rewrite the completion coefficient as the chosen low-degree part plus the residual tail,
    -- then evaluate each summand at stage `n`.
    calc
      AdicCompletion.eval I.toIdeal A (n : ℕ) f' =
          AdicCompletion.eval I.toIdeal A (n : ℕ)
            (AdicCompletion.of I.toIdeal A (a_lt + (a_eq : A)) + tail) := by
              rw [hsplit_completion]
      _ =
          AdicCompletion.eval I.toIdeal A (n : ℕ)
            (AdicCompletion.of I.toIdeal A (a_lt + (a_eq : A))) +
              AdicCompletion.eval I.toIdeal A (n : ℕ) tail := by
                rw [map_add]
      _ =
          (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A A)).mkQ (a_lt + (a_eq : A)) +
            (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A A)).mkQ a_n := by
              rw [AdicCompletion.eval_of]
              simpa using congrArg
                (fun z : A ⧸ (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A A)) ↦
                  (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A A)).mkQ (a_lt + (a_eq : A)) + z)
                ha_n
      _ = (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A A)).mkQ (a_lt + (a_eq : A) + a_n) := by
            rfl
      _ = Submodule.Quotient.mk (a_lt + (a_eq : A) + a_n) := by
            rfl
  have hxG : φ n x ∈ 𝒢 n d₀ := hφ n d₀ hx
  have hmid_mem :
      (a_eq : A) • φ n x ∈ 𝒢 n d := by
    have htmp :
        (a_eq : A) • φ n x ∈ 𝒢 n (Int.toNat (d - d₀) +ᵥ d₀) :=
      SetLike.GradedSMul.smul_mem (SetLike.coe_mem a_eq) hxG
    have hdeg :
        (Int.toNat (d - d₀) +ᵥ d₀ : ℤ) = d := by
      have hnonneg : 0 ≤ d - d₀ := sub_nonneg.mpr hd
      change (((Int.toNat (d - d₀) : ℕ) : ℤ) + d₀) = d
      calc
        (((Int.toNat (d - d₀) : ℕ) : ℤ) + d₀) = (d - d₀) + d₀ := by
          rw [Int.toNat_of_nonneg hnonneg]
        _ = d := by abel
    simpa [hdeg] using htmp
  have hlt_zero :
      ((DirectSum.decompose (𝒢 n) (a_lt • φ n x) d : 𝒢 n d) :
          G_.obj (OrderDual.toDual n)) = 0 := by
    simpa [B] using
      (decompose_smul_eq_zero_of_support_lt_cutoff
        (𝒜 := 𝒜) (ℬ := 𝒢 n) (x := φ n x) (hx := hxG) (hd := hd)
        (a_lt := a_lt) h_lt)
  have htail_zero :
      ((DirectSum.decompose (𝒢 n) (a_n • φ n x) d : 𝒢 n d) :
          G_.obj (OrderDual.toDual n)) = 0 := by
    simpa [B] using
      (decompose_smul_eq_zero_of_support_gt_cutoff
        (𝒜 := 𝒜) (ℬ := 𝒢 n) (x := φ n x) (hx := hxG) (hd := hd)
        (a_hi := a_n) ha_n_support)
  have hmid_decompose :
      ((DirectSum.decompose (𝒢 n) ((a_eq : A) • φ n x) d : 𝒢 n d) :
          G_.obj (OrderDual.toDual n)) =
        (a_eq : A) • φ n x := by
    simpa using (DirectSum.decompose_of_mem_same (𝒢 n) hmid_mem)
  -- Evaluate the pure tensor stagewise using the chosen representative, expand by linearity,
  -- and kill the low-degree and tail contributions with the cutoff lemmas.
  rw [tensorProductComparison_π_tmul_of_eval_eq
    (𝒜 := 𝒜) (I := I) (G_ := G_) (hGI := hGI) (φ := φ) (hφn := hφn)
    (n := n) (f' := f') (a := a_lt + (a_eq : A) + a_n) (x := x) h_eval_total]
  rw [LinearMap.map_smul]
  rw [add_smul, add_smul, DirectSum.decompose_add, DirectSum.decompose_add]
  simp [hlt_zero, hmid_decompose, htail_zero]

/-- Helper for Lemma 10.98.4: a finite ambient tensor preimage of a degree-`d` inverse-limit
element can be repackaged into a single element of `M_d` by keeping only the middle coefficients
in the source-proof cutoff decomposition. -/
private theorem exists_degree_piece_preimage_of_tensor_sum_preimage
    (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ 𝒜₊)
    (𝓜 : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜]
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, DirectSum.Decomposition (𝒢 n)]
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (h𝒢 :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j) (d : ℤ)
        {x : G_.obj i}, x ∈ 𝒢 (OrderDual.ofDual i) d →
          (G_.map f).hom x ∈ 𝒢 (OrderDual.ofDual j) d)
    (hGI :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (hφn :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        (G_.map f).hom ∘ₗ φ (OrderDual.ofDual i) = φ (OrderDual.ofDual j))
    (hφ :
      ∀ n d {x : M}, x ∈ 𝓜 d → φ n x ∈ 𝒢 n d)
    (d : ℤ)
    (y : ↑(limit (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d)))
    {k : ℕ}
    (a : Fin k → AdicCompletion I.toIdeal A)
    (m : Fin k → M)
    (hpreimage :
      (tensorProductComparison 𝒜 I G_ hGI φ hφn).hom
          (∑ j, a j ⊗ₜ[A] m j) =
        (degreewise_limit_forget_restrictScalars 𝒜 G_ 𝒢 h𝒢 d).hom y) :
    ∃ xMid : degreeZeroPiece 𝒜 𝓜 d,
      (degreewiseLimitMap 𝒜 𝓜 G_ 𝒢 h𝒢 φ hφn hφ d).hom xMid = y := by
  classical
  let S : Finset (Sigma fun _ : Fin k => ℤ) :=
    Finset.univ.sigma fun j ↦ (DirectSum.decompose 𝓜 (m j)).support
  let xComp : (Sigma fun _ : Fin k => ℤ) → M := fun p ↦
    ((DirectSum.decompose 𝓜 (m p.1) p.2 : 𝓜 p.2) : M)
  have hxComp : ∀ p, xComp p ∈ 𝓜 p.2 := by
    intro p
    exact SetLike.coe_mem (DirectSum.decompose 𝓜 (m p.1) p.2)
  have hsum_hom :
      (∑ j, a j ⊗ₜ[A] m j) =
        Finset.sum S (fun p ↦ a p.1 ⊗ₜ[A] xComp p) := by
    -- Rewrite the ambient finite sum once by decomposing each module term into homogeneous pieces.
    simpa [S, xComp] using
      (sum_tmul_eq_sum_homogeneous_tmul
        (𝒜 := 𝒜) (I := I) (𝓜 := 𝓜) (a := a) (m := m))
  have hpreimage' :
      (tensorProductComparison 𝒜 I G_ hGI φ hφn).hom
          (Finset.sum S (fun p ↦ a p.1 ⊗ₜ[A] xComp p)) =
        (degreewise_limit_forget_restrictScalars 𝒜 G_ 𝒢 h𝒢 d).hom y := by
    calc
      (tensorProductComparison 𝒜 I G_ hGI φ hφn).hom
          (Finset.sum S (fun p ↦ a p.1 ⊗ₜ[A] xComp p)) =
        (tensorProductComparison 𝒜 I G_ hGI φ hφn).hom
          (∑ j, a j ⊗ₜ[A] m j) := by
            rw [hsum_hom]
      _ = (degreewise_limit_forget_restrictScalars 𝒜 G_ 𝒢 h𝒢 d).hom y := hpreimage
  have hsplits :
      ∀ p : Sigma fun _ : Fin k => ℤ,
        ∃ a_lt : A, ∃ a_mid : 𝒜 (Int.toNat (d - p.2)), ∃ a_tail : A,
          AdicCompletion.eval I.toIdeal A (Int.toNat (d - p.2) + 1)
              (a p.1 - AdicCompletion.of I.toIdeal A (a_lt + (a_mid : A))) =
            Submodule.Quotient.mk a_tail ∧
            (∀ j, Int.toNat (d - p.2) ≤ j →
              ((DirectSum.decompose 𝒜 a_lt j : 𝒜 j) : A) = 0) ∧
            (∀ j, j ≤ Int.toNat (d - p.2) →
              ((DirectSum.decompose 𝒜 a_tail j : 𝒜 j) : A) = 0) := by
    intro p
    simpa using
      (completion_split_below_degree_stageSucc
        (𝒜 := 𝒜) (I := I) (f' := a p.1) (B := Int.toNat (d - p.2)))
  choose a_lt a_mid a_tail h_split h_lt h_tail using hsplits
  let T : Finset (Sigma fun _ : Fin k => ℤ) := S.filter fun p ↦ p.2 ≤ d
  let xMidVal : M :=
    Finset.sum T (fun p ↦ ((a_mid p : 𝒜 (Int.toNat (d - p.2))) : A) • xComp p)
  have hxMidVal_mem : xMidVal ∈ 𝓜 d := by
    -- Every retained middle coefficient has exactly the complementary degree needed to land in
    -- `M_d`.
    dsimp [xMidVal, T]
    refine Submodule.sum_mem _ ?_
    intro p hp
    have hp_le : p.2 ≤ d := (Finset.mem_filter.mp hp).2
    have hsmul :
        (((a_mid p : 𝒜 (Int.toNat (d - p.2))) : A) • xComp p) ∈
          𝓜 (Int.toNat (d - p.2) +ᵥ p.2) := by
      exact SetLike.GradedSMul.smul_mem (SetLike.coe_mem (a_mid p)) (hxComp p)
    have hdeg : (Int.toNat (d - p.2) +ᵥ p.2 : ℤ) = d := by
      have hnonneg : 0 ≤ d - p.2 := sub_nonneg.mpr hp_le
      change (((Int.toNat (d - p.2) : ℕ) : ℤ) + p.2) = d
      calc
        (((Int.toNat (d - p.2) : ℕ) : ℤ) + p.2) = (d - p.2) + p.2 := by
          rw [Int.toNat_of_nonneg hnonneg]
        _ = d := by abel
    simpa [hdeg] using hsmul
  let xMid : degreeZeroPiece 𝒜 𝓜 d := ⟨xMidVal, hxMidVal_mem⟩
  refine ⟨xMid, ?_⟩
  -- The source proof identifies the target element by checking the degree-`d` value at every
  -- ambient stage.
  apply degreewise_limit_ext_of_stagewise_val_eq
    (𝒜 := 𝒜) (G_ := G_) (𝒢 := 𝒢) (h𝒢 := h𝒢) (d := d)
  intro n
  let extract : ↑(limit G_) → G_.obj (OrderDual.toDual n) := fun z ↦
    ((DirectSum.decompose (𝒢 n) ((limit.π G_ (OrderDual.toDual n)).hom z) d : 𝒢 n d) :
      G_.obj (OrderDual.toDual n))
  let stageTerm : (Sigma fun _ : Fin k => ℤ) → G_.obj (OrderDual.toDual n) := fun p ↦
    ((DirectSum.decompose (𝒢 n)
        ((limit.π G_ (OrderDual.toDual n)).hom
          ((tensorProductComparison 𝒜 I G_ hGI φ hφn).hom (a p.1 ⊗ₜ[A] xComp p))) d :
        𝒢 n d) : G_.obj (OrderDual.toDual n))
  have hforget_stage :
      extract ((degreewise_limit_forget_restrictScalars 𝒜 G_ 𝒢 h𝒢 d).hom y) =
        ((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom y).1 := by
    have hforget_val :
        (limit.π G_ (OrderDual.toDual n)).hom
            ((degreewise_limit_forget_restrictScalars 𝒜 G_ 𝒢 h𝒢 d).hom y) =
          ((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom y).1 := by
      change
        (((degreewise_limit_forget_restrictScalars 𝒜 G_ 𝒢 h𝒢 d) ≫
            (ModuleCat.restrictScalars (algebraMap (𝒜 0) A)).map
              (limit.π G_ (OrderDual.toDual n))).hom y) =
          (((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)) ≫
              degreewiseStageSubtype 𝒜 G_ 𝒢 d n).hom y)
      rw [degreewise_limit_forget_restrictScalars_π]
    calc
      extract ((degreewise_limit_forget_restrictScalars 𝒜 G_ 𝒢 h𝒢 d).hom y) =
        ((DirectSum.decompose (𝒢 n)
            ((limit.π G_ (OrderDual.toDual n)).hom
              ((degreewise_limit_forget_restrictScalars 𝒜 G_ 𝒢 h𝒢 d).hom y)) d :
          𝒢 n d) : G_.obj (OrderDual.toDual n)) := by
            rfl
      _ = ((DirectSum.decompose (𝒢 n)
            (((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom y).1) d :
          𝒢 n d) : G_.obj (OrderDual.toDual n)) := by
            rw [hforget_val]
      _ = ((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom y).1 := by
            simpa using
              (DirectSum.decompose_of_mem_same
                (𝒢 n)
                ((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom y).2)
  have hstage_sum :
      Finset.sum S stageTerm =
        ((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom y).1 := by
    have hpreimage_n := congrArg extract hpreimage'
    have hstage_expand :
        extract
            ((tensorProductComparison 𝒜 I G_ hGI φ hφn).hom
              (Finset.sum S (fun p ↦ a p.1 ⊗ₜ[A] xComp p))) =
          Finset.sum S stageTerm := by
      dsimp [extract, stageTerm]
      rw [map_sum]
      have happly :
          (DirectSum.decompose (𝒢 n)
              (Finset.sum S fun p ↦
                (limit.π G_ (OrderDual.toDual n)).hom
                  ((tensorProductComparison 𝒜 I G_ hGI φ hφn).hom
                    (a p.1 ⊗ₜ[A] xComp p))) d : 𝒢 n d) =
            Finset.sum S (fun p ↦
              (DirectSum.decompose (𝒢 n)
                ((limit.π G_ (OrderDual.toDual n)).hom
                  ((tensorProductComparison 𝒜 I G_ hGI φ hφn).hom
                    (a p.1 ⊗ₜ[A] xComp p))) d : 𝒢 n d)) := by
        simpa using
          (DFinsupp.finset_sum_apply
            S
            (fun p ↦
              DirectSum.decompose (𝒢 n)
                ((limit.π G_ (OrderDual.toDual n)).hom
                  ((tensorProductComparison 𝒜 I G_ hGI φ hφn).hom
                    (a p.1 ⊗ₜ[A] xComp p))))
            d)
      simpa using congrArg (fun z : 𝒢 n d ↦ (z : G_.obj (OrderDual.toDual n))) happly
    calc
      Finset.sum S stageTerm =
        extract
          ((tensorProductComparison 𝒜 I G_ hGI φ hφn).hom
            (Finset.sum S (fun p ↦ a p.1 ⊗ₜ[A] xComp p))) := by
              exact hstage_expand.symm
      _ =
        extract ((degreewise_limit_forget_restrictScalars 𝒜 G_ 𝒢 h𝒢 d).hom y) := hpreimage_n
      _ =
        ((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom y).1 :=
          hforget_stage
  have hstage_filter :
      Finset.sum S stageTerm =
        Finset.sum T (fun p ↦ φ n (((a_mid p : 𝒜 (Int.toNat (d - p.2))) : A) • xComp p)) := by
    calc
      Finset.sum S stageTerm =
        Finset.sum S (fun p ↦
          if hp : p.2 ≤ d then
            φ n (((a_mid p : 𝒜 (Int.toNat (d - p.2))) : A) • xComp p)
          else 0) := by
            refine Finset.sum_congr rfl ?_
            intro p hpS
            by_cases hp : p.2 ≤ d
            · have hstage_p :
                  stageTerm p =
                    φ n (((a_mid p : 𝒜 (Int.toNat (d - p.2))) : A) • xComp p) := by
                simpa [stageTerm] using decompose_tensor_stage_eq_middle_of_cutoff
                  (𝒜 := 𝒜) (I := I) (hI := hI) (𝓜 := 𝓜) (G_ := G_) (𝒢 := 𝒢)
                  (hGI := hGI) (φ := φ) (hφn := hφn) (hφ := hφ)
                  (x := xComp p) (hx := hxComp p) (hd := hp) (f' := a p.1)
                  (a_lt := a_lt p) (a_eq := a_mid p) (a_tail := a_tail p)
                  (h_split := h_split p) (h_lt := h_lt p) (h_tail := h_tail p) (n := n)
              simp [hp, hstage_p]
            · have hstage_p : stageTerm p = 0 := by
                simpa [stageTerm] using decompose_tensor_stage_eq_zero_of_lt_module_degree
                  (𝒜 := 𝒜) (I := I) (𝓜 := 𝓜) (G_ := G_) (𝒢 := 𝒢)
                  (hGI := hGI) (φ := φ) (hφn := hφn) (hφ := hφ)
                  (x := xComp p) (hx := hxComp p) (hd := lt_of_not_ge hp)
                  (f' := a p.1) (n := n)
              simp [hp, hstage_p]
      _ =
        Finset.sum T (fun p ↦ φ n (((a_mid p : 𝒜 (Int.toNat (d - p.2))) : A) • xComp p)) := by
            simpa [T] using
              (Finset.sum_filter
                (s := S)
                (p := fun p : Sigma fun _ : Fin k => ℤ ↦ p.2 ≤ d)
                (f := fun p ↦
                  φ n (((a_mid p : 𝒜 (Int.toNat (d - p.2))) : A) • xComp p))).symm
  have hxMid_stage :
      ((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom
          ((degreewiseLimitMap 𝒜 𝓜 G_ 𝒢 h𝒢 φ hφn hφ d).hom xMid)).1 =
        Finset.sum T (fun p ↦ φ n (((a_mid p : 𝒜 (Int.toNat (d - p.2))) : A) • xComp p)) := by
    have hπxMid :
        ((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom
            ((degreewiseLimitMap 𝒜 𝓜 G_ 𝒢 h𝒢 φ hφn hφ d).hom xMid)).1 =
          φ n xMid.1 := by
      exact congrArg
        (fun f :
          ModuleCat.of (𝒜 0) (degreeZeroPiece 𝒜 𝓜 d) ⟶
            ModuleCat.of (𝒜 0) (degreeZeroPiece 𝒜 (𝒢 n) d) ↦
          (f.hom xMid).1)
        (degreewiseLimitMap_π
          (𝒜 := 𝒜) (𝓜 := 𝓜) (G_ := G_) (𝒢 := 𝒢) (h𝒢 := h𝒢) (φ := φ)
          (hφn := hφn) (hφ := hφ) (d := d) (n := n))
    calc
      ((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom
          ((degreewiseLimitMap 𝒜 𝓜 G_ 𝒢 h𝒢 φ hφn hφ d).hom xMid)).1 =
        φ n xMid.1 := hπxMid
      _ = φ n xMidVal := rfl
      _ = φ n (Finset.sum T fun p ↦ ((a_mid p : 𝒜 (Int.toNat (d - p.2))) : A) • xComp p) := rfl
      _ = Finset.sum T (fun p ↦ φ n (((a_mid p : 𝒜 (Int.toNat (d - p.2))) : A) • xComp p)) := by
            simpa [LinearMap.map_smul] using
              (map_sum (φ n) (fun p ↦ ((a_mid p : 𝒜 (Int.toNat (d - p.2))) : A) • xComp p) T)
  have hy_stage :
      Finset.sum T (fun p ↦ φ n (((a_mid p : 𝒜 (Int.toNat (d - p.2))) : A) • xComp p)) =
        ((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom y).1 := by
    calc
      Finset.sum T (fun p ↦ φ n (((a_mid p : 𝒜 (Int.toNat (d - p.2))) : A) • xComp p)) =
        Finset.sum S stageTerm := by
          simpa using hstage_filter.symm
      _ =
        ((limit.π (degreewiseSystem 𝒜 G_ 𝒢 h𝒢 d) (OrderDual.toDual n)).hom y).1 := by
          simpa using hstage_sum
  exact hxMid_stage.trans hy_stage

/-- Helper for Lemma 10.98.4: once the underlying degreewise comparison map is bijective, the
corresponding morphism in `ModuleCat (𝒜 0)` is automatically an isomorphism. -/
private theorem degreewiseLimitMap_isIso_of_bijective
    (𝓜 : ℤ → Submodule ℤ M)
    [SetLike.GradedSMul 𝒜 𝓜]
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (h𝒢 :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j) (d : ℤ)
        {x : G_.obj i}, x ∈ 𝒢 (OrderDual.ofDual i) d →
          (G_.map f).hom x ∈ 𝒢 (OrderDual.ofDual j) d)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (hφn :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        (G_.map f).hom ∘ₗ φ (OrderDual.ofDual i) = φ (OrderDual.ofDual j))
    (hφ :
      ∀ n d {x : M}, x ∈ 𝓜 d → φ n x ∈ 𝒢 n d)
    (d : ℤ)
    (hbij :
      Function.Bijective
        (degreewiseLimitMap 𝒜 𝓜 G_ 𝒢 h𝒢 φ hφn hφ d).hom) :
    IsIso (degreewiseLimitMap 𝒜 𝓜 G_ 𝒢 h𝒢 φ hφn hφ d) := by
  -- `ModuleCat` is concrete, so bijectivity of the underlying linear map is the exact
  -- categorical isomorphism criterion we need for the final step.
  exact (ConcreteCategory.isIso_iff_bijective _).2 hbij

/-- Lemma 10.98.4: let `(Gₙ)` be a sequential inverse system of graded `A`-modules indexed by
positive integers and annihilated stagewise by `I^n`, and let `φₙ : M → Gₙ` be a compatible
family of degree-preserving maps. If the canonical tensor-product comparison
`A' ⊗[A] M → \varprojlim Gₙ`, with `A'` the `I`-adic completion of `A`, is an isomorphism, then
for every degree `d : ℤ` the canonical induced map `M_d → \varprojlim G_{n,d}` is an isomorphism
as a map of `A₀ = 𝒜 0`-modules, provided the homogeneous ideal `I` is contained in the irrelevant
ideal `𝒜₊`.

This is the source statement `M ⊗_A A' → \varprojlim G_n`, written using the canonically
equivalent left-tensor form in mathlib. In Lean the hypothesis is exactly that the canonical
morphism `tensorProductComparison 𝒜 I G_ hGI φ hφn` is an isomorphism. -/
theorem graded_tensorProductComparison_isIso_implies_degreewiseLimitMap_isIso
    (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ 𝒜₊)
    (𝓜 : ℤ → Submodule ℤ M) [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜]
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{u} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, DirectSum.Decomposition (𝒢 n)]
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (h𝒢 :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j) (d : ℤ)
        {x : G_.obj i}, x ∈ 𝒢 (OrderDual.ofDual i) d →
          (G_.map f).hom x ∈ 𝒢 (OrderDual.ofDual j) d)
    (hGI :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (φ : ∀ n : ℕ+, M →ₗ[A] G_.obj (OrderDual.toDual n))
    (hφn :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        (G_.map f).hom ∘ₗ φ (OrderDual.ofDual i) = φ (OrderDual.ofDual j))
    (hφ :
      ∀ n d {x : M}, x ∈ 𝓜 d → φ n x ∈ 𝒢 n d)
    [IsIso (tensorProductComparison 𝒜 I G_ hGI φ hφn)] :
    ∀ d : ℤ, IsIso (degreewiseLimitMap 𝒜 𝓜 G_ 𝒢 h𝒢 φ hφn hφ d) := by
  intro d
  -- Reduce the source statement to bijectivity of the underlying `(𝒜 0)`-linear map on the
  -- `d`th homogeneous piece; the remaining work is exactly the source-proof injective/surjective
  -- decomposition.
  apply degreewiseLimitMap_isIso_of_bijective (𝒜 := 𝒜) (𝓜 := 𝓜) (G_ := G_) (𝒢 := 𝒢)
    (h𝒢 := h𝒢) (φ := φ) (hφn := hφn) (hφ := hφ) (d := d)
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    let f := (degreewiseLimitMap 𝒜 𝓜 G_ 𝒢 h𝒢 φ hφn hφ d).hom
    have hxy_zero :
        f (x - y) = 0 := by
      -- The injectivity step is reduced to a kernel computation on one homogeneous element.
      calc
        f (x - y) = f x - f y := by
          exact map_sub f x y
        _ = 0 := by
          rw [hxy, sub_self]
    -- Route correction: after restoring the local projection API, first pass from the degreewise
    -- kernel to the ambient tensor-kernel statement and only then resume the source's finite
    -- support descent.
    have htensor_zero :
        (tensorProductComparison 𝒜 I G_ hGI φ hφn).hom
            ((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] (x - y).1) = 0 := by
      exact tensorProductComparison_eq_zero_of_degreewise_zero
        (𝒜 := 𝒜) (I := I) (𝓜 := 𝓜) (G_ := G_) (𝒢 := 𝒢) (h𝒢 := h𝒢) (hGI := hGI)
        (φ := φ) (hφn := hφn) (hφ := hφ) (d := d) (z := x - y) hxy_zero
    have hcomparison_inj :
        Function.Injective (tensorProductComparison 𝒜 I G_ hGI φ hφn).hom :=
      ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
    have htmul_zero :
        ((1 : AdicCompletion I.toIdeal A) ⊗ₜ[A] (x - y).1) = 0 := by
      apply hcomparison_inj
      simpa using htensor_zero
    obtain ⟨s, hs_homogeneous, hzspan, hspan_zero⟩ :=
      exists_homogeneous_span_one_tmul_eq_zero
        (𝒜 := 𝒜) (I := I) (𝓜 := 𝓜) (d := d) (z := x - y) htmul_zero
    -- Route correction: the ambient kernel has now been reduced all the way to a finite
    -- homogeneous span, exactly as in the source proof. What remains is the source's low-degree
    -- quotient injectivity argument on this finite homogeneous family.
    have hstage_quotient :
        ∀ n : ℕ+,
          (Submodule.Quotient.mk
              (⟨(x - y).1, hzspan⟩ : Submodule.span A (s : Set M)) :
            Submodule.span A (s : Set M) ⧸
              (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (Submodule.span A (s : Set M))))) = 0 := by
      intro n
      -- The finite-span tensor relation now descends stagewise to the quotient statement that the
      -- source proof uses before the minimal-degree argument.
      exact quotient_mk_eq_zero_of_one_tmul_zero_stage
        (𝒜 := 𝒜) (I := I) (P := Submodule.span A (s : Set M))
        (z := ⟨(x - y).1, hzspan⟩) hspan_zero n
    by_cases hs_empty : s = ∅
    · have hzero : (x - y).1 = 0 := by
        have : (x - y).1 ∈ (⊥ : Submodule A M) := by
          simpa [hs_empty] using hzspan
        simpa using this
      apply Subtype.ext
      simpa using hzero
    · have hs_nonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs_empty
      obtain ⟨x₀, hx₀, hx₀_min⟩ :=
        Finset.exists_min_image s.attach
          (fun z : {z // z ∈ s} => homogeneousDegree 𝓜 z.1 (hs_homogeneous z.1 z.2))
          hs_nonempty.attach
      let m : ℤ := homogeneousDegree 𝓜 x₀.1 (hs_homogeneous x₀.1 x₀.2)
      have hs_lower :
          ∀ z, ∀ hz : z ∈ s, m ≤ homogeneousDegree 𝓜 z (hs_homogeneous z hz) := by
        intro z hz
        exact hx₀_min ⟨z, hz⟩ (by simp)
      let n : ℕ+ := ⟨Int.toNat (d - m) + 1, Nat.succ_pos _⟩
      have hzpow_subtype :
          (⟨(x - y).1, hzspan⟩ : Submodule.span A (s : Set M)) ∈
            I.toIdeal ^ (n : ℕ) •
              (⊤ : Submodule A (Submodule.span A (s : Set M))) := by
        exact (Submodule.Quotient.mk_eq_zero _).1 (hstage_quotient n)
      have hzpow :
          (x - y).1 ∈
            I.toIdeal ^ (Int.toNat (d - m) + 1) • Submodule.span A (s : Set M) := by
        simpa [n] using
          (Submodule.mem_smul_top_iff
            (I := I.toIdeal ^ (n : ℕ))
            (N := Submodule.span A (s : Set M))
            (x := ⟨(x - y).1, hzspan⟩)).1 hzpow_subtype
      have hzero : (x - y).1 = 0 := by
        exact eq_zero_of_homogeneous_mem_pow_smul_span_of_degree_lower_bound
          (𝒜 := 𝒜) (I := I) (hI := hI) (𝓜 := 𝓜)
          (s := s) hs_homogeneous m d hs_lower hzpow
      apply Subtype.ext
      simpa using hzero
  · intro y
    -- Route correction: the surjective half should first be reduced to an explicit finite sum in
    -- `AdicCompletion(I) ⊗ M`, and only then should the source's coefficient truncation be applied
    -- to each homogeneous module summand.
    classical
    let yAmbient : ↑(limit G_) :=
      (degreewise_limit_forget_restrictScalars 𝒜 G_ 𝒢 h𝒢 d).hom y
    let t : AdicCompletion I.toIdeal A ⊗[A] M :=
      (inv (tensorProductComparison 𝒜 I G_ hGI φ hφn)).hom yAmbient
    obtain ⟨k, a, m, ht⟩ := TensorProduct.exists_sum_tmul_eq t
    have hpreimage :
        (tensorProductComparison 𝒜 I G_ hGI φ hφn).hom
            (∑ j, a j ⊗ₜ[A] m j) = yAmbient := by
      -- Pull the ambient inverse-limit element back through the chosen inverse and rewrite the
      -- preimage as a finite sum of pure tensors.
      calc
        (tensorProductComparison 𝒜 I G_ hGI φ hφn).hom (∑ j, a j ⊗ₜ[A] m j) =
            (tensorProductComparison 𝒜 I G_ hGI φ hφn).hom t := by
              simpa [ht]
        _ = yAmbient := by
              simpa [t] using
                (Iso.inv_hom_id_apply
                  (asIso (tensorProductComparison 𝒜 I G_ hGI φ hφn)) yAmbient)
    obtain ⟨xMid, hxMid⟩ :=
      exists_degree_piece_preimage_of_tensor_sum_preimage
        (𝒜 := 𝒜) (I := I) (hI := hI) (𝓜 := 𝓜) (G_ := G_) (𝒢 := 𝒢)
        (h𝒢 := h𝒢) (hGI := hGI) (φ := φ) (hφn := hφn) (hφ := hφ)
        (d := d) (y := y) (a := a) (m := m) (by simpa [yAmbient] using hpreimage)
    exact ⟨xMid, hxMid⟩

end
