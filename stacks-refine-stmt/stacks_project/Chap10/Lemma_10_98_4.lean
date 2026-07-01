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
  sorry

end
