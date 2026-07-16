import Mathlib
import StacksProject_2024.stacks_project.Chap15.Remark_15_119_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open CategoryTheory
open scoped TensorProduct

universe u v w x

variable {R : Type u} [CommRing R]

local notation3:max "det(" M ")" => Module.det R M

section DeterminantLineMaps

variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

-- Proof sketch: the two algebra maps induced by `e` and `e.symm` compose to the identity because
-- `ExteriorAlgebra.map` is functorial and `e.symm` is inverse to `e`.
/-- The exterior-algebra map induced by `e.symm` is a left inverse to the map induced by `e`. -/
theorem exteriorAlgebraLinearEquiv_left_inv (e : M ≃ₗ[R] N) :
    (ExteriorAlgebra.map e.symm.toLinearMap).toLinearMap.comp
        (ExteriorAlgebra.map e.toLinearMap).toLinearMap =
      LinearMap.id := sorry

-- Proof sketch: the same functoriality argument shows that first applying the map induced by
-- `e.symm` and then the one induced by `e` is the identity on `ExteriorAlgebra R N`.
/-- The exterior-algebra map induced by `e` is a right inverse to the map induced by `e.symm`. -/
theorem exteriorAlgebraLinearEquiv_right_inv (e : M ≃ₗ[R] N) :
    (ExteriorAlgebra.map e.toLinearMap).toLinearMap.comp
        (ExteriorAlgebra.map e.symm.toLinearMap).toLinearMap =
      LinearMap.id := sorry

/-- The equivalence of exterior algebras induced by a linear equivalence of modules. -/
def exteriorAlgebraLinearEquiv (e : M ≃ₗ[R] N) :
    ExteriorAlgebra R M ≃ₗ[R] ExteriorAlgebra R N :=
  LinearEquiv.ofLinear
    (ExteriorAlgebra.map e.toLinearMap).toLinearMap
    (ExteriorAlgebra.map e.symm.toLinearMap).toLinearMap
    (exteriorAlgebraLinearEquiv_right_inv e)
    (exteriorAlgebraLinearEquiv_left_inv e)

-- Proof sketch: if `x` is annihilated by every generator `ι m`, then after applying the exterior
-- algebra map induced by `e`, the image is annihilated by every generator `ι n` because each `n`
-- is `e m` for some `m`.
/-- A linear equivalence carries the determinant line of the source module onto the determinant
line of the target module. -/
theorem determinantLine_map_eq (e : M ≃ₗ[R] N) :
    Submodule.map (ExteriorAlgebra.map e.toLinearMap).toLinearMap det(M) = det(N) := sorry

/-- The map induced by a linear equivalence on determinant lines realized as the degree-one
annihilator submodules inside exterior algebras. -/
def determinantLineMap (e : M ≃ₗ[R] N) :
    det(M) ≃ₗ[R] det(N) :=
  (exteriorAlgebraLinearEquiv e).ofSubmodules
    det(M)
    det(N)
    (determinantLine_map_eq e)

/-- `determinantLineMap` is given by the exterior-algebra map induced by the underlying linear
equivalence. -/
theorem determinantLineMap_apply (e : M ≃ₗ[R] N)
    (x : det(M)) :
    (determinantLineMap e x : ExteriorAlgebra R N) =
      ExteriorAlgebra.map e.toLinearMap x := rfl

end DeterminantLineMaps

namespace CategoryTheory.ShortComplex.ShortExact

section

variable {S : ShortComplex (ModuleCat R)}
variable [Module.Finite R S.X₁] [Module.Projective R S.X₁]
variable [Module.Finite R S.X₂] [Module.Projective R S.X₂]
variable [Module.Finite R S.X₃] [Module.Projective R S.X₃]

-- Proof sketch: localize the short exact sequence at every prime so it splits, use the wedge
-- product formula there, and then descend by uniqueness. The wedge formula determines the map on
-- pure tensors, hence uniquely determines the linear equivalence.
/-- The canonical determinant-line comparison map attached to a short exact sequence
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of finite projective `R`-modules is uniquely characterized by the
lift-and-wedge formula from the second proof in the text. -/
theorem existsUnique_determinantTensorIso (hS : S.ShortExact) :
    ∃! γ : (det(S.X₁) ⊗[R] det(S.X₃)) ≃ₗ[R] det(S.X₂),
      ∀ (x₁ : det(S.X₁)) (x₃ : det(S.X₃)) (y₃ : ExteriorAlgebra R S.X₂)
        (hy₃ : ExteriorAlgebra.map S.g.hom y₃ = (x₃ : ExteriorAlgebra R S.X₃)),
          (γ (x₁ ⊗ₜ[R] x₃) : ExteriorAlgebra R S.X₂) =
            ExteriorAlgebra.map S.f.hom (x₁ : ExteriorAlgebra R S.X₁) * y₃ := sorry

/-- The determinant-line comparison map canonically attached to a short exact sequence of finite
projective `R`-modules. -/
noncomputable def determinantTensorIso (hS : S.ShortExact) :
    (det(S.X₁) ⊗[R] det(S.X₃)) ≃ₗ[R] det(S.X₂) :=
  Classical.choose (existsUnique_determinantTensorIso hS)

/-- The canonical determinant comparison map for a short exact sequence satisfies the wedge
formula from the source text. -/
theorem determinantTensorIso_spec (hS : S.ShortExact)
    (x₁ : det(S.X₁)) (x₃ : det(S.X₃)) (y₃ : ExteriorAlgebra R S.X₂)
    (hy₃ : ExteriorAlgebra.map S.g.hom y₃ = (x₃ : ExteriorAlgebra R S.X₃)) :
    (hS.determinantTensorIso (x₁ ⊗ₜ[R] x₃) : ExteriorAlgebra R S.X₂) =
      ExteriorAlgebra.map S.f.hom (x₁ : ExteriorAlgebra R S.X₁) * y₃ := by
  obtain ⟨hγ, -⟩ := Classical.choose_spec (existsUnique_determinantTensorIso hS)
  exact hγ x₁ x₃ y₃ hy₃

end

end CategoryTheory.ShortComplex.ShortExact

section

variable {M' : Type v} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
  [Module.Projective R M']
variable {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
variable {M'' : Type x} [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
  [Module.Projective R M'']

/-- Bridge/view: the short complex in `ModuleCat R` canonically attached to a presented exact row
`M' ⟶ M ⟶ M''`, after universe-lifting the three modules to a common universe level. -/
abbrev shortComplexOfShortExact
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hexact : Function.Exact f g) :
    ShortComplex (ModuleCat.{max v (max w x)} R) :=
  ShortComplex.moduleCatMk
    ((((ULift.moduleEquiv : ULift.{max v (max w x), w} M ≃ₗ[R] M).symm.toLinearMap :
        M →ₗ[R] ULift.{max v (max w x), w} M).comp
      (f.comp ((ULift.moduleEquiv : ULift.{max v (max w x), v} M' ≃ₗ[R] M').toLinearMap :
        ULift.{max v (max w x), v} M' →ₗ[R] M'))))
    ((((ULift.moduleEquiv : ULift.{max v (max w x), x} M'' ≃ₗ[R] M'').symm.toLinearMap :
        M'' →ₗ[R] ULift.{max v (max w x), x} M'').comp
      (g.comp ((ULift.moduleEquiv : ULift.{max v (max w x), w} M ≃ₗ[R] M).toLinearMap :
        ULift.{max v (max w x), w} M →ₗ[R] M))))
    <| by
      ext x
      simp
      simpa using congr_fun hexact.comp_eq_zero (ULift.down x)

/-- The short complex attached to a presented short exact sequence is short exact. -/
theorem shortComplexOfShortExact_shortExact
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hf : Function.Injective f)
    (hg : Function.Surjective g) (hexact : Function.Exact f g) :
    (shortComplexOfShortExact f g hexact).ShortExact := by
  have hExact : (shortComplexOfShortExact f g hexact).Exact := by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (shortComplexOfShortExact f g hexact)]
    intro y
    constructor
    · intro hy
      have hyUp : ULift.up (g y.down) = 0 := by
        simpa [shortComplexOfShortExact] using hy
      have hy' : g y.down = 0 := by
        simpa using congr_arg ULift.down hyUp
      obtain ⟨x, hx⟩ := (hexact y.down).1 hy'
      refine ⟨⟨x⟩, ?_⟩
      change ULift.up (f x) = y
      apply ULift.ext
      simpa using hx
    · rintro ⟨x, rfl⟩
      change ULift.up (g (f x.down)) = 0
      apply ULift.ext
      simpa using congr_fun hexact.comp_eq_zero x.down
  have hMono : Mono (shortComplexOfShortExact f g hexact).f := by
    rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    change ULift.up (f x.down) = ULift.up (f y.down) at hxy
    apply ULift.ext
    apply hf
    simpa using congr_arg ULift.down hxy
  have hEpi : Epi (shortComplexOfShortExact f g hexact).g := by
    rw [ModuleCat.epi_iff_surjective]
    intro z
    obtain ⟨y, hy⟩ := hg z.down
    refine ⟨⟨y⟩, ?_⟩
    change ULift.up (g y) = z
    apply ULift.ext
    simpa using hy
  exact ShortComplex.ShortExact.mk' hExact hMono hEpi

/-- Bridge/view: when a short exact sequence of finite projective modules is presented by linear
maps `f` and `g`, this is the canonical determinant-line comparison map attached to that
presentation. -/
noncomputable abbrev determinantTensorIsoOfShortExact
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hf : Function.Injective f)
    (hg : Function.Surjective g) (hexact : Function.Exact f g) :
    (det(M') ⊗[R] det(M'')) ≃ₗ[R] det(M) :=
  let _ : Module.Finite R (shortComplexOfShortExact f g hexact).X₁ := by
    change Module.Finite R (ULift.{max v (max w x), v} M')
    infer_instance
  let _ : Module.Finite R (shortComplexOfShortExact f g hexact).X₂ := by
    change Module.Finite R (ULift.{max v (max w x), w} M)
    infer_instance
  let _ : Module.Finite R (shortComplexOfShortExact f g hexact).X₃ := by
    change Module.Finite R (ULift.{max v (max w x), x} M'')
    infer_instance
  let _ : Module.Projective R (shortComplexOfShortExact f g hexact).X₁ :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{max v (max w x), v} M' ≃ₗ[R] M').symm)
  let _ : Module.Projective R (shortComplexOfShortExact f g hexact).X₂ :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{max v (max w x), w} M ≃ₗ[R] M).symm)
  let _ : Module.Projective R (shortComplexOfShortExact f g hexact).X₃ :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{max v (max w x), x} M'' ≃ₗ[R] M'').symm)
  let _ : Module.Projective R (ULift.{max v (max w x), v} M') :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{max v (max w x), v} M' ≃ₗ[R] M').symm)
  let _ : Module.Projective R (ULift.{max v (max w x), w} M) :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{max v (max w x), w} M ≃ₗ[R] M).symm)
  let _ : Module.Projective R (ULift.{max v (max w x), x} M'') :=
    Module.Projective.of_equiv
      ((ULift.moduleEquiv : ULift.{max v (max w x), x} M'' ≃ₗ[R] M'').symm)
  (TensorProduct.congr
      (determinantLineMap
        ((ULift.moduleEquiv : ULift.{max v (max w x), v} M' ≃ₗ[R] M').symm))
      (determinantLineMap
        ((ULift.moduleEquiv : ULift.{max v (max w x), x} M'' ≃ₗ[R] M'').symm))).trans
    ((shortComplexOfShortExact_shortExact f g hf hg hexact).determinantTensorIso.trans
      (determinantLineMap
        (ULift.moduleEquiv : ULift.{max v (max w x), w} M ≃ₗ[R] M)))

/-- The map-level bridge `determinantTensorIsoOfShortExact` satisfies the same wedge formula as
the owner-level canonical map on the associated short exact short complex. -/
theorem determinantTensorIsoOfShortExact_spec
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hf : Function.Injective f)
    (hg : Function.Surjective g) (hexact : Function.Exact f g)
    (x' : det(M')) (x'' : det(M'')) (y'' : ExteriorAlgebra R M)
    (hy'' : ExteriorAlgebra.map g y'' = (x'' : ExteriorAlgebra R M'')) :
    (determinantTensorIsoOfShortExact f g hf hg hexact (x' ⊗ₜ[R] x'') :
        ExteriorAlgebra R M) =
      ExteriorAlgebra.map f (x' : ExteriorAlgebra R M') * y'' := sorry

-- Proof sketch: apply the owner-level canonical construction to the short complex associated to
-- `f` and `g`; the displayed witness is exactly the bridge `determinantTensorIsoOfShortExact`.
/-- Lemma 15.119.2: for a short exact sequence of finite projective `R`-modules, there exists a
canonical determinant-line isomorphism characterized by wedging an element from the left
determinant line with any lift of an element from the right determinant line. -/
theorem exists_determinant_tensor_iso_of_short_exact
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hf : Function.Injective f)
    (hg : Function.Surjective g) (hexact : Function.Exact f g) :
    ∃ γ : (det(M') ⊗[R] det(M'')) ≃ₗ[R] det(M),
      ∀ (x' : det(M')) (x'' : det(M'')) (y'' : ExteriorAlgebra R M)
        (_hy'' : ExteriorAlgebra.map g y'' = (x'' : ExteriorAlgebra R M'')),
          (γ (x' ⊗ₜ[R] x'') : ExteriorAlgebra R M) =
            ExteriorAlgebra.map f (x' : ExteriorAlgebra R M') * y'' := by
  refine ⟨determinantTensorIsoOfShortExact f g hf hg hexact, ?_⟩
  intro x' x'' y'' hy''
  exact determinantTensorIsoOfShortExact_spec f g hf hg hexact x' x'' y'' hy''

end
