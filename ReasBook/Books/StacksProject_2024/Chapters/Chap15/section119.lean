import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_15_119_1 (from Chap15) -/
open ExteriorAlgebra

universe u v

noncomputable section

namespace Module

/- Domain-style sampling for Remark 15.119.1:
- primary domain: determinant lines of finite projective modules, realized via exterior algebra;
- sampled owner declarations of the same kind:
  `ExteriorAlgebra.exteriorPower`,
  `ExteriorAlgebra.ι`,
  `Module.Invertible`,
  `(tensorLeft (ModuleCat.of R M)).IsEquivalence`,
  `ModuleCat.tensorLeft_isEquivalence_iff_moduleInvertible`;
- best owner abstraction:
  `source-facing`: the determinant line of a finite projective `R`-module `M`, realized by the
  annihilator owner `Module.det R M`;
  `core/canonical`: the Chapter `15` owner
  `(tensorLeft (ModuleCat.of R (Module.det R M))).IsEquivalence` for invertibility statements;
  `bridge/view`: the exterior-algebra annihilator description from the remark, together with the
  constant-rank identification with the top exterior power `⋀[R]^r M`;
- primitive vs. derived:
  primitive public data is the annihilator owner `Module.det R M` for an arbitrary `R`-module;
  the source-faithful finite-projective determinant-line interpretation, the constant-rank
  top-exterior-power comparison, and the specialized `Module.Invertible` statement are derived
  bridge API built from that owner.

This file therefore keeps the annihilator submodule as the owner, and places the finite-projective
content of Remark `15.119.1` in the derived bridge results that identify this owner with the
determinant line and its invertibility consequences.
-/

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The exterior-algebra annihilator submodule used in Remark `15.119.1` to realize the
determinant line of a finite projective module. The finite-projective content is carried by the
bridge results below, not by this owner itself. -/
abbrev det : Submodule R (ExteriorAlgebra R M) :=
  ⨅ m : M, (LinearMap.mulLeft R (ι R m)).ker

scoped[DeterminantLine] notation3:max "det(" M ")" => Module.det _ M

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

open scoped DeterminantLine

/-- Membership in `det(M)` is equivalent to being annihilated by left multiplication by
every degree-one generator of `ExteriorAlgebra R M`. -/
@[simp]
theorem mem_det_iff (x : ExteriorAlgebra R M) :
    x ∈ det(M) ↔ ∀ m : M, ι R m * x = 0 := by
  simp [Module.det]

section

variable [Module.Finite R M] [Module.Projective R M]

/-- Under a constant rank hypothesis, the determinant line agrees with the top exterior power
inside `ExteriorAlgebra R M`. This presents the exterior-algebra annihilator owner as the
standard top-exterior-power model under stronger assumptions. -/
theorem det_eq_topExteriorPower_of_rankAtStalk_eq (r : ℕ)
    (hM : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) :
    det(M) = ⋀[R]^r M := by
  sorry

/-- The determinant line of a finite projective module is invertible as an `R`-module. Via
Definition `15.118.1`, this is equivalent to the Chapter `15` tensor-left invertibility owner. -/
instance det_invertible : Module.Invertible R (Module.det R M) :=
  by
    sorry

end

end Module

end

/-! ### Lemma_15_119_2 (from Chap15) -/
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

/-! ### Lemma_15_119_3 (from Chap15) -/
noncomputable section
open CategoryTheory
open scoped TensorProduct
open scoped DeterminantLine

universe u v

variable {R : Type u} [CommRing R]

/-
Domain-style sampling for determinant-line comparison maps:
- primary domain: determinant lines of finite projective modules and the canonical comparison map
  attached to a short exact sequence;
- sampled owner declarations:
  * `CategoryTheory.ShortComplex.ShortExact.determinantTensorIso`,
  * `determinantTensorIsoOfShortExact`,
  * `shortComplexOfShortExact`,
  * `determinantLineMap`,
  * `CategoryTheory.ShortComplex.π₁.mapIso`,
  * `CategoryTheory.ShortComplex.π₂.mapIso`,
  * `CategoryTheory.ShortComplex.π₃.mapIso`;
- best owner abstraction: the canonical comparison map is the owner-level
  `CategoryTheory.ShortComplex.ShortExact.determinantTensorIso` on a short exact `ShortComplex`;
  the presentation-to-`ShortComplex` bridge is `shortComplexOfShortExact`, and the linear-map
  naturality theorem below is therefore a `bridge/view`;
- primitive data: an isomorphism of short exact sequences;
- derived API: the determinant-line maps induced on the left, middle, and right terms and the
  resulting tensor-product comparison map.
-/

namespace CategoryTheory.ShortComplex

namespace ShortExact

section Naturality

variable {S T : ShortComplex (ModuleCat R)}
variable [Module.Finite R S.X₁] [Module.Projective R S.X₁]
variable [Module.Finite R S.X₂] [Module.Projective R S.X₂]
variable [Module.Finite R S.X₃] [Module.Projective R S.X₃]
variable [Module.Finite R T.X₁] [Module.Projective R T.X₁]
variable [Module.Finite R T.X₂] [Module.Projective R T.X₂]
variable [Module.Finite R T.X₃] [Module.Projective R T.X₃]

/-- Core/canonical: an isomorphism of short exact sequences of finite projective `R`-modules
intertwines the owner-level determinant-line comparison maps. -/
theorem determinantTensorIso_naturality
    (hS : S.ShortExact) (e : S ≅ T) :
    CommSq
      (ModuleCat.ofHom <| hS.determinantTensorIso.toLinearMap)
      (ModuleCat.ofHom <|
        (TensorProduct.congr
          (determinantLineMap ((π₁.mapIso e).toLinearEquiv))
          (determinantLineMap ((π₃.mapIso e).toLinearEquiv))).toLinearMap)
      (ModuleCat.ofHom <| (determinantLineMap ((π₂.mapIso e).toLinearEquiv)).toLinearMap)
      (ModuleCat.ofHom <| (shortExact_of_iso e hS).determinantTensorIso.toLinearMap) := by
  sorry

end Naturality
end ShortExact
end CategoryTheory.ShortComplex

section Naturality

variable {M' : Type v} [AddCommGroup M'] [Module R M']
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M'' : Type v} [AddCommGroup M''] [Module R M'']
variable {K' : Type v} [AddCommGroup K'] [Module R K']
variable {K : Type v} [AddCommGroup K] [Module R K]
variable {K'' : Type v} [AddCommGroup K''] [Module R K'']

private theorem injective_of_commSq
    {f : M' →ₗ[R] M} {fK : K' →ₗ[R] K}
    (hf : Function.Injective f) (u : M' ≃ₗ[R] K') (v : M ≃ₗ[R] K)
    (huv : v.toLinearMap.comp f = fK.comp u.toLinearMap) :
    Function.Injective fK := by
  intro x y hxy
  have hx : v (f (u.symm x)) = fK x := by
    simpa using congrArg (fun φ : M' →ₗ[R] K ↦ φ (u.symm x)) huv
  have hy : v (f (u.symm y)) = fK y := by
    simpa using congrArg (fun φ : M' →ₗ[R] K ↦ φ (u.symm y)) huv
  have hxy' : u.symm x = u.symm y := hf <| v.injective <| hx.trans (hxy.trans hy.symm)
  exact u.symm.injective hxy'

private theorem surjective_of_commSq
    {g : M →ₗ[R] M''} {gK : K →ₗ[R] K''}
    (hg : Function.Surjective g) (v : M ≃ₗ[R] K) (w : M'' ≃ₗ[R] K'')
    (hvw : w.toLinearMap.comp g = gK.comp v.toLinearMap) :
    Function.Surjective gK := by
  intro z
  obtain ⟨y, hy⟩ := hg (w.symm z)
  refine ⟨v y, ?_⟩
  have hy' : w (g y) = gK (v y) := by
    simpa using congrArg (fun φ : M →ₗ[R] K'' ↦ φ y) hvw
  calc
    gK (v y) = w (g y) := by simpa using hy'.symm
    _ = z := by simpa [hy]

private theorem exact_of_commSq
    {f : M' →ₗ[R] M} {g : M →ₗ[R] M''}
    {fK : K' →ₗ[R] K} {gK : K →ₗ[R] K''}
    (hexact : Function.Exact f g)
    (u : M' ≃ₗ[R] K') (v : M ≃ₗ[R] K) (w : M'' ≃ₗ[R] K'')
    (huv : v.toLinearMap.comp f = fK.comp u.toLinearMap)
    (hvw : w.toLinearMap.comp g = gK.comp v.toLinearMap) :
    Function.Exact fK gK := by
  exact Function.Exact.of_ladder_linearEquiv_of_exact huv.symm hvw.symm hexact

variable [Module.Finite R M'] [Module.Projective R M']
variable [Module.Finite R M] [Module.Projective R M]
variable [Module.Finite R M''] [Module.Projective R M'']
variable [Module.Finite R K'] [Module.Projective R K']
variable [Module.Finite R K] [Module.Projective R K]
variable [Module.Finite R K''] [Module.Projective R K'']

/-- Bridge/view: an isomorphism of presented short exact sequences of finite projective
`R`-modules intertwines the determinant-line comparison maps from Lemma `15.119.2`. The target-row
injectivity, surjectivity, and exactness hypotheses are derived internally by transport along the
given linear equivalences, and the underlying owner-level comparison is still the short-complex
determinant isomorphism `determinantTensorIso`. -/
theorem determinantTensorIsoOfShortExact_naturality
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hf : Function.Injective f)
    (hg : Function.Surjective g) (hexact : Function.Exact f g)
    (fK : K' →ₗ[R] K) (gK : K →ₗ[R] K'') (u : M' ≃ₗ[R] K') (v : M ≃ₗ[R] K)
    (w : M'' ≃ₗ[R] K'')
    (huv : v.toLinearMap.comp f = fK.comp u.toLinearMap)
    (hvw : w.toLinearMap.comp g = gK.comp v.toLinearMap) :
    let hfK : Function.Injective fK := injective_of_commSq hf u v huv
    let hgK : Function.Surjective gK := surjective_of_commSq hg v w hvw
    let hexactK : Function.Exact fK gK := exact_of_commSq hexact u v w huv hvw
    CommSq
      (ModuleCat.ofHom <| (determinantTensorIsoOfShortExact f g hf hg hexact).toLinearMap)
      (ModuleCat.ofHom <|
        (TensorProduct.congr (determinantLineMap u) (determinantLineMap w)).toLinearMap)
      (ModuleCat.ofHom <| (determinantLineMap v).toLinearMap)
      (ModuleCat.ofHom <| (determinantTensorIsoOfShortExact fK gK hfK hgK hexactK).toLinearMap) :=
  by
  sorry

end Naturality

/-! ### Lemma_15_119_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped TensorProduct
open scoped DeterminantLine

universe u v

variable {R : Type u} [CommRing R]

/-
Domain-style sampling for determinant-line comparison maps in a submodule tower:
- primary domain: determinant lines of finite projective modules and the canonical comparison maps
  attached to short exact sequences;
- sampled owner declarations:
  * `CategoryTheory.ShortComplex.ShortExact.determinantTensorIso`,
  * `determinantTensorIsoOfShortExact_naturality`,
  * `determinantTensorIsoOfShortExact`,
  * `Submodule.quotientQuotientEquivQuotient`;
- best owner abstraction:
  `core/canonical`: `determinantTensorIsoOfShortExact_naturality` is the chapter-level owner for
    commutative squares of determinant comparison maps attached to isomorphic presented short exact
    rows;
  `source-facing`: the main theorem should specialize that owner square to a tower `K ≤ L ≤ M`
    and the quotients `L / K`, `M / L`, `M / K`;
  `bridge/view`: the quotient row `L / K → M / K → M / L` is expressed through the canonical
    submodule `L.map K.mkQ ⊆ M / K` and the standard quotient identifications.
- primitive data: the submodules `K ≤ L ≤ M` together with the finite projective hypotheses on
  `K`, `L / K`, and `M / L`;
- derived API: finiteness/projectivity of `L`, `M`, and `M / K`, and the resulting determinant
  comparison square.
-/

section SubmoduleTower

variable {M : Type v} [AddCommGroup M] [Module R M]

private theorem projective_of_submodule_quotient (N : Submodule R M)
    [Module.Projective R N] [Module.Projective R (M ⧸ N)] :
    Module.Projective R M := by
  let s : (M ⧸ N) →ₗ[R] M :=
    Classical.choose
      (Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective)
  have hs : N.mkQ.comp s = LinearMap.id :=
    Classical.choose_spec
      (Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective)
  obtain ⟨e, -, -⟩ :=
    ((Function.Exact.split_tfae (LinearMap.exact_subtype_mkQ N) Subtype.val_injective
      N.mkQ_surjective).out 0 2 rfl rfl).mp ⟨s, hs⟩
  exact Module.Projective.of_equiv e.symm

private theorem exact_inclusion_mkQ (K L : Submodule R M) (hKL : K ≤ L) :
    Function.Exact (Submodule.inclusion hKL) (K.submoduleOf L).mkQ := by
  have hExact : Function.Exact (K.submoduleOf L).subtype (K.submoduleOf L).mkQ :=
    LinearMap.exact_subtype_mkQ (K.submoduleOf L)
  simpa [Submodule.inclusion] using
    (Function.Surjective.comp_exact_iff_exact
      (Submodule.submoduleOfEquivOfLe hKL).symm.surjective).2 hExact

namespace SubmoduleTower

private theorem finite_submoduleOf (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Finite R ↥K] :
    Module.Finite R (K.submoduleOf L) :=
  Module.Finite.equiv (Submodule.submoduleOfEquivOfLe hKL).symm

private theorem projective_submoduleOf (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Projective R ↥K] :
    Module.Projective R (K.submoduleOf L) :=
  Module.Projective.of_equiv (Submodule.submoduleOfEquivOfLe hKL).symm

private theorem finite_L (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Finite R ↥K] [Module.Finite R (L ⧸ K.submoduleOf L)] :
    Module.Finite R ↥L := by
  letI := finite_submoduleOf K L hKL
  exact Module.Finite.of_submodule_quotient (K.submoduleOf L)

private theorem projective_L (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Projective R ↥K] [Module.Projective R (L ⧸ K.submoduleOf L)] :
    Module.Projective R ↥L := by
  letI := projective_submoduleOf K L hKL
  exact projective_of_submodule_quotient (K.submoduleOf L)

private theorem finite_M (L : Submodule R M)
    [Module.Finite R ↥L] [Module.Finite R (M ⧸ L)] :
    Module.Finite R M := by
  exact Module.Finite.of_submodule_quotient L

private theorem projective_M (L : Submodule R M)
    [Module.Projective R ↥L] [Module.Projective R (M ⧸ L)] :
    Module.Projective R M := by
  exact projective_of_submodule_quotient L

-- Bridge/view: the quotient of `L` by the induced submodule from `K` is canonically equivalent
-- to the image of `L` in `M ⧸ K`.
private noncomputable def quotientSubmoduleOfEquivImage (K L : Submodule R M) :
    (L ⧸ K.submoduleOf L) ≃ₗ[R] L.map K.mkQ :=
  let f : L →ₗ[R] M ⧸ K := K.mkQ.comp L.subtype
  let hk : f.ker = K.submoduleOf L := by
    ext x
    simp [f, Submodule.submoduleOf]
  let hr : f.range = L.map K.mkQ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  (Submodule.quotEquivOfEq _ _ hk.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr))

private theorem projective_quotientSubmodule (K L : Submodule R M)
    [Module.Projective R (L ⧸ K.submoduleOf L)] :
    Module.Projective R (L.map K.mkQ) :=
  Module.Projective.of_equiv (quotientSubmoduleOfEquivImage K L)

private theorem finite_quotientSubmodule (K L : Submodule R M)
    [Module.Finite R (L ⧸ K.submoduleOf L)] :
    Module.Finite R ↥(L.map K.mkQ) :=
  Module.Finite.equiv (quotientSubmoduleOfEquivImage K L)

private theorem projective_quotientQuotient (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Projective R (M ⧸ L)] :
    Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ) :=
  Module.Projective.of_equiv (Submodule.quotientQuotientEquivQuotient K L hKL).symm

private theorem finite_quotientQuotient (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Finite R (M ⧸ L)] :
    Module.Finite R ((M ⧸ K) ⧸ L.map K.mkQ) :=
  Module.Finite.equiv (Submodule.quotientQuotientEquivQuotient K L hKL).symm

private theorem finite_quotientKM (K : Submodule R M)
    [Module.Finite R M] :
    Module.Finite R (M ⧸ K) := by
  exact Module.Finite.quotient R K

private theorem projective_quotientKM (K L : Submodule R M)
    [Module.Projective R ↥(L.map K.mkQ)]
    [Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ)] :
    Module.Projective R (M ⧸ K) := by
  exact projective_of_submodule_quotient (L.map K.mkQ)

end SubmoduleTower

variable (K L : Submodule R M) (hKL : K ≤ L)
variable [Module.Finite R K] [Module.Projective R K]
variable [Module.Finite R (L ⧸ K.submoduleOf L)] [Module.Projective R (L ⧸ K.submoduleOf L)]
variable [Module.Finite R (M ⧸ L)] [Module.Projective R (M ⧸ L)]

local notation3:max "det(" M ")" => Module.det R M

open SubmoduleTower

namespace SubmoduleTower

/-- The determinant comparison map for
`0 → K → L → L / K → 0`. -/
noncomputable def submoduleDeterminantIso :
    (det(↥K) ⊗[R] det(L ⧸ K.submoduleOf L)) ≃ₗ[R] det(↥L) :=
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Projective R ↥L := projective_L K L hKL
  determinantTensorIsoOfShortExact
    (Submodule.inclusion hKL)
    (K.submoduleOf L).mkQ
    (Submodule.inclusion_injective hKL)
    (K.submoduleOf L).mkQ_surjective
    (exact_inclusion_mkQ K L hKL)

/-- The determinant comparison map for
`0 → L → M → M / L → 0`. -/
noncomputable def ambientDeterminantIso :
    (det(↥L) ⊗[R] det(M ⧸ L)) ≃ₗ[R] det(M) :=
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Projective R ↥L := projective_L K L hKL
  let _ : Module.Finite R M := finite_M L
  let _ : Module.Projective R M := projective_M L
  determinantTensorIsoOfShortExact
    L.subtype
    L.mkQ
    Subtype.val_injective
    L.mkQ_surjective
    (LinearMap.exact_subtype_mkQ L)

/-- The determinant comparison map for
`0 → K → M → M / K → 0`. -/
noncomputable def totalDeterminantIso :
    (det(↥K) ⊗[R] det(M ⧸ K)) ≃ₗ[R] det(M) :=
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Projective R ↥L := projective_L K L hKL
  let _ : Module.Finite R M := finite_M L
  let _ : Module.Projective R M := projective_M L
  let _ : Module.Finite R (M ⧸ K) := finite_quotientKM K
  let _ : Module.Finite R ↥(L.map K.mkQ) := finite_quotientSubmodule K L
  let _ : Module.Projective R ↥(L.map K.mkQ) := projective_quotientSubmodule K L
  let _ : Module.Finite R ((M ⧸ K) ⧸ L.map K.mkQ) := finite_quotientQuotient K L hKL
  let _ : Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ) := projective_quotientQuotient K L hKL
  let _ : Module.Projective R (M ⧸ K) := projective_quotientKM K L
  determinantTensorIsoOfShortExact
    K.subtype
    K.mkQ
    Subtype.val_injective
    K.mkQ_surjective
    (LinearMap.exact_subtype_mkQ K)

/-- Bridge/view: the determinant comparison map for
`0 → L / K → M / K → M / L → 0`, obtained from the canonical exact row
`0 → L.map K.mkQ → M / K → (M / K) / L.map K.mkQ → 0`
through the standard quotient identifications. -/
noncomputable def quotientDeterminantIso :
    (det(L ⧸ K.submoduleOf L) ⊗[R] det(M ⧸ L)) ≃ₗ[R] det(M ⧸ K) :=
  let _ : Module.Finite R ↥L := finite_L K L hKL
  let _ : Module.Finite R M := finite_M L
  let _ : Module.Finite R (M ⧸ K) := finite_quotientKM K
  let _ : Module.Finite R ↥(L.map K.mkQ) := finite_quotientSubmodule K L
  let _ : Module.Projective R ↥(L.map K.mkQ) := projective_quotientSubmodule K L
  let _ : Module.Finite R ((M ⧸ K) ⧸ L.map K.mkQ) := finite_quotientQuotient K L hKL
  let _ : Module.Projective R ((M ⧸ K) ⧸ L.map K.mkQ) := projective_quotientQuotient K L hKL
  let _ : Module.Projective R (M ⧸ K) := projective_quotientKM K L
  (TensorProduct.congr
      (determinantLineMap (quotientSubmoduleOfEquivImage K L))
      (determinantLineMap (Submodule.quotientQuotientEquivQuotient K L hKL).symm)).trans
    (determinantTensorIsoOfShortExact
      (L.map K.mkQ).subtype
      (L.map K.mkQ).mkQ
      Subtype.val_injective
      (L.map K.mkQ).mkQ_surjective
      (LinearMap.exact_subtype_mkQ (L.map K.mkQ)))

-- Proof sketch: derive the finite projective structures on `L`, `M`, and `M / K` from the three
-- source-facing hypotheses using split exactness for the quotient rows. Then compare the two ways
-- of passing from `det K ⊗ det(L / K) ⊗ det(M / L)` to `det M` by rewriting the left quotient row
-- through the canonical identifications `L / K ≃ L.map K.mkQ` and
-- `(M / K) / (L / K) ≃ M / L`, and finally applying the determinant-map naturality of
-- Lemma `15.119.3`.
/-- Lemma 15.119.4: for submodules `K ≤ L` of an `R`-module `M`, if `K`, `L / K`, and `M / L` are
finite projective, then the determinant comparison maps from Lemma `15.119.2` for the short exact
sequences
`0 → K → L → L / K → 0`, `0 → L → M → M / L → 0`, `0 → K → M → M / K → 0`, and
`0 → L / K → M / K → M / L → 0`
form a commutative square. The left vertical map is the source-facing quotient-row bridge
`quotientDeterminantIso K L hKL`, built from the canonical identifications
`L / K ≃ L.map K.mkQ` and `(M / K) / (L / K) ≃ M / L`. -/
theorem determinant_tensor_iso_tower_commutes :
    CommSq
      (ModuleCat.ofHom <|
        (TensorProduct.congr
          (submoduleDeterminantIso K L hKL)
          (LinearEquiv.refl R (det(M ⧸ L)))).toLinearMap)
      (ModuleCat.ofHom <|
        ((TensorProduct.assoc R
            (det(↥K))
            (det(L ⧸ K.submoduleOf L))
            (det(M ⧸ L))).trans
          (TensorProduct.congr
            (LinearEquiv.refl R (det(↥K)))
            (quotientDeterminantIso K L hKL))).toLinearMap)
      (ModuleCat.ofHom <|
        (ambientDeterminantIso K L hKL).toLinearMap)
      (ModuleCat.ofHom <| (totalDeterminantIso K L hKL).toLinearMap) := by
  sorry

/-- The determinant square from `determinant_tensor_iso_tower_commutes`, evaluated on a pure
tensor. -/
theorem determinant_tensor_iso_tower_commutes_apply
    (xK : det(↥K)) (xQ : det(L ⧸ K.submoduleOf L)) (xC : det(M ⧸ L)) :
    ambientDeterminantIso K L hKL
      ((TensorProduct.congr
          (submoduleDeterminantIso K L hKL)
          (LinearEquiv.refl R (det(M ⧸ L)))).toLinearMap
        (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) =
      totalDeterminantIso K L hKL
        (((TensorProduct.assoc R
            (det(↥K))
            (det(L ⧸ K.submoduleOf L))
            (det(M ⧸ L))).trans
          (TensorProduct.congr
            (LinearEquiv.refl R (det(↥K)))
            (quotientDeterminantIso K L hKL))).toLinearMap
          (xK ⊗ₜ[R] xQ ⊗ₜ[R] xC)) := by
  sorry

end SubmoduleTower
end SubmoduleTower

/-! ### Lemma_15_119_5 (from Chap15) -/
noncomputable section
open CategoryTheory
open LinearEquiv
open LinearMap
open scoped TensorProduct
open scoped DeterminantLine

universe u v w

variable {R : Type u} [CommRing R]
variable {M' : Type v} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
  [Module.Projective R M']
variable {M'' : Type w} [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
  [Module.Projective R M'']

/-
Domain-style sampling for Lemma 15.119.5:
- primary domain: determinant lines of finite projective modules and the canonical comparison maps
  attached to short exact sequences, specialized to the split rows for a direct sum;
- sampled owner declarations:
  * `CategoryTheory.ShortComplex.ShortExact.determinantTensorIso`,
  * `determinantTensorIsoOfShortExact`,
  * `determinantTensorIsoOfShortExact_naturality`,
  * `determinantLineMap`,
  * `LinearMap.projectiveDet`;
- best owner abstraction:
  `core/canonical`: `CategoryTheory.ShortComplex.ShortExact.determinantTensorIso`, with the
    presented-row bridge `determinantTensorIsoOfShortExact`;
  `bridge/view`: the symmetry square for the split exact rows
    `0 → M' → M' × M'' → M'' → 0` and `0 → M'' → M'' × M' → M' → 0`;
- primitive data: the finite projective modules `M'` and `M''`;
- derived API: the determinant comparison maps for the two split rows, the determinant-line map of
  `LinearEquiv.prodComm`, the canonical determinant scalar
  `tensorSwitchSign R M' M'' = det(-id_{M' ⊗[R] M''})`, and the tensor symmetry twisted by that
  scalar action.

This file therefore stays at the bridge layer and reuses the determinant-line owners already
introduced in `15.119.2` and `15.119.3`, rather than introducing any parallel split-row wrapper.
-/

section TensorSwitchSign

variable (R) (M') (M'')

private theorem determinantMap_eq_determinantLineMap_toLinearMap
    (e : (M' ⊗[R] M'') ≃ₗ[R] M' ⊗[R] M'') :
    LinearMap.determinantMap (fun _ ↦ rfl) e.toLinearMap =
      (determinantLineMap e).toLinearMap := by
  ext x
  rfl

/-- The canonical sign scalar `ε = det(-id_{M' ⊗[R] M''}) ∈ R` from the determinant owner
`LinearMap.projectiveDet`. -/
noncomputable def tensorSwitchSign : R :=
  LinearMap.projectiveDet
    (-LinearMap.id : (M' ⊗[R] M'') →ₗ[R] M' ⊗[R] M'')

/-- The canonical sign scalar acts on `det(M' ⊗[R] M'')` by the determinant-line map induced by
`-id_{M' ⊗[R] M''}`. -/
theorem tensorSwitchSign_spec :
    Module.toModuleEnd R (det(M' ⊗[R] M'')) (tensorSwitchSign R M' M'') =
      (determinantLineMap (neg R : (M' ⊗[R] M'') ≃ₗ[R] M' ⊗[R] M'')).toLinearMap := by
  simpa [tensorSwitchSign, determinantMap_eq_determinantLineMap_toLinearMap] using
    LinearMap.projectiveDet_spec
      (-LinearMap.id : (M' ⊗[R] M'') →ₗ[R] M' ⊗[R] M'')

/-- On the determinant line of `M' ⊗[R] M''`, the map induced by `-id` is scalar multiplication
by the canonical sign scalar `tensorSwitchSign R M' M''`. -/
theorem determinantLineMap_neg_toLinearMap_eq_tensorSwitchSign :
    (determinantLineMap (neg R : (M' ⊗[R] M'') ≃ₗ[R] M' ⊗[R] M'')).toLinearMap =
      Module.toModuleEnd R (det(M' ⊗[R] M'')) (tensorSwitchSign R M' M'') := by
  simpa using (tensorSwitchSign_spec R M' M'').symm

end TensorSwitchSign

/-- Lemma 15.119.5: for the split short exact sequences
`0 → M' → M' × M'' → M'' → 0` and `0 → M'' → M'' × M' → M' → 0`, the determinant-line
comparison maps from Lemma `15.119.2` are intertwined by switching the summands, up to the sign
scalar `tensorSwitchSign R M' M'' = det(-id_{M' ⊗[R] M''})` by which `-1` acts on the determinant
line of `M' ⊗[R] M''`. -/
theorem determinant_tensor_iso_switch_summands_commutes
    : CommSq
        (ModuleCat.ofHom <|
          (determinantTensorIsoOfShortExact
            (inl R M' M'')
            (snd R M' M'')
            inl_injective
            snd_surjective
            Function.Exact.inl_snd).toLinearMap)
        (ModuleCat.ofHom <|
          (TensorProduct.comm R (det(M')) (det(M''))).toLinearMap.comp
            (Module.toModuleEnd R (det(M') ⊗[R] det(M'')) (tensorSwitchSign R M' M'')))
        (ModuleCat.ofHom <| (determinantLineMap (prodComm R M' M'')).toLinearMap)
        (ModuleCat.ofHom <|
          (determinantTensorIsoOfShortExact
            (inl R M'' M')
            (snd R M'' M')
            inl_injective
            snd_surjective
            Function.Exact.inl_snd).toLinearMap) := by
  refine CommSq.mk ?_
  sorry

/-! ### Lemma_15_119_6 (from Chap15) -/
noncomputable section

open ExteriorAlgebra
open scoped DeterminantLine

universe u v w

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling for Lemma 15.119.6:
- primary domain: determinant maps on determinant lines of finite projective modules of equal
  local rank, together with the scalar-valued endomorphism specialization;
- sampled owner declarations:
  * `Module.det`,
  * `Module.rankAtStalk`,
  * `Module.Invertible.toModuleEnd_bijective`,
  * `determinantLineMap`,
  * `LinearMap.det`;
- best owner abstraction:
  `source-facing`: the determinant-line map attached to a linear map `f : M →ₗ[R] N` when `M`
    and `N` have the same local rank;
  `core/canonical`: the determinant line `Module.det R M`, together with the canonical
    identification of endomorphisms of an invertible module with scalars via
    `Module.Invertible.toModuleEnd_bijective`;
  `bridge/view`: the endomorphism scalar determinant and the finite free specialization
    `LinearMap.det`.
- primitive vs. derived:
  primitive data are finite projective modules `M`, `N`, a linear map `f : M →ₗ[R] N`, and the
  equality of the local rank functions `Module.rankAtStalk M = Module.rankAtStalk N`;
  the determinant scalar of an endomorphism and its finite free identification with
  `LinearMap.det` are derived from that owner.

The source theorem therefore keeps the determinant-line map as the owner and treats the
scalar-valued endomorphism determinant only as the bridge/view needed for Lemma `15.119.6`.
-/

section DeterminantMap

variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]

namespace Module

/-- If finite projective modules `M` and `N` have the same local rank, then the exterior-algebra
map induced by `f : M →ₗ[R] N` carries `det(M)` into `det(N)`. -/
theorem det_map_mem_of_rankAtStalk_eq
    (hMN : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = Module.rankAtStalk N p)
    (f : M →ₗ[R] N) (x : Module.det R M) :
    ExteriorAlgebra.map f (x : ExteriorAlgebra R M) ∈ Module.det R N := sorry

end Module

namespace LinearMap

/-- The canonical determinant-line map `det(M) → det(N)` induced by a linear map
`f : M →ₗ[R] N` between finite projective modules of the same local rank. -/
def determinantMap
    (hMN : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = Module.rankAtStalk N p)
    (f : M →ₗ[R] N) : Module.det R M →ₗ[R] Module.det R N :=
  LinearMap.codRestrict
    (Module.det R N)
    ((ExteriorAlgebra.map f).toLinearMap.comp (Module.det R M).subtype)
    (Module.det_map_mem_of_rankAtStalk_eq hMN f)

/-- The determinant-line map acts by the exterior-algebra map induced by the underlying linear
map. -/
theorem determinantMap_apply
    (hMN : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = Module.rankAtStalk N p)
    (f : M →ₗ[R] N) (x : Module.det R M) :
    (determinantMap hMN f x : ExteriorAlgebra R N) =
      ExteriorAlgebra.map f (x : ExteriorAlgebra R M) := rfl

section Endomorphisms

/-- The projective determinant of an endomorphism `f : M →ₗ[R] M`, defined as the unique scalar
whose action on `det(M)` agrees with the determinant-line map `det(f) : det(M) → det(M)`. -/
noncomputable def projectiveDet (f : M →ₗ[R] M) : R :=
  Function.surjInv
    (Module.Invertible.toModuleEnd_bijective R (Module.det R M)).surjective
    (determinantMap (fun _ ↦ rfl) f)

/-- `projectiveDet f` acts on the determinant line by the determinant map induced by `f`. -/
theorem projectiveDet_spec (f : M →ₗ[R] M) :
    Module.toModuleEnd R (Module.det R M) (projectiveDet f) =
      determinantMap (fun _ ↦ rfl) f :=
  Function.surjInv_eq (Module.Invertible.toModuleEnd_bijective R (Module.det R M)).surjective _

section FreeBridge

variable [Module.Free R M]

/-- On finite free modules, the projective determinant agrees with the usual determinant
`LinearMap.det`. -/
theorem projectiveDet_eq_det (f : M →ₗ[R] M) :
    projectiveDet f = LinearMap.det f := sorry

end FreeBridge
end Endomorphisms

end LinearMap

end DeterminantMap

section WeinsteinAronszajn

variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]

open LinearMap

-- Proof sketch: let `1 + a ∘ b` and `1 + b ∘ a` act on the determinant lines of `N` and `M`.
-- After stabilizing `M` and `N` by finite free summands, these endomorphisms become conjugate to
-- the block maps `1 + AB` and `1 + BA` on free modules, where the usual Weinstein-Aronszajn
-- identity applies. The defining uniqueness of `projectiveDet` then descends the equality back to
-- the scalar bridge extracted from the determinant-line owner.
/-- Lemma 15.119.6: for finite projective `R`-modules `M` and `N`, the determinants of
`id_N + a ∘ b` and `id_M + b ∘ a` agree, where determinant means the scalar bridge/view
`LinearMap.projectiveDet` obtained by identifying `End_R(det(M))` with `R` after passing through
the determinant-line map owner `LinearMap.determinantMap`. This is the Weinstein-Aronszajn
identity in the finite-projective setting of the source. -/
theorem det_id_add_a_comp_b_eq_det_id_add_b_comp_a (a : M →ₗ[R] N) (b : N →ₗ[R] M) :
    projectiveDet (1 + a ∘ₗ b) = projectiveDet (1 + b ∘ₗ a) := by
  sorry

section FreeBridge

variable [Module.Free R M] [Module.Free R N]

/-- Bridge/view: in the finite free case, Lemma `15.119.6` recovers the usual equality of
`LinearMap.det`. -/
theorem linearMap_det_id_add_a_comp_b_eq_det_id_add_b_comp_a
    (a : M →ₗ[R] N) (b : N →ₗ[R] M) :
    LinearMap.det (1 + a ∘ₗ b) = LinearMap.det (1 + b ∘ₗ a) := by
  rw [← projectiveDet_eq_det (1 + a ∘ₗ b), det_id_add_a_comp_b_eq_det_id_add_b_comp_a,
    projectiveDet_eq_det (1 + b ∘ₗ a)]

end FreeBridge

end WeinsteinAronszajn

end

/-! ### Lemma_15_119_7 (from Chap15) -/
noncomputable section

open scoped DeterminantLine

universe u

section

variable (R : Type u) [CommRing R]

local notation "K₀" => projectiveGrothendieckGroup R

/- Domain-style sampling for Lemma 15.119.7:
- primary domain: additive invariants of `K₀(R)` for finite projective `R`-modules, with values in
  the Picard group via the determinant line;
- sampled owner declarations:
  `ModulePropertyK0.lift`,
  `ModulePropertyK0.lift_of`,
  `projectiveGrothendieckGroup`,
  `CommRing.Pic.mk`,
  `Module.det`;
- best owner abstraction:
  the source-facing declaration is the determinant homomorphism
  `projectiveGrothendieckGroup R →+ Additive (CommRing.Pic R)`, while the canonical owner for its
  construction is the Chapter 10 quotient-descending API `ModulePropertyK0.lift`;
- primitive vs. derived:
  primitive data here is only the value of the invariant on a finite projective module,
  `M ↦ Additive.ofMul (CommRing.Pic.mk R det(M.obj))`;
  the descended `K₀` map and its evaluation formula are derived from that owner abstraction;
- source/core/bridge triage:
  `source-facing`: `projectiveGrothendieckGroup_det`;
  `core/canonical`: `ModulePropertyK0.lift`;
  `bridge/view`: the determinant-line owner `Module.det`, used through the textbook notation
  `det(M)` from Remark `15.119.1`.

This file should therefore expose the determinant map on `K₀(R)` as the main public API and build
it directly from the canonical `ModulePropertyK0.lift` owner abstraction, keeping the primitive
module-level determinant class only as the function fed to that owner.
-/

/-- The determinant Picard class attached to a finite projective `R`-module. This is the
primitive generator-level datum fed into the canonical `K₀` quotient lift. -/
private abbrev detClass (M : FiniteProjectiveModuleCat R) :
    Additive (CommRing.Pic R) :=
  Additive.ofMul (CommRing.Pic.mk R
    ((det((M.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R M.obj))))

/-- The determinant invariant on finite projective modules kills the short-exact-sequence
relations defining `K₀(R)`. -/
private theorem detClass_relations_le_ker :
    modulePropertyK0Relations R (finiteProjectiveModuleProperty R) ≤
      (FreeAbelianGroup.lift (detClass R)).ker := sorry

/-- Lemma 15.119.7: the determinant construction induces a map from `K₀(R)` to the Picard group of
`R`, sending the class of a finite locally free module to the Picard class of its determinant line
`det(M)`, realized here by the exterior-algebra annihilator model from Remark
`15.119.1`. In Lean, the Picard group is viewed
additively so that this becomes a homomorphism out of the additive Grothendieck group. -/
def projectiveGrothendieckGroup_det :
    K₀ →+ Additive (CommRing.Pic R) :=
  ModulePropertyK0.lift R (detClass R) (detClass_relations_le_ker R)

/-- On the class of a finite projective module, the determinant map returns the Picard class of
its determinant line `det((M.obj : ModuleCat R))`. -/
@[simp]
theorem projectiveGrothendieckGroup_det_apply_of
    (M : FiniteProjectiveModuleCat R) :
    projectiveGrothendieckGroup_det R
        (projectiveGrothendieckGroupOf R M) =
      Additive.ofMul (CommRing.Pic.mk R
        ((det((M.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R M.obj)))) := by
  simpa [detClass] using ModulePropertyK0.lift_of R
    (detClass R)
    (detClass_relations_le_ker R) M

end
