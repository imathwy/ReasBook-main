import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3.GrothendieckBasics

noncomputable section

open Module
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra Representation TensorProduct
open scoped ZeroObject

universe u w

namespace Representation

section ProjectiveGrothendieckGroup

local notation:max "P₀[" A "](" G ")" =>
  finiteProjectiveGroupAlgebraGrothendieckGroup A G

variable {A : Type u} [CommRing A]
variable {G : Type u} [Group G]

open scoped Representation

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Corollary 14-14.4-3: a split exact sequence of modules identifies the middle term
with the product of the two outer terms. -/
noncomputable def linearEquivProdOfRightSplitExact
    {R : Type u} [Ring R]
    {X₁ : Type w} [AddCommGroup X₁] [Module R X₁]
    {X₂ : Type w} [AddCommGroup X₂] [Module R X₂]
    {X₃ : Type w} [AddCommGroup X₃] [Module R X₃]
    (f : X₁ →ₗ[R] X₂) (g : X₂ →ₗ[R] X₃)
    (hf : Function.Injective f) (hexact : Function.Exact f g)
    (s : X₃ →ₗ[R] X₂) (hs : g.comp s = LinearMap.id) :
    (X₁ × X₃) ≃ₗ[R] X₂ := by
  -- Convert the split exact sequence to the canonical biproduct splitting in `ModuleCat`.
  let hexact' : LinearMap.range f = LinearMap.ker g := by
    simpa [LinearMap.exact_iff, eq_comm] using hexact
  exact
    ((ShortComplex.Splitting.ofExactOfSection _
      (ShortComplex.Exact.moduleCat_of_range_eq_ker (ModuleCat.ofHom f)
        (ModuleCat.ofHom g) hexact')
      (ModuleCat.ofHom s) (ModuleCat.hom_ext hs)
      (by simpa only [ModuleCat.mono_iff_injective] using hf)).isoBinaryBiproduct ≪≫
      ModuleCat.biprodIsoProd _ _).symm.toLinearEquiv

omit [IsLocalRing A] [Finite G] in
/-- Helper for Corollary 14-14.4-3: the explicit finite-projective owner on `P.V × Q.V` has class
`[P]ₚ₀ + [Q]ₚ₀`. -/
theorem finiteProjectiveGroupAlgebraGrothendieckClass_prod_eq_add
    (P Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∃ W : FiniteProjectiveGroupAlgebraModule A G,
      Nonempty (W.V ≃ₗ[A[G]] P.V × Q.V) ∧ [W]ₚ₀ = [P]ₚ₀ + [Q]ₚ₀ := by
  let W0 : ModuleCat A[G] := ModuleCat.of A[G] (P.V × Q.V)
  have hfinite : Module.Finite A[G] W0 := by
    change Module.Finite A[G] (P.V × Q.V)
    infer_instance
  let Wfg : FGModuleCat A[G] := ⟨W0, hfinite⟩
  have hproj : Module.Projective A[G] Wfg := by
    change Module.Projective A[G] (P.V × Q.V)
    infer_instance
  let W : FiniteProjectiveGroupAlgebraModule A G := ⟨Wfg, hproj⟩
  let f : P ⟶ W :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inl A[G] P.V Q.V))
  let g : W ⟶ Q :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.snd A[G] P.V Q.V))
  let r : W ⟶ P :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.fst A[G] P.V Q.V))
  let s : Q ⟶ W :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inr A[G] P.V Q.V))
  let T : ShortComplex (FiniteProjectiveGroupAlgebraModule A G) :=
    ShortComplex.mk f g (by
      ext x
      rfl)
  have hsplit : T.Splitting := by
    -- The product projections and inclusions supply the standard splitting.
    refine
      { r := r
        s := s
        f_r := ?_
        s_g := ?_
        id := ?_ }
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change (LinearMap.fst A[G] P.V Q.V) ((LinearMap.inl A[G] P.V Q.V) x) = x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change (LinearMap.snd A[G] P.V Q.V) ((LinearMap.inr A[G] P.V Q.V) x) = x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x, y⟩
      change
        (LinearMap.inl A[G] P.V Q.V ((LinearMap.fst A[G] P.V Q.V) (x, y)) +
            LinearMap.inr A[G] P.V Q.V ((LinearMap.snd A[G] P.V Q.V) (x, y))) =
          (x, y)
      simp
  have hT : T.ShortExact := hsplit.shortExact
  have hclass :=
    finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right
      (A := A) (G := G) T hT
  refine ⟨W, ?_, ?_⟩
  · -- The owner `W` was built on the product module itself.
    exact ⟨by
      change W0 ≃ₗ[A[G]] P.V × Q.V
      exact LinearEquiv.refl A[G] (P.V × Q.V)⟩
  · simpa [T, W, Wfg, W0] using hclass

/-- Helper for Corollary 14-14.4-3: a short exact sequence of finite projective `A[G]`-modules
splits because the right term is projective, so the middle term is linearly equivalent to the
product of the two outer terms. -/
theorem moduleCat_shortExact_middle_nonempty_linearEquiv_prod
    {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat R)) [Module.Projective R S.X₃] (hS : S.ShortExact) :
    Nonempty ((↑S.X₁ × ↑S.X₃) ≃ₗ[R] ↑S.X₂) := by
  have hsurj : Function.Surjective S.g.hom := hS.moduleCat_surjective_g
  have hinj : Function.Injective S.f.hom := hS.moduleCat_injective_f
  have hexact : Function.Exact S.f.hom S.g.hom :=
    (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S := S)).1 hS.exact
  -- Choose a section of `g` and apply the standard split-exact decomposition lemma.
  obtain ⟨s, hs⟩ :=
    Module.projective_lifting_property S.g.hom (LinearMap.id : S.X₃ →ₗ[R] S.X₃) hsurj
  refine ⟨?_⟩
  simpa using linearEquivProdOfRightSplitExact S.f.hom S.g.hom hinj hexact s hs

omit [IsLocalRing A] [Finite G] in
/-- Helper for Corollary 14-14.4-3: forgetting a short complex of finite projective
`A[G]`-modules to `ModuleCat A[G]` preserves the relation `g ∘ f = 0`. -/
theorem finiteProjective_underlying_moduleCat_zero
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule A G)) :
    S.f.hom.hom ≫ S.g.hom.hom = 0 := by
  let F : FiniteProjectiveGroupAlgebraModule A G ⥤ ModuleCat A[G] :=
    (ObjectProperty.ι (fun M : FGModuleCat A[G] ↦ Module.Projective A[G] M)) ⋙
      (ModuleCat.isFG A[G]).ι
  -- The mapped short complex in `ModuleCat A[G]` has the same two structure maps.
  simpa using (S.map F).zero

omit [IsLocalRing A] [Finite G] in
/-- Helper for Corollary 14-14.4-3: the cyclic map generated by `x` in an `A[G]`-module sends
`1` to `x`. -/
theorem regular_module_generated_map_apply_one
    {M : Type w} [AddCommGroup M] [Module A[G] M] (x : M) :
    (((LinearMap.id : A[G] →ₗ[A[G]] A[G]).smulRight x) 1 : M) = x := by
  -- Evaluating the cyclic map generated by `x` at `1` recovers `x`.
  simp

/-- Helper for Corollary 14-14.4-3: if `x` lies in the kernel of `g`, then the cyclic map
`r ↦ r • x` from the regular module also lands in that kernel. -/
theorem regular_module_generated_map_comp_zero
    {M : Type w} [AddCommGroup M] [Module A[G] M]
    {N : Type w} [AddCommGroup N] [Module A[G] N]
    (g : M →ₗ[A[G]] N) (x : M) (hx : g x = 0) :
    g.comp ((LinearMap.id : A[G] →ₗ[A[G]] A[G]).smulRight x) = 0 := by
  -- Extensionality reduces the claim to the hypothesis `g x = 0`.
  ext
  simp [hx]

/-- Helper for Corollary 14-14.4-3: the regular `A[G]`-module viewed in the finite-projective
owner category. -/
abbrev finiteProjective_regular_owner :
    FiniteProjectiveGroupAlgebraModule A G :=
  ⟨FGModuleCat.of A[G] A[G], inferInstance⟩

end ProjectiveGrothendieckGroup

end Representation
