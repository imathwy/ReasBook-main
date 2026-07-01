import stacks_project.Chap10.Definition_10_90_1
import stacks_project.Chap10.Lemma_10_5_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open CategoryTheory Module.Finite

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- A coherent module is finitely presented. -/
instance finitePresentation_of_coherent [Module.Coherent R M] :
    Module.FinitePresentation R M := by
  letI : Module.FinitePresentation R (⊤ : Submodule R M) :=
    (inferInstance : Module.Coherent R M).finitePresentation_submodule ⊤ inferInstance
  exact Module.FinitePresentation.of_equiv (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M)

attribute [instance 100] finitePresentation_of_coherent

-- Proof sketch: if `Q ≤ P` is finite, then `Q` is also a finite submodule of `M`, so coherence of
-- `M` makes `Q` finitely presented; together with finiteness of `P`, this shows `P` is coherent.
/-- Lemma 10.90.3: a finite submodule of a coherent `R`-module is coherent. -/
instance coherent_submodule_of_finite {P : Submodule R M}
    [Module.Coherent R M] [Module.Finite R P] :
    Module.Coherent R P where
  toFinite := inferInstance
  finitePresentation_submodule Q hQ := by
    let e : Q ≃ₗ[R] Q.map P.subtype :=
      Q.equivMapOfInjective P.subtype P.subtype_injective
    letI : Module.Finite R (Q.map P.subtype) := Module.Finite.of_fg
      ((iff_fg.mp hQ).map P.subtype)
    letI : Module.FinitePresentation R (Q.map P.subtype) :=
      (inferInstance : Module.Coherent R M).finitePresentation_submodule (Q.map P.subtype)
        inferInstance
    exact Module.FinitePresentation.of_equiv e.symm

attribute [instance 100] coherent_submodule_of_finite

-- Proof sketch: the image is a finite module because it is a quotient of the finite domain. The
-- short exact sequence `0 → ker φ → N → range φ → 0` and the finite presentation of the coherent
-- image then give finite generation of the kernel by Lemma `10.5.3`.
/-- The kernel of a map from a finite module to a coherent module is finite. -/
theorem ker_finite_of_finite_of_coherent (φ : N →ₗ[R] M) [Module.Finite R N]
    [Module.Coherent R M] :
    Module.Finite R (LinearMap.ker φ) := by
  have hExact : Function.Exact (LinearMap.ker φ).subtype φ.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  letI : Module.FinitePresentation R (LinearMap.range φ) := inferInstance
  exact Module.Finite.of_exact_of_finitePresentation (LinearMap.ker φ).subtype φ.rangeRestrict
    (Submodule.injective_subtype _) φ.surjective_rangeRestrict hExact

-- Proof sketch: `range φ` is a finite submodule of the coherent codomain because it is a quotient
-- of the finite domain, so the previous clause applies to this finite submodule.
/-- The image of a map from a finite module to a coherent module is coherent. -/
theorem range_coherent_of_finite_of_coherent (φ : N →ₗ[R] M) [Module.Finite R N]
    [Module.Coherent R M] :
    Module.Coherent R (LinearMap.range φ) := by
  letI : Module.Finite R (LinearMap.range φ) := Module.Finite.of_fg (Submodule.fg_range φ)
  infer_instance

-- Proof sketch: for a finite submodule of the quotient `M ⧸ range φ`, pull it back to a finite
-- submodule of `M`; coherence of `M` and Lemma `10.5.3` on the induced short exact sequence yield
-- finite presentation downstairs.
/-- The cokernel of a map from a finite module to a coherent module is coherent. -/
theorem cokernel_coherent_of_finite_of_coherent (φ : N →ₗ[R] M) [Module.Finite R N]
    [Module.Coherent R M] :
    Module.Coherent R (M ⧸ LinearMap.range φ) := sorry

-- Proof sketch: a coherent source is finite, so the preceding kernel-finiteness statement applies;
-- then the kernel is a finite submodule of the coherent source and hence coherent by the first
-- clause.
/-- The kernel of a morphism of coherent modules is coherent. -/
theorem ker_coherent_of_coherent (φ : N →ₗ[R] M) [Module.Coherent R N] [Module.Coherent R M] :
    Module.Coherent R (LinearMap.ker φ) := by
  letI : Module.Finite R (LinearMap.ker φ) := ker_finite_of_finite_of_coherent φ
  infer_instance

-- Proof sketch: a coherent source is finite, so the previous cokernel statement applies directly
-- to the map `φ`.
/-- The cokernel of a morphism of coherent modules is coherent. -/
theorem cokernel_coherent_of_coherent (φ : N →ₗ[R] M) [Module.Coherent R N]
    [Module.Coherent R M] :
    Module.Coherent R (M ⧸ LinearMap.range φ) :=
  cokernel_coherent_of_finite_of_coherent φ

end

namespace CategoryTheory.ShortComplex

section

variable {R : Type u} [Ring R]
variable {S : ShortComplex (ModuleCat.{v} R)}

-- Proof sketch: for a finite submodule `P ≤ S.X₂`, take its image in `S.X₃` and its inverse image
-- in `S.X₁`; the resulting short exact sequence on submodules has coherent outer terms, so Lemma
-- `10.5.3` promotes finite generation of `P` to finite presentation.
/-- In a short exact sequence of `R`-modules, if the left and right terms are coherent, then the
middle term is coherent. -/
theorem coherent_X2_of_shortExact (hS : S.ShortExact) [Module.Coherent R S.X₁]
    [Module.Coherent R S.X₃] :
    Module.Coherent R S.X₂ := sorry

-- Proof sketch: identify `S.X₁` with the kernel of `S.g`; since `S.X₂` and `S.X₃` are coherent,
-- the kernel of the map `S.g` is coherent by the kernel statement above.
/-- In a short exact sequence of `R`-modules, if the middle and right terms are coherent, then the
left term is coherent. -/
theorem coherent_X1_of_shortExact (hS : S.ShortExact) [Module.Coherent R S.X₂]
    [Module.Coherent R S.X₃] :
    Module.Coherent R S.X₁ := sorry

-- Proof sketch: identify `S.X₃` with the cokernel of `S.f`; since `S.X₁` and `S.X₂` are
-- coherent, the cokernel of `S.f` is coherent by the cokernel statement above.
/-- In a short exact sequence of `R`-modules, if the left and middle terms are coherent, then the
right term is coherent. -/
theorem coherent_X3_of_shortExact (hS : S.ShortExact) [Module.Coherent R S.X₁]
    [Module.Coherent R S.X₂] :
    Module.Coherent R S.X₃ := sorry

end

end CategoryTheory.ShortComplex
