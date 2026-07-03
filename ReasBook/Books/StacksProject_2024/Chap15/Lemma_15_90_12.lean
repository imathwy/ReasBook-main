import Mathlib
import StacksProject_2024.Chap15.«15_90_8_1»
import StacksProject_2024.Chap15.Lemma_15_90_9
import StacksProject_2024.Chap15.Lemma_15_90_13

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)

/-
Domain-style sampling:
- primary domain: formal glueing for module categories, with the degree-zero module recovered from
  the canonical formal glueing short complex;
- sampled owner declarations:
  `formalGlueingCan`,
  `formalGlueingH0`,
  `formalGlueingModuleComplex`,
  `ShortComplex.Exact.moduleCat_range_eq_ker`;
- best owner abstraction:
  the source-facing functors `formalGlueingCan` and `formalGlueingH0`, bridged through the owner
  kernel object `LinearMap.ker (formalGlueingModuleComplexBeta S f M)` attached to the formal
  glueing complex;
- primitive data:
  the module `M`, the canonical map `formalGlueingModuleComplexAlpha S f M`, and the kernel-level
  comparison between `H⁰(Can(M))` and `ker β`;
- derived API:
  the componentwise linear equivalence and the resulting natural isomorphism
  `formalGlueingCan S f ⋙ formalGlueingH0 S f ≅ 𝟭`.

Source/core/bridge triage:
- `source-facing`: the natural isomorphism below;
- `core/canonical`: `formalGlueingCan`, `formalGlueingH0`, and
  `ShortComplex.Exact.moduleCat_range_eq_ker`;
- `bridge/view`: the kernel-level comparison between `H⁰(Can(M))` and
  `LinearMap.ker (formalGlueingModuleComplexBeta S f M)`.
-/

private noncomputable def formalGlueingAlphaToKerBeta
    (M : ModuleCat R) :
    M →ₗ[R] LinearMap.ker (formalGlueingModuleComplexBeta S f M) :=
  (formalGlueingModuleComplexAlpha S f M).codRestrict _ fun x ↦ by
    change formalGlueingModuleComplexBeta S f M (formalGlueingModuleComplexAlpha S f M x) = 0
    simpa using LinearMap.congr_fun (formalGlueingModuleComplex_comp_eq_zero S f M) x

private noncomputable def formalGlueingH0ToKerBeta
    (M : ModuleCat R) :
    ((formalGlueingH0 S f).obj ((formalGlueingCan S f).obj M)) →ₗ[R]
      LinearMap.ker (formalGlueingModuleComplexBeta S f M) := by
  refine
    { toFun := fun x ↦ ⟨((formalGlueingCanBaseIso M).hom.hom x.1.1, x.1.2.1), by sorry⟩
      map_add' := by sorry
      map_smul' := by sorry }

private noncomputable def formalGlueingKerBetaToH0
    (M : ModuleCat R) :
    LinearMap.ker (formalGlueingModuleComplexBeta S f M) →ₗ[R]
      ((formalGlueingH0 S f).obj ((formalGlueingCan S f).obj M)) := by
  refine
    { toFun := fun x ↦
        ⟨((formalGlueingCanBaseIso M).inv.hom x.1.1, ⟨x.1.2, by sorry⟩), by sorry⟩
      map_add' := by sorry
      map_smul' := by sorry }

private noncomputable def formalGlueingH0KerBetaLinearEquiv
    (M : ModuleCat R) :
    ((formalGlueingH0 S f).obj ((formalGlueingCan S f).obj M)) ≃ₗ[R]
      LinearMap.ker (formalGlueingModuleComplexBeta S f M) :=
  LinearEquiv.ofLinear
    (formalGlueingH0ToKerBeta f M)
    (formalGlueingKerBetaToH0 f M)
    (by sorry)
    (by sorry)

private noncomputable def formalGlueingCanH0LinearEquiv_of_flat_of_quotientMap_bijective
    (hflat : (algebraMap R S).Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map))
    (M : ModuleCat R) :
    M ≃ₗ[R] ((formalGlueingH0 S f).obj ((formalGlueingCan S f).obj M)) := by
  let α := formalGlueingModuleComplexAlpha S f M
  let β := formalGlueingModuleComplexBeta S f M
  let α' : M →ₗ[R] LinearMap.ker (formalGlueingModuleComplexBeta S f M) :=
    formalGlueingAlphaToKerBeta f M
  have hExact : (formalGlueingModuleComplex S f M).Exact :=
    (formalGlueingModuleComplex_exact_of_flat_of_quotientMap_bijective M f hflat hquot).1
  have hMono : Mono (formalGlueingModuleComplex S f M).f :=
    (formalGlueingModuleComplex_exact_of_flat_of_quotientMap_bijective M f hflat hquot).2
  have hRangeKer : LinearMap.range α = LinearMap.ker β := by
    simpa [formalGlueingModuleComplex, α, β] using
      ShortComplex.Exact.moduleCat_range_eq_ker hExact
  have hInjective : Function.Injective α' := by
    intro x y hxy
    have hα : α x = α y := by
      exact congrArg Subtype.val hxy
    have hαInjective : Function.Injective α := by
      simpa [formalGlueingModuleComplex, α] using
        (ModuleCat.mono_iff_injective (formalGlueingModuleComplex S f M).f).1 hMono
    exact hαInjective hα
  have hSurjective : Function.Surjective α' := by
    intro y
    have hy : y.1 ∈ LinearMap.range α := by
      simpa [hRangeKer] using y.2
    rcases hy with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  exact
    (LinearEquiv.ofBijective α' ⟨hInjective, hSurjective⟩).trans
      (formalGlueingH0KerBetaLinearEquiv f M).symm

-- Proof sketch: identify `H⁰(Can(M))` with the kernel of the second map `β` in the formal
-- glueing module complex. Lemma `15.90.9` gives `range(α) = ker(β)` and injectivity of `α`, so
-- the canonical map `M → ker(β)` is a linear equivalence. Transport this through the kernel-level
-- bridge to obtain the desired componentwise isomorphism.
-- Lemma `15.90.9` identifies the unit map `M ⟶ H^0(Can(M))` with the first map in the formal
-- glueing complex and proves that it is an isomorphism under the flatness and quotient
-- hypotheses, yielding a natural isomorphism `Can ⋙ H^0 ≅ 𝟭`.
/-- Lemma 15.90.12: assume `φ : R → S` is a flat ring map and `I = (f₁, \ldots, fₜ) ⊂ R` is an
ideal such that `R/I → S/IS` is an isomorphism. Then the degree-zero functor `H^0` of Remark
15.90.10 is a left quasi-inverse to the canonical functor `Can`. In the formalization, the
right-adjoint owner is already the canonical functor `formalGlueingH0 R S f` from Remark
`15.90.10`, so the content here is the natural isomorphism
`formalGlueingCan S f ⋙ formalGlueingH0 S f ≅ 𝟭`. -/
noncomputable def formalGlueingH0_leftQuasiInverse_of_flat_of_quotientMap_bijective
    (hflat : (algebraMap R S).Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map)) :
    formalGlueingCan S f ⋙ formalGlueingH0 S f ≅ 𝟭 (ModuleCat R) :=
  NatIso.ofComponents
    (fun M ↦
      (formalGlueingCanH0LinearEquiv_of_flat_of_quotientMap_bijective
        f hflat hquot M).symm.toModuleIso)
    (by
      intro M N φ
      ext x
      sorry)

end
