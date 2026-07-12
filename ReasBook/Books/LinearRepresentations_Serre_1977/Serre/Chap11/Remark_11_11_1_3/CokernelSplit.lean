import Mathlib

/-!
Helper for Remark 11-11.1-3: an abstract integral splitting lemma.

A finitely generated abelian group splits along any saturated subgroup: the quotient is
torsion-free, hence free, hence projective, and the resulting section of the quotient map yields
a linear retraction onto the subgroup.  Working over an opaque module type keeps elaboration
cheap; the concrete coherence-target instantiations in `CoherenceDefectSaturation.lean` would
otherwise force the unifier to reconcile competing `Module ℤ` towers on a large product type.
-/

noncomputable section

namespace Representation

/-- A saturated submodule of a finitely generated `ℤ`-module admits a linear retraction. -/
theorem exists_leftInverse_subtype_of_saturated
    {T : Type*} [AddCommGroup T] [Module.Finite ℤ T]
    (N : Submodule ℤ T)
    (hsat : ∀ {t : T} {n : ℤ}, n ≠ 0 → n • t ∈ N → t ∈ N) :
    ∃ r : T →ₗ[ℤ] N, Function.LeftInverse r N.subtype := by
  classical
  -- the quotient is torsion-free
  haveI htf : Module.IsTorsionFree ℤ (T ⧸ N) := by
    constructor
    intro n hn x y hxy
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective N x
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective N y
    have hn0 : n ≠ 0 := hn.ne_zero
    have hmem : n • (t - u) ∈ N := by
      rw [smul_sub]
      rw [← Submodule.Quotient.eq]
      simpa using hxy
    have := hsat hn0 hmem
    rwa [Submodule.Quotient.eq]
  -- hence free and projective
  haveI : Module.Finite ℤ (T ⧸ N) := Module.Finite.quotient ℤ N
  haveI : Module.Free ℤ (T ⧸ N) := Module.free_of_finite_type_torsion_free'
  haveI : Module.Projective ℤ (T ⧸ N) := Module.Projective.of_free
  -- a section of the quotient map
  obtain ⟨σ, hσ⟩ :=
    Module.projective_lifting_property N.mkQ (LinearMap.id (R := ℤ) (M := T ⧸ N))
      (Submodule.Quotient.mk_surjective N)
  -- the complementary projector lands in `N`
  have hmem : ∀ t : T, t - σ (N.mkQ t) ∈ N := by
    intro t
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
    have : N.mkQ (σ (N.mkQ t)) = N.mkQ t := by
      have := congrArg (fun f => f (N.mkQ t)) hσ
      simpa using this
    rw [show (Submodule.Quotient.mk (σ (N.mkQ t)) : T ⧸ N) = N.mkQ (σ (N.mkQ t)) from rfl]
    rw [this]
    simp [Submodule.mkQ_apply]
  refine ⟨LinearMap.codRestrict N (LinearMap.id - σ.comp N.mkQ) (fun t => by
    simpa using hmem t), ?_⟩
  intro x
  apply Subtype.ext
  have hx : ((x : T) - σ (N.mkQ (x : T))) = (x : T) := by
    have hker : N.mkQ (x : T) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact x.2
    rw [hker, map_zero, sub_zero]
  simpa using hx

/-- Base change along a flat `ℤ`-algebra preserves injectivity of linear maps. Serre's
coefficient ring `B` is a subring of `ℂ`, hence torsion-free and flat over `ℤ`. -/
theorem baseChange_injective_of_flat
    {A : Type*} [CommRing A] [Module.Flat ℤ A]
    {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : M →ₗ[ℤ] N) (hf : Function.Injective f) :
    Function.Injective (f.baseChange A) := by
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := A) f hf
  have hco := congrFun (LinearMap.baseChange_eq_ltensor (A := A) (f := f))
  intro x y hxy
  apply hinj
  rw [← hco x, ← hco y]
  exact hxy

/-- The base change of the inclusion of a saturated submodule of a finitely generated
`ℤ`-module stays injective. -/
theorem baseChange_subtype_injective_of_saturated
    {T : Type*} [AddCommGroup T] [Module.Finite ℤ T]
    (N : Submodule ℤ T)
    (hsat : ∀ {t : T} {n : ℤ}, n ≠ 0 → n • t ∈ N → t ∈ N)
    (A : Type*) [CommRing A] :
    Function.Injective (N.subtype.baseChange A) := by
  obtain ⟨r, hr⟩ := exists_leftInverse_subtype_of_saturated N hsat
  have hr_comp : r.comp N.subtype = LinearMap.id := LinearMap.ext hr
  have hrA : (r.baseChange A).comp (N.subtype.baseChange A) = LinearMap.id := by
    simpa [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange A) hr_comp
  intro x y hxy
  calc
    x = ((r.baseChange A).comp (N.subtype.baseChange A)) x := by simp [hrA]
    _ = ((r.baseChange A).comp (N.subtype.baseChange A)) y := by
          simpa [LinearMap.comp_apply] using congrArg (fun z ↦ (r.baseChange A) z) hxy
    _ = y := by simp [hrA]

end Representation
