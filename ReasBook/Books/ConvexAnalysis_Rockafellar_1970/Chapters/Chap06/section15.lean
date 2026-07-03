import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_6_15 (from Chap02) -/
open scoped Rockafellar

section

open AffineSubspace
open Set

/-
Source/core/bridge triage:
- `source-facing`: Text 6.15 states that closures and relative interiors are preserved by
  translations, and more generally by affine equivalences of a finite-dimensional affine space,
  not by any chosen coordinate model.
- `core/canonical`: the intrinsic transport owner is `ContinuousAffineEquiv`, because preserving
  `intrinsicClosure` and `intrinsicInterior` only needs an affine homeomorphism. For
  `AffineEquiv`, the primitive bridge is continuity data for `e` and `e.symm`; finite-dimensional
  statements are derived corollaries.
- `bridge/view`: the public `AffineEquiv` theorems are thin finite-dimensional bridges from the
  source wording to that owner abstraction; ordinary closure is the topological companion theorem.
- Primitive data vs derived API: the only primitive object here is an affine equivalence together
  with whichever continuity data makes it a homeomorphism. Preservation of intrinsic closure and
  relative interior are derived owner API on that surface; the ordinary-closure statement is a
  companion corollary.
- Domain-style sampling: the relevant owner declarations inspected here are
  `ContinuousAffineEquiv.toHomeomorph`, `Homeomorph.subtype`, `Homeomorph.image_closure`,
  `AffineSubspace.mem_map_iff_mem_of_injective`, `AffineSubspace.map_span`, and
  `AffineEquiv.continuous_of_finiteDimensional`.
- Layer target: the new intrinsic-transport theorems are `core/canonical` owner declarations on
  `ContinuousAffineEquiv`; the `AffineEquiv` statements remain `bridge/view`.
-/

variable {𝕜 V W P Q : Type*}
  [Ring 𝕜]
  [AddCommGroup V] [Module 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W]
  [TopologicalSpace P] [AddTorsor V P]
  [TopologicalSpace Q] [AddTorsor W Q]

namespace ContinuousAffineEquiv

/-
Owner transport behind Text 6.15: affine homeomorphisms preserve intrinsic closures on affine
spaces.
-/
@[simp] theorem image_intrinsicClosure (e : P ≃ᴬ[𝕜] Q) (s : Set P) :
    cl[𝕜](e '' s) = e '' cl[𝕜](s) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  haveI : Nonempty s := hs.to_subtype
  let eA : P ≃ᵃ[𝕜] Q := e
  let spanHomeomorph : affineSpan 𝕜 s ≃ₜ (affineSpan 𝕜 s).map eA.toAffineMap :=
    e.toHomeomorph.subtype fun x ↦
      (AffineSubspace.mem_map_iff_mem_of_injective eA.injective).symm
  have hsubtype : eA.toAffineMap ∘ (↑) ∘ spanHomeomorph.symm = (↑) := by
    funext x
    exact congrArg Subtype.val (spanHomeomorph.apply_symm_apply x)
  change cl[𝕜](eA.toAffineMap '' s) = eA.toAffineMap '' cl[𝕜](s)
  rw [intrinsicClosure, intrinsicClosure, ← map_span eA.toAffineMap s,
    ← hsubtype, ← Function.comp_assoc, image_comp, image_comp,
    spanHomeomorph.symm.image_closure, spanHomeomorph.image_symm, ← preimage_comp,
    Function.comp_assoc, spanHomeomorph.symm_comp_self, Function.comp_id, preimage_comp]
  simp [eA]

@[simp] theorem image_intrinsicInterior (e : P ≃ᴬ[𝕜] Q) (s : Set P) :
    ri[𝕜](e '' s) = e '' ri[𝕜](s) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  haveI : Nonempty s := hs.to_subtype
  let eA : P ≃ᵃ[𝕜] Q := e
  let spanHomeomorph : affineSpan 𝕜 s ≃ₜ (affineSpan 𝕜 s).map eA.toAffineMap :=
    e.toHomeomorph.subtype fun x ↦
      (AffineSubspace.mem_map_iff_mem_of_injective eA.injective).symm
  have hsubtype : eA.toAffineMap ∘ (↑) ∘ spanHomeomorph.symm = (↑) := by
    funext x
    exact congrArg Subtype.val (spanHomeomorph.apply_symm_apply x)
  change ri[𝕜](eA.toAffineMap '' s) = eA.toAffineMap '' ri[𝕜](s)
  rw [intrinsicInterior, intrinsicInterior, ← map_span eA.toAffineMap s,
    ← hsubtype, ← Function.comp_assoc, image_comp, image_comp,
    spanHomeomorph.symm.image_interior, spanHomeomorph.image_symm, ← preimage_comp,
    Function.comp_assoc, spanHomeomorph.symm_comp_self, Function.comp_id, preimage_comp]
  simp [eA]

/-- Affine homeomorphisms preserve ambient closure. -/
@[simp] theorem image_closure (e : P ≃ᴬ[𝕜] Q) (s : Set P) :
    e '' closure s = closure (e '' s) := by
  simpa using e.toHomeomorph.image_closure s

end ContinuousAffineEquiv

namespace AffineEquiv

/-- Bundle an affine equivalence with continuity of both directions as a
`ContinuousAffineEquiv`. -/
def toContinuousAffineEquiv (e : P ≃ᵃ[𝕜] Q)
    (he : Continuous e) (he_symm : Continuous e.symm) : P ≃ᴬ[𝕜] Q :=
  { toAffineEquiv := e
    continuous_toFun := he
    continuous_invFun := he_symm }

@[simp] theorem coe_toContinuousAffineEquiv (e : P ≃ᵃ[𝕜] Q)
    (he : Continuous e) (he_symm : Continuous e.symm) :
    ⇑(e.toContinuousAffineEquiv he he_symm) = e :=
  rfl

end AffineEquiv

end

section

/-
Finite-dimensional bridge assumptions are kept at the TVS layer required by
`LinearMap.continuous_of_finiteDimensional`:
- complete nontrivially normed base field;
- `T2` on the source of each linear map (`V` for `e`, `W` for `e.symm`);
- finite dimensionality only on `V` (the one on `W` is derived from `e.linear`).
Topological-add-group structure on translation groups is recovered from the torsor hypotheses.
-/
variable
  {𝕜 V W P Q : Type*}
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W]
  [ContinuousSMul 𝕜 W] [T2Space W]
  [TopologicalSpace P] [AddTorsor V P] [IsTopologicalAddTorsor P]
  [TopologicalSpace Q] [AddTorsor W Q] [IsTopologicalAddTorsor Q]

namespace AffineEquiv

omit [T2Space W] in
private theorem continuous_of_finiteDimensional_tvs (e : P ≃ᵃ[𝕜] Q) : Continuous e := by
  letI : IsTopologicalAddGroup V :=
    IsTopologicalAddTorsor.to_isTopologicalAddGroup (V := V) (P := P)
  letI : IsTopologicalAddGroup W :=
    IsTopologicalAddTorsor.to_isTopologicalAddGroup (V := W) (P := Q)
  change Continuous e.toAffineMap
  rw [← AffineMap.continuous_linear_iff (f := e.toAffineMap)]
  exact (e.linear : V →ₗ[𝕜] W).continuous_of_finiteDimensional

omit [T2Space V] in
private theorem continuous_symm_of_finiteDimensional_tvs (e : P ≃ᵃ[𝕜] Q) :
    Continuous e.symm := by
  letI : IsTopologicalAddGroup V :=
    IsTopologicalAddTorsor.to_isTopologicalAddGroup (V := V) (P := P)
  letI : IsTopologicalAddGroup W :=
    IsTopologicalAddTorsor.to_isTopologicalAddGroup (V := W) (P := Q)
  haveI : FiniteDimensional 𝕜 W := e.linear.finiteDimensional
  change Continuous e.symm.toAffineMap
  rw [← AffineMap.continuous_linear_iff (f := e.symm.toAffineMap)]
  exact (e.symm.linear : W →ₗ[𝕜] V).continuous_of_finiteDimensional

/-- Finite-dimensional TVS bridge: an affine equivalence canonically upgrades to a
`ContinuousAffineEquiv`. -/
def toContinuousAffineEquivOfFiniteDimensional (e : P ≃ᵃ[𝕜] Q) : P ≃ᴬ[𝕜] Q :=
  e.toContinuousAffineEquiv (continuous_of_finiteDimensional_tvs e)
    (continuous_symm_of_finiteDimensional_tvs e)

/-- Text 6.15 (1), finite-dimensional bridge: affine equivalences preserve intrinsic closure, so
in particular translations do. -/
@[simp] theorem image_intrinsicClosure_of_finiteDimensional (e : P ≃ᵃ[𝕜] Q) (s : Set P) :
    cl[𝕜](e '' s) = e '' cl[𝕜](s) := by
  simpa only [toContinuousAffineEquivOfFiniteDimensional] using
    ContinuousAffineEquiv.image_intrinsicClosure
      (e := e.toContinuousAffineEquivOfFiniteDimensional) (s := s)

/-- Text 6.15 (1), finite-dimensional bridge: affine equivalences preserve closure, so in
particular translations do. -/
@[simp] theorem image_closure_of_finiteDimensional (e : P ≃ᵃ[𝕜] Q) (s : Set P) :
    e '' closure s = closure (e '' s) := by
  simpa only [toContinuousAffineEquivOfFiniteDimensional] using
    ContinuousAffineEquiv.image_closure
      (e := e.toContinuousAffineEquivOfFiniteDimensional) (s := s)

/-- Text 6.15 (2), finite-dimensional bridge: affine equivalences preserve relative interiors, so
in particular translations do. -/
@[simp] theorem image_intrinsicInterior_of_finiteDimensional (e : P ≃ᵃ[𝕜] Q) (s : Set P) :
    ri[𝕜](e '' s) = e '' ri[𝕜](s) := by
  simpa only [toContinuousAffineEquivOfFiniteDimensional] using
    ContinuousAffineEquiv.image_intrinsicInterior
      (e := e.toContinuousAffineEquivOfFiniteDimensional) (s := s)

end AffineEquiv

end
