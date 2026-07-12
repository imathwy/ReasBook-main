import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap10.EqualEndpointRing

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped TensorProduct

universe u

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k
local notation "K0→K0'" =>
  ModulePropertyK0.map R (finiteProjectiveModuleProperty_le_isFG R)

-- Proof sketch: classify finitely generated projective modules over
-- `R = {f ∈ k[x] | f(0) = f(1)}` by rank together with a unit parameter, and identify `K'_0(R)`
-- with `ℤ` via the finite-module Grothendieck group used canonically in this chapter.
/-- The generic-rank invariant on finite `R`-modules, computed after base change to the fraction
field of `R`. -/
private noncomputable def equalEndpointRank (M : FGModuleCat R) : ℤ :=
  let _ : Module.Finite R M.obj := M.property
  (Module.finrank (FractionRing R) ((FractionRing R) ⊗[R] M.obj) : ℤ)

/-- The Grothendieck relations for finite `R`-modules lie in the kernel of the generic-rank
functional. -/
private theorem equalEndpointRelations_le_ker_rank :
    modulePropertyK0Relations R (ModuleCat.isFG R) ≤
      (FreeAbelianGroup.lift (equalEndpointRank k)).ker := sorry

/-- The generic-rank map `K'_0(R) → ℤ` for the equal-endpoint ring. -/
private noncomputable def equalEndpointRankMap :
    finiteGrothendieckGroup R →+ ℤ :=
  ModulePropertyK0.lift R (equalEndpointRank k)
    (equalEndpointRelations_le_ker_rank k)

/-- The generic-rank map on `K'_0(R)` is bijective for the equal-endpoint ring. -/
-- Proof sketch: surjectivity is realized by the class of a free rank-one module. Injectivity is
-- the equal-endpoint analogue of the PID generic-rank computation, using the classification of
-- finite modules over this ring to show that the `K'_0`-class is determined by generic rank.
private theorem equalEndpointRankMap_bijective :
    Function.Bijective (equalEndpointRankMap k) := sorry

/-- Example 10.55.5 (1): for `R = {f ∈ k[x] | f(0) = f(1)}`, the finite-module Grothendieck group
`K'_0(R)` is canonically identified with `ℤ` by the generic-rank map. -/
noncomputable def equal_endpoint_ring_finiteGrothendieckGroup :
    finiteGrothendieckGroup R ≃+ ℤ :=
  AddEquiv.ofBijective (equalEndpointRankMap k) (equalEndpointRankMap_bijective k)

/-- The additive equivalence `K'_0(R) ≃+ ℤ` acts by the generic-rank map. -/
theorem equal_endpoint_ring_finiteGrothendieckGroup_apply (x : finiteGrothendieckGroup R) :
    equal_endpoint_ring_finiteGrothendieckGroup k x =
      equalEndpointRankMap k x := rfl

/-- Example 10.55.5 (2): for `R = {f ∈ k[x] | f(0) = f(1)}`, the Grothendieck group `K₀(R)` of finite
projective `R`-modules is identified with `Additive kˣ × ℤ`. -/
-- Proof sketch: combine the classification of finite projective modules over the equal-endpoint
-- ring with the generic-rank identification of `K'_0(R)` with `ℤ`, and choose an additive
-- equivalence whose second component matches the canonical comparison map to `K'_0(R)`.
theorem equal_endpoint_ring_projectiveGrothendieckGroup :
    ∃ e : projectiveGrothendieckGroup R ≃+ Additive kˣ × ℤ,
      (AddMonoidHom.snd (Additive kˣ) ℤ).comp e.toAddMonoidHom =
      (equal_endpoint_ring_finiteGrothendieckGroup k).toAddMonoidHom.comp K0→K0' := sorry

/-- On an element of `K₀(R)`, some additive equivalence
`K₀(R) ≃+ Additive kˣ × ℤ` has `ℤ`-component given by the canonical comparison to `K'_0(R)`
followed by the generic-rank identification of `K'_0(R)` with `ℤ`. -/
theorem equal_endpoint_ring_projectiveGrothendieckGroup_snd_apply
    (x : projectiveGrothendieckGroup R) :
    ∃ e : projectiveGrothendieckGroup R ≃+ Additive kˣ × ℤ,
      (e x).2 =
        equal_endpoint_ring_finiteGrothendieckGroup k (K0→K0' x) := by
  rcases equal_endpoint_ring_projectiveGrothendieckGroup k with ⟨e, he⟩
  refine ⟨e, ?_⟩
  simpa using DFunLike.congr_fun he x

end
