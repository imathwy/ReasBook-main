import Mathlib
import stacks_project.Chap15.Remark_15_119_1

-- Declarations for this item will be appended below by the statement pipeline.

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
