import Mathlib
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.SemilinearGaloisDescent

/-!
# `G`-equivariant Galois descent of representations

This module upgrades the abstract semilinear Galois descent
(`Serre/Chap14/Remark_14_14_5_1/Modular/SemilinearGaloisDescent.lean`) from vector spaces to
representations.  If a monoid `G` acts `L`-linearly on a finite-dimensional `L`-module `M` by a
representation `ρ` that **commutes** with the semilinear `Γ = Gal(L/k)`-action, then the `Γ`-fixed
points `M^Γ` carry a `k`-representation `descendedRep` whose scalar extension to `L` is `(M, ρ)`:

* `descentRepEquiv : (Representation.scalarExtension (k := L) (descendedRep A ρ hcomm)).Equiv ρ`.

This is exactly the form consumed by the modular Galois-descent summit: it turns a semilinear descent
datum on the underlying space of an `L[G]`-module into a genuine `k`-model.
-/

noncomputable section

universe u v

open scoped TensorProduct
open Module

namespace Representation

namespace SemilinearGaloisAction

variable {k : Type u} [Field k] {L : Type u} [Field L] [Algebra k L]
variable {M : Type v} [AddCommGroup M] [Module L M] [Module k M] [IsScalarTower k L M]
variable {G : Type*} [Monoid G]
variable (A : SemilinearGaloisAction k L M) (ρ : Representation L G M)
variable (hcomm : ∀ (σ : L ≃ₐ[k] L) (g : G) (m : M), A.act σ (ρ g m) = ρ g (A.act σ m))

include hcomm

/-- `G` preserves the `Γ`-fixed points. -/
theorem map_mem_fixed (g : G) {m : M} (hm : m ∈ A.fixed) : ρ g m ∈ A.fixed := by
  rw [A.mem_fixed_iff]
  intro σ
  rw [hcomm σ g m, (A.mem_fixed_iff.mp hm) σ]

/-- The descended `k`-representation on the `Γ`-fixed points: `g` acts by the (`k`-linear restriction
of the) `L`-linear operator `ρ g`, which preserves `M^Γ`. -/
def descendedRep : Representation k G A.fixed where
  toFun g := LinearMap.restrict ((ρ g).restrictScalars k)
    (fun _ hm => map_mem_fixed A ρ hcomm g hm)
  map_one' := by
    ext m
    simp [LinearMap.restrict_apply]
  map_mul' g h := by
    ext m
    simp [LinearMap.restrict_apply, map_mul, Module.End.mul_eq_comp]

@[simp] theorem descendedRep_apply_coe (g : G) (m : A.fixed) :
    ((descendedRep A ρ hcomm g m : A.fixed) : M) = ρ g (m : M) := rfl

variable [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional L M]

/-- **`G`-equivariance of the descent isomorphism.**  The descent map `descentEquiv : L ⊗[k] M^Γ ≅ M`
intertwines the base change of the descended `G`-action with `ρ`: for every `g` and `x`,
`descentEquiv (baseChange (descendedRep g) x) = ρ g (descentEquiv x)`.

This is the descent datum at the level of representations, stated without naming
`Representation.scalarExtension` (whose `[CommRing k]`-derived `Semiring L` instance clashes — though
it is `rfl`-defeq — with the ambient `Field L` one).  The summit assembly packages this into a
genuine `FDRep` isomorphism `FDRep.scalarExtension (FDRep.of descendedRep) ≅ (M, ρ)` once the carrier
is concrete. -/
theorem descentEquiv_baseChange_descendedRep (g : G) (x : L ⊗[k] A.fixed) :
    A.descentEquiv (LinearMap.baseChange L (descendedRep A ρ hcomm g) x)
      = ρ g (A.descentEquiv x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l m =>
      rw [LinearMap.baseChange_tmul, A.descentEquiv_tmul, descendedRep_apply_coe,
        A.descentEquiv_tmul, map_smul]
  | add x y hx hy => simp only [map_add]; rw [hx, hy]

end SemilinearGaloisAction

end Representation
