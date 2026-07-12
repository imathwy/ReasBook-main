import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.GaloisDescent
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.CoefficientTwist

/-!
# The σ-twist of a simple module is simple, and is isomorphic to it under Galois invariance

This module completes **step G1** of the characteristic-`p` Galois-descent argument
(Brick 2 of Remark 14-14.5-1).  Building on the coefficient twist `Tˢ = Twist σ T` of
`CoefficientTwist.lean` and the linear-independence engine of `GaloisDescent.lean`, it proves:

* `simple_twist` : the σ-coefficient twist of a **simple** `k̄[G]`-module is simple.  The
  `k̄[G]`-submodule lattices of `Tˢ` and `T` are order-isomorphic via the σ-semilinear identity
  `TwistSpace.ofBaseₛₗ : T ≃ₛₗ[σ] Tˢ` (a subset is `G`-stable and closed under the twisted scalar
  action `c • v = σ⁻¹ c • v` iff it is `G`-stable and closed under the original scalar action), so
  `Tˢ` is irreducible iff `T` is.

* `exists_twist_iso_of_modularCharacter_galoisInvariant` : if the modular Brauer character of a
  simple `T` is Galois-invariant (computing it with the σ-twisted lift returns the original
  character) and the lift is **Galois-equivariant on the prime-to-`p` roots**, then `Tˢ ≅ T`.
  Combine the eigenvalue-twist identity `modularChar(Tˢ, L) = modularChar(T, L ∘ σ̂)`
  (`modularCharacterOnPRegularConjClass_twist`) with the Galois-equivariance
  `L ∘ σ̂ = σ ∘ L` of the lift and the invariance hypothesis to get equal Brauer characters of the
  two simple modules, then feed `iso_of_simple_of_modularCharacterOnPRegularConjClass_eq`.

## On the Galois-equivariance hypothesis

The eigenvalue twist always gives `modularChar(Tˢ, L) = modularChar(T, L ∘ σ̂)`, where
`σ̂ = twistPrimeToPRoot σ` is the `σ`-permutation of the prime-to-`p` roots of unity.  To rewrite
the right-hand side into the `σ`-postcomposed lift `x ↦ σ (L x)` appearing in the
Galois-invariance hypothesis one needs `L ∘ σ̂ = σ ∘ L`, i.e. the lift commutes with the Galois
action.  This is **not** automatic for an arbitrary multiplicative lift
`lift : PrimeToPRoot p k̄ →* k̄ˣ`, but it holds for the canonical inclusion lift
`(primeToPRoots p k̄).subtype` (for which `L` is the literal field value of the root, and
`twistPrimeToPRoot_coe` gives `(σ̂ z : k̄) = σ (z : k̄)`), which is exactly the lift used
to express that the Brauer character is `k`-valued (`BrauerCharacterKValued.canonicalLift`).  The
hypothesis-free specialization to the inclusion lift is `exists_twist_iso_inclusionLift`.
-/

noncomputable section

universe u

open scoped TensorProduct Representation MonoidAlgebra

open CategoryTheory

namespace Representation

variable {k : Type u} [Field k]
variable {p : ℕ} [hp : Fact p.Prime] [hk : CharP k p]
variable {G : Type u} [Group G] [Finite G]

local notation3 "k̄" => AlgebraicClosure k

/-- A `k`-algebra automorphism of `k̄` is surjective as a ring homomorphism. -/
instance ringHomSurjective_algEquiv (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
    RingHomSurjective (σ : AlgebraicClosure k →+* AlgebraicClosure k) :=
  ⟨fun y ↦ ⟨σ.symm y, σ.apply_symm_apply y⟩⟩

variable (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (T : FDRep (AlgebraicClosure k) G)

/-- **The σ-semilinear identity intertwines the `G`-actions of `T` and its twist.**  Since the
twisted endomorphism `twistMap (T.ρ g)` has the same underlying additive map as `T.ρ g`, the
σ-semilinear identity `ofBaseₛₗ` carries `T.ρ g` to the twist action `twistRepresentation σ T g`. -/
theorem ofBaseₛₗ_intertwine (g : G) (w : T) :
    TwistSpace.ofBaseₛₗ (σ := σ) (T.ρ g w)
      = twistRepresentation σ T g (TwistSpace.ofBaseₛₗ (σ := σ) w) := by
  rw [twistRepresentation_apply, TwistSpace.ofBaseₛₗ_apply, TwistSpace.ofBaseₛₗ_apply,
    TwistSpace.twistMap_apply]

/-- Forward direction of the subrepresentation order isomorphism: the image of a subrepresentation
of `T.ρ` under the σ-semilinear identity is a subrepresentation of the twist. -/
def twistSubrepForward (W : Subrepresentation T.ρ) :
    Subrepresentation (twistRepresentation σ T) where
  toSubmodule :=
    Submodule.map (TwistSpace.ofBaseₛₗ (σ := σ)).toLinearMap W.toSubmodule
  apply_mem_toSubmodule g x hx := by
    rw [Submodule.mem_map] at hx ⊢
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨T.ρ g w, W.apply_mem_toSubmodule g hw, ?_⟩
    simp only [LinearEquiv.coe_coe]
    exact ofBaseₛₗ_intertwine σ T g w

/-- Inverse direction of the subrepresentation order isomorphism: the preimage of a
subrepresentation of the twist under the σ-semilinear identity is a subrepresentation of `T.ρ`. -/
def twistSubrepInverse (N : Subrepresentation (twistRepresentation σ T)) :
    Subrepresentation T.ρ where
  toSubmodule :=
    Submodule.comap (TwistSpace.ofBaseₛₗ (σ := σ)).toLinearMap N.toSubmodule
  apply_mem_toSubmodule g x hx := by
    rw [Submodule.mem_comap] at hx ⊢
    simp only [LinearEquiv.coe_coe] at hx ⊢
    rw [ofBaseₛₗ_intertwine σ T g x]
    exact N.apply_mem_toSubmodule g hx

/-- **The subrepresentation lattices of `T` and its σ-twist `Tˢ` are order-isomorphic.**  The
σ-semilinear identity `ofBaseₛₗ : T ≃ₛₗ[σ] Tˢ` is a bijection of underlying additive groups carrying
`T.ρ g` to `Tˢ.ρ g`, so `map`/`comap` along it identify the `G`-stable submodule lattices. -/
def subrepTwistOrderIso :
    Subrepresentation T.ρ ≃o Subrepresentation (twistRepresentation σ T) where
  toFun := twistSubrepForward σ T
  invFun := twistSubrepInverse σ T
  left_inv W := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.comap_map_eq_of_injective
      (f := (TwistSpace.ofBaseₛₗ (σ := σ)).toLinearMap)
      (TwistSpace.ofBaseₛₗ (σ := σ)).injective W.toSubmodule
  right_inv N := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.map_comap_eq_of_surjective
      (f := (TwistSpace.ofBaseₛₗ (σ := σ)).toLinearMap)
      (TwistSpace.ofBaseₛₗ (σ := σ)).surjective N.toSubmodule
  map_rel_iff' := by
    intro W₁ W₂
    exact Submodule.map_le_map_iff_of_injective
      (f := (TwistSpace.ofBaseₛₗ (σ := σ)).toLinearMap)
      (TwistSpace.ofBaseₛₗ (σ := σ)).injective W₁.toSubmodule W₂.toSubmodule

/-- **The underlying representation of the σ-twist of an irreducible representation is
irreducible.**  Transport `IsSimpleOrder` of the subrepresentation lattice across
`subrepTwistOrderIso`. -/
theorem isIrreducible_twistRepresentation [Representation.IsIrreducible T.ρ] :
    Representation.IsIrreducible (twistRepresentation σ T) :=
  (subrepTwistOrderIso σ T).isSimpleOrder_iff.mp inferInstance

/-- **The σ-coefficient twist of a simple `k̄[G]`-module is simple.** -/
theorem simple_twist [Simple T] : Simple (Twist σ T) := by
  haveI hirr : Representation.IsIrreducible T.ρ := FDRep.isIrreducible_of_simple T
  haveI : Representation.IsIrreducible (Twist σ T).ρ := isIrreducible_twistRepresentation σ T
  exact FDRep.simple_of_isIrreducible (Twist σ T)

section ModularCharacter

/-- **Equal Brauer characters of `Tˢ` and `T` from Galois invariance.**

Given the eigenvalue twist `modularChar(Tˢ, L) = modularChar(T, L ∘ σ̂)`
(`modularCharacterOnPRegularConjClass_twist`), the Galois-equivariance `L ∘ σ̂ = σ ∘ L` of the lift
(`hcompat`), and the Galois invariance `modularChar(T, σ ∘ L) = modularChar(T, L)` (`hInv`),
the modular Brauer characters of `Tˢ` and `T` coincide. -/
theorem modularCharacterOnPRegularConjClass_twist_eq_of_galoisCompat
    (lift : PrimeToPRoot p (AlgebraicClosure k) → AlgebraicClosure k)
    (hcompat : lift ∘ twistPrimeToPRoot σ
        = fun x ↦ (σ : AlgebraicClosure k →+* AlgebraicClosure k) (lift x))
    (hInv : FDRep.modularCharacterOnPRegularConjClass (p := p) T
              (fun x ↦ (σ : AlgebraicClosure k →+* AlgebraicClosure k) (lift x))
            = FDRep.modularCharacterOnPRegularConjClass (p := p) T lift) :
    FDRep.modularCharacterOnPRegularConjClass (p := p) (Twist σ T) lift
      = FDRep.modularCharacterOnPRegularConjClass (p := p) T lift := by
  rw [modularCharacterOnPRegularConjClass_twist (σ := σ) (T := T) lift, hcompat, hInv]

/-- **The σ-twist of a simple module with Galois-invariant modular character is isomorphic to it.**

Here `lift : PrimeToPRoot p k̄ →* k̄ˣ` is an injective multiplicative lift, `hcompat` records its
Galois-equivariance on the prime-to-`p` roots of unity (automatic for the canonical inclusion lift,
see `exists_twist_iso_inclusionLift`), and `hInv` is the Galois-invariance of the modular Brauer
character of `T` under the twist by `σ`.  The conclusion is `Tˢ ≅ T`, the Galois-fixedness output
of step G1. -/
theorem exists_twist_iso_of_modularCharacter_galoisInvariant
    (lift : PrimeToPRoot p (AlgebraicClosure k) →* (AlgebraicClosure k)ˣ)
    (hlift : Function.Injective lift)
    [Simple T]
    (hcompat : PrimeToPRoot.toFieldLift lift ∘ twistPrimeToPRoot σ
        = fun x ↦ (σ : AlgebraicClosure k →+* AlgebraicClosure k)
          (PrimeToPRoot.toFieldLift lift x))
    (hInv : FDRep.modularCharacterOnPRegularConjClass (p := p) T
              (fun x ↦ (σ : AlgebraicClosure k →+* AlgebraicClosure k)
                (PrimeToPRoot.toFieldLift lift x))
            = FDRep.modularCharacterOnPRegularConjClass (p := p) T
                (PrimeToPRoot.toFieldLift lift)) :
    Nonempty (Twist σ T ≅ T) := by
  haveI := simple_twist σ T
  refine iso_of_simple_of_modularCharacterOnPRegularConjClass_eq lift hlift (Twist σ T) T ?_
  exact modularCharacterOnPRegularConjClass_twist_eq_of_galoisCompat σ T
    (PrimeToPRoot.toFieldLift lift) hcompat hInv

/-- **Hypothesis-free specialization to the canonical inclusion lift.**

For the inclusion lift `(primeToPRoots p k̄).subtype`, whose field value on a prime-to-`p` root is
the root itself, the Galois-equivariance hypothesis is discharged by `twistPrimeToPRoot_coe`.  This
is the lift used to express `k`-valuedness of the modular Brauer character; the resulting `Tˢ ≅ T`
from the Galois invariance `hInv` is the Galois-fixedness consumed by the module-level descent. -/
theorem exists_twist_iso_inclusionLift
    [Simple T]
    (hInv : FDRep.modularCharacterOnPRegularConjClass (p := p) T
              (fun x ↦ (σ : AlgebraicClosure k →+* AlgebraicClosure k)
                (PrimeToPRoot.toFieldLift
                  (primeToPRoots p (AlgebraicClosure k)).subtype x))
            = FDRep.modularCharacterOnPRegularConjClass (p := p) T
                (PrimeToPRoot.toFieldLift
                  (primeToPRoots p (AlgebraicClosure k)).subtype)) :
    Nonempty (Twist σ T ≅ T) :=
  exists_twist_iso_of_modularCharacter_galoisInvariant σ T
    (primeToPRoots p (AlgebraicClosure k)).subtype
    (Subgroup.subtype_injective _)
    (by funext x; exact twistPrimeToPRoot_coe x)
    hInv

end ModularCharacter

end Representation
