import Mathlib
import Serre.Chap15.Exercise_15_15_5_3.MaximalIdealPowSquareZero

open scoped TensorProduct

universe u v w

section

variable {A : Type u} [CommRing A] [IsLocalRing A]

namespace Representation

section TransitionLiftBridge

variable {p : ℕ}
variable [CharP (IsLocalRing.ResidueField A) p]
variable {G : Type v} [Group G] [Finite G]
variable {E : Type w} [AddCommGroup E] [Module A E] [Module.Free A E] [Module.Finite A E]

local notation "𝔪" => IsLocalRing.maximalIdeal A
local notation "A⧸𝔪^(" n ")" => A ⧸ (𝔪 ^ n)
local notation "E⧸𝔪^(" n ")E" => E ⧸ ((𝔪 ^ n) • (⊤ : Submodule A E))

/-- Helper for Exercise 15-15.5-3: the quotient ring `A ⧸ 𝔪^(n+1)` acts on the `n`-th quotient
through `Ideal.Quotient.factorPowSucc`, so the transition map can be packaged on the larger
quotient-ring surface used by the projective lifting step. -/
private theorem maximalIdealPowTransition_map_smul_factorPowSucc
    (n : ℕ+)
    (r : A⧸𝔪^((n : ℕ) + 1))
    (x : E⧸𝔪^((n : ℕ) + 1)E) :
    maximalIdealPowTransition (A := A) (E := E) n (r • x) =
      Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ) r •
        maximalIdealPowTransition (A := A) (E := E) n x := by
  -- The transition map is induced by the identity on `E`, so scalar action commutes pointwise.
  refine Quotient.inductionOn' x ?_
  intro y
  refine Quotient.inductionOn' r ?_
  intro a
  rfl

/-- Helper for Exercise 15-15.5-3: package the transition
`E / 𝔪^(n+1) E → E / 𝔪^n E` as a genuinely `A ⧸ 𝔪^(n+1)`-linear map by transporting the scalar
action on the codomain through `Ideal.Quotient.factorPowSucc`. -/
abbrev maximalIdealPowTransition_linear_over_factorPowSucc
    (n : ℕ+) :
    letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
      Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
    E⧸𝔪^((n : ℕ) + 1)E →ₗ[A⧸𝔪^((n : ℕ) + 1)] E⧸𝔪^((n : ℕ))E := by
  letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
    Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
  exact
    { toFun := maximalIdealPowTransition (A := A) (E := E) n
      map_add' := (maximalIdealPowTransition (A := A) (E := E) n).map_add
      map_smul' := maximalIdealPowTransition_map_smul_factorPowSucc (A := A) (E := E) n }

/-- Helper for Exercise 15-15.5-3: the transported transition map has the same underlying
function as the original `A`-linear transition. This is the pointwise bridge back to the
source-level reduction map. -/
theorem maximalIdealPowTransition_linear_over_factorPowSucc_apply
    (n : ℕ+)
    (x : E⧸𝔪^((n : ℕ) + 1)E) :
    letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
      Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
    maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n x =
      maximalIdealPowTransition (A := A) (E := E) n x := by
  letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
    Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
  rfl

/-- Helper for Exercise 15-15.5-3: every downstairs endomorphism over `A ⧸ 𝔪^n` can be viewed as
an endomorphism over `A ⧸ 𝔪^(n+1)` on the same underlying quotient module, via
`Ideal.Quotient.factorPowSucc`. -/
private theorem downstairs_endomorphism_map_smul_factorPowSucc
    (n : ℕ+)
    (u : Module.End (A⧸𝔪^((n : ℕ))) (E⧸𝔪^((n : ℕ))E))
    (r : A⧸𝔪^((n : ℕ) + 1))
    (x : E⧸𝔪^((n : ℕ))E) :
    u (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ) r • x) =
      Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ) r • u x := by
  -- The transported scalar is exactly the scalar seen by the original `A ⧸ 𝔪^n`-linear map.
  simpa using u.map_smul (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ) r) x

/-- Helper for Exercise 15-15.5-3: package a downstairs `A ⧸ 𝔪^n`-linear endomorphism as an
`A ⧸ 𝔪^(n+1)`-linear endomorphism on the same underlying quotient module. -/
abbrev downstairs_endomorphism_over_factorPowSucc
    (n : ℕ+)
    (u : Module.End (A⧸𝔪^((n : ℕ))) (E⧸𝔪^((n : ℕ))E)) :
    letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
      Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
    Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) := by
  letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
    Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
  exact
    { toFun := u
      map_add' := u.map_add
      map_smul' := downstairs_endomorphism_map_smul_factorPowSucc (A := A) (E := E) n u }

/-- Helper for Exercise 15-15.5-3: the transported downstairs endomorphism has the same
underlying function as the original `A ⧸ 𝔪^n`-linear map. -/
theorem downstairs_endomorphism_over_factorPowSucc_apply
    (n : ℕ+)
    (u : Module.End (A⧸𝔪^((n : ℕ))) (E⧸𝔪^((n : ℕ))E))
    (x : E⧸𝔪^((n : ℕ))E) :
    letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
      Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
    downstairs_endomorphism_over_factorPowSucc (A := A) (E := E) n u x = u x := by
  letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
    Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
  rfl

/-- Helper for Exercise 15-15.5-3: the `(n+1)`-st quotient of a finite free `A`-module is already
projective over the quotient ring `A ⧸ 𝔪^(n+1)`. This isolates the canonical projective owner
needed before applying `Module.projective_lifting_property`. -/
theorem maximalIdealPowQuotient_projective_over_factorPowSucc
    (n : ℕ+) :
    Module.Projective (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E) := by
  let e :=
    LinearEquiv.extendScalarsOfSurjective
      (R := A)
      (S := A⧸𝔪^((n : ℕ) + 1))
      (M := TensorProduct A (A⧸𝔪^((n : ℕ) + 1)) E)
      (N := E⧸𝔪^((n : ℕ) + 1)E)
      (by simpa using (Ideal.Quotient.mk_surjective (I := (𝔪 ^ ((n : ℕ) + 1)))))
      (TensorProduct.quotTensorEquivQuotSMul E (𝔪 ^ ((n : ℕ) + 1)))
  -- The quotient is a base change of a free module, hence projective over the quotient ring.
  letI : Module.Projective (A⧸𝔪^((n : ℕ) + 1))
      (TensorProduct A (A⧸𝔪^((n : ℕ) + 1)) E) := inferInstance
  exact Module.Projective.of_equiv' e

/-- Helper for Exercise 15-15.5-3: once the transition map and the downstairs endomorphism are
both transported to the ring `A ⧸ 𝔪^(n+1)`, projectivity of the upstairs quotient lifts the
endomorphism across the surjective transition map. -/
theorem exists_linearMap_lift_of_transition_factorPowSucc
    (n : ℕ+) :
    letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
      Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
    ∀ f : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E),
      ∃ F : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E),
        (maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n).comp F =
          f.comp (maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n) := by
  letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
    Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
  intro f
  have hproj :
      Module.Projective (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E) :=
    maximalIdealPowQuotient_projective_over_factorPowSucc (A := A) (E := E) n
  have hsurj :
      Function.Surjective
        (maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n) := by
    -- Transporting scalars on the codomain does not change the underlying surjective function.
    intro x
    refine Quotient.inductionOn' x ?_
    intro y
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    -- Normalize both quotient constructors to the same representative before closing by reflexivity.
    change maximalIdealPowTransition (A := A) (E := E) n (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk y
    rfl
  obtain ⟨F, hF⟩ :=
    Module.projective_lifting_property
      (maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n)
      (f.comp (maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n))
      hsurj
  exact ⟨F, hF⟩

end TransitionLiftBridge

end Representation

end
