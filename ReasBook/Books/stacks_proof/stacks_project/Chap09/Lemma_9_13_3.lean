import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

/-
Domain-style sampling:
- primary domain: Dedekind linear independence of families of algebra morphisms and their
  underlying linear/function realizations;
- sampled declarations:
  `linearIndependent_monoidHom`,
  `linearIndependent_algHom_toLinearMap`,
  `AlgHom.toLinearMap`,
  `LinearMap.ltoFun`;
- best owner abstraction: `linearIndependent_algHom_toLinearMap` is the canonical owner in the
  `AlgHom` domain; the present lemma is only the thin source-facing bridge from that owner to the
  same family viewed as plain functions;
- primitive data vs. derived API:
  primitive data is the family `σ : ι → A →ₐ[R] B` with injective indexing;
  derived API is the induced family of linear maps `fun i ↦ (σ i).toLinearMap` and the resulting
  linear independence of the underlying functions `fun i ↦ (σ i : A → B)`.

Source/core/bridge triage:
- `source-facing`: `linearIndependent_extension_morphisms`;
- `core/canonical`: `linearIndependent_algHom_toLinearMap`;
- `bridge/view`: `LinearMap.ltoFun`.
-/
recall linearIndependent_algHom_toLinearMap

/-- Lemma 9.13.3: pairwise distinct morphisms of `F`-extensions `σ₁, …, σₙ : K →ₐ[F] L` are
`L`-linearly independent as functions `K → L`; equivalently, every nontrivial finite
`L`-linear combination of the `σᵢ` is nonzero at some element of `K`. The source states this for
field extensions indexed by `Fin n`, but the canonical owner theorem already works for any
injectively indexed family of `R`-algebra morphisms from a semiring-algebra `A` to a commutative
domain `B`. -/
-- Proof sketch: apply the canonical owner theorem
-- `linearIndependent_algHom_toLinearMap` to the family of algebra morphisms, then pass from the
-- resulting family of linear maps to the same family seen as functions via `LinearMap.ltoFun`.
@[stacks 0CKM]
theorem linearIndependent_extension_morphisms
    {R : Type u} {A : Type v} {B : Type w} {ι : Type x}
    [CommSemiring R] [Semiring A] [Algebra R A]
    [CommRing B] [IsDomain B] [Algebra R B]
    (σ : ι → A →ₐ[R] B) (hσ : Function.Injective σ) :
    LinearIndependent B (fun i ↦ (σ i : A → B)) := by
  -- First move to the canonical owner theorem about algebra morphisms viewed as linear maps.
  have hσ' : LinearIndependent B (fun i ↦ (σ i).toLinearMap) :=
    (linearIndependent_algHom_toLinearMap R A B).comp σ hσ
  -- The forgetful map from linear maps to plain functions is injective, so its kernel is trivial.
  have hker : LinearMap.ker (LinearMap.ltoFun R A B B) = ⊥ := by
    ext f
    simp [LinearMap.ext_iff]
  -- Transport linear independence across that injective forgetful map and identify the functions.
  simpa using hσ'.map' (LinearMap.ltoFun R A B B) hker
