import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory
open OrderDual

noncomputable section

universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Domain triage:
* `source-facing`: Lemma `15.27.4` studies a sequential inverse system of `A`-modules over `ℕ+`
  and the canonical comparison map from tensoring after inverse limit to the inverse limit of the
  tensorized system.
* `core/canonical` owners: the inverse system itself as a functor `OrderDual ℕ+ ⥤ ModuleCat A`,
  its transition maps coming from `Functor.map`, the canonical comparison morphism
  `CategoryTheory.Limits.limit.post`, and the flatness owner `Module.Flat`.
* `bridge/view`: bijectivity of the comparison morphism for finite modules, then flatness of the
  inverse limit deduced from that bijectivity criterion.

Relevant owner declarations sampled for this refinement:
* `CategoryTheory.SequentialInverseSystem.stepMap`
* `CategoryTheory.Functor.map`
* `CategoryTheory.Limits.limit.post`
* `CategoryTheory.Limits.limit.post_π`
* `Module.Flat.iff_preservesFiniteLimits_tensorLeft`

Primitive data are only the inverse system `M_`, the stagewise quotient-flat hypotheses, and the
surjectivity of the successive transition maps. The tensor-limit comparison itself is canonical
derived API, so the public statement uses `limit.post` directly rather than a local wrapper.
Because the system is indexed by `OrderDual ℕ+` rather than the chapter owner `ℕᵒᵖ`, the
successor map is kept only as a private `stepMap` helper mirroring the canonical owner vocabulary. -/

private theorem pnat_le_succ (n : ℕ+) : n ≤ n + 1 := by
  exact_mod_cast Nat.le_succ (n : ℕ)

/-- The successor map `M_{n + 1} → M_n` in a positive-index inverse system of `A`-modules. -/
private abbrev stepMap (M_ : OrderDual ℕ+ ⥤ ModuleCat A) (n : ℕ+) :
    M_.obj (toDual (n + 1)) ⟶ M_.obj (toDual n) :=
  M_.map (homOfLE (pnat_le_succ n))

variable (I : Ideal A) (M_ : OrderDual ℕ+ ⥤ ModuleCat A)
variable [∀ n : ℕ+, Module (A ⧸ I ^ (n : ℕ)) (M_.obj (toDual n))]
variable [∀ n : ℕ+, IsScalarTower A (A ⧸ I ^ (n : ℕ)) (M_.obj (toDual n))]

-- Proof sketch: resolve the finite `A`-module `Q` by finite free modules, tensor that resolution
-- with each stage `M_n`, use flatness over `A ⧸ I^n` and Lemma `15.27.3` to make the inverse
-- systems of `Tor₁^A(Q, M_n)` eventually zero, then pass to inverse limits through the resulting
-- exact complexes. Because finite free modules commute with inverse limits, the cokernel computed
-- after passing to the limit identifies with `Q ⊗[A] lim M_n`.
/-- Lemma 15.27.4 (1): for a surjective inverse system `M_n` of `A`-modules whose stage `M_n` is
flat over `A ⧸ I^n`, the canonical map from `Q ⊗[A] lim M_n` to `lim (Q ⊗[A] M_n)` is bijective
for every finite `A`-module `Q`. -/
theorem inverseLimit_tensor_finiteModule_bijective_of_surjective_and_quotientFlat
    (hflat :
      ∀ n : ℕ+, Module.Flat (A ⧸ I ^ (n : ℕ)) (M_.obj (toDual n)))
    (hsurj : ∀ n : ℕ+, Function.Surjective (stepMap M_ n))
    (Q : Type u) [AddCommGroup Q] [Module A Q] [Module.Finite A Q] :
    Function.Bijective (limit.post M_ (tensorLeft (ModuleCat.of A Q))) := sorry

-- Proof sketch: by Lemma `10.39.5`, it is enough to test injectivity after tensoring with every
-- injective map of finite `A`-modules. Part `(1)` identifies tensoring with `lim M_n` against a
-- finite module with the inverse limit of the stagewise tensors. The stagewise long exact Tor
-- sequences and Lemma `15.27.3` make the obstruction on kernels eventually vanish, and the
-- exactness of inverse limits for surjective systems then yields the needed injectivity.
/-- Lemma 15.27.4 (2): if `M_n` is a surjective inverse system of `A`-modules and each stage
`M_n` is flat over `A ⧸ I^n`, then the inverse limit `lim M_n` is flat over `A`. -/
theorem inverseLimit_flat_of_surjective_and_quotientFlat
    (hflat :
      ∀ n : ℕ+, Module.Flat (A ⧸ I ^ (n : ℕ)) (M_.obj (toDual n)))
    (hsurj : ∀ n : ℕ+, Function.Surjective (stepMap M_ n)) :
    Module.Flat A ↑(limit M_) := sorry

end
