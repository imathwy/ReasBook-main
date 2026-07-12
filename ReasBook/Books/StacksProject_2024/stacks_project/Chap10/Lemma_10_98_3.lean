import Mathlib

open CategoryTheory
open scoped DirectSum
open HomogeneousIdeal

universe u w

section

/- Domain triage:
* `source-facing`: Lemma `10.98.3` asks for one finite graded `A`-module whose quotients
  `N / I^n N` recover the given inverse system.
* `core/canonical` owners: the sequential inverse system is a functor
  `OrderDual ℕ+ ⥤ ModuleCat A`; the ambient graded module is carried by
  `DirectSum.Decomposition ℳ` and `SetLike.GradedSMul 𝒜 ℳ`; the quotient-transition maps are the
  canonical maps `AdicCompletion.transitionMap`.
* `bridge/view`: the stagewise graded equivalences from those quotients to the prescribed stages of
  the inverse system, expressed by linear equivalences together with degreewise compatibility and
  commuting quotient squares.

Primitive data are the finite graded stages, the transition maps, and the single realizing graded
module. The quotient identifications and their compatibility are derived API from that owner data,
so this file states the source-facing existential theorem directly rather than introducing a second
public wrapper structure.

Relevant owner declarations sampled for this refinement:
* `OrderDual ℕ+ ⥤ ModuleCat A`
* `AdicCompletion.transitionMap`
* `DirectSum.Decomposition`
* `SetLike.GradedSMul`
* `HomogeneousIdeal.irrelevant`
* `surjective_of_irrelevant_reduceModIdeal_surjective`
-/

local instance : AddAction ℕ ℤ where
  vadd n d := n + d
  zero_vadd := by
    intro d
    change ((0 : ℕ) : ℤ) + d = d
    simp
  add_vadd := by
    intro m n d
    change (((m + n : ℕ) : ℤ) + d) = (m : ℤ) + ((n : ℤ) + d)
    simp [Nat.cast_add, add_assoc]

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (𝒜 : ℕ → Submodule A A) [GradedRing 𝒜]

/-- Lemma 10.98.3 (1): a surjective inverse system of finite graded `A`-modules whose successive
transition kernels are the graded submodules `I^n N_{n + 1}` is realized by one finite graded
`A`-module. -/
-- Proof sketch: choose compatible homogeneous generators in degree `1`, use graded Nakayama to
-- show that each stage is generated in the same degrees, define the `d`th graded piece of the
-- limit module by the stabilized degree-`d` parts, and identify each stage with the quotient by
-- the corresponding power of `I`.
theorem exists_finite_graded_module_realizing_inverse_system_of_graded_ideal_power_quotients
    (I : HomogeneousIdeal 𝒜)
    (hI : I.toIdeal ≤ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, DirectSum.Decomposition (𝒢 n)]
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (h𝒢 :
      ∀ (n : ℕ+) (d : ℤ) {x : G_.obj (OrderDual.toDual (n + 1))},
        x ∈ 𝒢 (n + 1) d →
          ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) x ∈ 𝒢 n d)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1))))) :
    ∃ (N : ModuleCat.{w} A) (ℳ : ℤ → Submodule ℤ N)
      (_ : DirectSum.Decomposition ℳ) (_ : SetLike.GradedSMul 𝒜 ℳ) (_ : Module.Finite A N)
      (e :
        ∀ n : ℕ+,
          (N ⧸ (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A N))) ≃ₗ[A] G_.obj (OrderDual.toDual n)),
        (∀ (n : ℕ+) (d : ℤ) (x : N ⧸ (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A N))),
            e n x ∈ 𝒢 n d ↔
              x ∈
                (ℳ d).map
                  ((Submodule.mkQ (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A N))).restrictScalars
                    ℤ)) ∧
          ∀ n : ℕ+,
            CommSq
              (ModuleCat.ofHom
                (AdicCompletion.transitionMap I.toIdeal N (Nat.le_succ (n : ℕ))))
              (ModuleCat.ofHom (e (n + 1)).toLinearMap)
              (ModuleCat.ofHom (e n).toLinearMap)
              (G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))) := sorry

end
