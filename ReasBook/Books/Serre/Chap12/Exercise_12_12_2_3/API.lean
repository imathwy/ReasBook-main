import Mathlib

noncomputable section

open scoped Representation

universe u v

namespace Representation

section

variable {G : Type u} [Group G]

/-- The subfield of `ℂ` generated over `ℚ` by the values of the complex character `χ`. -/
abbrev characterField (χ : G → ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range χ)

/-- Helper for Exercise 12-12.2-3: package realizability of the scaled complex character `m • χ`
over the character field of `χ`. -/
private def RealizableOverCharacterField (χ : G → ℂ) (m : ℕ+) : Prop :=
  ∃ (W : Type v) (_ : AddCommGroup W) (_ : Module (characterField χ) W)
    (_ : FiniteDimensional (characterField χ) W)
    (τ : Representation (characterField χ) G W),
    (fun g ↦ algebraMap (characterField χ) ℂ (τ.character g)) =
      (((m : ℕ) : ℂ) • χ)

/-- A complex character has Schur index `m` if `m χ` is realizable over the character field and
`m` is minimal with this property. -/
def HasSchurIndex (χ : G → ℂ) (m : ℕ+) : Prop :=
  RealizableOverCharacterField.{u, v} χ m ∧
    ∀ n : ℕ+, RealizableOverCharacterField.{u, v} χ n → m ≤ n

/-- Unfolding `HasSchurIndex χ m` identifies it with realizability of `m χ` over the character
field of `χ`, together with minimality of the positive integer `m`. -/
theorem hasSchurIndex_iff (χ : G → ℂ) (m : ℕ+) :
    HasSchurIndex.{u, v} χ m ↔
      (∃ (W : Type v) (_ : AddCommGroup W) (_ : Module (characterField χ) W)
        (_ : FiniteDimensional (characterField χ) W)
        (τ : Representation (characterField χ) G W),
        (fun g ↦ algebraMap (characterField χ) ℂ (τ.character g)) =
          (((m : ℕ) : ℂ) • χ)) ∧
        ∀ n : ℕ+, (∃ (W : Type v) (_ : AddCommGroup W) (_ : Module (characterField χ) W)
          (_ : FiniteDimensional (characterField χ) W)
          (τ : Representation (characterField χ) G W),
          (fun g ↦ algebraMap (characterField χ) ℂ (τ.character g)) =
            (((n : ℕ) : ℂ) • χ)) → m ≤ n := by
  -- The public Schur-index API is just a reformulation of the private witness packaging.
  rfl

end

section

variable {K : Type v} [Field K]
variable {H : Type u} [Group H]

/-- Helper for Exercise 12-12.2-3: at the identity element, the one-dimensional representation
attached to `β` acts by the identity map. -/
theorem one_dimensional_representation_map_one
    (β : H →* Kˣ) :
    LinearMap.lsmul K K ((β 1 : Kˣ) : K) = 1 := by
  -- The unit-valued character sends `1` to `1`, so the resulting scalar action is trivial.
  ext
  simp [LinearMap.lsmul_apply]

/-- Helper for Exercise 12-12.2-3: the one-dimensional representation attached to `β` is
multiplicative. -/
theorem one_dimensional_representation_map_mul
    (β : H →* Kˣ) (x y : H) :
    LinearMap.lsmul K K ((β (x * y) : Kˣ) : K) =
      LinearMap.lsmul K K ((β x : Kˣ) : K) *
        LinearMap.lsmul K K ((β y : Kˣ) : K) := by
  -- Composition of scalar-multiplication maps multiplies the underlying scalars.
  ext
  simp [LinearMap.lsmul_apply, mul_comm]

/-- Helper for Exercise 12-12.2-3: the canonical one-dimensional representation attached to a
unit-valued character over `K`. -/
def oneDimensionalRepresentation (β : H →* Kˣ) : Representation K H K where
  toFun h := LinearMap.lsmul K K ((β h : Kˣ) : K)
  map_one' := one_dimensional_representation_map_one β
  map_mul' x y := one_dimensional_representation_map_mul β x y

/-- Helper for Exercise 12-12.2-3: the character of the one-dimensional representation attached
to `β` is just the underlying scalar-valued homomorphism. -/
theorem oneDimensionalRepresentation_character_apply
    (β : H →* Kˣ) (h : H) :
    (oneDimensionalRepresentation β).character h = ((β h : Kˣ) : K) := by
  -- In dimension `1`, scalar multiplication has trace equal to that scalar.
  rw [Representation.character]
  let b := Module.Free.chooseBasis K K
  rw [LinearMap.trace_eq_matrix_trace K b]
  have hmat :
      LinearMap.toMatrix b b (oneDimensionalRepresentation β h) =
        Matrix.diagonal fun _ ↦ ((β h : Kˣ) : K) := by
    -- The chosen basis identifies the action with the `1 × 1` diagonal matrix of `β h`.
    convert (Algebra.toMatrix_lsmul (b := b) (((β h : Kˣ) : K))) using 1
  rw [hmat]
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex K K) = 1 := by
    -- The carrier of the one-dimensional representation has rank `1`.
    rw [← Module.finrank_eq_card_chooseBasisIndex K K]
    rw [Module.finrank_self]
  simp [Matrix.trace, hcard]

end

end Representation
