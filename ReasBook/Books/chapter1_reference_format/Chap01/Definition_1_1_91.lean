import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Nat

section PrimitiveRootsMod

variable {n : ℕ} [NeZero n] (g : (ZMod n)ˣ)

/- Definition 1.1.91: a primitive root modulo `n` is an element `g` of the unit group
`(ZMod n)ˣ = (ℤ/nℤ)∗` whose order is `φ n`; in Lean this is the canonical predicate
`IsPrimitiveRoot g (φ n)`. The recurring textbook operator `ind_g a` is then the discrete
logarithm of `a` with respect to that primitive root, taken modulo `φ n`. -/
#check IsPrimitiveRoot g (φ n)

namespace IsPrimitiveRoot

variable {g}

/-- Helper for Definition 1.1.91: the powers of a primitive root with exponents in
`Fin (φ n)` are pairwise distinct. -/
theorem pow_fin_injective (hg : IsPrimitiveRoot g (φ n)) :
    Function.Injective (fun l : Fin (φ n) ↦ g ^ (l : ℕ)) := by
  intro i j hij
  -- Compare bounded exponents through `IsPrimitiveRoot.pow_inj` on their natural values.
  apply Fin.ext
  exact hg.pow_inj i.is_lt j.is_lt hij

/-- Helper for Definition 1.1.91: the bounded power map of a primitive root is a bijection onto
the unit group modulo `n`. -/
theorem pow_fin_bijective (hg : IsPrimitiveRoot g (φ n)) :
    Function.Bijective (fun l : Fin (φ n) ↦ g ^ (l : ℕ)) := by
  -- In a finite type, injectivity plus matching cardinalities gives bijectivity.
  refine (Fintype.bijective_iff_injective_and_card _).2 ?_
  refine ⟨hg.pow_fin_injective, ?_⟩
  simp [ZMod.card_units_eq_totient]

/-- Helper for Definition 1.1.91: every unit modulo `n` is a bounded power of a primitive root. -/
theorem exists_pow_eq_fin (hg : IsPrimitiveRoot g (φ n)) (a : (ZMod n)ˣ) :
    ∃ l : Fin (φ n), a = g ^ (l : ℕ) := by
  -- Surjectivity of the bounded power map produces the required exponent.
  rcases hg.pow_fin_bijective.surjective a with ⟨l, hl⟩
  exact ⟨l, hl.symm⟩

/-- The discrete logarithm of a unit modulo `n` with respect to a primitive root `g` is the unique
exponent in `Fin (φ n)` whose power of `g` is that unit; this encodes the textbook bound
`0 ≤ l ≤ φ(n) - 1`. -/
-- Proof sketch: the bounded power map `l ↦ g ^ l` from `Fin (φ n)` into `(ZMod n)ˣ` is injective
-- by `IsPrimitiveRoot.pow_inj`, hence bijective because both finite types have cardinality `φ n`.
-- Existence and uniqueness of the discrete logarithm then come from that bijection.
theorem existsUnique_log (hg : IsPrimitiveRoot g (φ n)) (a : (ZMod n)ˣ) :
    ∃! l : Fin (φ n), a = g ^ (l : ℕ) := by
  rcases hg.exists_pow_eq_fin a with ⟨l, hl⟩
  refine ExistsUnique.intro l hl ?_
  intro m hm
  -- Any two bounded exponents with the same power must agree by injectivity.
  apply hg.pow_fin_injective
  calc
    g ^ (m : ℕ) = a := hm.symm
    _ = g ^ (l : ℕ) := hl

/-- The canonical bounded discrete logarithm of a unit modulo `n` with respect to a primitive
root `g`. -/
noncomputable def log (hg : IsPrimitiveRoot g (φ n)) (a : (ZMod n)ˣ) : Fin (φ n) :=
  Classical.choose (ExistsUnique.exists (hg.existsUnique_log a))

/-- The same discrete logarithm, viewed in `ZMod (φ n)` for additive arithmetic on exponents:
the textbook index `ind_g a`. -/
abbrev index (hg : IsPrimitiveRoot g (φ n)) (a : (ZMod n)ˣ) : ZMod (φ n) :=
  hg.log a

/-- Evaluating the primitive root at its discrete logarithm recovers the original unit. -/
theorem pow_log (hg : IsPrimitiveRoot g (φ n)) (a : (ZMod n)ˣ) :
    a = g ^ (hg.log a : ℕ) := by
  simpa [log] using
    (Classical.choose_spec (ExistsUnique.exists (hg.existsUnique_log a)))

/-- A bounded exponent is the discrete logarithm of a unit exactly when it raises `g` to that
unit. -/
theorem log_eq_iff (hg : IsPrimitiveRoot g (φ n)) (a : (ZMod n)ˣ) (l : Fin (φ n)) :
    hg.log a = l ↔ a = g ^ (l : ℕ) := by
  constructor
  · intro h
    simpa [h] using hg.pow_log a
  · intro hl
    exact ExistsUnique.unique (hg.existsUnique_log a) (hg.pow_log a) hl

/-- The discrete logarithm of `g ^ l` is `l`. -/
theorem log_pow (hg : IsPrimitiveRoot g (φ n)) (l : Fin (φ n)) :
    hg.log (g ^ (l : ℕ)) = l :=
  (hg.log_eq_iff (g ^ (l : ℕ)) l).2 rfl

end IsPrimitiveRoot

end PrimitiveRootsMod

notation:max "ind_{" hg "} " a:arg => IsPrimitiveRoot.index hg a

section PrimitiveRootsModNotation

variable {n : ℕ} [NeZero n] {g : (ZMod n)ˣ} {a : (ZMod n)ˣ}
variable {hg : IsPrimitiveRoot g (φ n)}

/- The textbook index operator `ind_g a` is represented by the notation `ind_{hg} a`,
where `hg` records the primitive-root hypothesis needed to make that index canonical in Lean. -/
#check ind_{hg} a

end PrimitiveRootsModNotation
