import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

section

variable (R : Type u) [Ring R]

/-- A ring has global dimension at most `n` if every `R`-module has projective dimension at
most `n`. -/
class HasGlobalDimensionLE (n : ℕ) : Prop where
  hasProjectiveDimensionLE (M : ModuleCat.{u} R) : HasProjectiveDimensionLE M n

/-- Definition 10.109.10: a ring has finite global dimension if there is an integer `n` such that
every `R`-module has projective dimension at most `n`, equivalently admits a projective
resolution of length at most `n`. -/
@[stacks 00O6]
class IsFiniteGlobalDimensionRing : Prop where
  exists_bound : ∃ n : ℕ, HasGlobalDimensionLE R n

/-- A global-dimension bound on `R` induces the corresponding projective-dimension bound on every
`R`-module. -/
instance (n : ℕ) [HasGlobalDimensionLE R n] (M : ModuleCat.{u} R) :
    HasProjectiveDimensionLE M n :=
  HasGlobalDimensionLE.hasProjectiveDimensionLE M

/-- The global dimension of a ring with finite global dimension is the least uniform bound on the
projective dimensions of its modules. -/
noncomputable def globalDimension [IsFiniteGlobalDimensionRing R] : ℕ :=
  sInf { n : ℕ | HasGlobalDimensionLE R n }

/-- The global dimension itself is a valid uniform bound on projective dimensions. -/
-- Proof sketch: the defining set of `globalDimension R` is the set of all admissible bounds;
-- finite global dimension gives nonemptiness, and `sInf` belongs to that set in `ℕ`.
theorem hasGlobalDimensionLE_globalDimension [IsFiniteGlobalDimensionRing R] :
    HasGlobalDimensionLE R (globalDimension R) := by
  refine Nat.sInf_mem ?_
  simpa [Set.nonempty_def] using
    (IsFiniteGlobalDimensionRing.exists_bound : ∃ n : ℕ, HasGlobalDimensionLE R n)

/-- A ring of finite global dimension has the canonical bound given by its global dimension. -/
noncomputable instance [IsFiniteGlobalDimensionRing R] :
    HasGlobalDimensionLE R (globalDimension R) :=
  hasGlobalDimensionLE_globalDimension R

/-- Any admissible bound on the projective dimensions of `R`-modules dominates the global
dimension. -/
-- Proof sketch: `globalDimension R` is the infimum of the set of all integers `n` such that
-- `HasGlobalDimensionLE R n`, so every member of that set is at least `globalDimension R`.
theorem globalDimension_le {n : ℕ} [IsFiniteGlobalDimensionRing R] [HasGlobalDimensionLE R n] :
    globalDimension R ≤ n := by
  exact Nat.sInf_le (show n ∈ {m : ℕ | HasGlobalDimensionLE R m} from ‹HasGlobalDimensionLE R n›)

end
