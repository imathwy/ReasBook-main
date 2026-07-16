import Mathlib

open Polynomial

universe u

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: take the canonical extension `L := P.SplittingField`; then
-- `SplittingField.splits P` shows that `P` splits after mapping coefficients into `L`.
/-- Theorem 1.4.39: every polynomial over a field splits over some field extension, hence in
particular every nonconstant polynomial does. -/
theorem exists_field_extension_where_polynomial_splits {K : Type u} [Field K] (P : K[X]) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), (P.map (algebraMap K L)).Splits := by
  exact ⟨P.SplittingField, inferInstance, inferInstance, SplittingField.splits P⟩
