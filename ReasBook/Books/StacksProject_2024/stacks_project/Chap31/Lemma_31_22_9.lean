import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `AlgebraicGeometry.IsSmooth` and `AlgebraicGeometry.IsImmersion`; local Chapter 31 precedent
-- uses `Smooth f`, `IsImmersion`, and the regular immersion classes from
-- `Definition_31_21_1`. Source tag check: the item tag and source URL both give `067S`.

/-- Lemma 31.22.9 (1): in a commutative triangle `Y -i-> X -f-> S` and `Y -j-> S`,
if `f` is smooth, `i` and `j` are immersions, and `j` is a regular immersion, then `i` is a
regular immersion. -/
@[stacks 067S]
theorem isRegularImmersion_of_isRegularImmersion_over_smooth
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion i] [IsImmersion j] (hcomm : i ≫ f = j) (hf : Smooth f)
    [IsRegularImmersion j] :
    IsRegularImmersion i := sorry

/-- Lemma 31.22.9 (2): in a commutative triangle `Y -i-> X -f-> S` and `Y -j-> S`,
if `f` is smooth, `i` and `j` are immersions, and `j` is a Koszul-regular immersion, then `i` is
a Koszul-regular immersion. -/
@[stacks 067S]
theorem isKoszulRegularImmersion_of_isKoszulRegularImmersion_over_smooth
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion i] [IsImmersion j] (hcomm : i ≫ f = j) (hf : Smooth f)
    [IsKoszulRegularImmersion j] :
    IsKoszulRegularImmersion i := sorry

/-- Lemma 31.22.9 (3): in a commutative triangle `Y -i-> X -f-> S` and `Y -j-> S`,
if `f` is smooth, `i` and `j` are immersions, and `j` is an `H_1`-regular immersion, then `i` is
an `H_1`-regular immersion. -/
@[stacks 067S]
theorem isH1RegularImmersion_of_isH1RegularImmersion_over_smooth
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion i] [IsImmersion j] (hcomm : i ≫ f = j) (hf : Smooth f)
    [IsH1RegularImmersion j] :
    IsH1RegularImmersion i := sorry

/-- Lemma 31.22.9 (4): in a commutative triangle `Y -i-> X -f-> S` and `Y -j-> S`,
if `f` is smooth, `i` and `j` are immersions, and `j` is a quasi-regular immersion, then `i` is
a quasi-regular immersion. -/
@[stacks 067S]
theorem isQuasiRegularImmersion_of_isQuasiRegularImmersion_over_smooth
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion i] [IsImmersion j] (hcomm : i ≫ f = j) (hf : Smooth f)
    [IsQuasiRegularImmersion j] :
    IsQuasiRegularImmersion i := sorry

end AlgebraicGeometry
