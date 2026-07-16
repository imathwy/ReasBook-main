import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `AlgebraicGeometry.IsSmooth` and `AlgebraicGeometry.IsImmersion`; local Chapter 31 precedent
-- uses the project-facing `Smooth f`, explicit commutative triangles `hcomm : i ≫ f = j`, and
-- the regular-immersion classes from `Definition_31_21_1`. Source tag check: the item tag and
-- source URL both give `0693`.

/-- Lemma 31.22.12 (1): in a commutative triangle `Y -i-> X -f-> S` and `Y -j-> S`,
if `f` is smooth, `i` and `j` are immersions, and `i` is a Koszul-regular immersion, then `j` is
a Koszul-regular immersion. -/
@[stacks 0693]
theorem isKoszulRegularImmersion_of_isKoszulRegularImmersion_comp_smooth
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion i] [IsImmersion j] (hcomm : i ≫ f = j) (hf : Smooth f)
    [IsKoszulRegularImmersion i] :
    IsKoszulRegularImmersion j := sorry

/-- Lemma 31.22.12 (2): in a commutative triangle `Y -i-> X -f-> S` and `Y -j-> S`,
if `f` is smooth, `i` and `j` are immersions, and `i` is an `H_1`-regular immersion, then `j` is
an `H_1`-regular immersion. -/
@[stacks 0693]
theorem isH1RegularImmersion_of_isH1RegularImmersion_comp_smooth
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion i] [IsImmersion j] (hcomm : i ≫ f = j) (hf : Smooth f)
    [IsH1RegularImmersion i] :
    IsH1RegularImmersion j := sorry

/-- Lemma 31.22.12 (3): in a commutative triangle `Y -i-> X -f-> S` and `Y -j-> S`,
if `f` is smooth, `i` and `j` are immersions, and `i` is a quasi-regular immersion, then `j` is
a quasi-regular immersion. -/
@[stacks 0693]
theorem isQuasiRegularImmersion_of_isQuasiRegularImmersion_comp_smooth
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion i] [IsImmersion j] (hcomm : i ≫ f = j) (hf : Smooth f)
    [IsQuasiRegularImmersion i] :
    IsQuasiRegularImmersion j := sorry

end AlgebraicGeometry
