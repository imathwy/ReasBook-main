import Mathlib
import StacksProject_2024.Chap31.Definition_31_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {S : ShortComplex X.Modules}

-- Semantic recall: `lean_leansearch` surfaced the module-level exact-sequence owner
-- `associatedPrimes.subset_union_of_exact`, and Chapter 10 provides the matching weak-assassin
-- owner `weaklyAssociatedPrimes.subset_union_of_exact`. The source-facing scheme statement stays
-- on the existing Chapter 31 owner `weakAss`; although the source applies it to quasi-coherent
-- modules, the stalkwise weak-assassin owner and the short-exact input are already defined for an
-- arbitrary short complex in `X.Modules`.

/-- Lemma 31.5.4 (1): for a short exact sequence of `\mathcal O_X`-modules on a scheme `X`, every
weakly associated point of the middle term is weakly associated to the left term or to the right
term. The source's quasi-coherent case is a specialization of this scheme-module statement. -/
theorem weakAss_middle_subset_union_of_shortExact
    (hS : S.ShortExact) :
    S.X₂.weakAss ⊆ S.X₁.weakAss ∪ S.X₃.weakAss := sorry

/-- Pointwise form of `weakAss_middle_subset_union_of_shortExact`. -/
theorem mem_weakAss_left_or_right_of_mem_middle_of_shortExact
    (hS : S.ShortExact) {x : X} (hx : x ∈ S.X₂.weakAss) :
    x ∈ S.X₁.weakAss ∨ x ∈ S.X₃.weakAss :=
  weakAss_middle_subset_union_of_shortExact hS hx

/-- Lemma 31.5.4 (2): for a short exact sequence of `\mathcal O_X`-modules on a scheme `X`, every
weakly associated point of the left term is weakly associated to the middle term. The source's
quasi-coherent case is a specialization of this scheme-module statement. -/
theorem weakAss_left_subset_of_shortExact
    (hS : S.ShortExact) :
    S.X₁.weakAss ⊆ S.X₂.weakAss := sorry

/-- Pointwise form of `weakAss_left_subset_of_shortExact`. -/
theorem mem_weakAss_middle_of_mem_left_of_shortExact
    (hS : S.ShortExact) {x : X} (hx : x ∈ S.X₁.weakAss) :
    x ∈ S.X₂.weakAss :=
  weakAss_left_subset_of_shortExact hS hx

end AlgebraicGeometry.Scheme.Modules
