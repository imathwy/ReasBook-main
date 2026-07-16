import Mathlib
import StacksProject_2024.stacks_project.Chap32.Lemma_32_20_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the scheme gluing infrastructure and local
-- Section 32.20 precedent supplies `FinitePresentationOver`, its base-change functor, and
-- `CategoricalPullback` as the owner for the displayed fibre-product category.

/-- The product of the finite-presentation categories over the punctured local schemes
`U_i = Spec(𝒪_{S,s_i}) ×_S U`. -/
abbrev finitePresentationPuncturedStalkProduct
    {ι : Type u} (S : Scheme.{u}) (U : S.Opens) (s : ι → S) : Type (u + 1) :=
  (i : ι) → FinitePresentationOver (stalkOpenIntersection S U (s i)).toScheme

/-- The product of the finite-presentation categories over the local schemes
`S_i = Spec(𝒪_{S,s_i})`. -/
abbrev finitePresentationStalkProduct
    {ι : Type u} (S : Scheme.{u}) (s : ι → S) : Type (u + 1) :=
  (i : ι) → FinitePresentationOver (Spec (S.presheaf.stalk (s i)))

/-- The restriction functor from finite-presentation schemes over `U` to their family of
restrictions over the punctured local schemes `U_i`. -/
abbrev finitePresentationToPuncturedStalkProduct
    {ι : Type u} (S : Scheme.{u}) (U : S.Opens) (s : ι → S) :
    FinitePresentationOver U.toScheme ⥤
      finitePresentationPuncturedStalkProduct S U s where
  obj X := fun i ↦ FinitePresentationOver.baseChange ((S.fromSpecStalk (s i)) ∣_ U) |>.obj X
  map f := fun i ↦ FinitePresentationOver.baseChange ((S.fromSpecStalk (s i)) ∣_ U) |>.map f

/-- The restriction functor from the product of finite-presentation categories over the stalk
schemes `S_i` to the product over the punctured stalk schemes `U_i`. -/
abbrev finitePresentationStalkProductToPuncturedStalkProduct
    {ι : Type u} (S : Scheme.{u}) (U : S.Opens) (s : ι → S) :
    finitePresentationStalkProduct S s ⥤
      finitePresentationPuncturedStalkProduct S U s where
  obj X := fun i ↦ FinitePresentationOver.baseChange
    (stalkOpenIntersection S U (s i)).ι |>.obj (X i)
  map f := fun i ↦ FinitePresentationOver.baseChange
    (stalkOpenIntersection S U (s i)).ι |>.map (f i)

/-- The displayed fibre-product category of finite-presentation gluing data over `U` and over the
finite family of local schemes `S_i = Spec(𝒪_{S,s_i})`, compared over the punctured local schemes
`U_i`. -/
abbrev finitePresentationFiniteStalkGluingCategory
    {ι : Type u} (S : Scheme.{u}) (U : S.Opens) (s : ι → S) : Type (u + 1) :=
  CategoricalPullback
    (finitePresentationToPuncturedStalkProduct S U s)
    (finitePresentationStalkProductToPuncturedStalkProduct S U s)

/-- Lemma 32.20.5: let `S` be a scheme and let `s_i` be a finite family of pairwise distinct
closed points. If `U = S \ {s_i}` is retrocompact in `S`, then the category of schemes of finite
presentation over `S` is equivalent to the fibre product of the category over `U` and the product
of the categories over `S_i = Spec(𝒪_{S,s_i})`, compared after restriction to the punctured local
schemes `U_i = S_i \ {s_i}`. -/
@[stacks 0E8Q]
theorem finitePresentationOver_equivalence_finitePuncturedStalkGluing
    {ι : Type u} [Finite ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens)
    (hU : (U : Set S) = (Set.range s)ᶜ)
    (hUqc : QuasiCompact U.ι) :
    Nonempty (FinitePresentationOver S ≌
      finitePresentationFiniteStalkGluingCategory S U s) := sorry

end AlgebraicGeometry
