import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` found the categorical owner
-- `CategoryTheory.IsFinitelyPresentable`; local Chapter 28 precedent represents "directed
-- colimit with surjective transition maps" as an `IsColimit` cocone over a filtered index
-- category, with categorical epimorphisms for the transition maps. Mathlib/project search found
-- no separate `X.Algebras` owner, so commutative `O_X`-algebras are represented as commutative
-- monoid objects in the monoidal category `X.Modules`.

/-- Lemma 28.22.12: let `X` be a quasi-compact and quasi-separated scheme, and let `A` be a finite
quasi-coherent `\mathcal O_X`-algebra. Then `A` is a directed colimit of finite and finitely
presented quasi-coherent `\mathcal O_X`-algebras whose transition maps are surjective.

Here `\mathcal O_X`-algebras are represented as commutative monoid objects of `X.Modules`;
"finite" and "quasi-coherent" are imposed on the underlying module object, while "finitely
presented algebra" is the categorical finite-presentability predicate on the algebra object. -/
@[stacks 086N]
theorem exists_filteredSystem_finite_finitelyPresentable_algebra_colimit
    {X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    [MonoidalCategory X.Modules] [BraidedCategory X.Modules]
    (A : CommMon X.Modules) [A.X.IsFiniteType] [A.X.IsQuasicoherent] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
      ∃ (B : I ⥤ CommMon X.Modules) (φ : B ⟶ (Functor.const I).obj A),
        ∃ (_ : IsColimit (Cocone.mk A φ))
          (_ : ∀ i : I, (B.obj i).X.IsFiniteType)
          (_ : ∀ i : I, (B.obj i).X.IsQuasicoherent)
          (_ : ∀ i : I, IsFinitelyPresentable (B.obj i)),
          ∀ {i i' : I} (f : i ⟶ i'), Epi (B.map f) := sorry

end AlgebraicGeometry.Scheme.Modules
