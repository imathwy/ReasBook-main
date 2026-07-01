import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/- Domain-style sampling for Lemma 8.10.1:
- primary domain: source-facing sites presented by `Precoverage` together with fibred categories and
  strongly cartesian morphisms;
- sampled owner API:
  `CategoryTheory.Precoverage`,
  `CategoryTheory.Precoverage.HasIsos`,
  `CategoryTheory.Functor.IsFibered`,
  `CategoryTheory.Functor.IsStronglyCartesian`;
- best owner abstraction: the source-facing owner here is still `Precoverage`; the site axioms are
  derived typeclass API on that owner, while fibredness and strong cartesianness come from the
  canonical fibered-category owner API on the functor `p`.

Source/core/bridge triage:
- `source-facing`: the inherited covering families `stronglyCartesianLiftPrecoverage J p`;
- `core/canonical`: the four `Precoverage` site-axiom typeclasses and the owner predicates
  `Functor.IsFibered` and `Functor.IsStronglyCartesian`;
- `bridge/view`: no separate bundled "is a site" wrapper is kept, since the textbook sentence is
  carried canonically by the four site-axiom instances on `stronglyCartesianLiftPrecoverage J p`;
  downstream files should use those instances directly.

Primitive-vs-derived split:
- primitive data: a base precoverage `J`, a functor `p : S ⥤ C`, and the defining condition that a
  family in `S` is covering when each arrow is strongly cartesian and its image family is
  `J`-covering;
- derived API: the membership characterization for represented families and the four site-axiom
  instances on the inherited precoverage. -/

/-- Lemma 8.10.1: the inherited precoverage on the total category of a fibred category, whose
covering families are the strongly cartesian families whose images in the base form a covering
family. -/
def stronglyCartesianLiftPrecoverage (J : Precoverage C) (p : S ⥤ C) : Precoverage S where
  coverings x :=
    { R | ∃ (ι : Type (max u₂ v₂)) (X : ι → S) (f : ∀ i, X i ⟶ x),
        R = Presieve.ofArrows X f ∧
          (∀ i, p.IsStronglyCartesian (p.map (f i)) (f i)) ∧
          Presieve.ofArrows (p.obj ∘ X) (fun i ↦ p.map (f i)) ∈ J (p.obj x) }

variable (J : Precoverage C) (p : S ⥤ C)

-- Proof sketch: unfold `stronglyCartesianLiftPrecoverage`. One direction is immediate from the
-- defining existential package. For the converse, rewrite the represented presieve by the given
-- family and read off the strong cartesianness and the covering condition downstairs.
/-- A family belongs to the inherited precoverage exactly when each arrow is strongly cartesian and
its image family is covering in the base precoverage. -/
@[simp]
theorem ofArrows_mem_stronglyCartesianLiftPrecoverage_iff
    {x : S} {ι : Type w} (X : ι → S) (f : ∀ i, X i ⟶ x) :
    Presieve.ofArrows X f ∈ stronglyCartesianLiftPrecoverage J p x ↔
      (∀ i, p.IsStronglyCartesian (p.map (f i)) (f i)) ∧
        Presieve.ofArrows (p.obj ∘ X) (fun i ↦ p.map (f i)) ∈ J (p.obj x) := sorry

-- Proof sketch: verify the four site axioms for the inherited precoverage.
-- Singleton isomorphisms are strongly cartesian, compositions of strongly cartesian arrows stay
-- strongly cartesian, and pullbacks of covering families are obtained from fibred pullbacks and
-- the pullback axiom for the site downstairs.
/-- The inherited precoverage contains singleton isomorphism covering families. -/
instance [J.HasIsos] :
    (stronglyCartesianLiftPrecoverage J p).HasIsos := sorry

-- Proof sketch: use fibred pullbacks over base pullbacks. The pullback axiom downstairs gives the
-- required pullback square of the image family, and fibredness lifts that square to the total
-- category with strongly cartesian comparison maps.
/-- The inherited precoverage admits pullbacks of its covering families. -/
instance [J.HasPullbacks] [p.IsFibered] :
    (stronglyCartesianLiftPrecoverage J p).HasPullbacks := sorry

-- Proof sketch: pull back a strongly cartesian covering family along a map in `S`. Fibredness
-- produces the pullback objects upstairs, their projections remain strongly cartesian, and the
-- image family downstairs is a base change of a `J`-covering family.
/-- The inherited precoverage is stable under base change. -/
instance [J.IsStableUnderBaseChange] [p.IsFibered] :
    (stronglyCartesianLiftPrecoverage J p).IsStableUnderBaseChange := sorry

-- Proof sketch: compose two inherited covering families. Strong cartesianness is preserved by
-- composition, and the image family downstairs is a composite covering family for `J`.
/-- The inherited precoverage is stable under composition of covering families. -/
instance [J.IsStableUnderComposition] :
    (stronglyCartesianLiftPrecoverage J p).IsStableUnderComposition := sorry

end

end CategoryTheory
