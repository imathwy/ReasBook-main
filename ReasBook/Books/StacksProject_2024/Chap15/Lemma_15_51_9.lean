import Mathlib
import StacksProject_2024.Chap15.Definition_15_41_1
import StacksProject_2024.Chap10.Lemma_10_43_9
import StacksProject_2024.Chap15.Lemma_15_51_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open IsLocalRing

namespace Algebra

universe u

/- Domain triage:
- primary domain: geometrically reduced algebras over fields and the Chapter 15 formal-fiber
  axioms for field-algebra properties;
- sampled owner declarations:
  `Algebra.IsGeometricallyReduced`,
  `IsRegularRingMap`,
  `RingHom.FaithfullyFlat`,
  `isReduced_of_faithfullyFlat`,
  `FieldAlgebraProperty.HasPropertyA`,
  `FieldAlgebraProperty.HasPropertyB`,
  `FieldAlgebraProperty.HasPropertyC`,
  `FieldAlgebraProperty.HasPropertiesABCDE`,
  `isGeometricallyReduced_iff_of_isSeparable`;
- best owner abstraction: the public owner is the Chapter 15 package
  `FieldAlgebraProperty.HasPropertiesABCDE`, specialized directly to the canonical
  field-algebra predicate `fun k R ↦ fun [Field k] [CommRing R] [Algebra k R] ↦
    IsGeometricallyReduced k R`;
- source/core/bridge triage:
  clauses `(1)` through `(5)` are the source-facing companions, while the chapter-level
  `FieldAlgebraProperty.HasPropertiesABCDE` instance is the core/canonical owner interface.

Primitive data are the ambient field/ring maps and the fiber hypotheses. Reducedness after
tensoring, localization stability, regular/faithfully-flat fiber transfer, and separable-base-field
invariance stay in derived owner API rather than being repackaged by a local wrapper.
-/

/-- The canonical `FieldAlgebraProperty` bridge for geometric reducedness. -/
abbrev IsGeometricallyReducedProperty : FieldAlgebraProperty :=
  fun k R ↦ fun [Field k] [CommRing R] [Algebra k R] ↦ IsGeometricallyReduced k R

-- Proof sketch: a finitely generated field extension is built from a purely transcendental
-- extension and a finite algebraic extension. Polynomial extensions and localizations preserve
-- geometric reducedness, and algebraic field extensions preserve reducedness after tensoring with
-- a geometrically reduced algebra.
/-- Lemma 15.51.9 (1): geometric reducedness is preserved after base change along a finitely
generated field extension. -/
theorem isGeometricallyReduced_baseChange_of_finitelyGeneratedFieldExtension
    {k : Type u} {K : Type u} {R : Type u}
    [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R] [Algebra.EssFiniteType k K]
    [IsGeometricallyReduced k R] :
    IsGeometricallyReduced K (K ⊗[k] R) := sorry

section

variable {k : Type u} {R : Type u} [Field k] [CommRing R] [Algebra k R]

-- Proof sketch: geometric reducedness is defined by reducedness after tensoring with field
-- extensions. Reducedness is a local property of commutative rings, and localizing a
-- geometrically reduced algebra stays geometrically reduced, so the global ring is geometrically
-- reduced exactly when all of its prime localizations are.
/-- Lemma 15.51.9 (2): a Noetherian `k`-algebra is geometrically reduced if and only if all of its
prime localizations are geometrically reduced over `k`. -/
theorem isGeometricallyReduced_iff_forall_localization_atPrime [IsNoetherianRing R] :
    IsGeometricallyReduced k R ↔
      ∀ p : PrimeSpectrum R, IsGeometricallyReduced k (Localization.AtPrime p.asIdeal) := sorry

end

section

variable {A : Type u} {B : Type u} {C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

-- Proof sketch: fix `p : Spec(A)` and base change the regular map `B → C` along `κ(p)`. The
-- induced map on fibers is regular. Since the fiber of `A → B` over `p` is geometrically reduced,
-- its base change to an algebraic closure of `κ(p)` is reduced; then Lemma `15.42.1` applied to
-- the regular map on base-changed fibers shows the corresponding base change of the fiber of
-- `A → C` is reduced, which is exactly geometric reducedness.
/-- Lemma 15.51.9 (3): if `A → B → C` are maps of commutative rings, `A → B` is flat, every fiber
of `A → B` is geometrically reduced, and `B → C` is a regular ring map, then every fiber of
`A → C` is geometrically reduced. -/
theorem fibers_areGeometricallyReduced_of_flat_of_regular [Module.Flat A B]
    [(algebraMap B C).IsRegularRingMap]
    (hAB :
      ∀ p : PrimeSpectrum A, IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber B)) :
    ∀ p : PrimeSpectrum A, IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber C) := sorry

-- Proof sketch: fix `p : Spec(A)` and base change the faithfully flat map `B → C` along `κ(p)`.
-- This gives a faithfully flat map of fiber rings. If the fiber of `A → C` over `p` is
-- geometrically reduced, then after tensoring with an algebraic closure of `κ(p)` the target
-- fiber is reduced. Lemma `10.164.2` descends reducedness along the faithfully flat map of these
-- base-changed fibers, giving geometric reducedness of the fiber of `A → B` over `p`.
/-- Lemma 15.51.9 (4): if `A → B → C` are maps of commutative rings, every fiber of `A → C` is
geometrically reduced, and `B → C` is faithfully flat, then every fiber of `A → B` is
geometrically reduced. -/
theorem fibers_areGeometricallyReduced_of_comp_of_faithfullyFlat
    (hBC_ff : (algebraMap B C).FaithfullyFlat)
    (hAC :
      ∀ p : PrimeSpectrum A, IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber C)) :
    ∀ p : PrimeSpectrum A, IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber B) := sorry

end

section

variable {k : Type u} {k' : Type u} {R : Type u}
variable [Field k] [Field k'] [CommRing R]
variable [Algebra k k'] [Algebra k' R] [Algebra k R] [IsScalarTower k k' R]

-- Proof sketch: this is exactly the separable-base-field invariance of geometric reducedness from
-- Lemma `10.43.9`; apply that result and take the forward implication.
/-- Lemma 15.51.9 (5): if `k' / k` is a separable algebraic field extension and `R` is
geometrically reduced over `k`, then `R` is geometrically reduced over `k'`. -/
theorem isGeometricallyReduced_of_separableAlgebraicExtension [Algebra.IsSeparable k k']
    [IsGeometricallyReduced k R] :
    IsGeometricallyReduced k' R :=
  (isGeometricallyReduced_iff_of_isSeparable : IsGeometricallyReduced k R ↔
    IsGeometricallyReduced k' R).1 inferInstance

-- Proof sketch: this repackages source-facing clause `(5)` as the Chapter 15 axiom `(E)` for the
-- canonical field-algebra property `fun k R ↦ IsGeometricallyReduced k R`.
/-- Lemma 15.51.9 (5), owner-form: geometric reducedness has property `(E)` in the Chapter 15
formal-fiber package. -/
theorem isGeometricallyReduced_hasPropertyE :
    IsGeometricallyReducedProperty.HasPropertyE := by
  refine ⟨?_⟩
  intro k k' R _ _ _ _ _ _ _ _ hR
  exact
    (isGeometricallyReduced_iff_of_isSeparable :
      IsGeometricallyReduced k R ↔ IsGeometricallyReduced k' R).1 hR

end

section

-- Proof sketch: first descend the faithfully flat local map `B → C` to the induced faithfully
-- flat map on closed fibers over the residue field `κ(A)`. Then test geometric reducedness of the
-- source closed fiber by tensoring with arbitrary field extensions of `κ(A)` and descend
-- reducedness along that faithfully flat base change using Lemma `10.164.2`.
/-- Geometric reducedness descends on the closed fiber along a faithfully flat local extension. -/
theorem isGeometricallyReduced_closedFiberDescent
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
    (hBC : RingHom.FaithfullyFlat (algebraMap B C))
    (hC : IsGeometricallyReduced (ResidueField A) ((maximalIdeal A).Fiber C)) :
    IsGeometricallyReduced (ResidueField A) ((maximalIdeal A).Fiber B) := by
  sorry

-- Proof sketch: the five source-facing clauses above match the five fields of the canonical
-- Chapter 15 owner `FieldAlgebraProperty.HasPropertiesABCDE` for the property
-- `fun k R ↦ IsGeometricallyReduced k R`; only property `(B)` needs a symmetry to match the
-- owner's local-to-global orientation.
/-- Lemma 15.51.9 packages geometric reducedness into the canonical Chapter 15 owner for
field-algebra properties satisfying the formal-fiber axioms `(A)` through `(E)`. -/
instance isGeometricallyReduced_hasPropertiesABCDE :
    IsGeometricallyReducedProperty.HasPropertiesABCDE where
  baseChange := by
    intro k R K _ _ _ _ _ _ _ hR
    letI : IsGeometricallyReduced k R := hR
    exact isGeometricallyReduced_baseChange_of_finitelyGeneratedFieldExtension
  localizationCriterion := by
    intro k R _ _ _ _
    simpa using
      (isGeometricallyReduced_iff_forall_localization_atPrime :
        IsGeometricallyReduced k R ↔
          ∀ p : PrimeSpectrum R, IsGeometricallyReduced k (Localization.AtPrime p.asIdeal))
  regularAscent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hAB q
    exact fibers_areGeometricallyReduced_of_flat_of_regular hAB q
  closedFiberDescent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBC hC
    exact isGeometricallyReduced_closedFiberDescent hBC hC
  separableBaseChange := by
    intro k k' R _ _ _ _ _ _ _ _ hR
    exact isGeometricallyReduced_hasPropertyE.separableBaseChange k k' R hR

end

end Algebra
