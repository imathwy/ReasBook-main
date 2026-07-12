import Mathlib
import StacksProject_2024.Chap10.Definition_10_136_1
import StacksProject_2024.Chap10.Definition_10_136_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: relative complete intersections and syntomic morphisms of commutative rings;
- sampled owner declarations:
  `RingHom.Syntomic`,
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection.baseChange`;
- best owner abstraction:
  `Algebra.IsRelativeGlobalCompleteIntersection R S` is the source-facing owner for the algebra,
  while `(algebraMap R S).Syntomic` is the canonical ring-hom owner on the conclusion side;
- primitive vs. derived:
  the relative global complete intersection witness is primitive data in the source-facing class,
  whereas syntomicity is derived API and should be exposed as a theorem under that owner rather
  than as a parallel standalone theorem name.
-/

namespace IsRelativeGlobalCompleteIntersection

namespace PresentationFlatness

variable {n c : ℕ}

/-- Helper for Chap10 Lemma 10 136 13: a finite list built from a `Fin`-indexed family
generates the same ideal as the range of that family. -/
private theorem ideal_ofList_ofFn_eq_span_range {A : Type*} [CommRing A] {c : ℕ}
    (xs : Fin c → A) :
    Ideal.ofList (List.ofFn xs) = Ideal.span (Set.range xs) := by
  -- The two ideals have the same displayed generators.
  rw [Ideal.ofList]
  congr
  ext x
  constructor
  · intro hx
    rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact List.mem_ofFn.mpr ⟨i, rfl⟩

/-- Helper for Chap10 Lemma 10 136 13: the full prefix in a nonempty `Fin`-indexed list is
the whole relation ideal after localization. -/
private theorem fullLocalizedRelationIdeal_eq_map_span_range {n c' : ℕ}
    (f : Fin (c' + 1) → MvPolynomial (Fin n) R)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span (Set.range f))) q
    let A := Localization.AtPrime q'.asIdeal
    Ideal.ofList
        (List.take (((Fin.last c' : Fin (c' + 1)) : ℕ) + 1)
          ((List.ofFn f).map (algebraMap (MvPolynomial (Fin n) R) A))) =
      Ideal.map (algebraMap (MvPolynomial (Fin n) R) A) (Ideal.span (Set.range f)) := by
  -- The last prefix has length `c' + 1`, so it is the full mapped relation list.
  intro q' A
  have htake :
      List.take (((Fin.last c' : Fin (c' + 1)) : ℕ) + 1)
          ((List.ofFn f).map (algebraMap (MvPolynomial (Fin n) R) A)) =
        (List.ofFn f).map (algebraMap (MvPolynomial (Fin n) R) A) := by
    simp
  rw [htake, ← Ideal.map_ofList, ideal_ofList_ofFn_eq_span_range]

end PresentationFlatness

/-- Helper for Chap10 Lemma 10 136 13: a relative global complete intersection algebra is flat
over the base ring. -/
private theorem moduleFlat (hS : IsRelativeGlobalCompleteIntersection R S) :
    Module.Flat R S := by
  -- The intended route is to choose a finite presentation, replace it by its explicit quotient
  -- model, apply Lemma 10.136.12(2) to the full localized relation prefix at each target prime,
  -- and transport flatness back through the presentation quotient equivalence.
  sorry

/-- Helper for Chap10 Lemma 10 136 13: every residue-field fiber of a relative global complete
intersection is a global complete intersection over that residue field. -/
private theorem fiber_isGlobalCompleteIntersection
    (hS : IsRelativeGlobalCompleteIntersection R S) (p : PrimeSpectrum R) :
    IsGlobalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
  -- A subsingleton fiber is covered by the zero-ring convention for global complete intersections.
  by_cases hsub : Subsingleton (p.asIdeal.Fiber S)
  · letI : Subsingleton (p.asIdeal.Fiber S) := hsub
    exact inferInstance
  -- Otherwise the fiber has a prime, so the relative dimension formula applies to the chosen
  -- presentation and becomes the global complete-intersection dimension formula after base change.
  rcases hS.exists_presentation with ⟨n, c, P, hP⟩
  refine ⟨Or.inr ?_⟩
  refine ⟨n, c, P.baseChange p.asIdeal.ResidueField, ?_⟩
  have hp_nonempty : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S)) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mpr (not_subsingleton_iff_nontrivial.mp hsub)
  calc
    ringKrullDim (p.asIdeal.Fiber S) = P.dimension := hP p hp_nonempty
    _ = (P.baseChange p.asIdeal.ResidueField).dimension := by
      simp [Algebra.Presentation.dimension]

-- Proof sketch: a relative global complete intersection is finitely presented by definition, and
-- each fiber is a global complete intersection, hence a local complete intersection. The only new
-- ingredient is flatness, which is obtained from the localized prefix-quotient flatness statement
-- of Lemma `10.136.12 (2)` after choosing a presentation locally at each prime of `S`.
/-- Lemma 10.136.13: a relative global complete intersection `R`-algebra is syntomic over `R`. -/
@[stacks 00SW]
theorem syntomic (hS : IsRelativeGlobalCompleteIntersection R S) :
    (algebraMap R S).Syntomic := by
  -- Assemble syntomicity by filling the three defining components of `RingHom.Syntomic`.
  refine ⟨?_, ?_, ?_⟩
  · -- Flatness is the hard input isolated in the module-flatness helper.
    exact RingHom.flat_algebraMap_iff.mpr (moduleFlat hS)
  · -- The defining presentation witness gives finite presentation of the algebra.
    letI : IsRelativeGlobalCompleteIntersection R S := hS
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  · -- Each fiber is global complete intersection, hence local complete intersection.
    rw [RingHom.HasLocalCompleteIntersectionFibers, toAlgebra_algebraMap]
    intro p
    letI : IsGlobalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
      fiber_isGlobalCompleteIntersection hS p
    exact inferInstance

end IsRelativeGlobalCompleteIntersection

end

end Algebra
