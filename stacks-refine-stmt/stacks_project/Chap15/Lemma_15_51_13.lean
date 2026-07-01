import stacks_project.Chap10.Definition_10_157_1
import stacks_project.Chap15.Lemma_15_51_10

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open IsLocalRing
open scoped TensorProduct

universe u

/- Domain sampling pass:
- primary domain: Chapter 15 field-algebra properties satisfying the formal-fiber axioms,
  specialized to Serre's condition `(R_n)` after finite extensions of the base field;
- sampled owner declarations:
  `SerreConditionR`,
  `serreConditionR_of_flat_of_fiber`,
  `serreConditionR_of_faithfullyFlat`,
  `FieldAlgebraProperty.HasPropertiesABCDE`,
  `FieldAlgebraProperty`;
- best owner abstraction: the source-facing Chapter 15 owner
  `FiniteFieldExtensionSerreConditionRProperty n`, whose primitive data are exactly the
  `SerreConditionR` conditions on the tensor-product base changes `K ⊗[k] A`;
- source/core/bridge triage:
  `FiniteFieldExtensionSerreConditionRProperty n` is `source-facing`,
  `SerreConditionR` on each finite tensor-product base change is `core/canonical`,
  and `FieldAlgebraProperty.HasPropertiesABCDE` is the derived `bridge/view` package of axioms
  `(A)` through `(E)`.

Primitive data are only the predicate saying that every finite field extension `K / k` makes
`K ⊗[k] A` satisfy `SerreConditionR _ n`. The chapter-level `(A)`--`(E)` package is derived API
on top of that source-facing owner, so the file should expose that owner directly instead of
keeping separate one-use closure wrappers.
-/

namespace Algebra

/-- The finite-field-extension form of Serre's condition `(R_n)`, viewed as a Chapter 15
`FieldAlgebraProperty`. -/
abbrev FiniteFieldExtensionSerreConditionRProperty (n : ℕ) : FieldAlgebraProperty :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦
    ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
      SerreConditionR (K ⊗[k] A) n

end Algebra

section

variable {n : ℕ}

-- Proof sketch: fix a finitely generated extension `K / k` and a finite extension `L / K`.
-- Re-express `L ⊗[K] (K ⊗[k] A)` as `L ⊗[k] A`, note that `L / k` is still finite after
-- descending to a finite subextension of the chosen finitely generated extension, and then apply
-- the defining finite-field-extension hypothesis over `k`.
/-- Lemma 15.51.13 (1): the finite-field-extension form of Serre's condition `(R_n)` is preserved
after base change along a finitely generated extension of the ground field. -/
theorem finiteFieldExtensionSerreConditionR_baseChange_of_finitelyGeneratedFieldExtension
    {k : Type u} {K : Type u} {A : Type u}
    [Field k] [Field K] [CommRing A] [Algebra k K] [Algebra k A] [Algebra.EssFiniteType k K]
    (hA : FiniteFieldExtensionSerreConditionRProperty n k A) :
    FiniteFieldExtensionSerreConditionRProperty n K (K ⊗[k] A) := sorry

section

variable {k : Type u} {A : Type u} [Field k] [CommRing A] [Algebra k A]

-- Proof sketch: unfold the source-facing property and apply the prime-local criterion for
-- `SerreConditionR` to each finite tensor-product base change `K ⊗[k] A`.
/-- Lemma 15.51.13 (2): for a Noetherian `k`-algebra `A`, the finite-field-extension form of
Serre's condition `(R_n)` can be checked on the localizations `A_𝔭`. -/
theorem finiteFieldExtensionSerreConditionR_iff_localizationAtPrime [IsNoetherianRing A] :
    FiniteFieldExtensionSerreConditionRProperty n k A ↔
      ∀ p : PrimeSpectrum A,
        FiniteFieldExtensionSerreConditionRProperty n k (Localization.AtPrime p.asIdeal) := sorry

end

section

variable {A : Type u} {B : Type u} {C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]

-- Proof sketch: after any finite residue-field extension of `κ(p)`, apply
-- `serreConditionR_of_flat_of_fiber` to the induced base change of the fiber map. Regularity of
-- the fibers of `B → C` comes from the regular-ring-map hypothesis, so `(R_n)` ascends from the
-- fibers of `A → B` to those of `A → C`.
/-- Lemma 15.51.13 (3): if `A → B → C` are maps of Noetherian rings, `A → B` is flat, every fiber
of `A → B` satisfies the finite-field-extension form of `(R_n)`, and `B → C` is regular, then
every fiber of `A → C` satisfies the same property. -/
theorem fiber_finiteFieldExtensionSerreConditionR_of_regularRingMap [Module.Flat A B]
    [(algebraMap B C).IsRegularRingMap]
    (hfiber :
      ∀ p : PrimeSpectrum A,
        FiniteFieldExtensionSerreConditionRProperty n p.asIdeal.ResidueField (p.asIdeal.Fiber B)) :
    ∀ p : PrimeSpectrum A,
      FiniteFieldExtensionSerreConditionRProperty n p.asIdeal.ResidueField (p.asIdeal.Fiber C) :=
  sorry

end

section

variable {A : Type u} {B : Type u} {C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]

-- Proof sketch: after any finite residue-field extension of `ResidueField A`, the induced map on
-- closed fibers stays faithfully flat. Apply `serreConditionR_of_faithfullyFlat` to descend
-- `(R_n)` from the extended closed fiber over `C` to the corresponding extended closed fiber over
-- `B`.
/-- Lemma 15.51.13 (4): under a faithfully flat local extension on closed fibers, the
finite-field-extension form of Serre's condition `(R_n)` descends from the closed fiber over `C`
to the closed fiber over `B`. -/
theorem closedFiber_finiteFieldExtensionSerreConditionR_of_faithfullyFlat
    (hBC : RingHom.FaithfullyFlat (algebraMap B C))
    (hC :
      FiniteFieldExtensionSerreConditionRProperty n (ResidueField A) ((maximalIdeal A).Fiber C)) :
    FiniteFieldExtensionSerreConditionRProperty n (ResidueField A) ((maximalIdeal A).Fiber B) :=
  sorry

end

end

namespace Algebra

section

variable {n : ℕ}

-- Proof sketch: reduce to the finite separable case by descending the chosen finite extension of
-- the larger base field to a finite subextension, then identify the resulting tensor product with
-- a localization of a finite base change over the original field using Lemma `10.43.8`.
/-- Lemma 15.51.13 (5), owner-form: the Chapter 15 field-algebra property
`P(k → R) := ∀ K / k` finite, `SerreConditionR (K ⊗[k] R) n` has property `(E)`. -/
theorem finiteFieldExtensionSerreConditionR_hasPropertyE :
    (FiniteFieldExtensionSerreConditionRProperty n).HasPropertyE := sorry

-- Proof sketch: property `(A)` writes a finitely generated extension `K / k` as in Lemma
-- `10.45.3`, passes to a smooth `k'`-model of the separable part using Lemma `10.158.10`,
-- ascends `(R_n)` along the resulting smooth map by Lemma `10.163.5`, localizes to the fraction
-- field, and then descends back along the faithfully flat map to `K` using Lemma `10.164.6`.
-- Property `(B)` is the prime-local criterion for `(R_n)`. Property `(C)` applies
-- Lemma `10.163.5` fiberwise after finite residue-field extension. Property `(D)` is the
-- closed-fiber faithfully flat descent statement from Lemma `10.164.6`. Property `(E)` is the
-- separable-base-field reduction recorded in `finiteFieldExtensionSerreConditionR_hasPropertyE`.
/-- Lemma 15.51.13 packages the finite-field-extension form of Serre's condition `(R_n)` into the
canonical owner for field-algebra properties satisfying `(A)` through `(E)`. -/
instance finiteFieldExtensionSerreConditionR_hasPropertiesABCDE :
    (FiniteFieldExtensionSerreConditionRProperty n).HasPropertiesABCDE where
  baseChange := by
    intro k A K _ _ _ _ _ _ _ hA
    exact finiteFieldExtensionSerreConditionR_baseChange_of_finitelyGeneratedFieldExtension hA
  localizationCriterion := by
    intro k A _ _ _ _
    exact finiteFieldExtensionSerreConditionR_iff_localizationAtPrime
  regularAscent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hfiber q
    exact fiber_finiteFieldExtensionSerreConditionR_of_regularRingMap hfiber q
  closedFiberDescent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBC hC
    exact closedFiber_finiteFieldExtensionSerreConditionR_of_faithfullyFlat hBC hC
  separableBaseChange := by
    simpa using finiteFieldExtensionSerreConditionR_hasPropertyE.separableBaseChange

end

end Algebra
