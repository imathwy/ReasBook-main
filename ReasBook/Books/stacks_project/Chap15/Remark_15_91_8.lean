import Mathlib
import stacks_project.Chap10.Lemma_10_97_2
import stacks_project.Chap15.Definition_15_89_1
import stacks_project.Chap15.Lemma_15_90_3
import stacks_project.Chap15.Lemma_15_91_6
import stacks_project.Chap15.Proposition_15_90_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped IdealPowerTorsion

/-
Domain-style sampling:
* primary domain: Beauville-Laszlo glueing pairs for principal-adic completion, with fixed-power
  torsion as a bridge statement;
* sampled owner declarations:
  `IsBeauvilleLaszloGlueingPairAlong`,
  `principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion`,
  `tensorBaseChangeUnitPrimaryComponent_bijective`,
  `Submodule.torsionBy`,
  `principalAdicCompletion`;
* owner abstraction: the chapter-level glueing-pair owner
  `IsBeauvilleLaszloGlueingPairAlong (algebraMap R (principalAdicCompletion f)) f`;
* primitive data: a commutative ring `R`, an element `f : R`, and flatness of
  `R → principalAdicCompletion f`;
* derived API: the induced map on `f ^ n`-torsion, its bijectivity consequences, and the resulting
  Beauville-Laszlo glueing-pair criterion.

Source/core/bridge triage:
* `source-facing`: the fixed-power torsion comparison together with the concluding
  Beauville-Laszlo glueing-pair statement in Remark `15.91.8`;
* `core/canonical`: `IsBeauvilleLaszloGlueingPairAlong`,
  `principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion`, and
  `tensorBaseChangeUnitPrimaryComponent_bijective`;
* `bridge/view`: the restricted completion map between the two torsion submodules.
-/

section

variable {R : Type u} [CommRing R]

-- Proof sketch: if `x` is killed by `f^n` in `R`, then applying the algebra map to the equality
-- `(f^n) * x = 0` shows that the image of `x` is killed by the image of `f^n` in the completion.
/-- The algebra map sends `f^n`-torsion elements of `R` to `f^n`-torsion elements of the
principal adic completion. -/
private theorem completionMap_mem_powTorsion
    (f : R) (n : ℕ) (x : (R[f ^ n] : Submodule R R)) :
    Algebra.linearMap R (principalAdicCompletion f) x ∈
      ((principalAdicCompletion f)[f ^ n] : Submodule R (principalAdicCompletion f)) := sorry

/-- The canonical map from the `f^n`-torsion of `R` to the `f^n`-torsion of its principal adic
completion. -/
abbrev powTorsionToPrincipalAdicCompletion (f : R) (n : ℕ) :
    (R[f ^ n] : Submodule R R) →ₗ[R]
      ((principalAdicCompletion f)[f ^ n] : Submodule R (principalAdicCompletion f)) :=
  ((Algebra.linearMap R (principalAdicCompletion f)).domRestrict
      (R[f ^ n] : Submodule R R)).codRestrict
    ((principalAdicCompletion f)[f ^ n] : Submodule R (principalAdicCompletion f))
    (completionMap_mem_powTorsion f n)

-- Proof sketch: tensor the exact sequence `0 → R[f^n] → R → R` with the flat completion
-- `principalAdicCompletion f`. Flatness preserves exactness, so the tensor product identifies with
-- the kernel of multiplication by `f^n` on the completion. Apply
-- `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective` with
-- `R' = principalAdicCompletion f`, using `principalAdicCompletion_quotientMap_bijective` to
-- discharge the quotient-map hypothesis, to identify `R[f^n]` with that tensor product.
/-- Remark 15.91.8: if the canonical map from `R` to its `(f)`-adic completion is flat, then for
every natural number `n` the induced map `R[f^n] → R^∧[f^n]` is bijective; this source-faithful
statement is generalized from positive `n` by the canonical trivial case `n = 0`. -/
theorem powTorsionToPrincipalAdicCompletion_bijective_of_flat
    (f : R)
    (hflat : (algebraMap R (principalAdicCompletion f)).Flat)
    (n : ℕ) :
    Function.Bijective (powTorsionToPrincipalAdicCompletion f n) := sorry

-- Proof sketch: the chapter owner theorem
-- `principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion`
-- reduces the Beauville-Laszlo condition to bijectivity on `f^∞`-torsion. Lemma `15.90.3`
-- supplies that bijectivity from flatness of the completion map together with the quotient
-- comparison for `(f)`, and Lemma `15.91.1` provides the latter comparison.
/-- Remark 15.91.8: if the canonical map from `R` to its `(f)`-adic completion is flat, then
`(R, f)` is a Beauville-Laszlo glueing pair. -/
theorem isBeauvilleLaszloGlueingPair_of_flat
    (f : R)
    (hflat : (algebraMap R (principalAdicCompletion f)).Flat) :
    IsBeauvilleLaszloGlueingPairAlong (algebraMap R (principalAdicCompletion f)) f := by
  sorry

-- Proof sketch: for a Noetherian ring, Algebra Lemma `10.97.2` gives flatness of the canonical
-- map `R → principalAdicCompletion f`. Applying the previous theorem supplies the bijectivity for
-- each natural number `n`.
/-- Over a Noetherian ring, the map on `f^n`-torsion from `R` to its `(f)`-adic completion is
bijective for every natural number `n`. -/
theorem powTorsionToPrincipalAdicCompletion_bijective_of_isNoetherianRing
    [IsNoetherianRing R] (f : R) (n : ℕ) :
    Function.Bijective (powTorsionToPrincipalAdicCompletion f n) := by
  simpa using powTorsionToPrincipalAdicCompletion_bijective_of_flat f
    (adicCompletion_algebraMap_flat (Ideal.span ({f} : Set R))) n

-- Proof sketch: for Noetherian `R`, Lemma `10.97.2` gives flatness of the completion map, and the
-- previous theorem upgrades this to the canonical Beauville-Laszlo owner statement.
/-- In particular, if `R` is Noetherian, then `(R, f)` is a Beauville-Laszlo glueing pair. -/
theorem isBeauvilleLaszloGlueingPair_of_isNoetherianRing
    [IsNoetherianRing R] (f : R) :
    IsBeauvilleLaszloGlueingPairAlong (algebraMap R (principalAdicCompletion f)) f := by
  simpa using isBeauvilleLaszloGlueingPair_of_flat f
    (adicCompletion_algebraMap_flat (Ideal.span ({f} : Set R)))

end
