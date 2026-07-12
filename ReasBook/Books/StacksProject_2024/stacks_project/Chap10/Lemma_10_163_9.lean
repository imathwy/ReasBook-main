import Mathlib
import StacksProject_2024.Chap10.Definition_10_37_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.Smooth R S] [IsNormalRing R]

/- Domain-style sampling pass:
* primary domain: commutative algebra of smooth ring maps and ascent of normality;
* sampled owner declarations:
  `IsNormalRing`,
  `Algebra.Smooth`,
  `isNormalRing_of_flat_of_fiber`,
  `isRegularRing_of_smooth`,
  `isNormalRing_of_isRegularRing`;
* best owner abstraction: this theorem is a `source-facing` smooth-ascent statement, while the
  canonical owner theorem is `isNormalRing_of_flat_of_fiber`; smoothness and fiber regularity
  should remain derived API rather than being repackaged locally.

Primitive data vs. derived API:
* primitive data: the smooth `R`-algebra structure on `S` and the normal-ring owner `[IsNormalRing R]`;
* derived API: flatness of `R → S`, smoothness of every residue-field fiber by base change,
  regularity of those fibers from `isRegularRing_of_smooth`, and their normality from
  `isNormalRing_of_isRegularRing`.

Layering:
* `source-facing`: `isNormalRing_of_smooth`;
* `core/canonical`: `IsNormalRing`, `Algebra.Smooth`, and `isNormalRing_of_flat_of_fiber`;
* `bridge/view`: smooth base change to `p.asIdeal.Fiber S` and the regular-to-normal bridge on the
  fibers.
-/
-- Proof sketch: smooth algebras are flat, so it is enough to apply the canonical ascent theorem
-- `isNormalRing_of_flat_of_fiber`. Each fiber `κ(𝔭) ⊗[R] S`, formalized as `p.asIdeal.Fiber S`,
-- is smooth over the field `κ(𝔭)` by base change, hence regular by Lemma `10.163.10`, and
-- therefore normal by Lemma `10.157.5`.
/-- Lemma 10.163.9: if `R → S` is smooth and `R` is a normal ring, then `S` is a normal ring. -/
theorem isNormalRing_of_smooth :
    IsNormalRing S := sorry

/-- Smooth algebras over normal base rings are normal. -/
instance : IsNormalRing S :=
  isNormalRing_of_smooth

end
