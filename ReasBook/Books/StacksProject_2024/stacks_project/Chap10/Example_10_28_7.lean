import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open Ideal
open scoped ZeroObject

universe u

section

variable {A : Type u} [CommRing A]

/-- Elements of the colon ideal become zero in `A ⧸ I` after multiplication by `a`. -/
-- Proof sketch: if `x ∈ I : (a)`, then `x * a ∈ I` by `Ideal.mem_colon_span_singleton`; applying
-- the quotient map `A → A ⧸ I` shows that the class of `x * a` vanishes in `A ⧸ I`.
private theorem colon_span_singleton_le_comap_mul_right (I : Ideal A) (a : A) :
    I.colon (span {a}) ≤ Submodule.comap (LinearMap.mulRight A a) I := sorry

/-- The map `A/(I : a) → A/I` induced by multiplication by `a`. -/
private def quotient_colon_span_singleton_mul (I : Ideal A) (a : A) :
    ModuleCat.of A (A ⧸ I.colon (span {a})) ⟶ ModuleCat.of A (A ⧸ I) :=
  ModuleCat.ofHom <|
    Submodule.mapQ (I.colon (span {a})) I (LinearMap.mulRight A a)
      (colon_span_singleton_le_comap_mul_right I a)

private abbrev quotient_sup_span_singleton_factor (I : Ideal A) (a : A) :
    ModuleCat.of A (A ⧸ I) ⟶ ModuleCat.of A (A ⧸ (I ⊔ span {a})) :=
  ModuleCat.ofHom <| (Ideal.Quotient.factorₐ A (le_sup_left : I ≤ I ⊔ span {a})).toLinearMap

/-- The image of `A/(I : a) → A/I` lands in the kernel of `A/I → A/(I + (a))`. -/
-- Proof sketch: on a class represented by `x`, the composite is the class of `x * a`; since
-- `x * a ∈ (a) ≤ I + (a)`, that class is zero in the quotient by `I + (a)`.
private theorem quotient_colon_span_singleton_range_le_ker (I : Ideal A) (a : A) :
    LinearMap.range (quotient_colon_span_singleton_mul I a).hom ≤
      LinearMap.ker (quotient_sup_span_singleton_factor I a).hom :=
  sorry

/-- The short complex underlying the standard sequence
`0 → A/(I : a) → A/I → A/(I, a) → 0`. -/
def quotient_colon_span_singleton_shortComplex (I : Ideal A) (a : A) :
    ShortComplex (ModuleCat A) :=
  ShortComplex.moduleCatMkOfKerLERange
    (quotient_colon_span_singleton_mul I a)
    (quotient_sup_span_singleton_factor I a)
    (quotient_colon_span_singleton_range_le_ker I a)

/-- Example 10.28.7 (first assertion): there is a short exact sequence
`0 → A/(I : a) → A/I → A/(I, a) → 0`, where the first arrow is given by
multiplication by `a`. -/
theorem quotient_colon_span_singleton_shortExact (I : Ideal A) (a : A) :
    (quotient_colon_span_singleton_shortComplex I a).ShortExact := sorry

/-- Example 10.28.7 (second assertion): if a property of `A`-modules is closed under
isomorphisms, closed under extensions, and holds for the zero module, then the ideals `I` such
that `A ⧸ I` has that property form an Oka family. -/
-- Proof sketch: for the Oka step, apply `P.IsClosedUnderExtensions` to the standard short exact
-- sequence from `quotient_colon_span_singleton_shortExact I a`, whose end terms are
-- `A/(I : a)` and `A/(I + (a))`. For the top ideal, use the canonical `ContainsZero` instance.
theorem objectProperty_quotient_ideal_isOka (P : ObjectProperty (ModuleCat A))
    [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions] [P.ContainsZero] :
    Ideal.IsOka (fun I : Ideal A ↦ P (ModuleCat.of A (A ⧸ I))) where
  top := by
    simpa using
      P.prop_of_isZero (ModuleCat.isZero_of_subsingleton (ModuleCat.of A (A ⧸ (⊤ : Ideal A))))
  oka {I} {a} hsup hcolon :=
    P.prop_X₂_of_shortExact (quotient_colon_span_singleton_shortExact I a) hcolon hsup

end
