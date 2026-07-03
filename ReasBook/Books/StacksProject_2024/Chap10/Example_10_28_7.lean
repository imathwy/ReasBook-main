import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open Ideal
open scoped ZeroObject

universe u

section

variable {A : Type u} [CommRing A]

/-- Helper for Example 10.28.7: the colon ideal `(I : a)` is the comap of multiplication by `a`
through the quotient map to `A ⧸ I`. -/
private theorem colon_span_singleton_eq_comap_mul_right (I : Ideal A) (a : A) :
    I.colon (span {a}) = Submodule.comap (LinearMap.mulRight A a) I := by
  ext x
  constructor
  · intro hx
    -- Translate colon membership into the concrete condition `x * a ∈ I`.
    change x * a ∈ I
    exact Ideal.mem_colon_span_singleton.mp hx
  · intro hx
    -- Repackage the multiplication condition as membership in the colon ideal.
    change x * a ∈ I at hx
    exact Ideal.mem_colon_span_singleton.mpr hx

/-- Elements of the colon ideal become zero in `A ⧸ I` after multiplication by `a`. -/
-- Proof sketch: if `x ∈ I : (a)`, then `x * a ∈ I` by `Ideal.mem_colon_span_singleton`; applying
-- the quotient map `A → A ⧸ I` shows that the class of `x * a` vanishes in `A ⧸ I`.
private theorem colon_span_singleton_le_comap_mul_right (I : Ideal A) (a : A) :
    I.colon (span {a}) ≤ Submodule.comap (LinearMap.mulRight A a) I := by
  -- This is the monotone form of the colon/comap identification used to define the quotient map.
  rw [colon_span_singleton_eq_comap_mul_right I a]

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
  by
    rintro _ ⟨y, rfl⟩
    refine Quotient.inductionOn' y ?_
    intro x
    rw [LinearMap.mem_ker]
    -- On representatives, the composite is the class of `x * a` modulo `I ⊔ (a)`.
    simp only [quotient_colon_span_singleton_mul, quotient_sup_span_singleton_factor]
    -- That class vanishes because `x * a` already lies in the principal ideal `(a)`.
    exact Ideal.Quotient.eq_zero_iff_mem.mpr <|
      Submodule.mem_sup.2 ⟨0, by simp, x * a, Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩, by simp⟩

/-- Helper for Example 10.28.7: any class in `A ⧸ I` that dies in `A ⧸ (I + (a))` comes from a
class in `A ⧸ (I : a)` by multiplication by `a`. -/
private theorem quotient_sup_span_singleton_ker_le_range (I : Ideal A) (a : A) :
    LinearMap.ker (quotient_sup_span_singleton_factor I a).hom ≤
      LinearMap.range (quotient_colon_span_singleton_mul I a).hom := by
  intro y hy
  rcases Ideal.Quotient.mk_surjective y with ⟨x, rfl⟩
  have hy_zero : (quotient_sup_span_singleton_factor I a).hom (Ideal.Quotient.mk I x) = 0 :=
    LinearMap.mem_ker.mp hy
  have hy_mem : x ∈ I ⊔ span {a} := by
    -- Read the kernel condition as membership of a representative in `I ⊔ (a)`.
    simpa [quotient_sup_span_singleton_factor, Ideal.Quotient.eq_zero_iff_mem] using hy_zero
  obtain ⟨u, huI, v, hv, huv⟩ := Submodule.mem_sup.mp hy_mem
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hv
  refine ⟨Ideal.Quotient.mk (I.colon (span {a})) b, ?_⟩
  -- The principal part `v = b * a` produces the desired preimage, while the `u ∈ I` part dies.
  change Ideal.Quotient.mk I (b * a) = Ideal.Quotient.mk I x
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← huv, hb]
  have hsub : v - (u + v) = -u := by
    ring
  rw [hsub]
  exact I.neg_mem huI

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
    (quotient_colon_span_singleton_shortComplex I a).ShortExact := by
  have hExact_hom :
      Function.Exact (quotient_colon_span_singleton_mul I a).hom
        (quotient_sup_span_singleton_factor I a).hom := by
    refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
    · apply LinearMap.ext
      intro x
      exact LinearMap.mem_ker.mp <|
        quotient_colon_span_singleton_range_le_ker I a ⟨x, rfl⟩
    · exact quotient_sup_span_singleton_ker_le_range I a
  have hInj :
      Function.Injective (quotient_colon_span_singleton_mul I a).hom := by
    -- Injectivity is the kernel computation for the quotient-by-colon map.
    have hker :
        LinearMap.ker (quotient_colon_span_singleton_mul I a).hom =
          (Submodule.comap (LinearMap.mulRight A a) I).map (I.colon (span {a})).mkQ := by
      simpa [quotient_colon_span_singleton_mul] using
        (Submodule.ker_mapQ (p := I.colon (span {a})) (q := I)
          (f := LinearMap.mulRight A a) (h := colon_span_singleton_le_comap_mul_right I a))
    exact LinearMap.ker_eq_bot.mp <| by
      rw [hker, colon_span_singleton_eq_comap_mul_right, Submodule.mkQ_map_self]
  have hSurj :
      Function.Surjective (quotient_sup_span_singleton_factor I a).hom := by
    -- The quotient map to a larger ideal is always surjective.
    simpa [quotient_sup_span_singleton_factor] using
      (Ideal.Quotient.factor_surjective (le_sup_left : I ≤ I ⊔ span {a}))
  -- Assemble exactness, injectivity, and surjectivity into short exactness.
  refine ModuleCat.shortComplex_shortExact (quotient_colon_span_singleton_shortComplex I a) ?_ ?_ ?_
  · simpa using hExact_hom
  · simpa using hInj
  · simpa using hSurj

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
