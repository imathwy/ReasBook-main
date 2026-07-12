import StacksProject_2024.Chap29.Definition_29_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` pointed to the canonical affine-localization / open-restriction
-- API around `basicOpenIsoSpecAway`, `Spec.map`, and scheme restriction `f ∣_ U`.
-- The birational owner is the chapter-local morphism predicate `IsBirational` from
-- `Definition_29_50_1`, while the
-- “isomorphism over an open” clauses are stated directly by the canonical restriction morphism to
-- the preimage open.

section FirstExample

variable (k : Type u) [Field k]

/-- The variables `x` and `y_α` used in the first ring of Example 29.50.4. -/
abbrev example29504FirstVars :=
  Unit ⊕ k

/-- The polynomial ring `k[x]` from the first example of Example 29.50.4. -/
abbrev example29504FirstA :=
  Polynomial k

/-- The ambient polynomial ring before quotienting by the relations of Example 29.50.4. -/
abbrev example29504FirstAmbient :=
  MvPolynomial (example29504FirstVars k) k

/-- The distinguished variable `x` in the ambient ring of Example 29.50.4. -/
abbrev example29504FirstX : example29504FirstAmbient k :=
  MvPolynomial.X (Sum.inl ())

/-- The variable `y_α` in the ambient ring of Example 29.50.4. -/
abbrev example29504FirstY (a : k) : example29504FirstAmbient k :=
  MvPolynomial.X (Sum.inr a)

/-- The ideal `((x - α) y_α, y_α y_β)` defining the quotient ring `B` in the first example of
Example 29.50.4. -/
def example29504FirstIdeal : Ideal (example29504FirstAmbient k) :=
  Ideal.span
    ({f |
        (∃ a : k, f = (example29504FirstX k - MvPolynomial.C a) * example29504FirstY k a) ∨
          ∃ a b : k, f = example29504FirstY k a * example29504FirstY k b} :
      Set (example29504FirstAmbient k))

/-- The quotient ring
`k[x, {y_α}_{α ∈ k}] / ((x - α) y_α, y_α y_β)` from Example 29.50.4. -/
abbrev example29504FirstB :=
  example29504FirstAmbient k ⧸ example29504FirstIdeal k

/-- The canonical ring map `A = k[x] → B` sending `x` to the class of `x`. -/
abbrev example29504FirstInclusion : example29504FirstA k →+* example29504FirstB k :=
  Polynomial.eval₂RingHom
    (algebraMap k (example29504FirstB k))
    (Ideal.Quotient.mk _ (example29504FirstX k))

/-- The auxiliary polynomial map sending `x` to `X` and every `y_α` to `0`. -/
def example29504FirstRetractionAux :
    example29504FirstAmbient k →+* example29504FirstA k :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i ↦ Sum.elim (fun _ ↦ Polynomial.X) (fun _ ↦ 0) i)

/-- The defining relations of `B` vanish under the map setting all `y_α` equal to `0`. -/
theorem example29504FirstIdeal_le_kerRetractionAux :
    example29504FirstIdeal k ≤ RingHom.ker (example29504FirstRetractionAux k) := by
  refine Ideal.span_le.2 ?_
  rintro x (⟨a, rfl⟩ | ⟨a, b, rfl⟩)
  · simp [example29504FirstRetractionAux, example29504FirstX, example29504FirstY, RingHom.mem_ker]
  · simp [example29504FirstRetractionAux, example29504FirstY, RingHom.mem_ker]

/-- The retraction `B → A` setting all `y_α` equal to `0`. -/
abbrev example29504FirstRetraction : example29504FirstB k →+* example29504FirstA k :=
  Ideal.Quotient.lift
    (example29504FirstIdeal k)
    (example29504FirstRetractionAux k)
    (example29504FirstIdeal_le_kerRetractionAux k)

/-- The affine scheme `Spec(A)` from the first example of Example 29.50.4. -/
abbrev example29504FirstAScheme : Scheme :=
  Spec (CommRingCat.of (example29504FirstA k))

/-- The affine scheme `Spec(B)` from the first example of Example 29.50.4. -/
abbrev example29504FirstBScheme : Scheme :=
  Spec (CommRingCat.of (example29504FirstB k))

/-- The morphism `Spec(B) → Spec(A)` induced by the inclusion `A ⊂ B`. -/
abbrev example29504FirstSpecBToA :
    example29504FirstBScheme k ⟶ example29504FirstAScheme k :=
  Spec.map (CommRingCat.ofHom (example29504FirstInclusion k))

/-- The morphism `Spec(A) → Spec(B)` induced by the retraction `B → A`. -/
abbrev example29504FirstSpecAToB :
    example29504FirstAScheme k ⟶ example29504FirstBScheme k :=
  Spec.map (CommRingCat.ofHom (example29504FirstRetraction k))

/-- The retraction `B → A` is a left inverse to the inclusion `A → B`. -/
theorem example29504FirstRetraction_leftInverse :
    Function.LeftInverse
      (example29504FirstRetraction k)
      (example29504FirstInclusion k) := sorry

variable [Infinite k]

/-- Example 29.50.4: in the first explicit construction over an infinite field `k`, the affine
schemes `Spec(A)` and `Spec(B)` are connected by a birational morphism `Spec(A) → Spec(B)`. -/
theorem example29504FirstSpecAToB_isBirational
    [Finite (irreducibleComponents (example29504FirstAScheme k))]
    [Finite (irreducibleComponents (example29504FirstBScheme k))] :
    IsBirational (example29504FirstSpecAToB k) := sorry

/-- In the first example of Example 29.50.4, the opposite morphism `Spec(B) → Spec(A)` is also
birational. -/
theorem example29504FirstSpecBToA_isBirational
    [Finite (irreducibleComponents (example29504FirstBScheme k))]
    [Finite (irreducibleComponents (example29504FirstAScheme k))] :
    IsBirational (example29504FirstSpecBToA k) := sorry

/-- In the first example of Example 29.50.4, the morphism `Spec(B) → Spec(A)` is not an
isomorphism over any nonempty open subset of `Spec(A)`. -/
theorem example29504FirstSpecBToA_not_isIsoOverAnyOpen
    (U : (example29504FirstAScheme k).Opens) (hU : Nonempty U) :
    ¬ IsIso (example29504FirstSpecBToA k ∣_ U) := sorry

/-- In the first example of Example 29.50.4, the morphism `Spec(A) → Spec(B)` is not an
isomorphism over any nonempty open subset of `Spec(B)`. -/
theorem example29504FirstSpecAToB_not_isIsoOverAnyOpen
    (U : (example29504FirstBScheme k).Opens) (hU : Nonempty U) :
    ¬ IsIso (example29504FirstSpecAToB k ∣_ U) := sorry

end FirstExample

section SecondExample

/-- The target affine scheme `Spec(A)` in the second example of Example 29.50.4. -/
abbrev example29504SecondTargetScheme (A : Type u) [CommRing A] : Scheme :=
  Spec (CommRingCat.of A)

/-- The source affine scheme `Spec(S⁻¹A)` in the second example of Example 29.50.4. -/
abbrev example29504SecondSourceScheme (A : Type u) [CommRing A] (S : Submonoid A) : Scheme :=
  Spec (CommRingCat.of (Localization S))

/-- The localization morphism `Spec(S⁻¹A) → Spec(A)` from the second example of
Example 29.50.4. -/
abbrev example29504SecondLocalizationMorphism
    (A : Type u) [CommRing A] (S : Submonoid A) :
    example29504SecondSourceScheme A S ⟶ example29504SecondTargetScheme A :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization S)))

variable (A : Type u) [CommRing A] [IsDomain A]

/-- In the second example of Example 29.50.4, the localization morphism `Spec(S⁻¹A) → Spec(A)`
is birational when `0 ∉ S`. -/
theorem example29504SecondLocalization_isBirational
    (S : Submonoid A) (h0 : (0 : A) ∉ S)
    [Finite (irreducibleComponents (example29504SecondSourceScheme A S))]
    [Finite (irreducibleComponents (example29504SecondTargetScheme A))] :
    IsBirational (example29504SecondLocalizationMorphism A S) := sorry

/-- If the localization morphism `Spec(S⁻¹A) → Spec(A)` from the second example of
Example 29.50.4 is an isomorphism over some nonempty open of `Spec(A)`, then every element of `S`
becomes invertible in a principal localization `A_a`. -/
theorem example29504Second_exists_principalLocalization_of_exists_isIsoOverOpen
    (S : Submonoid A)
    (hU :
      ∃ U : (example29504SecondTargetScheme A).Opens, Nonempty U ∧
        IsIso (example29504SecondLocalizationMorphism A S ∣_ U)) :
    ∃ a : A, ∀ s : S, IsUnit (algebraMap A (Localization.Away a) s.1) := sorry

/-- The multiplicative subset of odd integers used in the counterexample from
Example 29.50.4. -/
def example29504OddSubmonoid : Submonoid ℤ where
  carrier := {z | Odd z}
  one_mem' := by
    simpa using odd_one
  mul_mem' := by
    intro a b ha hb
    exact Odd.mul ha hb

/-- For `A = ℤ` and `S` the odd integers, the localization morphism is not an isomorphism over any
nonempty open of `Spec(ℤ)`. -/
theorem example29504OddLocalization_not_isIsoOverAnyOpen
    (U : (example29504SecondTargetScheme ℤ).Opens) (hU : Nonempty U) :
    ¬ IsIso (example29504SecondLocalizationMorphism ℤ example29504OddSubmonoid ∣_ U) := sorry

end SecondExample

end AlgebraicGeometry
