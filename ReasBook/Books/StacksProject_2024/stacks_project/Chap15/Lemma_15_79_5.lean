import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_65_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_75_1
import StacksProject_2024.stacks_project.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I J : Ideal R)

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.79.5:
- primary domain: perfect complexes in quotient derived categories under derived scalar extension
  along compatible quotient maps `R → R ⧸ I`, `R → R ⧸ J`, and `R → R ⧸ (I * J)`;
- sampled owner declarations:
  `derivedTensorWithAlgebra`,
  `K ⊗[R]^L[(R ⧸ I)]`,
  `DerivedCategory.IsPerfect`,
  `isPerfect_of_derivedTensorWithAlgebra_quotient_isPerfect_of_isNilpotent`;
- best owner abstraction:
  the source-facing statement is the perfectness of the quotient-ring base changes
  `K ⊗[R]^L[(R ⧸ I)]`, `K ⊗[R]^L[(R ⧸ J)]`, and `K ⊗[R]^L[(R ⧸ (I * J))]`, so the public
  theorem should use the chapter's canonical owner `derivedTensorWithAlgebra` rather than the
  stronger restriction-of-scalars presentation in `D(R)`;
- primitive vs. derived:
  primitive data are the commutative ring `R`, the ideals `I`, `J`, and the object `K : D(R)`;
  the three perfectness predicates live on the already-owned quotient derived objects
  `K ⊗[R]^L[(R ⧸ I)]`, `K ⊗[R]^L[(R ⧸ J)]`, and `K ⊗[R]^L[(R ⧸ (I * J))]`, so no extra degree-zero
  quotient-module packaging belongs in the public API;
- source/core/bridge triage:
  `source-facing`: perfectness of the quotient-derived objects over `R ⧸ I` and `R ⧸ J` implies
    perfectness over `R ⧸ (I * J)`;
  `core/canonical`: `derivedTensorWithAlgebra` and `DerivedCategory.IsPerfect`;
  `bridge/view`: any later restriction-of-scalars identification back in `D(R)` is only a bridge,
    not the main statement here.
-/

-- Proof sketch: first replace `R` by `R ⧸ (I * J)` and `K` by its reduction modulo `I * J`.
-- The induced map `R ⧸ (I * J) → R ⧸ (I ⊓ J)` has square-zero kernel, so Lemma `15.79.4`
-- reduces the claim to the case `I ⊓ J = 0`. In that case, represent `K` by a K-flat complex,
-- use the short exact sequence relating reduction modulo `I`, `J`, and `I + J`, deduce bounded
-- cohomology, and then apply the compactness criterion of Proposition `15.79.3` via the five
-- lemma on direct-sum comparison maps.
/-- Helper for Lemma 15.79.5: modulo `I ∩ J`, the image of `IJ` vanishes. -/
lemma quotient_inf_image_mul_eq_bot :
    Ideal.map (Ideal.Quotient.mk (I ⊓ J)) (I * J) = ⊥ := by
  -- The quotient by `I ∩ J` kills every element of `IJ` because `IJ ⊆ I ∩ J`.
  apply (Ideal.map_eq_bot_iff_le_ker _).2
  rw [Ideal.mk_ker]
  exact Ideal.mul_le_inf

/-- Helper for Lemma 15.79.5: the image of `I ∩ J` inside `R / IJ` is square-zero, hence
nilpotent. -/
lemma quotient_mul_image_inf_isNilpotent :
    IsNilpotent (Ideal.map (Ideal.Quotient.mk (I * J)) (I ⊓ J)) := by
  refine ⟨2, ?_⟩
  -- Squaring the image factors through the image of `(I ∩ J)^2`, which already lies in `IJ`.
  rw [pow_two, ← Ideal.map_mul, Ideal.zero_eq_bot]
  apply (Ideal.map_eq_bot_iff_le_ker _).2
  rw [Ideal.mk_ker]
  exact Ideal.mul_mono inf_le_left inf_le_right

/-- Helper for Lemma 15.79.5: the iterated quotient map from `R / IJ` to
`(R / (I ∩ J)) / \overline{IJ}` is surjective. -/
lemma quotient_mul_to_quotient_inf_surjective :
    Function.Surjective ⇑(Ideal.quotientMapₐ
      (Ideal.map (Ideal.Quotient.mkₐ R (I ⊓ J)) (I * J))
      (Ideal.Quotient.mkₐ R (I ⊓ J))
      Ideal.le_comap_map) := by
  -- This is the standard surjectivity statement for quotient maps induced by a surjective source
  -- map.
  simpa using
    (Ideal.quotientMap_surjective
      (f := Ideal.Quotient.mk (I ⊓ J))
      (I := Ideal.map (Ideal.Quotient.mk (I ⊓ J)) (I * J))
      (J := I * J)
      (H := Ideal.le_comap_map)
      Ideal.Quotient.mk_surjective)

/-- Helper for Lemma 15.79.5: the kernel of the iterated quotient map from `R / IJ` is the image
of `I ∩ J`. -/
lemma quotient_mul_to_quotient_inf_kernel :
    RingHom.ker ((Ideal.quotientMapₐ
      (Ideal.map (Ideal.Quotient.mkₐ R (I ⊓ J)) (I * J))
      (Ideal.Quotient.mkₐ R (I ⊓ J))
      Ideal.le_comap_map).toRingHom) =
      Ideal.map (Ideal.Quotient.mk (I * J)) (I ⊓ J) := by
  -- This is the standard kernel computation for an iterated quotient map.
  simpa using (Ideal.ker_quotientMap_mk (I := I ⊓ J) (J := I * J))

/-- Helper for Lemma 15.79.5: quotienting `R / IJ` by the image of `I ∩ J` identifies with
`R / (I ∩ J)`. -/
noncomputable def quotient_mul_image_inf_quotient_equiv_quotient_inf :
    ((R ⧸ (I * J)) ⧸ Ideal.map (Ideal.Quotient.mk (I * J)) (I ⊓ J)) ≃ₐ[R] R ⧸ (I ⊓ J) :=
  let e₁ :
      ((R ⧸ (I * J)) ⧸ Ideal.map (Ideal.Quotient.mk (I * J)) (I ⊓ J)) ≃ₐ[R]
        ((R ⧸ (I * J)) ⧸ RingHom.ker ((Ideal.quotientMapₐ
          (Ideal.map (Ideal.Quotient.mkₐ R (I ⊓ J)) (I * J))
          (Ideal.Quotient.mkₐ R (I ⊓ J))
          Ideal.le_comap_map).toRingHom)) :=
    Ideal.quotientEquivAlgOfEq R (quotient_mul_to_quotient_inf_kernel (R := R) (I := I) (J := J)).symm
  let e₂ :
      ((R ⧸ (I * J)) ⧸ RingHom.ker ((Ideal.quotientMapₐ
        (Ideal.map (Ideal.Quotient.mkₐ R (I ⊓ J)) (I * J))
        (Ideal.Quotient.mkₐ R (I ⊓ J))
        Ideal.le_comap_map).toRingHom)) ≃ₐ[R]
          ((R ⧸ (I ⊓ J)) ⧸ Ideal.map (Ideal.Quotient.mk (I ⊓ J)) (I * J)) :=
    Ideal.quotientKerAlgEquivOfSurjective
      (f := Ideal.quotientMapₐ
        (Ideal.map (Ideal.Quotient.mkₐ R (I ⊓ J)) (I * J))
        (Ideal.Quotient.mkₐ R (I ⊓ J))
        Ideal.le_comap_map)
      (quotient_mul_to_quotient_inf_surjective (R := R) (I := I) (J := J))
  let e₃ :
      ((R ⧸ (I ⊓ J)) ⧸ Ideal.map (Ideal.Quotient.mk (I ⊓ J)) (I * J)) ≃ₐ[R]
        ((R ⧸ (I ⊓ J)) ⧸ ⊥) :=
    Ideal.quotientEquivAlgOfEq R (quotient_inf_image_mul_eq_bot (R := R) (I := I) (J := J))
  -- Identify the iterated quotient with the quotient by `I ∩ J`, then collapse the trivial final
  -- quotient.
  e₁.trans <| e₂.trans <| e₃.trans <| AlgEquiv.quotientBot R (R ⧸ (I ⊓ J))

/-- Helper for Lemma 15.79.5: perfectness modulo `I` base-changes further to perfectness modulo
`I ⊔ J`. -/
lemma isPerfect_derivedTensorWithAlgebra_quotient_sup_of_isPerfect_left
    (K : DMod)
    (hI : (K ⊗[R]^L[(R ⧸ I)]).IsPerfect) :
    (K ⊗[R]^L[(R ⧸ (I ⊔ J))]).IsPerfect := by
  -- TODO: once the chapter base-change theorem `derivedTensorWithAlgebra_isPerfect` is available
  -- in dependency-closed form, base change `K ⊗[R]^L[R ⧸ I]` along
  -- `R ⧸ I → R ⧸ (I ⊔ J)` and identify the iterated tensor product with
  -- `K ⊗[R]^L[R ⧸ (I ⊔ J)]` via `derivedTensorWithAlgebraCompIso`.
  sorry

/-- Helper for Lemma 15.79.5: in the reduced case `I ∩ J = 0`, the source proof shows that
perfectness modulo `I` and modulo `J` implies perfectness over `R`. -/
lemma isPerfect_of_isPerfect_quotient_left_right_of_inf_eq_bot
    (K : DMod)
    (hInf : I ⊓ J = ⊥)
    (hI : (K ⊗[R]^L[(R ⧸ I)]).IsPerfect)
    (hJ : (K ⊗[R]^L[(R ⧸ J)]).IsPerfect) :
    K.IsPerfect := by
  -- Route correction: the remaining argument must follow the textbook proof through a K-flat
  -- representative, the short exact quotient-complex row, boundedness, and then the compactness
  -- criterion of Proposition `15.79.3`.
  have hSup :
      (K ⊗[R]^L[(R ⧸ (I ⊔ J))]).IsPerfect :=
    isPerfect_derivedTensorWithAlgebra_quotient_sup_of_isPerfect_left
      (R := R) (I := I) (J := J) K hI
  -- TODO: build the short exact sequence
  -- `0 → P → P/IP ⊕ P/JP → P/(I ⊔ J)P → 0` for a K-flat representative `P` of `K`, use `hInf`
  -- to identify the left term with `P`, deduce bounded cohomology from `hI`, `hJ`, and `hSup`,
  -- and then prove compactness by the five-lemma comparison diagram from the source proof.
  sorry

/-- Helper for Lemma 15.79.5: after passing from `R / IJ` to the square-zero thickening
`R / (I ∩ J)`, the remaining work is the source-proof zero-intersection argument. -/
lemma quotient_mul_inf_nilpotent_bridge
    (K : DMod)
    (hI : (K ⊗[R]^L[(R ⧸ I)]).IsPerfect)
    (hJ : (K ⊗[R]^L[(R ⧸ J)]).IsPerfect) :
    (K ⊗[R]^L[(R ⧸ (I * J))]).IsPerfect := by
  -- Route correction: the quotient-ideal front half is complete, so the remaining work is the
  -- source-faithful derived-category descent through the zero-intersection case and the final
  -- nilpotent thickening.
  -- TODO: combine `quotient_mul_image_inf_isNilpotent` with
  -- `quotient_mul_image_inf_quotient_equiv_quotient_inf` to replace `R / IJ` by `R / (I ∩ J)`,
  -- apply the nilpotent-thickening descent lemma of 15.79.4, and then finish with the
  -- zero-intersection source proof using the short exact quotient-complex sequence and
  -- Proposition 15.79.3.
  sorry

/-- Lemma 15.79.5: if the quotient-derived base changes
`K \otimes_R^{\mathbf L} (R / I)` and `K \otimes_R^{\mathbf L} (R / J)` are perfect in
`D(R / I)` and `D(R / J)`, then `K \otimes_R^{\mathbf L} (R / IJ)` is perfect in
`D(R / IJ)`. -/
theorem isPerfect_derivedTensorWithAlgebra_quotient_mul_of_isPerfect_quotient_left_right
    (K : DMod)
    (hI : (K ⊗[R]^L[(R ⧸ I)]).IsPerfect)
    (hJ : (K ⊗[R]^L[(R ⧸ J)]).IsPerfect) :
    (K ⊗[R]^L[(R ⧸ (I * J))]).IsPerfect := by
  -- The proved ideal-theoretic reduction isolates the remaining source-faithful derived-category
  -- descent in `quotient_mul_inf_nilpotent_bridge`.
  exact quotient_mul_inf_nilpotent_bridge (R := R) (I := I) (J := J) K hI hJ

end

end CategoryTheory
