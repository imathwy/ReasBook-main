import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

/-
Domain triage:
* primary domain: Jacobson rings via away-localizations in commutative algebra;
* source-facing layer: the example asserts that a product of fields is Jacobson;
* core/canonical owners: `IsJacobsonRing` and mathlib's away-localization API;
* bridge/view used here: surjectivity of each canonical map `R → Localization.Away f`,
  obtained from an associated idempotent and the owner theorem
  `IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem`.
-/

section

variable {R : Type u} [CommRing R]

/-- If the canonical map to every localization away from a single element is surjective, then `R`
is a Jacobson ring. Equivalently, each away-localization is already a quotient of `R` through the
localization map. -/
theorem isJacobsonRing_of_localizationAway_surjective
    (h : ∀ f : R, Function.Surjective (algebraMap R (Localization.Away f))) :
    IsJacobsonRing R :=
  by
    rw [isJacobsonRing_iff_sInf_maximal]
    intro P hP
    refine ⟨{ J : Ideal R | P ≤ J ∧ J.IsMaximal }, ?_, ?_⟩
    · intro J hJ
      exact Or.inl hJ.2
    · refine le_antisymm (le_sInf fun J hJ ↦ hJ.1) ?_
      intro x hx
      by_contra hxP
      let φ : R →+* Localization.Away x := algebraMap R (Localization.Away x)
      have hdisj : Disjoint (Submonoid.powers x : Set R) (P : Set R) := by
        rw [Ideal.disjoint_powers_iff_notMem x hP.isRadical]
        exact hxP
      have hPmap : (Ideal.map φ P).IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint
          (Submonoid.powers x) (Localization.Away x) P hP hdisj
      obtain ⟨M, hMmax, hPM⟩ := Ideal.exists_le_maximal (Ideal.map φ P) hPmap.ne_top
      letI := hMmax
      have hMcomapMax : (Ideal.comap φ M).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective φ (h x)
      have hPle : P ≤ Ideal.comap φ M := fun y hy ↦ hPM (Ideal.mem_map_of_mem _ hy)
      have hxM : x ∉ Ideal.comap φ M := by
        intro hxM
        exact hMmax.ne_top <|
          Ideal.eq_top_of_isUnit_mem _ hxM (IsLocalization.Away.algebraMap_isUnit x)
      exact hxM <| Ideal.mem_sInf.mp hx ⟨hPle, hMcomapMax⟩

end

section

variable {A : Type u} (k : A → Type v) [∀ a, Field (k a)]

open IsLocalization.Away

private def piFieldIdempotent (f : ∀ a, k a) : ∀ a, k a := fun a ↦
  letI := Classical.decEq (k a)
  if f a = 0 then 0 else 1

private theorem piFieldIdempotent_spec (f : ∀ a, k a) :
    IsIdempotentElem (piFieldIdempotent k f) := by
  classical
  ext a
  simp [piFieldIdempotent]

/-- The coordinatewise idempotent attached to `f` is associated to `f`. -/
-- Proof sketch: define the idempotent coordinatewise by testing whether the given coordinate is
-- zero, and define a unit coordinatewise by using `1` at zero coordinates and the original value
-- elsewhere. Then `f = u * e`, so `f` is associated to this idempotent `e`.
private theorem piFieldIdempotent_associated (f : ∀ a, k a) :
    Associated f (piFieldIdempotent k f) := by
  classical
  let u : ∀ a, k a := fun a ↦
    letI := Classical.decEq (k a)
    if f a = 0 then 1 else f a
  have hu : IsUnit u := by
    rw [Pi.isUnit_iff]
    intro a
    by_cases h : f a = 0
    · simp [u, h]
    · simp [u, h, isUnit_iff_ne_zero]
  have hf : f = u * piFieldIdempotent k f := by
    ext a
    by_cases h : f a = 0
    · simp [u, piFieldIdempotent, h]
    · simp [u, piFieldIdempotent, h]
  exact (Associated.of_eq hf).trans <|
    associated_unit_mul_left _ _ hu

/-- Example 10.35.7: if `k a` is a field for each `a : A`, then `∀ a, k a` is a Jacobson ring.
This strengthens the source statement, which also assumes `A` is infinite. -/
@[stacks 02CC]
instance pi_isJacobsonRing : IsJacobsonRing ((a : A) → k a) :=
  isJacobsonRing_of_localizationAway_surjective fun f ↦ by
    let e := piFieldIdempotent k f
    have he : IsIdempotentElem e := piFieldIdempotent_spec k f
    have hfe : Associated f e := piFieldIdempotent_associated k f
    letI : IsLocalization.Away e (Localization.Away f) := of_associated hfe
    exact IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he

end
