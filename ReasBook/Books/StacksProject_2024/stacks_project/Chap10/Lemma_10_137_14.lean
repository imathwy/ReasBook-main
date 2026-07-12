import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

variable (R : Type u) (S' : Type v) (S'' : Type w)
variable [CommRing R] [CommRing S'] [CommRing S''] [Algebra R S'] [Algebra R S'']

/- Domain-style sampling:
- primary domain: smooth commutative `R`-algebras and their stability under finite products;
- sampled owner declarations:
  `Algebra.Smooth`,
  `Algebra.FormallySmooth.pi_iff`,
  `Algebra.FinitePresentation.of_isLocalizationAway`,
  `IsLocalization.away_of_isIdempotentElem`;
- best owner abstraction: `Algebra.Smooth R A`;
- primitive data: the smooth owner on `S' × S''`, or the two smooth owners on `S'` and `S''`;
- derived API: the factorwise formal smoothness and finite presentation coming from the canonical
  idempotent localizations, and the converse product smoothness obtained by transporting along the
  canonical `Bool`-indexed product view and applying `FormallySmooth.pi_iff`.

Source/core/bridge triage:
- `source-facing`: the binary-product statement below;
- `core/canonical`: `Algebra.Smooth`, `Algebra.FormallySmooth`, `Algebra.FinitePresentation`, and
  `IsLocalization.Away`;
- `bridge/view`: the equivalence between `S' × S''` and the `Bool`-indexed product used only to
  invoke the finite-product owner API.
-/

/-- Lemma 10.137.14: a product `R`-algebra `S' × S''` is smooth over `R` if and only if both
factors `S'` and `S''` are smooth over `R`. -/
theorem smooth_prod_iff :
    Smooth R (S' × S'') ↔ Smooth R S' ∧ Smooth R S'' := by
  let A : Bool → Type (max v w) := fun b ↦ cond b (ULift.{v} S'') (ULift.{w} S')
  letI : ∀ b, CommRing (A b) := by
    intro b
    cases b
    · change CommRing (ULift.{w} S')
      infer_instance
    · change CommRing (ULift.{v} S'')
      infer_instance
  letI : ∀ b, Algebra R (A b) := by
    intro b
    cases b
    · change Algebra R (ULift.{w} S')
      infer_instance
    · change Algebra R (ULift.{v} S'')
      infer_instance
  let eBool : ((b : Bool) → A b) ≃ₐ[R] A false × A true :=
    AlgEquiv.mk
      (Equiv.mk
        (fun f ↦ (f false, f true))
        (fun x b ↦ by
          cases b
          · exact x.1
          · exact x.2)
        (by
          intro f
          funext b
          cases b
          · rfl
          · rfl)
        (by
          intro x
          rfl))
      (by intro x y; rfl)
      (by intro x y; rfl)
      (by intro r; rfl)
  let eLeft : A false ≃ₐ[R] S' := by
    change ULift.{w} S' ≃ₐ[R] S'
    exact ULift.algEquiv
  let eRight : A true ≃ₐ[R] S'' := by
    change ULift.{v} S'' ≃ₐ[R] S''
    exact ULift.algEquiv
  let e : ((b : Bool) → A b) ≃ₐ[R] S' × S'' :=
    eBool.trans (AlgEquiv.prodCongr eLeft eRight)
  constructor
  · intro h
    letI : Smooth R (S' × S'') := h
    constructor
    · letI : Algebra (S' × S'') S' := (AlgHom.fst R S' S'').toAlgebra
      have hker : RingHom.ker (algebraMap (S' × S'') S') = Ideal.span {((0 : S'), (1 : S''))} := by
        ext x
        rw [Ideal.mem_span_singleton, RingHom.mem_ker]
        constructor
        · intro hx
          change x.1 = 0 at hx
          exact ⟨(0, x.2), by
            ext
            · simp [hx]
            · simp⟩
        · rintro ⟨y, rfl⟩
          change (((0 : S'), (1 : S'')) * y).1 = 0
          simp
      have h01 : ((0 : S'), (1 : S'')) = 1 - ((1 : S'), (0 : S'')) := by
        ext
        · simp
        · simp
      have hloc : IsLocalization.Away ((1 : S'), (0 : S'')) S' := by
        refine IsLocalization.away_of_isIdempotentElem ?_ ?_ Prod.fst_surjective
        · simp [IsIdempotentElem]
        · simpa [h01] using hker
      letI : FormallySmooth (S' × S'') S' :=
        FormallySmooth.of_isLocalization (Submonoid.powers ((1 : S'), (0 : S'')))
      exact ⟨FormallySmooth.comp R (S' × S'') S', Algebra.FinitePresentation.of_isLocalizationAway ((1 : S'), (0 : S''))⟩
    · letI : Algebra (S' × S'') S'' := (AlgHom.snd R S' S'').toAlgebra
      have hker : RingHom.ker (algebraMap (S' × S'') S'') = Ideal.span {((1 : S'), (0 : S''))} := by
        ext x
        rw [Ideal.mem_span_singleton, RingHom.mem_ker]
        constructor
        · intro hx
          change x.2 = 0 at hx
          exact ⟨(x.1, 0), by
            ext
            · simp
            · simp [hx]⟩
        · rintro ⟨y, rfl⟩
          change (((1 : S'), (0 : S'')) * y).2 = 0
          simp
      have h10 : ((1 : S'), (0 : S'')) = 1 - ((0 : S'), (1 : S'')) := by
        ext
        · simp
        · simp
      have hloc : IsLocalization.Away ((0 : S'), (1 : S'')) S'' := by
        refine IsLocalization.away_of_isIdempotentElem ?_ ?_ Prod.snd_surjective
        · simp [IsIdempotentElem]
        · simpa [h10] using hker
      letI : FormallySmooth (S' × S'') S'' :=
        FormallySmooth.of_isLocalization (Submonoid.powers ((0 : S'), (1 : S'')))
      exact ⟨FormallySmooth.comp R (S' × S'') S'', Algebra.FinitePresentation.of_isLocalizationAway ((0 : S'), (1 : S''))⟩
  · rintro ⟨h', h''⟩
    let _ : ∀ b, Smooth R (A b) := by
      intro b
      cases b
      · exact Smooth.of_equiv eLeft.symm
      · exact Smooth.of_equiv eRight.symm
    letI : Smooth R ((b : Bool) → A b) := by
      rw [smooth_iff]
      constructor
      · simpa using (FormallySmooth.pi_iff A).2 fun b ↦ (inferInstance : FormallySmooth R (A b))
      · infer_instance
    exact Smooth.of_equiv e

end Algebra
