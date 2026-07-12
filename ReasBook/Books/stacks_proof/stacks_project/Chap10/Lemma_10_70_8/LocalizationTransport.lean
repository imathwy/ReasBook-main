import StacksProject_2024.Chap10.Lemma_10_70_8.ScaledReesAlgebra

universe u v

noncomputable section

open HomogeneousLocalization

section

/-- Helper for Lemma 10.70.8: a homogeneous-localization map sends a degree-zero fraction `r / 1`
to the corresponding degree-zero fraction after applying the graded map on degree zero. -/
theorem homogeneousLocalization_map_fromZeroRingHom
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜]
    {B : Type*} [CommRing B] {τ : Type*} [SetLike τ B] [AddSubgroupClass τ B]
    (ℬ : ι → τ) [GradedRing ℬ]
    (g : 𝒜 →+*ᵍ ℬ) {P : Submonoid A} {Q : Submonoid B} (comap_le : P ≤ Q.comap g)
    (a : 𝒜 0) :
    HomogeneousLocalization.map g comap_le (HomogeneousLocalization.fromZeroRingHom 𝒜 P a) =
      HomogeneousLocalization.fromZeroRingHom ℬ Q (g.gradedAddHom 0 a) := by
  ext
  simp [HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.map_mk]

/-- Helper for Lemma 10.70.8: `Away.map` preserves the degree-zero algebra map. -/
theorem away_map_fromZeroRingHom
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜]
    {B : Type*} [CommRing B] {τ : Type*} [SetLike τ B] [AddSubgroupClass τ B]
    (ℬ : ι → τ) [GradedRing ℬ]
    (g : 𝒜 →+*ᵍ ℬ) (f : A) (a : 𝒜 0) :
    HomogeneousLocalization.Away.map g f
      (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) a) =
      HomogeneousLocalization.fromZeroRingHom ℬ (Submonoid.powers (g f))
        (g.gradedAddHom 0 a) := by
  simpa [HomogeneousLocalization.Away.map] using
    homogeneousLocalization_map_fromZeroRingHom 𝒜 ℬ g
      (P := Submonoid.powers f) (Q := Submonoid.powers (g f))
      (by
        intro x hx
        rcases hx with ⟨n, rfl⟩
        exact ⟨n, by simp⟩)
      a

/-- Helper for Lemma 10.70.8: transporting a function along a codomain equality commutes with
evaluation at a point. -/
theorem cast_fun_apply
    {α : Type u} {β γ : Type v} (h : β = γ) (f : α → β) (x : α) :
    cast (congrArg (fun t ↦ α → t) h) f x = cast h (f x) := by
  cases h
  rfl

/-- Helper for Lemma 10.70.8: transporting a homogeneous-localization ring homomorphism along an
equality of the inverted degree-one parameter commutes with evaluation. -/
theorem cast_awayRingHom_apply
    {ι : Type*} [AddCommMonoid ι] [DecidableEq ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜]
    {d : ι} {f g : 𝒜 d} {S : Type*} [CommRing S]
    (h : f = g) (φ : S →+* Away 𝒜 (f : A)) (x : S) :
    cast (congrArg (fun y : 𝒜 d ↦ S →+* Away 𝒜 (y : A)) h) φ x =
      cast (congrArg (fun y : 𝒜 d ↦ Away 𝒜 (y : A)) h) (φ x) := by
  cases h
  rfl

/-- Helper for Lemma 10.70.8: transporting a function along a domain equality commutes with
evaluation after transporting the input. -/
theorem cast_fun_dom_apply
    {α β : Type u} {γ : Type v} (h : α = β) (f : β → γ) (x : α) :
    cast (congrArg (fun t ↦ t → γ) h.symm) f x = f (cast h x) := by
  cases h
  rfl

/-- Helper for Lemma 10.70.8: transporting an away-chart element along an equality of chart
parameters transports its ordinary localization value along the induced equality of localizations.
-/
theorem cast_away_val
    {ι : Type*} [AddCommMonoid ι] [DecidableEq ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜] {f g : A} (h : f = g) (x : Away 𝒜 f) :
    HomogeneousLocalization.val (cast (congrArg (fun y ↦ Away 𝒜 y) h) x) =
      cast (congrArg (fun y ↦ Localization.Away y) h) (HomogeneousLocalization.val x) := by
  cases h
  rfl

/-- Helper for Lemma 10.70.8: the same transport formula for `Away` values when the chart
parameter equality comes from equality inside a graded piece. -/
theorem cast_away_val_subtype
    {ι : Type*} [AddCommMonoid ι] [DecidableEq ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜] {d : ι} {f g : 𝒜 d} (h : f = g) (x : Away 𝒜 (f : A)) :
    HomogeneousLocalization.val (cast (congrArg (fun y : 𝒜 d ↦ Away 𝒜 (y : A)) h) x) =
      cast (congrArg (fun y : 𝒜 d ↦ Localization.Away (y : A)) h)
        (HomogeneousLocalization.val x) := by
  simpa using cast_away_val 𝒜 (congrArg Subtype.val h) x

/-- Helper for Lemma 10.70.8: transporting a standard away-localization fraction along an
equality of inverted elements only changes the recorded denominator data. -/
theorem cast_localizationAway_mk
    {A : Type*} [CommRing A] {f g r s t : A} (h : f = g) (hst : s = t)
    (hs : s ∈ Submonoid.powers f) (ht : t ∈ Submonoid.powers g) :
    cast (congrArg (fun y ↦ Localization.Away y) h) (Localization.mk r ⟨s, hs⟩) =
      Localization.mk r ⟨t, ht⟩ := by
  cases h
  cases hst
  rfl

end
