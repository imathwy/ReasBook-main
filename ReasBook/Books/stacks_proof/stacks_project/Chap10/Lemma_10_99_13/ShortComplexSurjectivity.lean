import Mathlib

open CategoryTheory CategoryTheory.Limits ModuleCat MonoidalCategory
open scoped ModuleCat

noncomputable section

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Helper for Lemma 10.99.13: if a morphism of short complexes is an isomorphism on the middle
and right terms, then it induces an epimorphism on homology. -/
theorem epi_shortComplex_homologyMap_of_isIso_τ₂_τ₃
    {S₁ S₂ : ShortComplex (ModuleCat S)} (φ : S₁ ⟶ S₂)
    [S₁.HasHomology] [S₂.HasHomology] [IsIso φ.τ₂] [IsIso φ.τ₃] :
    Epi (ShortComplex.homologyMap φ) := by
  -- An isomorphism on the middle term and a monomorphism on the right term make the cycles map
  -- an isomorphism.
  have hcycles : IsIso (ShortComplex.cyclesMap φ) := by
    apply ShortComplex.isIso_cyclesMap_of_isIso_of_mono'
    · infer_instance
    · infer_instance
  -- An epimorphic cycles map gives an epimorphic homology map.
  let _ : Epi (ShortComplex.cyclesMap φ) := by infer_instance
  infer_instance

/-- Helper for Lemma 10.99.13: the previous short-complex criterion upgrades to surjectivity on
underlying functions in `ModuleCat S`. -/
theorem surjective_shortComplex_homologyMap_of_isIso_τ₂_τ₃
    {S₁ S₂ : ShortComplex (ModuleCat S)} (φ : S₁ ⟶ S₂)
    [S₁.HasHomology] [S₂.HasHomology] [IsIso φ.τ₂] [IsIso φ.τ₃] :
    Function.Surjective (ShortComplex.homologyMap φ) := by
  -- The category of modules detects epimorphisms as surjective linear maps.
  have hEpi : Epi (ShortComplex.homologyMap φ) :=
    epi_shortComplex_homologyMap_of_isIso_τ₂_τ₃ φ
  exact (ModuleCat.epi_iff_surjective _).1 hEpi

/-- Helper for Lemma 10.99.13: restricting scalars does not change the underlying function of a
surjective module morphism. -/
theorem surjective_restrictScalars_map
    {X Y : ModuleCat S} (f : X ⟶ Y) (hf : Function.Surjective f) :
    Function.Surjective ((ModuleCat.restrictScalars (algebraMap R S)).map f) := by
  -- The source proof constructs the comparison over `S`; this helper transports the final
  -- surjectivity statement back to the `R`-linear target of the theorem.
  intro y
  rcases hf y with ⟨x, rfl⟩
  exact ⟨x, rfl⟩

/-- Helper for Lemma 10.99.13: adjoining an arbitrary extra degree-two summand leaves degrees one
and zero unchanged, so the induced comparison of short complexes is the degree-two inclusion and
the identity below it. -/
noncomputable def adjoin_degree_two_summand_comparison
    {X₂ Y₂ X₁ X₀ : ModuleCat S}
    {d₂ : X₂ ⟶ X₁} {e₂ : Y₂ ⟶ X₁} {d₁ : X₁ ⟶ X₀}
    (hsource : d₂ ≫ d₁ = 0) (htarget : biprod.desc d₂ e₂ ≫ d₁ = 0) :
    ShortComplex.mk d₂ d₁ hsource ⟶
      ShortComplex.mk (biprod.desc d₂ e₂) d₁ htarget where
  τ₁ := biprod.inl
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := by
    -- The corrected differential restricts to the original one on the left summand.
    simp
  comm₂₃ := by
    -- The lower two degrees are unchanged.
    simp

/-- Helper for Lemma 10.99.13: once the corrected presentation is built, the source proof's
surjectivity step is purely formal because the comparison is an isomorphism on degrees one and
zero. -/
theorem surjective_homologyMap_of_adjoin_degree_two_summand
    {X₂ Y₂ X₁ X₀ : ModuleCat S}
    {d₂ : X₂ ⟶ X₁} {e₂ : Y₂ ⟶ X₁} {d₁ : X₁ ⟶ X₀}
    (hsource : d₂ ≫ d₁ = 0) (htarget : biprod.desc d₂ e₂ ≫ d₁ = 0) :
    Function.Surjective
      (ShortComplex.homologyMap
        (adjoin_degree_two_summand_comparison (d₂ := d₂) (e₂ := e₂) (d₁ := d₁)
          hsource htarget)) := by
  -- The previously proved short-complex criterion applies directly to the comparison morphism.
  let comparison :=
    adjoin_degree_two_summand_comparison (d₂ := d₂) (e₂ := e₂) (d₁ := d₁) hsource htarget
  haveI : IsIso comparison.τ₂ := by
    dsimp [comparison, adjoin_degree_two_summand_comparison]
    infer_instance
  haveI : IsIso comparison.τ₃ := by
    dsimp [comparison, adjoin_degree_two_summand_comparison]
    infer_instance
  simpa using
    (surjective_shortComplex_homologyMap_of_isIso_τ₂_τ₃ comparison)

/-- Helper for Lemma 10.99.13: after adjoining the extra degree-two summand, restricting scalars
does not change the underlying surjective degree-one homology comparison. -/
theorem surjective_restrictScalars_homologyMap_of_adjoin_degree_two_summand
    {X₂ Y₂ X₁ X₀ : ModuleCat S}
    {d₂ : X₂ ⟶ X₁} {e₂ : Y₂ ⟶ X₁} {d₁ : X₁ ⟶ X₀}
    (hsource : d₂ ≫ d₁ = 0) (htarget : biprod.desc d₂ e₂ ≫ d₁ = 0) :
    Function.Surjective
      ((ModuleCat.restrictScalars (algebraMap R S)).map
        (ShortComplex.homologyMap
          (adjoin_degree_two_summand_comparison (d₂ := d₂) (e₂ := e₂) (d₁ := d₁)
            hsource htarget))) := by
  -- The `S`-linear degree-one homology map is already surjective by the previous helper.
  have hsurj :
      Function.Surjective
        (ShortComplex.homologyMap
          (adjoin_degree_two_summand_comparison (d₂ := d₂) (e₂ := e₂) (d₁ := d₁)
            hsource htarget)) :=
    surjective_homologyMap_of_adjoin_degree_two_summand
      (d₂ := d₂) (e₂ := e₂) (d₁ := d₁) hsource htarget
  -- Restricting scalars preserves the underlying surjective function.
  exact surjective_restrictScalars_map _ hsurj

/-- Helper for Lemma 10.99.13: conjugating a surjective module morphism by source and target
isomorphisms preserves surjectivity of the underlying function. -/
theorem surjective_of_iso_conjugation
    {A B X Y : ModuleCat R} (eSource : A ≅ X) (eTarget : B ≅ Y) (f : X ⟶ Y)
    (hf : Function.Surjective f) :
    Function.Surjective (eSource.hom ≫ f ≫ eTarget.inv) := by
  -- Move the target element across the chosen target isomorphism, then pull the preimage back
  -- across the chosen source isomorphism.
  intro y
  rcases hf (eTarget.hom y) with ⟨x, hx⟩
  refine ⟨eSource.inv x, ?_⟩
  change eTarget.inv (f (eSource.hom (eSource.inv x))) = y
  simp [hx]

/-- Helper for Lemma 10.99.13: once the source and target `Tor₁` owners are identified with the
two textbook short-complex homology objects, the final comparison and its surjectivity are purely
formal. -/
theorem exists_surjective_of_owner_conjugation
    {A B : ModuleCat R}
    {X₂ Y₂ X₁ X₀ : ModuleCat S}
    {d₂ : X₂ ⟶ X₁} {e₂ : Y₂ ⟶ X₁} {d₁ : X₁ ⟶ X₀}
    (hsource : d₂ ≫ d₁ = 0) (htarget : biprod.desc d₂ e₂ ≫ d₁ = 0)
    (eSource :
      A ≅ (ModuleCat.restrictScalars (algebraMap R S)).obj
        (ShortComplex.homology (ShortComplex.mk d₂ d₁ hsource)))
    (eTarget :
      B ≅ (ModuleCat.restrictScalars (algebraMap R S)).obj
        (ShortComplex.homology (ShortComplex.mk (biprod.desc d₂ e₂) d₁ htarget))) :
    ∃ comparison : A ⟶ B, Function.Surjective comparison := by
  let comparison :
      A ⟶ B :=
    eSource.hom ≫
      (ModuleCat.restrictScalars (algebraMap R S)).map
        (ShortComplex.homologyMap
          (adjoin_degree_two_summand_comparison (d₂ := d₂) (e₂ := e₂) (d₁ := d₁)
            hsource htarget)) ≫
      eTarget.inv
  refine ⟨comparison, ?_⟩
  -- The middle restricted homology map is the generic surjective map proved above.
  have hmiddle :
      Function.Surjective
        ((ModuleCat.restrictScalars (algebraMap R S)).map
          (ShortComplex.homologyMap
            (adjoin_degree_two_summand_comparison (d₂ := d₂) (e₂ := e₂) (d₁ := d₁)
              hsource htarget))) :=
    surjective_restrictScalars_homologyMap_of_adjoin_degree_two_summand
      (d₂ := d₂) (e₂ := e₂) (d₁ := d₁) hsource htarget
  -- Conjugate the surjective middle map by the owner-level identifications.
  simpa [comparison] using surjective_of_iso_conjugation eSource eTarget _ hmiddle

end
