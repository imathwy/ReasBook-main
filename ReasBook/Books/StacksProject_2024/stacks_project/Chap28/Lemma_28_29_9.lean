import Mathlib.AlgebraicGeometry.AffineScheme

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Source/core/bridge triage:
- `source-facing`: every point of `W` admits an affine open neighborhood whose images in the two
  affine targets are basic opens;
- `core/canonical`: the proof is built from the canonical affine-open intersection owner
  `exists_basicOpen_le_affine_inter`, the open-immersion affine-open equivalence
  `IsOpenImmersion.affineOpensEquiv`, and the image computation `Scheme.image_basicOpen`;
- `bridge/view`: two small private helpers isolate the single-open-immersion and image-computation
  steps so the public theorem keeps the Stacks-facing statement while avoiding one monolithic proof
  term. -/

private theorem exists_affineOpen_containing_of_isOpenImmersion
    {U W : Scheme.{u}} [IsAffine U] (i : W ⟶ U) [IsOpenImmersion i] (w : W) :
    ∃ f : Γ(U, ⊤), ∃ Wi : W.affineOpens,
      w ∈ (Wi : W.Opens) ∧ Scheme.Hom.opensRange ((Wi : W.Opens).ι ≫ i) = U.basicOpen f := by
  let x : Scheme.Hom.opensRange i := ⟨i w, by simp⟩
  obtain ⟨f, hf, hwf⟩ :=
    (isAffineOpen_top U).exists_basicOpen_le x (by simp)
  let Wi : W.affineOpens :=
    (IsOpenImmersion.affineOpensEquiv i).symm
      ⟨⟨U.basicOpen f, (isAffineOpen_top U).basicOpen f⟩, hf⟩
  refine ⟨f, Wi, ?_, ?_⟩
  · change i w ∈ U.basicOpen f
    simpa [x] using hwf
  · have hs :
        (IsOpenImmersion.affineOpensEquiv i) Wi =
          ⟨⟨U.basicOpen f, (isAffineOpen_top U).basicOpen f⟩, hf⟩ := by
        simpa [Wi] using
          (IsOpenImmersion.affineOpensEquiv i).apply_symm_apply
            ⟨⟨U.basicOpen f, (isAffineOpen_top U).basicOpen f⟩, hf⟩
    have hs' : ↑↑((IsOpenImmersion.affineOpensEquiv i) Wi) = U.basicOpen f := by
      simpa using congrArg (fun Z ↦ (↑↑Z : U.Opens)) hs
    have himage : (Scheme.Hom.opensFunctor i).obj (Wi : W.Opens) = U.basicOpen f :=
      (IsOpenImmersion.affineOpensEquiv_apply_coe_coe i Wi).symm.trans hs'
    simpa [Scheme.Hom.opensRange_comp] using himage

private theorem exists_global_basicOpen_image_of_basicOpen
    {U W : Scheme.{u}} [IsAffine U] (i : W ⟶ U) [IsOpenImmersion i] (Wi : W.affineOpens)
    (f : Γ(U, ⊤)) (hWi : Scheme.Hom.opensRange ((Wi : W.Opens).ι ≫ i) = U.basicOpen f)
    (a : Γ(W, (Wi : W.Opens))) :
    ∃ f' : Γ(U, ⊤), Scheme.Hom.opensRange ((W.basicOpen a).ι ≫ i) = U.basicOpen f' := by
  let p := (Wi : W.Opens).ι ≫ i
  let ai : Γ(((Wi : W.Opens) : Scheme), ⊤) := ((Wi : W.Opens).topIso.inv) a
  let r : Γ(U, p ''ᵁ (⊤ : (((Wi : W.Opens) : Scheme).Opens))) := (Scheme.Hom.appIso p ⊤).inv ai
  have hp : p ''ᵁ (⊤ : (((Wi : W.Opens) : Scheme).Opens)) = U.basicOpen f := by
    simpa [p, Scheme.Hom.opensRange_comp] using hWi
  let r' : Γ(U, U.basicOpen f) := (U.presheaf.map (eqToHom hp.symm).op) r
  obtain ⟨f', hf'⟩ := (isAffineOpen_top U).basicOpen_basicOpen_is_basicOpen f r'
  refine ⟨f', ?_⟩
  have hsource :
      Scheme.Hom.opensRange ((W.basicOpen a).ι ≫ i) =
        p ''ᵁ (((Wi : W.Opens) : Scheme).basicOpen ai) := by
    calc
      Scheme.Hom.opensRange ((W.basicOpen a).ι ≫ i) = i ''ᵁ W.basicOpen a := by
        simp [Scheme.Hom.opensRange_comp]
      _ = i ''ᵁ ((Wi : W.Opens).ι ''ᵁ (((Wi : W.Opens) : Scheme).basicOpen ai)) := by
        rw [Scheme.Opens.ι_image_basicOpen_topIso_inv (Wi : W.Opens) a]
      _ = p ''ᵁ (((Wi : W.Opens) : Scheme).basicOpen ai) := by
        simp [p]
  have himage :
      p ''ᵁ (((Wi : W.Opens) : Scheme).basicOpen ai) = U.basicOpen r := by
    simpa [p, r] using Scheme.image_basicOpen p ai
  have hr' : U.basicOpen r' = U.basicOpen r := by
    simpa [r'] using Scheme.basicOpen_res_eq U r (eqToHom hp.symm).op
  exact hsource.trans <| himage.trans <| hr'.symm.trans hf'.symm

/-- Lemma 28.29.9: if `W` admits open immersions into affine schemes `U` and `V`, then every
point of `W` has an affine open neighborhood whose images in `U` and `V` are standard opens. -/
@[stacks 0H9B] theorem exists_affineOpenNeighborhood_mappingTo_basicOpens
    {U V W : Scheme.{u}} [IsAffine U] [IsAffine V]
    (i : W ⟶ U) (j : W ⟶ V) [IsOpenImmersion i] [IsOpenImmersion j] (w : W) :
    ∃ W' : W.Opens, w ∈ W' ∧ IsAffineOpen W' ∧
      ∃ f : Γ(U, ⊤), ∃ g : Γ(V, ⊤),
        Scheme.Hom.opensRange (W'.ι ≫ i) = U.basicOpen f ∧
          Scheme.Hom.opensRange (W'.ι ≫ j) = V.basicOpen g := by
  obtain ⟨fi, Wi, hwi, hWi⟩ := exists_affineOpen_containing_of_isOpenImmersion i w
  obtain ⟨fj, Wj, hwj, hWj⟩ := exists_affineOpen_containing_of_isOpenImmersion j w
  obtain ⟨a, b, hab, hwa⟩ := exists_basicOpen_le_affine_inter Wi.2 Wj.2 w ⟨hwi, hwj⟩
  obtain ⟨f, hf⟩ := exists_global_basicOpen_image_of_basicOpen i Wi fi hWi a
  obtain ⟨g, hg⟩ := exists_global_basicOpen_image_of_basicOpen j Wj fj hWj b
  refine ⟨W.basicOpen a, hwa, Wi.2.basicOpen a, f, g, hf, ?_⟩
  rw [Scheme.Hom.opensRange_comp, hab]
  simpa [Scheme.Hom.opensRange_comp] using hg

end AlgebraicGeometry
