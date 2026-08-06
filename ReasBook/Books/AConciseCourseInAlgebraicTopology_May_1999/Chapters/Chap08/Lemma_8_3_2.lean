import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_1

open CategoryTheory
open scoped unitInterval

universe u

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced only model-category cofibration APIs, so the
-- faithful owner here is the project pair `IsCofibration` / `IsBasedCofibration`.

/-- Helper for Lemma 8.3.2: evaluating the extension formula at the source basepoint forces the
extended homotopy to stay fixed at the chosen basepoint of `X`. -/
theorem extensionFixedAtBasepoint
    {A X Y : BasedSpace.{u}} {i : A ⟶ X} {f₀ : X ⟶ Y} {g : A ⟶ Y}
    {G : C(X.right, Y.right)}
    (F : f₀.right.hom.Homotopy G)
    (H : ((i ≫ f₀).right.hom) HRel[A] g.right.hom)
    (hF : ∀ z : I × A.right, F (z.1, i.right.hom z.2) = H z)
    (t : I) :
    F (t, underTopBasepoint X) = f₀.right.hom (underTopBasepoint X) := by
  -- Evaluate the based-map triangle of `i` at the unique point of the terminal object.
  have hiBase : i.right.hom (underTopBasepoint A) = underTopBasepoint X := by
    have hw :=
      congrArg
        (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
        (Under.w i)
    simpa [underTopBasepoint] using hw
  -- Move from the extension formula on `A` to the singleton-relative condition on `X`.
  calc
    F (t, underTopBasepoint X) = F (t, i.right.hom (underTopBasepoint A)) := by
      rw [hiBase]
    _ = H (t, underTopBasepoint A) := by
      simpa using hF (t, underTopBasepoint A)
    _ = ((i ≫ f₀).right.hom) (underTopBasepoint A) := by
      exact H.eq_fst t (by simp [basedBasepointSet])
    _ = f₀.right.hom (underTopBasepoint X) := by
      change f₀.right.hom (i.right.hom (underTopBasepoint A)) = _
      rw [hiBase]

/-- Helper for Lemma 8.3.2: the endpoint of a singleton-relative homotopy preserves the chosen
basepoint. -/
theorem endpointPreservesBasepoint_of_basedHomotopyRel
    {X Y : BasedSpace.{u}} {f₀ : X ⟶ Y} {G : C(X.right, Y.right)}
    (hFrel : f₀.right.hom HRel[X] G) :
    G (underTopBasepoint X) = underTopBasepoint Y := by
  -- The relative condition identifies the endpoint map with the initial based map on the
  -- singleton basepoint set of `X`.
  have hendpoint : f₀.right.hom (underTopBasepoint X) = G (underTopBasepoint X) := by
    exact hFrel.fst_eq_snd (by simp [basedBasepointSet])
  -- Evaluate the based-map triangle of `f₀` at the terminal point.
  have hf₀Base : f₀.right.hom (underTopBasepoint X) = underTopBasepoint Y := by
    have hw :=
      congrArg
        (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
        (Under.w f₀)
    simpa [underTopBasepoint] using hw
  exact hendpoint.symm.trans hf₀Base

/-- Lemma 8.3.2. If the underlying unbased map of a based map `i : A ⟶ X` is a cofibration, then
`i` is a based cofibration. In this `BasedSpace` formalization, the source side condition that the
basepoint of `X` lies in `A` is encoded by choosing `A` as a based space and taking `i` to be a
morphism of based spaces. -/
theorem IsCofibration.isBasedCofibration
    {A X : BasedSpace.{u}} {i : A ⟶ X}
    (hi : IsCofibration.{u, u, u} i.right.hom) : IsBasedCofibration i := by
  intro Y f₀ g H
  let hUnderlying : (f₀.right.hom.comp i.right.hom).Homotopy g.right.hom := by
    -- Forget the singleton-relative condition and keep only the underlying homotopy.
    simpa using H.toHomotopy
  -- Apply the unbased homotopy extension property to the underlying maps.
  obtain ⟨G, F, hF⟩ :=
    hi.exists_homotopy_extension f₀.right.hom g.right.hom hUnderlying
  have hF' : ∀ z : I × A.right, F (z.1, i.right.hom z.2) = H z := by
    -- The extension theorem returns compatibility with `hUnderlying`, which is definitionally the
    -- same homotopy as `H.toHomotopy`.
    simpa [hUnderlying] using hF
  -- Recover the missing based structure from the singleton-relative condition at the source
  -- basepoint.
  let hFrel : f₀.right.hom HRel[X] G := by
    refine
      { toHomotopy := F
        prop' := ?_ }
    intro t x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    -- The singleton-relative condition on `X` is exactly the basepoint calculation proved above.
    exact extensionFixedAtBasepoint F H hF' t
  have hGbase : G (underTopBasepoint X) = underTopBasepoint Y :=
    endpointPreservesBasepoint_of_basedHomotopyRel hFrel
  have hGw : X.hom ≫ TopCat.ofHom G = Y.hom := by
    -- Two maps out of the terminal object agree once they agree at its unique point.
    ext u
    have hu : TopCat.terminalIsoPUnit.hom u = PUnit.unit := by
      cases h : TopCat.terminalIsoPUnit.hom u
      rfl
    have hu' : u = TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u) := by
      exact (congrArg (fun f ↦ f u) TopCat.terminalIsoPUnit.hom_inv_id).symm
    calc
      (X.hom ≫ TopCat.ofHom G) u = G (X.hom u) := rfl
      _ = G (X.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u))) := by
        rw [hu']
      _ = G (X.hom (TopCat.terminalIsoPUnit.inv PUnit.unit)) := by
        rw [hu]
      _ = G (underTopBasepoint X) := rfl
      _ = underTopBasepoint Y := hGbase
      _ = Y.hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
      _ = Y.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u)) := by
        rw [hu]
      _ = Y.hom u := by
        simp
  let Gbased : X ⟶ Y := Under.homMk (TopCat.ofHom G) hGw
  -- Package the endpoint map as a based map; the pointwise extension formula is unchanged.
  refine ⟨Gbased, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [Gbased] using hFrel
  · simpa [Gbased, hFrel] using hF'
