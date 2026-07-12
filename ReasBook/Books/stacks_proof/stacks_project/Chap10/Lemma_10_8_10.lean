import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import StacksProject_2024.Chap04.Lemma_4_19_8
import StacksProject_2024.Chap04.Lemma_4_21_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

section

variable {I : Type u} [Category.{v} I] [Small.{v} I]
variable [HasSpanCocones I]

/-- Helper for Lemma 10.8.10: the quotient indexing the connected components of a `v`-small
category is itself `v`-small. -/
private instance connected_components_small :
    Small.{v} (CategoryTheory.ConnectedComponents I) := by
  dsimp [CategoryTheory.ConnectedComponents]
  infer_instance

-- Proof sketch: the source statement is about abelian groups, whose owner category in mathlib is
-- `AddCommGrpCat`. By `hasExactColimitsOfShape_of_preservesMono`, it is enough to show that
-- `colim : (I ⥤ AddCommGrpCat) ⥤ AddCommGrpCat` preserves monomorphisms. Decompose `I` into
-- connected components using Lemma `4.19.8`, each of which is filtered, apply filtered exactness
-- in `AddCommGrpCat` componentwise, and reassemble the result using exactness of coproducts.

/-- Helper for Lemma 10.8.10: the canonical legs from a decomposed diagram into the coproduct of
the componentwise colimits are natural in the decomposed index. -/
private lemma decomposed_component_cocone_naturality
    (F : CategoryTheory.Decomposed I ⥤ AddCommGrpCat)
    {X Y : CategoryTheory.Decomposed I} (f : X ⟶ Y) :
    F.map f ≫ colimit.ι (CategoryTheory.inclusion Y.1 ⋙ F) Y.2 ≫
          Limits.Sigma.ι
            (fun j : CategoryTheory.ConnectedComponents I =>
              colimit (CategoryTheory.inclusion j ⋙ F))
            Y.1 =
      (colimit.ι (CategoryTheory.inclusion X.1 ⋙ F) X.2 ≫
          Limits.Sigma.ι
            (fun j : CategoryTheory.ConnectedComponents I =>
              colimit (CategoryTheory.inclusion j ⋙ F))
            X.1) ≫
        ((Functor.const (CategoryTheory.Decomposed I)).obj
          (∐ fun j : CategoryTheory.ConnectedComponents I =>
            colimit (CategoryTheory.inclusion j ⋙ F))).map f := by
  -- Destruct the sigma-category morphism so the goal becomes the `colimit.w` relation on the
  -- relevant connected component, followed by the fixed coproduct injection.
  rcases X with ⟨j, X⟩
  rcases Y with ⟨_, Y⟩
  rcases f with ⟨f⟩
  simpa [Functor.const_obj_map] using
    (colimit.w_assoc (F := CategoryTheory.inclusion j ⋙ F) f
      (Limits.Sigma.ι
        (fun j : CategoryTheory.ConnectedComponents I =>
          colimit (CategoryTheory.inclusion j ⋙ F))
        j))

/-- Helper for Lemma 10.8.10: the chosen `Sigma.desc` map agrees with the legs of any cocone over
the decomposed diagram after restricting to one connected component. -/
private lemma decomposed_component_cocone_desc_fac
    (F : CategoryTheory.Decomposed I ⥤ AddCommGrpCat) (s : Cocone F)
    (j : CategoryTheory.ConnectedComponents I) (X : j.Component) :
    colimit.ι (CategoryTheory.inclusion j ⋙ F) X ≫
        Limits.Sigma.ι
          (fun k : CategoryTheory.ConnectedComponents I =>
            colimit (CategoryTheory.inclusion k ⋙ F))
          j ≫
        Limits.Sigma.desc
        (fun k : CategoryTheory.ConnectedComponents I =>
          colimit.desc (CategoryTheory.inclusion k ⋙ F)
            (Cocone.whisker (CategoryTheory.inclusion k) s)) =
        s.ι.app ⟨j, X⟩ := by
  -- First descend out of the coproduct of componentwise colimits, then out of the colimit on the
  -- chosen connected component.
  rw [Limits.Sigma.ι_desc]
  simpa using colimit.ι_desc (Cocone.whisker (CategoryTheory.inclusion j) s) X

/-- Helper for Lemma 10.8.10: a diagram on the decomposed category has a canonical cocone whose
vertex is the coproduct of the colimits over the connected components. -/
private def decomposed_component_cocone
    (F : CategoryTheory.Decomposed I ⥤ AddCommGrpCat) :
    Cocone F where
  pt := ∐ fun j : CategoryTheory.ConnectedComponents I =>
    colimit (CategoryTheory.inclusion j ⋙ F)
  ι :=
    { app := fun X =>
        colimit.ι (CategoryTheory.inclusion X.1 ⋙ F) X.2 ≫
          Limits.Sigma.ι
            (fun j : CategoryTheory.ConnectedComponents I =>
              colimit (CategoryTheory.inclusion j ⋙ F))
            X.1
      naturality := fun _ _ f => decomposed_component_cocone_naturality F f }

/-- Helper for Lemma 10.8.10: the coproduct of the componentwise colimits is a colimit of the
whole decomposed diagram. -/
private def decomposed_component_cocone_isColimit
    (F : CategoryTheory.Decomposed I ⥤ AddCommGrpCat) :
    IsColimit (decomposed_component_cocone F) := by
  -- Route correction: define the desc morphism by assembling the componentwise colimit desc maps,
  -- then prove uniqueness by extensionality on the coproduct and on each component colimit.
  refine
    { desc := fun s =>
        Limits.Sigma.desc
          (fun j : CategoryTheory.ConnectedComponents I =>
            colimit.desc (CategoryTheory.inclusion j ⋙ F)
              (Cocone.whisker (CategoryTheory.inclusion j) s))
      fac := ?_
      uniq := ?_ }
  · intro s X
    cases X with
    | mk j X =>
        simpa [decomposed_component_cocone] using decomposed_component_cocone_desc_fac F s j X
  · intro s m hm
    apply Limits.Sigma.hom_ext
    intro j
    apply colimit.hom_ext
    intro X
    simpa [decomposed_component_cocone, Category.assoc] using
      (hm ⟨j, X⟩).trans (decomposed_component_cocone_desc_fac F s j X).symm

/-- Helper for Lemma 10.8.10: the colimit of a decomposed diagram is canonically the coproduct of
the colimits over its connected components. -/
private def decomposed_colimit_iso_component_coproduct
    (F : CategoryTheory.Decomposed I ⥤ AddCommGrpCat) :
    (∐ fun j : CategoryTheory.ConnectedComponents I =>
      colimit (CategoryTheory.inclusion j ⋙ F)) ≅ colimit F :=
  IsColimit.coconePointUniqueUpToIso
    (decomposed_component_cocone_isColimit F) (colimit.isColimit F)

/-- Helper for Lemma 10.8.10: under the componentwise colimit decomposition, the canonical
inclusion of an object in the decomposed diagram is the component colimit leg followed by the
corresponding coproduct injection. -/
@[reassoc (attr := simp)]
private lemma decomposed_colimit_iso_component_coproduct_ι
    (F : CategoryTheory.Decomposed I ⥤ AddCommGrpCat)
    (j : CategoryTheory.ConnectedComponents I) (X : j.Component) :
    colimit.ι (CategoryTheory.inclusion j ⋙ F) X ≫
        Limits.Sigma.ι
          (fun k : CategoryTheory.ConnectedComponents I =>
            colimit (CategoryTheory.inclusion k ⋙ F))
          j ≫
      (decomposed_colimit_iso_component_coproduct F).hom =
        colimit.ι F ⟨j, X⟩ := by
  -- The comparison isomorphism between the two colimit cocones is determined by its effect on
  -- each cocone leg.
  simpa [decomposed_component_cocone, decomposed_colimit_iso_component_coproduct] using
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (decomposed_component_cocone_isColimit F) (colimit.isColimit F) ⟨j, X⟩

/-- Helper for Lemma 10.8.10: the inverse of the componentwise colimit decomposition sends the
canonical colimit leg of the decomposed diagram to the matching coproduct summand. -/
@[reassoc (attr := simp)]
private lemma decomposed_colimit_iso_component_coproduct_inv_ι
    (F : CategoryTheory.Decomposed I ⥤ AddCommGrpCat)
    (j : CategoryTheory.ConnectedComponents I) (X : j.Component) :
    colimit.ι F ⟨j, X⟩ ≫ (decomposed_colimit_iso_component_coproduct F).inv =
      colimit.ι (CategoryTheory.inclusion j ⋙ F) X ≫
        Limits.Sigma.ι
          (fun k : CategoryTheory.ConnectedComponents I =>
            colimit (CategoryTheory.inclusion k ⋙ F))
          j := by
  -- Postcompose the forward leg formula with the inverse comparison isomorphism and cancel the
  -- resulting isomorphism.
  apply (cancel_mono ((decomposed_colimit_iso_component_coproduct F).hom)).1
  -- After postcomposing with the comparison isomorphism, both sides become the forward leg
  -- formula proved above.
  simp only [Category.assoc]
  simpa using (decomposed_colimit_iso_component_coproduct_ι F j X).symm

/-- Helper for Lemma 10.8.10: postcomposing the inverse decomposition leg with the fixed coproduct
comparison map preserves the componentwise leg formula. -/
private lemma decomposed_colimit_iso_component_coproduct_inv_postcompose
    {F G : CategoryTheory.Decomposed I ⥤ AddCommGrpCat} (α : F ⟶ G)
    (j : CategoryTheory.ConnectedComponents I) (X : j.Component) :
    colimit.ι F ⟨j, X⟩ ≫ (decomposed_colimit_iso_component_coproduct F).inv ≫
        (Limits.Sigma.map
          (fun j : CategoryTheory.ConnectedComponents I =>
            colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)) ≫
          (decomposed_colimit_iso_component_coproduct G).hom) =
      (colimit.ι (CategoryTheory.inclusion j ⋙ F) X ≫
          Limits.Sigma.ι
            (fun k : CategoryTheory.ConnectedComponents I =>
              colimit (CategoryTheory.inclusion k ⋙ F))
            j) ≫
        (Limits.Sigma.map
          (fun j : CategoryTheory.ConnectedComponents I =>
            colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)) ≫
          (decomposed_colimit_iso_component_coproduct G).hom) := by
  -- Freeze the inverse-leg rewrite before entering the coproduct comparison. This isolates the
  -- stable source-faithful transport step needed in the main comparison proof.
  simpa [Category.assoc] using
    congrArg
      (fun k =>
        k ≫
          (Limits.Sigma.map
            (fun j : CategoryTheory.ConnectedComponents I =>
              colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)) ≫
            (decomposed_colimit_iso_component_coproduct G).hom))
      (decomposed_colimit_iso_component_coproduct_inv_ι F j X)

/-- Helper for Lemma 10.8.10: after identifying a decomposed colimit with the coproduct of the
componentwise colimits, precomposing the transported coproduct map with a decomposed colimit leg
recovers the corresponding stagewise map into the target colimit. -/
private lemma decomposed_colim_map_eq_sigma_map_leg
    {F G : CategoryTheory.Decomposed I ⥤ AddCommGrpCat} (α : F ⟶ G)
    (j : CategoryTheory.ConnectedComponents I) (X : j.Component) :
    colimit.ι F ⟨j, X⟩ ≫
        ((decomposed_colimit_iso_component_coproduct F).inv ≫
          Limits.Sigma.map
            (fun k : CategoryTheory.ConnectedComponents I =>
              colim.map (Functor.whiskerLeft (CategoryTheory.inclusion k) α)) ≫
          (decomposed_colimit_iso_component_coproduct G).hom) =
      α.app ⟨j, X⟩ ≫ colimit.ι G ⟨j, X⟩ := by
  -- Route correction: compare at codomain `colim.obj G` directly so the final proof only uses the
  -- fixed decomposition rewrites, not any extra definitional transport.
  rw [decomposed_colimit_iso_component_coproduct_inv_postcompose]
  -- The coproduct comparison now reduces to the componentwise colimit map relation.
  calc
    colimit.ι (CategoryTheory.inclusion j ⋙ F) X ≫
        Limits.Sigma.ι
          (fun k : CategoryTheory.ConnectedComponents I =>
            colimit (CategoryTheory.inclusion k ⋙ F))
          j ≫
        Limits.Sigma.map
          (fun k : CategoryTheory.ConnectedComponents I =>
            colim.map (Functor.whiskerLeft (CategoryTheory.inclusion k) α)) ≫
        (decomposed_colimit_iso_component_coproduct G).hom =
      colimit.ι (CategoryTheory.inclusion j ⋙ F) X ≫
        colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α) ≫
        Limits.Sigma.ι
          (fun k : CategoryTheory.ConnectedComponents I =>
            colimit (CategoryTheory.inclusion k ⋙ G))
          j ≫
        (decomposed_colimit_iso_component_coproduct G).hom := by
          simpa [Category.assoc] using
            (Limits.Sigma.ι_map_assoc
              (fun k : CategoryTheory.ConnectedComponents I =>
                colim.map (Functor.whiskerLeft (CategoryTheory.inclusion k) α))
              j
              (decomposed_colimit_iso_component_coproduct G).hom)
    _ =
      (Functor.whiskerLeft (CategoryTheory.inclusion j) α).app X ≫
        colimit.ι (CategoryTheory.inclusion j ⋙ G) X ≫
        Limits.Sigma.ι
          (fun k : CategoryTheory.ConnectedComponents I =>
            colimit (CategoryTheory.inclusion k ⋙ G))
          j ≫
        (decomposed_colimit_iso_component_coproduct G).hom := by
          simpa [Category.assoc] using
            congrArg
              (fun k =>
                k ≫
                  Limits.Sigma.ι
                    (fun t : CategoryTheory.ConnectedComponents I =>
                      colimit (CategoryTheory.inclusion t ⋙ G))
                    j ≫
                  (decomposed_colimit_iso_component_coproduct G).hom)
              (ι_colimMap (Functor.whiskerLeft (CategoryTheory.inclusion j) α) X)
    _ = α.app ⟨j, X⟩ ≫ colimit.ι G ⟨j, X⟩ := by
          simpa [Functor.whiskerLeft_app, Category.assoc] using
            congrArg
              (fun k => α.app ⟨j, X⟩ ≫ k)
              (decomposed_colimit_iso_component_coproduct_ι G j X)

/-- Helper for Lemma 10.8.10: after identifying a decomposed colimit with the coproduct of the
componentwise colimits, the induced map on colimits is the coproduct of the componentwise colimit
maps. -/
private lemma decomposed_colim_map_eq_sigma_map
    {F G : CategoryTheory.Decomposed I ⥤ AddCommGrpCat} (α : F ⟶ G) :
    colim.map α =
      (decomposed_colimit_iso_component_coproduct F).inv ≫
        Limits.Sigma.map
          (fun j : CategoryTheory.ConnectedComponents I =>
            colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)) ≫
        (decomposed_colimit_iso_component_coproduct G).hom := by
  -- Route correction: the only remaining work is to compare both candidates on every colimit leg
  -- and reuse the dedicated codomain-stable leg lemma proved just above.
  apply colimit.hom_ext
  intro X
  cases X with
  | mk j X =>
      simpa using (decomposed_colim_map_eq_sigma_map_leg α j X).symm

/-- Helper for Lemma 10.8.10: each connected component inherits exact colimits from AB5 exactness
of filtered colimits in `AddCommGrpCat`. -/
private lemma component_exact_colimits_of_shape
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h)
    (j : CategoryTheory.ConnectedComponents I) :
    HasExactColimitsOfShape j.Component AddCommGrpCat.{v} := by
  -- Replace the connected component by a final directed-poset model, then invoke exactness of
  -- directed colimits in `AddCommGrpCat` on that small source and push exactness forward.
  letI : IsFiltered j.Component := connected_components_are_filtered hMap j
  letI : EssentiallySmall.{v} j.Component := by infer_instance
  letI : FinallySmall.{v} j.Component :=
    CategoryTheory.finallySmall_of_essentiallySmall (J := j.Component)
  obtain ⟨K, _, _, _, x, hx⟩ := CategoryTheory.exists_final_from_directed (𝓘 := j.Component)
  letI : PartialOrder K := inferInstance
  letI : Nonempty K := inferInstance
  letI : IsDirectedOrder K := inferInstance
  letI : x.Final := hx
  letI : AB5OfSize.{0, v} AddCommGrpCat.{v} := by
    simpa using (AB5OfSize_shrink AddCommGrpCat.{v})
  letI : HasExactColimitsOfShape K AddCommGrpCat.{v} := inferInstance
  exact hasExactColimitsOfShape_of_final AddCommGrpCat.{v} x

/-- Helper for Lemma 10.8.10: exactness of coproducts over connected components is obtained by
shrinking the component index and transporting the AB4 instance back along the discrete
equivalence. -/
private lemma connected_components_discrete_exact_colimits :
    HasExactColimitsOfShape (Discrete (CategoryTheory.ConnectedComponents I))
      AddCommGrpCat.{v} := by
  -- The source proof reduces the remaining exactness step to coproducts indexed by the set of
  -- connected components; we realize that exactness via `AB4OfSize_shrink`.
  letI : AB4OfSize.{v} AddCommGrpCat.{v} := by
    simpa using (AB4OfSize_shrink AddCommGrpCat.{v})
  exact HasExactColimitsOfShape.of_domain_equivalence AddCommGrpCat.{v}
    (Discrete.equivalence (equivShrink.{v} (CategoryTheory.ConnectedComponents I)).symm)

/-- Helper for Lemma 10.8.10: on each connected component, filtered exactness in
`AddCommGrpCat` shows that the colimit map of a monomorphism remains a monomorphism. -/
private lemma component_colim_map_mono
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h)
    (j : CategoryTheory.ConnectedComponents I)
    {F G : j.Component ⥤ AddCommGrpCat} (β : F ⟶ G) [Mono β] :
    Mono (colim.map β) := by
  -- Insert the exact filtered-colimit instance explicitly, then let the standard exactness-to-mono
  -- bridge prove that the componentwise colimit functor preserves monomorphisms.
  letI : HasExactColimitsOfShape j.Component AddCommGrpCat :=
    by simpa using (component_exact_colimits_of_shape (hMap := hMap) j)
  let hExact :
      ∀ (S : ShortComplex (j.Component ⥤ AddCommGrpCat)), S.Exact →
        (S.map (colim : (j.Component ⥤ AddCommGrpCat) ⥤ AddCommGrpCat)).Exact :=
    fun S hS ↦ by
      -- Read exactness of the colimit functor through the chosen colimit cocones.
      simpa using
        (Limits.colim.exact_mapShortComplex (S := S) hS
          (hc₁ := colimit.isColimit S.X₁)
          (c₂ := colimit.cocone S.X₂) (hc₂ := colimit.isColimit S.X₂)
          (c₃ := colimit.cocone S.X₃) (hc₃ := colimit.isColimit S.X₃)
          (f := colim.map S.f) (g := colim.map S.g)
          (fun X ↦ colimit.ι_map S.f X) (fun X ↦ colimit.ι_map S.g X))
  letI :
      (colim : (j.Component ⥤ AddCommGrpCat) ⥤ AddCommGrpCat).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_map_exact _ hExact
  infer_instance

/-- Helper for Lemma 10.8.10: the coproduct of componentwise monomorphisms in `AddCommGrpCat`
is again a monomorphism. -/
private lemma sigma_map_mono_via_ab4
    {A B : CategoryTheory.ConnectedComponents I → AddCommGrpCat}
    (p : ∀ j : CategoryTheory.ConnectedComponents I, A j ⟶ B j)
    [∀ j, Mono (p j)] :
    Mono (Limits.Sigma.map p) := by
  -- Transport exactness of coproducts to the discrete connected-component index and then apply
  -- the same exactness-to-mono bridge to the discrete-shape colimit functor.
  letI : HasExactColimitsOfShape (Discrete (CategoryTheory.ConnectedComponents I)) AddCommGrpCat :=
    by simpa using (connected_components_discrete_exact_colimits (I := I))
  let hExact :
      ∀ (S : ShortComplex (Discrete (CategoryTheory.ConnectedComponents I) ⥤ AddCommGrpCat)),
        S.Exact →
          (S.map (colim :
            (Discrete (CategoryTheory.ConnectedComponents I) ⥤ AddCommGrpCat) ⥤
              AddCommGrpCat)).Exact :=
    fun S hS ↦ by
      -- Exactness of coproducts is exactness of colimits over the discrete index.
      simpa using
        (Limits.colim.exact_mapShortComplex (S := S) hS
          (hc₁ := colimit.isColimit S.X₁)
          (c₂ := colimit.cocone S.X₂) (hc₂ := colimit.isColimit S.X₂)
          (c₃ := colimit.cocone S.X₃) (hc₃ := colimit.isColimit S.X₃)
          (f := colim.map S.f) (g := colim.map S.g)
          (fun X ↦ colimit.ι_map S.f X) (fun X ↦ colimit.ι_map S.g X))
  letI :
      (colim :
        (Discrete (CategoryTheory.ConnectedComponents I) ⥤ AddCommGrpCat) ⥤
          AddCommGrpCat).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_map_exact _ hExact
  let φ : Discrete (CategoryTheory.ConnectedComponents I) ⥤ AddCommGrpCat :=
    Discrete.functor A
  let ψ : Discrete (CategoryTheory.ConnectedComponents I) ⥤ AddCommGrpCat :=
    Discrete.functor B
  let η : φ ⟶ ψ := Discrete.natTrans fun j => p j.as
  letI : ∀ X, Mono (η.app X) := fun j ↦ by
    change Mono (p j.as)
    infer_instance
  letI : Mono η := by
    exact NatTrans.mono_of_mono_app η
  -- Compute the sigma map as the discrete-shape colimit map between the standard coproduct
  -- cocones.
  exact Limits.colim.map_mono' η
    (Limits.coproductIsCoproduct' φ)
    (Limits.coproductIsCoproduct' ψ)
    (Limits.Sigma.map p)
    (fun j ↦ by simpa [η, φ, ψ] using Limits.Sigma.ι_map p j.as)

/-- Lemma 10.8.10: if the index category `I` satisfies the hypotheses of Categories, Lemma 4.19.8,
then taking colimits of diagrams of abelian groups over `I` is exact. The owner abstraction is the
instance `HasExactColimitsOfShape I AddCommGrpCat`. -/
@[stacks 04B0]
instance abelian_group_colimits_exact
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    HasExactColimitsOfShape I AddCommGrpCat := by
  -- Route correction: keep the source decomposition route, but now the only work is to prove that
  -- the decomposed colimit functor preserves monomorphisms by factoring it through the component
  -- colimits and the coproduct over connected components.
  letI :
      (colim : (CategoryTheory.Decomposed I ⥤ AddCommGrpCat) ⥤ AddCommGrpCat).PreservesMonomorphisms := by
    refine ⟨?_⟩
    intro F G α hα
    have hComponent :
        ∀ j : CategoryTheory.ConnectedComponents I,
          Mono (colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)) := by
      intro j
      letI : ∀ X, Mono ((Functor.whiskerLeft (CategoryTheory.inclusion j) α).app X) := fun X ↦ by
        change Mono (α.app ⟨j, X⟩)
        infer_instance
      letI : Mono (Functor.whiskerLeft (CategoryTheory.inclusion j) α) := by
        exact NatTrans.mono_of_mono_app (Functor.whiskerLeft (CategoryTheory.inclusion j) α)
      exact component_colim_map_mono hMap j (Functor.whiskerLeft (CategoryTheory.inclusion j) α)
    letI :
        ∀ j : CategoryTheory.ConnectedComponents I,
          Mono (colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)) := hComponent
    have hSigma :
        Mono
          (Limits.Sigma.map
            (fun j : CategoryTheory.ConnectedComponents I =>
              colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α))) :=
      sigma_map_mono_via_ab4
        (fun j : CategoryTheory.ConnectedComponents I =>
          colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α))
    letI :
        Mono
          (Limits.Sigma.map
            (fun j : CategoryTheory.ConnectedComponents I =>
              colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α))) := hSigma
    haveI : Mono ((decomposed_colimit_iso_component_coproduct F).inv) := by infer_instance
    have hInvSigma :
        Mono
          ((decomposed_colimit_iso_component_coproduct F).inv ≫
            Limits.Sigma.map
              (fun j : CategoryTheory.ConnectedComponents I =>
                colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α))) :=
      by
        constructor
        intro Z u v huv
        apply (cancel_mono ((decomposed_colimit_iso_component_coproduct F).inv)).1
        apply (cancel_mono
          (Limits.Sigma.map
            (fun j : CategoryTheory.ConnectedComponents I =>
              colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)))).1
        simpa [Category.assoc] using huv
    haveI :
        Mono
          ((decomposed_colimit_iso_component_coproduct F).inv ≫
            Limits.Sigma.map
              (fun j : CategoryTheory.ConnectedComponents I =>
                colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α))) := hInvSigma
    have hComp :
        Mono
          (((decomposed_colimit_iso_component_coproduct F).inv ≫
              Limits.Sigma.map
                (fun j : CategoryTheory.ConnectedComponents I =>
                  colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α))) ≫
            (decomposed_colimit_iso_component_coproduct G).hom) :=
      by
        constructor
        intro Z u v huv
        apply (cancel_mono
          ((decomposed_colimit_iso_component_coproduct F).inv ≫
            Limits.Sigma.map
              (fun j : CategoryTheory.ConnectedComponents I =>
                colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)))).1
        apply (cancel_mono ((decomposed_colimit_iso_component_coproduct G).hom)).1
        simpa [Category.assoc] using huv
    rw [decomposed_colim_map_eq_sigma_map α]
    simpa [Category.assoc] using hComp
  letI : HasExactColimitsOfShape (CategoryTheory.Decomposed I) AddCommGrpCat :=
    hasExactColimitsOfShape_of_preservesMono AddCommGrpCat (CategoryTheory.Decomposed I)
  -- Transport exactness back along the canonical decomposition equivalence.
  exact
    (HasExactColimitsOfShape.of_domain_equivalence
      (C := AddCommGrpCat)
      (J := CategoryTheory.Decomposed I)
      (J' := I)
      (CategoryTheory.decomposedEquiv (J := I)))

end
