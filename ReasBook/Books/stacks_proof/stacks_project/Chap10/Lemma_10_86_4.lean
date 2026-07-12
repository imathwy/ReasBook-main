import Mathlib
import StacksProject_2024.Chap10.Definition_10_86_1
import StacksProject_2024.Chap10.Lemma_10_86_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Countable I]

local notation "AbelianGroupInverseSystem" => OrderDual I ⥤ AddCommGrpCat
local notation "invlim" => (lim : AbelianGroupInverseSystem ⥤ AddCommGrpCat)

-- Domain sampling:
-- * source-facing layer: this file proves inverse-limit exactness for short exact sequences of
--   abelian-group inverse systems.
-- * core/canonical owner: `CategoryTheory.Functor.IsMittagLeffler` on the underlying
--   `Type`-valued inverse system, recalled in `Definition_10_86_1`.
-- * relevant owner API sampled before refinement:
--   `CategoryTheory.Functor.IsMittagLeffler`,
--   `CategoryTheory.Functor.isMittagLeffler_iff_eventualRange`,
--   `CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp`,
--   `CategoryTheory.Functor.IsMittagLeffler.toPreimages`.
-- Primitive data are only the short exact sequence and the owner Mittag-Leffler hypothesis on the
-- left term; stagewise image stabilization is derived bridge API from that owner abstraction.
--
-- Proof sketch: inverse limits of abelian groups are left exact, so only surjectivity of the map
-- on limits needs proof. For a compatible family in `(C_i)`, consider the inverse system of
-- fibres `E_i = g_i⁻¹(c_i)`; exactness makes each `E_i` nonempty, and the owner hypothesis
-- `(S.X₁ ⋙ forget AddCommGrpCat).IsMittagLeffler` upgrades the induced set-valued inverse system
-- `(E_i)` to a Mittag-Leffler system. Lemma `10.86.3` then gives a compatible family in the
-- fibres, yielding a lift in `\varprojlim B_i`.
/-- Helper for Lemma 10.86.4: shorthand for the inverse limit object of an abelian-group inverse
system. -/
private abbrev inverseLimitObject (F : AbelianGroupInverseSystem) : AddCommGrpCat :=
  (lim : AbelianGroupInverseSystem ⥤ AddCommGrpCat).obj F

/-- Helper for Lemma 10.86.4: transition maps in the fibre system land in the next fibre because
the chosen point of the limit is compatible. -/
private theorem fibreInverseSystemMap_mem
    (S : ShortComplex AbelianGroupInverseSystem)
    (c : inverseLimitObject S.X₃)
    {j i : OrderDual I}
    (f : j ⟶ i)
    (x : { b : S.X₂.obj j // S.g.app j b = limit.π S.X₃ j c }) :
    S.g.app i (S.X₂.map f x.1) = limit.π S.X₃ i c := by
  -- Naturality of `g` transfers the fibre condition along the transition map.
  rw [← ConcreteCategory.comp_apply, S.g.naturality f, ConcreteCategory.comp_apply, x.2]
  exact congrArg (fun h => h c) (limit.w S.X₃ f)

/-- Helper for Lemma 10.86.4: evaluating a short exact sequence of inverse systems at a single
stage preserves short exactness. -/
private theorem stagewise_shortExact
    (S : ShortComplex AbelianGroupInverseSystem)
    (hS : S.ShortExact) (i : OrderDual I) :
    (S.map ((evaluation (OrderDual I) AddCommGrpCat).obj i)).ShortExact := by
  -- Exactness, injectivity, and surjectivity are all tested pointwise in the functor category.
  have hExact : (S.map ((evaluation (OrderDual I) AddCommGrpCat).obj i)).Exact := by
    simpa using hS.exact.map ((evaluation (OrderDual I) AddCommGrpCat).obj i)
  have hMono : Mono (((evaluation (OrderDual I) AddCommGrpCat).obj i).map S.f) := by
    have hmonoNat : Mono S.f := hS.mono_f
    exact (NatTrans.mono_iff_mono_app (f := S.f)).1 hmonoNat i
  have hEpi : Epi (((evaluation (OrderDual I) AddCommGrpCat).obj i).map S.g) := by
    have hepiNat : Epi S.g := hS.epi_g
    exact (NatTrans.epi_iff_epi_app (f := S.g)).1 hepiNat i
  exact ShortComplex.ShortExact.mk' hExact hMono hEpi

/-- Helper for Lemma 10.86.4: the fibre transition map over a compatible limit point in `X₃`. -/
private def fibreInverseSystemMap
    (S : ShortComplex AbelianGroupInverseSystem)
    (c : inverseLimitObject S.X₃)
    {j i : OrderDual I}
    (f : j ⟶ i) :
    { b : S.X₂.obj j // S.g.app j b = limit.π S.X₃ j c } →
      { b : S.X₂.obj i // S.g.app i b = limit.π S.X₃ i c } :=
  fun x ↦ ⟨S.X₂.map f x.1, fibreInverseSystemMap_mem S c f x⟩

/-- Helper for Lemma 10.86.4: the fibre transition maps respect identities. -/
private theorem fibreInverseSystemMap_id
    (S : ShortComplex AbelianGroupInverseSystem)
    (c : inverseLimitObject S.X₃)
    (i : OrderDual I) :
    fibreInverseSystemMap S c (𝟙 i) = id := by
  -- The fibre map over an identity morphism is definitionally the identity.
  funext x
  apply Subtype.ext
  simp [fibreInverseSystemMap]

/-- Helper for Lemma 10.86.4: the fibre transition maps respect composition. -/
private theorem fibreInverseSystemMap_comp
    (S : ShortComplex AbelianGroupInverseSystem)
    (c : inverseLimitObject S.X₃)
    {k j i : OrderDual I}
    (g : k ⟶ j) (f : j ⟶ i) :
    fibreInverseSystemMap S c (g ≫ f) =
      fibreInverseSystemMap S c f ∘ fibreInverseSystemMap S c g := by
  -- Composition in the fibre system is inherited from the underlying inverse system `X₂`.
  funext x
  apply Subtype.ext
  simp [fibreInverseSystemMap]

/-- Helper for Lemma 10.86.4: the inverse system of fibres of a compatible family in `X₃`. -/
private def fibreInverseSystem
    (S : ShortComplex AbelianGroupInverseSystem)
    (c : inverseLimitObject S.X₃) :
    OrderDual I ⥤ Type _ where
  obj i := { b : S.X₂.obj i // S.g.app i b = limit.π S.X₃ i c }
  map f := fibreInverseSystemMap S c f
  map_id := fibreInverseSystemMap_id S c
  map_comp := fibreInverseSystemMap_comp S c

/-- Helper for Lemma 10.86.4: every stagewise fibre is nonempty by surjectivity of the stagewise
right map in the short exact sequence. -/
private theorem fibreInverseSystem_nonempty
    (S : ShortComplex AbelianGroupInverseSystem)
    (hS : S.ShortExact)
    (c : inverseLimitObject S.X₃)
    (i : OrderDual I) :
    Nonempty ((fibreInverseSystem S c).obj i) := by
  -- Evaluating the short exact sequence at `i` gives a surjection onto the chosen stage value.
  have hStage : (S.map ((evaluation (OrderDual I) AddCommGrpCat).obj i)).ShortExact :=
    stagewise_shortExact S hS i
  obtain ⟨b, hb⟩ := hStage.ab_surjective_g (limit.π S.X₃ i c)
  exact ⟨⟨b, hb⟩⟩

/-- Helper for Lemma 10.86.4: the fibre inverse system inherits the Mittag-Leffler property from
the left inverse system via the source proof's difference argument. -/
private theorem fibre_inverse_system_isMittagLeffler
    (S : ShortComplex AbelianGroupInverseSystem)
    (hS : S.ShortExact)
    (hML : (S.X₁ ⋙ forget AddCommGrpCat).IsMittagLeffler)
    (c : inverseLimitObject S.X₃) :
    (fibreInverseSystem S c).IsMittagLeffler := by
  classical
  -- We prove stabilization of fibre images at each stage using stabilization in `X₁`.
  rw [Functor.isMittagLeffler_iff_subset_range_comp]
  intro i
  obtain ⟨j, f, hf⟩ := (Functor.isMittagLeffler_iff_subset_range_comp
    (S.X₁ ⋙ forget AddCommGrpCat)).1 hML i
  refine ⟨j, f, ?_⟩
  intro k g
  rintro _ ⟨e_j, rfl⟩
  let E := fibreInverseSystem S c
  let A := S.X₁ ⋙ forget AddCommGrpCat
  let e'_k : E.obj k := Classical.choice (fibreInverseSystem_nonempty S hS c k)
  let e'_j : E.obj j := E.map g e'_k
  have hStagej : (S.map ((evaluation (OrderDual I) AddCommGrpCat).obj j)).ShortExact :=
    stagewise_shortExact S hS j
  have hdiff_zero : S.g.app j (e_j.1 - e'_j.1) = 0 := by
    -- The difference of two lifts of the same element lies in the kernel of `g_j`.
    calc
      S.g.app j (e_j.1 - e'_j.1) = S.g.app j e_j.1 - S.g.app j e'_j.1 := by
        simp
      _ = limit.π S.X₃ j c - limit.π S.X₃ j c := by rw [e_j.2, e'_j.2]
      _ = 0 := sub_self _
  obtain ⟨a_j, ha_j⟩ := ((S.map ((evaluation (OrderDual I) AddCommGrpCat).obj j)).ab_exact_iff).1
    hStagej.exact (e_j.1 - e'_j.1) hdiff_zero
  have ha_range : A.map f a_j ∈ Set.range (A.map (g ≫ f)) := by
    -- Stabilization in `X₁` lets us realize the correction term from stage `k`.
    exact hf g ⟨a_j, rfl⟩
  obtain ⟨a_k, ha_k⟩ := ha_range
  have hzero_k : S.g.app k (S.f.app k a_k) = 0 := by
    -- The short-complex relation `g ∘ f = 0` is evaluated at stage `k`.
    simpa using (S.map ((evaluation (OrderDual I) AddCommGrpCat).obj k)).ab_zero_apply a_k
  have he_k_mem : S.g.app k (e'_k.1 + S.f.app k a_k) = limit.π S.X₃ k c := by
    -- Adding an element from `A_k` keeps us inside the fibre over `c_k`.
    calc
      S.g.app k (e'_k.1 + S.f.app k a_k)
          = S.g.app k e'_k.1 + S.g.app k (S.f.app k a_k) := by simp
      _ = limit.π S.X₃ k c + 0 := by rw [e'_k.2, hzero_k]
      _ = limit.π S.X₃ k c := by simp
  let e_k : E.obj k := ⟨e'_k.1 + S.f.app k a_k, he_k_mem⟩
  have ha_j' : e_j.1 = e'_j.1 + S.f.app j a_j := by
    -- Rewriting the exactness witness as an additive decomposition matches the source proof.
    have haux : S.f.app j a_j + e'_j.1 = e_j.1 := (eq_sub_iff_add_eq).1 ha_j
    simpa [add_comm, add_left_comm, add_assoc] using haux.symm
  have he'_j : S.X₂.map f e'_j.1 = S.X₂.map (g ≫ f) e'_k.1 := by
    -- The chosen comparison lift `e'_j` came from stage `k`.
    change S.X₂.map f (S.X₂.map g e'_k.1) = S.X₂.map (g ≫ f) e'_k.1
    simpa using congrArg (fun h => h e'_k.1) (S.X₂.map_comp g f).symm
  have hnat_f :
      S.X₂.map f (S.f.app j a_j) = S.f.app i (A.map f a_j) := by
    -- Naturality of `f` identifies mapping a correction term with correcting after mapping.
    change S.X₂.map f (S.f.app j a_j) = S.f.app i (S.X₁.map f a_j)
    simpa using congrArg (fun h => h a_j) (S.f.naturality f)
  have hnat_gf :
      S.X₂.map (g ≫ f) (S.f.app k a_k) = S.f.app i (A.map (g ≫ f) a_k) := by
    -- The same naturality identity is used for the correction term from stage `k`.
    change S.X₂.map (g ≫ f) (S.f.app k a_k) = S.f.app i (S.X₁.map (g ≫ f) a_k)
    simpa using congrArg (fun h => h a_k) (S.f.naturality (g ≫ f))
  have himage_j :
      S.X₂.map f e_j.1 = S.X₂.map f e'_j.1 + S.f.app i (A.map f a_j) := by
    -- Transport the stage-`j` additive decomposition down to stage `i`.
    calc
      S.X₂.map f e_j.1 = S.X₂.map f (e'_j.1 + S.f.app j a_j) := by rw [ha_j']
      _ = S.X₂.map f e'_j.1 + S.X₂.map f (S.f.app j a_j) := by simp
      _ = S.X₂.map f e'_j.1 + S.f.app i (A.map f a_j) := by rw [hnat_f]
  have himage_k :
      S.X₂.map (g ≫ f) e_k.1 = S.X₂.map (g ≫ f) e'_k.1 + S.f.app i (A.map (g ≫ f) a_k) := by
    -- The corrected stage-`k` element differs from `e'_k` by the transported correction term.
    calc
      S.X₂.map (g ≫ f) e_k.1 = S.X₂.map (g ≫ f) (e'_k.1 + S.f.app k a_k) := by rfl
      _ = S.X₂.map (g ≫ f) e'_k.1 + S.X₂.map (g ≫ f) (S.f.app k a_k) := by simp
      _ = S.X₂.map (g ≫ f) e'_k.1 + S.f.app i (A.map (g ≫ f) a_k) := by rw [hnat_gf]
  refine ⟨e_k, ?_⟩
  apply Subtype.ext
  -- The stage-`i` images agree because the correction term was chosen from stabilized images.
  calc
    (E.map (g ≫ f) e_k).1 = S.X₂.map (g ≫ f) e_k.1 := rfl
    _ = S.X₂.map (g ≫ f) e'_k.1 + S.f.app i (A.map (g ≫ f) a_k) := himage_k
    _ = S.X₂.map f e'_j.1 + S.f.app i (A.map f a_j) := by rw [he'_j, ha_k]
    _ = S.X₂.map f e_j.1 := himage_j.symm
    _ = (E.map f e_j).1 := rfl

/-- Helper for Lemma 10.86.4: turn a compatible family in the underlying `Type`-valued inverse
system into a point of the categorical inverse limit. -/
private noncomputable def sectionsToLimit
    (F : AbelianGroupInverseSystem)
    (s : (F ⋙ forget AddCommGrpCat).sections) :
    inverseLimitObject F :=
  (preservesLimitIso (forget AddCommGrpCat) F).inv
    ((Types.limitEquivSections (F ⋙ forget AddCommGrpCat)).symm s)

/-- Helper for Lemma 10.86.4: the point of the inverse limit attached to a section has the expected
stagewise coordinates. -/
private theorem limit_π_sectionsToLimit
    (F : AbelianGroupInverseSystem)
    (s : (F ⋙ forget AddCommGrpCat).sections)
    (i : OrderDual I) :
    limit.π F i (sectionsToLimit F s) = s.val i := by
  -- First move to the underlying `Type` limit, then evaluate the section there.
  let t : limit (F ⋙ forget AddCommGrpCat) :=
    (Types.limitEquivSections (F ⋙ forget AddCommGrpCat)).symm s
  have hπ :
      limit.π F i ((preservesLimitIso (forget AddCommGrpCat) F).inv t) =
        limit.π (F ⋙ forget AddCommGrpCat) i t := by
    exact congrArg (fun k => k t) (preservesLimitIso_inv_π (forget AddCommGrpCat) F i)
  simpa [sectionsToLimit, t] using hπ.trans (Types.limitEquivSections_symm_apply
    (F ⋙ forget AddCommGrpCat) s i)

/-- Helper for Lemma 10.86.4: a section of the fibre system forgets to a compatible family in
`X₂`. -/
private theorem fibre_sections_compatible
    (S : ShortComplex AbelianGroupInverseSystem)
    (c : inverseLimitObject S.X₃)
    (s : (fibreInverseSystem S c).sections)
    {j i : OrderDual I}
    (f : j ⟶ i) :
    S.X₂.map f (s.val j).1 = (s.val i).1 := by
  -- Compatibility is exactly the section condition after forgetting the fibre predicate.
  exact congrArg Subtype.val (s.property f)

/-- Helper for Lemma 10.86.4: forgetting the fibre predicate turns a fibre section into a section
of the middle inverse system. -/
private noncomputable def fibreSectionsToSections
    (S : ShortComplex AbelianGroupInverseSystem)
    (c : inverseLimitObject S.X₃)
    (s : (fibreInverseSystem S c).sections) :
    (S.X₂ ⋙ forget AddCommGrpCat).sections where
  val i := (s.val i).1
  property := fibre_sections_compatible S c s

/-- Helper for Lemma 10.86.4: the forgotten fibre section still maps stagewise to the chosen point
of the right inverse system. -/
private theorem g_fibreSectionsToSections
    (S : ShortComplex AbelianGroupInverseSystem)
    (c : inverseLimitObject S.X₃)
    (s : (fibreInverseSystem S c).sections)
    (i : OrderDual I) :
    S.g.app i ((fibreSectionsToSections S c s).val i) = limit.π S.X₃ i c :=
  (s.val i).2

/-- Helper for Lemma 10.86.4: surjectivity of the map on inverse limits is obtained by applying
Lemma `10.86.3` to the inverse system of fibres over a compatible family in `X₃`. -/
private theorem epi_limit_map_of_countable_and_isMittagLeffler_left
    (S : ShortComplex AbelianGroupInverseSystem)
    (hS : S.ShortExact)
    (hML : (S.X₁ ⋙ forget AddCommGrpCat).IsMittagLeffler) :
    Epi ((S.map invlim).g) := by
  classical
  rw [AddCommGrpCat.epi_iff_surjective]
  intro c
  let c' : inverseLimitObject S.X₃ := c
  have hc' : c' = c := rfl
  let E := fibreInverseSystem (I := I) S c'
  letI : ∀ i : OrderDual I, Nonempty (E.obj i) := fun i ↦ fibreInverseSystem_nonempty S hS c' i
  have hE : E.IsMittagLeffler := fibre_inverse_system_isMittagLeffler (I := I) S hS hML c'
  obtain ⟨s, hs⟩ := nonempty_sections_of_countable_mittagLeffler_inverse_system E hE
  let sE : E.sections := ⟨s, hs⟩
  let sb : (S.X₂ ⋙ forget AddCommGrpCat).sections := fibreSectionsToSections S c' sE
  refine ⟨sectionsToLimit S.X₂ sb, ?_⟩
  apply (preservesLimitIso (forget AddCommGrpCat) S.X₃).toEquiv.injective
  apply Types.limit_ext
  intro i
  have hleft :
      limit.π (S.X₃ ⋙ forget AddCommGrpCat) i
          ((preservesLimitIso (forget AddCommGrpCat) S.X₃).hom
            (((S.map invlim).g) (sectionsToLimit S.X₂ sb))) =
        limit.π S.X₃ i (((S.map invlim).g) (sectionsToLimit S.X₂ sb)) := by
    exact congrArg (fun k => k (((S.map invlim).g) (sectionsToLimit S.X₂ sb)))
      (preservesLimitIso_hom_π (forget AddCommGrpCat) S.X₃ i)
  have hright :
      limit.π (S.X₃ ⋙ forget AddCommGrpCat) i
          ((preservesLimitIso (forget AddCommGrpCat) S.X₃).hom c) =
        limit.π S.X₃ i c := by
    exact congrArg (fun k => k c) (preservesLimitIso_hom_π (forget AddCommGrpCat) S.X₃ i)
  -- Coordinatewise, the lifted family maps to the original compatible family `c`.
  have hcoord₁ :
      limit.π (S.X₃ ⋙ forget AddCommGrpCat) i
          ((preservesLimitIso (forget AddCommGrpCat) S.X₃).hom
            (((S.map invlim).g) (sectionsToLimit S.X₂ sb))) =
        limit.π S.X₃ i c' := by
    calc
      limit.π (S.X₃ ⋙ forget AddCommGrpCat) i
          ((preservesLimitIso (forget AddCommGrpCat) S.X₃).hom
            (((S.map invlim).g) (sectionsToLimit S.X₂ sb)))
        = limit.π S.X₃ i (((S.map invlim).g) (sectionsToLimit S.X₂ sb)) := hleft
      _ = S.g.app i (limit.π S.X₂ i (sectionsToLimit S.X₂ sb)) := by
        change ((limMap S.g ≫ limit.π S.X₃ i) (sectionsToLimit S.X₂ sb)) =
          ((limit.π S.X₂ i ≫ S.g.app i) (sectionsToLimit S.X₂ sb))
        simpa using congrArg (fun k => k (sectionsToLimit S.X₂ sb)) (limMap_π S.g i)
      _ = S.g.app i ((fibreSectionsToSections S c' sE).val i) := by
        rw [limit_π_sectionsToLimit]
      _ = limit.π S.X₃ i c' := g_fibreSectionsToSections S c' sE i
  have hcoord₂ :
      limit.π S.X₃ i c' =
        limit.π (S.X₃ ⋙ forget AddCommGrpCat) i
          ((preservesLimitIso (forget AddCommGrpCat) S.X₃).hom c) := by
    simpa [hc'] using hright.symm
  exact hcoord₁.trans hcoord₂

/-- Lemma 10.86.4: for a short exact sequence `0 ⟶ (A_i) ⟶ (B_i) ⟶ (C_i) ⟶ 0` of directed
inverse systems of abelian groups over a countable directed preorder `I`, if `(A_i)` is
Mittag-Leffler, then the induced sequence
`0 ⟶ \varprojlim_i A_i ⟶ \varprojlim_i B_i ⟶ \varprojlim_i C_i ⟶ 0`
is short exact. -/
@[stacks 0598]
theorem inverseSystem_limit_shortExact_of_countable_and_isMittagLeffler_left
    (S : ShortComplex AbelianGroupInverseSystem)
    (hS : S.ShortExact)
    (hML : (S.X₁ ⋙ forget AddCommGrpCat).IsMittagLeffler) :
    (S.map invlim).ShortExact := by
  -- Inverse limits are left exact, so exactness and injectivity come from kernel preservation.
  have hExact : (S.map invlim).Exact := by
    have hmono : Mono S.f := hS.mono_f
    simpa using hS.exact.map_of_mono_of_preservesKernel invlim hmono inferInstance
  have hMono : Mono (S.map invlim).f := by
    -- Coordinatewise injectivity on the evaluated short exact sequences forces injectivity on the limit.
    rw [AddCommGrpCat.mono_iff_injective]
    intro x y hxy
    apply (preservesLimitIso (forget AddCommGrpCat) S.X₁).toEquiv.injective
    apply Types.limit_ext
    intro i
    have hStage : (S.map ((evaluation (OrderDual I) AddCommGrpCat).obj i)).ShortExact :=
      stagewise_shortExact S hS i
    have hleft :
        limit.π (S.X₁ ⋙ forget AddCommGrpCat) i
            ((preservesLimitIso (forget AddCommGrpCat) S.X₁).hom x) =
          limit.π S.X₁ i x := by
      exact congrArg (fun k => k x) (preservesLimitIso_hom_π (forget AddCommGrpCat) S.X₁ i)
    have hright :
        limit.π (S.X₁ ⋙ forget AddCommGrpCat) i
            ((preservesLimitIso (forget AddCommGrpCat) S.X₁).hom y) =
          limit.π S.X₁ i y := by
      exact congrArg (fun k => k y) (preservesLimitIso_hom_π (forget AddCommGrpCat) S.X₁ i)
    change
      limit.π (S.X₁ ⋙ forget AddCommGrpCat) i
          ((preservesLimitIso (forget AddCommGrpCat) S.X₁).hom x) =
        limit.π (S.X₁ ⋙ forget AddCommGrpCat) i
          ((preservesLimitIso (forget AddCommGrpCat) S.X₁).hom y)
    rw [hleft, hright]
    apply hStage.ab_injective_f
    calc
      S.f.app i (limit.π S.X₁ i x)
          = limit.π S.X₂ i (((S.map invlim).f) x) := by
              change ((limit.π S.X₁ i ≫ S.f.app i) x) = ((limMap S.f ≫ limit.π S.X₂ i) x)
              simpa using (congrArg (fun k => k x) (limMap_π S.f i)).symm
      _ = limit.π S.X₂ i (((S.map invlim).f) y) := congrArg (fun z => limit.π S.X₂ i z) hxy
      _ = S.f.app i (limit.π S.X₁ i y) := by
              change ((limMap S.f ≫ limit.π S.X₂ i) y) = ((limit.π S.X₁ i ≫ S.f.app i) y)
              simpa using congrArg (fun k => k y) (limMap_π S.f i)
  -- The only nonformal part is surjectivity, handled by the fibre-system argument above.
  exact ShortComplex.ShortExact.mk' hExact hMono
    (epi_limit_map_of_countable_and_isMittagLeffler_left S hS hML)
