import Mathlib
import Mathlib.Algebra.Category.CommAlgCat.Basic
import StacksProject_2024.Chap10.Lemma_10_37_17
import StacksProject_2024.Chap10.Lemma_10_39_3
import StacksProject_2024.Chap10.Lemma_10_39_16

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open CategoryTheory.Under
open CommRingCat
open CommRingCat.Hom

universe u v

/- Domain-style sampling for Lemma 10.39.20:
- primary domain: filtered colimits of commutative `R`-algebras in `Under (CommRingCat.of R)`;
- sampled owner declarations:
  `RingHom.FaithfullyFlat`,
  `CategoryTheory.MorphismProperty.IsStableUnderFilteredColimits`,
  `PrimeSpectrum.comap_surjective_of_faithfullyFlat`,
  `flat_of_isColimit_filtered_system`;
- best owner abstraction: filtered-colimit stability of the morphism property
  `fun f : A ⟶ B ↦ (hom f).FaithfullyFlat`, with the source-facing `Under` theorem below as a
  wrapper around that owner statement;
- primitive data: a filtered diagram `F`, a colimit cocone `c`, and the stagewise owner property
  `(hom (F.obj j).hom).FaithfullyFlat`;
- derived API: the source-facing cocone-point and chosen-colimit faithful-flatness conclusions.

Source/core/bridge triage:
- `source-facing`: faithful flatness of the structural map of a filtered colimit `R`-algebra;
- `core/canonical`: `RingHom.FaithfullyFlat` organized as a morphism property stable under filtered
  colimits;
- `bridge/view`: the `Under (CommRingCat.of R)` presentation, whose underlying ring diagram is the
  target of the owner stability statement.
-/

section

variable {R : Type u} [CommRing R]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ Under (CommRingCat.of R))

namespace RingHom.FaithfullyFlat

-- Proof sketch: use `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`. For flatness, forget
-- the diagram to `R`-modules and apply Lemma `10.39.3` to the underlying filtered colimit. For
-- surjectivity on prime spectra, pick any stage and lift a prime of `R` there via
-- `PrimeSpectrum.comap_surjective_of_faithfullyFlat`; then compose with the cocone map and rewrite
-- with `PrimeSpectrum.comap_comp_apply` and `Under.w`.
/-- Faithful flatness is stable under filtered colimits of commutative-ring morphisms. -/
instance isStableUnderFilteredColimits :
    CategoryTheory.MorphismProperty.IsStableUnderFilteredColimits
      (fun {A B : CommRingCat} (f : A ⟶ B) ↦ (hom f).FaithfullyFlat) := by
  -- TODO: package the fixed-base theorem below into the general morphism-property statement by
  -- base-changing an arbitrary filtered natural transformation along the source colimit cocone.
  sorry

end RingHom.FaithfullyFlat

/-- Helper for Lemma 10.39.20: any colimit cocone of a filtered diagram of nontrivial
commutative rings has a nontrivial cocone point. -/
theorem nontrivial_of_isColimit_filtered_system
    (G : J ⥤ CommRingCat.{max u v}) (c : Cocone G) (hc : IsColimit c)
    [∀ j, Nontrivial (G.obj j)] :
    Nontrivial ↑c.pt := by
  -- Proof comment: transport to the canonical filtered-colimit cocone, where nontriviality is
  -- already available from the earlier filtered-colimit theorem.
  let e := hc.coconePointUniqueUpToIso (CommRingCat.FilteredColimits.colimitCoconeIsColimit G)
  letI : Nontrivial ((CommRingCat.FilteredColimits.colimitCocone G).pt) :=
    filtered_colimit_nontrivial G
  obtain ⟨x, y, hxy⟩ :=
    Nontrivial.exists_pair_ne (α := (CommRingCat.FilteredColimits.colimitCocone G).pt)
  exact ⟨e.symm.commRingCatIsoToRingEquiv x, e.symm.commRingCatIsoToRingEquiv y, fun h ↦
    hxy (e.symm.commRingCatIsoToRingEquiv.injective h)⟩

/-- Helper for Lemma 10.39.20: after quotienting by a maximal ideal, each faithfully flat stage
has a nontrivial closed fiber. -/
theorem stage_pushout_nontrivial_of_faithfully_flat
    {j : J} (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat)
    (m : Ideal R) [m.IsMaximal] :
    Nontrivial (((Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk m))).obj (F.obj j)).right) := by
  letI : Algebra R (F.obj j).right := (F.obj j).hom.hom.toAlgebra
  letI : Module R (F.obj j).right := (F.obj j).hom.hom.toAlgebra.toModule
  letI : Module.FaithfullyFlat R (F.obj j).right := by
    exact
      (RingHom.faithfullyFlat_algebraMap_iff
        (R := R) (S := (F.obj j).right)).mp <| by
          simpa [RingHom.algebraMap_toAlgebra] using hF j
  have hm_ne_top : m ≠ ⊤ := (inferInstance : m.IsMaximal).ne_top
  letI : Nontrivial (R ⧸ m) := by
    exact (Ideal.Quotient.nontrivial_iff).2 hm_ne_top
  letI : Nontrivial (TensorProduct R (R ⧸ m) ((F.obj j).right)) := by
    exact
      (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left
        (R := R) (M := R ⧸ m) (N := (F.obj j).right)).2 inferInstance
  let e :=
    CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of (R ⧸ m)) (F.obj j)
  -- Proof comment: the pushout-model fiber ring is canonically the tensor-product fiber ring.
  obtain ⟨x, y, hxy⟩ :=
    Nontrivial.exists_pair_ne (α := TensorProduct R (R ⧸ m) ((F.obj j).right))
  have hinj : Function.Injective e.hom.right :=
    (ConcreteCategory.bijective_of_isIso e.hom.right).injective
  exact ⟨e.hom.right x, e.hom.right y, fun h ↦ hxy (hinj h)⟩

/-- Helper for Lemma 10.39.20: forgetting a filtered diagram of commutative `R`-algebras to
`R`-modules sends stagewise flatness to flatness of the colimit algebra. -/
theorem flat_of_isColimit_filtered_system_under
    (c : Cocone F) (hc : IsColimit c) (hF : ∀ j, (hom (F.obj j).hom).Flat) :
    (hom c.pt.hom).Flat := by
  -- Route correction: the remaining source-faithful work is to package the explicit underlying
  -- `ModuleCat R` diagram of `F`, prove its cocone is colimiting by reflecting through
  -- `forget (ModuleCat R)` and comparing with the forgotten `CommRingCat` colimit cocone, and
  -- then apply Lemma `10.39.3` to that module diagram.
  -- TODO: build the `ModuleCat` diagram with universe-stable forgetful comparison to the ring
  -- cocone, then invoke `flat_of_isColimit_filtered_system`.
  sorry

/-- Helper for Lemma 10.39.20: after quotienting by a maximal ideal, the pushed-out colimit
ring stays nontrivial because filtered colimits preserve the inequality `1 ≠ 0`. -/
theorem pushout_colimit_nontrivial_of_filtered_faithfully_flat_system
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat)
    (m : Ideal R) [m.IsMaximal] :
    Nontrivial (((Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk m))).obj c.pt).right) := by
  -- Route correction: the remaining structural step is to package the pushed-out diagram in a
  -- universe-stable `CommRingCat` universe so that `Under.pushout` and
  -- `nontrivial_of_isColimit_filtered_system` agree definitionally on the same codomain category.
  -- TODO: compare the literal pushed-out diagram with the rebundled `CommRingCat` diagram used by
  -- `nontrivial_of_isColimit_filtered_system`, then apply stagewise nontriviality.
  sorry

/-- Helper for Lemma 10.39.20: a nontrivial pushed-out colimit over `R ⧸ m` yields a prime of the
colimit ring whose contraction back to `R` is the maximal ideal `m`. -/
theorem pushout_colimit_closed_point_lift
    (c : Cocone F) (m : Ideal R) [m.IsMaximal]
    [Nontrivial (((Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk m))).obj c.pt).right)] :
    (⟨m, inferInstance⟩ : PrimeSpectrum R) ∈
      Set.range (PrimeSpectrum.comap (hom c.pt.hom)) := by
  classical
  obtain ⟨y'⟩ := PrimeSpectrum.nonempty_iff_nontrivial.mpr
    (show Nontrivial (((Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk m))).obj c.pt).right)
      from inferInstance)
  let y : PrimeSpectrum c.pt.right :=
    PrimeSpectrum.comap
      (pushout.inl c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom y'
  refine ⟨y, ?_⟩
  -- Proof comment: contract first along the pushout leg into `c.pt.right`, then rewrite the
  -- composite through the quotient square and use maximality to identify the contraction.
  change PrimeSpectrum.comap
      ((pushout.inl c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom.comp
        (hom c.pt.hom)) y' = _
  rw [show
      (pushout.inl c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom.comp (hom c.pt.hom) =
        (pushout.inr c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom.comp
          (Ideal.Quotient.mk m) by
        simpa using congrArg CommRingCat.Hom.hom
          (pushout.condition (f := c.pt.hom)
            (g := CommRingCat.ofHom (Ideal.Quotient.mk m)))]
  change PrimeSpectrum.comap (Ideal.Quotient.mk m)
      (PrimeSpectrum.comap
        (pushout.inr c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom y') = _
  apply PrimeSpectrum.ext
  -- Proof comment: every contraction from the quotient ring contains the kernel of the quotient
  -- map, which is exactly `m`.
  have hle :
      m ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk m)
        (PrimeSpectrum.comap
          (pushout.inr c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom y')).asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal, Ideal.mk_ker] using
      (Ideal.ker_le_comap (Ideal.Quotient.mk m))
  exact
    (Ideal.IsMaximal.eq_of_le
      (I := m)
      (J := (PrimeSpectrum.comap (Ideal.Quotient.mk m)
        (PrimeSpectrum.comap
          (pushout.inr c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom y')).asIdeal)
      (show m.IsMaximal from inferInstance)
      (PrimeSpectrum.comap (Ideal.Quotient.mk m)
        (PrimeSpectrum.comap
          (pushout.inr c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom y')).2.ne_top
      hle).symm

/-- Helper for Lemma 10.39.20: every closed point of `Spec R` lifts to the colimit ring of a
filtered faithfully flat system. -/
theorem closed_points_subset_range_of_filtered_faithfully_flat_system
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat) :
    closedPoints (PrimeSpectrum R) ⊆
      Set.range (PrimeSpectrum.comap (hom c.pt.hom)) := by
  intro x hx
  have hxmax : x.asIdeal.IsMaximal := by
    -- Proof comment: a closed point of the prime spectrum is exactly a maximal ideal.
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp (by simpa [closedPoints] using hx)
  letI : x.asIdeal.IsMaximal := hxmax
  letI :
      Nontrivial (((Under.pushout
        (CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal))).obj c.pt).right) :=
    pushout_colimit_nontrivial_of_filtered_faithfully_flat_system
      (F := F) c hc hF x.asIdeal
  -- Proof comment: the nontrivial quotient fiber over the closed point supplies a prime of the
  -- pushed-out colimit, and its contraction gives back the original closed point.
  simpa using pushout_colimit_closed_point_lift (F := F) c x.asIdeal

-- Proof sketch: use Lemma 10.39.3 for the flatness part after forgetting the `R`-algebra diagram
-- to `R`-modules, then apply Lemma 10.39.16 to the closed-point lifting statement above.
/-- Lemma 10.39.20: if `c` is a colimit cocone of a filtered diagram of faithfully flat
commutative `R`-algebras, then its cocone point is faithfully flat over `R`. This is the
canonical filtered-diagram formulation in `Under (CommRingCat.of R)`. -/
theorem faithfullyFlat_of_isColimit_filtered_system
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat) :
    (hom c.pt.hom).FaithfullyFlat := by
  have hflat : (hom c.pt.hom).Flat :=
    flat_of_isColimit_filtered_system_under (F := F) c hc (fun j ↦ (hF j).1)
  -- Proof comment: Lemma `10.39.16` reduces faithful flatness to flatness plus the closed-point
  -- lifting statement proved above.
  rw [faithfullyFlat_iff_closedPoints_subset_range _ hflat]
  exact closed_points_subset_range_of_filtered_faithfully_flat_system F c hc hF

/-- Companion form of Lemma 10.39.20 for the chosen colimit object `colimit F`. -/
theorem faithfullyFlat_colimit_of_filtered_system
    [HasColimit F]
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat) :
    (hom (colimit F).hom).FaithfullyFlat := by
  simpa using faithfullyFlat_of_isColimit_filtered_system F (colimit.cocone F)
    (colimit.isColimit F) hF

end
