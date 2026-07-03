import Mathlib
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Homology.CochainComplexPlus

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_10_1 (from Chap21) -/
open CategoryTheory Opposite

noncomputable section

universe u v

namespace CategoryTheory

/-- Lemma 21.10.1: an injective abelian sheaf on a site is injective as an object of the category
of abelian presheaves. -/
-- Proof sketch: apply Lemma `12.29.1` to the sheafification adjunction
-- `presheafToSheaf J AddCommGrpCat ⊣ sheafToPresheaf J AddCommGrpCat`. Exactness of abelian
-- sheafification gives preservation of injective objects by the right adjoint.
theorem injective_underlying_abelian_presheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : Sheaf J AddCommGrpCat.{max u v}) (hF : Injective F) :
    Injective ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj F) := sorry

end CategoryTheory

/-! ### Lemma_21_10_2 (from Chap21) -/
open CategoryTheory Opposite CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {U : C} {ι : Type (max u v)}
variable [Limits.HasFiniteProducts (Over U)]

-- Proof sketch: use Lemma `21.10.1` to regard `ℐ` as an injective abelian presheaf, then apply
-- Lemma `21.9.6` to the Čech cohomology functors of the covering family. The degree-zero case is
-- identified with sections over `U` by the sheaf condition from Lemma `21.8.2`, while positive
-- degrees vanish because higher right derived functors of a left exact functor vanish on
-- injective objects.
/-- Lemma 21.10.2: for a covering family `family : ι → Over U` on the slice site `(C / U, J.over
U)` and an injective abelian sheaf `ℐ`, the Čech cohomology of the underlying abelian presheaf is
the group of sections `ℐ(U)` in degree `0` and is zero in every positive degree. -/
theorem cechCohomology_of_injective_sheaf
    (family : ι → Over U) (hfamily : (J.over U).CoversTop family)
    (ℐ : Sheaf J AddCommGrpCat.{max u v}) (hℐ : Injective ℐ) (p : ℕ) :
    if hp : p = 0 then
      IsIsomorphic
        (cechCohomology U family ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj ℐ) p)
        (ℐ.1.obj (op U))
    else
      Limits.IsZero
        (cechCohomology U family ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj ℐ) p) :=
  sorry

-- Proof sketch: specialize `cechCohomology_of_injective_sheaf` to `p = 0`; the `if` reduces to
-- the degree-zero branch, which is the sheaf-condition identification of Čech `H^0` with
-- sections over `U`.
/-- The degree-zero Čech cohomology of an injective abelian sheaf is canonically isomorphic to its
sections over the covered object. -/
theorem cechCohomology_zero_of_injective_sheaf
    (family : ι → Over U) (hfamily : (J.over U).CoversTop family)
    (ℐ : Sheaf J AddCommGrpCat.{max u v}) (hℐ : Injective ℐ) :
    IsIsomorphic
      (cechCohomology U family ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj ℐ) 0)
      (ℐ.1.obj (op U)) :=
  sorry

-- Proof sketch: regard `ℐ` as injective in abelian presheaves by Lemma `21.10.1`, then identify
-- `\check H^p` with the `p`-th right derived functor of `\check H^0` using Lemma `21.9.6`.
-- Positive derived functors vanish on injective objects, so the resulting Čech cohomology object
-- is zero.
/-- In every positive degree, the Čech cohomology of an injective abelian sheaf vanishes. -/
theorem cechCohomology_isZero_of_pos_of_injective_sheaf
    (family : ι → Over U) (hfamily : (J.over U).CoversTop family)
    (ℐ : Sheaf J AddCommGrpCat.{max u v}) (hℐ : Injective ℐ)
    (p : ℕ) (hp : 0 < p) :
    Limits.IsZero
      (cechCohomology U family ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj ℐ) p) :=
  sorry

end CategoryTheory

/-! ### Lemma_21_10_3 (from Chap21) -/
open CategoryTheory Opposite

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat]
variable [EnoughInjectives (Sheaf J AddCommGrpCat)]

attribute [local instance] HasDerivedCategory.standard

section

variable (U : C) [Limits.HasFiniteProducts (Over U)]
variable {ι : Type (max u v)} (family : ι → Over U)

/-- The Čech complex functor on abelian sheaves, obtained by forgetting to abelian presheaves and
then applying the Čech complex on the slice site over `U`. -/
abbrev cechComplexOnAbelianSheaves :
    Sheaf J AddCommGrpCat ⥤ CochainComplex AddCommGrpCat ℕ :=
  sheafToPresheaf J AddCommGrpCat ⋙ cechComplexOnPresheaves U family

-- Proof sketch: extending an `ℕ`-indexed cochain complex along `embeddingUpNat` produces a
-- `ℤ`-indexed cochain complex that is strictly zero in negative degrees, so it is bounded below.
/-- The extended Čech complex of an abelian sheaf is bounded below as a `\mathbf Z`-indexed
cochain complex. -/
theorem cechComplexOnAbelianSheavesToPlus_obj_mem
    (F : Sheaf J AddCommGrpCat) :
    CochainComplex.plus AddCommGrpCat
      (((cechComplexOnAbelianSheaves U family).obj F).extend ComplexShape.embeddingUpNat) := sorry

/-- The Čech complex functor on abelian sheaves, regarded as a bounded-below cochain-complex
functor so that it can be viewed in `D^+(\mathbf Z)`. -/
abbrev cechComplexOnAbelianSheavesToPlus :
    Sheaf J AddCommGrpCat ⥤ CochainComplex.Plus AddCommGrpCat :=
  (CochainComplex.plus AddCommGrpCat).lift
    ((cechComplexOnAbelianSheaves U family) ⋙
      (ComplexShape.embeddingUpNat).extendFunctor AddCommGrpCat)
    (fun F ↦ cechComplexOnAbelianSheavesToPlus_obj_mem U family F)

/-- The functor sending an abelian sheaf to its Čech complex for the covering `family`, viewed as
an object of the bounded-below derived category `D^+(\mathbf Z)`. -/
abbrev abelianSheafCechDerivedFunctor :
    Sheaf J AddCommGrpCat ⥤ boundedBelowDerivedCategory AddCommGrpCat :=
  cechComplexOnAbelianSheavesToPlus U family ⋙
    boundedBelowCochainComplexToDerivedBelow (𝟭 AddCommGrpCat)

/-- Sections over a fixed object of the site define an additive functor on abelian sheaves. -/
local instance sheafSectionsFunctor_additive :
    (((sheafSections J AddCommGrpCat).obj (op U))).Additive := sorry

/-- The bounded-below derived global-sections functor `RΓ(U,-)` on abelian sheaves over the site.
-/
abbrev abelianSheafDerivedSectionsFunctor :
    Sheaf J AddCommGrpCat ⥤ boundedBelowDerivedCategory AddCommGrpCat :=
  degreeZeroToBoundedBelowDerived ((sheafSections J AddCommGrpCat).obj (op U))

/-- The degree-`p` Čech cohomology functor on abelian sheaves for the covering `family`. -/
abbrev abelianSheafCechCohomologyFunctor (p : ℕ) :
    Sheaf J AddCommGrpCat ⥤ AddCommGrpCat :=
  sheafToPresheaf J AddCommGrpCat ⋙ (cechCohomologyDegree U family p).obj

/-- The degree-`p` site cohomology functor `\mathcal F \mapsto H^p(U, \mathcal F)` on abelian
sheaves. -/
abbrev abelianSheafSiteCohomologyFunctor (p : ℕ) :
    Sheaf J AddCommGrpCat ⥤ AddCommGrpCat :=
  ((sheafSections J AddCommGrpCat).obj (op U)).rightDerived p

-- Proof sketch: choose an injective resolution `ℱ ⟶ ℐ^•`, form the double complex
-- `\check{\mathcal C}^\bullet(\mathcal U, \mathcal I^\bullet)`, and compare both
-- `\check{\mathcal C}^\bullet(\mathcal U, \mathcal F)` and `\Gamma(U,\mathcal I^\bullet)` with
-- its total complex. Lemma `21.10.2` gives acyclicity of the rows for injectives, so
-- Lemma `12.25.4` makes the comparison from sections a quasi-isomorphism. Passing to `D^+`
-- yields the required natural transformation from the Čech complex functor to `RΓ(U,-)`.
/-- Lemma 21.10.3: for a covering family `family : ι → Over U` on the slice site `(C / U,
J.over U)`, there exists a natural transformation from the Čech complex functor
`\check{\mathcal C}^\bullet(\mathcal U,-)` to the bounded-below derived global-sections functor
`RΓ(U,-)` on abelian sheaves, both viewed as functors `\mathrm{Ab}(C) ⥤ D^+(\mathbf Z)`. -/
theorem cechDerivedFunctor_exists_natTrans_to_derivedSections
    (hfamily : (J.over U).CoversTop family) :
    ∃ τ :
      (abelianSheafCechDerivedFunctor U family :
        Sheaf J AddCommGrpCat ⥤ boundedBelowDerivedCategory AddCommGrpCat) ⟶
        abelianSheafDerivedSectionsFunctor U,
      True := sorry

-- Proof sketch: apply the cohomology functor `H^p` to the derived-category transformation from
-- `cechDerivedFunctor_exists_natTrans_to_derivedSections`. The source identifies with the degree
-- `p` Čech cohomology functor by construction of the bounded-below complex, and the target is the
-- `p`-th right derived functor of sections, i.e. `H^p(U,-)`.
/-- The derived Čech-to-cohomology comparison induces a degree-`p` natural transformation
`\check H^p(U,-) \to H^p(U,-)` on abelian sheaves. -/
theorem cechCohomology_exists_natTrans_to_siteCohomology
    (hfamily : (J.over U).CoversTop family) (p : ℕ) :
    ∃ τ :
      (abelianSheafCechCohomologyFunctor U family p :
        Sheaf J AddCommGrpCat ⥤ AddCommGrpCat) ⟶
        abelianSheafSiteCohomologyFunctor U p,
      True := sorry

end

end CategoryTheory

/-! ### Lemma_21_10_4 (from Chap21) -/
open CategoryTheory Opposite Limits

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace AbelianSheafTorsor

variable {H : Sheaf J AddCommGrpCat.{w}}

-- Proof sketch: evaluate the underlying sheaf isomorphism at the chosen object of the site; the
-- inverse isomorphism transports any local section back, so section-existence is preserved.
/-- An isomorphism of abelian sheaf torsors preserves the existence of a section over any object of
the site. -/
theorem nonempty_sections_iff_of_iso {P Q : AbelianSheafTorsor H} (e : P ≅ Q) (U : C) :
    Nonempty (P.carrier.1.obj (op U)) ↔ Nonempty (Q.carrier.1.obj (op U)) := sorry

namespace IsoClasses

variable {ι : Type w} (V : ι → C)

/-- An isomorphism class of torsors is trivial on the covering family `V` if any representative
admits a section over every object `V i`. -/
abbrev IsTrivialOnCover (c : AbelianSheafTorsor.IsoClasses H) : Prop :=
  Quot.liftOn c
    (fun P : AbelianSheafTorsor H ↦ ∀ i : ι, Nonempty (P.carrier.1.obj (op (V i))))
    (fun _ _ hPQ ↦ propext <|
      hPQ.elim fun e ↦
        forall_congr' fun i ↦ AbelianSheafTorsor.nonempty_sections_iff_of_iso e (V i))

-- Proof sketch: this is immediate from the quotient-lift definition of `IsTrivialOnCover`.
/-- A representative torsor is trivial on `V` exactly when its isomorphism class is. -/
theorem isTrivialOnCover_quot_mk_iff (P : AbelianSheafTorsor H) :
    (show AbelianSheafTorsor.IsoClasses H from Quot.mk _ P).IsTrivialOnCover V ↔
      ∀ i : ι, Nonempty (P.carrier.1.obj (op (V i))) := sorry

end IsoClasses
end AbelianSheafTorsor

variable {U : C} {ι : Type w}
variable [HasFiniteProducts (Over U)]

-- Proof sketch: choose local sections on the covering family `V`, take their pairwise
-- differences to obtain a Čech `1`-cocycle on the slice site `(C/U, J.over U)`, and check that
-- changing the local sections changes the cocycle by a coboundary. Conversely, glue trivial
-- torsors on the cover using a Čech `1`-cocycle. This yields the subset of torsor classes inside
-- `H¹(U, G)` singled out by Lemma `21.4.3`, hence the usual comparison map from Čech cohomology
-- to sheaf cohomology is injective.
/-- Lemma 21.10.4: via the torsor classification of Lemma 21.4.3 on the slice site `(C/U, J.over
U)`, the degree-one Čech cohomology of a covering family `V : ι → Over U` is identified with the
isomorphism classes of `(G.over U)`-torsors whose restriction to every `V i` is trivial,
equivalently whose underlying sheaf on `(C/U, J.over U)` has a section over each `V i`. -/
theorem cech_H1_equiv_torsorIsoClasses_isTrivialOnCover
    (V : ι → Over U) (hV : (J.over U).CoversTop V) (G : Sheaf J AddCommGrpCat.{w}) :
    Nonempty ((cechCohomology U V ((sheafToPresheaf J AddCommGrpCat.{w}).obj G) 1) ≃
      { c : AbelianSheafTorsor.IsoClasses (G.over U) // c.IsTrivialOnCover V }) := sorry

end CategoryTheory

/-! ### Lemma_21_10_5 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]
variable [HasInjectiveResolutions (Sheaf J AddCommGrpCat)]

/-
Domain-style sampling for Lemma 21.10.5:
- primary domain: right derived functors of the canonical inclusion `sheafToPresheaf` for abelian
  sheaves on a site, and the canonical cohomology-presheaf owner `Sheaf.cohomologyPresheafFunctor`;
- sampled owner declarations:
  `sheafToPresheaf`,
  `Sheaf.cohomologyPresheafFunctor`,
  `Sheaf.cohomologyPresheaf`,
  `CategoryTheory.evaluation`;
- best owner abstraction: the functor-level comparison between
  `(sheafToPresheaf J AddCommGrpCat).rightDerived p` and `Sheaf.cohomologyPresheafFunctor J p`;
- primitive data: the site `(C, J)` and the cohomological degree `p`;
- derived API here: objectwise evaluation at a sheaf `F`, yielding the comparison with
  `F.cohomologyPresheaf p`.

Source/core/bridge triage:
- `source-facing`: the functor-level comparison identifying the degree-`p` right derived functor of
  the inclusion with the cohomology presheaf functor;
- `core/canonical`: the owners `sheafToPresheaf`, `Sheaf.cohomologyPresheafFunctor`, and
  `Sheaf.cohomologyPresheaf`;
- `bridge/view`: evaluating the source-facing functor isomorphism at a specific abelian sheaf `F`.

The objectwise statement below is therefore derived API and should be obtained from the owner
theorem rather than carried as a parallel primitive result.
-/

-- The left-exactness clause of the textbook lemma is already available in mathlib as the instance
-- `PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat)`.
-- Proof sketch: compute the higher right derived functors of the inclusion `sheafToPresheaf`
-- on injective resolutions of abelian sheaves. Applying the inclusion to an injective resolution
-- leaves the objectwise sections complexes, and taking degree-`p` homology gives the cohomology
-- presheaf `U ↦ H^p(U, F)`.
/-- Lemma 21.10.5: the right derived functor of the inclusion
`Sheaf J AddCommGrpCat ⥤ Cᵒᵖ ⥤ AddCommGrpCat` in degree `p` is canonically isomorphic to the
cohomology presheaf `F ↦ (U ↦ H^p(U, F))`; the left exactness of the inclusion is supplied by the
existing `PreservesFiniteLimits` instance on `sheafToPresheaf`. -/
theorem abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor (p : ℕ) :
    IsIsomorphic ((sheafToPresheaf J AddCommGrpCat).rightDerived p)
      (Sheaf.cohomologyPresheafFunctor J p) := sorry

-- Proof sketch: evaluate the functor-level isomorphism from
-- `abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor` at the abelian sheaf `F`.
/-- Evaluated at an abelian sheaf `F`, the `p`-th right derived functor of the inclusion into
presheaves is the cohomology presheaf of `F`. -/
theorem abelianSheafInclusion_rightDerived_obj_is_cohomologyPresheaf
    (F : Sheaf J AddCommGrpCat) (p : ℕ) :
    IsIsomorphic (((sheafToPresheaf J AddCommGrpCat).rightDerived p).obj F)
      (F.cohomologyPresheaf p) := by
  let h :
      IsIsomorphic ((sheafToPresheaf J AddCommGrpCat).rightDerived p)
        (Sheaf.cohomologyPresheafFunctor J p) :=
    abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor p
  let ⟨e⟩ := h
  simpa [Sheaf.cohomologyPresheaf] using
    (show IsIsomorphic (((sheafToPresheaf J AddCommGrpCat).rightDerived p).obj F)
        ((Sheaf.cohomologyPresheafFunctor J p).obj F) from
      ⟨e.app F⟩)

/-! ### Lemma_21_10_6 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf

noncomputable section

universe v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]
variable [HasInjectiveResolutions (Sheaf J AddCommGrpCat)]

variable (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type (max u v)} (family : ι → Over U)

/-- A functorial package for the spectral sequence computing sheaf cohomology over `U` from the
Čech cohomology of the cohomology presheaves attached to the covering family `family`. -/
structure CechToSheafCohomologySpectralSequence
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat]
    [HasExt (Sheaf J AddCommGrpCat)]
    (U : C) [HasFiniteProducts (Over U)] {ι : Type (max u v)} (family : ι → Over U) where
  /-- The cohomological spectral sequence attached to each abelian sheaf, functorially in the
  sheaf and starting on the `E₂`-page. -/
  spectralSequenceFunctor :
    Sheaf J AddCommGrpCat ⥤ E₂CohomologicalSpectralSequenceNat AddCommGrpCat
  /-- The `E₂`-page is the Čech cohomology of the cohomology presheaf `\underline{H}^q(F)`. -/
  pageTwoIso :
    ∀ (F : Sheaf J AddCommGrpCat) (p q : ℕ),
      ((spectralSequenceFunctor.obj F).page 2).X (p, q) ≅
        cechCohomology U family (F.cohomologyPresheaf q) p
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : Sheaf J AddCommGrpCat → ℕ → AddCommGrpCat
  /-- The abutment identifies with sheaf cohomology of `F` over `U`. -/
  targetIso :
    ∀ (F : Sheaf J AddCommGrpCat) (n : ℕ),
      abutment F n ≅
        F.H' n U

-- Proof sketch: apply the Grothendieck spectral sequence to the composite of the left exact
-- inclusion `sheafToPresheaf J AddCommGrpCat` with degree-zero Čech cohomology for `family`.
-- Lemma `21.8.2` identifies degree-zero Čech cohomology with sections over `U`, Lemma `21.10.2`
-- shows that injective abelian sheaves are Čech-acyclic for the cover, Lemma `21.9.6`
-- identifies higher Čech cohomology with the right derived functors of degree zero, and Lemma
-- `21.10.5` identifies the right derived functors of the inclusion with the cohomology
-- presheaves. The naturality of the Grothendieck construction yields functoriality in `F`.
/-- Lemma 21.10.6: for a covering family `family : ι → Over U` on the slice site `(C / U, J.over
U)`, there is a cohomological spectral sequence functorial in an abelian sheaf `F` whose
`E_2^{p,q}`-term is `\check H^p(family, \underline{H}^q(F))` and whose abutment is the sheaf
cohomology `H^{p+q}(U, F)`. -/
theorem exists_cechToSheafCohomologySpectralSequence :
    Nonempty (CechToSheafCohomologySpectralSequence J U family) := sorry

end

end CategoryTheory

/-! ### Lemma_21_10_7 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasProducts AddCommGrpCat.{v}]
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt (Sheaf J AddCommGrpCat.{v})]
variable [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{v})]
variable {U : C} [HasFiniteProducts (Over U)]
variable {ι : Type w}

/-- The degree-`n` Čech intersection index type of the covering family `family`. -/
private abbrev coverIntersectionIndex (family : ι → Over U) (n : ℕ) :=
  (((FormalCoproduct.mk ι family).cech).obj (op (SimplexCategory.mk n))).I

/-- The underlying object of `C` of the `i`-th degree-`n` Čech intersection of `family`. -/
private abbrev coverIntersectionObject (family : ι → Over U) (n : ℕ)
    (i : coverIntersectionIndex family n) : C :=
  ((((FormalCoproduct.mk ι family).cech).obj (op (SimplexCategory.mk n))).obj i).left

-- Proof sketch: apply the spectral sequence of Lemma `21.10.6`. The hypothesis says that every
-- positive cohomology presheaf `F.cohomologyPresheaf q` with `q > 0` vanishes on each term of the
-- Čech nerve of `family`, so its associated Čech complex is zero and the `E₂`-page is
-- concentrated on the `q = 0` row. The spectral sequence therefore degenerates at `E₂`, and the
-- remaining row identifies `\check H^p(\mathcal U, \mathcal F)` with `H^p(U, \mathcal F)`.
/-- Lemma 21.10.7: if every positive-degree cohomology group of `F` vanishes on every iterated
Čech intersection of the covering family `family`, then the degree-`p` Čech cohomology of `F`
with respect to `family` is canonically isomorphic to the site cohomology `H^p(U, F)`. The
iterated intersections are formalized by the objects `coverIntersectionObject family n i`. -/
theorem cechCohomology_iso_siteCohomology_of_acyclic_intersections
    (family : ι → Over U) (hfamily : (J.over U).CoversTop family)
    (F : Sheaf J AddCommGrpCat.{v})
    (hacyclic : ∀ (q : ℕ) (_hq : 0 < q) (n : ℕ) (i : coverIntersectionIndex family n),
      IsZero (F.H' q (coverIntersectionObject family n i)))
    (p : ℕ) :
    IsIsomorphic
      (cechCohomology U family ((sheafToPresheaf J AddCommGrpCat.{v}).obj F) p)
      (F.H' p U) := sorry

end CategoryTheory

/-! ### Lemma_21_10_8 (from Chap21) -/
open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 21.10.8:
- primary domain: Čech cohomology of abelian presheaves on the slice site `(C / U, J.over U)` and
  its interaction with short exact sequences of abelian sheaves;
- sampled owner declarations:
  `cechComplex`,
  `cechCohomology`,
  `cechCohomologyDegree`,
  `cechComplexFunctor_exact`;
- best owner abstraction: the source-facing owner for the degree-`1` Čech cohomology object is the
  chapter declaration `cechCohomology U family F 1`, built from the core/canonical owner
  `cechComplexFunctor`;
- primitive data: the site `(C, J)`, the object `U`, the covering family, and the underlying
  abelian presheaf `F`;
- derived API here: the cofinal-refinement predicate and the surjectivity consequence for a short
  exact sequence of abelian sheaves.

Source/core/bridge triage:
- `source-facing`: `HasVanishingFirstCechOnCofinalCoverings` and the surjectivity lemma;
- `core/canonical`: `cechComplexFunctor` and the chapter owner `cechCohomology`;
- `bridge/view`: restriction along `(Over.forget U).op` from presheaves on `C` to presheaves on
  `Over U`.

The refinement therefore keeps the source-facing predicate, but rewrites its payload to the owner
`cechCohomology U family F 1` instead of repeating the raw homology expression.
-/

/-- A presheaf has vanishing first Čech cohomology on a cofinal collection of coverings of `U` if
every covering family of `U` admits a refinement whose first Čech cohomology vanishes. -/
def HasVanishingFirstCechOnCofinalCoverings
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    [Limits.HasFiniteProducts (Over U)] [Limits.HasProducts AddCommGrpCat.{max u v}]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) : Prop :=
  ∀ {ι : Type w} (V : ι → Over U), (J.over U).CoversTop V →
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Nonempty
          ((FormalCoproduct.mk κ W : FormalCoproduct (Over U)) ⟶
            (FormalCoproduct.mk ι V : FormalCoproduct (Over U))) ∧
        IsZero (cechCohomology U W F 1)

-- Proof sketch: this is just the defining expansion of
-- `HasVanishingFirstCechOnCofinalCoverings`; apply the hypothesis to the chosen covering family.
/-- Unfolding the cofinal Čech-vanishing hypothesis yields a refining covering of `U` with trivial
first Čech cohomology. -/
theorem hasVanishingFirstCechOnCofinalCoverings_exists_refinement
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
    [Limits.HasFiniteProducts (Over U)] [Limits.HasProducts AddCommGrpCat.{max u v}]
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (hF : HasVanishingFirstCechOnCofinalCoverings J U F)
    {ι : Type w} (V : ι → Over U) (hV : (J.over U).CoversTop V) :
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Nonempty
          ((FormalCoproduct.mk κ W : FormalCoproduct (Over U)) ⟶
            (FormalCoproduct.mk ι V : FormalCoproduct (Over U))) ∧
        IsZero (cechCohomology U W F 1) :=
  hF V hV

-- Proof sketch: use exactness to identify local lifts of a section of `S.X₃` as a Čech
-- `1`-cocycle with values in `S.X₁`; then refine the chosen cover so that the first Čech
-- cohomology of `S.X₁` vanishes, making the cocycle a coboundary. Correct the local lifts by this
-- coboundary and glue the resulting compatible sections of `S.X₂` to a global lift over `U`.
/-- Lemma 21.10.8: if `0 ⟶ \mathcal F ⟶ \mathcal G ⟶ \mathcal H ⟶ 0` is a short exact sequence
of abelian sheaves on a site and the left term has vanishing first Čech cohomology on a cofinal
collection of coverings of `U`, then the map `\mathcal G(U) \to \mathcal H(U)` is surjective. -/
theorem shortExact_right_map_surjective_of_vanishingFirstCech_on_cofinal_coverings
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
    [Limits.HasFiniteProducts (Over U)] [Limits.HasProducts AddCommGrpCat.{max u v}]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v}))
    (hS : S.ShortExact)
    (hcech :
      HasVanishingFirstCechOnCofinalCoverings J U
        ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj S.X₁)) :
    Function.Surjective (S.g.app (op U)) := sorry

end CategoryTheory

/-! ### Lemma_21_10_9 (from Chap21) -/
open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

/-- A presheaf has vanishing higher Čech cohomology on a cofinal collection of coverings of `U` if
every covering family of `U` admits a refinement whose positive-degree Čech cohomology vanishes. -/
def HasVanishingHigherCechOnCofinalCoverings
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    [Limits.HasFiniteProducts (Over U)] [Limits.HasProducts AddCommGrpCat.{v}]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) : Prop :=
  ∀ {ι : Type w} (V : ι → Over U), (J.over U).CoversTop V →
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Nonempty
          ((FormalCoproduct.mk κ W : FormalCoproduct (Over U)) ⟶
            (FormalCoproduct.mk ι V : FormalCoproduct (Over U))) ∧
        ∀ (p : ℕ), 0 < p →
          IsZero
            ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p).obj
              ((cechComplexFunctor W).obj ((Over.forget U).op ⋙ F)))

-- Proof sketch: this is just the defining expansion of
-- `HasVanishingHigherCechOnCofinalCoverings`; apply the hypothesis to the chosen covering family.
/-- Unfolding the cofinal higher Čech-vanishing hypothesis yields a refining covering of `U`
whose positive-degree Čech cohomology is trivial in every degree. -/
theorem hasVanishingHigherCechOnCofinalCoverings_exists_refinement
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
    [Limits.HasFiniteProducts (Over U)] [Limits.HasProducts AddCommGrpCat.{v}]
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    (hF : HasVanishingHigherCechOnCofinalCoverings J U F)
    {ι : Type w} (V : ι → Over U) (hV : (J.over U).CoversTop V) :
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Nonempty
          ((FormalCoproduct.mk κ W : FormalCoproduct (Over U)) ⟶
            (FormalCoproduct.mk ι V : FormalCoproduct (Over U))) ∧
        ∀ (p : ℕ), 0 < p →
          IsZero
            ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p).obj
              ((cechComplexFunctor W).obj ((Over.forget U).op ⋙ F))) := sorry

-- Proof sketch: embed `F` into an injective abelian sheaf `ℐ`, let `ℚ := ℐ/F`, and use
-- Lemma `21.10.8` degreewise on the short exact sequence
-- `0 ⟶ F ⟶ ℐ ⟶ ℚ ⟶ 0` to make sections exact over `U`. The long exact sequence in Čech
-- cohomology shows that `ℚ` again satisfies the same cofinal higher Čech-vanishing hypothesis,
-- while injectivity of `ℐ` gives vanishing of `H^n(U, ℐ)` for `n > 0`. Induct on `p` through the
-- long exact cohomology sequence of `0 ⟶ F ⟶ ℐ ⟶ ℚ ⟶ 0`.
/-- Lemma 21.10.9: if an abelian sheaf on a site has vanishing higher Čech cohomology on a
cofinal collection of coverings of `U`, then every higher cohomology group `H^p(U, \mathcal F)`
with `p > 0` is zero. -/
theorem higherCohomology_isZero_of_vanishingHigherCech_on_cofinal_coverings
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
    [Limits.HasFiniteProducts (Over U)] [Limits.HasProducts AddCommGrpCat.{v}]
    [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v})
    (hF :
      HasVanishingHigherCechOnCofinalCoverings J U
        ((sheafToPresheaf J AddCommGrpCat.{v}).obj F))
    (p : ℕ) (hp : 0 < p) :
    IsZero (F.H' p U) := sorry

end CategoryTheory
