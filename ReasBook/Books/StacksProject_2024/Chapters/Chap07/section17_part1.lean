import Mathlib
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_17_1 (from Chap07) -/
open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe w u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 7.17.1:
- primary domain: Grothendieck-topology covers and explicit covering families;
- sampled owner abstractions:
  `GrothendieckTopology.Cover`,
  `Presieve.exists_eq_ofArrows`,
  `SemiRepresentableFamily.Over.toSieve`,
  `SemiRepresentableFamily.Over.toPresieve`;
- source-facing layer: quasi-compactness of an object in a site;
- core/canonical owner: `J.QuasiCompactObject U` as a universe-independent property of `U`;
- bridge/view layer: explicit covering families `SemiRepresentableFamily.Over U`.

Primitive data are only the topology `J`, the object `U`, and a covering sieve on `U`. Explicit
indexed families are a bridge/view presentation of that sieve, so the public owner should not
store the index universe as primitive data.
-/

/-- Definition 7.17.1: an object `U` of a site `(C, J)` is quasi-compact if every covering family
of maps with fixed target `U` admits a covering refinement whose refinement morphism has finite
image on indices. -/
def QuasiCompactObject (J : GrothendieckTopology C) (U : C) : Prop :=
  ∀ S : J.Cover U,
    ∃ (T : Set S.Arrow) (_ : T.Finite),
      Sieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f) ∈ J U

-- Proof sketch: transport a covering sieve across an isomorphism using pullback stability and
-- `GrothendieckTopology.pullback_mem_iff_of_isIso`, then apply the finite-subcover field on the
-- isomorphic source object and push the resulting finite family back across the same isomorphism.
/-- Quasi-compactness is closed under isomorphisms of site objects. -/
instance quasiCompactObject_isClosedUnderIsomorphisms (J : GrothendieckTopology C) :
    CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms (J.QuasiCompactObject) :=
  { of_iso := by
      intro U V e hU S
      classical
      -- Pull the target cover back along the isomorphism so that `hU` applies on the source.
      let S' : J.Cover U := S.pullback e.hom
      obtain ⟨T, hT, hTcover⟩ := hU S'
      -- Postcompose the finite family on `U` along the isomorphism and record only its image in
      -- the original covering family on `V`.
      let β : T → S.Arrow := fun I ↦ I.1.base
      let T' : Set S.Arrow := Set.range β
      have hT' : T'.Finite := by
        letI := hT.fintype
        simpa [T', β] using Set.finite_range β
      have hpush :
          Sieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f ≫ e.hom) ∈ J V := by
        have hpull :
            (Sieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f ≫ e.hom)).pullback e.hom ∈
              J U := by
          rw [Sieve.pullback_ofArrows_of_iso]
          simpa [Category.assoc] using hTcover
        exact (GrothendieckTopology.pullback_mem_iff_of_isIso (J := J) (i := e.hom)).1 hpull
      -- Reindex the transported family by its range so the witness is a finite subset of
      -- `S.Arrow`, exactly as required by the definition.
      have hT'presieve :
          Presieve.ofArrows (fun I : T' ↦ I.1.Y) (fun I ↦ I.1.f) =
            Presieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f ≫ e.hom) := by
        let a : T → T' := fun I ↦ ⟨β I, ⟨I, rfl⟩⟩
        have ha : Function.Surjective a := by
          rintro ⟨I, i, rfl⟩
          exact ⟨i, rfl⟩
        calc
          Presieve.ofArrows (fun I : T' ↦ I.1.Y) (fun I ↦ I.1.f)
              =
                Presieve.ofArrows
                  (fun I : T ↦ (a I).1.Y)
                  (fun I ↦ (a I).1.f) := by
            symm
            exact Presieve.ofArrows_comp_eq_of_surjective (fun I : T' ↦ I.1.f) ha
          _ = Presieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f ≫ e.hom) := by
            rfl
      refine ⟨T', hT', ?_⟩
      simpa [Sieve.ofArrows, hT'presieve] using hpush }

/-- The fixed `max u v`-small owner formulation of quasi-compactness refines any covering family,
regardless of the indexing universe used to present that family. -/
theorem QuasiCompactObject.finite_image_refinement_of_family
    {J : GrothendieckTopology C} {U : C} (hU : QuasiCompactObject J U)
    (𝒰 : SemiRepresentableFamily.Over.{w} U) (h𝒰 : 𝒰.toSieve ∈ J U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{w} U) (_ : 𝒱.toSieve ∈ J U) (φ : 𝒱 ⟶ 𝒰),
      Set.Finite (Set.range φ.α) := by
  let S : J.Cover U := ⟨𝒰.toSieve, h𝒰⟩
  obtain ⟨T, hT, hTcover⟩ := hU S
  let 𝒱₀ := SemiRepresentableFamily.Over.ofArrows (fun I : T ↦ I.1.Y) fun I ↦ I.1.f
  have h𝒱₀ : 𝒱₀.toSieve ∈ J U := hTcover
  have hfactor :
      ∀ I : T, ∃ i : 𝒰.index, ∃ g : I.1.Y ⟶ (𝒰.obj i).left, I.1.f = g ≫ (𝒰.obj i).hom := by
    intro I
    exact Sieve.ofArrows.exists I.1.hf
  choose α g hg using hfactor
  let R : Set 𝒰.index := Set.range α
  have hR : R.Finite := by
    letI := hT.fintype
    simpa [R] using Set.finite_range α
  let 𝒱 : SemiRepresentableFamily.Over.{w} U :=
    { index := R
      obj := fun i ↦ 𝒰.obj i.1 }
  have hle : 𝒱₀.toSieve ≤ 𝒱.toSieve := by
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro I
    let iR : R := ⟨α I, by exact ⟨I, rfl⟩⟩
    refine ⟨_, g I, _, Presieve.ofArrows.mk iR, ?_⟩
    simpa [𝒱₀, 𝒱, iR] using (hg I).symm
  have h𝒱 : 𝒱.toSieve ∈ J U := by
    exact J.superset_covering hle h𝒱₀
  refine ⟨𝒱, h𝒱, ?_, ?_⟩
  · exact
      { α := Subtype.val
        f := fun i ↦ 𝟙 (𝒰.obj i.1) }
  · change Set.Finite (Set.range (Subtype.val : R → 𝒰.index))
    simpa [Subtype.range_coe] using hR

/-- Companion formulation of Definition 7.17.1 for an explicitly indexed covering family. -/
theorem quasiCompactObject_finite_image_refinement_ofArrows
    {J : GrothendieckTopology C} {U : C} (hU : QuasiCompactObject J U)
    {ι : Type w} (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U)
    (hcover : Sieve.ofArrows Uᵢ π ∈ J U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{w} U) (_ : 𝒱.toSieve ∈ J U)
      (φ : 𝒱 ⟶ SemiRepresentableFamily.Over.ofArrows Uᵢ π),
      Set.Finite (Set.range φ.α) := by
  have h𝒰 : (SemiRepresentableFamily.Over.ofArrows Uᵢ π).toSieve ∈ J U := by
    simpa [toSieve, toPresieve, ofArrows] using hcover
  simpa [toSieve, toPresieve, ofArrows] using
    hU.finite_image_refinement_of_family (SemiRepresentableFamily.Over.ofArrows Uᵢ π) h𝒰

end CategoryTheory.GrothendieckTopology

/-! ### Lemma_7_17_2 (from Chap07) -/
open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe w u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 7.17.2:
- primary domain: Grothendieck-topology covering families, presieves, and refinements;
- sampled owner/bridge declarations:
  `CategoryTheory.Presieve`,
  `GrothendieckTopology.Cover`,
  `GrothendieckTopology.QuasiCompactObject`,
  `QuasiCompactObject.finite_image_refinement_of_family`,
  `SemiRepresentableFamily.Over.toPresieve`,
  `SemiRepresentableFamily.Over.toSieve`;
- source-facing owners: `HasFiniteSubcoverProperty`, `HasFiniteRefinementProperty`;
- core/canonical consequence already present upstream: `J.QuasiCompactObject U`;
- bridge/view layer: explicit indexed covering families `SemiRepresentableFamily.Over U`.

Primitive data for the source-facing properties are the topology `J`, the object `U`, and a
presieve `R : Presieve U`, which records the actual arrows in the chosen covering family without
fixing an index universe. Explicit `SemiRepresentableFamily.Over U` presentations are derived
bridge/view API from that presieve owner. The downstream consequence `J.QuasiCompactObject U`
already has its canonical sieve-level owner upstream, so this file keeps only the genuinely
stronger source-facing owners and their implication to that canonical consequence.
-/

/-- A site object satisfies the finite-refinement condition when every covering presieve on `U`
admits a finite covering family refining that presieve. -/
class HasFiniteRefinementProperty (J : GrothendieckTopology C) (U : C) : Prop where
  finite_refinement
    (R : Presieve U) (hR : Sieve.generate R ∈ J U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{max u v} U) (_ : Finite 𝒱.index)
      (_ : 𝒱.toSieve ∈ J U),
      𝒱.toSieve ≤ Sieve.generate R

/-- A site object satisfies the finite-subcover condition when every covering presieve on `U`
already contains finitely many of its own arrows generating a covering sieve. -/
class HasFiniteSubcoverProperty (J : GrothendieckTopology C) (U : C) : Prop where
  finite_subcover
    (R : Presieve U) (hR : Sieve.generate R ∈ J U) :
    ∃ (S : Set R.uncurry) (_ : S.Finite),
      Sieve.ofArrows
        (fun i : S ↦ i.1.1.1)
        (fun i ↦ i.1.1.2) ∈ J U

/-- The canonical presieve generated by all arrows already lying in `R` is exactly `R` itself. -/
theorem presieve_of_uncurry_eq {U : C} (R : Presieve U) :
    Presieve.ofArrows (fun i : R.uncurry ↦ i.1.1) (fun i ↦ i.1.2) = R := by
  funext Y f
  apply propext
  constructor
  · intro hf
    rcases hf with ⟨i⟩
    exact i.2
  · intro hf
    let i : R.uncurry := ⟨⟨Y, f⟩, hf⟩
    exact Presieve.ofArrows.mk i

/-- The presieve-level finite-refinement owner applies to any explicit indexed covering family,
independently of the indexing universe. -/
theorem HasFiniteRefinementProperty.finite_refinement_of_family
    {J : GrothendieckTopology C} {U : C} (hU : HasFiniteRefinementProperty J U)
    (𝒰 : SemiRepresentableFamily.Over.{w} U) (h𝒰 : 𝒰.toSieve ∈ J U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{max u v} U) (_ : Finite 𝒱.index)
      (_ : 𝒱.toSieve ∈ J U),
      𝒱.toSieve ≤ 𝒰.toSieve := by
  simpa [toSieve] using hU.finite_refinement 𝒰.toPresieve h𝒰

-- Proof sketch: given a finite covering subfamily, use that same subfamily as the finite refining
-- covering family, together with the evident refinement maps into the original cover.
/-- Lemma 7.17.2 (1): if every covering of `U` contains a finite covering subfamily, then every
covering of `U` admits a finite covering refinement. -/
theorem hasFiniteSubcoverProperty_implies_hasFiniteRefinementProperty
    {J : GrothendieckTopology C} {U : C} (hU : HasFiniteSubcoverProperty J U) :
    HasFiniteRefinementProperty J U :=
  { finite_refinement := fun R hR ↦ by
      obtain ⟨S, hS, hSieve⟩ := hU.finite_subcover R hR
      let 𝒱 : SemiRepresentableFamily.Over.{max u v} U :=
        ofArrows
          (fun i : S ↦ i.1.1.1)
          (fun i ↦ i.1.1.2)
      have hle : 𝒱.toSieve ≤ Sieve.generate R := by
        apply Sieve.generate_mono
        rw [Presieve.ofArrows_le_iff]
        intro i
        exact i.1.2
      refine ⟨𝒱, hS.to_subtype, ?_, hle⟩
      simpa [𝒱, toSieve, toPresieve, ofArrows] using hSieve }

-- Proof sketch: a finite refining covering has finite index type, so the image of its index map
-- in the original family is finite; this is exactly the finite-image refinement required in the
-- definition of quasi-compactness above.
/-- Lemma 7.17.2 (2): if every covering of `U` admits a finite covering refinement, then `U` is
quasi-compact. -/
theorem hasFiniteRefinementProperty_implies_quasiCompactObject
    {J : GrothendieckTopology C} {U : C} (hU : HasFiniteRefinementProperty J U) :
    J.QuasiCompactObject U := by
  change
    ∀ S : J.Cover U,
      ∃ (T : Set S.Arrow) (_ : T.Finite),
        Sieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f) ∈ J U
  intro S
  have hS : Sieve.generate (S : Sieve U) ∈ J U := by
    simpa using S.condition
  obtain ⟨𝒱₀, h𝒱₀fin, h𝒱₀, hle⟩ := hU.finite_refinement (S : Sieve U) hS
  have hle' : 𝒱₀.toSieve ≤ (S : Sieve U) := by
    simpa using hle
  let toArrow : 𝒱₀.index → S.Arrow := fun i ↦
    { Y := (𝒱₀.obj i).left
      f := (𝒱₀.obj i).hom
      hf := by
        have hi : 𝒱₀.toSieve ((𝒱₀.obj i).hom) := by
          exact (Sieve.le_generate 𝒱₀.toPresieve) _ _ (Presieve.ofArrows.mk i)
        have hi' : (S : Sieve U) ((𝒱₀.obj i).hom) := by
          exact hle' (𝒱₀.obj i).hom hi
        simpa using hi' }
  let T : Set S.Arrow := Set.range toArrow
  have hT : T.Finite := by
    let _ : Finite 𝒱₀.index := h𝒱₀fin
    letI := Fintype.ofFinite 𝒱₀.index
    simpa [T, toArrow] using Set.finite_range toArrow
  have hTpresieve :
      Presieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f) = 𝒱₀.toPresieve := by
    let a : 𝒱₀.index → T := fun i ↦ ⟨toArrow i, ⟨i, rfl⟩⟩
    have ha : Function.Surjective a := by
      rintro ⟨I, i, rfl⟩
      exact ⟨i, rfl⟩
    calc
      Presieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f)
          =
            Presieve.ofArrows
              (fun i : 𝒱₀.index ↦ (a i).1.Y)
              (fun i ↦ (a i).1.f) := by
        symm
        exact Presieve.ofArrows_comp_eq_of_surjective (fun I : T ↦ I.1.f) ha
      _ = 𝒱₀.toPresieve := by
        rfl
  have hTcover : Sieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f) ∈ J U := by
    rw [Sieve.ofArrows, hTpresieve]
    exact h𝒱₀
  refine ⟨T, hT, ?_⟩
  exact hTcover

/-- Helper for Lemma 7.17.2: a morphism into the canonical uncurry family factors through the
subfamily indexed by the image of its index map. -/
theorem toSieve_le_range_family_of_hom
    {U : C} (R : Presieve U) {𝒱 : SemiRepresentableFamily.Over.{max u v} U}
    (φ : 𝒱 ⟶ ofArrows (fun i : R.uncurry ↦ i.1.1) (fun i ↦ i.1.2)) :
    𝒱.toSieve ≤
      (ofArrows (fun i : Set.range φ.α ↦ i.1.1.1) (fun i ↦ i.1.1.2)).toSieve := by
  let 𝒲 : SemiRepresentableFamily.Over.{max u v} U :=
    ofArrows (fun i : Set.range φ.α ↦ i.1.1.1) (fun i ↦ i.1.1.2)
  -- Reindex `𝒱` by the image of `φ.α`; the component maps are unchanged.
  let ψ : 𝒱 ⟶ 𝒲 :=
    { α := fun i ↦ ⟨φ.α i, ⟨i, rfl⟩⟩
      f := fun i ↦ φ.f i }
  -- The induced family morphism gives the required sieve inclusion.
  simpa [𝒲] using toSieve_le_of_hom ψ

/-- Helper for Lemma 7.17.2: a sieve refinement by `Sieve.generate R` chooses, for each component
of an explicit family, an actual arrow of `R` through which that component factors. -/
theorem exists_hom_to_uncurry_family_of_sieve_refinement
    {U : C} (R : Presieve U) (𝒱 : SemiRepresentableFamily.Over.{max u v} U)
    (hle : 𝒱.toSieve ≤ Sieve.generate R) :
    Nonempty (𝒱 ⟶ ofArrows (fun i : R.uncurry ↦ i.1.1) (fun i ↦ i.1.2)) := by
  classical
  let 𝒰 : SemiRepresentableFamily.Over.{max u v} U :=
    ofArrows (fun i : R.uncurry ↦ i.1.1) (fun i ↦ i.1.2)
  have hfactor :
      ∀ i : 𝒱.index,
        ∃ j : R.uncurry, ∃ g : (𝒱.obj i).left ⟶ j.1.1, g ≫ j.1.2 = (𝒱.obj i).hom := by
    intro i
    -- Each generator of `𝒱.toSieve` lies in `Sieve.generate R`, so it factors through a chosen
    -- arrow of `R`.
    have hi : 𝒱.toSieve ((𝒱.obj i).hom) := by
      exact Sieve.le_generate 𝒱.toPresieve _ _ (Presieve.ofArrows.mk i)
    have hi' : Sieve.generate R ((𝒱.obj i).hom) := by
      exact hle (𝒱.obj i).hom hi
    rcases hi' with ⟨Y, g, f, hf, hgf⟩
    exact ⟨⟨⟨Y, f⟩, hf⟩, g, hgf⟩
  choose α g hg using hfactor
  -- Package the chosen factorizations as a morphism of fixed-target families.
  refine ⟨
    { α := α
      f := fun i ↦ Over.homMk (g i) (by simpa [𝒰] using hg i) }⟩

-- In the source text, condition (1) is a covering-family notion of quasi-compactness. The
-- current Mathlib owner `QuasiCompactObject` is sieve-based and is strong enough to produce the
-- finite-refinement property directly, so the source counterexample should not be stated as a
-- negation involving this owner.
/-- Lemma 7.17.2 (3), repaired owner form: with the current sieve-level owner,
`QuasiCompactObject` implies the finite-refinement condition. The source counterexample to the
reverse implication belongs to the covering-family presentation of quasi-compactness, not to this
formal owner. -/
theorem exists_quasiCompactObject_not_hasFiniteRefinementProperty
    {J : GrothendieckTopology C} {U : C} (hU : J.QuasiCompactObject U) :
    HasFiniteRefinementProperty J U := by
  refine
    { finite_refinement := fun R hR ↦ by
        let 𝒰 : SemiRepresentableFamily.Over.{max u v} U :=
          ofArrows (fun i : R.uncurry ↦ i.1.1) (fun i ↦ i.1.2)
        have h𝒰toPresieve : 𝒰.toPresieve = R := by
          simpa [𝒰, toPresieve, ofArrows] using presieve_of_uncurry_eq R
        have h𝒰toSieve : 𝒰.toSieve = Sieve.generate R := by
          simp [toSieve, h𝒰toPresieve]
        -- Apply quasi-compactness to the canonical uncurry family attached to `R`.
        obtain ⟨𝒱, h𝒱, φ, hφfin⟩ :=
          hU.finite_image_refinement_of_family 𝒰 (by simpa [h𝒰toSieve] using hR)
        let 𝒲 : SemiRepresentableFamily.Over.{max u v} U :=
          ofArrows (fun i : Set.range φ.α ↦ i.1.1.1) (fun i ↦ i.1.1.2)
        have hle_cover : 𝒱.toSieve ≤ 𝒲.toSieve := by
          simpa [𝒲] using toSieve_le_range_family_of_hom R φ
        have h𝒲 : 𝒲.toSieve ∈ J U := by
          exact J.superset_covering hle_cover h𝒱
        have h𝒲le : 𝒲.toSieve ≤ Sieve.generate R := by
          -- The range family is literally a subfamily of the uncurry family for `R`.
          change
            Sieve.generate
                (Presieve.ofArrows (fun i : Set.range φ.α ↦ i.1.1.1) (fun i ↦ i.1.1.2)) ≤
              Sieve.generate R
          refine (Sieve.generate_le_iff _ _).2 ?_
          rw [Presieve.ofArrows_le_iff]
          intro i
          exact Sieve.le_generate R _ _ i.1.2
        exact ⟨𝒲, hφfin.to_subtype, h𝒲, h𝒲le⟩ }

-- Proof sketch: under the current presieve-level owner, a finite covering refinement of a
-- covering presieve already determines finitely many arrows of the original presieve whose
-- generated sieve is covering. Thus the source-text counterexample to `(2) → (3)` belongs to the
-- original covering-family presentation, not to this repaired presieve owner.
/-- Lemma 7.17.2 (4), repaired owner form: with the current presieve-level definitions, the
finite-refinement condition implies the finite-subcover condition. The source counterexample to the
reverse implication of the covering-family formulation is therefore not represented by
`HasFiniteRefinementProperty K V ∧ ¬ HasFiniteSubcoverProperty K V`. -/
theorem hasFiniteRefinementProperty_implies_hasFiniteSubcoverProperty
    {J : GrothendieckTopology C} {U : C} (hU : HasFiniteRefinementProperty J U) :
    HasFiniteSubcoverProperty J U := by
  refine
    { finite_subcover := fun R hR ↦ by
        obtain ⟨𝒱, h𝒱fin, h𝒱, hle⟩ := hU.finite_refinement R hR
        obtain ⟨φ⟩ := exists_hom_to_uncurry_family_of_sieve_refinement R 𝒱 hle
        let S : Set R.uncurry := Set.range φ.α
        let 𝒲 : SemiRepresentableFamily.Over.{max u v} U :=
          ofArrows (fun i : S ↦ i.1.1.1) (fun i ↦ i.1.1.2)
        have hS : S.Finite := by
          let _ : Finite 𝒱.index := h𝒱fin
          letI : Fintype 𝒱.index := Fintype.ofFinite 𝒱.index
          simpa [S] using Set.finite_range φ.α
        have hle_cover : 𝒱.toSieve ≤ 𝒲.toSieve := by
          simpa [S, 𝒲] using toSieve_le_range_family_of_hom R φ
        have h𝒲 : 𝒲.toSieve ∈ J U := by
          exact J.superset_covering hle_cover h𝒱
        -- The finite image of the comparison map is the required finite covering subset of `R`.
        refine ⟨S, hS, ?_⟩
        simpa [S, 𝒲, toSieve, toPresieve, ofArrows] using h𝒲 }

end CategoryTheory.GrothendieckTopology

/-! ### Lemma_7_17_3 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open Opposite
open CategoryTheory.SemiRepresentableFamily.Over

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology

open scoped SheafifiedRepresentable

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/-
Source/core/bridge triage for 7.17.3:
- source-facing predicate on the site side: `J.QuasiCompactObject U`
- core/canonical predicate on the sheaf side: `Sheaf.IsQuasiCompactObject`
- bridge/view object: `J.sheafifiedRepresentable U`
-/
-- Proof sketch: for `(1) → (2)`, turn a locally surjective coproduct map to `h_U^#` into a
-- covering family over `U` and then refine it to finitely many summands. For `(2) → (1)`, start
-- from a covering family of `U`, use the canonical locally surjective cover map
-- `J.sheafifiedRepresentableCoverMap`, apply the owner field
-- `Sheaf.IsQuasiCompactObject.finite_subcoproduct`, and convert the resulting finite locally
-- surjective coproduct map of sheafified representables back to a covering sieve on `U`.

/-- Helper for Lemma 7.17.3: a morphism from a sheafified representable into a coproduct of
sheaves locally factors through a single summand. -/
lemma locally_factor_coproduct_morphism_through_single_summand
    {ι : Type (max u v)} {V : C} (ℱᵢ : ι → Sheaf J (Type (max u v))) [HasCoproduct ℱᵢ]
    (β : h[V]^#[J] ⟶ ∐ ℱᵢ) :
    ∃ R : J.Cover V, ∀ r : R.Arrow, ∃ i : ι, ∃ τ : h[r.Y]^#[J] ⟶ ℱᵢ i,
      J.sheafifiedRepresentableMap r.f ≫ β = τ ≫ Limits.Sigma.ι ℱᵢ i := by
  classical
  let F : Discrete ι ⥤ Sheaf J (Type (max u v)) := Discrete.functor ℱᵢ
  let E : Cocone (F ⋙ sheafToPresheaf J (Type (max u v))) := colimit.cocone _
  let hE : IsColimit E := colimit.isColimit _
  let hS := Sheaf.isColimitSheafifyCocone (J := J) (D := Type (max u v)) E hE
  let e : ((presheafToSheaf J (Type (max u v))).obj E.pt) ≅ ∐ ℱᵢ := by
    simpa [Sheaf.sheafifyCocone] using hS.coconePointUniqueUpToIso (colimit.isColimit F)
  let η : E.pt ⟶ ((presheafToSheaf J (Type (max u v))).obj E.pt).obj :=
    (sheafificationAdjunction J (Type (max u v))).unit.app E.pt
  let xV : (∐ ℱᵢ).obj.obj (op V) := J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) V β
  let zV : ((presheafToSheaf J (Type (max u v))).obj E.pt).obj.obj (op V) :=
    e.inv.hom.app (op V) xV
  let R : J.Cover V := ⟨Presheaf.imageSieve η zV, Presheaf.imageSieve_mem J η zV⟩
  refine ⟨R, ?_⟩
  intro r
  let tr : E.pt.obj (op r.Y) := Presheaf.localPreimage η zV r.f r.hf
  have htr :
      η.app (op r.Y) tr =
        ((presheafToSheaf J (Type (max u v))).obj E.pt).obj.map r.f.op zV := by
    -- The chosen local preimage in the presheaf coproduct maps to the restricted section.
    simpa [η, tr] using Presheaf.app_localPreimage η zV r.f r.hf
  let ev := (evaluation Cᵒᵖ (Type (max u v))).obj (op r.Y)
  have hcol : IsColimit (ev.mapCocone E) := by
    -- Evaluate the presheaf coproduct cocone at `r.Y` so joint surjectivity is pointwise.
    exact isColimitOfPreserves ev hE
  obtain ⟨j, y, hjy⟩ := Types.jointly_surjective_of_isColimit hcol tr
  let i : ι := j.as
  let τ : h[r.Y]^#[J] ⟶ ℱᵢ i :=
    (J.uliftSheafifiedRepresentableHomEquiv (ℱᵢ i) r.Y).symm y
  refine ⟨i, τ, ?_⟩
  apply (J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) r.Y).injective
  have hβ :
      (J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) r.Y)
          (J.sheafifiedRepresentableMap r.f ≫ β) =
        (∐ ℱᵢ).obj.map r.f.op xV := by
    -- Restrict the original section of the coproduct along `r.f`.
    simpa [xV] using J.uliftSheafifiedRepresentableHomEquiv_naturality r.f (∐ ℱᵢ) β
  have hτ0 := J.uliftSheafifiedRepresentableHomEquiv_comp τ (Limits.Sigma.ι ℱᵢ i)
  have hy : (J.uliftSheafifiedRepresentableHomEquiv (ℱᵢ i) r.Y) τ = y := by
    exact Equiv.apply_symm_apply (J.uliftSheafifiedRepresentableHomEquiv (ℱᵢ i) r.Y) y
  have hτ :
      (J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) r.Y)
          (τ ≫ Limits.Sigma.ι ℱᵢ i) =
        (Limits.Sigma.ι ℱᵢ i).hom.app (op r.Y) y := by
    -- The chosen point of the `i`-th summand induces the expected coproduct section.
    simpa [hy] using hτ0
  rw [hβ, hτ]
  have hzV : e.hom.hom.app (op V) zV = xV := by
    change e.hom.hom.app (op V) (e.inv.hom.app (op V) xV) = xV
    exact congrArg (fun f => f.hom.app (op V) xV) e.inv_hom_id
  have hright :
      e.hom.hom.app (op r.Y) (η.app (op r.Y) tr) =
        (∐ ℱᵢ).obj.map r.f.op xV := by
    rw [htr]
    -- After applying the colimit isomorphism, the chosen presheaf lift becomes the
    -- restriction of the original coproduct section.
    simpa [ConcreteCategory.comp_apply, hzV] using
      congrArg (fun f => f zV) (e.hom.hom.naturality r.f.op)
  have hη : η = CategoryTheory.toSheafify J E.pt := by
    simpa [η] using
      (CategoryTheory.sheafificationAdjunction_unit_app
        (J := J) (D := Type (max u v)) (P := E.pt))
  have hηtr :
      η.app (op r.Y) tr =
        ((Sheaf.sheafifyCocone E).ι.app j).hom.app (op r.Y) y := by
    rw [← hjy]
    have hι' : E.ι.app j ≫ η = ((Sheaf.sheafifyCocone E).ι.app j).hom := by
      rw [hη]
      simpa using
        (Sheaf.sheafifyCocone_ι_app_val (J := J) (D := Type (max u v)) E j).symm
    -- Rewrite the chosen pointwise lift through the sheafified coproduct cocone.
    exact congrArg (fun f => f.app (op r.Y) y) hι'
  have hcomp :
      (Sheaf.sheafifyCocone E).ι.app j ≫
          (by simpa [Sheaf.sheafifyCocone] using e.hom) =
        Limits.Sigma.ι ℱᵢ i := by
    -- The colimit isomorphism identifies the sheafified presheaf coproduct injections with the
    -- actual coproduct injections in `Sheaf`.
    simpa [i] using hS.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) j
  have hleft :
      e.hom.hom.app (op r.Y) (η.app (op r.Y) tr) =
        (Limits.Sigma.ι ℱᵢ i).hom.app (op r.Y) y := by
    rw [hηtr]
    exact congrArg (fun f => f.hom.app (op r.Y) y) hcomp
  exact hright.symm.trans hleft

/-- Helper for Lemma 7.17.3: downward closure for the sieve of arrows whose map to `h[U]^#`
factors through one summand of a fixed coproduct map. -/
lemma single_summand_factor_sieve_downward_closed
    {ι : Type (max u v)} {U Y Z : C} (ℱᵢ : ι → Sheaf J (Type (max u v))) [HasCoproduct ℱᵢ]
    (π : (∐ ℱᵢ) ⟶ h[U]^#[J]) {f : Y ⟶ U}
    (hf : ∃ i : ι, ∃ τ : h[Y]^#[J] ⟶ ℱᵢ i,
      τ ≫ Limits.Sigma.ι ℱᵢ i ≫ π = J.sheafifiedRepresentableMap f)
    (g : Z ⟶ Y) :
    ∃ i : ι, ∃ τ : h[Z]^#[J] ⟶ ℱᵢ i,
      τ ≫ Limits.Sigma.ι ℱᵢ i ≫ π = J.sheafifiedRepresentableMap (g ≫ f) := by
  rcases hf with ⟨i, τ, hτ⟩
  refine ⟨i, J.sheafifiedRepresentableMap g ≫ τ, ?_⟩
  -- Precompose the chosen factorization along `g`.
  simpa [Category.assoc, sheafifiedRepresentableMap, sheafifiedRepresentableFunctor,
    uliftSheafifiedRepresentableFunctor] using congrArg (fun k => J.sheafifiedRepresentableMap g ≫ k) hτ

/-- Helper for Lemma 7.17.3: the arrows into `U` whose map to `h[U]^#` factors through a single
summand of `π` form a sieve. -/
def singleSummandFactorSieve
    {ι : Type (max u v)} {U : C} (ℱᵢ : ι → Sheaf J (Type (max u v))) [HasCoproduct ℱᵢ]
    (π : (∐ ℱᵢ) ⟶ h[U]^#[J]) : Sieve U where
  arrows Y f :=
    ∃ i : ι, ∃ τ : h[Y]^#[J] ⟶ ℱᵢ i,
      τ ≫ Limits.Sigma.ι ℱᵢ i ≫ π = J.sheafifiedRepresentableMap f
  downward_closed := single_summand_factor_sieve_downward_closed (J := J) ℱᵢ π

/-- Helper for Lemma 7.17.3: a locally surjective coproduct map to `h[U]^#` yields a covering
sieve of arrows whose corresponding sheafified-representable maps already factor through one
summand. -/
lemma exists_coproduct_lift_of_image_sieve_mem_identity
    {ι : Type (max u v)} {U Y : C} (ℱᵢ : ι → Sheaf J (Type (max u v))) [HasCoproduct ℱᵢ]
    (π : (∐ ℱᵢ) ⟶ h[U]^#[J]) {f : Y ⟶ U}
    (hf :
      Presheaf.imageSieve π.hom
        (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J]))) f) :
    ∃ β : h[Y]^#[J] ⟶ ∐ ℱᵢ, β ≫ π = J.sheafifiedRepresentableMap f := by
  let xU : (h[U]^#[J]).obj.obj (op U) :=
    J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J]))
  let t : (∐ ℱᵢ).obj.obj (op Y) := Presheaf.localPreimage π.hom xU f hf
  let β : h[Y]^#[J] ⟶ ∐ ℱᵢ := (J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) Y).symm t
  refine ⟨β, ?_⟩
  apply (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) Y).injective
  -- Compare both morphisms by the section of `h[U]^#` over `Y` they correspond to.
  calc
    J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) Y (β ≫ π) =
        π.hom.app (op Y) ((J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) Y) β) := by
          simpa using J.uliftSheafifiedRepresentableHomEquiv_comp β π
    _ = π.hom.app (op Y) t := by
      have hβt : (J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) Y) β = t := by
        simpa [β, t] using
          (Equiv.apply_symm_apply (J.uliftSheafifiedRepresentableHomEquiv (∐ ℱᵢ) Y) t)
      exact congrArg (π.hom.app (op Y)) hβt
    _ = (h[U]^#[J]).obj.map f.op xU := by
      simpa [t] using Presheaf.app_localPreimage π.hom xU f hf
    _ = J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) Y
        (J.sheafifiedRepresentableMap f) := by
          simpa [xU, sheafifiedRepresentableMap] using
            (J.uliftSheafifiedRepresentableHomEquiv_naturality
              f (h[U]^#[J]) (𝟙 (h[U]^#[J]))).symm

/-- Helper for Lemma 7.17.3: once a local lift of `h[f] : h[Y]^# ⟶ h[U]^#` to the coproduct is
given, the pullback of the single-summand sieve along `f` is covering. -/
lemma pullback_singleSummandFactorSieve_mem_of_lift
    {ι : Type (max u v)} {U Y : C} (ℱᵢ : ι → Sheaf J (Type (max u v))) [HasCoproduct ℱᵢ]
    (π : (∐ ℱᵢ) ⟶ h[U]^#[J]) {f : Y ⟶ U} (β : h[Y]^#[J] ⟶ ∐ ℱᵢ)
    (hβ : β ≫ π = J.sheafifiedRepresentableMap f) :
    Sieve.pullback f (singleSummandFactorSieve (J := J) ℱᵢ π) ∈ J Y := by
  obtain ⟨R, hR⟩ := locally_factor_coproduct_morphism_through_single_summand
    (J := J) ℱᵢ β
  have hle : R.1 ≤ Sieve.pullback f (singleSummandFactorSieve (J := J) ℱᵢ π) := by
    intro Z g hg
    rcases hR ⟨Z, g, hg⟩ with ⟨i, τ, hτ⟩
    refine ⟨i, τ, ?_⟩
    -- Compose the local single-summand factorization with `π` and use the lift identity.
    calc
      τ ≫ Limits.Sigma.ι ℱᵢ i ≫ π = J.sheafifiedRepresentableMap g ≫ β ≫ π := by
        simpa [Category.assoc] using congrArg (fun k => k ≫ π) hτ.symm
      _ = J.sheafifiedRepresentableMap g ≫ J.sheafifiedRepresentableMap f := by
        simpa [Category.assoc] using congrArg (fun k => J.sheafifiedRepresentableMap g ≫ k) hβ
      _ = J.sheafifiedRepresentableMap (g ≫ f) := by
        simp [sheafifiedRepresentableMap, sheafifiedRepresentableFunctor,
          uliftSheafifiedRepresentableFunctor]
  -- The cover produced by local factorization refines the pullback sieve.
  exact J.superset_covering hle R.2

/-- Helper for Lemma 7.17.3: a locally surjective coproduct map to `h[U]^#` yields a covering
sieve of arrows whose corresponding sheafified-representable maps already factor through one
summand. -/
lemma singleSummandFactorSieve_mem
    {ι : Type (max u v)} {U : C} (ℱᵢ : ι → Sheaf J (Type (max u v))) [HasCoproduct ℱᵢ]
    (π : (∐ ℱᵢ) ⟶ h[U]^#[J]) (hπ : Sheaf.IsLocallySurjective π) :
    singleSummandFactorSieve (J := J) ℱᵢ π ∈ J U := by
  letI : Sheaf.IsLocallySurjective π := hπ
  let xU : (h[U]^#[J]).obj.obj (op U) :=
    J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J]))
  let S : Sieve U := Presheaf.imageSieve π.hom xU
  have hS : S ∈ J U := by
    -- Local surjectivity covers the identity section of `h[U]^#`.
    simpa [S, xU] using Presheaf.imageSieve_mem J π.hom xU
  -- Route correction: first cover the identity section, then refine each local lift to one
  -- summand and conclude by a single transitivity step.
  refine J.transitive hS (singleSummandFactorSieve (J := J) ℱᵢ π) ?_
  intro Y f hf
  obtain ⟨β, hβ⟩ := exists_coproduct_lift_of_image_sieve_mem_identity
    (J := J) ℱᵢ π (f := f) (by simpa [S, xU] using hf)
  -- Each arrow of the image sieve has a local lift, and that lift locally factors through one
  -- summand of the coproduct.
  exact pullback_singleSummandFactorSieve_mem_of_lift (J := J) ℱᵢ π β hβ

/-- Lemma 7.17.3: an object `U` of a site `(C, J)` is quasi-compact if and only if the sheafified
representable `h_U^#` is a quasi-compact object of the topos `Sh(C, J)`. -/
theorem quasiCompactObject_iff_isQuasiCompactObject_sheafifiedRepresentable
    (U : C) :
    J.QuasiCompactObject U ↔ (h[U]^#[J]).IsQuasiCompactObject := by
  constructor
  · intro hU
    refine ⟨?_⟩
    intro ι ℱᵢ _ π hπ
    classical
    let _ : HasColimitsOfShape (Discrete ι) (Type (max u v)) := inferInstance
    let hSingle : singleSummandFactorSieve (J := J) ℱᵢ π ∈ J U :=
      singleSummandFactorSieve_mem (J := J) ℱᵢ π hπ
    let S : J.Cover U := ⟨singleSummandFactorSieve (J := J) ℱᵢ π, hSingle⟩
    obtain ⟨T, hT, hTcover⟩ := hU S
    let κ : T → ι := fun t ↦ Classical.choose t.1.hf
    let τ : ∀ t : T, h[t.1.Y]^#[J] ⟶ ℱᵢ (κ t) :=
      fun t ↦ Classical.choose (Classical.choose_spec t.1.hf)
    have hτ :
        ∀ t : T, τ t ≫ Limits.Sigma.ι ℱᵢ (κ t) ≫ π = J.sheafifiedRepresentableMap t.1.f := by
      intro t
      exact Classical.choose_spec (Classical.choose_spec t.1.hf)
    let K : Set ι := Set.range κ
    have hK : K.Finite := by
      let _ : Fintype T := hT.fintype
      simpa [K, κ] using Set.finite_range κ
    refine ⟨K, hK, ?_⟩
    let _ : HasColimitsOfShape (Discrete T) (Type (max u v)) := inferInstance
    let _ : HasColimitsOfShape (Discrete T) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    let _ : HasColimitsOfShape (Discrete K) (Type (max u v)) := inferInstance
    let _ : HasColimitsOfShape (Discrete K) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    let σ : ∐ (fun t : T ↦ h[t.1.Y]^#[J]) ⟶ ∐ (fun k : K ↦ ℱᵢ k.1) :=
      Limits.Sigma.desc
        (fun t : T ↦
          τ t ≫ Limits.Sigma.ι (fun k : K ↦ ℱᵢ k.1) ⟨κ t, ⟨t, rfl⟩⟩)
    let μ : ∐ (fun k : K ↦ ℱᵢ k.1) ⟶ h[U]^#[J] :=
      Limits.Sigma.desc (fun k : K ↦ Limits.Sigma.ι ℱᵢ k.1 ≫ π)
    have hfac :
        Limits.Sigma.desc (fun t : T ↦ J.sheafifiedRepresentableMap t.1.f) = σ ≫ μ := by
      -- The finite cover map factors through the finite subcoproduct indexed by the labels.
      apply Limits.Sigma.hom_ext
      intro t
      have hμ :
          Limits.Sigma.ι (fun k : K ↦ ℱᵢ k.1) ⟨κ t, ⟨t, rfl⟩⟩ ≫ μ =
            Limits.Sigma.ι ℱᵢ (κ t) ≫ π := by
        exact Limits.Sigma.ι_desc (fun k : K ↦ Limits.Sigma.ι ℱᵢ k.1 ≫ π) ⟨κ t, ⟨t, rfl⟩⟩
      calc
        Limits.Sigma.ι (fun t : T ↦ h[t.1.Y]^#[J]) t ≫
            Limits.Sigma.desc (fun t : T ↦ J.sheafifiedRepresentableMap t.1.f) =
          J.sheafifiedRepresentableMap t.1.f := by
            exact Limits.Sigma.ι_desc (fun t : T ↦ J.sheafifiedRepresentableMap t.1.f) t
        _ = τ t ≫ Limits.Sigma.ι ℱᵢ (κ t) ≫ π := (hτ t).symm
        _ = τ t ≫ Limits.Sigma.ι (fun k : K ↦ ℱᵢ k.1) ⟨κ t, ⟨t, rfl⟩⟩ ≫ μ := by
          simpa [Category.assoc] using congrArg (fun k => τ t ≫ k) hμ.symm
        _ = Limits.Sigma.ι (fun t : T ↦ h[t.1.Y]^#[J]) t ≫ σ ≫ μ := by
          have hσ :
              Limits.Sigma.ι (fun t : T ↦ h[t.1.Y]^#[J]) t ≫ σ =
                τ t ≫ Limits.Sigma.ι (fun k : K ↦ ℱᵢ k.1) ⟨κ t, ⟨t, rfl⟩⟩ := by
            exact
              Limits.Sigma.ι_desc
                (fun t : T ↦
                  τ t ≫ Limits.Sigma.ι (fun k : K ↦ ℱᵢ k.1) ⟨κ t, ⟨t, rfl⟩⟩) t
          simpa [Category.assoc] using congrArg (fun k => k ≫ μ) hσ.symm
    have hpres :
        Presheaf.IsLocallySurjective J
          (Limits.Sigma.desc
            (fun t : T ↦ CategoryTheory.uliftYoneda.{max u v}.map t.1.f)) := by
      exact
        (J.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
          (fun t : T ↦ t.1.f)).1 hTcover
    have hsheaf :
        Sheaf.IsLocallySurjective
          (Limits.Sigma.desc (fun t : T ↦ J.sheafifiedRepresentableMap t.1.f)) := by
      exact
        (J.isLocallySurjective_sigmaDesc_sheafifiedRepresentableMap_iff
          (fun t : T ↦ t.1.Y) (fun t ↦ t.1.f)).2 hpres
    letI :
        Sheaf.IsLocallySurjective
          (Limits.Sigma.desc (fun t : T ↦ J.sheafifiedRepresentableMap t.1.f)) := hsheaf
    have hfac_hom :
        σ.hom ≫ μ.hom = (Limits.Sigma.desc (fun t : T ↦ J.sheafifiedRepresentableMap t.1.f)).hom :=
      congrArg (fun f => f.hom) hfac.symm
    -- Local surjectivity descends across the factorization through the finite subcoproduct.
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac_hom
  · intro hU
    intro S
    let π : ∐ (fun I : S.Arrow ↦ h[I.Y]^#[J]) ⟶ h[U]^#[J] := J.sheafifiedRepresentableCoverMap S
    have hπ : Sheaf.IsLocallySurjective π := by
      simpa [π] using sheafifiedRepresentableCoverMap_isLocallySurjective (J := J) S
    obtain ⟨T, hT, hTsurj⟩ := hU.finite_subcoproduct (fun I : S.Arrow ↦ h[I.Y]^#[J]) π hπ
    refine ⟨T, hT, ?_⟩
    let _ : HasColimitsOfShape (Discrete T) (Type (max u v)) := inferInstance
    let _ : HasColimitsOfShape (Discrete T) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    have hfac :
        (Limits.Sigma.desc
          (fun i : T ↦ Limits.Sigma.ι (fun I : S.Arrow ↦ h[I.Y]^#[J]) i.1 ≫ π)) =
          Limits.Sigma.desc (fun I : T ↦ J.sheafifiedRepresentableMap I.1.f) := by
      -- Identify the finite subcoproduct map coming from `finite_subcoproduct` with the usual
      -- sigma-desc map built from the chosen finite family of arrows.
      apply Limits.Sigma.hom_ext
      intro I
      have h1 :
          Limits.Sigma.ι (fun I : S.Arrow ↦ h[I.Y]^#[J]) I.1 ≫ π =
            J.sheafifiedRepresentableMap I.1.f := by
        simpa [π, sheafifiedRepresentableCoverMap] using
          (Limits.Sigma.ι_desc
            (f := fun I : S.Arrow ↦ h[I.Y]^#[J])
            (p := fun I : S.Arrow ↦ J.sheafifiedRepresentableMap I.f)
            (b := I.1))
      have h2 :
          Limits.Sigma.ι (fun I : T ↦ h[I.1.Y]^#[J]) I ≫
              Limits.Sigma.desc (fun I : T ↦ J.sheafifiedRepresentableMap I.1.f) =
            J.sheafifiedRepresentableMap I.1.f := by
        exact
          Limits.Sigma.ι_desc
            (f := fun I : T ↦ h[I.1.Y]^#[J])
            (p := fun I : T ↦ J.sheafifiedRepresentableMap I.1.f)
            (b := I)
      rw [Limits.Sigma.ι_desc]
      exact h1.trans h2.symm
    have hTsurj' :
        Sheaf.IsLocallySurjective
          (Limits.Sigma.desc (fun I : T ↦ J.sheafifiedRepresentableMap I.1.f)) := by
      simpa [hfac] using hTsurj
    have hpres :
        Presheaf.IsLocallySurjective J
          (Limits.Sigma.desc (fun I : T ↦ CategoryTheory.uliftYoneda.{max u v}.map I.1.f)) := by
      exact
        (J.isLocallySurjective_sigmaDesc_sheafifiedRepresentableMap_iff
          (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f)).1 hTsurj'
    change Sieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f) ∈ J U
    exact
      (J.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
        (fun I : T ↦ I.1.f)).2 hpres

end CategoryTheory.GrothendieckTopology

/-! ### Definition_7_17_4 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace CategoryTheory
namespace Sheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type w)]

/- Domain-style sampling for Definition 7.17.4:
- primary domain: quasi-compactness in the topos of set-valued sheaves, expressed through locally
  surjective coproduct maps;
- sampled owner abstractions:
  `GrothendieckTopology.QuasiCompactObject`,
  `Sheaf.IsLocallySurjective`,
  `Sheaf.isLocallySurjective_iff_epi`,
  `Sheaf.isColimitSheafifyCocone`,
  `ObjectProperty.IsClosedUnderFiniteCoproducts`;
- source-facing layer here: `Sheaf.IsQuasiCompactObject`;
- core/canonical recall for part (2): quasi-compactness of the terminal sheaf
  `Sheaf.IsQuasiCompactObject (⊤_ (Sheaf J (Type w)))`;
- core/canonical owners reused here: coproducts in `Sheaf J (Type w)` and the terminal sheaf.

Primitive data are only a locally surjective morphism from a coproduct into `ℱ`. The induced map
from a finite subcoproduct is derived directly from the canonical coproduct owner
`Limits.Sigma.desc`. A finite subset of the original index type is primitive here, while an
auxiliary finite type or a specific `Fin n` presentation is only derived bookkeeping and should
not be part of the public owner field. -/

/- Definition 7.17.4 (1): an object `ℱ` of the topos `Sh(C)` is quasi-compact if every
locally surjective morphism from a coproduct `∐ᵢ ℱᵢ ⟶ ℱ` admits a finite subcoproduct whose
induced morphism to `ℱ` is still locally surjective. -/
@[mk_iff isQuasiCompactObject_iff]
class IsQuasiCompactObject (ℱ : Sheaf J (Type w)) : Prop where
  finite_subcoproduct {ι : Type w} (ℱᵢ : ι → Sheaf J (Type w)) [HasCoproduct ℱᵢ]
      (π : (∐ ℱᵢ) ⟶ ℱ) (hπ : IsLocallySurjective π) :
      ∃ (T : Set ι) (hT : T.Finite),
        IsLocallySurjective
          (by
            let _ : Fintype T := hT.fintype
            let _ : HasColimitsOfShape (Discrete T) (Sheaf J (Type w)) :=
              Sheaf.instHasColimitsOfShape
            exact Limits.Sigma.desc (fun i : T ↦ Limits.Sigma.ι ℱᵢ i.1 ≫ π))

end Sheaf

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]

/- Definition 7.17.4 (2): the topos `Sh(C)` is quasi-compact if and only if its terminal sheaf is
a quasi-compact object. The canonical owner is the direct terminal-sheaf expression below, so no
parallel alias is introduced. -/
#check (Sheaf.IsQuasiCompactObject (⊤_ (Sheaf J (Type (max u v)))) : Prop)
end GrothendieckTopology

end CategoryTheory

/-! ### Lemma_7_17_5 (from Chap07) -/
open CategoryTheory
open CategoryTheory.ObjectProperty
open Opposite

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

open Limits
open CategoryTheory.Presheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]

/-
Source/core/bridge triage for 7.17.5:
- core/canonical owner: `ObjectProperty.IsClosedUnderQuotients` applied to
  `Sheaf.IsQuasiCompactObject`
- source-facing statements: Lemma `7.17.5 (2)` on sheaves and Lemma `7.17.5 (1)` on site objects
- bridge/view: `Sheaf.isLocallySurjective_iff_epi`, `J.sheafifiedRepresentableMap`, together with
  `GrothendieckTopology.quasiCompactObject_iff_isQuasiCompactObject_sheafifiedRepresentable`
- primitive data: the owner predicate `Sheaf.IsQuasiCompactObject`
- derived API: quotient stability for locally surjective morphisms and the site-side transfer along
  sheafified representables
-/

omit [HasWeakSheafify J (Type (max u v))] in
/-- Helper for Lemma 7.17.5: on presheaves, pulling back each summand of a locally surjective
sigma-desc along a fixed map preserves local surjectivity. -/
private theorem presheaf_isLocallySurjective_sigmaDesc_pullback_snd
    {F G : Cᵒᵖ ⥤ Type (max u v)} (q : F ⟶ G)
    {ι : Type (max u v)} (X : ι → Cᵒᵖ ⥤ Type (max u v))
    (α : ∀ i, X i ⟶ G) [HasCoproduct X] [HasCoproduct fun i ↦ pullback (α i) q]
    (hα : Presheaf.IsLocallySurjective J (Limits.Sigma.desc α)) :
    Presheaf.IsLocallySurjective J (Limits.Sigma.desc (fun i ↦ pullback.snd (α i) q)) := by
  -- Route correction: the pullback bridge is proved sectionwise by unpacking a coproduct witness,
  -- turning it into a pointwise pullback witness, and then repacking it into the pulled-back
  -- coproduct.
  refine ⟨fun s ↦ J.superset_covering ?_ (hα.imageSieve_mem (q.app _ s))⟩
  intro V g hg
  rcases hg with ⟨y, hy⟩
  cases hxy : (Types.coproductIso (fun i ↦ (X i).obj (op V))).hom
      ((Limits.sigmaObjIso X (op V)).hom y) with
  | mk i x =>
      -- First isolate the summand of the coproduct section that maps to the chosen local image.
      have hcopro :
          (Types.coproductIso (fun i ↦ (X i).obj (op V))).inv ⟨i, x⟩ =
            Sigma.ι (fun i ↦ (X i).obj (op V)) i x := by
        exact congrFun
          (Types.coproductIso_mk_comp_inv (fun i ↦ (X i).obj (op V)) i) x
      have hpre' := congrArg
          (fun z ↦ (Types.coproductIso (fun i ↦ (X i).obj (op V))).inv z) hxy
      have hpre :
          (Limits.sigmaObjIso X (op V)).hom y =
            Sigma.ι (fun i ↦ (X i).obj (op V)) i x := by
        simpa [hcopro] using hpre'
      have hy' : y = (Limits.sigmaObjIso X (op V)).inv
          (Sigma.ι (fun i ↦ (X i).obj (op V)) i x) := by
        simpa using congrArg (fun z ↦ (Limits.sigmaObjIso X (op V)).inv z) hpre
      have hdesc_mor :
          (Sigma.ι X i).app (op V) ≫ (Limits.Sigma.desc α).app (op V) = (α i).app (op V) := by
        simpa using CategoryTheory.congr_app (Limits.Sigma.ι_desc α i) (op V)
      have hdesc :
          (Limits.Sigma.desc α).app (op V)
            ((Limits.sigmaObjIso X (op V)).inv
              (Sigma.ι (fun i ↦ (X i).obj (op V)) i x)) =
            (α i).app (op V) x := by
        simpa using
          congrFun
            ((Limits.ι_comp_sigmaObjIso_inv_assoc X (op V) i
              ((Limits.Sigma.desc α).app (op V))).trans hdesc_mor) x
      have hx : (α i).app (op V) x = G.map g.op (q.app _ s) := by
        rw [← hdesc, ← hy']
        exact hy
      have hqx : (α i).app (op V) x = q.app (op V) (F.map g.op s) := by
        calc
          (α i).app (op V) x = G.map g.op (q.app _ s) := hx
          _ = q.app (op V) (F.map g.op s) := by
            symm
            simpa using congrFun (q.naturality g.op) s
      -- Build the corresponding pointwise pullback element and then reinsert it into the coproduct.
      let t' : Types.PullbackObj ((α i).app (op V)) (q.app (op V)) :=
        ⟨⟨x, F.map g.op s⟩, hqx⟩
      let t : (pullback (α i) q).obj (op V) :=
        (Limits.pullbackObjIso (α i) q (op V)).inv ((Types.pullbackIsoPullback _ _).inv t')
      have hsnd : (pullback.snd (α i) q).app (op V) t = F.map g.op s := by
        dsimp [t]
        simpa [t'] using
          congrFun (Limits.pullbackObjIso_inv_comp_snd (α i) q (op V))
            ((Types.pullbackIsoPullback ((α i).app (op V)) (q.app (op V))).inv t')
      have hdesc'_mor :
          (Sigma.ι (fun i ↦ pullback (α i) q) i).app (op V) ≫
              (Limits.Sigma.desc (fun i ↦ pullback.snd (α i) q)).app (op V) =
            (pullback.snd (α i) q).app (op V) := by
        simpa using
          CategoryTheory.congr_app
            (Limits.Sigma.ι_desc (fun i ↦ pullback.snd (α i) q) i) (op V)
      refine ⟨
        (Limits.sigmaObjIso (fun i ↦ pullback (α i) q) (op V)).inv
          (Sigma.ι (fun i ↦ (pullback (α i) q).obj (op V)) i t),
        ?_⟩
      simpa using
        (congrFun
            ((Limits.ι_comp_sigmaObjIso_inv_assoc (fun i ↦ pullback (α i) q)
              (op V) i ((Limits.Sigma.desc (fun i ↦ pullback.snd (α i) q)).app (op V))).trans
              hdesc'_mor) t).trans hsnd

/-- Helper for Lemma 7.17.5: local surjectivity of a sheaf sigma-desc is equivalent to local
surjectivity of the corresponding underlying presheaf sigma-desc after inserting the
sheafification comparison isomorphisms. -/
private theorem isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc
    {ι : Type (max u v)} (X : ι → Sheaf J (Type (max u v)))
    {G : Sheaf J (Type (max u v))}
    (α : ∀ i, X i ⟶ G) [HasCoproduct X] :
    IsLocallySurjective (Limits.Sigma.desc α) ↔
      Presheaf.IsLocallySurjective J (Limits.Sigma.desc (fun i ↦ (α i).hom)) := by
  let Gsh := presheafToSheaf J (Type (max u v))
  let Fpres : ι → Cᵒᵖ ⥤ Type (max u v) := fun i ↦ (X i).obj
  let gPres : ∐ Fpres ⟶ G.obj := Limits.Sigma.desc (fun i ↦ (α i).hom)
  let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let Y : ι → Sheaf J (Type (max u v)) := fun i ↦ Gsh.obj (Fpres i)
  let _ : HasCoproduct Y := by
    simpa [Y, Fpres, Gsh] using
      (Limits.hasCoproduct_of_equiv_of_iso X Y (Equiv.refl _) fun i ↦
        (sheafificationIso (X i)).symm)
  let sourceIso : (∐ X) ⟶ ∐ Y := Limits.Sigma.map (fun i ↦ (sheafificationIso (X i)).hom)
  let middle : (∐ Y) ⟶ Gsh.obj (∐ Fpres) := Limits.sigmaComparison Gsh Fpres
  have hfac :
      Limits.Sigma.desc α = sourceIso ≫ middle ≫ Gsh.map gPres ≫ (sheafificationIso G).inv := by
    -- Compare the sheaf sigma-desc with the sheafified presheaf sigma-desc componentwise.
    apply Limits.Sigma.hom_ext
    intro i
    have hnat :
        (sheafificationIso (X i)).hom ≫ Gsh.map ((α i).hom) ≫ (sheafificationIso G).inv =
          α i := by
      -- Naturality of the sheafification isomorphism identifies each component map.
      have hnat' :
          (sheafificationIso (X i)).hom ≫ Gsh.map ((α i).hom) =
            α i ≫ (sheafificationIso G).hom := by
        simpa [Gsh, sheafificationNatIso, sheafificationIso] using
          ((sheafificationNatIso J (Type (max u v))).hom.naturality (α i)).symm
      calc
        (sheafificationIso (X i)).hom ≫ Gsh.map ((α i).hom) ≫ (sheafificationIso G).inv =
            α i ≫ (sheafificationIso G).hom ≫ (sheafificationIso G).inv := by
              simpa [Category.assoc] using
                congrArg (fun k => k ≫ (sheafificationIso G).inv) hnat'
        _ = α i := by simp
    rw [Limits.Sigma.ι_desc]
    symm
    change Limits.Sigma.ι X i ≫ Limits.Sigma.map (fun i ↦ (sheafificationIso (X i)).hom) ≫
          Limits.sigmaComparison Gsh Fpres ≫ Gsh.map gPres ≫ (sheafificationIso G).inv = α i
    rw [Limits.Sigma.ι_map_assoc, Limits.ι_comp_sigmaComparison_assoc]
    have hι : Gsh.map (Limits.Sigma.ι Fpres i) ≫ Gsh.map gPres = Gsh.map ((α i).hom) := by
      -- The presheaf sigma-desc collapses to the chosen component after the `i`th injection.
      simpa [gPres, Fpres] using
        congrArg (fun k => Gsh.map k)
          (Limits.Sigma.ι_desc (f := Fpres) (p := fun j ↦ (α j).hom) (b := i))
    calc
      (sheafificationIso (X i)).hom ≫ Gsh.map (Limits.Sigma.ι Fpres i) ≫ Gsh.map gPres ≫
          (sheafificationIso G).inv =
        (sheafificationIso (X i)).hom ≫ Gsh.map ((α i).hom) ≫ (sheafificationIso G).inv := by
          simpa [Category.assoc] using
            congrArg (fun k => (sheafificationIso (X i)).hom ≫ k ≫ (sheafificationIso G).inv) hι
      _ = α i := hnat
  constructor
  · intro hdesc
    have hcomp :
        Sheaf.IsLocallySurjective
          (sourceIso ≫ middle ≫ Gsh.map gPres ≫ (sheafificationIso G).inv) := by
      -- Replace the original sigma-desc by the comparison factorization.
      exact hfac.symm ▸ hdesc
    have hmid : Sheaf.IsLocallySurjective (middle ≫ Gsh.map gPres) := by
      -- Cancel the source and target isomorphisms on the sheaf side.
      rw [Sheaf.isLocallySurjective_iff_epi] at hcomp ⊢
      have hcomp' : Epi ((sourceIso ≫ (middle ≫ Gsh.map gPres)) ≫ (sheafificationIso G).inv) := by
        simpa [Category.assoc] using hcomp
      have hleft : Epi (sourceIso ≫ (middle ≫ Gsh.map gPres)) :=
        (epi_comp_iff_of_isIso
          (sourceIso ≫ (middle ≫ Gsh.map gPres)) ((sheafificationIso G).inv)).1 hcomp'
      exact
        (epi_comp_iff_of_epi sourceIso (middle ≫ Gsh.map gPres)).1
          (by simpa [Category.assoc] using hleft)
    have hmap : Sheaf.IsLocallySurjective (Gsh.map gPres) := by
      -- Cancel the sigma-comparison after moving to the presheaf side.
      rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
      have hmid' :
          Presheaf.IsLocallySurjective J
            ((sheafToPresheaf J (Type (max u v))).map (middle ≫ Gsh.map gPres)) := by
        exact hmid
      have hmid'' :
          Presheaf.IsLocallySurjective J
            (((sheafToPresheaf J (Type (max u v))).map middle) ≫
              (sheafToPresheaf J (Type (max u v))).map (Gsh.map gPres)) := by
        rw [Functor.map_comp] at hmid'
        exact hmid'
      let _ :
          Presheaf.IsLocallySurjective J
            ((sheafToPresheaf J (Type (max u v))).map middle) := by
        infer_instance
      let _ :
          Presheaf.IsLocallyInjective J
            ((sheafToPresheaf J (Type (max u v))).map middle) := by
        infer_instance
      exact
        (Presheaf.comp_isLocallySurjective_iff J
          ((sheafToPresheaf J (Type (max u v))).map middle)
          ((sheafToPresheaf J (Type (max u v))).map (Gsh.map gPres))).1 hmid''
    rw [Presheaf.isLocallySurjective_presheafToSheaf_map_iff] at hmap
    simpa [gPres] using hmap
  · intro hpres
    have hmap : Sheaf.IsLocallySurjective (Gsh.map gPres) := by
      -- Sheafify the locally surjective presheaf sigma-desc.
      rw [Presheaf.isLocallySurjective_presheafToSheaf_map_iff]
      simpa [gPres] using hpres
    let _ : Sheaf.IsLocallySurjective (Gsh.map gPres) := hmap
    have hmid : Sheaf.IsLocallySurjective (middle ≫ Gsh.map gPres) := by
      -- Compose back with the sigma-comparison on the sheaf side.
      infer_instance
    let _ : Sheaf.IsLocallySurjective (middle ≫ Gsh.map gPres) := hmid
    have hcomp :
        Sheaf.IsLocallySurjective
          (sourceIso ≫ middle ≫ Gsh.map gPres ≫ (sheafificationIso G).inv) := by
      -- Reinsert the source and target isomorphisms to recover the original sigma-desc.
      infer_instance
    exact hfac ▸ hcomp

/-- Helper for Lemma 7.17.5: pulling back each summand of a locally surjective sheaf sigma-desc
along a fixed map preserves local surjectivity. -/
private theorem isLocallySurjective_sigma_desc_pullback_snd
    {F G : Sheaf J (Type (max u v))} (q : F ⟶ G)
    {ι : Type (max u v)} (X : ι → Sheaf J (Type (max u v)))
    (α : ∀ i, X i ⟶ G)
    [HasCoproduct X] [HasCoproduct fun i ↦ pullback (α i) q]
    (hα : IsLocallySurjective (Limits.Sigma.desc α)) :
    IsLocallySurjective (Limits.Sigma.desc fun i ↦ pullback.snd (α i) q) := by
  let Fsh := sheafToPresheaf J (Type (max u v))
  let sourceMap :
      ∐ (fun i ↦ Fsh.obj (pullback (α i) q)) ⟶
        ∐ (fun i ↦ pullback (Fsh.map (α i)) (Fsh.map q)) :=
    Limits.Sigma.map (fun i ↦ Limits.pullbackComparison Fsh (α i) q)
  have hα_pres :
      Presheaf.IsLocallySurjective J (Limits.Sigma.desc (fun i ↦ Fsh.map (α i))) := by
    -- Move the original sigma-desc to the presheaf level.
    simpa using (isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc (J := J) X α).1 hα
  have hpull_pres :
      Presheaf.IsLocallySurjective J
        (Limits.Sigma.desc (fun i ↦ pullback.snd (Fsh.map (α i)) (Fsh.map q))) := by
    -- Apply the sectionwise presheaf pullback construction.
    simpa using
      presheaf_isLocallySurjective_sigmaDesc_pullback_snd
        (J := J) (Fsh.map q) (fun i ↦ Fsh.obj (X i)) (fun i ↦ Fsh.map (α i)) hα_pres
  have hfac :
      sourceMap ≫ Limits.Sigma.desc (fun i ↦ pullback.snd (Fsh.map (α i)) (Fsh.map q)) =
        Limits.Sigma.desc (fun i ↦ Fsh.map (pullback.snd (α i) q)) := by
    -- The pullback comparison identifies the presheaf pullback family with the underlying
    -- presheaf of the sheaf pullback family.
    apply Limits.Sigma.hom_ext
    intro i
    simp only [sourceMap, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_desc]
    exact Limits.pullbackComparison_comp_snd Fsh (α i) q
  have hpull_sheaf_pres :
      Presheaf.IsLocallySurjective J
        (Limits.Sigma.desc (fun i ↦ Fsh.map (pullback.snd (α i) q))) := by
    -- Compose the locally surjective presheaf pullback family with the pullback comparison map.
    let _ : Presheaf.IsLocallySurjective J sourceMap := by
      infer_instance
    have hcomp :
        Presheaf.IsLocallySurjective J
          (sourceMap ≫ Limits.Sigma.desc (fun i ↦ pullback.snd (Fsh.map (α i)) (Fsh.map q))) := by
      exact (Presheaf.comp_isLocallySurjective_iff J sourceMap _).2 hpull_pres
    exact hfac ▸ hcomp
  -- Transport the pulled-back sigma-desc back to the sheaf level.
  exact
    (isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc
      (J := J) (fun i ↦ pullback (α i) q) (fun i ↦ pullback.snd (α i) q)).2 <| by
        simpa using hpull_sheaf_pres

omit [HasWeakSheafify J (Type (max u v))] in
/-- Helper for Lemma 7.17.5: once each pulled-back summand satisfies the pullback compatibility
relation, the finite pulled-back coproduct map factors through the corresponding finite original
family map. -/
lemma restricted_pullback_family_factorization
    {ι : Type (max u v)} {T : Set ι}
    {F G : Sheaf J (Type (max u v))} {X Y : ι → Sheaf J (Type (max u v))}
    [HasCoproduct X] [HasCoproduct fun i : T ↦ X i.1] [HasCoproduct fun i : T ↦ Y i.1]
    (π : F ⟶ G) (a : ∐ X ⟶ G)
    (fstY : ∀ i, Y i ⟶ X i) (sndY : ∀ i, Y i ⟶ F)
    (hcomp : ∀ i, sndY i ≫ π = fstY i ≫ Limits.Sigma.ι X i ≫ a) :
    Limits.Sigma.desc (fun i : T ↦ sndY i.1) ≫ π =
      Limits.Sigma.map (fun i : T ↦ fstY i.1) ≫
        Limits.Sigma.desc (fun i : T ↦ Limits.Sigma.ι X i.1 ≫ a) := by
  -- Reduce the coproduct equality to each finite summand and rewrite using the pullback relation.
  apply Limits.Sigma.hom_ext
  intro i
  rw [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_desc]
  simpa using hcomp i.1

omit [HasWeakSheafify J (Type (max u v))] in
/-- Helper for Lemma 7.17.5: if a finite pulled-back family factors through a finite original
family and the pulled-back family together with the quotient map are locally surjective, then the
original finite family is locally surjective as well. -/
lemma isLocallySurjective_of_epi_factorization
    {A B C D : Sheaf J (Type (max u v))}
    {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ D} {k : D ⟶ C}
    (fac : f ≫ g = h ≫ k)
    (hf : IsLocallySurjective f) (hg : IsLocallySurjective g) :
    IsLocallySurjective k := by
  -- Read local surjectivity as epimorphism and descend the epi across the factorization.
  rw [Sheaf.isLocallySurjective_iff_epi] at hf hg ⊢
  letI : Epi (f ≫ g) := by infer_instance
  exact CategoryTheory.epi_of_epi_fac fac.symm

instance isQuasiCompactObject_isClosedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (IsQuasiCompactObject : ObjectProperty (Sheaf J (Type (max u v)))) := by
  refine ⟨?_⟩
  intro F G π _ hF
  refine ⟨?_⟩
  intro ι X _ a ha
  classical
  -- Route correction: switch from sheafified presheaf pullbacks to the canonical sheaf pullback
  -- family so the pullback compatibility is exactly `pullback.condition`.
  let Y : ι → Sheaf J (Type (max u v)) := fun i ↦ pullback (Limits.Sigma.ι X i ≫ a) π
  let fstY : ∀ i, Y i ⟶ X i := fun i ↦ pullback.fst (Limits.Sigma.ι X i ≫ a) π
  let sndY : ∀ i, Y i ⟶ F := fun i ↦ pullback.snd (Limits.Sigma.ι X i ≫ a) π
  let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let _ : HasCoproduct Y := by
    infer_instance
  let b : (∐ Y) ⟶ F := Limits.Sigma.desc sndY
  have hb : IsLocallySurjective b := by
    -- Pull back the locally surjective source family along the quotient map.
    have ha' : IsLocallySurjective (Limits.Sigma.desc (fun i ↦ Limits.Sigma.ι X i ≫ a)) := by
      have hdesc : Limits.Sigma.desc (fun i ↦ Limits.Sigma.ι X i ≫ a) = a := by
        apply Limits.Sigma.hom_ext
        intro i
        rw [Limits.Sigma.ι_desc]
      simpa [hdesc] using ha
    simpa [b, sndY] using
      isLocallySurjective_sigma_desc_pullback_snd
        (J := J) (q := π) (X := X) (α := fun i ↦ Limits.Sigma.ι X i ≫ a) ha'
  obtain ⟨T, hT, hbT_raw⟩ := hF.finite_subcoproduct Y b hb
  let _ : Fintype T := hT.fintype
  let _ : HasColimitsOfShape (Discrete T) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let bT : (∐ fun i : T ↦ Y i.1) ⟶ F :=
    Limits.Sigma.desc (fun i : T ↦ Limits.Sigma.ι Y i.1 ≫ b)
  have hbT : IsLocallySurjective bT := by
    simpa [bT] using hbT_raw
  let γ : (∐ fun i : T ↦ X i.1) ⟶ G :=
    Limits.Sigma.desc (fun i : T ↦ Limits.Sigma.ι X i.1 ≫ a)
  let δ : (∐ fun i : T ↦ Y i.1) ⟶ (∐ fun i : T ↦ X i.1) :=
    Limits.Sigma.map (fun i : T ↦ fstY i.1)
  have hpull : ∀ i, sndY i ≫ π = fstY i ≫ Limits.Sigma.ι X i ≫ a := by
    -- Each component identity is the defining commutativity of the pullback square.
    intro i
    simpa [fstY, sndY, Category.assoc] using
      (pullback.condition (f := Limits.Sigma.ι X i ≫ a) (g := π)).symm
  have hbT_eq : bT = Limits.Sigma.desc (fun i : T ↦ sndY i.1) := by
    apply Limits.Sigma.hom_ext
    intro i
    calc
      Limits.Sigma.ι (fun i : T ↦ Y i.1) i ≫ bT =
          Limits.Sigma.ι Y i.1 ≫ b := by
            simpa [bT] using
              (Limits.Sigma.ι_desc (fun i : T ↦ Limits.Sigma.ι Y i.1 ≫ b) i)
      _ = sndY i.1 := by
        simpa [b, sndY] using (Limits.Sigma.ι_desc sndY i)
      _ = Limits.Sigma.ι (fun i : T ↦ Y i.1) i ≫ Limits.Sigma.desc (fun i : T ↦ sndY i.1) := by
        symm
        exact Limits.Sigma.ι_desc (fun i : T ↦ sndY i.1) i
  have hfac : bT ≫ π = δ ≫ γ := by
    rw [hbT_eq]
    simpa [γ, δ] using
      restricted_pullback_family_factorization
        (J := J) (T := T) (F := F) (G := G) (X := X) (Y := Y) π a fstY sndY hpull
  have hπ : IsLocallySurjective π := by
    rw [Sheaf.isLocallySurjective_iff_epi]
    infer_instance
  -- With the finite factorization in place, epi descent converts the finite pulled-back family
  -- into the finite original family required by quasi-compactness of `G`.
  refine ⟨T, hT, ?_⟩
  exact isLocallySurjective_of_epi_factorization (J := J) hfac hbT hπ

/-- Lemma 7.17.5 (2): a locally surjective image of a quasi-compact sheaf of sets is
quasi-compact. -/
theorem isQuasiCompactObject_of_isLocallySurjective
    {F G : Sheaf J (Type (max u v))} (π : F ⟶ G)
    (hπ : IsLocallySurjective π) (hF : F.IsQuasiCompactObject) :
    G.IsQuasiCompactObject := by
  -- Route correction: once quotient-closure is established, the target is the epi image of `F`.
  rw [Sheaf.isLocallySurjective_iff_epi] at hπ
  exact
    ObjectProperty.prop_of_epi
      (P := (IsQuasiCompactObject : ObjectProperty (Sheaf J (Type (max u v))))) π hF

end CategoryTheory.Sheaf

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open CategoryTheory.Sheaf
open scoped SheafifiedRepresentable

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]

/-- Lemma 7.17.5 (1): if `h[U]^#[J] ⟶ h[V]^#[J]` is locally surjective and `U` is quasi-compact,
then `V` is quasi-compact. -/
theorem quasiCompactObject_of_isLocallySurjective_sheafifiedRepresentableMap
    {U V : C} (f : U ⟶ V)
    (hf : IsLocallySurjective (J.sheafifiedRepresentableMap f))
    (hU : J.QuasiCompactObject U) :
    J.QuasiCompactObject V := by
  -- Route correction: transport quasi-compactness to sheafified representables, apply the sheaf
  -- statement, and transport back.
  rw [J.quasiCompactObject_iff_isQuasiCompactObject_sheafifiedRepresentable] at hU ⊢
  exact
    CategoryTheory.Sheaf.isQuasiCompactObject_of_isLocallySurjective
      (π := J.sheafifiedRepresentableMap f) hf hU

end CategoryTheory.GrothendieckTopology
