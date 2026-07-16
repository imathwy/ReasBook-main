import Mathlib
import Mathlib.Data.List.TFAE
import stacks_proof.stacks_project.Chap18.Definition_18_40_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget CommRingCat.{max u v})]
variable [HasWeakSheafify J (Type (max u v))]

/- Domain-style sampling for Lemma 18.40.1:
- primary domain: local surjectivity of morphisms of set-valued sheaves attached to the structure
  sheaf of a ringed site;
- sampled owner declarations:
  `HasLocalUnitDichotomy`,
  `Sheaf.IsLocallySurjective`,
  `oneNeverZeroEqualizerMap`,
  `Limits.coprod.desc`,
  `Limits.prod.lift`;
- best owner abstraction: the intrinsic binary factorization morphism in `Sheaf J (Type _)`
  from the coproduct of two copies of `O ⨯ O` to `O ⨯ O`, where `O` is the underlying
  set-valued structure sheaf;
- primitive data: the two component morphisms `O ⨯ O ⟶ O ⨯ O` sending `(f, a)` to `(f, af)` and
  `(f, b)` to `(f, b(1 - f))`;
- derived API: local surjectivity of the canonical coproduct map and its sectionwise
  factorization reformulation.
Source/core/bridge triage:
- `source-facing`: `binaryFactorizationMap` and `ringed_site_local_unit_tfae`;
- `core/canonical`: `Sheaf.IsLocallySurjective`, `Limits.prod.lift`, and `Limits.coprod.desc`;
- `bridge/view`: the internal component maps on the underlying set-valued structure sheaf.
-/

variable (𝒪 : Sheaf J CommRingCat.{max u v})

private abbrev underlyingTypeSheaf (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf J (Type (max u v)) :=
  (sheafCompose J (forget CommRingCat)).obj 𝒪

local notation "O" => underlyingTypeSheaf 𝒪

private def binaryFactorizationSecond
    (g : ∀ {U : Cᵒᵖ}, 𝒪.obj.obj U → 𝒪.obj.obj U → 𝒪.obj.obj U)
    (hg :
      ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a b : 𝒪.obj.obj U),
        g ((𝒪.obj.map f).hom a) ((𝒪.obj.map f).hom b) =
          (𝒪.obj.map f).hom (g a b)) :
    O ⨯ O ⟶ O :=
  { hom :=
      { app := fun U x ↦
          g ((prod.snd : O ⨯ O ⟶ O).hom.app U x) ((prod.fst : O ⨯ O ⟶ O).hom.app U x)
        naturality := by
          intro U V f
          ext x
          have hsnd : (prod.snd : O ⨯ O ⟶ O).hom.app V ((O ⨯ O).obj.map f x) =
              (𝒪.obj.map f).hom ((prod.snd : O ⨯ O ⟶ O).hom.app U x) := by
            simpa using congr_fun ((prod.snd : O ⨯ O ⟶ O).hom.naturality f) x
          have hfst : (prod.fst : O ⨯ O ⟶ O).hom.app V ((O ⨯ O).obj.map f x) =
              (𝒪.obj.map f).hom ((prod.fst : O ⨯ O ⟶ O).hom.app U x) := by
            simpa using congr_fun ((prod.fst : O ⨯ O ⟶ O).hom.naturality f) x
          dsimp
          rw [hsnd, hfst]
          exact hg f _ _ } }

private def binaryFactorizationComponent
    (g : ∀ {U : Cᵒᵖ}, 𝒪.obj.obj U → 𝒪.obj.obj U → 𝒪.obj.obj U)
    (hg :
      ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a b : 𝒪.obj.obj U),
        g ((𝒪.obj.map f).hom a) ((𝒪.obj.map f).hom b) =
          (𝒪.obj.map f).hom (g a b)) :
    O ⨯ O ⟶ O ⨯ O :=
  prod.lift prod.fst (binaryFactorizationSecond 𝒪 g hg)

private def binaryFactorizationLeft : O ⨯ O ⟶ O ⨯ O :=
  binaryFactorizationComponent 𝒪
    (fun a f ↦ a * f)
    (fun f a b ↦ by
      simpa using (RingHom.map_mul ((𝒪.obj.map f).hom) a b).symm)

private def binaryFactorizationRight : O ⨯ O ⟶ O ⨯ O :=
  binaryFactorizationComponent 𝒪
    (fun b f ↦ b * (1 - f))
    (fun f a b ↦ by
      simpa [map_sub] using
        (RingHom.map_mul ((𝒪.obj.map f).hom) a (1 - b)).symm)

local instance binaryFactorizationHasColimit : HasColimit (pair (O ⨯ O) (O ⨯ O)) := by
  let _ : HasColimitsOfShape (Discrete WalkingPair) (Type (max u v)) := inferInstance
  let _ : HasColimitsOfShape (Discrete WalkingPair) (Sheaf J (Type (max u v))) :=
    (Sheaf.instHasColimitsOfShape :
      HasColimitsOfShape (Discrete WalkingPair) (Sheaf J (Type (max u v))))
  infer_instance

/-- The binary factorization morphism from Stacks `18.40.1 (3)`, expressed as a morphism of
set-valued sheaves. With `O` the underlying set-valued sheaf of `𝒪`, this is the canonical
morphism `((O ⨯ O) ⨿ (O ⨯ O)) ⟶ (O ⨯ O)` whose left summand sends `(f, a)` to `(f, af)` and
whose right summand sends `(f, b)` to `(f, b(1 - f))`. -/
def binaryFactorizationMap : (O ⨯ O) ⨿ (O ⨯ O) ⟶ O ⨯ O :=
  coprod.desc (binaryFactorizationLeft 𝒪) (binaryFactorizationRight 𝒪)

variable {𝒪}

/-- Helper for Lemma 18.40.1: the raw presheaf of pairs of sections of `𝒪`, used to model the
sectionwise formulas appearing in clause `(3)` before sheafification. -/
private def rawBinaryFactorizationTarget (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Cᵒᵖ ⥤ Type (max u v) where
  obj U := 𝒪.obj.obj U × 𝒪.obj.obj U
  map f x := ((𝒪.obj.map f).hom x.1, (𝒪.obj.map f).hom x.2)
  map_id := by
    intro U
    funext x
    apply Prod.ext <;> simp
  map_comp := by
    intro U V W f g
    funext x
    apply Prod.ext <;> simp

/-- Helper for Lemma 18.40.1: the raw presheaf coproduct source with left and right tagged local
factorizations, modeled explicitly by a pointwise sum. -/
private def rawBinaryFactorizationSource (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Cᵒᵖ ⥤ Type (max u v) where
  obj U := Sum
    ((rawBinaryFactorizationTarget (J := J) 𝒪).obj U)
    ((rawBinaryFactorizationTarget (J := J) 𝒪).obj U)
  map f := Sum.map
    ((rawBinaryFactorizationTarget (J := J) 𝒪).map f)
    ((rawBinaryFactorizationTarget (J := J) 𝒪).map f)
  map_id := by
    intro U
    funext x
    cases x <;> simp [rawBinaryFactorizationTarget]
  map_comp := by
    intro U V W f g
    funext x
    cases x <;> simp [rawBinaryFactorizationTarget]

/-- Helper for Lemma 18.40.1: the raw presheaf map sending the left tagged summand `(f, a)` to
`(f, af)` and the right tagged summand `(f, b)` to `(f, b(1 - f))`. -/
private def rawBinaryFactorizationMap (𝒪 : Sheaf J CommRingCat.{max u v}) :
    rawBinaryFactorizationSource (J := J) 𝒪 ⟶ rawBinaryFactorizationTarget (J := J) 𝒪 where
  app U x :=
    match x with
    | Sum.inl (f, a) => (f, a * f)
    | Sum.inr (f, b) => (f, b * (1 - f))
  naturality := by
    intro U V f
    funext x
    cases x with
    | inl x =>
        rcases x with ⟨s, a⟩
        apply Prod.ext <;> simp [rawBinaryFactorizationSource, rawBinaryFactorizationTarget,
          RingHom.map_mul]
    | inr x =>
        rcases x with ⟨s, b⟩
        apply Prod.ext <;> simp [rawBinaryFactorizationSource, rawBinaryFactorizationTarget,
          RingHom.map_mul, map_sub]

/-- Helper for Lemma 18.40.1: for the explicit raw presheaf map, lying in the image sieve over
`i : V ⟶ U` is exactly the existence of a left or right local factorization of `c|_i`. -/
private lemma raw_binary_factorization_imageSieve_iff
    (U V : C) (i : V ⟶ U) (f c : 𝒪.obj.obj (op U)) :
    (Presheaf.imageSieve (rawBinaryFactorizationMap (J := J) 𝒪)
        ((f, c) : (rawBinaryFactorizationTarget (J := J) 𝒪).obj (op U))).arrows i ↔
      (∃ a : 𝒪.obj.obj (op V), (𝒪.obj.map i.op).hom c = a * (𝒪.obj.map i.op).hom f) ∨
        ∃ b : 𝒪.obj.obj (op V),
          (𝒪.obj.map i.op).hom c = b * (1 - (𝒪.obj.map i.op).hom f) := by
  rw [Presheaf.imageSieve_apply]
  constructor
  · intro h
    rcases h with ⟨t, ht⟩
    -- Split the tagged witness into the left and right factorization branches from the source text.
    cases t with
    | inl t =>
        rcases t with ⟨g, a⟩
        left
        refine ⟨a, ?_⟩
        have hg : g = (𝒪.obj.map i.op).hom f := by
          exact congrArg (fun x => x.1) ht
        have hc : a * g = (𝒪.obj.map i.op).hom c := by
          exact congrArg (fun x => x.2) ht
        rw [hg] at hc
        exact hc.symm
    | inr t =>
        rcases t with ⟨g, b⟩
        right
        refine ⟨b, ?_⟩
        have hg : g = (𝒪.obj.map i.op).hom f := by
          exact congrArg (fun x => x.1) ht
        have hc : b * (1 - g) = (𝒪.obj.map i.op).hom c := by
          exact congrArg (fun x => x.2) ht
        rw [hg] at hc
        exact hc.symm
  · intro h
    rcases h with ⟨a, ha⟩ | ⟨b, hb⟩
    · -- A left factorization gives an explicit preimage in the left tagged summand.
      refine ⟨Sum.inl (((𝒪.obj.map i.op).hom f), a), ?_⟩
      apply Prod.ext
      · rfl
      · exact ha.symm
    · -- A right factorization gives an explicit preimage in the right tagged summand.
      refine ⟨Sum.inr (((𝒪.obj.map i.op).hom f), b), ?_⟩
      apply Prod.ext
      · rfl
      · exact hb.symm

/-- Helper for Lemma 18.40.1: local surjectivity of the explicit raw presheaf map is exactly the
textbook sectionwise factorization condition in clause `(3)`. -/
private theorem isLocallySurjective_rawBinaryFactorizationMap_iff :
    Presheaf.IsLocallySurjective J (rawBinaryFactorizationMap (J := J) 𝒪) ↔
      ∀ (U : C) (f c : 𝒪.obj.obj (op U)),
        ∃ S : J.Cover U, ∀ I : S.Arrow,
          (∃ a : 𝒪.obj.obj (op I.Y),
              (𝒪.obj.map I.f.op).hom c = a * (𝒪.obj.map I.f.op).hom f) ∨
            ∃ b : 𝒪.obj.obj (op I.Y),
              (𝒪.obj.map I.f.op).hom c = b * (1 - (𝒪.obj.map I.f.op).hom f) := by
  constructor
  · intro h U f c
    letI : Presheaf.IsLocallySurjective J (rawBinaryFactorizationMap (J := J) 𝒪) := h
    let S : J.Cover U := ⟨
      Presheaf.imageSieve (rawBinaryFactorizationMap (J := J) 𝒪)
        ((f, c) : (rawBinaryFactorizationTarget (J := J) 𝒪).obj (op U)),
      Presheaf.imageSieve_mem (J := J) (rawBinaryFactorizationMap (J := J) 𝒪)
        ((f, c) : (rawBinaryFactorizationTarget (J := J) 𝒪).obj (op U))⟩
    refine ⟨S, ?_⟩
    intro I
    -- The canonical image-sieve cover produces the required local factorization on each arrow.
    exact (raw_binary_factorization_imageSieve_iff (J := J) (𝒪 := 𝒪) U I.Y I.f f c).1 I.hf
  · intro h
    refine ⟨?_⟩
    intro U s
    rcases s with ⟨f, c⟩
    obtain ⟨S, hS⟩ := h U f c
    -- A covering family whose arrows all land in the image sieve makes the image sieve covering.
    refine J.superset_covering ?_ S.2
    intro V i hi
    let I : S.Arrow := ⟨V, i, hi⟩
    exact (raw_binary_factorization_imageSieve_iff (J := J) (𝒪 := 𝒪) U V i f c).2 (hS I)

/-- Helper for Lemma 18.40.1: the sheafification of the underlying presheaf of `O × O`. This is
the canonical summand appearing in the source-side comparison with `binaryFactorizationMap`. -/
private abbrev binaryFactorizationSheafifiedTarget :
    Sheaf J (Type (max u v)) :=
  (presheafToSheaf J (Type (max u v))).obj
    ((sheafToPresheaf J (Type (max u v))).obj (O ⨯ O))

private abbrev binaryFactorizationUnderlyingPresheaf :
    Cᵒᵖ ⥤ Type (max u v) :=
  (sheafToPresheaf J (Type (max u v))).obj (O ⨯ O)

local instance binaryFactorizationSheafifiedHasColimit :
    HasColimit
      (pair
        (binaryFactorizationSheafifiedTarget (J := J) (𝒪 := 𝒪))
        (binaryFactorizationSheafifiedTarget (J := J) (𝒪 := 𝒪))) := by
  let _ : HasColimitsOfShape (Discrete WalkingPair) (Sheaf J (Type (max u v))) :=
    (Sheaf.instHasColimitsOfShape :
      HasColimitsOfShape (Discrete WalkingPair) (Sheaf J (Type (max u v))))
  infer_instance

/-- Helper for Lemma 18.40.1: the sheaf coproduct source
`(O × O) ⨿ (O × O)` is canonically the coproduct of the two sheafifications of the underlying
presheaf of `O × O`. This isolates the source-side comparison needed for the final transport to
presheaves. -/
private def binary_factorization_source_iso :
    colimit
        (pair
          (binaryFactorizationSheafifiedTarget (J := J) (𝒪 := 𝒪))
          (binaryFactorizationSheafifiedTarget (J := J) (𝒪 := 𝒪))) ≅
      (O ⨯ O) ⨿ (O ⨯ O) :=
  HasColimit.isoOfNatIso <|
    NatIso.ofComponents
      (fun j ↦ by
        cases j using Discrete.recOn with
        | mk j =>
            cases j with
            | left =>
                -- Each summand is already a sheaf, so the comparison is the counit isomorphism.
                exact (sheafificationIso (O ⨯ O)).symm
            | right =>
                exact (sheafificationIso (O ⨯ O)).symm)
      (by
        intro i j f
        -- The discrete two-point diagram has only identity branches; the mixed branches are
        -- impossible because they would force `WalkingPair.left = WalkingPair.right`.
        ext U x
        cases i using Discrete.recOn with
        | mk i =>
            cases j using Discrete.recOn with
            | mk j =>
                cases i with
                | left =>
                    cases j with
                    | left =>
                        simp
                    | right =>
                        rcases f with ⟨⟨h⟩⟩
                        cases h
                | right =>
                    cases j with
                    | left =>
                        rcases f with ⟨⟨h⟩⟩
                        cases h
                    | right =>
                        simp)

/- Remaining transport gap for Lemma 18.40.1:
the stable binary-coproduct route reduces the proof to two explicit presheaf identifications:
1. identify the underlying presheaf of `O × O` with the raw presheaf of pairs of sections;
2. identify the induced binary coproduct source with the raw `Sum`-presheaf source.
Once those data-level bridges are available, the sheaf comparison follows from
`binary_factorization_source_iso`, `preservesColimitIso`, and
`Presheaf.isLocallySurjective_presheafToSheaf_map_iff`. -/

/-- Helper for Lemma 18.40.1: the first coordinate projection from the explicit raw target
presheaf. -/
private def rawBinaryFactorizationTargetFst :
    rawBinaryFactorizationTarget (J := J) 𝒪 ⟶ (sheafToPresheaf J (Type (max u v))).obj O where
  app U x := x.1
  naturality := by
    intro U V f
    funext x
    rfl

/-- Helper for Lemma 18.40.1: the second coordinate projection from the explicit raw target
presheaf. -/
private def rawBinaryFactorizationTargetSnd :
    rawBinaryFactorizationTarget (J := J) 𝒪 ⟶ (sheafToPresheaf J (Type (max u v))).obj O where
  app U x := x.2
  naturality := by
    intro U V f
    funext x
    rfl

/-- Helper for Lemma 18.40.1: the product of the underlying presheaf of `O` with itself is the
explicit presheaf of pairs of sections used in the raw sectionwise formulas. -/
private def binary_factorization_pair_presheaf_iso :
    ((sheafToPresheaf J (Type (max u v))).obj O) ⨯
        ((sheafToPresheaf J (Type (max u v))).obj O) ≅
      rawBinaryFactorizationTarget (J := J) 𝒪 :=
  Limits.binaryProductIso _ _

/-- Helper for Lemma 18.40.1: the underlying presheaf of the sheaf product `O × O` is identified
with the explicit raw presheaf of pairs of local sections. -/
private def binary_factorization_target_presheaf_iso :
    binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪) ≅
      rawBinaryFactorizationTarget (J := J) 𝒪 :=
  (asIso (prodComparison (sheafToPresheaf J (Type (max u v))) O O)) ≪≫
    binary_factorization_pair_presheaf_iso (J := J) (𝒪 := 𝒪)

/-- Helper for Lemma 18.40.1: the pair-model comparison reads the first coordinate by the first
product projection. -/
private theorem binary_factorization_pair_presheaf_iso_hom_fst :
    (binary_factorization_pair_presheaf_iso (J := J) (𝒪 := 𝒪)).hom ≫
        rawBinaryFactorizationTargetFst (J := J) (𝒪 := 𝒪) =
      prod.fst := by
  -- Proof comment: the comparison is objectwise the identity on pairs, so the first coordinate is
  -- read literally.
  simpa [binary_factorization_pair_presheaf_iso, rawBinaryFactorizationTargetFst] using
    (Limits.binaryProductIso_hom_comp_fst
      ((sheafToPresheaf J (Type (max u v))).obj O)
      ((sheafToPresheaf J (Type (max u v))).obj O))

/-- Helper for Lemma 18.40.1: the pair-model comparison reads the second coordinate by the second
product projection. -/
private theorem binary_factorization_pair_presheaf_iso_hom_snd :
    (binary_factorization_pair_presheaf_iso (J := J) (𝒪 := 𝒪)).hom ≫
        rawBinaryFactorizationTargetSnd (J := J) (𝒪 := 𝒪) =
      prod.snd := by
  -- Proof comment: the second-coordinate formula is the same objectwise identity calculation.
  simpa [binary_factorization_pair_presheaf_iso, rawBinaryFactorizationTargetSnd] using
    (Limits.binaryProductIso_hom_comp_snd
      ((sheafToPresheaf J (Type (max u v))).obj O)
      ((sheafToPresheaf J (Type (max u v))).obj O))

/-- Helper for Lemma 18.40.1: after the sheaf-product comparison, the first raw coordinate is the
underlying first projection of `O × O`. -/
private theorem binary_factorization_target_presheaf_iso_hom_fst :
    (binary_factorization_target_presheaf_iso (J := J) (𝒪 := 𝒪)).hom ≫
        rawBinaryFactorizationTargetFst (J := J) (𝒪 := 𝒪) =
      (sheafToPresheaf J (Type (max u v))).map (prod.fst : O ⨯ O ⟶ O) := by
  -- Proof comment: first pass through the product comparison, then read the first coordinate via
  -- the explicit pair-model identification.
  rw [binary_factorization_target_presheaf_iso, Iso.trans_hom, Category.assoc]
  rw [binary_factorization_pair_presheaf_iso_hom_fst (J := J) (𝒪 := 𝒪)]
  simpa using prodComparison_fst (sheafToPresheaf J (Type (max u v))) O O

/-- Helper for Lemma 18.40.1: after the sheaf-product comparison, the second raw coordinate is the
underlying second projection of `O × O`. -/
private theorem binary_factorization_target_presheaf_iso_hom_snd :
    (binary_factorization_target_presheaf_iso (J := J) (𝒪 := 𝒪)).hom ≫
        rawBinaryFactorizationTargetSnd (J := J) (𝒪 := 𝒪) =
      (sheafToPresheaf J (Type (max u v))).map (prod.snd : O ⨯ O ⟶ O) := by
  -- Proof comment: the second coordinate follows from the same product comparison together with
  -- the explicit second-coordinate formula.
  rw [binary_factorization_target_presheaf_iso, Iso.trans_hom, Category.assoc]
  rw [binary_factorization_pair_presheaf_iso_hom_snd (J := J) (𝒪 := 𝒪)]
  simpa using prodComparison_snd (sheafToPresheaf J (Type (max u v))) O O

/-- Helper for Lemma 18.40.1: the left tagged branch of the explicit `Sum`-valued raw source. -/
private def raw_binary_factorization_source_inl :
    rawBinaryFactorizationTarget (J := J) 𝒪 ⟶ rawBinaryFactorizationSource (J := J) 𝒪 where
  app U x := Sum.inl x
  naturality := by
    intro U V f
    funext x
    rfl

/-- Helper for Lemma 18.40.1: the right tagged branch of the explicit `Sum`-valued raw source. -/
private def raw_binary_factorization_source_inr :
    rawBinaryFactorizationTarget (J := J) 𝒪 ⟶ rawBinaryFactorizationSource (J := J) 𝒪 where
  app U x := Sum.inr x
  naturality := by
    intro U V f
    funext x
    rfl

/-- Helper for Lemma 18.40.1: the categorical coproduct of two raw target presheaves is the
explicit `Sum`-presheaf source used in the sectionwise factorization formulas. -/
private def raw_binary_factorization_coprod_iso :
    (rawBinaryFactorizationTarget (J := J) 𝒪) ⨿ (rawBinaryFactorizationTarget (J := J) 𝒪) ≅
      rawBinaryFactorizationSource (J := J) 𝒪 :=
  Limits.binaryCoproductIso _ _

/-- Helper for Lemma 18.40.1: transporting the canonical coproduct source along the target
identification gives the explicit raw `Sum`-presheaf source. -/
private def binary_factorization_source_presheaf_iso :
    let P := binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)
    (P ⨿ P) ≅ rawBinaryFactorizationSource (J := J) 𝒪 :=
  let α := binary_factorization_target_presheaf_iso (J := J) (𝒪 := 𝒪)
  (asIso (coprod.map α.hom α.hom)) ≪≫
    raw_binary_factorization_coprod_iso (J := J) (𝒪 := 𝒪)

/-- Helper for Lemma 18.40.1: the explicit coproduct-model comparison sends the left coprojection
to the left tagged branch. -/
private theorem raw_binary_factorization_coprod_iso_hom_inl :
    (coprod.inl :
        rawBinaryFactorizationTarget (J := J) 𝒪 ⟶
          (rawBinaryFactorizationTarget (J := J) 𝒪) ⨿
            (rawBinaryFactorizationTarget (J := J) 𝒪)) ≫
      (raw_binary_factorization_coprod_iso (J := J) (𝒪 := 𝒪)).hom =
        raw_binary_factorization_source_inl (J := J) (𝒪 := 𝒪) := by
  -- Proof comment: the explicit coproduct comparison is objectwise the identity on `Sum.inl`.
  simpa [raw_binary_factorization_coprod_iso, raw_binary_factorization_source_inl] using
    (Limits.binaryCoproductIso_inl_comp_hom
      (rawBinaryFactorizationTarget (J := J) 𝒪)
      (rawBinaryFactorizationTarget (J := J) 𝒪))

/-- Helper for Lemma 18.40.1: the explicit coproduct-model comparison sends the right coprojection
to the right tagged branch. -/
private theorem raw_binary_factorization_coprod_iso_hom_inr :
    (coprod.inr :
        rawBinaryFactorizationTarget (J := J) 𝒪 ⟶
          (rawBinaryFactorizationTarget (J := J) 𝒪) ⨿
            (rawBinaryFactorizationTarget (J := J) 𝒪)) ≫
      (raw_binary_factorization_coprod_iso (J := J) (𝒪 := 𝒪)).hom =
        raw_binary_factorization_source_inr (J := J) (𝒪 := 𝒪) := by
  -- Proof comment: the right branch is the same identity-on-tags computation with `Sum.inr`.
  simpa [raw_binary_factorization_coprod_iso, raw_binary_factorization_source_inr] using
    (Limits.binaryCoproductIso_inr_comp_hom
      (rawBinaryFactorizationTarget (J := J) 𝒪)
      (rawBinaryFactorizationTarget (J := J) 𝒪))

/-- Helper for Lemma 18.40.1: maps into the explicit raw pair presheaf are determined by their two
coordinate projections. -/
private theorem rawBinaryFactorizationTarget_hom_ext
    {P : Cᵒᵖ ⥤ Type (max u v)}
    {f g : P ⟶ rawBinaryFactorizationTarget (J := J) 𝒪}
    (hfst :
      f ≫ rawBinaryFactorizationTargetFst (J := J) (𝒪 := 𝒪) =
        g ≫ rawBinaryFactorizationTargetFst (J := J) (𝒪 := 𝒪))
    (hsnd :
      f ≫ rawBinaryFactorizationTargetSnd (J := J) (𝒪 := 𝒪) =
        g ≫ rawBinaryFactorizationTargetSnd (J := J) (𝒪 := 𝒪)) :
    f = g := by
  -- Proof comment: evaluate at each object and compare the resulting ordered pairs coordinatewise.
  ext U x
  apply Prod.ext
  · exact congrFun (congrArg (fun k ↦ k.app U) hfst) x
  · exact congrFun (congrArg (fun k ↦ k.app U) hsnd) x

/-- Helper for Lemma 18.40.1: after transporting the categorical source and target to the explicit
raw models, the underlying presheaf binary factorization map becomes the raw `Sum`-presheaf map. -/
private theorem binaryFactorizationSourceConjugation :
    let P := binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)
    let α := binary_factorization_target_presheaf_iso (J := J) (𝒪 := 𝒪)
    let β := binary_factorization_source_presheaf_iso (J := J) (𝒪 := 𝒪)
    let gPair : (P ⨿ P) ⟶ P :=
      coprod.desc
        ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationLeft 𝒪))
        ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationRight 𝒪))
    gPair ≫ α.hom = β.hom ≫ rawBinaryFactorizationMap (J := J) 𝒪 := by
  -- Route correction: after making the pair and coproduct comparisons objectwise explicit, the
  -- conjugation can be checked branchwise on raw sections instead of by transport-heavy rewrites.
  apply rawBinaryFactorizationTarget_hom_ext
  · apply coprod.hom_ext
    · -- Proof comment: on the left branch both maps keep the first coordinate `f`.
      ext U x
      cases x
      rfl
    · -- Proof comment: on the right branch the first coordinate is also preserved verbatim.
      ext U x
      cases x
      rfl
  · apply coprod.hom_ext
    · -- Proof comment: on the left branch both maps compute the second coordinate as `a * f`.
      ext U x
      cases x
      rfl
    · -- Proof comment: on the right branch both maps compute the second coordinate as
      -- `b * (1 - f)`.
      ext U x
      cases x
      rfl

/-- Helper for Lemma 18.40.1: sheafifying each leg of the binary source diagram produces the
diagram of the two sheafified target presheaves. -/
private def binaryFactorizationSheafifiedPairDiagramIso :
    (pair
        (binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪))
        (binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)) ⋙
        presheafToSheaf J (Type (max u v))) ≅
      pair
        (binaryFactorizationSheafifiedTarget (J := J) (𝒪 := 𝒪))
        (binaryFactorizationSheafifiedTarget (J := J) (𝒪 := 𝒪)) :=
  NatIso.ofComponents
    (fun j ↦ by
      cases j using Discrete.recOn with
      | mk j =>
          cases j <;> exact Iso.refl _)
    (by
      intro i j f
      cases i using Discrete.recOn with
      | mk i =>
          cases j using Discrete.recOn with
          | mk j =>
              cases i with
              | left =>
                  cases j with
                  | left =>
                      simp
                  | right =>
                      rcases f with ⟨⟨h⟩⟩
                      cases h
              | right =>
                  cases j with
                  | left =>
                      rcases f with ⟨⟨h⟩⟩
                      cases h
                  | right =>
                      simp)

/-- Helper for Lemma 18.40.1: sheafifying the coproduct of the underlying target presheaf
recovers the actual sheaf coproduct source of `binaryFactorizationMap`. -/
private def binaryFactorizationSheafifiedSourceIso :
    (presheafToSheaf J (Type (max u v))).obj
        ((binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)) ⨿
          (binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪))) ≅
      (O ⨯ O) ⨿ (O ⨯ O) :=
  (preservesColimitIso
      (presheafToSheaf J (Type (max u v)))
      (pair
        (binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪))
        (binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)))) ≪≫
      (HasColimit.isoOfNatIso
      (binaryFactorizationSheafifiedPairDiagramIso (J := J) (𝒪 := 𝒪))) ≪≫
    binary_factorization_source_iso (J := J) (𝒪 := 𝒪)

/-- Helper for Lemma 18.40.1: transporting a sheaf morphism across the source and target
sheafification isomorphisms recovers the map induced by the underlying presheaf morphism. -/
private theorem sheafificationIso_inv_comp_hom_eq_map
    {𝒢₁ 𝒢₂ : Sheaf J (Type (max u v))}
    (f : 𝒢₁ ⟶ 𝒢₂) :
    (sheafificationIso 𝒢₁).inv ≫ f ≫ (sheafificationIso 𝒢₂).hom =
      (presheafToSheaf J (Type (max u v))).map f.hom := by
  -- Proof comment: rewrite the naturality square for `sheafificationNatIso` after precomposing
  -- with the inverse source comparison.
  have hpre :
      (sheafificationIso 𝒢₁).inv ≫ (f ≫ (sheafificationIso 𝒢₂).hom) =
        (sheafificationIso 𝒢₁).inv ≫
          ((sheafificationIso 𝒢₁).hom ≫
            (presheafToSheaf J (Type (max u v))).map f.hom) := by
    exact
      congrArg
        (fun k ↦ (sheafificationIso 𝒢₁).inv ≫ k)
        ((sheafificationNatIso J (Type (max u v))).hom.naturality f)
  -- Proof comment: cancel the source sheafification isomorphism to isolate the sheafified map.
  simpa [Category.assoc] using
    hpre.trans
      (Iso.inv_hom_id_assoc
        (sheafificationIso 𝒢₁)
        ((presheafToSheaf J (Type (max u v))).map f.hom))

/-- Helper for Lemma 18.40.1: the sheafified source comparison sends the left coprojection of the
sheafified presheaf coproduct to the left coprojection of the actual sheaf source, after
identifying each summand by `sheafificationIso`. -/
private theorem binaryFactorizationSheafifiedSourceIso_hom_inl :
    let G := presheafToSheaf J (Type (max u v))
    let P := binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)
    G.map (coprod.inl : P ⟶ P ⨿ P) ≫
      (binaryFactorizationSheafifiedSourceIso (J := J) (𝒪 := 𝒪)).hom =
        (sheafificationIso (O ⨯ O)).inv ≫ coprod.inl := by
  -- Proof comment: rewrite the composite source comparison one colimit factor at a time until the
  -- left coprojection is read through the explicit source-side sheafification comparison.
  rw [binaryFactorizationSheafifiedSourceIso, Iso.trans_hom, Iso.trans_hom, Category.assoc]
  rw [ι_preservesColimitIso_hom
    (G := presheafToSheaf J (Type (max u v)))
    (F := pair
      (binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪))
      (binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)))
    (j := Discrete.mk WalkingPair.left)]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc
    (w := binaryFactorizationSheafifiedPairDiagramIso (J := J) (𝒪 := 𝒪))
    (j := Discrete.mk WalkingPair.left)]
  unfold binary_factorization_source_iso
  rw [HasColimit.isoOfNatIso_ι_hom_assoc]
  simp

/-- Helper for Lemma 18.40.1: the sheafified source comparison sends the right coprojection of the
sheafified presheaf coproduct to the right coprojection of the actual sheaf source, after
identifying each summand by `sheafificationIso`. -/
private theorem binaryFactorizationSheafifiedSourceIso_hom_inr :
    let G := presheafToSheaf J (Type (max u v))
    let P := binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)
    G.map (coprod.inr : P ⟶ P ⨿ P) ≫
      (binaryFactorizationSheafifiedSourceIso (J := J) (𝒪 := 𝒪)).hom =
        (sheafificationIso (O ⨯ O)).inv ≫ coprod.inr := by
  -- Proof comment: the right coprojection is computed by the same colimit-leg comparison, now at
  -- the right branch of the walking pair.
  rw [binaryFactorizationSheafifiedSourceIso, Iso.trans_hom, Iso.trans_hom, Category.assoc]
  rw [ι_preservesColimitIso_hom
    (G := presheafToSheaf J (Type (max u v)))
    (F := pair
      (binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪))
      (binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)))
    (j := Discrete.mk WalkingPair.right)]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc
    (w := binaryFactorizationSheafifiedPairDiagramIso (J := J) (𝒪 := 𝒪))
    (j := Discrete.mk WalkingPair.right)]
  unfold binary_factorization_source_iso
  rw [HasColimit.isoOfNatIso_ι_hom_assoc]
  simp

/-- Helper for Lemma 18.40.1: once the source and target presheaf identifications are in place,
local surjectivity of the binary coproduct map is equivalent to local surjectivity of the raw
`Sum`-presheaf map. -/
private theorem pair_raw_binary_factorization_isLocallySurjective_iff :
    let P := binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)
    let gPair : (P ⨿ P) ⟶ P :=
      coprod.desc
        ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationLeft 𝒪))
        ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationRight 𝒪))
    Presheaf.IsLocallySurjective J gPair ↔
      Presheaf.IsLocallySurjective J (rawBinaryFactorizationMap (J := J) 𝒪) := by
  -- Route correction: the object transport is now isolated in
  -- `binary_factorization_source_presheaf_iso` and
  -- `binary_factorization_target_presheaf_iso`; the only remaining work is the conjugation
  -- identity comparing `gPair` with `rawBinaryFactorizationMap`.
  let α := binary_factorization_target_presheaf_iso (J := J) (𝒪 := 𝒪)
  let β := binary_factorization_source_presheaf_iso (J := J) (𝒪 := 𝒪)
  let gPair :
      ((binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)) ⨿
        (binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪))) ⟶
        binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪) :=
    coprod.desc
      ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationLeft 𝒪))
      ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationRight 𝒪))
  have hconj :
      gPair ≫ α.hom = β.hom ≫ rawBinaryFactorizationMap (J := J) 𝒪 := by
    simpa [α, β, gPair] using binaryFactorizationSourceConjugation (J := J) (𝒪 := 𝒪)
  let _ : Presheaf.IsLocallyInjective J α.hom := by infer_instance
  let _ : Presheaf.IsLocallySurjective J α.hom := by infer_instance
  let _ : Presheaf.IsLocallyInjective J β.hom := by infer_instance
  let _ : Presheaf.IsLocallySurjective J β.hom := by infer_instance
  constructor
  · intro h
    have hcomp : Presheaf.IsLocallySurjective J (gPair ≫ α.hom) :=
      (Presheaf.isLocallySurjective_comp_iff J gPair α.hom).2 h
    rw [hconj] at hcomp
    exact (Presheaf.comp_isLocallySurjective_iff
      J β.hom (rawBinaryFactorizationMap (J := J) 𝒪)).1 hcomp
  · intro h
    have hcomp : Presheaf.IsLocallySurjective J (β.hom ≫ rawBinaryFactorizationMap (J := J) 𝒪) :=
      (Presheaf.comp_isLocallySurjective_iff
        J β.hom (rawBinaryFactorizationMap (J := J) 𝒪)).2 h
    rw [← hconj] at hcomp
    exact (Presheaf.isLocallySurjective_comp_iff J gPair α.hom).1 hcomp

/-- Helper for Lemma 18.40.1: after transporting the sheafified coproduct source and target back
to the raw presheaf models, the sheafified coproduct map agrees with `binaryFactorizationMap`. -/
private theorem binaryFactorizationSheafifiedConjugation :
    let G := presheafToSheaf J (Type (max u v))
    let P := binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)
    let gPair : (P ⨿ P) ⟶ P :=
      coprod.desc
        ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationLeft 𝒪))
        ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationRight 𝒪))
    (G.map gPair) ≫ (sheafificationIso (O ⨯ O)).inv =
      (binaryFactorizationSheafifiedSourceIso (J := J) (𝒪 := 𝒪)).hom ≫
        binaryFactorizationMap 𝒪 := by
  -- Route correction: instead of normalizing the whole transport composite at once, first move to
  -- the actual coproduct source via the inverse comparison and then check the left and right
  -- branches separately.
  let G := presheafToSheaf J (Type (max u v))
  let P := binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)
  let gPair : (P ⨿ P) ⟶ P :=
    coprod.desc
      ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationLeft 𝒪))
      ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationRight 𝒪))
  let α := sheafificationIso (O ⨯ O)
  let β := binaryFactorizationSheafifiedSourceIso (J := J) (𝒪 := 𝒪)
  have hinlInv :
      (coprod.inl : (O ⨯ O) ⟶ (O ⨯ O) ⨿ (O ⨯ O)) ≫ β.inv =
        α.hom ≫ G.map (coprod.inl : P ⟶ P ⨿ P) := by
    apply (cancel_mono β.hom).1
    -- Proof comment: postcompose with `β.hom` and use the already-computed left-leg formula.
    simp [β, α, G, P, Category.assoc, binaryFactorizationSheafifiedSourceIso_hom_inl]
  have hinrInv :
      (coprod.inr : (O ⨯ O) ⟶ (O ⨯ O) ⨿ (O ⨯ O)) ≫ β.inv =
        α.hom ≫ G.map (coprod.inr : P ⟶ P ⨿ P) := by
    apply (cancel_mono β.hom).1
    -- Proof comment: the right-leg inverse formula is the same cancellation argument.
    simp [β, α, G, P, Category.assoc, binaryFactorizationSheafifiedSourceIso_hom_inr]
  have hleftMap :
      α.hom ≫
          G.map ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationLeft 𝒪)) ≫ α.inv =
        binaryFactorizationLeft 𝒪 := by
    apply (cancel_mono α.hom).1
    -- Proof comment: transport the sheafified underlying-presheaf map back across
    -- `sheafificationIso`.
    simpa [α, G, Category.assoc] using
      (congrArg
        (fun k ↦ α.hom ≫ k)
        (sheafificationIso_inv_comp_hom_eq_map (J := J) (f := binaryFactorizationLeft 𝒪))).symm
  have hrightMap :
      α.hom ≫
          G.map ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationRight 𝒪)) ≫
            α.inv =
        binaryFactorizationRight 𝒪 := by
    apply (cancel_mono α.hom).1
    -- Proof comment: the right branch uses the same sheafification transport identity.
    simpa [α, G, Category.assoc] using
      (congrArg
        (fun k ↦ α.hom ≫ k)
        (sheafificationIso_inv_comp_hom_eq_map (J := J) (f := binaryFactorizationRight 𝒪))).symm
  have hcore :
      β.inv ≫ (G.map gPair) ≫ α.inv = binaryFactorizationMap 𝒪 := by
    apply coprod.hom_ext
    · -- Proof comment: after rewriting the inverse source comparison on the left branch, the
      -- transported map is exactly `binaryFactorizationLeft`.
      calc
        coprod.inl ≫ β.inv ≫ G.map gPair ≫ α.inv
            = α.hom ≫ G.map (coprod.inl : P ⟶ P ⨿ P) ≫ G.map gPair ≫ α.inv := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ k ≫ G.map gPair ≫ α.inv) hinlInv
        _ = α.hom ≫ G.map ((coprod.inl : P ⟶ P ⨿ P) ≫ gPair) ≫ α.inv := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ α.hom ≫ k ≫ α.inv)
                  (Functor.map_comp G (coprod.inl : P ⟶ P ⨿ P) gPair).symm
        _ = α.hom ≫
              G.map ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationLeft 𝒪)) ≫
                α.inv := by
              simpa [gPair, Category.assoc] using
                congrArg (fun k ↦ α.hom ≫ G.map k ≫ α.inv)
                  (coprod.inl_desc
                    ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationLeft 𝒪))
                    ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationRight 𝒪)))
        _ = binaryFactorizationLeft 𝒪 := hleftMap
        _ = coprod.inl ≫ binaryFactorizationMap 𝒪 := by
              simpa [binaryFactorizationMap] using
                (coprod.inl_desc (binaryFactorizationLeft 𝒪) (binaryFactorizationRight 𝒪)).symm
    · -- Proof comment: the right branch reduces in the same way to
      -- `binaryFactorizationRight`.
      calc
        coprod.inr ≫ β.inv ≫ G.map gPair ≫ α.inv
            = α.hom ≫ G.map (coprod.inr : P ⟶ P ⨿ P) ≫ G.map gPair ≫ α.inv := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ k ≫ G.map gPair ≫ α.inv) hinrInv
        _ = α.hom ≫ G.map ((coprod.inr : P ⟶ P ⨿ P) ≫ gPair) ≫ α.inv := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ α.hom ≫ k ≫ α.inv)
                  (Functor.map_comp G (coprod.inr : P ⟶ P ⨿ P) gPair).symm
        _ = α.hom ≫
              G.map ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationRight 𝒪)) ≫
                α.inv := by
              simpa [gPair, Category.assoc] using
                congrArg (fun k ↦ α.hom ≫ G.map k ≫ α.inv)
                  (coprod.inr_desc
                    ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationLeft 𝒪))
                    ((sheafToPresheaf J (Type (max u v))).map (binaryFactorizationRight 𝒪)))
        _ = binaryFactorizationRight 𝒪 := hrightMap
        _ = coprod.inr ≫ binaryFactorizationMap 𝒪 := by
              simpa [binaryFactorizationMap] using
                (coprod.inr_desc (binaryFactorizationLeft 𝒪) (binaryFactorizationRight 𝒪)).symm
  -- Proof comment: now transport the branchwise equality back across the source comparison.
  calc
    (G.map gPair) ≫ α.inv = β.hom ≫ (β.inv ≫ (G.map gPair) ≫ α.inv) := by
      calc
        (G.map gPair) ≫ α.inv = (𝟙 _) ≫ ((G.map gPair) ≫ α.inv) := by simp
        _ = (β.hom ≫ β.inv) ≫ ((G.map gPair) ≫ α.inv) := by rw [Iso.hom_inv_id]
        _ = β.hom ≫ (β.inv ≫ (G.map gPair) ≫ α.inv) := by simp [Category.assoc]
    _ = β.hom ≫ binaryFactorizationMap 𝒪 := by rw [hcore]

/-- Helper for Lemma 18.40.1: the underlying presheaf of `binaryFactorizationMap` is locally
surjective exactly when the explicit presheaf coproduct-desc model is locally surjective. -/
private theorem underlying_binaryFactorizationMap_isLocallySurjective_iff :
    let F := sheafToPresheaf J (Type (max u v))
    let G := presheafToSheaf J (Type (max u v))
    let P := binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)
    let gPair : (P ⨿ P) ⟶ P :=
      coprod.desc
        (F.map (binaryFactorizationLeft 𝒪))
        (F.map (binaryFactorizationRight 𝒪))
    Presheaf.IsLocallySurjective J (F.map (binaryFactorizationMap 𝒪)) ↔
      Presheaf.IsLocallySurjective J gPair := by
  let F := sheafToPresheaf J (Type (max u v))
  let G := presheafToSheaf J (Type (max u v))
  let P := binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)
  let gPair : (P ⨿ P) ⟶ P :=
    coprod.desc
      (F.map (binaryFactorizationLeft 𝒪))
      (F.map (binaryFactorizationRight 𝒪))
  have hconj :
      (G.map gPair) ≫ (sheafificationIso (O ⨯ O)).inv =
        (binaryFactorizationSheafifiedSourceIso (J := J) (𝒪 := 𝒪)).hom ≫
          binaryFactorizationMap 𝒪 := by
    simpa [F, G, P, gPair] using
      binaryFactorizationSheafifiedConjugation (J := J) (𝒪 := 𝒪)
  constructor
  · intro hpres
    have hmap : Sheaf.IsLocallySurjective (binaryFactorizationMap 𝒪) := by
      rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
      exact hpres
    have hcomp :
        Sheaf.IsLocallySurjective
          ((binaryFactorizationSheafifiedSourceIso (J := J) (𝒪 := 𝒪)).hom ≫
            binaryFactorizationMap 𝒪) := by
      let _ : Sheaf.IsLocallySurjective (binaryFactorizationMap 𝒪) := hmap
      infer_instance
    rw [← hconj] at hcomp
    have hmap' : Sheaf.IsLocallySurjective (G.map gPair) := by
      rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
      have hcomp'' :
          Presheaf.IsLocallySurjective J
            (F.map ((G.map gPair) ≫ (sheafificationIso (O ⨯ O)).inv)) := by
        exact hcomp
      have hcomp' :
          Presheaf.IsLocallySurjective J
            (F.map (G.map gPair) ≫ F.map ((sheafificationIso (O ⨯ O)).inv)) := by
        rw [Functor.map_comp] at hcomp''
        exact hcomp''
      let _ :
          Presheaf.IsLocallySurjective J (F.map ((sheafificationIso (O ⨯ O)).inv)) := by
        infer_instance
      let _ :
          Presheaf.IsLocallyInjective J (F.map ((sheafificationIso (O ⨯ O)).inv)) := by
        infer_instance
      exact
        (Presheaf.isLocallySurjective_comp_iff J
          (F.map (G.map gPair))
          (F.map ((sheafificationIso (O ⨯ O)).inv))).1 hcomp'
    rw [Presheaf.isLocallySurjective_presheafToSheaf_map_iff] at hmap'
    exact hmap'
  · intro hpres
    have hmap : Sheaf.IsLocallySurjective (G.map gPair) := by
      rw [Presheaf.isLocallySurjective_presheafToSheaf_map_iff]
      exact hpres
    have hcomp :
        Sheaf.IsLocallySurjective ((G.map gPair) ≫ (sheafificationIso (O ⨯ O)).inv) := by
      let _ : Sheaf.IsLocallySurjective (G.map gPair) := hmap
      infer_instance
    rw [hconj] at hcomp
    have hmap' : Sheaf.IsLocallySurjective (binaryFactorizationMap 𝒪) := by
      rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
      have hcomp'' :
          Presheaf.IsLocallySurjective J
            (F.map
              ((binaryFactorizationSheafifiedSourceIso (J := J) (𝒪 := 𝒪)).hom ≫
                binaryFactorizationMap 𝒪)) := by
        exact hcomp
      have hcomp' :
          Presheaf.IsLocallySurjective J
            (F.map ((binaryFactorizationSheafifiedSourceIso (J := J) (𝒪 := 𝒪)).hom) ≫
              F.map (binaryFactorizationMap 𝒪)) := by
        rw [Functor.map_comp] at hcomp''
        exact hcomp''
      let _ :
          Presheaf.IsLocallySurjective J
            (F.map ((binaryFactorizationSheafifiedSourceIso (J := J) (𝒪 := 𝒪)).hom)) := by
        infer_instance
      let _ :
          Presheaf.IsLocallyInjective J
            (F.map ((binaryFactorizationSheafifiedSourceIso (J := J) (𝒪 := 𝒪)).hom)) := by
        infer_instance
      exact
        (Presheaf.comp_isLocallySurjective_iff J
          (F.map ((binaryFactorizationSheafifiedSourceIso (J := J) (𝒪 := 𝒪)).hom))
          (F.map (binaryFactorizationMap 𝒪))).1 hcomp'
    rw [Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
    exact hmap'

/-- Unfolding `Sheaf.IsLocallySurjective (binaryFactorizationMap 𝒪)` gives the sectionwise local
factorization formula from Stacks `18.40.1 (3)`. This remains companion API, while the main owner
clause is the local surjectivity of the named sheaf morphism. -/
theorem isLocallySurjective_binaryFactorizationMap_iff :
    Sheaf.IsLocallySurjective (binaryFactorizationMap 𝒪) ↔
      ∀ (U : C) (f c : 𝒪.obj.obj (op U)),
        ∃ S : J.Cover U, ∀ I : S.Arrow,
          (∃ a : 𝒪.obj.obj (op I.Y),
              (𝒪.obj.map I.f.op).hom c = a * (𝒪.obj.map I.f.op).hom f) ∨
            ∃ b : 𝒪.obj.obj (op I.Y),
              (𝒪.obj.map I.f.op).hom c = b * (1 - (𝒪.obj.map I.f.op).hom f) := by
  -- Route correction: the presheaf transport is now settled in
  -- `binaryFactorizationSourceConjugation` and
  -- `pair_raw_binary_factorization_isLocallySurjective_iff`.
  let F := sheafToPresheaf J (Type (max u v))
  let P := binaryFactorizationUnderlyingPresheaf (J := J) (𝒪 := 𝒪)
  let gPair : (P ⨿ P) ⟶ P :=
    coprod.desc
      (F.map (binaryFactorizationLeft 𝒪))
      (F.map (binaryFactorizationRight 𝒪))
  -- Proof comment: first move from the named sheaf morphism to the explicit presheaf coproduct
  -- model, then apply the already-established sectionwise raw-factorization criterion.
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  have hunderlying :
      Presheaf.IsLocallySurjective J (F.map (binaryFactorizationMap 𝒪)) ↔
        Presheaf.IsLocallySurjective J gPair := by
    simpa [F, P, gPair] using
      underlying_binaryFactorizationMap_isLocallySurjective_iff (J := J) (𝒪 := 𝒪)
  have hpair :
      Presheaf.IsLocallySurjective J gPair ↔
        Presheaf.IsLocallySurjective J (rawBinaryFactorizationMap (J := J) 𝒪) := by
    simpa [P, gPair] using
      pair_raw_binary_factorization_isLocallySurjective_iff (J := J) (𝒪 := 𝒪)
  rw [hunderlying]
  rw [hpair]
  exact isLocallySurjective_rawBinaryFactorizationMap_iff (J := J) (𝒪 := 𝒪)

/-- Helper for Lemma 18.40.1: the two-generator case of the local unit-ideal criterion follows
from one Bezout identity and local unit dichotomy applied to the first summand. -/
lemma two_generator_cover_of_local_unit_dichotomy
    [HasLocalUnitDichotomy J 𝒪]
    (U : C) (x y : 𝒪.obj.obj (op U))
    (hxy : Ideal.span ({x, y} : Set (𝒪.obj.obj (op U))) = ⊤) :
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      IsUnit ((𝒪.obj.map I.f.op).hom x) ∨ IsUnit ((𝒪.obj.map I.f.op).hom y) := by
  rw [Ideal.eq_top_iff_one] at hxy
  rcases Ideal.mem_span_pair.mp hxy with ⟨a, b, hab⟩
  -- Apply the dichotomy to the first Bezout summand `a * x`.
  obtain ⟨S, hS⟩ := HasLocalUnitDichotomy.local_unit_dichotomy (J := J) (𝒪 := 𝒪) U (a * x)
  refine ⟨S, ?_⟩
  intro I
  rcases hS I with hax | hcomp
  · left
    -- If `(a * x)|` is a unit, then the factor `x|` is a unit as well.
    have hxmul :
        IsUnit
          (((𝒪.obj.map I.f.op).hom x) * ((𝒪.obj.map I.f.op).hom a)) := by
      simpa [RingHom.map_mul, mul_comm] using hax
    exact isUnit_of_mul_isUnit_left hxmul
  · right
    have hmap :
        ((𝒪.obj.map I.f.op).hom a) * ((𝒪.obj.map I.f.op).hom x) +
            ((𝒪.obj.map I.f.op).hom b) * ((𝒪.obj.map I.f.op).hom y) = 1 := by
      simpa [RingHom.map_add, RingHom.map_mul] using
        congrArg ((𝒪.obj.map I.f.op).hom) hab
    have hcomp' :
        IsUnit
          (1 - ((𝒪.obj.map I.f.op).hom a) * ((𝒪.obj.map I.f.op).hom x)) := by
      simpa [RingHom.map_mul] using hcomp
    -- Rewrite the complementary branch with the restricted Bezout identity.
    have hby :
        ((𝒪.obj.map I.f.op).hom b) * ((𝒪.obj.map I.f.op).hom y) =
          1 - ((𝒪.obj.map I.f.op).hom a) * ((𝒪.obj.map I.f.op).hom x) := by
      rw [eq_sub_iff_add_eq]
      simpa [add_comm, add_left_comm, add_assoc] using hmap
    have hymul :
        IsUnit
          (((𝒪.obj.map I.f.op).hom y) * ((𝒪.obj.map I.f.op).hom b)) := by
      rw [mul_comm, hby]
      exact hcomp'
    exact isUnit_of_mul_isUnit_left hymul

/-- Helper for Lemma 18.40.1: local unit dichotomy gives the sectionwise factorization formula
appearing in clause `(3)` by taking local inverses of `f` or of `1 - f`. -/
lemma local_factorization_of_local_unit_dichotomy
    [HasLocalUnitDichotomy J 𝒪]
    (U : C) (f c : 𝒪.obj.obj (op U)) :
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      (∃ a : 𝒪.obj.obj (op I.Y),
          (𝒪.obj.map I.f.op).hom c = a * (𝒪.obj.map I.f.op).hom f) ∨
        ∃ b : 𝒪.obj.obj (op I.Y),
          (𝒪.obj.map I.f.op).hom c = b * (1 - (𝒪.obj.map I.f.op).hom f) := by
  obtain ⟨S, hS⟩ := HasLocalUnitDichotomy.local_unit_dichotomy (J := J) (𝒪 := 𝒪) U f
  refine ⟨S, ?_⟩
  intro I
  rcases hS I with hf | hf
  · rcases hf with ⟨u, hu⟩
    -- On the `f`-unit branch, multiply by the local inverse of `f`.
    refine Or.inl ?_
    refine ⟨(𝒪.obj.map I.f.op).hom c * ↑u⁻¹, ?_⟩
    calc
      (𝒪.obj.map I.f.op).hom c =
          (𝒪.obj.map I.f.op).hom c * ((↑u⁻¹ : _) * ↑u) := by
            simp
      _ =
          ((𝒪.obj.map I.f.op).hom c * ↑u⁻¹) * ↑u := by
            simp [mul_assoc]
      _ =
          ((𝒪.obj.map I.f.op).hom c * ↑u⁻¹) * (𝒪.obj.map I.f.op).hom f := by
            simpa [hu]
  · rcases hf with ⟨u, hu⟩
    -- On the complementary branch, multiply by the local inverse of `1 - f`.
    refine Or.inr ?_
    refine ⟨(𝒪.obj.map I.f.op).hom c * ↑u⁻¹, ?_⟩
    calc
      (𝒪.obj.map I.f.op).hom c =
          (𝒪.obj.map I.f.op).hom c * ((↑u⁻¹ : _) * ↑u) := by
            simp
      _ =
          ((𝒪.obj.map I.f.op).hom c * ↑u⁻¹) * ↑u := by
            simp [mul_assoc]
      _ =
          ((𝒪.obj.map I.f.op).hom c * ↑u⁻¹) * (1 - (𝒪.obj.map I.f.op).hom f) := by
            simpa [hu]

/-- Helper for Lemma 18.40.1: a finite family of sections whose span is the unit ideal admits a
cover on which one member becomes invertible. This is the finitary induction step used in the
textbook proof of `(1) → (2)`. -/
lemma finset_generator_cover_of_local_unit_dichotomy
    [HasLocalUnitDichotomy J 𝒪] :
    ∀ n : ℕ, ∀ (U : C) (t : Finset (𝒪.obj.obj (op U))),
      t.Nonempty →
      t.card ≤ n →
      Ideal.span (↑t : Set (𝒪.obj.obj (op U))) = ⊤ →
      ∃ S : J.Cover U, ∀ I : S.Arrow,
        ∃ g ∈ t, IsUnit ((𝒪.obj.map I.f.op).hom g) := by
  classical
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih U t htne htcard hspan
  by_cases hsingleton : t.card = 1
  · rcases Finset.card_eq_one.mp hsingleton with ⟨x, rfl⟩
    -- In the singleton case, the unique generator is already a unit globally.
    have hx : IsUnit x := by
      simpa [Ideal.span_singleton_eq_top] using hspan
    let S : J.Cover U := ⟨⊤, J.top_mem U⟩
    refine ⟨S, ?_⟩
    intro I
    refine ⟨x, by simp, ?_⟩
    simpa using hx.map ((𝒪.obj.map I.f.op).hom)
  · have hcard_gt_one : 1 < t.card := by
      have hcard_pos : 0 < t.card := htne.card_pos
      omega
    obtain ⟨x, hxmem⟩ := htne
    let s := t.erase x
    have hsinsert : insert x s = t := by
      dsimp [s]
      exact Finset.insert_erase hxmem
    have hsnonempty : s.Nonempty := by
      have hspos : 0 < s.card := by
        dsimp [s]
        rw [Finset.card_erase_of_mem hxmem]
        omega
      exact Finset.card_pos.mp hspos
    have hslt : s.card < n := by
      have hslt' : s.card < t.card := by
        dsimp [s]
        rw [Finset.card_erase_of_mem hxmem]
        omega
      exact lt_of_lt_of_le hslt' htcard
    have hset : (↑t : Set (𝒪.obj.obj (op U))) = Set.insert x (↑s : Set (𝒪.obj.obj (op U))) := by
      ext y
      constructor
      · intro hy
        by_cases hxy : y = x
        · exact Or.inl hxy
        · right
          dsimp [s]
          simp [hy, hxy]
      · intro hy
        rcases hy with rfl | hy
        · exact hxmem
        · exact Finset.mem_of_mem_erase hy
    have hspan_insert :
        Ideal.span (Set.insert x (↑s : Set (𝒪.obj.obj (op U)))) = ⊤ := by
      simpa [hset] using hspan
    have hone :
        (1 : 𝒪.obj.obj (op U)) ∈ Ideal.span (Set.insert x (↑s : Set (𝒪.obj.obj (op U)))) := by
      rw [hspan_insert]
      simp
    -- Split `1` into a distinguished summand and a remainder in the span of the rest.
    rcases Ideal.mem_span_insert.mp hone with ⟨a, b, hb, hab⟩
    have hab_top : Ideal.span ({a * x, b} : Set (𝒪.obj.obj (op U))) = ⊤ := by
      rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair]
      exact ⟨1, 1, by simpa using hab.symm⟩
    obtain ⟨S, hS⟩ :=
      two_generator_cover_of_local_unit_dichotomy (J := J) (𝒪 := 𝒪) U (a * x) b hab_top
    have hInner :
        ∀ I : S.Arrow,
          ∃ T : J.Cover I.Y, ∀ K : T.Arrow,
            ∃ g ∈ t, IsUnit ((𝒪.obj.map K.f.op).hom ((𝒪.obj.map I.f.op).hom g)) := by
      intro I
      rcases hS I with hax | hbI
      · -- If the distinguished generator is already invertible, any further restriction keeps it
        -- invertible, so the top cover of `I.Y` suffices.
        have hxI : IsUnit ((𝒪.obj.map I.f.op).hom x) := by
          have hxmul :
              IsUnit
                (((𝒪.obj.map I.f.op).hom x) * ((𝒪.obj.map I.f.op).hom a)) := by
            simpa [RingHom.map_mul, mul_comm] using hax
          exact isUnit_of_mul_isUnit_left hxmul
        let T : J.Cover I.Y := ⟨⊤, J.top_mem I.Y⟩
        refine ⟨T, ?_⟩
        intro K
        refine ⟨x, ?_, ?_⟩
        · exact hxmem
        · simpa using hxI.map ((𝒪.obj.map K.f.op).hom)
      · -- If the remainder becomes invertible, recurse on the restricted remaining generators.
        let φ : 𝒪.obj.obj (op U) → 𝒪.obj.obj (op I.Y) := (𝒪.obj.map I.f.op).hom
        let t' : Finset (𝒪.obj.obj (op I.Y)) := s.image φ
        have ht'nonempty : t'.Nonempty := by
          exact hsnonempty.image φ
        have hbmem : φ b ∈ Ideal.span (↑t' : Set (𝒪.obj.obj (op I.Y))) := by
          dsimp [t', φ]
          rw [Finset.coe_image]
          have hbmap :
              (𝒪.obj.map I.f.op).hom b ∈
                Ideal.map ((𝒪.obj.map I.f.op).hom) (Ideal.span (↑s : Set (𝒪.obj.obj (op U)))) :=
            Ideal.mem_map_of_mem ((𝒪.obj.map I.f.op).hom) hb
          simpa [Ideal.map_span] using hbmap
        have ht'top : Ideal.span (↑t' : Set (𝒪.obj.obj (op I.Y))) = ⊤ := by
          exact Ideal.eq_top_of_isUnit_mem _ hbmem hbI
        have ht'lt : t'.card < n := by
          have himage : t'.card ≤ s.card := by
            dsimp [t']
            exact Finset.card_image_le
          exact lt_of_le_of_lt himage hslt
        obtain ⟨T, hT⟩ :=
          ih t'.card ht'lt I.Y t' ht'nonempty le_rfl ht'top
        refine ⟨T, ?_⟩
        intro K
        rcases hT K with ⟨g', hg't, hg'unit⟩
        rcases Finset.mem_image.mp hg't with ⟨y, hy, rfl⟩
        refine ⟨y, ?_, ?_⟩
        · exact Finset.mem_of_mem_erase hy
        · simpa using hg'unit
    choose T hT using hInner
    refine ⟨S.bind T, ?_⟩
    intro L
    rcases L.hf with ⟨Y, g, f, hf, hg, hgf⟩
    let I : S.Arrow := ⟨Y, f, hf⟩
    let K : (T I).Arrow := ⟨L.Y, g, hg⟩
    rcases hT I K with ⟨y, hyt, hyunit⟩
    refine ⟨y, hyt, ?_⟩
    -- The bind-arrow factorization rewrites the final restriction as the two-step restriction
    -- already produced on the chosen inner cover.
    have hcompmap :
        (𝒪.obj.map L.f.op).hom y =
          (𝒪.obj.map K.f.op).hom ((𝒪.obj.map I.f.op).hom y) := by
      dsimp [I, K]
      rw [← hgf]
      simp
    rw [hcompmap]
    exact hyunit

-- Proof sketch: `(1) → (2)` is the induction on the number of generators from the source text.
-- `(2) → (1)` is the singleton case applied to the finite set `{f, 1 - f}`. Clause `(3)` is the
-- owner-level local-surjectivity statement for `binaryFactorizationMap 𝒪`.
/-- Lemma 18.40.1: for a ringed site `(\mathcal C, \mathcal O)`, the local dichotomy that every
section is locally either invertible or complementary-invertible, the local unit-ideal criterion
for finitely many sections, and the local surjectivity of the binary factorization map are
equivalent. -/
@[stacks 04ES]
theorem ringed_site_local_unit_tfae
    (𝒪 : Sheaf J CommRingCat) :
    List.TFAE [
      HasLocalUnitDichotomy J 𝒪,
      ∀ (U : C) (s : Set (𝒪.obj.obj (op U)))
        (_ : s.Finite) (_ : s.Nonempty) (_ : Ideal.span s = ⊤),
          ∃ S : J.Cover U, ∀ I : S.Arrow,
            ∃ g ∈ s, IsUnit ((𝒪.obj.map I.f.op).hom g),
      Sheaf.IsLocallySurjective (binaryFactorizationMap 𝒪)
    ] := by
  tfae_have 2 → 1 := by
    intro h
    refine ⟨fun U f ↦ ?_⟩
    have hsfinite : ({f, 1 - f} : Set (𝒪.obj.obj (op U))).Finite := by
      simp
    have hsnonempty : ({f, 1 - f} : Set (𝒪.obj.obj (op U))).Nonempty := by
      exact ⟨f, by simp⟩
    have hspan : Ideal.span ({f, 1 - f} : Set (𝒪.obj.obj (op U))) = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      rw [Ideal.mem_span_pair]
      refine ⟨1, 1, ?_⟩
      ring
    obtain ⟨S, hS⟩ := h U {f, 1 - f} hsfinite hsnonempty hspan
    refine ⟨S, ?_⟩
    intro I
    rcases hS I with ⟨g, hg, hgunit⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact Or.inl hgunit
    · exact Or.inr <| by simpa [map_sub] using hgunit
  tfae_have 1 → 2 := by
    intro h U s hsfinite hsnonempty hspan
    letI : HasLocalUnitDichotomy J 𝒪 := h
    let t : Finset (𝒪.obj.obj (op U)) := hsfinite.toFinset
    have htne : t.Nonempty := by
      rcases hsnonempty with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      change x ∈ hsfinite.toFinset
      exact hsfinite.mem_toFinset.mpr hx
    have htspan : Ideal.span (↑t : Set (𝒪.obj.obj (op U))) = ⊤ := by
      simpa [t] using hspan
    -- Apply the finset induction to the chosen finite generating family.
    obtain ⟨S, hS⟩ :=
      finset_generator_cover_of_local_unit_dichotomy
        (J := J) (𝒪 := 𝒪) t.card U t htne le_rfl htspan
    refine ⟨S, ?_⟩
    intro I
    rcases hS I with ⟨g, hg, hgunit⟩
    refine ⟨g, ?_, hgunit⟩
    exact hsfinite.mem_toFinset.mp hg
  tfae_have 1 → 3 := by
    intro h
    letI : HasLocalUnitDichotomy J 𝒪 := h
    -- Route correction: clause `(3)` is proved through the sectionwise factorization bridge.
    rw [isLocallySurjective_binaryFactorizationMap_iff]
    exact local_factorization_of_local_unit_dichotomy (J := J) (𝒪 := 𝒪)
  tfae_have 3 → 1 := by
    intro h
    rw [isLocallySurjective_binaryFactorizationMap_iff] at h
    refine ⟨fun U f ↦ ?_⟩
    obtain ⟨S, hS⟩ := h U f 1
    refine ⟨S, ?_⟩
    intro I
    rcases hS I with hI | hI
    · rcases hI with ⟨a, ha⟩
      left
      have ha' : a * (𝒪.obj.map I.f.op).hom f = 1 := by
        simpa using ha.symm
      simpa using IsUnit.of_mul_eq_one_right a ha'
    · rcases hI with ⟨b, hb⟩
      right
      have hb' : b * (1 - (𝒪.obj.map I.f.op).hom f) = 1 := by
        simpa using hb.symm
      simpa using IsUnit.of_mul_eq_one_right b hb'
  tfae_finish

end CategoryTheory
