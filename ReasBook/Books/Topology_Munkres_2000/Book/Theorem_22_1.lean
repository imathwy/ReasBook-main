module

public import Topology_Munkres_2000.Book.Definition_22_2.Saturation
public import Mathlib.Topology.Maps.Strict.Basic

public section

universe u v

namespace Topology.IsQuotientMap

variable {X : Type u} {Y : Type v}

/-- Helper for Theorem 22.1: the image of an intersection with a saturated set is the
intersection of the corresponding images. -/
private lemma image_inter_of_isSaturated {p : X → Y} {A U : Set X}
    (hA_sat : Set.IsSaturated p A) :
    p '' (U ∩ A) = p '' U ∩ p '' A := by
  -- The forward inclusion is valid for arbitrary images.
  ext y
  constructor
  · rintro ⟨x, ⟨hxU, hxA⟩, rfl⟩
    exact ⟨⟨x, hxU, rfl⟩, ⟨x, hxA, rfl⟩⟩
  · rintro ⟨⟨x, hxU, rfl⟩, ⟨a, haA, hax⟩⟩
    -- Saturation moves membership in `A` from `a` to the point `x` in the same fiber.
    have hxA : x ∈ A := Set.isSaturated_iff_mem_of_eq.mp hA_sat haA hax.symm
    exact ⟨x, ⟨hxU, hxA⟩, rfl⟩

/-- Helper for Theorem 22.1: ambient preimages of subsets of the restricted range are
the subtype images of their restricted preimages. -/
private lemma preimage_subtypeImage_restrictRange {p : X → Y} {A : Set X}
    (hA_sat : Set.IsSaturated p A) (V : Set (Set.range (A.restrict p))) :
    p ⁻¹' (Subtype.val '' V) =
      Subtype.val '' (Set.rangeFactorization (A.restrict p) ⁻¹' V) := by
  -- Compare membership pointwise, using saturation only in the ambient-to-subtype direction.
  ext x
  constructor
  · rintro ⟨y, hyV, hyx⟩
    obtain ⟨a, ha⟩ := y.property
    have hxA : x ∈ A :=
      Set.isSaturated_iff_mem_of_eq.mp hA_sat a.property (hyx.symm.trans ha.symm)
    let xA : A := ⟨x, hxA⟩
    have hxy : Set.rangeFactorization (A.restrict p) xA = y := Subtype.ext hyx.symm
    have hxV : Set.rangeFactorization (A.restrict p) xA ∈ V := by
      rwa [hxy]
    exact ⟨xA, hxV, rfl⟩
  · rintro ⟨xA, hxV, rfl⟩
    exact ⟨Set.rangeFactorization (A.restrict p) xA, hxV, rfl⟩

/-- Helper for Theorem 22.1: images under the range factorization of a restriction are
ambient images pulled back to the range subtype. -/
private lemma image_rangeFactorization_restrict {p : X → Y} {A : Set X} (U : Set A) :
    Set.rangeFactorization (A.restrict p) '' U =
      Subtype.val ⁻¹' (p '' (Subtype.val '' U)) := by
  -- Both sides say that a range point has a representative in `U`.
  ext y
  constructor
  · rintro ⟨x, hxU, hxy⟩
    exact ⟨x.1, ⟨x, hxU, rfl⟩, congrArg Subtype.val hxy⟩
  · rintro ⟨z, ⟨x, hxU, hxz⟩, hzy⟩
    subst z
    have hxy : Set.rangeFactorization (A.restrict p) x = y := Subtype.ext hzy
    exact ⟨x, hxU, hxy⟩

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Helper for Theorem 22.1: an open map induces an open range factorization on every
saturated restriction. -/
private lemma isOpenMap_rangeFactorization_restrict {p : X → Y} {A : Set X}
    (hA_sat : Set.IsSaturated p A) (hp : IsOpenMap p) :
    IsOpenMap (Set.rangeFactorization (A.restrict p)) := by
  intro U hU
  -- Represent the open subtype set by an ambient open set, then normalize its image.
  obtain ⟨W, hW, hUW⟩ := hU.image_val
  rw [image_rangeFactorization_restrict, hUW,
    image_inter_of_isSaturated hA_sat, Set.preimage_inter, Set.range_restrict,
    Subtype.coe_preimage_self, Set.inter_univ]
  exact (hp W hW).preimage continuous_subtype_val

/-- Helper for Theorem 22.1: a closed map induces a closed range factorization on every
saturated restriction. -/
private lemma isClosedMap_rangeFactorization_restrict {p : X → Y} {A : Set X}
    (hA_sat : Set.IsSaturated p A) (hp : IsClosedMap p) :
    IsClosedMap (Set.rangeFactorization (A.restrict p)) := by
  intro U hU
  -- The closed case uses the same image normalization with an ambient closed representative.
  obtain ⟨W, hW, hUW⟩ := hU.image_val
  rw [image_rangeFactorization_restrict, hUW,
    image_inter_of_isSaturated hA_sat, Set.preimage_inter, Set.range_restrict,
    Subtype.coe_preimage_self, Set.inter_univ]
  exact (hp W hW).preimage continuous_subtype_val

/-- Theorem 22.1 (1): The restriction of a quotient map to an open or closed
saturated subset, corestricted to its image, is a quotient map. -/
theorem restrictImage_of_isOpen_or_isClosed {p : X → Y} (hp : IsQuotientMap p)
    {A : Set X} (hA_sat : Set.IsSaturated p A) (hA : IsOpen A ∨ IsClosed A) :
    IsStrictMap (A.restrict p) := by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  -- The restricted range factorization is continuous and canonically surjective.
  have hcont : Continuous (Set.rangeFactorization (A.restrict p)) :=
    (hp.continuous.comp continuous_subtype_val).rangeFactorization
  refine ⟨?_, Set.rangeFactorization_surjective⟩
  rcases hA with hA_open | hA_closed
  · refine IsCoinducing.of_isOpen_preimage_iff_isOpen fun V ↦ ?_
    constructor
    · intro hpre
      -- Push the restricted preimage into `X`, reflect openness through `p`, and pull back.
      have hopen_image :
          IsOpen (Subtype.val '' (Set.rangeFactorization (A.restrict p) ⁻¹' V)) :=
        hA_open.isOpenMap_subtype_val _ hpre
      have hopen_preimage : IsOpen (p ⁻¹' (Subtype.val '' V)) := by
        rwa [preimage_subtypeImage_restrictRange hA_sat]
      have hopen_range : IsOpen (Subtype.val '' V) :=
        hp.isCoinducing.isOpen_preimage.mp hopen_preimage
      have hopen_subtype :
          IsOpen ((Subtype.val : Set.range (A.restrict p) → Y) ⁻¹' (Subtype.val '' V)) :=
        hopen_range.preimage continuous_subtype_val
      rw [Set.preimage_image_eq V Subtype.val_injective] at hopen_subtype
      exact hopen_subtype
    · intro hV
      exact hV.preimage hcont
  · refine IsCoinducing.of_isClosed_preimage_iff_isClosed fun V ↦ ?_
    constructor
    · intro hpre
      -- The identical bridge reflects closedness when `A` is closed.
      have hclosed_image :
          IsClosed (Subtype.val '' (Set.rangeFactorization (A.restrict p) ⁻¹' V)) :=
        hA_closed.isClosedMap_subtype_val _ hpre
      have hclosed_preimage : IsClosed (p ⁻¹' (Subtype.val '' V)) := by
        rwa [preimage_subtypeImage_restrictRange hA_sat]
      have hclosed_range : IsClosed (Subtype.val '' V) :=
        hp.isCoinducing.isClosed_preimage.mp hclosed_preimage
      have hclosed_subtype :
          IsClosed ((Subtype.val : Set.range (A.restrict p) → Y) ⁻¹' (Subtype.val '' V)) :=
        hclosed_range.preimage continuous_subtype_val
      rw [Set.preimage_image_eq V Subtype.val_injective] at hclosed_subtype
      exact hclosed_subtype
    · intro hV
      exact hV.preimage hcont

/-- Companion for Theorem 22.1 (2): The restriction of an open or closed quotient map to a
saturated subset, corestricted to its image, is a quotient map. -/
theorem restrictImage_of_isOpenMap_or_isClosedMap {p : X → Y} (hp : IsQuotientMap p)
    {A : Set X} (hA_sat : Set.IsSaturated p A) (hp_map : IsOpenMap p ∨ IsClosedMap p) :
    IsStrictMap (A.restrict p) := by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  -- Apply the standard continuous-surjective criterion after transferring the map property.
  have hcont : Continuous (Set.rangeFactorization (A.restrict p)) :=
    (hp.continuous.comp continuous_subtype_val).rangeFactorization
  rcases hp_map with hp_open | hp_closed
  · exact (isOpenMap_rangeFactorization_restrict hA_sat hp_open).isQuotientMap
      hcont Set.rangeFactorization_surjective
  · exact (isClosedMap_rangeFactorization_restrict hA_sat hp_closed).isQuotientMap
      hcont Set.rangeFactorization_surjective

end Topology.IsQuotientMap
