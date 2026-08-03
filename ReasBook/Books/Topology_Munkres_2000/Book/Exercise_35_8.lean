module

public import Topology_Munkres_2000.Book.Exercise_35_6

public section

universe u v

namespace AbsoluteRetract

/-- Helper for Exercise 35.8: the canonical label of a point in the adjunction space. -/
private noncomputable def extensionAdjunctionCode {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (A : Set X) (f : C(A, Y)) : X ⊕ Y → X ⊕ Y :=
  Sum.elim
    (fun x ↦ @dite (X ⊕ Y) (x ∈ A) (Classical.propDecidable (x ∈ A))
      (fun hx ↦ Sum.inr (f ⟨x, hx⟩)) (fun _ ↦ Sum.inl x))
    Sum.inr

/-- Helper for Exercise 35.8: the adjunction space obtained by identifying `a` with `f a`. -/
private abbrev ExtensionAdjunctionSpace {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (A : Set X) (f : C(A, Y)) : Type u :=
  Quotient (Setoid.ker (extensionAdjunctionCode A f))

/-- Helper for Exercise 35.8: the quotient map onto the adjunction space. -/
private noncomputable def extensionAdjunctionQuotientMap {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (A : Set X) (f : C(A, Y)) :
    X ⊕ Y → ExtensionAdjunctionSpace A f :=
  Quotient.mk (Setoid.ker (extensionAdjunctionCode A f))

/-- Helper for Exercise 35.8: the canonical map from `X` into the adjunction space. -/
private noncomputable def extensionAdjunctionIncludeX {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (A : Set X) (f : C(A, Y)) :
    X → ExtensionAdjunctionSpace A f :=
  extensionAdjunctionQuotientMap A f ∘ Sum.inl

/-- Helper for Exercise 35.8: the canonical map from `Y` into the adjunction space. -/
private noncomputable def extensionAdjunctionIncludeY {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (A : Set X) (f : C(A, Y)) :
    Y → ExtensionAdjunctionSpace A f :=
  extensionAdjunctionQuotientMap A f ∘ Sum.inr

/-- Helper for Exercise 35.8: an attaching point has the same code as its image in `Y`. -/
private theorem extensionAdjunctionCode_inl_of_mem {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (A : Set X) (f : C(A, Y)) {x : X} (hx : x ∈ A) :
    extensionAdjunctionCode A f (Sum.inl x) = Sum.inr (f ⟨x, hx⟩) := by
  -- Select the attaching branch in the definition of the canonical code.
  simp [extensionAdjunctionCode, hx]

/-- Helper for Exercise 35.8: a point outside the attaching set retains its left label. -/
private theorem extensionAdjunctionCode_inl_of_not_mem {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (A : Set X) (f : C(A, Y)) {x : X} (hx : x ∉ A) :
    extensionAdjunctionCode A f (Sum.inl x) = Sum.inl x := by
  -- Select the unattached branch in the definition of the canonical code.
  simp [extensionAdjunctionCode, hx]

/-- Helper for Exercise 35.8: a point of `Y` retains its right label. -/
private theorem extensionAdjunctionCode_inr {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (A : Set X) (f : C(A, Y)) (y : Y) :
    extensionAdjunctionCode A f (Sum.inr y) = Sum.inr y := by
  -- The right summand is already in canonical form.
  rfl

/-- Helper for Exercise 35.8: the canonical quotient map has the quotient-map property. -/
private theorem extensionAdjunctionQuotientMap_isQuotientMap {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (f : C(A, Y)) :
    Topology.IsQuotientMap (extensionAdjunctionQuotientMap A f) := by
  -- Use the quotient topology supplied by `Quotient`.
  exact isQuotientMap_quotient_mk'

/-- Helper for Exercise 35.8: quotient representatives agree exactly when their codes agree. -/
private theorem extensionAdjunctionQuotientMap_eq_iff {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (f : C(A, Y))
    (w w' : X ⊕ Y) :
    extensionAdjunctionQuotientMap A f w = extensionAdjunctionQuotientMap A f w' ↔
      extensionAdjunctionCode A f w = extensionAdjunctionCode A f w' := by
  -- This is equality in a quotient by the kernel of the code.
  exact Quotient.eq

/-- Helper for Exercise 35.8: the canonical inclusion of `X` is continuous. -/
private theorem extensionAdjunctionContinuous_includeX {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (f : C(A, Y)) :
    Continuous (extensionAdjunctionIncludeX A f) := by
  -- Compose the continuous coproduct injection with the quotient map.
  exact (extensionAdjunctionQuotientMap_isQuotientMap A f).continuous.comp continuous_inl

/-- Helper for Exercise 35.8: the canonical inclusion of `Y` is continuous. -/
private theorem extensionAdjunctionContinuous_includeY {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (f : C(A, Y)) :
    Continuous (extensionAdjunctionIncludeY A f) := by
  -- Compose the continuous coproduct injection with the quotient map.
  exact (extensionAdjunctionQuotientMap_isQuotientMap A f).continuous.comp continuous_inr

/-- Helper for Exercise 35.8: attaching identifies every `a : A` with `f a`. -/
private theorem extensionAdjunctionGlue {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (A : Set X) (f : C(A, Y)) (a : A) :
    extensionAdjunctionIncludeX A f a = extensionAdjunctionIncludeY A f (f a) := by
  -- Equality of canonical codes gives equality of quotient representatives.
  apply Quotient.sound
  exact extensionAdjunctionCode_inl_of_mem A f a.property

/-- Helper for Exercise 35.8: every fiber over a right-hand canonical label is closed. -/
private theorem extensionAdjunctionRightFiber_isClosed {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T1Space X] [T1Space Y] {A : Set X} (hA : IsClosed A)
    (f : C(A, Y)) (y : Y) :
    IsClosed {w : X ⊕ Y | extensionAdjunctionCode A f w = Sum.inr y} := by
  classical
  have hLeft :
      Sum.inl ⁻¹' {w : X ⊕ Y | extensionAdjunctionCode A f w = Sum.inr y} =
        ((↑) : A → X) '' (f ⁻¹' ({y} : Set Y)) := by
    ext x
    constructor
    · intro hxCode
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hxCode
      by_cases hxA : x ∈ A
      · refine ⟨⟨x, hxA⟩, ?_, rfl⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        rw [extensionAdjunctionCode_inl_of_mem A f hxA] at hxCode
        exact Sum.inr.inj hxCode
      · rw [extensionAdjunctionCode_inl_of_not_mem A f hxA] at hxCode
        exact (Sum.inl_ne_inr hxCode).elim
    · rintro ⟨a, ha, rfl⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff] at ha ⊢
      rw [extensionAdjunctionCode_inl_of_mem A f a.property]
      exact congrArg Sum.inr ha
  have hRight :
      Sum.inr ⁻¹' {w : X ⊕ Y | extensionAdjunctionCode A f w = Sum.inr y} = {y} := by
    ext y'
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff,
      extensionAdjunctionCode_inr, Sum.inr.injEq]
  -- The two coproduct components are respectively a closed image from `A` and a singleton.
  rw [isClosed_sum_iff, hLeft, hRight]
  exact ⟨hA.isClosedMap_subtype_val _ (isClosed_singleton.preimage f.continuous),
    isClosed_singleton⟩

/-- Helper for Exercise 35.8: the fiber of an unattached left-hand label is closed. -/
private theorem extensionAdjunctionLeftFiber_isClosed {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T1Space X] [T1Space Y] (A : Set X) (f : C(A, Y))
    (x : X) (hx : x ∉ A) :
    IsClosed {w : X ⊕ Y | extensionAdjunctionCode A f w = Sum.inl x} := by
  classical
  have hLeft :
      Sum.inl ⁻¹' {w : X ⊕ Y | extensionAdjunctionCode A f w = Sum.inl x} = {x} := by
    ext x'
    constructor
    · intro hxCode
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hxCode
      by_cases hxA' : x' ∈ A
      · rw [extensionAdjunctionCode_inl_of_mem A f hxA'] at hxCode
        exact (Sum.inr_ne_inl hxCode).elim
      · rw [extensionAdjunctionCode_inl_of_not_mem A f hxA'] at hxCode
        simpa only [Set.mem_singleton_iff] using Sum.inl.inj hxCode
    · intro hx'
      simp only [Set.mem_singleton_iff] at hx'
      subst x'
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      exact extensionAdjunctionCode_inl_of_not_mem A f hx
  have hRight :
      Sum.inr ⁻¹' {w : X ⊕ Y | extensionAdjunctionCode A f w = Sum.inl x} = ∅ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq, extensionAdjunctionCode_inr,
      Set.mem_empty_iff_false, iff_false]
    exact Sum.inr_ne_inl
  -- Both coproduct components are closed: a singleton and the empty set.
  rw [isClosed_sum_iff, hLeft, hRight]
  exact ⟨isClosed_singleton, isClosed_empty⟩

/-- Helper for Exercise 35.8: every canonical-code fiber is closed. -/
private theorem extensionAdjunctionCodeFiber_isClosed {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T1Space X] [T1Space Y] {A : Set X} (hA : IsClosed A)
    (f : C(A, Y)) (w : X ⊕ Y) :
    IsClosed {w' : X ⊕ Y | extensionAdjunctionCode A f w' = extensionAdjunctionCode A f w} := by
  classical
  -- Split according to whether the representative has a right label or an unattached left label.
  cases w with
  | inl x =>
      by_cases hx : x ∈ A
      · rw [extensionAdjunctionCode_inl_of_mem A f hx]
        exact extensionAdjunctionRightFiber_isClosed hA f (f ⟨x, hx⟩)
      · rw [extensionAdjunctionCode_inl_of_not_mem A f hx]
        exact extensionAdjunctionLeftFiber_isClosed A f x hx
  | inr y =>
      rw [extensionAdjunctionCode_inr A f y]
      exact extensionAdjunctionRightFiber_isClosed hA f y

/-- Helper for Exercise 35.8: a closed attachment of two `T₁` spaces is `T₁`. -/
private theorem extensionAdjunctionT1Space {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T1Space X] [T1Space Y] {A : Set X} (hA : IsClosed A)
    (f : C(A, Y)) : T1Space (ExtensionAdjunctionSpace A f) := by
  refine ⟨?_⟩
  intro z
  -- Closedness is checked after pulling the singleton back along the quotient map.
  apply (extensionAdjunctionQuotientMap_isQuotientMap A f).isClosed_preimage.mp
  induction z using Quotient.inductionOn with
  | _ w =>
      have hPreimage :
          extensionAdjunctionQuotientMap A f ⁻¹'
              ({(⟦w⟧ : ExtensionAdjunctionSpace A f)} :
                Set (ExtensionAdjunctionSpace A f)) =
            {w' : X ⊕ Y | extensionAdjunctionCode A f w' =
              extensionAdjunctionCode A f w} := by
        ext w'
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
        exact Quotient.eq
      rw [hPreimage]
      exact extensionAdjunctionCodeFiber_isClosed hA f w

/-- Helper for Exercise 35.8: the canonical copy of `Y` is closedly embedded. -/
private theorem extensionAdjunctionIncludeY_isClosedEmbedding {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y] {A : Set X} (hA : IsClosed A)
    (f : C(A, Y)) : Topology.IsClosedEmbedding (extensionAdjunctionIncludeY A f) := by
  classical
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact extensionAdjunctionContinuous_includeY A f
  · intro y y' hyy'
    have hCode := (extensionAdjunctionQuotientMap_eq_iff A f (Sum.inr y) (Sum.inr y')).mp hyy'
    rw [extensionAdjunctionCode_inr A f y, extensionAdjunctionCode_inr A f y'] at hCode
    exact Sum.inr.inj hCode
  · intro C hC
    -- Pull the image back to the coproduct, where its two closed components are explicit.
    apply (extensionAdjunctionQuotientMap_isQuotientMap A f).isClosed_preimage.mp
    have hLeft :
        Sum.inl ⁻¹' (extensionAdjunctionQuotientMap A f ⁻¹'
          (extensionAdjunctionIncludeY A f '' C)) =
            ((↑) : A → X) '' (f ⁻¹' C) := by
      ext x
      constructor
      · rintro ⟨y, hyC, hxy⟩
        have hCode := (extensionAdjunctionQuotientMap_eq_iff A f
          (Sum.inl x) (Sum.inr y)).mp hxy.symm
        by_cases hxA : x ∈ A
        · refine ⟨⟨x, hxA⟩, ?_, rfl⟩
          simp only [Set.mem_preimage]
          rw [extensionAdjunctionCode_inl_of_mem A f hxA,
            extensionAdjunctionCode_inr A f y] at hCode
          rwa [Sum.inr.inj hCode]
        · rw [extensionAdjunctionCode_inl_of_not_mem A f hxA,
            extensionAdjunctionCode_inr A f y] at hCode
          exact (Sum.inl_ne_inr hCode).elim
      · rintro ⟨a, ha, rfl⟩
        refine ⟨f a, ha, ?_⟩
        exact (extensionAdjunctionGlue A f a).symm
    have hRight :
        Sum.inr ⁻¹' (extensionAdjunctionQuotientMap A f ⁻¹'
          (extensionAdjunctionIncludeY A f '' C)) = C := by
      ext y
      constructor
      · rintro ⟨y', hy'C, hyy'⟩
        have hCode := (extensionAdjunctionQuotientMap_eq_iff A f
          (Sum.inr y) (Sum.inr y')).mp hyy'.symm
        rw [extensionAdjunctionCode_inr A f y,
          extensionAdjunctionCode_inr A f y'] at hCode
        rwa [Sum.inr.inj hCode]
      · intro hyC
        exact ⟨y, hyC, rfl⟩
    rw [isClosed_sum_iff, hLeft, hRight]
    exact ⟨hA.isClosedMap_subtype_val _ (hC.preimage f.continuous), hC⟩

/-- Helper for Exercise 35.8: compatible maps on `X` and `Y` are constant on attachment fibers. -/
private theorem extensionAdjunctionFactorsThrough {X Y : Type u} {Z : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (A : Set X) (f : C(A, Y))
    (gX : C(X, Z)) (gY : C(Y, Z)) (hAttach : ∀ a : A, gX a = gY (f a)) :
    Function.FactorsThrough (Sum.elim gX gY) (extensionAdjunctionQuotientMap A f) := by
  classical
  intro w w' hww'
  -- Normalize both representatives by their codes and use compatibility on attached points.
  have hCode := (extensionAdjunctionQuotientMap_eq_iff A f w w').mp hww'
  cases w with
  | inl x =>
      cases w' with
      | inl x' =>
          by_cases hx : x ∈ A
          · by_cases hx' : x' ∈ A
            · rw [extensionAdjunctionCode_inl_of_mem A f hx,
                extensionAdjunctionCode_inl_of_mem A f hx'] at hCode
              have hf : f ⟨x, hx⟩ = f ⟨x', hx'⟩ := Sum.inr.inj hCode
              calc
                Sum.elim gX gY (Sum.inl x) = gY (f ⟨x, hx⟩) := hAttach ⟨x, hx⟩
                _ = gY (f ⟨x', hx'⟩) := congrArg gY hf
                _ = Sum.elim gX gY (Sum.inl x') := (hAttach ⟨x', hx'⟩).symm
            · rw [extensionAdjunctionCode_inl_of_mem A f hx,
                extensionAdjunctionCode_inl_of_not_mem A f hx'] at hCode
              exact (Sum.inr_ne_inl hCode).elim
          · by_cases hx' : x' ∈ A
            · rw [extensionAdjunctionCode_inl_of_not_mem A f hx,
                extensionAdjunctionCode_inl_of_mem A f hx'] at hCode
              exact (Sum.inl_ne_inr hCode).elim
            · rw [extensionAdjunctionCode_inl_of_not_mem A f hx,
                extensionAdjunctionCode_inl_of_not_mem A f hx'] at hCode
              exact congrArg gX (Sum.inl.inj hCode)
      | inr y =>
          by_cases hx : x ∈ A
          · rw [extensionAdjunctionCode_inl_of_mem A f hx,
              extensionAdjunctionCode_inr A f y] at hCode
            calc
              Sum.elim gX gY (Sum.inl x) = gY (f ⟨x, hx⟩) := hAttach ⟨x, hx⟩
              _ = gY y := congrArg gY (Sum.inr.inj hCode)
              _ = Sum.elim gX gY (Sum.inr y) := rfl
          · rw [extensionAdjunctionCode_inl_of_not_mem A f hx,
              extensionAdjunctionCode_inr A f y] at hCode
            exact (Sum.inl_ne_inr hCode).elim
  | inr y =>
      cases w' with
      | inl x =>
          by_cases hx : x ∈ A
          · rw [extensionAdjunctionCode_inr A f y,
              extensionAdjunctionCode_inl_of_mem A f hx] at hCode
            calc
              Sum.elim gX gY (Sum.inr y) = gY y := rfl
              _ = gY (f ⟨x, hx⟩) := congrArg gY (Sum.inr.inj hCode)
              _ = Sum.elim gX gY (Sum.inl x) := (hAttach ⟨x, hx⟩).symm
          · rw [extensionAdjunctionCode_inr A f y,
              extensionAdjunctionCode_inl_of_not_mem A f hx] at hCode
            exact (Sum.inr_ne_inl hCode).elim
      | inr y' =>
          rw [extensionAdjunctionCode_inr A f y,
            extensionAdjunctionCode_inr A f y'] at hCode
          exact congrArg gY (Sum.inr.inj hCode)

/-- Helper for Exercise 35.8: disjoint closed sets in the adjunction space admit a
continuous zero-one separator. -/
private theorem extensionAdjunctionExistsSeparator {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T4Space X] [T4Space Y] {A : Set X} (hA : IsClosed A)
    (f : C(A, Y)) {S T : Set (ExtensionAdjunctionSpace A f)} (hS : IsClosed S)
    (hT : IsClosed T) (hST : Disjoint S T) :
    ∃ g : C(ExtensionAdjunctionSpace A f, ℝ), Set.EqOn g 0 S ∧ Set.EqOn g 1 T := by
  classical
  let SX : Set X := extensionAdjunctionIncludeX A f ⁻¹' S
  let TX : Set X := extensionAdjunctionIncludeX A f ⁻¹' T
  let SY : Set Y := extensionAdjunctionIncludeY A f ⁻¹' S
  let TY : Set Y := extensionAdjunctionIncludeY A f ⁻¹' T
  have hSX : IsClosed SX := hS.preimage (extensionAdjunctionContinuous_includeX A f)
  have hTX : IsClosed TX := hT.preimage (extensionAdjunctionContinuous_includeX A f)
  have hSY : IsClosed SY := hS.preimage (extensionAdjunctionContinuous_includeY A f)
  have hTY : IsClosed TY := hT.preimage (extensionAdjunctionContinuous_includeY A f)
  have hSXTX : Disjoint SX TX := hST.preimage (extensionAdjunctionIncludeX A f)
  have hSYTY : Disjoint SY TY := hST.preimage (extensionAdjunctionIncludeY A f)
  -- First separate the two pulled-back closed sets in `Y`.
  obtain ⟨gY, hgYS, hgYT, -⟩ :=
    exists_continuous_zero_one_of_isClosed hSY hTY hSYTY
  -- Tietze extends the boundary values `gY ∘ f` across `X`.
  obtain ⟨gA, hgA⟩ := (gY.comp f).exists_restrict_eq hA
  have hgA_eq (a : A) : gA a = gY (f a) := ContinuousMap.congr_fun hgA a
  have hgA_zero (a : A) (ha : (a : X) ∈ SX) : gA a = 0 := by
    have hfa : f a ∈ SY := by
      change extensionAdjunctionIncludeY A f (f a) ∈ S
      change extensionAdjunctionIncludeX A f a ∈ S at ha
      rw [← extensionAdjunctionGlue A f a]
      exact ha
    exact (hgA_eq a).trans (hgYS hfa)
  have hgA_one (a : A) (ha : (a : X) ∈ TX) : gA a = 1 := by
    have hfa : f a ∈ TY := by
      change extensionAdjunctionIncludeY A f (f a) ∈ T
      change extensionAdjunctionIncludeX A f a ∈ T at ha
      rw [← extensionAdjunctionGlue A f a]
      exact ha
    exact (hgA_eq a).trans (hgYT hfa)
  -- Patch the extension with constants on the two closed pullbacks in `X`.
  let k : X → ℝ := fun x ↦ if x ∈ A then gA x else if x ∈ SX then 0 else 1
  have hkA : Set.EqOn k gA A := by
    intro x hx
    simp only [k, if_pos hx]
  have hkSX : Set.EqOn k 0 SX := by
    intro x hx
    by_cases hxA : x ∈ A
    · simp only [k, if_pos hxA, hgA_zero ⟨x, hxA⟩ hx, Pi.zero_apply]
    · simp only [k, if_neg hxA, if_pos hx, Pi.zero_apply]
  have hkTX : Set.EqOn k 1 TX := by
    intro x hx
    by_cases hxA : x ∈ A
    · simp only [k, if_pos hxA, hgA_one ⟨x, hxA⟩ hx, Pi.one_apply]
    · by_cases hxS : x ∈ SX
      · exact (Set.disjoint_left.mp hSXTX hxS hx).elim
      · simp only [k, if_neg hxA, if_neg hxS, Pi.one_apply]
  have hkContinuousA : ContinuousOn k A := gA.continuous.continuousOn.congr hkA
  have hkContinuousSX : ContinuousOn k SX := continuous_const.continuousOn.congr hkSX
  have hkContinuousTX : ContinuousOn k TX := continuous_const.continuousOn.congr hkTX
  let D : Set X := A ∪ SX ∪ TX
  have hD : IsClosed D := (hA.union hSX).union hTX
  have hkContinuous : ContinuousOn k D :=
    (hkContinuousA.union_of_isClosed hkContinuousSX hA hSX).union_of_isClosed
      hkContinuousTX (hA.union hSX) hTX
  let kD : C(D, ℝ) :=
    ⟨fun x ↦ k x, continuousOn_iff_continuous_restrict.mp hkContinuous⟩
  -- A second Tietze extension now has the required values on both pullbacks.
  obtain ⟨gX, hgX⟩ := kD.exists_restrict_eq hD
  have hgX_eq (x : D) : gX x = k x := ContinuousMap.congr_fun hgX x
  have hgXS : Set.EqOn gX 0 SX := by
    intro x hx
    calc
      gX x = k x := hgX_eq ⟨x, Or.inl (Or.inr hx)⟩
      _ = 0 := hkSX hx
  have hgXT : Set.EqOn gX 1 TX := by
    intro x hx
    calc
      gX x = k x := hgX_eq ⟨x, Or.inr hx⟩
      _ = 1 := hkTX hx
  have hAttach (a : A) : gX a = gY (f a) := by
    calc
      gX a = k a := hgX_eq ⟨a, Or.inl (Or.inl a.property)⟩
      _ = gA a := hkA a.property
      _ = gY (f a) := hgA_eq a
  let gSum : C(X ⊕ Y, ℝ) :=
    ⟨Sum.elim gX gY, gX.continuous.sumElim gY.continuous⟩
  let q : C(X ⊕ Y, ExtensionAdjunctionSpace A f) :=
    ⟨extensionAdjunctionQuotientMap A f,
      (extensionAdjunctionQuotientMap_isQuotientMap A f).continuous⟩
  have hq : Topology.IsQuotientMap q :=
    extensionAdjunctionQuotientMap_isQuotientMap A f
  have hFactors :
      Function.FactorsThrough gSum q :=
    extensionAdjunctionFactorsThrough A f gX gY hAttach
  let g : C(ExtensionAdjunctionSpace A f, ℝ) :=
    hq.lift gSum hFactors
  have hgComp :
      g.comp q = gSum := hq.lift_comp gSum hFactors
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, rfl⟩ := hq.surjective z
    have hgw := ContinuousMap.congr_fun hgComp w
    cases w with
    | inl x =>
        exact hgw.trans (hgXS hz)
    | inr y =>
        exact hgw.trans (hgYS hz)
  · intro z hz
    obtain ⟨w, rfl⟩ := hq.surjective z
    have hgw := ContinuousMap.congr_fun hgComp w
    cases w with
    | inl x =>
        exact hgw.trans (hgXT hz)
    | inr y =>
        exact hgw.trans (hgYT hz)

/-- Helper for Exercise 35.8: a closed attachment of normal spaces is normal. -/
private theorem extensionAdjunctionNormalSpace {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T4Space X] [T4Space Y] {A : Set X} (hA : IsClosed A)
    (f : C(A, Y)) : NormalSpace (ExtensionAdjunctionSpace A f) := by
  refine ⟨?_⟩
  intro S T hS hT hST
  -- A zero-one separator yields disjoint inverse-image neighborhoods at the midpoint.
  obtain ⟨g, hgS, hgT⟩ := extensionAdjunctionExistsSeparator hA f hS hT hST
  refine ⟨g ⁻¹' Set.Iio (1 / 2 : ℝ), g ⁻¹' Set.Ioi (1 / 2 : ℝ),
    isOpen_Iio.preimage g.continuous, isOpen_Ioi.preimage g.continuous, ?_, ?_, ?_⟩
  · intro z hz
    have hgz : g z = 0 := by
      simpa only [Pi.zero_apply] using hgS hz
    simp only [Set.mem_preimage, Set.mem_Iio, hgz]
    norm_num
  · intro z hz
    have hgz : g z = 1 := by
      simpa only [Pi.one_apply] using hgT hz
    simp only [Set.mem_preimage, Set.mem_Ioi, hgz]
    norm_num
  · rw [Set.disjoint_left]
    intro z hzS hzT
    change g z < (1 / 2 : ℝ) at hzS
    change (1 / 2 : ℝ) < g z at hzT
    exact (not_lt_of_ge (le_of_lt hzT)) hzS

/-- Helper for Exercise 35.8: a closed attachment of `T₄` spaces is `T₄`. -/
private theorem extensionAdjunctionT4Space {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T4Space X] [T4Space Y] {A : Set X} (hA : IsClosed A)
    (f : C(A, Y)) : T4Space (ExtensionAdjunctionSpace A f) := by
  letI : T1Space (ExtensionAdjunctionSpace A f) := extensionAdjunctionT1Space hA f
  letI : NormalSpace (ExtensionAdjunctionSpace A f) := extensionAdjunctionNormalSpace hA f
  -- The two established separation structures assemble into `T4Space`.
  infer_instance

/-- Helper for Exercise 35.8: a normal absolute retract has the universal extension property. -/
theorem toUniversalExtensionProperty {Y : Type u} [TopologicalSpace Y] [T4Space Y]
    (hY : AbsoluteRetract.{u, u} Y) : UniversalExtensionProperty.{u, u} Y := by
  refine ⟨?_⟩
  intro X _ _ A hA f
  classical
  -- Attach `X` to a disjoint canonical copy of `Y` along `f`.
  letI : T4Space (ExtensionAdjunctionSpace A f) := extensionAdjunctionT4Space hA f
  let includeX : C(X, ExtensionAdjunctionSpace A f) :=
    ⟨extensionAdjunctionIncludeX A f, extensionAdjunctionContinuous_includeX A f⟩
  let includeY : C(Y, ExtensionAdjunctionSpace A f) :=
    ⟨extensionAdjunctionIncludeY A f, extensionAdjunctionContinuous_includeY A f⟩
  have hIncludeY : Topology.IsClosedEmbedding includeY :=
    extensionAdjunctionIncludeY_isClosedEmbedding hA f
  -- The absolute retract hypothesis retracts the attachment onto the canonical copy of `Y`.
  obtain ⟨r, hr⟩ := (Set.isRetract_iff (Set.range includeY)).mp
    (hY.isRetract_range includeY hIncludeY)
  let rangeHomeomorph : Y ≃ₜ Set.range includeY :=
    hIncludeY.isEmbedding.toHomeomorph
  let g : C(X, Y) :=
    (rangeHomeomorph.symm : C(Set.range includeY, Y)).comp (r.comp includeX)
  refine ⟨g, ?_⟩
  ext a
  have hRangeValue :
      ((rangeHomeomorph (f a) : Set.range includeY) : ExtensionAdjunctionSpace A f) =
        includeY (f a) := by
    rfl
  have hrValue : r (includeY (f a)) = rangeHomeomorph (f a) := by
    have hr' := hr (rangeHomeomorph (f a))
    rw [hRangeValue] at hr'
    exact hr'
  -- Glue identifies `a` with `f a`; the retraction and range homeomorphism then recover `f a`.
  calc
    g.restrict A a = rangeHomeomorph.symm (r (includeX a)) := rfl
    _ = rangeHomeomorph.symm (r (includeY (f a))) :=
      congrArg rangeHomeomorph.symm
        (congrArg r (extensionAdjunctionGlue A f a))
    _ = rangeHomeomorph.symm (rangeHomeomorph (f a)) :=
      congrArg rangeHomeomorph.symm hrValue
    _ = f a := rangeHomeomorph.symm_apply_apply (f a)

end AbsoluteRetract

/-- Exercise 35.8. A normal space is an absolute retract if and only if it has the
universal extension property. -/
theorem absoluteRetract_iff_universalExtensionProperty
    {Y : Type u} [TopologicalSpace Y] [T4Space Y] :
    AbsoluteRetract.{u, u} Y ↔ UniversalExtensionProperty.{u, u} Y :=
  ⟨AbsoluteRetract.toUniversalExtensionProperty,
    UniversalExtensionProperty.toAbsoluteRetract⟩
