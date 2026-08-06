import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Topology.UnitInterval

open scoped unitInterval

universe u v

variable {ι : Type u} {B : Type v} [TopologicalSpace B]

-- Semantic analogues checked: `PartitionOfUnity`, `BumpCovering`, and `LocallyFinite`.
-- The source notion is weaker, so we keep a dedicated owner with explicit `I`-valued functions.

/-- Definition 7.4.2: a numerable open cover of `B` is an indexed open cover `cover` equipped
with functions `toFun i : B → I` whose inverse images of `(0, 1]` are exactly the cover members,
and whose cover family is locally finite. -/
structure NumerableOpenCover (ι : Type u) (B : Type v) [TopologicalSpace B] where
  /-- The indexed family of open sets underlying the cover. -/
  cover : ι → TopologicalSpace.Opens B
  /-- The underlying family of `I`-valued functions. -/
  toFun : ι → B → I
  /-- The open sets `cover i` form an open cover of `B`. -/
  isOpenCover : TopologicalSpace.IsOpenCover cover
  /-- The inverse image of `(0, 1]` under the `i`th function is the `i`th cover member. -/
  iocPreimage_eq (i : ι) : toFun i ⁻¹' Set.Ioc (0 : I) 1 = cover i
  /-- The indexed cover family is locally finite. -/
  locallyFinite : LocallyFinite fun i ↦ (cover i).carrier

namespace NumerableOpenCover

/-- A numerable open cover can be evaluated as its family of `I`-valued functions. -/
instance : CoeFun (NumerableOpenCover ι B) (fun _ ↦ ι → B → I) where
  coe 𝒰 := 𝒰.toFun

/-- Evaluating a numerable open cover agrees with evaluating its `I`-valued function family. -/
@[simp]
theorem coe_apply (𝒰 : NumerableOpenCover ι B) (i : ι) (b : B) :
    𝒰 i b = 𝒰.toFun i b := rfl

/-- A point lies in the `i`th cover member exactly when the `i`th numerating function takes a
value in `(0, 1]`. -/
@[simp]
theorem mem_cover_iff_pos (𝒰 : NumerableOpenCover ι B) (i : ι) (b : B) :
    b ∈ 𝒰.cover i ↔ 0 < 𝒰 i b := by
  constructor
  · intro hb
    have hb' : b ∈ 𝒰 i ⁻¹' Set.Ioc (0 : I) 1 := by
      rw [𝒰.iocPreimage_eq i]
      exact hb
    change 𝒰 i b ∈ Set.Ioc (0 : I) 1 at hb'
    exact hb'.1
  · intro hb
    have hb' : 𝒰 i b ∈ Set.Ioc (0 : I) 1 := ⟨hb, le_top⟩
    have hb'' : b ∈ 𝒰 i ⁻¹' Set.Ioc (0 : I) 1 := hb'
    rw [𝒰.iocPreimage_eq i] at hb''
    exact hb''

/-- A point lies in the `i`th cover member exactly when the `i`th numerating function is nonzero.
-/
@[simp]
theorem mem_cover_iff_ne_zero (𝒰 : NumerableOpenCover ι B) (i : ι) (b : B) :
    b ∈ 𝒰.cover i ↔ 𝒰 i b ≠ 0 := by
  rw [mem_cover_iff_pos]
  constructor
  · intro hb hzero
    have hzero' : (𝒰 i b : ℝ) = 0 := by
      simpa using congrArg (fun x : I ↦ (x : ℝ)) hzero
    change (0 : ℝ) < (𝒰 i b : ℝ) at hb
    rw [hzero'] at hb
    exact (lt_irrefl 0) hb
  · intro hne
    have hne' : (𝒰 i b : ℝ) ≠ 0 := by
      intro hzero
      apply hne
      exact Subtype.ext <| by simpa using hzero
    change (0 : ℝ) < (𝒰 i b : ℝ)
    exact lt_of_le_of_ne (𝒰 i b).2.1 (Ne.symm hne')

/-- The `i`th cover member is exactly the support of the `i`th numerating function. -/
@[simp]
theorem support_eq (𝒰 : NumerableOpenCover ι B) (i : ι) :
    Function.support (𝒰 i) = 𝒰.cover i := by
  ext b
  rw [Function.mem_support]
  exact (mem_cover_iff_ne_zero 𝒰 i b).symm

/-- The supports of the numerating functions form a locally finite family. -/
theorem locallyFinite_support (𝒰 : NumerableOpenCover ι B) :
    LocallyFinite fun i ↦ Function.support (𝒰 i) := by
  simpa [𝒰.support_eq] using 𝒰.locallyFinite

/-- Every point of `B` lies in some cover member, so one numerating function is nonzero there. -/
theorem exists_ne_zero (𝒰 : NumerableOpenCover ι B) (b : B) :
    ∃ i, 𝒰 i b ≠ 0 := by
  obtain ⟨i, hi⟩ := 𝒰.isOpenCover.exists_mem b
  exact ⟨i, (mem_cover_iff_ne_zero 𝒰 i b).mp hi⟩

/-- Every point of `B` lies in some cover member, so one numerating function is positive there. -/
theorem exists_pos (𝒰 : NumerableOpenCover ι B) (b : B) :
    ∃ i, 0 < 𝒰 i b := by
  obtain ⟨i, hi⟩ := 𝒰.isOpenCover.exists_mem b
  exact ⟨i, (mem_cover_iff_pos 𝒰 i b).mp hi⟩

end NumerableOpenCover
