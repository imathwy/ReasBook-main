module

public import Topology_Munkres_2000.Book.Definition_52_5.Convention
public import Mathlib.Topology.Subpath

public section

universe u

namespace FundamentalGroup

namespace LeftToRight

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Remark 52.2: every point traversed by a path lies in the path
component of its source. -/
private lemma pathPointMemPathComponent {x y : X} (p : Path x y) (t : unitInterval) :
    p t ∈ pathComponent x := by
  -- The initial subpath joins the source to the chosen point.
  have htarget : p t = p t := rfl
  exact ⟨(p.subpath 0 t).cast p.source.symm htarget⟩

/-- Helper for Remark 52.2: every point of a path homotopy lies in the path
component of the common source. -/
private lemma pathHomotopyPointMemPathComponent {x y : X} {p q : Path x y}
    (F : p.Homotopy q) (z : unitInterval × unitInterval) : F z ∈ pathComponent x := by
  -- Fixing the homotopy parameter gives a path with the same source.
  simpa only [Path.Homotopy.eval_apply, ContinuousMap.Homotopy.curry_apply,
    ContinuousMap.HomotopyWith.coe_toHomotopy] using
    pathPointMemPathComponent (F.eval z.1) z.2

/-- Helper for Remark 52.2: a path contained in a set lifts to the corresponding
subtype, and forgetting the subtype recovers the original path. -/
private lemma existsSubtypePathLift (A : Set X) {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (p : Path x y) (hp : ∀ t, p t ∈ A) :
    ∃ q : Path (⟨x, hx⟩ : A) ⟨y, hy⟩,
      q.map continuous_subtype_val = p := by
  -- First discharge continuity and endpoint compatibility for the subtype-valued path.
  have hcontinuous : Continuous (fun t ↦ (⟨p t, hp t⟩ : A)) :=
    p.continuous.subtype_mk hp
  have hsource : (⟨p 0, hp 0⟩ : A) = ⟨x, hx⟩ := by
    apply Subtype.ext
    exact p.source
  have htarget : (⟨p 1, hp 1⟩ : A) = ⟨y, hy⟩ := by
    apply Subtype.ext
    exact p.target
  let q : Path (⟨x, hx⟩ : A) ⟨y, hy⟩ :=
    { toFun := fun t ↦ ⟨p t, hp t⟩
      continuous_toFun := hcontinuous
      source' := hsource
      target' := htarget }
  refine ⟨q, ?_⟩
  -- Forgetting membership leaves the original path pointwise.
  ext t
  rfl

/-- Helper for Remark 52.2: an ambient homotopy whose image stays in a set
restricts to a homotopy between subtype-valued paths. -/
private lemma subtypePathsHomotopicOfValHomotopy (A : Set X) {a b : A}
    (p q : Path a b)
    (F : (p.map continuous_subtype_val).Homotopy (q.map continuous_subtype_val))
    (hF : ∀ z, F z ∈ A) : p.Homotopic q := by
  -- Build the lifted homotopy after isolating all continuity and boundary fields.
  have hcontinuous : Continuous (fun z ↦ (⟨F z, hF z⟩ : A)) :=
    F.continuous.subtype_mk hF
  have hzero (t : unitInterval) : (⟨F (0, t), hF (0, t)⟩ : A) = p t := by
    apply Subtype.ext
    exact F.map_zero_left t
  have hone (t : unitInterval) : (⟨F (1, t), hF (1, t)⟩ : A) = q t := by
    apply Subtype.ext
    exact F.map_one_left t
  have hrelative (t s : unitInterval) (hs : s ∈ ({0, 1} : Set unitInterval)) :
      (⟨F (t, s), hF (t, s)⟩ : A) = p s := by
    apply Subtype.ext
    exact F.eq_fst t hs
  let G : p.Homotopy q :=
    { toFun := fun z ↦ ⟨F z, hF z⟩
      continuous_toFun := hcontinuous
      map_zero_left := hzero
      map_one_left := hone
      prop' := hrelative }
  -- The constructed relative homotopy witnesses the desired relation.
  exact ⟨G⟩

/-- Helper for Remark 52.2: inclusion of a path component induces a bijection
on fundamental groups before changing to the left-to-right convention. -/
private lemma pathComponentFundamentalMap_bijective (x₀ : X) :
    Function.Bijective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x₀, X))
      ⟨x₀, mem_pathComponent_self x₀⟩) := by
  constructor
  · -- Equality after inclusion supplies an ambient homotopy, which restricts to the component.
    intro P Q hPQ
    induction P using Path.Homotopic.Quotient.ind with
    | mk p =>
        induction Q using Path.Homotopic.Quotient.ind with
        | mk q =>
            rw [FundamentalGroup.map_apply, FundamentalGroup.map_apply,
              ← Path.Homotopic.Quotient.mk_map,
              ← Path.Homotopic.Quotient.mk_map] at hPQ
            have hpath :
                Path.Homotopic.Quotient.mk
                    (p.map continuous_subtype_val) =
                  Path.Homotopic.Quotient.mk
                    (q.map continuous_subtype_val) := by
              exact congrArg FundamentalGroup.toPath hPQ
            obtain ⟨F⟩ := Path.Homotopic.Quotient.eq.mp hpath
            have hpq : p.Homotopic q :=
              subtypePathsHomotopicOfValHomotopy (pathComponent x₀) p q F
                (fun z ↦ pathHomotopyPointMemPathComponent F z)
            exact congrArg FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.eq.mpr hpq)
  · -- Lift an arbitrary ambient loop pointwise into the path component.
    intro P
    induction P using Path.Homotopic.Quotient.ind with
    | mk p =>
        obtain ⟨q, hq⟩ := existsSubtypePathLift (pathComponent x₀)
          (mem_pathComponent_self x₀) (mem_pathComponent_self x₀) p
          (fun t ↦ pathPointMemPathComponent p t)
        refine ⟨Path.Homotopic.Quotient.mk q, ?_⟩
        rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map, hq]

/-- Remark 52.2. The inclusion of the path component containing `x₀` into `X`
induces a bijection on fundamental groups, so `π₁(X, x₀)` depends only on that
path component. -/
theorem pathComponentInclusion_bijective (x₀ : X) :
    Function.Bijective (map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x₀, X))
      ⟨x₀, mem_pathComponent_self x₀⟩) := by
  -- First establish the corresponding bijection before the opposite-group convention.
  have hfundamental := pathComponentFundamentalMap_bijective x₀
  constructor
  · -- Apply quotient-level injectivity after removing `MulOpposite.op`.
    intro p q hpq
    apply MulOpposite.unop_injective
    apply hfundamental.1
    simpa only [map_apply, MulOpposite.unop_op] using
      congrArg MulOpposite.unop hpq
  · -- Lift a quotient class and wrap its preimage with `MulOpposite.op`.
    intro q
    obtain ⟨p, hp⟩ := hfundamental.2 q.unop
    refine ⟨MulOpposite.op p, ?_⟩
    apply MulOpposite.unop_injective
    simpa only [map_apply, MulOpposite.unop_op] using hp

end LeftToRight

end FundamentalGroup
