import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Covering.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Definition_1_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open CategoryTheory FundamentalGroup Path.Homotopic.Quotient
open scoped FundamentalGroup Pointwise

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B}

/-- Basepoint change along a path inside a fiber commutes with the induced map on fundamental
groups of a covering map. -/
theorem mapOfEq_comp_basepoint_change (hp : IsCoveringMap p)
    {b : B} {e e' : p ⁻¹' {b}} (δ : Path e.1 e'.1) :
    (mapOfEq ⟨p, hp.continuous⟩ e'.property).comp (γ[δ]).toMonoidHom =
      (γ[((δ.map hp.continuous).cast e.property.symm e'.property.symm)]).toMonoidHom.comp
        (mapOfEq ⟨p, hp.continuous⟩ e.property) := by
  let he : p e.1 = b := e.property
  let he' : p e'.1 = b := e'.property
  let F := FundamentalGroupoid.map ⟨p, hp.continuous⟩
  let eδ : FundamentalGroupoid.mk e.1 ≅ FundamentalGroupoid.mk e'.1 :=
    (Groupoid.isoEquivHom _ _).symm ⟦δ⟧
  let eb : FundamentalGroupoid.mk (p e.1) ≅ FundamentalGroupoid.mk b :=
    eqToIso (congrArg FundamentalGroupoid.mk he)
  let eb' : FundamentalGroupoid.mk (p e'.1) ≅ FundamentalGroupoid.mk b :=
    eqToIso (congrArg FundamentalGroupoid.mk he')
  let eδb : FundamentalGroupoid.mk b ≅ FundamentalGroupoid.mk b :=
    (Groupoid.isoEquivHom _ _).symm ⟦(δ.map hp.continuous).cast he.symm he'.symm⟧
  have heδb :
      eδb = eb.symm ≪≫ F.mapIso eδ ≪≫ eb' := by
    ext
    simpa [eδb, eδ, eb, eb', F, mk_map] using
      (FundamentalGroupoid.conj_eqToHom he.symm he'.symm).symm
  ext α
  change eb'.conj (F.map (eδ.conj α)) = eδb.conj (eb.conj (F.map α))
  (convert congrArg eb'.conj (F.map_conj eδ α) using 1; simp [heδb])
  rfl

/-- A path joining two points of the same fiber conjugates the corresponding image subgroups of
`π₁(E)` inside `π₁(B, b)`. -/
theorem mapOfEq_range_conjugate_of_path (hp : IsCoveringMap p) {b : B}
    (e e' : p ⁻¹' {b}) (δ : Path e.1 e'.1) :
    (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
      MulAut.conj (fromPath ⟦(δ.map hp.continuous).cast e.property.symm e'.property.symm⟧) •
        (mapOfEq ⟨p, hp.continuous⟩ e.property).range := by
  let he : p e.1 = b := e.property
  let he' : p e'.1 = b := e'.property
  let g : FundamentalGroup B b := fromPath ⟦(δ.map hp.continuous).cast he.symm he'.symm⟧
  let m : FundamentalGroup E e.1 →* FundamentalGroup B b := mapOfEq ⟨p, hp.continuous⟩ he
  let m' : FundamentalGroup E e'.1 →* FundamentalGroup B b := mapOfEq ⟨p, hp.continuous⟩ he'
  let c : FundamentalGroup E e.1 →* FundamentalGroup E e'.1 := (γ[δ]).toMonoidHom
  have hcomp :
      m'.comp c =
        (γ[((δ.map hp.continuous).cast he.symm he'.symm)]).toMonoidHom.comp m :=
    mapOfEq_comp_basepoint_change hp δ
  have hcomp' : m'.comp c = (MulAut.conj g).toMonoidHom.comp m := by
    simpa [g] using hcomp
  have hrange : (m'.comp c).range = m'.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective c (γ[δ]).surjective,
      ← MonoidHom.range_eq_map]
  calc
    m'.range = (m'.comp c).range := hrange.symm
    _ = ((MulAut.conj g).toMonoidHom.comp m).range := by rw [hcomp']
    _ = m.range.map (MulAut.conj g).toMonoidHom := MonoidHom.range_comp _ _
    _ = MulAut.conj g • m.range := by
      rfl

/-- If two points in the fiber `p ⁻¹' {b}` are joined by a path in `E`, then the image subgroups
of the induced maps on fundamental groups at those points are conjugate inside `π₁(B, b)`. -/
-- Proof sketch: choose a path `δ` joining the two fiber points. The projected loop `(p ∘ δ)` at
-- `b` defines the conjugating element `g : π₁(B, b)`, and naturality of `mapOfEq` with respect to
-- basepoint change identifies the two image subgroups up to the inner automorphism `MulAut.conj g`.
theorem fundamentalGroup_map_range_conjugate (hp : IsCoveringMap p) {b : B}
    (e e' : p ⁻¹' {b}) (h : Joined e.1 e'.1) :
    ∃ g : FundamentalGroup B b,
      (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
        MulAut.conj g • (mapOfEq ⟨p, hp.continuous⟩ e.property).range :=
  ⟨fromPath ⟦(h.somePath.map hp.continuous).cast e.property.symm e'.property.symm⟧,
    mapOfEq_range_conjugate_of_path hp e e' h.somePath⟩

/-- Ordinary-point form of `fundamentalGroup_map_range_conjugate`: if `e,e' : E` lie in the same
fiber of `p` and are joined in `E`, then the image subgroup of `π₁(E, e') → π₁(B, p e')` is
conjugate to the image of `π₁(E, e) → π₁(B, p e')`. -/
theorem fundamentalGroup_map_range_conjugate_of_eq (hp : IsCoveringMap p)
    (e e' : E) (he : p e = p e') (h : Joined e e') :
    ∃ g : FundamentalGroup B (p e'),
      (FundamentalGroup.map ⟨p, hp.continuous⟩ e').range =
        MulAut.conj g • (mapOfEq ⟨p, hp.continuous⟩ he).range := by
  obtain ⟨g, hg⟩ :=
    fundamentalGroup_map_range_conjugate hp ⟨e, he⟩ ⟨e', rfl⟩ h
  refine ⟨g, ?_⟩
  have hmap : FundamentalGroup.map ⟨p, hp.continuous⟩ e' =
      mapOfEq ⟨p, hp.continuous⟩ rfl :=
    FundamentalGroup.map_eq_mapOfEq_rfl e'
  simpa [hmap] using hg

/-- Theorem 3.2.4: if `E` is path connected and `e,e' : E` lie in the same fiber of a covering
map `p : E → B`, then the image subgroups of the induced maps on fundamental groups at `e` and
`e'` are conjugate inside `π₁(B, p e')`. -/
theorem fundamentalGroup_map_range_conjugate_of_pathConnectedSpace [PathConnectedSpace E]
    (hp : IsCoveringMap p) (e e' : E) (he : p e = p e') :
    ∃ g : FundamentalGroup B (p e'),
      (FundamentalGroup.map ⟨p, hp.continuous⟩ e').range =
        MulAut.conj g • (mapOfEq ⟨p, hp.continuous⟩ he).range :=
  fundamentalGroup_map_range_conjugate_of_eq hp e e' he (PathConnectedSpace.joined e e')

end IsCoveringMap
