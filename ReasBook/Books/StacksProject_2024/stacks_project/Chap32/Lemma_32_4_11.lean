import Mathlib
import StacksProject_2024.stacks_project.Chap32.Situation_32_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ j, CompactSpace ↥(D.obj j)]
variable [∀ j, QuasiSeparatedSpace ↥(D.obj j)]
variable [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]

-- Semantic recall: `lean_leansearch` surfaced
-- `AlgebraicGeometry.exists_preimage_eq` in `Mathlib.AlgebraicGeometry.AffineTransitionLimit`;
-- the statements below package the source-facing quasi-compact-open descent and stabilization
-- clauses for the directed inverse-system setup fixed in Situation `32.4.5`.

/-- Lemma 32.4.11 (1): for a quasi-compact open `V ⊆ S = \lim_i S_i` in Situation `32.4.5`,
there exists a stage `i` and a quasi-compact open `V_i ⊆ S_i` whose inverse image in `S`
is `V`. -/
@[stacks 01Z4]
theorem exists_compactOpen_stage_preimage_eq
    (V : CompactOpens c.pt.carrier) :
    ∃ i : I, ∃ Vi : CompactOpens (D.obj i).carrier,
      (Opens.map (c.π.app i).base).obj Vi.toOpens = V.toOpens := sorry

/-- Lemma 32.4.11 (2): if two quasi-compact opens on stages `i` and `i'` have the same inverse
image in the limit scheme `S`, then they become equal after pullback to some common upper stage. -/
@[stacks 01Z4]
theorem exists_ge_compactOpen_stage_preimage_eq_of_preimage_eq
    (i i' : I) (Vi : CompactOpens (D.obj i).carrier) (Vi' : CompactOpens (D.obj i').carrier)
    (hpreimage :
      (Opens.map (c.π.app i).base).obj Vi.toOpens =
        (Opens.map (c.π.app i').base).obj Vi'.toOpens) :
    ∃ (i'' : I) (hii'' : i ≤ i'') (hi'i'' : i' ≤ i''),
      (Opens.map (D.map (homOfLE hii'')).base).obj Vi.toOpens =
        (Opens.map (D.map (homOfLE hi'i'')).base).obj Vi'.toOpens := sorry

/-- Lemma 32.4.11 (3): if finitely many quasi-compact opens on a stage `S_i` pull back to a cover
of the limit scheme `S`, then after passing to some upper stage `i' ≥ i` their inverse images
already cover `S_{i'}`. -/
@[stacks 01Z4]
theorem exists_ge_iSup_eq_top_of_compactOpen_preimage_cover
    (n : ℕ) (i : I) (Vi : Fin n → CompactOpens (D.obj i).carrier)
    (hcover :
      iSup (fun a ↦ (Opens.map (c.π.app i).base).obj (Vi a).toOpens) = ⊤) :
    ∃ (i' : I) (hii' : i ≤ i'),
      iSup (fun a ↦ (Opens.map (D.map (homOfLE hii')).base).obj (Vi a).toOpens) = ⊤ := sorry

end

end AlgebraicGeometry
