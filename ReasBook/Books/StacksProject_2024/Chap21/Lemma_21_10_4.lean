import Mathlib
import StacksProject_2024.Chap21.Definition_21_8_1
import StacksProject_2024.Chap21.Lemma_21_4_3

-- Declarations for this item will be appended below by the statement pipeline.

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
