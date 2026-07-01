import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.CategoryTheory.Preadditive.Biproducts

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits HomologicalComplex
open HomologicalComplex.homotopyCofiber

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V]
variable {A B : ChainComplex V ℤ} (f : A ⟶ B)

private lemma downRel (n : ℤ) : (ComplexShape.down ℤ).Rel n (n - 1) :=
  ComplexShape.down_mk n (n - 1) (sub_add_cancel n 1)

/- Domain-style sampling:
- primary domain: chain-complex mapping cones, viewed through the canonical owner
  `HomologicalComplex.homotopyCofiber`;
- sampled owner declarations:
  `HomologicalComplex.homotopyCofiber.XIsoBiprod`,
  `HomologicalComplex.homotopyCofiber.inrX_d`,
  `HomologicalComplex.homotopyCofiber.inlX_d`,
  `CategoryTheory.Biprod.ofComponents`;
- best owner abstraction: the cone object `homotopyCofiber f` with its canonical degreewise
  biproduct presentation; the textbook order `B.X n ⊞ A.X (n - 1)` is a `bridge/view`, obtained
  from `XIsoBiprod` by the biproduct braiding;
- primitive data: the chain map `f` and the owner morphisms `d`, `fstX`, `sndX`, `inlX`, `inrX`;
- derived API: the block-matrix description of the cone differential in textbook coordinates.
- layer triage: this theorem is a `bridge/view` restatement of the owner differential formulas,
  not a second cone owner. -/

-- Proof sketch: rewrite the homotopy-cofiber differential using
-- `homotopyCofiber.d_fstX` and `homotopyCofiber.d_sndX`, then transport across the biproduct
-- braidings to swap from mathlib's `A.X (n - 1) ⊞ B.X n` order to the textbook order
-- `B.X n ⊞ A.X (n - 1)`.
/-- The degree `n` term of the cone of `f`, written in the textbook order `B.X n ⊞ A.X (n - 1)`. -/
def chainMapConeTextbookXIso (n : ℤ) :
    (homotopyCofiber f).X n ≅ B.X n ⊞ A.X (n - 1) :=
  XIsoBiprod f n (n - 1) (downRel n) ≪≫
    biprod.braiding (A.X (n - 1)) (B.X n)

private theorem chainMap_cone_d_eq_ofComponents_owner (n : ℤ) :
    (XIsoBiprod f n (n - 1) (downRel n)).inv ≫ (homotopyCofiber f).d n (n - 1) ≫
        (XIsoBiprod f (n - 1) ((n - 1) - 1) (downRel (n - 1))).hom =
      Biprod.ofComponents (-A.d (n - 1) ((n - 1) - 1)) (f.f (n - 1)) 0 (B.d n (n - 1)) := by
  sorry

/-- 15.28.6.1: after identifying the degree `n` term of the cone of a chain map `f : A ⟶ B`
with `B.X n ⊞ A.X (n - 1)`, its differential is the block matrix
`(d_B,n  f_{n-1}; 0  -d_A,n-1)`. -/
theorem chainMap_cone_d_eq_ofComponents (n : ℤ) :
    (chainMapConeTextbookXIso f n).inv ≫ (homotopyCofiber f).d n (n - 1) ≫
        (chainMapConeTextbookXIso f (n - 1)).hom =
      Biprod.ofComponents (B.d n (n - 1)) 0 (f.f (n - 1))
        (-A.d (n - 1) ((n - 1) - 1)) := by
  calc
    (chainMapConeTextbookXIso f n).inv ≫ (homotopyCofiber f).d n (n - 1) ≫
        (chainMapConeTextbookXIso f (n - 1)).hom =
      (biprod.braiding (A.X (n - 1)) (B.X n)).inv ≫
          ((XIsoBiprod f n (n - 1) (downRel n)).inv ≫ (homotopyCofiber f).d n (n - 1) ≫
            (XIsoBiprod f (n - 1) ((n - 1) - 1) (downRel (n - 1))).hom) ≫
          (biprod.braiding (A.X ((n - 1) - 1)) (B.X (n - 1))).hom := by
        simp [chainMapConeTextbookXIso, Category.assoc]
    _ =
      (biprod.braiding (A.X (n - 1)) (B.X n)).inv ≫
          Biprod.ofComponents (-A.d (n - 1) ((n - 1) - 1)) (f.f (n - 1)) 0
            (B.d n (n - 1)) ≫
          (biprod.braiding (A.X ((n - 1) - 1)) (B.X (n - 1))).hom := by
        rw [chainMap_cone_d_eq_ofComponents_owner]
    _ =
      Biprod.ofComponents (B.d n (n - 1)) 0 (f.f (n - 1))
        (-A.d (n - 1) ((n - 1) - 1)) := by
        rw [← Biprod.ofComponents_eq
          ((biprod.braiding (A.X (n - 1)) (B.X n)).inv ≫
            Biprod.ofComponents (-A.d (n - 1) ((n - 1) - 1)) (f.f (n - 1)) 0
              (B.d n (n - 1)) ≫
            (biprod.braiding (A.X ((n - 1) - 1)) (B.X (n - 1))).hom)]
        ext <;> simp
