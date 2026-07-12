import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

noncomputable section

open CategoryTheory
open Scheme

variable {X : Scheme}

/-- Definition 29.7.1 (1): for an open subscheme `U ⊆ X`, the scheme theoretic closure of `U`
in `X` is the scheme-theoretic image of the inclusion `U ⟶ X`. -/
@[stacks 01RA]
def schemeTheoreticClosure (U : X.Opens) : Scheme :=
  Scheme.Hom.image U.ι

/-- The canonical closed immersion from the scheme theoretic closure of an open subscheme into the
ambient scheme. -/
def schemeTheoreticClosureι (U : X.Opens) : schemeTheoreticClosure U ⟶ X :=
  Scheme.Hom.imageι U.ι

/-- Companion expansion for `schemeTheoreticClosure`. -/
@[stacks 01RA, simp] theorem schemeTheoreticClosure_eq_image (U : X.Opens) :
    schemeTheoreticClosure U = Scheme.Hom.image U.ι := rfl

/-- Companion expansion for the canonical immersion from the scheme theoretic closure. -/
@[simp] theorem schemeTheoreticClosureι_eq_imageι (U : X.Opens) :
    schemeTheoreticClosureι U = Scheme.Hom.imageι U.ι := rfl

/-- For open subschemes `U, V ⊆ X`, the scheme theoretic closure of `U ∩ V` in `V`. -/
@[stacks 01RA]
def schemeTheoreticClosureIn (U V : X.Opens) : Scheme :=
  Scheme.Hom.image (X.homOfLE (inf_le_right : U ⊓ V ≤ V))

/-- The canonical closed immersion from the scheme theoretic closure of `U ∩ V` into `V`. -/
def schemeTheoreticClosureInι (U V : X.Opens) : schemeTheoreticClosureIn U V ⟶ V :=
  Scheme.Hom.imageι (X.homOfLE (inf_le_right : U ⊓ V ≤ V))

/-- Companion expansion for `schemeTheoreticClosureIn`. -/
@[stacks 01RA, simp] theorem schemeTheoreticClosureIn_eq_image (U V : X.Opens) :
    schemeTheoreticClosureIn U V =
      Scheme.Hom.image (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) := rfl

/-- Companion expansion for the canonical immersion from the relative scheme theoretic closure. -/
@[simp] theorem schemeTheoreticClosureInι_eq_imageι (U V : X.Opens) :
    schemeTheoreticClosureInι U V =
      Scheme.Hom.imageι (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) := rfl

/-- Definition 29.7.1 (2): an open subscheme `U ⊆ X` is scheme theoretically dense in `X` if for
every open subscheme `V ⊆ X`, the scheme theoretic closure of `U ∩ V` in `V` is equal to `V`. -/
@[stacks 01RA]
def schemeTheoreticallyDense (U : X.Opens) : Prop :=
  ∀ V : X.Opens, schemeTheoreticClosureIn U V = V

/-- Companion expansion for `schemeTheoreticallyDense`. -/
@[stacks 01RA, simp] theorem schemeTheoreticallyDense_iff (U : X.Opens) :
    schemeTheoreticallyDense U ↔
      ∀ V : X.Opens, schemeTheoreticClosureIn U V = V := Iff.rfl

end

end AlgebraicGeometry
