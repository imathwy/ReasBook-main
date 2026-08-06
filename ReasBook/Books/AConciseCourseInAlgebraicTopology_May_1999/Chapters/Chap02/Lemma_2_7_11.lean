module

public import Books.AConciseCourseInAlgebraicTopology_May_1999.GrothendieckFiberwiseColimit

public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits

noncomputable section

variable {C : Type u₁} [Category.{v₁} C]
variable {F : C ⥤ Cat}
variable [∀ S : C, HasColimitsOfShape (F.obj S) GrpCat]
variable [HasColimitsOfShape C GrpCat]
variable (G : Grothendieck F ⥤ GrpCat)
variable (S : C) (U : F.obj S)

/- Lemma 2.7.11 is the `GrpCat` specialization of the canonical Grothendieck-construction
comparison isomorphism `colimitFiberwiseColimitIso`: the iterated colimit of `G` over the fibers
and then over the base is canonically isomorphic to the single colimit of `G` over
`Grothendieck F`. -/
#check colimitFiberwiseColimitIso G

/- For each pair `(S, U)`, the canonical cocone leg into `colimit G` is the composite of the fiber
cocone leg, the base cocone leg, and the comparison isomorphism, as stated by
`ι_colimitFiberwiseColimitIso_hom`. -/
#check ι_colimitFiberwiseColimitIso_hom G S U

end
