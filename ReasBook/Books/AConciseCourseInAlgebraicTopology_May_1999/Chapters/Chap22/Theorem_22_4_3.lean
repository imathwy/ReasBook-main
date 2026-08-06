import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.CWType
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Definition_18_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_4_1

noncomputable section

universe u

-- Source/core/bridge triage: this theorem is source-facing, while the reusable hypothesis owners
-- already live earlier in the repository as `SimpleSpace X` and `TopCat.HasCWType X`.

/-- Theorem 22.4.3: a simple space with the homotopy type of a CW complex admits a Postnikov
system. The simple-space hypothesis is expressed through the chapter owner `SimpleSpace X`, and
the CW-type hypothesis is expressed through the Chapter 10 owner `TopCat.HasCWType X`, whose
defining existential form is `TopCat.hasCWType_iff`. -/
theorem exists_postnikov_system_of_simple_space_of_cw_type
    {X : TopCat.{u}} [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    [SimpleSpace X] (hCWType : TopCat.HasCWType X) :
    Nonempty (PostnikovSystem X) := sorry
