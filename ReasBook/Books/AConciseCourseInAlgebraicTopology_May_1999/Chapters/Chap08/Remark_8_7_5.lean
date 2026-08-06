import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Construction_8_7_2

open CategoryTheory

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

/- Remark 8.7.5 is a bridge/view remark recording the loop-side comparison square from the fiber
sequence to the looped cofiber sequence. -/

section

variable {X Y : BasedSpace} (f : X ⟶ Y)

/- Construction 8.7.2 supplies the source-facing comparison morphism
`η : F_f ⟶ Ωᵇ C_f` for a fixed map `f : X ⟶ Y`. -/
#check (homotopyFiberToLoopHomotopyCofiber f : homotopyFiber f ⟶ Ωᵇ (homotopyCofiber f))

/- Remark 8.7.5 uses the incoming `HomotopicUnder` comparison square exported with
Construction 8.7.2. -/

#check
  (homotopyFiberToLoopHomotopyCofiber.comp_homotopyFiberLoopInclusion_homotopic f :
    HomotopicUnder
      (homotopyFiberLoopInclusion f ≫ homotopyFiberToLoopHomotopyCofiber f)
      (signedLoopBasedMap (homotopyCofiberTargetInclusion f)))

end
