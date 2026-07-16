import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_60.Definition_8_60_extra_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Notation 8.60-extra-6: for `v ∈ TₑG = GroupLieAlgebra I G`, the notation `vᴸ` denotes the
smooth left-invariant vector field `mulInvariantVectorField v` from equation (8.13). The
chapter's canonical owner for this construction was already recalled in
`Definition_8_60_extra_5`, so this file only adds the source-facing notation. -/
recall mulInvariantVectorField

postfix:max "ᴸ" => mulInvariantVectorField
