module

import Book.Ch3.Algorithm_3_2_1.Iterates
public import Book.Ch5.Definition_5_11.Toeplitz
import Book.Ch5.Cor_5_23
import Book.Ch5.Definition_5_27.BCCB

public section

/-!
Remark 5.4 compares four qualitative method families in image reconstruction:
wavelet methods, multigrid methods, Toeplitz-based methods, and two-level
preconditioners. The current repository still lacks concrete Chapter 5 owners
for the wavelet, multigrid, and two-level families themselves, so this remark
stays at a thin source-facing `#check` surface instead of inventing a new
public owner for that qualitative comparison.

The Chapter 5 Toeplitz/BCCB owners and the Chapter 3 conjugate-gradient owner
remain relevant backend anchors, but they are secondary to that explicit
source-facing clause surface.
-/

section

universe u

variable {Method : Type u}
variable (WaveletMethod MultigridMethod ToeplitzMethod TwoLevelPreconditioner : Method → Prop)
variable
  (CanCompeteWith HasNoRealAdvantageOver : (Method → Prop) → (Method → Prop) → Prop)

/- Remark 5.4-extra-1. The source-facing qualitative content of the remark is
the direct family-level clause surface saying that wavelet, multigrid, and
Toeplitz-based methods can compete with two-level preconditioners, and that
Toeplitz-based methods have no real advantage over them. -/
#check
  CanCompeteWith WaveletMethod TwoLevelPreconditioner ∧
    CanCompeteWith MultigridMethod TwoLevelPreconditioner ∧
    CanCompeteWith ToeplitzMethod TwoLevelPreconditioner ∧
    HasNoRealAdvantageOver ToeplitzMethod TwoLevelPreconditioner

end

/- Remark 5.4. The Chapter 5 Toeplitz matrices compared with block-circulant
methods are still represented by the canonical owner `Matrix.toeplitzByDiag`. -/
#check Matrix.toeplitzByDiag

/- Remark 5.4. Corollary 5.23 remains the Chapter 5 Toeplitz-to-circulant
backend anchor for the Toeplitz side of the comparison. -/
#check Matrix.bestCirculantApproximation_toeplitzByDiag_eq_circulant

/- Remark 5.4. The Chapter 5 block-circulant side of the comparison is
represented by `Matrix.bccb`. -/
#check Matrix.bccb

/- Remark 5.4. The Chapter 3 iterative-method backend anchor is
`ConjugateGradient.iterates`. -/
#check ConjugateGradient.iterates
