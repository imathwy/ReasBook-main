/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

-- Aggregated imports for textbook formalization checks.
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap00.section03
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap01.section01
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap01.section02
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap01.section03
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap01.section04
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap01.section05
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap02.section01
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap02.section02
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap02.section03
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap02.section04
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap02.section05
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap02.section06
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap03.section01
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap03.section02
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap03.section03
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap03.section04
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap03.section05
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap03.section06
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap04.section01
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap04.section02
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap04.section03
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap04.section04
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap05.section01
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap05.section02
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap05.section03
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap05.section04
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap05.section05
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap06.section01
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap06.section02
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap06.section03
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap07.section01
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap07.section02
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap07.section03
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap07.section04
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap07.section05
import Books.IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chapters.Chap07.section06

/-!
Overview page for `Introduction to Real Analysis, Volume I (Jiri Lebl, 2025)`.

This aggregation module imports the currently formalized sections in this book.

Verso links:
- [Book home](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/)
- [Book overview](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/book/)

Directory:

Chapter 00

- [Section 0.3 file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap00/section03.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap00/section03/))

Chapter 01 -- Real Numbers

- [1.1 Basic Properties file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap01/section01.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap01/section01/))
- [1.2 The Set of Real Numbers file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap01/section02.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap01/section02/))
- [1.3 Absolute Value and Bounded Functions file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap01/section03.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap01/section03/))
- [1.4 Intervals and the Size of R file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap01/section04.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap01/section04/))
- [1.5 Decimal Representation of the Reals file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap01/section05.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap01/section05/))

Chapter 02 -- Sequences and Series

- [2.1 Sequences and Limits file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap02/section01.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap02/section01/))
- [2.2 Facts About Limits of Sequences file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap02/section02.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap02/section02/))
- [2.3 Limit Superior, Limit Inferior, and Bolzano-Weierstrass file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap02/section03.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap02/section03/))
- [2.4 Cauchy Sequences file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap02/section04.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap02/section04/))
- [2.5 Series file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap02/section05.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap02/section05/))
- [2.6 More on Series file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap02/section06.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap02/section06/))

Chapter 03 -- Continuous Functions

- [3.1 Limits of Functions file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap03/section01.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap03/section01/))
- [3.2 Continuous Functions file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap03/section02.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap03/section02/))
- [3.3 Extreme and Intermediate Value Theorems file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap03/section03.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap03/section03/))
- [3.4 Uniform Continuity file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap03/section04.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap03/section04/))
- [3.5 Limits at Infinity file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap03/section05.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap03/section05/))
- [3.6 Monotone Functions and Continuity file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap03/section06.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap03/section06/))

Chapter 04 -- The Derivative

- [4.1 The Derivative file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap04/section01.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap04/section01/))
- [4.2 Mean Value Theorem file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap04/section02.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap04/section02/))
- [4.3 Taylor's Theorem file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap04/section03.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap04/section03/))
- [4.4 Inverse Function Theorem file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap04/section04.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap04/section04/))

Chapter 05 -- The Riemann Integral

- [5.1 The Riemann Integral file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap05/section01.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap05/section01/))
- [5.2 Properties of the Integral file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap05/section02.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap05/section02/))
- [5.3 Fundamental Theorem of Calculus file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap05/section03.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap05/section03/))
- [5.4 The Logarithm and the Exponential file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap05/section04.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap05/section04/))
- [5.5 Improper Integrals file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap05/section05.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap05/section05/))

Chapter 06 -- Sequences of Functions

- [6.1 Pointwise and Uniform Convergence file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap06/section01.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap06/section01/))
- [6.2 Interchange of Limits file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap06/section02.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap06/section02/))
- [6.3 Picard's Theorem file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap06/section03.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap06/section03/))

Chapter 07 -- Metric Spaces

- [7.1 Metric Spaces file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap07/section01.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap07/section01/))
- [7.2 Open and Closed Sets file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap07/section02.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap07/section02/))
- [7.3 Sequences and Convergence file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap07/section03.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap07/section03/))
- [7.4 Completeness and Compactness file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap07/section04.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap07/section04/))
- [7.5 Continuous Functions file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap07/section05.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap07/section05/))
- [7.6 Fixed Point Theorem and Picard's Theorem Again file](https://github.com/imathwy/ReasBook-main/blob/main/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap07/section06.lean) ([Verso](https://imathwy.github.io/ReasBook-main/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap07/section06/))

-/
