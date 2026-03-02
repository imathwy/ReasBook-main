/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part13
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part15
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part16

/-!
Overview page for 2.9 Some Closedness Criteria.

This aggregation module imports all currently available part files for this section.
Use this page to jump to each part page quickly.

Verso links:
- [Section overview](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09/)
- [Chapter overview](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/)
- [Book overview](/ReasBook/books/convexanalysis_rockafellar_1970/book/)

Directory:

- Part 1 ([Documentation](/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section09_part1.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09_part1/))
- Part 2 ([Documentation](/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section09_part2.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09_part2/))
- Part 3 ([Documentation](/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section09_part3.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09_part3/))
- Part 4 ([Documentation](/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section09_part4.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09_part4/))
- Part 5 ([Documentation](/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section09_part5.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09_part5/))
- Part 6 ([Documentation](/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section09_part6.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09_part6/))
- Part 7 ([Documentation](/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section09_part7.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09_part7/))
- Part 8 ([Documentation](/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section09_part8.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09_part8/))
- Part 9 ([Documentation](/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section09_part9.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09_part9/))
- Part 10 ([Documentation](/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section09_part10.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09_part10/))
- Part 11 ([Documentation](/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section09_part11.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09_part11/))
- Part 13 ([Documentation](/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section09_part13.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09_part13/))
- Part 14 ([Documentation](/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section09_part14.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09_part14/))
- Part 15 ([Documentation](/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section09_part15.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09_part15/))
- Part 16 ([Documentation](/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section09_part16.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section09_part16/))

-/
