/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part13
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part15
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part16
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part17
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part18
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part19
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part20
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part21
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part22
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part23

/-!
Overview page for 3.15 Polars of Convex Functions.

This aggregation module imports all currently available part files for this section.
Use this page to jump to each part page quickly.

Verso links:
- [Section overview](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15/)
- [Chapter overview](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/)
- [Book overview](/ReasBook/books/convexanalysis_rockafellar_1970/book/)

Directory:

- Part 1 ([Documentation](../section15_part1.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part1/))
- Part 2 ([Documentation](../section15_part2.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part2/))
- Part 3 ([Documentation](../section15_part3.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part3/))
- Part 4 ([Documentation](../section15_part4.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part4/))
- Part 5 ([Documentation](../section15_part5.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part5/))
- Part 6 ([Documentation](../section15_part6.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part6/))
- Part 7 ([Documentation](../section15_part7.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part7/))
- Part 8 ([Documentation](../section15_part8.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part8/))
- Part 9 ([Documentation](../section15_part9.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part9/))
- Part 10 ([Documentation](../section15_part10.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part10/))
- Part 11 ([Documentation](../section15_part11.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part11/))
- Part 12 ([Documentation](../section15_part12.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part12/))
- Part 13 ([Documentation](../section15_part13.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part13/))
- Part 14 ([Documentation](../section15_part14.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part14/))
- Part 15 ([Documentation](../section15_part15.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part15/))
- Part 16 ([Documentation](../section15_part16.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part16/))
- Part 17 ([Documentation](../section15_part17.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part17/))
- Part 18 ([Documentation](../section15_part18.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part18/))
- Part 19 ([Documentation](../section15_part19.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part19/))
- Part 20 ([Documentation](../section15_part20.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part20/))
- Part 21 ([Documentation](../section15_part21.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part21/))
- Part 22 ([Documentation](../section15_part22.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part22/))
- Part 23 ([Documentation](../section15_part23.html)) ([Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap03/section15_part23/))

-/
