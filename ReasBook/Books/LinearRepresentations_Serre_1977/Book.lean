import Mathlib

import LinearRepresentations_Serre_1977.Chapters.Chap01
import LinearRepresentations_Serre_1977.Chapters.Chap02
import LinearRepresentations_Serre_1977.Chapters.Chap03
import LinearRepresentations_Serre_1977.Chapters.Chap04
import LinearRepresentations_Serre_1977.Chapters.Chap05
import LinearRepresentations_Serre_1977.Chapters.Chap06
import LinearRepresentations_Serre_1977.Chapters.Chap07
import LinearRepresentations_Serre_1977.Chapters.Chap08
import LinearRepresentations_Serre_1977.Chapters.Chap09
import LinearRepresentations_Serre_1977.Chapters.Chap10
import LinearRepresentations_Serre_1977.Chapters.Chap11
import LinearRepresentations_Serre_1977.Chapters.Chap12
import LinearRepresentations_Serre_1977.Chapters.Chap13
import LinearRepresentations_Serre_1977.Chapters.Chap14
import LinearRepresentations_Serre_1977.Chapters.Chap15
import LinearRepresentations_Serre_1977.Chapters.Chap16
import LinearRepresentations_Serre_1977.Chapters.Chap17
import LinearRepresentations_Serre_1977.Chapters.Chap18
import LinearRepresentations_Serre_1977.Chapters.Chap19
import LinearRepresentations_Serre_1977.Chapters.Chap20
import LinearRepresentations_Serre_1977.Chapters.Chap21
import LinearRepresentations_Serre_1977.Chapters.Chap22
import LinearRepresentations_Serre_1977.Chapters.Chap23

/-!
Overview page for LinearRepresentations_Serre_1977.

This aggregation module imports the currently formalized sections in this book.
Use the links below to jump directly into chapter and section overview pages.

Verso links:
- [Book home](/ReasBook-private/books/linearrepresentations_serre_1977/)
- [Book overview](/ReasBook-private/books/linearrepresentations_serre_1977/book/)

Directory:

Chapter 01

- Section 1.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap01/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap01/section01/))

Chapter 02

- Section 2.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap02/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap02/section01/))

Chapter 03

- Section 3.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap03/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap03/section01/))

Chapter 04

- Section 4.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap04/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap04/section01/))

Chapter 05

- Section 5.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap05/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap05/section01/))

Chapter 06

- Section 6.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap06/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap06/section01/))

Chapter 07

- Section 7.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap07/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap07/section01/))

Chapter 08

- Section 8.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap08/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap08/section01/))

Chapter 09

- Section 9.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap09/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap09/section01/))

Chapter 10

- Section 10.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap10/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap10/section01/))

Chapter 11

- Section 11.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap11/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap11/section01/))

Chapter 12

- Section 12.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap12/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap12/section01/))

Chapter 13

- Section 13.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap13/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap13/section01/))

Chapter 14

- Section 14.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap14/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap14/section01/))

Chapter 15

- Section 15.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap15/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap15/section01/))

Chapter 16

- Section 16.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap16/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap16/section01/))

Chapter 17

- Section 17.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap17/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap17/section01/))

Chapter 18

- Section 18.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap18/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap18/section01/))

Chapter 19

- Section 19.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap19/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap19/section01/))

Chapter 20

- Section 20.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap20/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap20/section01/))

Chapter 21

- Section 21.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap21/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap21/section01/))

Chapter 22

- Section 22.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap22/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap22/section01/))

Chapter 23

- Section 23.1 ([Documentation](/ReasBook-private/docs/Books/LinearRepresentations_Serre_1977/Chapters/Chap23/section01.html)) ([Verso](/ReasBook-private/books/linearrepresentations_serre_1977/chapters/chap23/section01/))

-/

/-!
# LinearRepresentations_Serre_1977

Auto-managed aggregation root for `LinearRepresentations_Serre_1977`.
Keep project mathematics in `Chapters/` and let the orchestrator manage
the import block above.
-/
