import Mathlib.Algebra.Homology.Homology
import Mathlib.CategoryTheory.Abelian.Basic

def SpectralSequencePageShape (r : ℕ): ComplexShape (ℤ×ℤ) where
  Rel i j := (j.1 = i.1 - r) ∧ (j.2 = i.2 + (Int.ofNat r - 1))
  next_eq hi hj := Prod.ext (hi.left.trans hj.left.symm) (hi.right.trans hj.right.symm)
  prev_eq hi hj := Prod.ext (add_right_cancel (hi.left.symm.trans hj.left)) (add_right_cancel (hi.right.symm.trans hj.right))

variable (V : _) [CategoryTheory.Category V] [CategoryTheory.Abelian V]

abbrev SpectralSequencePage (r : ℕ) := HomologicalComplex V (SpectralSequencePageShape r)

structure SpectralSequence where
  E (r : ℕ): SpectralSequencePage V r
  NextPage : (E (r + 1)).X = (E r).homology

#check CategoryTheory.Abelian
#check HomologicalComplex.homology