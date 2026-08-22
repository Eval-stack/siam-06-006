import Mathlib

open scoped BigOperators ComplexConjugate Matrix

namespace RomanianProblem.SpectralProduct

abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def IsUpperTriangular {n : ℕ} (R : CMat n) : Prop :=
  ∀ i j, j < i → R i j = 0

theorem prod_norm_sq_eq_of_charpoly_eq_diagonal
    {n : ℕ} (R : CMat n) (lam d : Fin n → ℂ)
    (htri : IsUpperTriangular R) (hdiag : ∀ i, R i i = lam i)
    (hchar : Matrix.charpoly R = Matrix.charpoly (Matrix.diagonal d)) :
    ∏ i, (1 - ‖lam i‖ ^ 2) = ∏ i, (1 - ‖d i‖ ^ 2) := by
  classical
  have hrootsR :
      (Matrix.charpoly R).roots = ((Finset.univ : Finset (Fin n)).1.map lam) := by
    rw [Matrix.charpoly_of_isUpperTriangular R htri]
    rw [Polynomial.roots_prod]
    · simp [hdiag]
    · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Polynomial.X_sub_C_ne_zero _
  have hrootsD :
      (Matrix.charpoly (Matrix.diagonal d)).roots =
        ((Finset.univ : Finset (Fin n)).1.map d) := by
    rw [Matrix.charpoly_diagonal]
    rw [Polynomial.roots_prod]
    · simp
    · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Polynomial.X_sub_C_ne_zero _
  have hm : ((Finset.univ : Finset (Fin n)).1.map lam) =
      ((Finset.univ : Finset (Fin n)).1.map d) := by
    rw [← hrootsR, ← hrootsD, hchar]
  have hp := congrArg
    (fun s : Multiset ℂ ↦ (s.map fun x ↦ 1 - ‖x‖ ^ 2).prod) hm
  simpa [List.prod_ofFn] using hp

end RomanianProblem.SpectralProduct
