import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace RomanianProblem.Hadamard

theorem det_norm_le_prod_row_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ≤ ∏ i : Fin n, ‖WithLp.toLp 2 (fun j => A i j)‖ := by
  classical
  let row : Fin n → EuclideanSpace ℂ (Fin n) :=
    fun i => WithLp.toLp 2 (fun j => A i j)
  let e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) ℂ
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by
    simp
  let b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis hdim row
  have hstandard : e.toBasis.det row = A.det := by
    rw [e.toBasis.det_apply]
    change (A.transpose).det = A.det
    exact Matrix.det_transpose A
  have hchange : ‖e.toBasis.det row‖ = ‖b.toBasis.det row‖ := by
    rw [e.toBasis.det.eq_smul_basis_det b.toBasis]
    simp [e.det_to_matrix_orthonormalBasis b]
  have hgs : b.toBasis.det row = ∏ i, inner ℂ (b i) (row i) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det hdim row
  rw [← hstandard, hchange, hgs, norm_prod]
  apply Finset.prod_le_prod
  · intro i hi
    positivity
  · intro i hi
    simpa [b.orthonormal.1 i, row] using norm_inner_le_norm (𝕜 := ℂ) (b i) (row i)

theorem hadamard_det_sq_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ^ 2 ≤ ∏ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 := by
  have h := det_norm_le_prod_row_norm A
  have hsq : ‖A.det‖ ^ 2 ≤
      (∏ i : Fin n, ‖WithLp.toLp 2 (fun j => A i j)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [← Finset.prod_pow] at hsq
  simpa only [EuclideanSpace.norm_sq_eq, PiLp.toLp_apply] using hsq

theorem posSemidef_det_le_prod_diagonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) :
    ‖A.det‖ ≤ ∏ i : Fin n, RCLike.re (A i i) := by
  classical
  let B : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt A
  have hBsq : B ^ 2 = A := by
    exact CFC.sq_sqrt A hA.nonneg
  have hBherm : B.IsHermitian := by
    exact (CFC.sqrt_nonneg A).isSelfAdjoint
  have hrow (i : Fin n) :
      (∑ j : Fin n, ‖B i j‖ ^ 2) = RCLike.re (A i i) := by
    rw [← hBsq]
    simp only [pow_two, Matrix.mul_apply, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← hBherm.apply j i]
    simpa [Complex.mul_conj] using Complex.norm_mul_self_eq_normSq (B i j)
  have hdet : ‖A.det‖ = ‖B.det‖ ^ 2 := by
    rw [← hBsq]
    simp [pow_two, Matrix.det_mul]
  rw [hdet]
  simpa only [hrow] using hadamard_det_sq_le B

end RomanianProblem.Hadamard
