import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 200000

noncomputable section

open scoped BigOperators ComplexConjugate Matrix
open Finset

namespace RomanianProblem.CauchyDeterminant

abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def InUnitDisk {n : ℕ} (z : Fin n → ℂ) : Prop := ∀ i, ‖z i‖ < 1

def vandermondeSq {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ‖(Matrix.vandermonde z).det‖ ^ 2

def boundaryProduct {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, ‖1 - z i * conj (z j)‖

def kernelMatrix {n : ℕ} (z : Fin n → ℂ) : CMat n :=
  fun i j => (1 - z i * conj (z j))⁻¹

theorem kernel_denom_ne_zero
    {n : ℕ} (z : Fin n → ℂ) (hz : InUnitDisk z) (i j : Fin n) :
    1 - z i * conj (z j) ≠ 0 := by
  intro h
  have hprod : z i * conj (z j) = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖z i‖ * ‖z j‖ = 1 := by
    have h' := congrArg norm hprod
    simpa [norm_mul] using h'
  have hprod_lt : ‖z i‖ * ‖z j‖ < 1 := by
    rcases (norm_nonneg (z j)).eq_or_lt with hj0 | hj0
    · simp [← hj0]
    · calc
        ‖z i‖ * ‖z j‖ < 1 * ‖z j‖ := mul_lt_mul_of_pos_right (hz i) hj0
        _ < 1 * 1 := mul_lt_mul_of_pos_left (hz j) (by norm_num)
        _ = 1 := by norm_num
  exact (ne_of_lt hprod_lt) hnorm

open Polynomial

def lagrangeNumerator {n : ℕ} (y : Fin n → ℂ) (j : Fin n) : ℂ[X] :=
  ∏ k ∈ Finset.univ.erase j, (X - C (y k))

def coefficientMatrix {n : ℕ} (p : Fin n → ℂ[X]) : CMat n :=
  fun k j => (p j).coeff k

def evaluationMatrix {n : ℕ} (y : Fin n → ℂ) (p : Fin n → ℂ[X]) : CMat n :=
  fun i j => (p j).eval (y i)

theorem evaluationMatrix_eq_vandermonde_mul_coefficientMatrix
    {n : ℕ} (y : Fin n → ℂ) (p : Fin n → ℂ[X])
    (hdeg : ∀ j, (p j).natDegree < n) :
    evaluationMatrix y p = Matrix.vandermonde y * coefficientMatrix p := by
  apply Matrix.ext
  intro i j
  change (p j).eval (y i) = ∑ k : Fin n, y i ^ (k : ℕ) * (p j).coeff k
  rw [eval, eval₂_eq_sum]
  have hsupp : (p j).support ⊆ Finset.range n :=
    Polynomial.supp_subset_range (hdeg j)
  rw [sum_eq_of_subset _ (fun k => zero_mul ((y i) ^ k)) hsupp,
    ← Fin.sum_univ_eq_sum_range]
  congr 1
  ext k
  simp [mul_comm]

theorem lagrangeNumerator_natDegree_lt
    {n : ℕ} (y : Fin n → ℂ) (j : Fin n) :
    (lagrangeNumerator y j).natDegree < n := by
  unfold lagrangeNumerator
  calc
    (∏ k ∈ Finset.univ.erase j, (X - C (y k))).natDegree
        ≤ ∑ k ∈ Finset.univ.erase j, (X - C (y k)).natDegree :=
      Polynomial.natDegree_prod_le (Finset.univ.erase j) (fun k => X - C (y k))
    _ = (Finset.univ.erase j).card := by simp
    _ = n - 1 := by simp
    _ < n := Nat.sub_lt (Fin.pos_iff_nonempty.mpr ⟨j⟩) (by decide)

theorem lagrangeNumerator_eval
    {n : ℕ} (y : Fin n → ℂ) (i j : Fin n) :
    (lagrangeNumerator y j).eval (y i) =
      if i = j then ∏ k ∈ Finset.univ.erase j, (y j - y k) else 0 := by
  classical
  by_cases hij : i = j
  · subst i
    unfold lagrangeNumerator
    rw [Polynomial.eval_prod]
    rw [ite_eq_left rfl]
    apply Finset.prod_congr rfl
    intro k hk
    simp
  · have hi : i ∈ Finset.univ.erase j := by simp [hij]
    unfold lagrangeNumerator
    rw [Polynomial.eval_prod]
    simp only [hij, ↓reduceIte]
    apply Finset.prod_eq_zero hi
    simp

def lagrangeDiagonal {n : ℕ} (y : Fin n → ℂ) (i : Fin n) : ℂ :=
  ∏ k ∈ Finset.univ.erase i, (y i - y k)

theorem evaluationMatrix_lagrangeNumerator
    {n : ℕ} (y : Fin n → ℂ) :
    evaluationMatrix y (lagrangeNumerator y) = Matrix.diagonal (lagrangeDiagonal y) := by
  ext i j
  by_cases hij : i = j
  · subst i
    simp [evaluationMatrix, lagrangeNumerator_eval, lagrangeDiagonal, Matrix.diagonal]
  · simp [evaluationMatrix, lagrangeNumerator_eval, lagrangeDiagonal, Matrix.diagonal, hij]

theorem det_vandermonde_mul_det_coefficientMatrix_lagrange
    {n : ℕ} (y : Fin n → ℂ) :
    (Matrix.vandermonde y).det *
        (coefficientMatrix (lagrangeNumerator y)).det =
      ∏ i : Fin n, lagrangeDiagonal y i := by
  calc
    (Matrix.vandermonde y).det *
          (coefficientMatrix (lagrangeNumerator y)).det =
        (evaluationMatrix y (lagrangeNumerator y)).det := by
      rw [evaluationMatrix_eq_vandermonde_mul_coefficientMatrix y
        (lagrangeNumerator y) (lagrangeNumerator_natDegree_lt y), Matrix.det_mul]
    _ = (Matrix.diagonal (lagrangeDiagonal y)).det := by
      rw [evaluationMatrix_lagrangeNumerator]
    _ = ∏ i : Fin n, lagrangeDiagonal y i := Matrix.det_diagonal

theorem prod_Iio_norm_sub_eq_prod_Ioi_norm_sub
    {n : ℕ} (y : Fin n → ℂ) :
    (∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖y i - y j‖) =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖y j - y i‖ := by
  rw [Finset.prod_sigma', Finset.prod_sigma']
  refine Finset.prod_bij' (fun p _ => ⟨p.2, p.1⟩) (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro ⟨i, j⟩ hij
    simpa only [Finset.mem_sigma, Finset.mem_univ, true_and,
      Finset.mem_Iio, Finset.mem_Ioi] using hij
  · intro ⟨i, j⟩ hij
    simpa only [Finset.mem_sigma, Finset.mem_univ, true_and,
      Finset.mem_Ioi, Finset.mem_Iio] using hij
  · intro ⟨i, j⟩ _
    rfl
  · intro ⟨i, j⟩ _
    simp
  · intro ⟨i, j⟩ _
    simp

theorem norm_prod_lagrangeDiagonal
    {n : ℕ} (y : Fin n → ℂ) :
    ‖∏ i : Fin n, lagrangeDiagonal y i‖ =
      ‖(Matrix.vandermonde y).det‖ ^ 2 := by
  rw [Matrix.det_vandermonde]
  simp_rw [lagrangeDiagonal, norm_prod]
  have herase (i : Fin n) :
      Finset.univ.erase i = Finset.Iio i ∪ Finset.Ioi i := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
      Finset.mem_Iio, Finset.mem_Ioi]
    constructor
    · exact lt_or_gt_of_ne
    · intro h
      exact h.elim ne_of_lt (fun hlt => ne_of_gt hlt)
  have hdisj (i : Fin n) : Disjoint (Finset.Iio i) (Finset.Ioi i) := by
    refine Finset.disjoint_left.mpr ?_
    intro j hji hij
    exact (Finset.mem_Iio.mp hji).asymm (Finset.mem_Ioi.mp hij)
  simp_rw [herase]
  simp_rw [Finset.prod_union (hdisj _)]
  rw [Finset.prod_mul_distrib, prod_Iio_norm_sub_eq_prod_Ioi_norm_sub]
  simp_rw [norm_sub_rev]
  rw [← pow_two]

theorem norm_det_coefficientMatrix_lagrange
    {n : ℕ} (y : Fin n → ℂ) (hinj : Function.Injective y) :
    ‖(coefficientMatrix (lagrangeNumerator y)).det‖ =
      ‖(Matrix.vandermonde y).det‖ := by
  have hdet : (Matrix.vandermonde y).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have h := congrArg norm (det_vandermonde_mul_det_coefficientMatrix_lagrange y)
  rw [norm_mul, norm_prod_lagrangeDiagonal, pow_two] at h
  exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hdet) h

def unitNumerator {n : ℕ} (y : Fin n → ℂ) (j : Fin n) : ℂ[X] :=
  ∏ k ∈ Finset.univ.erase j, (1 - C (y k) * X)

theorem reverse_X_sub_C (a : ℂ) :
    (X - C a).reverse = 1 - C a * X := by
  rw [show X - C a = X + C (-a) by simp [sub_eq_add_neg]]
  rw [Polynomial.reverse_add_C]
  have hX : (X : ℂ[X]).reverse = 1 := by
    rw [show (X : ℂ[X]) = X * 1 by simp, Polynomial.reverse_X_mul]
    simpa only [← Polynomial.C_1] using Polynomial.reverse_C (1 : ℂ)
  rw [hX]
  simp [sub_eq_add_neg]

theorem reverse_prod_X_sub_C {n : ℕ} (s : Finset (Fin n)) (y : Fin n → ℂ) :
    (∏ k ∈ s, (X - C (y k))).reverse =
      ∏ k ∈ s, (1 - C (y k) * X) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, ← Polynomial.C_1] using
      Polynomial.reverse_C (1 : ℂ)
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Polynomial.reverse_mul_of_domain, ih,
        reverse_X_sub_C, Finset.prod_insert ha]

theorem reverse_lagrangeNumerator
    {n : ℕ} (y : Fin n → ℂ) (j : Fin n) :
    (lagrangeNumerator y j).reverse = unitNumerator y j := by
  exact reverse_prod_X_sub_C (Finset.univ.erase j) y

theorem lagrangeNumerator_natDegree
    {n : ℕ} (y : Fin n → ℂ) (j : Fin n) :
    (lagrangeNumerator y j).natDegree = n - 1 := by
  unfold lagrangeNumerator
  rw [Polynomial.natDegree_prod_of_monic]
  · simp
  · intro i hi
    exact (Polynomial.monic_X_sub_C (y i))

theorem coefficientMatrix_unit_eq_reversed_lagrange
    {n : ℕ} (y : Fin n → ℂ) :
    coefficientMatrix (unitNumerator y) =
      (coefficientMatrix (lagrangeNumerator y)).submatrix Fin.revPerm id := by
  ext k j
  change (unitNumerator y j).coeff k =
    (lagrangeNumerator y j).coeff (Fin.revPerm k)
  rw [← reverse_lagrangeNumerator]
  rw [Polynomial.coeff_reverse, lagrangeNumerator_natDegree]
  have hk : (k : ℕ) ≤ n - 1 := by simpa using Nat.le_pred_of_lt k.isLt
  rw [Polynomial.revAt_le (N := n - 1) hk]
  simp [Fin.revPerm_apply, Fin.val_rev, Nat.sub_sub, Nat.add_comm]

theorem norm_det_coefficientMatrix_unit
    {n : ℕ} (y : Fin n → ℂ) (hinj : Function.Injective y) :
    ‖(coefficientMatrix (unitNumerator y)).det‖ =
      ‖(Matrix.vandermonde y).det‖ := by
  rw [coefficientMatrix_unit_eq_reversed_lagrange]
  rw [Matrix.det_permute]
  have hs : (((Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤˣ) : ℤ) = 1) ∨
      (((Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤˣ) : ℤ) = -1) :=
    Int.isUnit_eq_one_or (Units.isUnit _)
  rcases hs with hs | hs
  · simp [hs, norm_det_coefficientMatrix_lagrange y hinj]
  · simp [hs, norm_det_coefficientMatrix_lagrange y hinj]

def rowDenominator {n : ℕ} (z : Fin n → ℂ) (i : Fin n) : ℂ :=
  ∏ j : Fin n, (1 - z i * conj (z j))

def clearedKernel {n : ℕ} (z : Fin n → ℂ) : CMat n :=
  evaluationMatrix z (unitNumerator (fun j => conj (z j)))

theorem clearedKernel_apply
    {n : ℕ} (z : Fin n → ℂ) (i j : Fin n) :
    clearedKernel z i j =
      ∏ k ∈ Finset.univ.erase j, (1 - z i * conj (z k)) := by
  unfold clearedKernel evaluationMatrix unitNumerator
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro k hk
  simp
  ring

theorem clearedKernel_eq_diagonal_mul_kernelMatrix
    {n : ℕ} (z : Fin n → ℂ) (hz : InUnitDisk z) :
    clearedKernel z = Matrix.diagonal (rowDenominator z) * kernelMatrix z := by
  ext i j
  rw [clearedKernel_apply]
  simp only [Matrix.mul_apply, Matrix.diagonal, kernelMatrix]
  simp
  unfold rowDenominator
  rw [← Finset.prod_erase_mul Finset.univ
    (fun k => 1 - z i * conj (z k)) (Finset.mem_univ j)]
  field_simp [kernel_denom_ne_zero z hz i j]

theorem det_clearedKernel
    {n : ℕ} (z : Fin n → ℂ) (hz : InUnitDisk z) :
    (clearedKernel z).det =
      (∏ i : Fin n, rowDenominator z i) * (kernelMatrix z).det := by
  rw [clearedKernel_eq_diagonal_mul_kernelMatrix z hz, Matrix.det_mul,
    Matrix.det_diagonal]

theorem norm_prod_rowDenominator_eq_boundaryProduct
    {n : ℕ} (z : Fin n → ℂ) :
    ‖∏ i : Fin n, rowDenominator z i‖ = boundaryProduct z := by
  simp [rowDenominator, boundaryProduct, norm_prod]

theorem norm_det_clearedKernel_eq_kernel_boundary
    {n : ℕ} (z : Fin n → ℂ) (hz : InUnitDisk z) :
    ‖(clearedKernel z).det‖ = ‖(kernelMatrix z).det‖ * boundaryProduct z := by
  rw [det_clearedKernel z hz, norm_mul,
    norm_prod_rowDenominator_eq_boundaryProduct]
  ring

theorem unitNumerator_natDegree_lt
    {n : ℕ} (y : Fin n → ℂ) (j : Fin n) :
    (unitNumerator y j).natDegree < n := by
  unfold unitNumerator
  calc
    (∏ k ∈ Finset.univ.erase j, (1 - C (y k) * X)).natDegree
        ≤ ∑ k ∈ Finset.univ.erase j, (1 - C (y k) * X).natDegree :=
      Polynomial.natDegree_prod_le (Finset.univ.erase j)
        (fun k => 1 - C (y k) * X)
    _ ≤ ∑ _k ∈ Finset.univ.erase j, 1 := by
      apply Finset.sum_le_sum
      intro k hk
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · simp
      · calc
          (C (y k) * X).natDegree ≤ (C (y k)).natDegree + X.natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ 1 := by simp
    _ = n - 1 := by simp
    _ < n := Nat.sub_lt (Fin.pos_iff_nonempty.mpr ⟨j⟩) (by decide)

theorem conj_comp_injective
    {n : ℕ} (z : Fin n → ℂ) (hinj : Function.Injective z) :
    Function.Injective (fun j => conj (z j)) := by
  intro i j h
  apply hinj
  have h' := congrArg conj h
  simpa using h'

theorem norm_det_vandermonde_conj
    {n : ℕ} (z : Fin n → ℂ) :
    ‖(Matrix.vandermonde (fun j => conj (z j))).det‖ =
      ‖(Matrix.vandermonde z).det‖ := by
  rw [Matrix.det_vandermonde, Matrix.det_vandermonde]
  simp_rw [norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  simpa only [map_sub] using Complex.norm_conj (z j - z i)

theorem norm_det_clearedKernel_eq_vandermondeSq
    {n : ℕ} (z : Fin n → ℂ) (hinj : Function.Injective z) :
    ‖(clearedKernel z).det‖ = vandermondeSq z := by
  rw [clearedKernel,
    evaluationMatrix_eq_vandermonde_mul_coefficientMatrix z
      (unitNumerator (fun j => conj (z j)))
      (unitNumerator_natDegree_lt (fun j => conj (z j))),
    Matrix.det_mul, norm_mul,
    norm_det_coefficientMatrix_unit (fun j => conj (z j))
      (conj_comp_injective z hinj)]
  rw [norm_det_vandermonde_conj]
  unfold vandermondeSq
  rw [pow_two]

theorem cauchy_kernel_det_identity
    {n : ℕ} (z : Fin n → ℂ)
    (hz : InUnitDisk z)
    (hinj : Function.Injective z) :
    ‖(kernelMatrix z).det‖ * boundaryProduct z = vandermondeSq z := by
  rw [← norm_det_clearedKernel_eq_kernel_boundary z hz]
  exact norm_det_clearedKernel_eq_vandermondeSq z hinj

end RomanianProblem.CauchyDeterminant
