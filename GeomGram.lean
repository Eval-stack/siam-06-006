import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 200000

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace RomanianProblem.GeomGram

abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def InUnitDisk {n : ℕ} (z : Fin n → ℂ) : Prop := ∀ i, ‖z i‖ < 1

def kernelMatrix {n : ℕ} (z : Fin n → ℂ) : CMat n :=
  fun i j => (1 - z i * conj (z j))⁻¹

def geomGram {n : ℕ} (z : Fin n → ℂ) : CMat n :=
  fun i j => ∑ k : Fin n, (z i * conj (z j)) ^ (k : ℕ)

def powerDiag {n : ℕ} (z : Fin n → ℂ) : CMat n :=
  Matrix.diagonal (fun i => z i ^ n)

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

theorem geomGram_eq_kernel_sub
    {n : ℕ} (z : Fin n → ℂ) (hz : InUnitDisk z) :
    geomGram z =
      kernelMatrix z - powerDiag z * kernelMatrix z * (powerDiag z)ᴴ := by
  classical
  ext i j
  let a : ℂ := z i * conj (z j)
  have hden : 1 - a ≠ 0 := by
    simpa [a] using kernel_denom_ne_zero z hz i j
  have hgeom :
      (∑ k ∈ Finset.range n, a ^ k) * (1 - a) = 1 - a ^ n := by
    simpa [mul_comm] using geom_sum_mul_neg a n
  change (∑ k : Fin n, a ^ (k : ℕ)) = _
  rw [Fin.sum_univ_eq_sum_range]
  simp [powerDiag, kernelMatrix]
  have hp : a ^ n = z i ^ n * conj (z j) ^ n := by
    simp [a, mul_pow]
  rw [show
    (1 - z i * conj (z j))⁻¹ -
        z i ^ n * (1 - z i * conj (z j))⁻¹ * conj (z j) ^ n =
      (1 - a ^ n) / (1 - a) by
        rw [div_eq_mul_inv, hp]
        simp only [a]
        ring]
  exact (eq_div_iff hden).2 hgeom

end RomanianProblem.GeomGram
