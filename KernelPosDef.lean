import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension
import RomanianProblem.CauchyDeterminant

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Matrix MatrixOrder Topology

namespace RomanianProblem.KernelPosDef

open Filter

abbrev InUnitDisk {n : ℕ} (z : Fin n → ℂ) : Prop :=
  ∀ i, ‖z i‖ < 1

def kernelMatrix {n : ℕ} (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (1 - z i * conj (z j))⁻¹

def partialGram {n : ℕ} (z : Fin n → ℂ) (m : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  let V : Matrix (Fin n) (Fin m) ℂ := fun i k => z i ^ (k : ℕ)
  V * Vᴴ

theorem partialGram_posSemidef {n : ℕ} (z : Fin n → ℂ) (m : ℕ) :
    (partialGram z m).PosSemidef := by
  classical
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem partialGram_apply {n : ℕ} (z : Fin n → ℂ) (m : ℕ)
    (i j : Fin n) :
    partialGram z m i j = ∑ k ∈ Finset.range m, (z i * conj (z j)) ^ k := by
  classical
  change (∑ k : Fin m, z i ^ (k : ℕ) * conj (z j ^ (k : ℕ))) = _
  calc
    _ = ∑ k ∈ Finset.range m, z i ^ k * conj (z j) ^ k := by
      simpa only [map_pow] using
        Fin.sum_univ_eq_sum_range (fun k => z i ^ k * conj (z j) ^ k) m
    _ = _ := by simp only [mul_pow]

theorem tendsto_partialGram {n : ℕ} (z : Fin n → ℂ) (hz : InUnitDisk z) :
    Tendsto (partialGram z) atTop (𝓝 (kernelMatrix z)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hnorm : ‖z i * conj (z j)‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg (z i), norm_nonneg (z j), hz i, hz j]
  simpa only [partialGram_apply, kernelMatrix] using
    (hasSum_geometric_of_norm_lt_one hnorm).tendsto_sum_nat

theorem kernel_posSemidef {n : ℕ} (z : Fin n → ℂ) (hz : InUnitDisk z) :
    (kernelMatrix z).PosSemidef := by
  classical
  exact Matrix.posSemidef_is_closed.mem_of_tendsto
    (tendsto_partialGram z hz) (Filter.Eventually.of_forall (partialGram_posSemidef z))

theorem kernel_posDef {n : ℕ} (z : Fin n → ℂ) (hz : InUnitDisk z)
    (hinj : Function.Injective z) :
    (kernelMatrix z).PosDef := by
  classical
  have hpsd := kernel_posSemidef z hz
  apply hpsd.posDef_iff_det_ne_zero.mpr
  intro hdet
  have hz' : RomanianProblem.CauchyDeterminant.InUnitDisk z := hz
  have hid := RomanianProblem.CauchyDeterminant.cauchy_kernel_det_identity z hz' hinj
  have hk : kernelMatrix z = RomanianProblem.CauchyDeterminant.kernelMatrix z := rfl
  rw [← hk, hdet, norm_zero, zero_mul] at hid
  have hvpos : 0 < RomanianProblem.CauchyDeterminant.vandermondeSq z := by
    unfold RomanianProblem.CauchyDeterminant.vandermondeSq
    exact sq_pos_of_pos (norm_pos_iff.mpr
      (Matrix.det_vandermonde_ne_zero_iff.mpr hinj))
  linarith

end RomanianProblem.KernelPosDef
