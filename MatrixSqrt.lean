import Mathlib.Analysis.Matrix.Order

open scoped ComplexConjugate ComplexOrder Matrix MatrixOrder

namespace RomanianProblem.MatrixSqrt

abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

theorem posDef_sqrt_identities {n : ℕ} (K : CMat n) (hK : K.PosDef) :
    let Si : CMat n := CFC.sqrt K
    let S : CMat n := Si⁻¹
    Si * Si = K ∧ S * Si = 1 ∧ Si * S = 1 ∧ Siᴴ = Si ∧ Sᴴ = S := by
  classical
  dsimp
  have hSi : IsUnit (CFC.sqrt K) :=
    (CFC.isUnit_sqrt_iff K hK.posSemidef.nonneg).2 hK.isUnit
  have hsq : CFC.sqrt K * CFC.sqrt K = K := by
    simpa [pow_two] using CFC.sq_sqrt K hK.posSemidef.nonneg
  have hherm : (CFC.sqrt K)ᴴ = CFC.sqrt K :=
    (CFC.sqrt_nonneg K).isSelfAdjoint
  have hdet : IsUnit (CFC.sqrt K).det :=
    (Matrix.isUnit_iff_isUnit_det (CFC.sqrt K)).mp hSi
  refine ⟨hsq, ?_, ?_, hherm, ?_⟩
  · exact Matrix.nonsing_inv_mul _ hdet
  · exact Matrix.mul_nonsing_inv _ hdet
  · exact ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K)).isHermitian.inv)

end RomanianProblem.MatrixSqrt
