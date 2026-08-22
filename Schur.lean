import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Matrix

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace RomanianProblem.Schur

def IsUpperTriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i j, j < i → A i j = 0

def IsUnitary {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  U * Uᴴ = 1 ∧ Uᴴ * U = 1

def tailBlock {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => A i.succ j.succ

def blockDiagOne {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun i => Fin.cases 0 (fun j => W i j) j) i

theorem blockDiagOne_conjTranspose {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) :
    (blockDiagOne W)ᴴ = blockDiagOne Wᴴ := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp [blockDiagOne]

theorem blockDiagOne_mul {n : ℕ} (W₁ W₂ : Matrix (Fin n) (Fin n) ℂ) :
    blockDiagOne W₁ * blockDiagOne W₂ = blockDiagOne (W₁ * W₂) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [blockDiagOne, Matrix.mul_apply, Fin.sum_univ_succ]

theorem blockDiagOne_unitary {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ)
    (hW₁ : W * Wᴴ = 1) (hW₂ : Wᴴ * W = 1) :
    blockDiagOne W * (blockDiagOne W)ᴴ = 1 ∧
      (blockDiagOne W)ᴴ * blockDiagOne W = 1 := by
  rw [blockDiagOne_conjTranspose, blockDiagOne_mul, blockDiagOne_mul, hW₁, hW₂]
  constructor <;> ext i j <;>
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp [blockDiagOne, Matrix.one_apply, ne_comm]

theorem tailBlock_blockDiag_mul {n : ℕ} (W₁ W₂ : Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    tailBlock (blockDiagOne W₁ * A * blockDiagOne W₂) =
      W₁ * tailBlock A * W₂ := by
  ext i j
  simp [tailBlock, blockDiagOne, Matrix.mul_apply, Fin.sum_univ_succ]

theorem blockDiag_conjugate_firstColumn {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hcol : ∀ i : Fin n, A i.succ 0 = 0) :
    ∀ i : Fin n,
      (blockDiagOne Wᴴ * A * blockDiagOne W) i.succ 0 = 0 := by
  intro i
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, blockDiagOne]
  simp [hcol]

theorem isUpperTriangular_of_firstColumn_tail {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hcol : ∀ i : Fin n, A i.succ 0 = 0)
    (htail : IsUpperTriangular (tailBlock A)) :
    IsUpperTriangular A := by
  intro i j hji
  by_cases hi : i = 0
  · subst i
    exact (Fin.not_lt_zero j hji).elim
  by_cases hj : j = 0
  · subst j
    simpa [Fin.succ_pred i hi] using hcol (i.pred hi)
  have hp : j.pred hj < i.pred hi := by
    rw [← Fin.succ_lt_succ_iff]
    simpa [Fin.succ_pred i hi, Fin.succ_pred j hj] using hji
  simpa [tailBlock, Fin.succ_pred i hi, Fin.succ_pred j hj] using
    htail (i.pred hi) (j.pred hj) hp

theorem exists_eigen_orthonormalBasis {n : ℕ}
    (f : Module.End ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    ∃ (μ : ℂ) (b : OrthonormalBasis (Fin (n + 1)) ℂ
        (EuclideanSpace ℂ (Fin (n + 1)))),
      f (b 0) = μ • b 0 ∧
      ∀ i, LinearMap.toMatrix b.toBasis b.toBasis f i 0 = if i = 0 then μ else 0 := by
  classical
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  let x : EuclideanSpace ℂ (Fin (n + 1)) := ((‖v‖ : ℂ)⁻¹) • v
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv.2
  have hxnorm : ‖x‖ = 1 := by
    simp [x, norm_smul, hvnorm]
  have hxEig : f x = μ • x := by
    dsimp only [x]
    rw [map_smul, hv.apply_eq_smul]
    simp [smul_smul, mul_comm]
  let seed : Fin (n + 1) → EuclideanSpace ℂ (Fin (n + 1)) :=
    Fin.cases x (fun _ => 0)
  have hseed0 : seed 0 = x := rfl
  have horth : Orthonormal ℂ (({0} : Set (Fin (n + 1))).domRestrict seed) := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [Set.domRestrict_apply]
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst i
    subst j
    simp [seed, hxnorm]
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin (n + 1))) =
      Fintype.card (Fin (n + 1)) := by
    simp
  obtain ⟨b, hb⟩ :=
    horth.exists_orthonormalBasis_extension_of_card_eq hcard
  have hb0 : b 0 = x := by
    simpa [seed] using hb 0 (by simp)
  refine ⟨μ, b, ?_, ?_⟩
  · simpa [hb0] using hxEig
  · intro i
    rw [LinearMap.toMatrix_apply]
    change b.repr (f (b 0)) i = if i = 0 then μ else 0
    rw [hb0, hxEig, map_smul]
    simp only [PiLp.smul_apply]
    rw [OrthonormalBasis.repr_apply_apply, ← hb0,
      orthonormal_iff_ite.mp b.orthonormal]
    split <;> simp_all

theorem exists_unitary_schur : ∀ n : ℕ, ∀ T : Matrix (Fin n) (Fin n) ℂ,
    ∃ (U R : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℂ),
      IsUnitary U ∧ IsUpperTriangular R ∧
        (∀ i, R i i = lam i) ∧ T = U * R * Uᴴ := by
  intro n
  induction n with
  | zero =>
      intro T
      refine ⟨1, T, fun i => Fin.elim0 i, ?_, ?_, ?_, ?_⟩
      · constructor <;> simp
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · simp
  | succ n ih =>
      intro T
      classical
      let e : OrthonormalBasis (Fin (n + 1)) ℂ
          (EuclideanSpace ℂ (Fin (n + 1))) := EuclideanSpace.basisFun (Fin (n + 1)) ℂ
      let f : Module.End ℂ (EuclideanSpace ℂ (Fin (n + 1))) :=
        Matrix.toLin e.toBasis e.toBasis T
      obtain ⟨μ, b, heig, hBcol⟩ := exists_eigen_orthonormalBasis f
      let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := e.toBasis.toMatrix b
      let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
        LinearMap.toMatrix b.toBasis b.toBasis f
      have hQ₁ : Q * Qᴴ = 1 := by
        exact e.toMatrix_orthonormalBasis_self_mul_conjTranspose b
      have hQ₂ : Qᴴ * Q = 1 := by
        exact e.toMatrix_orthonormalBasis_conjTranspose_mul_self b
      have hQstar : Qᴴ = b.toBasis.toMatrix e := by
        calc
          Qᴴ = Qᴴ * 1 := by simp
          _ = Qᴴ * (Q * b.toBasis.toMatrix e) := by
            congr 1
            exact (e.toBasis.toMatrix_mul_toMatrix_flip b.toBasis).symm
          _ = (Qᴴ * Q) * b.toBasis.toMatrix e := by rw [Matrix.mul_assoc]
          _ = b.toBasis.toMatrix e := by rw [hQ₂, Matrix.one_mul]
      have hTQB : T = Q * B * Qᴴ := by
        rw [hQstar]
        symm
        simpa [Q, B, f] using
          (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
            (f := f) e.toBasis b.toBasis e.toBasis b.toBasis)
      let C : Matrix (Fin n) (Fin n) ℂ := tailBlock B
      obtain ⟨W, Rtail, lamtail, hW, hRtail, hdiagTail, hC⟩ := ih C
      let D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := blockDiagOne W
      let R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Dᴴ * B * D
      let U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Q * D
      let lam : Fin (n + 1) → ℂ := fun i => R i i
      have hD : IsUnitary D := by
        exact blockDiagOne_unitary W hW.1 hW.2
      have htailR : tailBlock R = Rtail := by
        dsimp only [R, D]
        rw [blockDiagOne_conjTranspose]
        rw [tailBlock_blockDiag_mul]
        dsimp only [C] at hC
        rw [hC]
        calc
          Wᴴ * (W * Rtail * Wᴴ) * W =
              (Wᴴ * W) * Rtail * (Wᴴ * W) := by ac_rfl
          _ = Rtail := by rw [hW.2]; simp
      have hfirstR : ∀ i : Fin n, R i.succ 0 = 0 := by
        dsimp only [R, D]
        rw [blockDiagOne_conjTranspose]
        apply blockDiag_conjugate_firstColumn W B
        intro i
        simpa [B] using hBcol i.succ
      have hR : IsUpperTriangular R := by
        apply isUpperTriangular_of_firstColumn_tail R hfirstR
        rw [htailR]
        exact hRtail
      have hU : IsUnitary U := by
        constructor
        · simp only [U, Matrix.conjTranspose_mul]
          calc
            Q * D * (Dᴴ * Qᴴ) = Q * (D * Dᴴ) * Qᴴ := by ac_rfl
            _ = 1 := by rw [hD.1, Matrix.mul_one, hQ₁]
        · simp only [U, Matrix.conjTranspose_mul]
          calc
            Dᴴ * Qᴴ * (Q * D) = Dᴴ * (Qᴴ * Q) * D := by ac_rfl
            _ = 1 := by rw [hQ₂, Matrix.mul_one, hD.2]
      have hrecover : T = U * R * Uᴴ := by
        rw [hTQB]
        simp only [U, R, Matrix.conjTranspose_mul]
        calc
          Q * B * Qᴴ = Q * (D * Dᴴ) * B * (D * Dᴴ) * Qᴴ := by
            rw [hD.1]
            simp
          _ = Q * D * (Dᴴ * B * D) * (Dᴴ * Qᴴ) := by ac_rfl
      exact ⟨U, R, lam, hU, hR, fun i => rfl, hrecover⟩

end RomanianProblem.Schur
