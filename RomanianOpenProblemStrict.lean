/-
RomanianOpenProblemStrict.lean

Lean 4 + Mathlib candidate formalization of the proposed solution to the
Romanian-textbook extremal problem.

PURPOSE
-------
This file contains no proof-bypass declarations.  Every proposition below has
an ordinary Lean proof script.  Therefore Lean must either construct a proof
term for every theorem or stop at the first theorem whose script does not
succeed.

This is deliberately different from a proof outline: it is a strict
accept/reject target for Lean.

MATHEMATICAL OBJECTIVE FORMALIZED
--------------------------------
We formalize the multiplicative version

  F(z) =
    |det(V(z))|^2
      * ∏_{i,j} |1 - z_i * conjugate(z_j)|,

where V(z) is the n x n Vandermonde matrix.  This is exp(W) for the W used in
the proposed proof.  Maximizing W and maximizing F are equivalent on
configurations for which W is finite.

The proposed sharp radius is

  rho_n = ((n - 1)/(3n - 1))^(1/(2n)),

and the proposed maximizing configurations are centered regular n-gons of
that radius.

IMPORTANT
---------
I have not run the Lean executable on this file in the current environment.
The point of this version is that there is no trusted escape hatch: if a
Mathlib theorem name, a tactic step, or the mathematics is wrong, Lean rejects
the file rather than silently accepting the step.
-/

import Mathlib
import RomanianProblem.CauchyDeterminant
import RomanianProblem.GeomGram
import RomanianProblem.Hadamard
import RomanianProblem.InjectiveDensity
import RomanianProblem.KernelPosDef
import RomanianProblem.MatrixSqrt
import RomanianProblem.Schur
import RomanianProblem.SpectralProduct
import RomanianProblem.ScalarRow

set_option autoImplicit false
set_option maxHeartbeats 200000

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Matrix MatrixOrder Topology
open Filter

lemma sum_exp_mul_fin_eq_zero
    {n d : ℕ} (hn : 0 < n) (hd0 : 0 < d) (hdn : d < n) :
    ∑ k : Fin n,
      Complex.exp (2 * Real.pi * Complex.I * (d : ℂ) * (k : ℕ) / (n : ℂ)) = 0 := by
  let ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (d : ℂ) / (n : ℂ))
  have hξ1 : ξ ≠ 1 := by
    intro h
    have hdvd : n ∣ d :=
      (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hn.ne').mp (by
        simpa [ξ, mul_assoc] using h)
    exact (Nat.not_dvd_of_pos_of_lt hd0 hdn) hdvd
  have hgeom : ∑ k ∈ Finset.range n, ξ ^ k = 0 := by
    have hpow : ξ ^ n = 1 := by
      rw [← Complex.exp_nat_mul]
      rw [show (n : ℂ) * (2 * Real.pi * Complex.I * (d : ℂ) / (n : ℂ)) =
          2 * Real.pi * Complex.I * (d : ℂ) / (1 : ℂ) by
        field_simp [Nat.cast_ne_zero.mpr hn.ne']]
      simpa using
        ((Complex.exp_two_pi_mul_I_mul_div_eq_one_iff
          (k := d) (N := 1) one_ne_zero).mpr (one_dvd d))
    have h := geom_sum_mul_neg ξ n
    rw [hpow, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hξ1.symm)
  rw [← Fin.sum_univ_eq_sum_range (fun k => ξ ^ k) n] at hgeom
  calc
    ∑ k : Fin n,
        Complex.exp (2 * Real.pi * Complex.I * (d : ℂ) * (k : ℕ) / (n : ℂ)) =
        ∑ k : Fin n, ξ ^ (k : ℕ) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [← Complex.exp_nat_mul]
          congr 1
          ring
    _ = 0 := hgeom

noncomputable def fourierMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i k => Complex.exp
    (2 * Real.pi * Complex.I * (i : ℕ) * (k : ℕ) / (n : ℂ))

lemma fourierMatrix_mul_conjTranspose
    {n : ℕ} (hn : 0 < n) :
    fourierMatrix n * (fourierMatrix n).conjTranspose =
      (n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  classical
  have hexp_conj (x y : ℂ) :
      Complex.exp x * conj (Complex.exp y) =
        Complex.exp (x + conj y) := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
  have hstar_two : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    apply Complex.ext <;> norm_num
  have hconj_fourier (a b : ℕ) :
      conj (2 * Real.pi * Complex.I * (a : ℂ) * (b : ℂ) / (n : ℂ)) =
        -(2 * Real.pi * Complex.I * (a : ℂ) * (b : ℂ) / (n : ℂ)) := by
    simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I,
      map_natCast]
    rw [hstar_two]
    ring
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  by_cases hij : i = j
  · subst j
    rw [show ((n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) i i = (n : ℂ) by simp]
    simp only [fourierMatrix]
    have hterm : ∀ k : Fin n,
        Complex.exp (2 * Real.pi * Complex.I * (i : ℕ) * (k : ℕ) / (n : ℂ)) *
          star (Complex.exp
            (2 * Real.pi * Complex.I * (i : ℕ) * (k : ℕ) / (n : ℂ))) = 1 := by
      intro k
      change Complex.exp _ * conj (Complex.exp _) = 1
      rw [hexp_conj]
      rw [hconj_fourier (i : ℕ) (k : ℕ)]
      rw [← Complex.exp_zero]
      congr 1
      ring
    simp_rw [hterm]
    simp
  · have hij' : (i : ℕ) < (j : ℕ) ∨ (j : ℕ) < (i : ℕ) :=
      Nat.lt_or_gt_of_ne (fun h => hij (Fin.ext h))
    have hrhs : ((n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) i j = 0 := by
      simp [hij]
    rw [hrhs]
    rcases hij' with hijlt | hjilt
    · let d := (j : ℕ) - (i : ℕ)
      have hd0 : 0 < d := Nat.sub_pos_of_lt hijlt
      have hdn : d < n := lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
      have hs := sum_exp_mul_fin_eq_zero hn hd0 hdn
      have hsc : ∑ k : Fin n,
          starRingEnd ℂ
            (Complex.exp
              (2 * Real.pi * Complex.I * (d : ℂ) * (k : ℕ) / (n : ℂ))) = 0 := by
        rw [← map_sum, hs, map_zero]
      convert hsc using 1
      apply Finset.sum_congr rfl
      intro k _
      simp only [fourierMatrix]
      change Complex.exp _ * conj (Complex.exp _) = conj (Complex.exp _)
      rw [hexp_conj, ← Complex.exp_conj]
      congr 1
      rw [hconj_fourier (j : ℕ) (k : ℕ),
        hconj_fourier d (k : ℕ)]
      rw [Nat.cast_sub (Nat.le_of_lt hijlt)]
      ring
    · let d := (i : ℕ) - (j : ℕ)
      have hd0 : 0 < d := Nat.sub_pos_of_lt hjilt
      have hdn : d < n := lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
      have hs := sum_exp_mul_fin_eq_zero hn hd0 hdn
      convert hs using 1
      apply Finset.sum_congr rfl
      intro k _
      simp only [fourierMatrix]
      change Complex.exp _ * conj (Complex.exp _) = Complex.exp _
      rw [hexp_conj]
      congr 1
      rw [hconj_fourier (j : ℕ) (k : ℕ)]
      rw [Nat.cast_sub (Nat.le_of_lt hjilt)]
      ring

lemma primitive_root_fin_product
    {n : ℕ} (hn : 0 < n) {ω r : ℂ} (hω : IsPrimitiveRoot ω n) :
    ∏ j : Fin n, (1 - ω ^ (j : ℕ) * r) = 1 - r ^ n := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  let roots := Polynomial.nthRootsFinset n (1 : ℂ)
  let p : Fin n → roots := fun j =>
    ⟨ω ^ (j : ℕ), by
      apply (Polynomial.mem_nthRootsFinset hn (1 : ℂ)).2
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]⟩
  have hpbij : Function.Bijective p := by
    constructor
    · intro i j hij
      apply Fin.ext
      apply hω.pow_inj i.isLt j.isLt
      exact Subtype.ext_iff.mp hij
    · intro x
      have hxpow : (x : ℂ) ^ n = 1 :=
        (Polynomial.mem_nthRootsFinset hn (1 : ℂ)).1 x.property
      obtain ⟨m, hm, hmω⟩ := hω.eq_pow_of_pow_eq_one hxpow
      refine ⟨⟨m, hm⟩, ?_⟩
      exact Subtype.ext hmω
  have hreindex :
      (∏ j : Fin n, (1 - ω ^ (j : ℕ) * r)) =
        ∏ x : roots, (1 - (x : ℂ) * r) := by
    apply Fintype.prod_bijective p hpbij
    intro j
    rfl
  rw [hreindex]
  calc
    (∏ x : roots, (1 - (x : ℂ) * r)) =
        ∏ x ∈ roots, (1 - x * r) := by
          exact Finset.prod_coe_sort roots (fun x : ℂ => 1 - x * r)
    _ = 1 - r ^ n :=
      by simpa [roots] using
        (hω.pow_sub_pow_eq_prod_sub_mul (1 : ℂ) r hn).symm

namespace RomanianOpenProblemStrict

abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-! ### Basic definitions -/

def InUnitDisk {n : ℕ} (z : Fin n → ℂ) : Prop :=
  ∀ i, ‖z i‖ < 1

def vandermondeSq {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ‖(Matrix.vandermonde z).det‖ ^ 2

def boundaryProduct {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, ‖1 - z i * conj (z j)‖

def radialProduct {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∏ i : Fin n, (1 - ‖z i‖ ^ (2 * n))

def objective {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  vandermondeSq z * boundaryProduct z

def q (n : ℕ) : ℝ :=
  ((n : ℝ) - 1) / (3 * (n : ℝ) - 1)

def rho (n : ℕ) : ℝ :=
  Real.rpow (q n) (1 / (2 * (n : ℝ)))

def upperBound (n : ℕ) : ℝ :=
  (n : ℝ) ^ n
    * Real.rpow (q n) (((n : ℝ) - 1) / 2)
    * (1 - q n) ^ n

def regularAngle (n : ℕ) (θ : ℝ) (j : Fin n) : ℝ :=
  θ + 2 * Real.pi * (j : ℕ) / (n : ℝ)

def regularPoint (n : ℕ) (θ : ℝ) (j : Fin n) : ℂ :=
  (rho n : ℂ) *
    Complex.exp (Complex.I * (regularAngle n θ j : ℂ))

def IsRegularMaximizer {n : ℕ} (z : Fin n → ℂ) : Prop :=
  ∃ (θ : ℝ) (σ : Equiv.Perm (Fin n)),
    ∀ j, z (σ j) = regularPoint n θ j

/-! ### Elementary facts about q_n and rho_n -/

theorem q_pos {n : ℕ} (hn : 2 ≤ n) : 0 < q n := by
  unfold q
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnum : 0 < (n : ℝ) - 1 := by linarith
  have hden : 0 < 3 * (n : ℝ) - 1 := by linarith
  exact div_pos hnum hden

theorem q_lt_one {n : ℕ} (hn : 2 ≤ n) : q n < 1 := by
  unfold q
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < 3 * (n : ℝ) - 1 := by linarith
  rw [div_lt_one hden]
  linarith

theorem q_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ q n :=
  (q_pos hn).le

theorem rho_pos {n : ℕ} (hn : 2 ≤ n) : 0 < rho n := by
  unfold rho
  exact Real.rpow_pos_of_pos (q_pos hn) _

theorem rho_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ rho n :=
  (rho_pos hn).le

theorem rho_lt_one {n : ℕ} (hn : 2 ≤ n) : rho n < 1 := by
  unfold rho
  have hq0 : 0 < q n := q_pos hn
  have hq1 : q n < 1 := q_lt_one hn
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hexp : 0 < (1 / (2 * (n : ℝ)) : ℝ) := by positivity
  exact Real.rpow_lt_one hq0.le hq1 hexp

/-! ### Matrices in the first determinant argument -/

def kernelMatrix {n : ℕ} (z : Fin n → ℂ) : CMat n :=
  fun i j => (1 - z i * conj (z j))⁻¹

def geomGram {n : ℕ} (z : Fin n → ℂ) : CMat n :=
  fun i j => ∑ k : Fin n, (z i * conj (z j)) ^ (k : ℕ)

def powerDiag {n : ℕ} (z : Fin n → ℂ) : CMat n :=
  Matrix.diagonal (fun i => z i ^ n)

/-- `G = V Vᴴ`. -/
theorem geomGram_eq_vandermonde_gram
    {n : ℕ} (z : Fin n → ℂ) :
    geomGram z =
      Matrix.vandermonde z * (Matrix.vandermonde z)ᴴ := by
  classical
  ext i j
  simp [geomGram, Matrix.mul_apply, mul_pow]

/-- No denominator in the kernel vanishes for points in the open unit disk. -/
theorem kernel_denom_ne_zero
    {n : ℕ} (z : Fin n → ℂ) (hz : InUnitDisk z) (i j : Fin n) :
    1 - z i * conj (z j) ≠ 0 := by
  intro h
  have hprod : z i * conj (z j) = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖z i‖ * ‖z j‖ = 1 := by
    have := congrArg norm hprod
    simpa [norm_mul] using this
  have hi : ‖z i‖ < 1 := hz i
  have hj : ‖z j‖ < 1 := hz j
  have hnonneg : 0 ≤ ‖z i‖ := norm_nonneg _
  have hprod_lt : ‖z i‖ * ‖z j‖ < 1 := by
    rcases (norm_nonneg (z j)).eq_or_lt with hj0 | hj0
    · simp [← hj0]
    · calc
        ‖z i‖ * ‖z j‖ < 1 * ‖z j‖ := mul_lt_mul_of_pos_right hi hj0
        _ < 1 * 1 := mul_lt_mul_of_pos_left hj (by norm_num)
        _ = 1 := by norm_num
  exact (ne_of_lt hprod_lt) hnorm

/-- Pointwise geometric-series identity `G = K - Z K Zᴴ`. -/
theorem geomGram_eq_kernel_sub
    {n : ℕ} (z : Fin n → ℂ) (hz : InUnitDisk z) :
    geomGram z =
      kernelMatrix z -
        powerDiag z * kernelMatrix z * (powerDiag z)ᴴ := by
  have hz' : RomanianProblem.GeomGram.InUnitDisk z := hz
  change RomanianProblem.GeomGram.geomGram z =
    RomanianProblem.GeomGram.kernelMatrix z -
      RomanianProblem.GeomGram.powerDiag z *
        RomanianProblem.GeomGram.kernelMatrix z *
          (RomanianProblem.GeomGram.powerDiag z)ᴴ
  exact RomanianProblem.GeomGram.geomGram_eq_kernel_sub z hz'

/-!
The next lemma is the Cauchy determinant identity specialized to the
Szegő kernel.  Its conclusion is written without division so the zero cases
are explicit.
-/
theorem cauchy_kernel_det_identity
    {n : ℕ} (z : Fin n → ℂ)
    (hz : InUnitDisk z)
    (hinj : Function.Injective z) :
    ‖(kernelMatrix z).det‖ * boundaryProduct z = vandermondeSq z := by
  have hz' : RomanianProblem.CauchyDeterminant.InUnitDisk z := hz
  change ‖(RomanianProblem.CauchyDeterminant.kernelMatrix z).det‖ *
      RomanianProblem.CauchyDeterminant.boundaryProduct z =
        RomanianProblem.CauchyDeterminant.vandermondeSq z
  exact RomanianProblem.CauchyDeterminant.cauchy_kernel_det_identity z hz' hinj

/-!
A row-form Hadamard determinant inequality over C.

  |det A|^2 <= product_i sum_j |A_ij|^2.

The proof is the Gram-Schmidt/Hadamard volume argument.
-/
theorem hadamard_det_sq_le
    {n : ℕ} (A : CMat n) :
    ‖A.det‖ ^ 2 ≤
      ∏ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 := by
  exact RomanianProblem.Hadamard.hadamard_det_sq_le A

/-!
Strict-contraction eigenvalue determinant bound used in Step 1.

The eigenvalue data are given as an explicit unitary Schur form.  This keeps
the theorem itself elementary: once T = U R Uᴴ with R upper triangular and U
unitary, Hadamard on I-RRᴴ gives the product bound.
-/
def IsUnitary {n : ℕ} (U : CMat n) : Prop :=
  U * Uᴴ = 1 ∧ Uᴴ * U = 1

def IsUpperTriangular {n : ℕ} (R : CMat n) : Prop :=
  ∀ i j, j < i → R i j = 0

theorem schur_det_bound
    {n : ℕ} (T U R : CMat n) (lam : Fin n → ℂ)
    (hU : IsUnitary U)
    (htri : IsUpperTriangular R)
    (hdiag : ∀ i, R i i = lam i)
    (hT : T = U * R * Uᴴ)
    (hpos : (1 - T * Tᴴ).PosSemidef) :
    ‖(1 - T * Tᴴ).det‖ ≤
      ∏ i : Fin n, (1 - ‖lam i‖ ^ 2) := by
  classical
  have hconj :
      1 - T * Tᴴ = U * (1 - R * Rᴴ) * Uᴴ := by
    rcases hU with ⟨hUUh, hUhU⟩
    subst T
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      1 - U * R * Uᴴ * (U * (Rᴴ * Uᴴ)) =
          1 - U * (R * Rᴴ) * Uᴴ := by
            congr 1
            calc
              U * R * Uᴴ * (U * (Rᴴ * Uᴴ)) =
                  U * R * (Uᴴ * U) * (Rᴴ * Uᴴ) := by noncomm_ring
              _ = U * (R * Rᴴ) * Uᴴ := by rw [hUhU]; simp [Matrix.mul_assoc]
      _ = U * (1 - R * Rᴴ) * Uᴴ := by
            calc
              1 - U * (R * Rᴴ) * Uᴴ =
                  U * Uᴴ - U * (R * Rᴴ) * Uᴴ := by rw [hUUh]
              _ = U * (1 - R * Rᴴ) * Uᴴ := by noncomm_ring
  have hdet :
      ‖(1 - T * Tᴴ).det‖ = ‖(1 - R * Rᴴ).det‖ := by
    rw [hconj, Matrix.det_mul, Matrix.det_mul]
    have hdetU : ‖U.det‖ = 1 := by
      have hu := congrArg Matrix.det hU.1
      have hu' : ‖U.det‖ * ‖U.det‖ = 1 := by
        simpa [Matrix.det_mul] using congrArg norm hu
      nlinarith [norm_nonneg U.det]
    have hdetUh : ‖(Uᴴ).det‖ = 1 := by
      simpa using hdetU
    simp [norm_mul, hdetU, hdetUh]
  rw [hdet]
  have hposR : (1 - R * Rᴴ).PosSemidef := by
    rw [hconj] at hpos
    have hUunit : IsUnit U :=
      isUnit_iff_exists_inv.mpr ⟨Uᴴ, hU.1⟩
    exact (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hUunit).mp hpos
  have hhad :=
    RomanianProblem.Hadamard.posSemidef_det_le_prod_diagonal (1 - R * Rᴴ) hposR
  have hdiagR :
      ∀ i : Fin n,
        RCLike.re ((1 - R * Rᴴ) i i)
          ≤ 1 - ‖lam i‖ ^ 2 := by
    intro i
    have hsum :
        (R * Rᴴ) i i =
          ∑ j : Fin n, R i j * conj (R i j) := by
      simp [Matrix.mul_apply]
    simp only [Matrix.sub_apply, Matrix.one_apply, if_pos]
    rw [hsum]
    have hnonneg :
        0 ≤ ∑ j : Fin n, ‖R i j‖ ^ 2 := by positivity
    have hcontains :
        ‖lam i‖ ^ 2 ≤ ∑ j : Fin n, ‖R i j‖ ^ 2 := by
      rw [← hdiag i]
      exact Finset.single_le_sum
        (fun j _ => sq_nonneg ‖R i j‖)
        (Finset.mem_univ i)
    simp [Complex.mul_conj, Complex.sq_norm] at *
    linarith
  have hrhs_nonneg :
      0 ≤ ∏ i : Fin n, (1 - ‖lam i‖ ^ 2) := by
    -- Positivity of every factor follows from positivity of I-RRᴴ.
    apply Finset.prod_nonneg
    intro i hi
    have hii := hposR.diag_nonneg (i := i)
    have hii' : 0 ≤ RCLike.re ((1 - R * Rᴴ) i i) :=
      (Complex.nonneg_iff.mp hii).1
    have hle := hdiagR i
    linarith
  calc
    ‖(1 - R * Rᴴ).det‖
        ≤ ∏ i : Fin n, RCLike.re ((1 - R * Rᴴ) i i) := by
            simpa using hhad
    _ ≤ ∏ i : Fin n, (1 - ‖lam i‖ ^ 2) := by
      exact Finset.prod_le_prod
        (fun i _ => by
          have hii := hposR.diag_nonneg (i := i)
          exact (Complex.nonneg_iff.mp hii).1)
        (fun i _ => hdiagR i)

/-!
Existence of a unitary Schur form over C.
This is the standard finite-dimensional Schur triangularization theorem.
-/
theorem exists_unitary_schur
    {n : ℕ} (T : CMat n) :
    ∃ (U R : CMat n) (lam : Fin n → ℂ),
      IsUnitary U ∧
      IsUpperTriangular R ∧
      (∀ i, R i i = lam i) ∧
      T = U * R * Uᴴ := by
  change ∃ (U R : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℂ),
    RomanianProblem.Schur.IsUnitary U ∧
      RomanianProblem.Schur.IsUpperTriangular R ∧
      (∀ i, R i i = lam i) ∧ T = U * R * Uᴴ
  exact RomanianProblem.Schur.exists_unitary_schur n T

/-!
Step 1 core: B <= product_i (1-|z_i|^(2n)).
-/
theorem boundaryProduct_le_radialProduct_of_injective
    {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (hz : InUnitDisk z) (hinj : Function.Injective z) :
    boundaryProduct z ≤ radialProduct z := by
  classical
  exact (by
    let K : CMat n := kernelMatrix z
    let G : CMat n := geomGram z
    let Z : CMat n := powerDiag z

    have hGK : G = K - Z * K * Zᴴ := by
      simpa [K, G, Z] using geomGram_eq_kernel_sub z hz

    have hGgram :
        G = Matrix.vandermonde z * (Matrix.vandermonde z)ᴴ := by
      simpa [G] using geomGram_eq_vandermonde_gram z

    have hdetC :
        ‖K.det‖ * boundaryProduct z = vandermondeSq z := by
      simpa [K] using cauchy_kernel_det_identity z hz hinj

    have hKpos : K.PosDef := by
      have hz' : RomanianProblem.KernelPosDef.InUnitDisk z := hz
      change (RomanianProblem.KernelPosDef.kernelMatrix z).PosDef
      exact RomanianProblem.KernelPosDef.kernel_posDef z hz' hinj

    let Si : CMat n := CFC.sqrt K
    let S : CMat n := Si⁻¹
    let T : CMat n := S * Z * Si

    have hsqrt :
        Si * Si = K ∧ S * Si = 1 ∧ Si * S = 1 ∧ Siᴴ = Si ∧ Sᴴ = S := by
      simpa [Si, S] using
        RomanianProblem.MatrixSqrt.posDef_sqrt_identities K hKpos
    rcases hsqrt with ⟨hSiSq, hSSi, hSiS, hSiH, hSH⟩

    have hSinv :
        S * K * S = 1 := by
      rw [← hSiSq]
      simp [Matrix.mul_assoc, hSSi, hSiS]

    have hTT :
        1 - T * Tᴴ = S * G * S := by
      calc
        1 - T * Tᴴ = 1 - S * (Z * K * Zᴴ) * S := by
          unfold T
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSiH, hSH, ← hSiSq]
          noncomm_ring
        _ = S * (K - Z * K * Zᴴ) * S := by
          rw [Matrix.mul_sub, Matrix.sub_mul, hSinv]
        _ = S * G * S := by rw [hGK]

    have hposT : (1 - T * Tᴴ).PosSemidef := by
      rw [hTT]
      have hGpos : G.PosSemidef := by
        rw [hGgram]
        exact Matrix.posSemidef_self_mul_conjTranspose _
      have hcongr := hGpos.conjTranspose_mul_mul_same S
      rw [hSH] at hcongr
      exact hcongr

    obtain ⟨U, R, lam, hU, htri, hdiag, hschur⟩ :=
      exists_unitary_schur T

    have hsimilar :
        ∏ i : Fin n, (1 - ‖lam i‖ ^ 2) =
          ∏ i : Fin n, (1 - ‖z i‖ ^ (2 * n)) := by
      have hcharTZ : Matrix.charpoly T = Matrix.charpoly Z := by
        calc
          Matrix.charpoly T = Matrix.charpoly (S * (Z * Si)) := by
            simp [T, Matrix.mul_assoc]
          _ = Matrix.charpoly ((Z * Si) * S) :=
            Matrix.charpoly_mul_comm S (Z * Si)
          _ = Matrix.charpoly Z := by rw [Matrix.mul_assoc, hSiS, Matrix.mul_one]
      have hcharTR : Matrix.charpoly T = Matrix.charpoly R := by
        calc
          Matrix.charpoly T = Matrix.charpoly (U * (R * Uᴴ)) := by
            rw [hschur, Matrix.mul_assoc]
          _ = Matrix.charpoly ((R * Uᴴ) * U) :=
            Matrix.charpoly_mul_comm U (R * Uᴴ)
          _ = Matrix.charpoly R := by rw [Matrix.mul_assoc, hU.2, Matrix.mul_one]
      have hcharR :
          Matrix.charpoly R =
            Matrix.charpoly (Matrix.diagonal fun i : Fin n ↦ z i ^ n) := by
        rw [← hcharTR, hcharTZ]
        simp [Z, powerDiag]
      have hp :=
        RomanianProblem.SpectralProduct.prod_norm_sq_eq_of_charpoly_eq_diagonal
          R lam (fun i : Fin n ↦ z i ^ n) htri hdiag hcharR
      simpa [norm_pow, pow_mul, mul_comm] using hp

    have hBdet :
        boundaryProduct z = ‖(1 - T * Tᴴ).det‖ := by
      -- det(S G S)=det(G)/det(K), and det(G)=|det V|^2.
      have hdetG : ‖G.det‖ = vandermondeSq z := by
        rw [hGgram, Matrix.det_mul, Matrix.det_conjTranspose]
        simp [vandermondeSq, norm_mul, pow_two]
      have hdetKpos : 0 < ‖K.det‖ := by
        exact norm_pos_iff.mpr
          (hKpos.posSemidef.posDef_iff_det_ne_zero.mp hKpos)
      rw [hTT, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul]
      have hSdet :
          ‖S.det‖ ^ 2 = 1 / ‖K.det‖ := by
        have hd := congrArg Matrix.det hSinv
        have hdn := congrArg norm hd
        simp only [Matrix.det_mul, Matrix.det_one, norm_mul, norm_one] at hdn
        apply (eq_div_iff hdetKpos.ne').2
        calc
          ‖S.det‖ ^ 2 * ‖K.det‖ = ‖S.det‖ * ‖K.det‖ * ‖S.det‖ := by ring
          _ = 1 := hdn
      have hboundary : boundaryProduct z = ‖G.det‖ / ‖K.det‖ := by
        apply (eq_div_iff hdetKpos.ne').2
        calc
          boundaryProduct z * ‖K.det‖ = ‖K.det‖ * boundaryProduct z := by ring
          _ = vandermondeSq z := hdetC
          _ = ‖G.det‖ := hdetG.symm
      calc
        boundaryProduct z = ‖G.det‖ / ‖K.det‖ := hboundary
        _ = (1 / ‖K.det‖) * ‖G.det‖ := by ring
        _ = ‖S.det‖ ^ 2 * ‖G.det‖ := by rw [hSdet]
        _ = ‖S.det‖ * ‖G.det‖ * ‖S.det‖ := by ring

    rw [hBdet]
    calc
      ‖(1 - T * Tᴴ).det‖
          ≤ ∏ i : Fin n, (1 - ‖lam i‖ ^ 2) :=
            schur_det_bound T U R lam hU htri hdiag hschur hposT
      _ = radialProduct z := by
        simpa [radialProduct] using hsimilar
    )


theorem boundaryProduct_le_radialProduct
    {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (hz : InUnitDisk z) :
    boundaryProduct z ≤ radialProduct z := by
  classical
  let injSet : Set (Fin n → ℂ) :=
    {w | Function.Injective w ∧ InUnitDisk w}
  have hdense : z ∈ closure injSet := by
    have hz' : RomanianProblem.InjectiveDensity.InUnitDisk z := hz
    have hd :=
      RomanianProblem.InjectiveDensity.dense_injective_tuples_in_open_disk z hz'
    change z ∈ closure {w : Fin n → ℂ | Function.Injective w ∧ ∀ i, ‖w i‖ < 1} at hd
    exact hd
  have hcontB : Continuous (boundaryProduct : (Fin n → ℂ) → ℝ) := by
    unfold boundaryProduct
    fun_prop
  have hcontR : Continuous (radialProduct : (Fin n → ℂ) → ℝ) := by
    unfold radialProduct
    fun_prop
  have hclosed : IsClosed {w : Fin n → ℂ | boundaryProduct w ≤ radialProduct w} :=
    isClosed_le hcontB hcontR
  apply hclosed.closure_subset_iff.mpr _ hdense
  intro w hw
  exact boundaryProduct_le_radialProduct_of_injective hn w hw.2 hw.1

/-! ### Scalar inequality for the weighted Vandermonde step -/

def rowFactor (n : ℕ) (t : ℝ) : ℝ :=
  (1 - q n * t ^ n) * (∑ k ∈ Finset.range n, t ^ k)

theorem rowFactor_derivative_sign
    {n : ℕ} (hn : 2 ≤ n) :
    ∀ t : ℝ, 0 < t →
      ((t < 1 → deriv (rowFactor n) t > 0) ∧
       (1 < t → deriv (rowFactor n) t < 0)) := by
  intro t ht
  constructor
  · intro ht1
    change 0 < deriv (RomanianProblem.ScalarRow.rowFactor n) t
    exact RomanianProblem.ScalarRow.rowFactor_derivative_pos hn ht.le ht1
  · intro ht1
    change deriv (RomanianProblem.ScalarRow.rowFactor n) t < 0
    exact RomanianProblem.ScalarRow.rowFactor_derivative_neg hn ht1

theorem scalar_row_bound
    {n : ℕ} (hn : 2 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    rowFactor n t ≤ (n : ℝ) * (1 - q n) := by
  change RomanianProblem.ScalarRow.rowFactor n t ≤
    (n : ℝ) * (1 - RomanianProblem.ScalarRow.q n)
  exact RomanianProblem.ScalarRow.scalar_row_bound hn t ht

theorem scalar_row_bound_eq_iff
    {n : ℕ} (hn : 2 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    rowFactor n t = (n : ℝ) * (1 - q n) ↔ t = 1 := by
  change RomanianProblem.ScalarRow.rowFactor n t =
      (n : ℝ) * (1 - RomanianProblem.ScalarRow.q n) ↔ t = 1
  exact RomanianProblem.ScalarRow.scalar_row_bound_eq_iff hn t ht

/-! ### Weighted Vandermonde step -/

def weightedVandermonde {n : ℕ} (z : Fin n → ℂ) : CMat n :=
  fun i k =>
    (Real.sqrt (1 - ‖z i‖ ^ (2 * n)) : ℂ) *
      ((z i) / (rho n : ℂ)) ^ (k : ℕ)

theorem weightedVandermonde_det_sq
    {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (hz : InUnitDisk z) :
    ‖(weightedVandermonde z).det‖ ^ 2 =
      (rho n) ^ (-2 * (n * (n - 1) / 2 : ℤ))
        * vandermondeSq z * radialProduct z := by
  classical
  have hdet : (weightedVandermonde z).det =
      (∏ i : Fin n, (Real.sqrt (1 - ‖z i‖ ^ (2 * n)) : ℂ)) *
      (∏ k : Fin n, ((rho n : ℂ)⁻¹) ^ (k : ℕ)) *
      (Matrix.vandermonde z).det := by
    let d : Fin n → ℂ :=
      fun i => (Real.sqrt (1 - ‖z i‖ ^ (2 * n)) : ℂ)
    let c : Fin n → ℂ :=
      fun k => ((rho n : ℂ)⁻¹) ^ (k : ℕ)
    have hmatrix : weightedVandermonde z =
        Matrix.of fun i k => d i *
          (Matrix.of fun i k => c k * Matrix.vandermonde z i k) i k := by
      ext i k
      change (Real.sqrt (1 - ‖z i‖ ^ (2 * n)) : ℂ) *
        ((z i) / (rho n : ℂ)) ^ (k : ℕ) =
        (Real.sqrt (1 - ‖z i‖ ^ (2 * n)) : ℂ) *
          (((rho n : ℂ)⁻¹) ^ (k : ℕ) * (z i) ^ (k : ℕ))
      rw [div_pow, div_eq_mul_inv]
      ring
    calc
      (weightedVandermonde z).det =
          (Matrix.of fun i k => d i *
            (Matrix.of fun i k => c k * Matrix.vandermonde z i k) i k).det :=
        congrArg Matrix.det hmatrix
      _ = (∏ i, d i) *
          (Matrix.of fun i k => c k * Matrix.vandermonde z i k).det :=
        Matrix.det_mul_column d _
      _ = (∏ i, d i) * ((∏ k, c k) * (Matrix.vandermonde z).det) := by
        rw [Matrix.det_mul_row c (Matrix.vandermonde z)]
      _ = (∏ i : Fin n, (Real.sqrt (1 - ‖z i‖ ^ (2 * n)) : ℂ)) *
          (∏ k : Fin n, ((rho n : ℂ)⁻¹) ^ (k : ℕ)) *
          (Matrix.vandermonde z).det := by
        simp only [d, c]
        ring
  have hcolumn :
      ‖∏ k : Fin n, ((rho n : ℂ)⁻¹) ^ (k : ℕ)‖ ^ 2 =
        (rho n) ^ (-2 * (n * (n - 1) / 2 : ℤ)) := by
    have hsum : (∑ k : Fin n, (k : ℕ)) = n * (n - 1) / 2 := by
      calc
        (∑ k : Fin n, (k : ℕ)) = ∑ k ∈ Finset.range n, k :=
          Fin.sum_univ_eq_sum_range (fun k => k) n
        _ = n * (n - 1) / 2 := Finset.sum_range_id n
    have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hcast : ((n * (n - 1) / 2 : ℕ) : ℤ) =
        (n * (n - 1) / 2 : ℤ) := by
      rw [← hn1]
      norm_cast
    calc
      ‖∏ k : Fin n, ((rho n : ℂ)⁻¹) ^ (k : ℕ)‖ ^ 2 =
          (∏ k : Fin n, (rho n)⁻¹ ^ (k : ℕ)) ^ 2 := by
        simp only [norm_prod, norm_pow, norm_inv, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (rho_pos hn)]
      _ = ((rho n)⁻¹ ^ (∑ k : Fin n, (k : ℕ))) ^ 2 := by
        rw [Finset.prod_pow_eq_pow_sum]
      _ = ((rho n)⁻¹ ^ (n * (n - 1) / 2)) ^ 2 := by rw [hsum]
      _ = (rho n) ^ (-2 * (n * (n - 1) / 2 : ℤ)) := by
        rw [← pow_mul]
        rw [← hcast]
        rw [show -2 * ((n * (n - 1) / 2 : ℕ) : ℤ) =
          -((n * (n - 1) / 2) * 2 : ℕ) by omega]
        rw [zpow_neg, zpow_natCast]
        rw [inv_pow]
  have hrow :
      ‖∏ i : Fin n, (Real.sqrt (1 - ‖z i‖ ^ (2 * n)) : ℂ)‖ ^ 2 =
        radialProduct z := by
    have hnonneg : ∀ i : Fin n, 0 ≤ 1 - ‖z i‖ ^ (2 * n) := by
      intro i
      have hpow : ‖z i‖ ^ (2 * n) ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (le_of_lt (hz i))
      linarith
    calc
      ‖∏ i : Fin n, (Real.sqrt (1 - ‖z i‖ ^ (2 * n)) : ℂ)‖ ^ 2 =
          (∏ i : Fin n, Real.sqrt (1 - ‖z i‖ ^ (2 * n))) ^ 2 := by
        simp only [norm_prod, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
      _ = ∏ i : Fin n, (Real.sqrt (1 - ‖z i‖ ^ (2 * n))) ^ 2 := by
        rw [Finset.prod_pow]
      _ = radialProduct z := by
        simp only [radialProduct, Real.sq_sqrt (hnonneg _)]
  rw [hdet]
  simp only [norm_mul, mul_pow]
  rw [hcolumn, hrow]
  unfold vandermondeSq
  ring

theorem weightedVandermonde_row_norm
    {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (hz : InUnitDisk z) (i : Fin n) :
    (∑ k : Fin n, ‖weightedVandermonde z i k‖ ^ 2)
      =
    rowFactor n (‖z i‖ ^ 2 / rho n ^ 2) := by
  classical
  have hrho : 0 < rho n := rho_pos hn
  have hq : 0 < q n := q_pos hn
  have hzi : 0 ≤ 1 - ‖z i‖ ^ (2 * n) := by
    have hlt : ‖z i‖ ^ (2 * n) < 1 :=
      pow_lt_one₀ (norm_nonneg _) (hz i) (by omega)
    linarith
  have hrhopow :
      rho n ^ (2 * n) = q n := by
    unfold rho
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    calc
      (q n).rpow (1 / (2 * (n : ℝ))) ^ (2 * n) =
          (q n).rpow ((1 / (2 * (n : ℝ))) * (2 * n : ℕ)) :=
        (Real.rpow_mul_natCast (q_nonneg hn) _ _).symm
      _ = (q n).rpow 1 := by
        congr 1
        push_cast
        field_simp
      _ = q n := Real.rpow_one (q n)
  have hterm : ∀ k : Fin n,
      ‖weightedVandermonde z i k‖ ^ 2 =
        (1 - ‖z i‖ ^ (2 * n)) *
          (‖z i‖ ^ 2 / rho n ^ 2) ^ (k : ℕ) := by
    intro k
    have hsqrt :
        ‖(Real.sqrt (1 - ‖z i‖ ^ (2 * n)) : ℂ)‖ ^ 2 =
          1 - ‖z i‖ ^ (2 * n) := by
      simp [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hzi]
    have hratio : ‖z i / (rho n : ℂ)‖ ^ 2 =
        ‖z i‖ ^ 2 / rho n ^ 2 := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrho]
      ring
    have hpow : ‖z i / (rho n : ℂ)‖ ^ ((k : ℕ) * 2) =
        (‖z i / (rho n : ℂ)‖ ^ 2) ^ (k : ℕ) := by
      rw [mul_comm, pow_mul]
    unfold weightedVandermonde
    rw [norm_mul, mul_pow, norm_pow, hsqrt, ← pow_mul, hpow, hratio]
  have hlead :
      1 - ‖z i‖ ^ (2 * n) =
        1 - q n * (‖z i‖ ^ 2 / rho n ^ 2) ^ n := by
    rw [div_pow, ← pow_mul, ← pow_mul, hrhopow]
    field_simp
  simp_rw [hterm]
  unfold rowFactor
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => (‖z i‖ ^ 2 / rho n ^ 2) ^ k) n]
  rw [← Finset.mul_sum]
  rw [hlead]

theorem weighted_vandermonde_bound
    {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (hz : InUnitDisk z) :
    vandermondeSq z * radialProduct z ≤ upperBound n := by
  classical
  let A := weightedVandermonde z
  have hHad := hadamard_det_sq_le A
  have hrows :
      ∀ i : Fin n,
        (∑ j : Fin n, ‖A i j‖ ^ 2)
          ≤ (n : ℝ) * (1 - q n) := by
    intro i
    rw [show ∑ j : Fin n, ‖A i j‖ ^ 2 =
        rowFactor n (‖z i‖ ^ 2 / rho n ^ 2) by
      simpa [A] using weightedVandermonde_row_norm hn z hz i]
    apply scalar_row_bound hn
    positivity
  have hprod :
      (∏ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2)
        ≤ ((n : ℝ) * (1 - q n)) ^ n := by
    calc
      (∏ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2) ≤
          ∏ _i : Fin n, ((n : ℝ) * (1 - q n)) := by
        exact Finset.prod_le_prod
          (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg ‖A i j‖))
          (fun i _ => hrows i)
      _ = ((n : ℝ) * (1 - q n)) ^ n := by simp
  have hdet := weightedVandermonde_det_sq hn z hz
  rw [hdet] at hHad
  unfold upperBound
  have hrho : 0 < rho n := rho_pos hn
  have hrhoq :
      rho n ^ (n * (n - 1)) =
        Real.rpow (q n) (((n : ℝ) - 1) / 2) := by
    unfold rho
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    calc
      (q n).rpow (1 / (2 * (n : ℝ))) ^ (n * (n - 1)) =
          (q n).rpow ((1 / (2 * (n : ℝ))) * (n * (n - 1) : ℕ)) :=
        (Real.rpow_mul_natCast (q_nonneg hn) _ _).symm
      _ = (q n).rpow (((n : ℝ) - 1) / 2) := by
        congr 1
        push_cast
        rw [Nat.cast_sub (by omega)]
        field_simp
        ring
  have hbinomCast : ((n * (n - 1) / 2 : ℕ) : ℤ) =
      (n * (n - 1) / 2 : ℤ) := by
    have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    rw [← hn1]
    norm_cast
  have htwice : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    rw [mul_comm]
    exact Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one n)
  have hexponent :
      -2 * (n * (n - 1) / 2 : ℤ) = -((n * (n - 1) : ℕ) : ℤ) := by
    rw [← hbinomCast]
    have htwiceZ :
        (2 : ℤ) * ((n * (n - 1) / 2 : ℕ) : ℤ) =
          ((n * (n - 1) : ℕ) : ℤ) := by
      exact_mod_cast htwice
    omega
  have hscale :
      rho n ^ (-2 * (n * (n - 1) / 2 : ℤ)) =
        (rho n ^ (n * (n - 1)))⁻¹ := by
    rw [hexponent, zpow_neg, zpow_natCast]
  have hcombined :
      rho n ^ (-2 * (n * (n - 1) / 2 : ℤ)) *
          (vandermondeSq z * radialProduct z) ≤
        ((n : ℝ) * (1 - q n)) ^ n :=
    by simpa [mul_assoc] using hHad.trans hprod
  rw [hscale] at hcombined
  have hrhopos : 0 < rho n ^ (n * (n - 1)) := pow_pos hrho _
  have hmul := mul_le_mul_of_nonneg_left hcombined hrhopos.le
  have hbound :
      vandermondeSq z * radialProduct z ≤
        rho n ^ (n * (n - 1)) * ((n : ℝ) * (1 - q n)) ^ n := by
    calc
      vandermondeSq z * radialProduct z =
          rho n ^ (n * (n - 1)) *
            ((rho n ^ (n * (n - 1)))⁻¹ *
              (vandermondeSq z * radialProduct z)) := by
        field_simp
      _ ≤ rho n ^ (n * (n - 1)) * ((n : ℝ) * (1 - q n)) ^ n := hmul
  rw [hrhoq] at hbound
  calc
    vandermondeSq z * radialProduct z ≤
        (q n).rpow (((n : ℝ) - 1) / 2) *
          ((n : ℝ) * (1 - q n)) ^ n := hbound
    _ = (n : ℝ) ^ n * (q n).rpow (((n : ℝ) - 1) / 2) *
          (1 - q n) ^ n := by rw [mul_pow]; ring

/-! ### Equality in the weighted Hadamard step -/

theorem fin_prod_eq_pow_forces_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : ι → ℝ) (M : ℝ) (hM : 0 < M)
    (hf0 : ∀ i, 0 ≤ f i) (hfM : ∀ i, f i ≤ M)
    (hprod : (∏ i, f i) = M ^ Fintype.card ι) :
    ∀ i, f i = M := by
  classical
  intro i
  apply le_antisymm (hfM i)
  apply not_lt.mp
  intro hi
  let rest := ∏ j ∈ (Finset.univ : Finset ι).erase i, f j
  have hfactor : f i * rest = ∏ j : ι, f j := by
    exact Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)
  have hfullpos : 0 < ∏ j : ι, f j := by
    rw [hprod]
    exact pow_pos hM _
  have hrestpos : 0 < rest := by
    have : 0 < f i * rest := hfactor.symm ▸ hfullpos
    rcases mul_pos_iff.mp this with hpos | hneg
    · exact hpos.2
    · exact False.elim ((not_lt_of_ge (hf0 i)) hneg.1)
  have hrestle : rest ≤
      ∏ _j ∈ (Finset.univ : Finset ι).erase i, M := by
    exact Finset.prod_le_prod
      (fun j _ => hf0 j)
      (fun j _ => hfM j)
  have hstrict :
      (∏ j : ι, f j) < M ^ Fintype.card ι := by
    calc
      (∏ j : ι, f j) = f i * rest := hfactor.symm
      _ < M * rest := mul_lt_mul_of_pos_right hi hrestpos
      _ ≤ M * (∏ _j ∈ (Finset.univ : Finset ι).erase i, M) :=
        mul_le_mul_of_nonneg_left hrestle hM.le
      _ = M ^ Fintype.card ι := by
        calc
          M * (∏ _j ∈ (Finset.univ : Finset ι).erase i, M) =
              M * M ^ ((Finset.univ : Finset ι).erase i).card := by
            rw [Finset.prod_const]
          _ = M * M ^ (Fintype.card ι - 1) := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
            simp
          _ = M ^ Fintype.card ι := by
            rw [← pow_succ']
            congr 1
            have : 0 < Fintype.card ι := Fintype.card_pos
            omega
  rw [hprod] at hstrict
  exact (lt_self_iff_false _).mp hstrict

theorem fin_prod_eq_forces_eq_of_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℝ) (hg : ∀ i, 0 < g i)
    (hf0 : ∀ i, 0 ≤ f i) (hfg : ∀ i, f i ≤ g i)
    (hprod : (∏ i, f i) = ∏ i, g i) :
    ∀ i, f i = g i := by
  classical
  intro i
  apply le_antisymm (hfg i)
  apply not_lt.mp
  intro hi
  let restf := ∏ j ∈ (Finset.univ : Finset ι).erase i, f j
  let restg := ∏ j ∈ (Finset.univ : Finset ι).erase i, g j
  have hfactorf : f i * restf = ∏ j : ι, f j :=
    Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)
  have hfactorg : g i * restg = ∏ j : ι, g j :=
    Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i)
  have hfullpos : 0 < ∏ j : ι, f j := by
    rw [hprod]
    exact Finset.prod_pos fun j _ => hg j
  have hrestfpos : 0 < restf := by
    have hmul : 0 < f i * restf := hfactorf.symm ▸ hfullpos
    rcases mul_pos_iff.mp hmul with hpos | hneg
    · exact hpos.2
    · exact False.elim ((not_lt_of_ge (hf0 i)) hneg.1)
  have hrestle : restf ≤ restg :=
    Finset.prod_le_prod
      (fun j _ => hf0 j)
      (fun j _ => hfg j)
  have hstrict : (∏ j : ι, f j) < ∏ j : ι, g j := by
    calc
      (∏ j : ι, f j) = f i * restf := hfactorf.symm
      _ < g i * restf := mul_lt_mul_of_pos_right hi hrestfpos
      _ ≤ g i * restg := mul_le_mul_of_nonneg_left hrestle (hg i).le
      _ = ∏ j : ι, g j := hfactorg
  rw [hprod] at hstrict
  exact (lt_self_iff_false _).mp hstrict

theorem hadamard_det_sq_eq_forces_rows_orthogonal
    {n : ℕ} (A : CMat n)
    (hrowpos : ∀ i : Fin n, 0 < ∑ k : Fin n, ‖A i k‖ ^ 2)
    (heq : ‖A.det‖ ^ 2 = ∏ i : Fin n, ∑ k : Fin n, ‖A i k‖ ^ 2) :
    ∀ i j : Fin n, i ≠ j →
      ∑ k : Fin n, A i k * conj (A j k) = 0 := by
  classical
  let row : Fin n → EuclideanSpace ℂ (Fin n) :=
    fun i => WithLp.toLp 2 (fun k => A i k)
  let e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) ℂ
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) =
      Fintype.card (Fin n) := by simp
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
  have hdetprod : ‖A.det‖ = ∏ i, ‖inner ℂ (b i) (row i)‖ := by
    rw [← hstandard, hchange, hgs, norm_prod]
  have hrowsq (i : Fin n) :
      ‖row i‖ ^ 2 = ∑ k : Fin n, ‖A i k‖ ^ 2 := by
    simpa [row] using
      (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 (fun k => A i k)))
  have hsq : ‖A.det‖ ^ 2 = (∏ i, ‖row i‖) ^ 2 := by
    rw [← Finset.prod_pow]
    calc
      ‖A.det‖ ^ 2 = ∏ i : Fin n, ∑ k : Fin n, ‖A i k‖ ^ 2 := heq
      _ = ∏ i : Fin n, ‖row i‖ ^ 2 := by
        exact Finset.prod_congr rfl fun i _ => (hrowsq i).symm
  have hnormprod : ‖A.det‖ = ∏ i, ‖row i‖ := by
    have hleft : 0 ≤ ‖A.det‖ := norm_nonneg _
    have hright : 0 ≤ ∏ i, ‖row i‖ :=
      Finset.prod_nonneg fun i _ => norm_nonneg _
    nlinarith
  have hprodInner :
      (∏ i, ‖inner ℂ (b i) (row i)‖) = ∏ i, ‖row i‖ := by
    rw [← hdetprod, hnormprod]
  have hrowne (i : Fin n) : row i ≠ 0 := by
    intro hzrow
    have : ‖row i‖ ^ 2 = 0 := by simp [hzrow]
    rw [hrowsq i] at this
    linarith [hrowpos i]
  have hcauchy : ∀ i : Fin n,
      ‖inner ℂ (b i) (row i)‖ = ‖row i‖ := by
    apply fin_prod_eq_forces_eq_of_le
    · intro i
      exact norm_pos_iff.mpr (hrowne i)
    · intro i
      exact norm_nonneg _
    · intro i
      simpa [b.orthonormal.1 i] using
        norm_inner_le_norm (𝕜 := ℂ) (b i) (row i)
    · exact hprodInner
  have hparallel : ∀ i : Fin n, ∃ c : ℂ, c ≠ 0 ∧ row i = c • b i := by
    intro i
    have hbne : b i ≠ 0 := by
      exact norm_ne_zero_iff.mp (by simp [b.orthonormal.1 i])
    apply (norm_inner_eq_norm_iff hbne (hrowne i)).mp
    simpa [b.orthonormal.1 i] using hcauchy i
  intro i j hij
  obtain ⟨ci, hci0, hci⟩ := hparallel i
  obtain ⟨cj, hcj0, hcj⟩ := hparallel j
  have hinner : inner ℂ (row j) (row i) = 0 := by
    rw [hci, hcj]
    simp [inner_smul_left, inner_smul_right, b.orthonormal.2 hij.symm]
  simpa [row, EuclideanSpace.inner_toLp_toLp, dotProduct] using hinner

theorem weighted_det_sq_eq_of_upperBound_eq
    {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (hz : InUnitDisk z)
    (heq : vandermondeSq z * radialProduct z = upperBound n) :
    ‖(weightedVandermonde z).det‖ ^ 2 =
      ((n : ℝ) * (1 - q n)) ^ n := by
  have hrho : 0 < rho n := rho_pos hn
  have hrhoq :
      rho n ^ (n * (n - 1)) =
        (q n).rpow (((n : ℝ) - 1) / 2) := by
    unfold rho
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    calc
      (q n).rpow (1 / (2 * (n : ℝ))) ^ (n * (n - 1)) =
          (q n).rpow ((1 / (2 * (n : ℝ))) * (n * (n - 1) : ℕ)) :=
        (Real.rpow_mul_natCast (q_nonneg hn) _ _).symm
      _ = (q n).rpow (((n : ℝ) - 1) / 2) := by
        congr 1
        push_cast
        rw [Nat.cast_sub (by omega)]
        field_simp
        ring
  have hbinomCast : ((n * (n - 1) / 2 : ℕ) : ℤ) =
      (n * (n - 1) / 2 : ℤ) := by
    have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    rw [← hn1]
    norm_cast
  have htwice : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    rw [mul_comm]
    exact Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one n)
  have hexponent :
      -2 * (n * (n - 1) / 2 : ℤ) = -((n * (n - 1) : ℕ) : ℤ) := by
    rw [← hbinomCast]
    have htwiceZ :
        (2 : ℤ) * ((n * (n - 1) / 2 : ℕ) : ℤ) =
          ((n * (n - 1) : ℕ) : ℤ) := by
      exact_mod_cast htwice
    omega
  have hscale :
      rho n ^ (-2 * (n * (n - 1) / 2 : ℤ)) =
        (rho n ^ (n * (n - 1)))⁻¹ := by
    rw [hexponent, zpow_neg, zpow_natCast]
  rw [weightedVandermonde_det_sq hn z hz]
  rw [show rho n ^ (-2 * (n * (n - 1) / 2 : ℤ)) *
        vandermondeSq z * radialProduct z =
        rho n ^ (-2 * (n * (n - 1) / 2 : ℤ)) *
          (vandermondeSq z * radialProduct z) by ring]
  rw [heq, hscale]
  unfold upperBound
  rw [← hrhoq]
  field_simp
  rw [mul_pow]
  ring

theorem weighted_equality_forces_radii
    {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (hz : InUnitDisk z)
    (heq :
      vandermondeSq z * radialProduct z = upperBound n) :
    ∀ i : Fin n, ‖z i‖ = rho n := by
  classical
  let A := weightedVandermonde z
  let M : ℝ := (n : ℝ) * (1 - q n)
  let r : Fin n → ℝ := fun i => ∑ k : Fin n, ‖A i k‖ ^ 2
  have hM : 0 < M := by
    dsimp [M]
    exact mul_pos (by positivity) (sub_pos.mpr (q_lt_one hn))
  have hr0 : ∀ i, 0 ≤ r i := by
    intro i
    exact Finset.sum_nonneg (fun k _ => sq_nonneg ‖A i k‖)
  have hrM : ∀ i, r i ≤ M := by
    intro i
    dsimp [r, M]
    rw [show ∑ k : Fin n, ‖A i k‖ ^ 2 =
        rowFactor n (‖z i‖ ^ 2 / rho n ^ 2) by
      simpa [A] using weightedVandermonde_row_norm hn z hz i]
    exact scalar_row_bound hn _ (by positivity)
  have hHad : ‖A.det‖ ^ 2 ≤ ∏ i, r i := by
    simpa [r] using hadamard_det_sq_le A
  have hprodLe : (∏ i, r i) ≤ M ^ n := by
    calc
      (∏ i, r i) ≤ ∏ _i : Fin n, M :=
        Finset.prod_le_prod
          (fun i _ => hr0 i)
          (fun i _ => hrM i)
      _ = M ^ n := by simp
  have hrho : 0 < rho n := rho_pos hn
  have hrhoq :
      rho n ^ (n * (n - 1)) =
        (q n).rpow (((n : ℝ) - 1) / 2) := by
    unfold rho
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    calc
      (q n).rpow (1 / (2 * (n : ℝ))) ^ (n * (n - 1)) =
          (q n).rpow ((1 / (2 * (n : ℝ))) * (n * (n - 1) : ℕ)) :=
        (Real.rpow_mul_natCast (q_nonneg hn) _ _).symm
      _ = (q n).rpow (((n : ℝ) - 1) / 2) := by
        congr 1
        push_cast
        rw [Nat.cast_sub (by omega)]
        field_simp
        ring
  have hbinomCast : ((n * (n - 1) / 2 : ℕ) : ℤ) =
      (n * (n - 1) / 2 : ℤ) := by
    have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    rw [← hn1]
    norm_cast
  have htwice : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    rw [mul_comm]
    exact Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one n)
  have hexponent :
      -2 * (n * (n - 1) / 2 : ℤ) = -((n * (n - 1) : ℕ) : ℤ) := by
    rw [← hbinomCast]
    have htwiceZ :
        (2 : ℤ) * ((n * (n - 1) / 2 : ℕ) : ℤ) =
          ((n * (n - 1) : ℕ) : ℤ) := by
      exact_mod_cast htwice
    omega
  have hscale :
      rho n ^ (-2 * (n * (n - 1) / 2 : ℤ)) =
        (rho n ^ (n * (n - 1)))⁻¹ := by
    rw [hexponent, zpow_neg, zpow_natCast]
  have hdetFormula := weightedVandermonde_det_sq hn z hz
  have hdetEq : ‖A.det‖ ^ 2 = M ^ n := by
    change ‖(weightedVandermonde z).det‖ ^ 2 = M ^ n
    rw [hdetFormula]
    rw [show rho n ^ (-2 * (n * (n - 1) / 2 : ℤ)) *
          vandermondeSq z * radialProduct z =
          rho n ^ (-2 * (n * (n - 1) / 2 : ℤ)) *
            (vandermondeSq z * radialProduct z) by ring]
    rw [heq, hscale]
    unfold upperBound
    rw [← hrhoq]
    dsimp [M]
    field_simp
    rw [mul_pow]
    ring
  have hprodEq : (∏ i, r i) = M ^ n := by
    apply le_antisymm hprodLe
    rw [← hdetEq]
    exact hHad
  let finZero : Fin n := ⟨0, by omega⟩
  letI : Nonempty (Fin n) := ⟨finZero⟩
  have hrEq : ∀ i, r i = M :=
    fin_prod_eq_pow_forces_eq r M hM hr0 hrM (by simpa using hprodEq)
  intro i
  have hrowEq :
      rowFactor n (‖z i‖ ^ 2 / rho n ^ 2)
        = (n : ℝ) * (1 - q n) := by
    rw [← weightedVandermonde_row_norm hn z hz i]
    exact hrEq i
  have ht :
      ‖z i‖ ^ 2 / rho n ^ 2 = 1 :=
    (scalar_row_bound_eq_iff hn _
      (by positivity)).mp hrowEq
  have hnorm : 0 ≤ ‖z i‖ := norm_nonneg _
  have hsq : ‖z i‖ ^ 2 = rho n ^ 2 := by
    field_simp [hrho.ne'] at ht
    exact ht
  nlinarith

theorem weighted_equality_forces_regular
    {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (hz : InUnitDisk z)
    (heq :
      vandermondeSq z * radialProduct z = upperBound n) :
    IsRegularMaximizer z := by
  classical
  have hradii := weighted_equality_forces_radii hn z hz heq
  let M : ℝ := (n : ℝ) * (1 - q n)
  have hrowEq : ∀ i : Fin n,
      (∑ k : Fin n, ‖weightedVandermonde z i k‖ ^ 2) = M := by
    intro i
    rw [weightedVandermonde_row_norm hn z hz i]
    have ht : ‖z i‖ ^ 2 / rho n ^ 2 = 1 := by
      rw [hradii i]
      field_simp [rho_pos hn |>.ne']
    rw [ht]
    dsimp [M]
    simp [rowFactor]
    ring
  have hrowpos : ∀ i : Fin n,
      0 < ∑ k : Fin n, ‖weightedVandermonde z i k‖ ^ 2 := by
    intro i
    rw [hrowEq i]
    dsimp [M]
    exact mul_pos (by positivity) (sub_pos.mpr (q_lt_one hn))
  have hHadEq : ‖(weightedVandermonde z).det‖ ^ 2 =
      ∏ i : Fin n, ∑ k : Fin n, ‖weightedVandermonde z i k‖ ^ 2 := by
    rw [weighted_det_sq_eq_of_upperBound_eq hn z hz heq]
    calc
      ((n : ℝ) * (1 - q n)) ^ n = ∏ _i : Fin n, M := by
        simp [M]
      _ = ∏ i : Fin n,
          ∑ k : Fin n, ‖weightedVandermonde z i k‖ ^ 2 := by
        exact Finset.prod_congr rfl fun i _ => (hrowEq i).symm
  have hAorth := hadamard_det_sq_eq_forces_rows_orthogonal
    (weightedVandermonde z) hrowpos hHadEq
  have horth :
      ∀ i j : Fin n, i ≠ j →
        ∑ k : Fin n,
          ((z i * conj (z j)) / (rho n : ℂ)^2) ^ (k : ℕ) = 0 := by
    intro i j hij
    have hraw := hAorth i j hij
    have hrhopowlt : rho n ^ (2 * n) < 1 :=
      pow_lt_one₀ (rho_nonneg hn) (rho_lt_one hn) (by omega)
    have hprefnonneg : 0 ≤ 1 - rho n ^ (2 * n) := by linarith
    have hterm : ∀ k : Fin n,
        weightedVandermonde z i k * conj (weightedVandermonde z j k) =
          (1 - rho n ^ (2 * n) : ℝ) *
            (((z i * conj (z j)) / (rho n : ℂ)^2) ^ (k : ℕ)) := by
      intro k
      have hsquare :
          (Real.sqrt (1 - rho n ^ (2 * n)) : ℂ) *
              (Real.sqrt (1 - rho n ^ (2 * n)) : ℂ) =
            (1 - rho n ^ (2 * n) : ℝ) := by
        exact_mod_cast Real.mul_self_sqrt hprefnonneg
      have hbase :
          (z i / (rho n : ℂ)) * conj (z j / (rho n : ℂ)) =
            (z i * conj (z j)) / (rho n : ℂ)^2 := by
        rw [map_div₀, Complex.conj_ofReal]
        field_simp [(rho_pos hn).ne']
      unfold weightedVandermonde
      rw [hradii i, hradii j]
      simp only [map_mul, map_pow, Complex.conj_ofReal]
      rw [show
        (Real.sqrt (1 - rho n ^ (2 * n)) : ℂ) *
            (z i / (rho n : ℂ)) ^ (k : ℕ) *
            ((Real.sqrt (1 - rho n ^ (2 * n)) : ℂ) *
              conj (z j / (rho n : ℂ)) ^ (k : ℕ)) =
          ((Real.sqrt (1 - rho n ^ (2 * n)) : ℂ) *
            (Real.sqrt (1 - rho n ^ (2 * n)) : ℂ)) *
            (((z i / (rho n : ℂ)) *
              conj (z j / (rho n : ℂ))) ^ (k : ℕ)) by
        rw [mul_pow]
        ring]
      rw [hsquare, hbase]
    simp_rw [hterm] at hraw
    rw [← Finset.mul_sum] at hraw
    exact (mul_eq_zero.mp hraw).resolve_left (by
      exact_mod_cast (sub_pos.mpr hrhopowlt).ne')
  let finZero : Fin n := ⟨0, by omega⟩
  letI : OfNat (Fin n) 0 := ⟨finZero⟩
  letI : NeZero n := ⟨by omega⟩
  have hratios :
      ∀ i j : Fin n, i ≠ j →
        ∃ m : Fin n,
          m ≠ 0 ∧
          z i / z j =
            Complex.exp (2 * Real.pi * Complex.I * (m : ℕ) / (n : ℂ)) := by
    intro i j hij
    have hzj0 : z j ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [hradii j]
      exact (rho_pos hn).ne'
    have hnormsq : Complex.normSq (z j) = rho n ^ 2 := by
      rw [← Complex.sq_norm, hradii j]
    have hinv : (z j)⁻¹ = conj (z j) / (rho n : ℂ)^2 := by
      rw [Complex.inv_def, hnormsq]
      rw [div_eq_mul_inv]
      rw [Complex.ofReal_inv, Complex.ofReal_pow]
    have hxi :
        (z i * conj (z j)) / (rho n : ℂ)^2 = z i / z j := by
      symm
      rw [div_eq_mul_inv, hinv]
      ring
    let ξ : ℂ := z i / z j
    have hg : ∑ k : Fin n, ξ ^ (k : ℕ) = 0 := by
      dsimp [ξ]
      rw [← hxi]
      exact horth i j hij
    have hg' : ∑ k ∈ Finset.range n, ξ ^ k = 0 := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => ξ ^ k) n]
      exact hg
    have hpow : ξ ^ n = 1 := by
      have hgeom := geom_sum_mul_neg ξ n
      rw [hg'] at hgeom
      exact (sub_eq_zero.mp (by simpa using hgeom.symm)).symm
    have hxi0 : ξ ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow (by omega)] at hpow
      exact zero_ne_one hpow
    have hxi1 : ξ ≠ 1 := by
      intro hone
      have hnzero : (n : ℂ) = 0 := by
        simpa [hone] using hg
      have : n = 0 := Nat.cast_eq_zero.mp hnzero
      omega
    let u : ℂˣ := Units.mk0 ξ hxi0
    have hu : u ∈ rootsOfUnity n ℂ := by
      apply (mem_rootsOfUnity' n u).mpr
      exact hpow
    obtain ⟨m, hm, hmexp⟩ := (Complex.mem_rootsOfUnity n u).mp hu
    let mf : Fin n := ⟨m, hm⟩
    have hmf0 : mf ≠ 0 := by
      intro hm0
      have hmNat : m = 0 := by
        exact Fin.ext_iff.mp hm0
      subst m
      apply hxi1
      simpa [u] using hmexp.symm
    refine ⟨mf, hmf0, ?_⟩
    change ξ = Complex.exp
      (2 * Real.pi * Complex.I * ((mf : ℕ) : ℂ) / (n : ℂ))
    calc
      ξ = Complex.exp
          (2 * Real.pi * Complex.I * ((m : ℕ) : ℂ) / (n : ℂ)) := by
        rw [show 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (n : ℂ) =
          2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) / (n : ℂ)) by ring]
        simpa [u] using hmexp.symm
      _ = Complex.exp
          (2 * Real.pi * Complex.I * ((mf : ℕ) : ℂ) / (n : ℂ)) := by
        simp [mf]
  have hdetpos : 0 < ‖(weightedVandermonde z).det‖ ^ 2 := by
    rw [hHadEq]
    exact Finset.prod_pos fun i _ => hrowpos i
  have hdetne : (weightedVandermonde z).det ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero, zero_pow (by omega)] at hdetpos
    exact (lt_irrefl 0) hdetpos
  have hzinj : Function.Injective z := by
    intro i j hijz
    by_contra hij
    apply hdetne
    apply Matrix.det_zero_of_row_eq hij
    funext k
    unfold weightedVandermonde
    rw [hijz]
  let j₀ : Fin n := 0
  have hzj₀ : z j₀ ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hradii j₀]
    exact (rho_pos hn).ne'
  let exponent : Fin n → Fin n := fun i =>
    if h : i = j₀ then 0 else Classical.choose (hratios i j₀ h)
  have hexponent : ∀ i : Fin n,
      z i / z j₀ = Complex.exp
        (2 * Real.pi * Complex.I * ((exponent i : Fin n) : ℕ) / (n : ℂ)) := by
    intro i
    by_cases hi : i = j₀
    · subst i
      simp [exponent, hzj₀]
    · simpa [exponent, hi] using (Classical.choose_spec (hratios i j₀ hi)).2
  have hexponent_inj : Function.Injective exponent := by
    intro i j hij
    apply hzinj
    have hquot : z i / z j₀ = z j / z j₀ := by
      rw [hexponent i, hexponent j, hij]
    exact (div_left_inj' hzj₀).mp hquot
  have hexponent_surj : Function.Surjective exponent :=
    Finite.injective_iff_surjective.mp hexponent_inj
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective exponent
    ⟨hexponent_inj, hexponent_surj⟩
  let σ : Equiv.Perm (Fin n) := e.symm
  let θ : ℝ := Complex.arg (z j₀)
  refine ⟨θ, σ, ?_⟩
  intro k
  have heσ : exponent (σ k) = k := by
    exact e.apply_symm_apply k
  have hquot := hexponent (σ k)
  rw [heσ] at hquot
  have hzσ : z (σ k) =
      Complex.exp (2 * Real.pi * Complex.I * (k : ℕ) / (n : ℂ)) * z j₀ := by
    exact (div_eq_iff hzj₀).mp hquot
  have hzj₀polar : z j₀ = (rho n : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
    rw [← hradii j₀]
    simpa [θ, mul_comm] using (Complex.norm_mul_exp_arg_mul_I (z j₀)).symm
  rw [hzσ, hzj₀polar]
  unfold regularPoint regularAngle
  calc
    Complex.exp (2 * Real.pi * Complex.I * (k : ℕ) / (n : ℂ)) *
          ((rho n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        (rho n : ℂ) *
          (Complex.exp (2 * Real.pi * Complex.I * (k : ℕ) / (n : ℂ)) *
            Complex.exp (Complex.I * (θ : ℂ))) := by ring
    _ = (rho n : ℂ) * Complex.exp
          (2 * Real.pi * Complex.I * (k : ℕ) / (n : ℂ) +
            Complex.I * (θ : ℂ)) := by rw [Complex.exp_add]
    _ = (rho n : ℂ) * Complex.exp
          (Complex.I * ((θ + 2 * Real.pi * (k : ℕ) / (n : ℝ) : ℝ) : ℂ)) := by
      congr 2
      push_cast
      field_simp
      ring

/-! ### Regular polygon attains the bound -/

theorem regularPoint_in_disk
    {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    InUnitDisk (regularPoint n θ) := by
  intro j
  simp [regularPoint, Complex.norm_exp, regularAngle,
    abs_of_pos (rho_pos hn), rho_lt_one hn]

theorem regularPoint_vandermondeSq
    {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    vandermondeSq (regularPoint n θ)
      = (n : ℝ) ^ n * rho n ^ (n * (n - 1)) := by
  classical
  let c : ℂ := (rho n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  have hmatrix : Matrix.vandermonde (regularPoint n θ) =
      Matrix.of fun i (k : Fin n) => c ^ (k : ℕ) * fourierMatrix n i k := by
    ext i k
    change ((rho n : ℂ) * Complex.exp
        (Complex.I * (regularAngle n θ i : ℂ))) ^ (k : ℕ) =
      c ^ (k : ℕ) * fourierMatrix n i k
    simp only [regularAngle, fourierMatrix, c, mul_pow,
      ← Complex.exp_nat_mul]
    rw [show
      (rho n : ℂ) ^ (k : ℕ) *
          Complex.exp ((k : ℕ) * (Complex.I * ((θ + 2 * Real.pi * (i : ℕ) /
            (n : ℝ) : ℝ) : ℂ))) =
        (rho n : ℂ) ^ (k : ℕ) *
          (Complex.exp ((k : ℕ) * (Complex.I * (θ : ℂ))) *
            Complex.exp (2 * Real.pi * Complex.I * (i : ℕ) * (k : ℕ) /
              (n : ℂ))) by
      congr 1
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp [show (n : ℂ) ≠ 0 by
        exact_mod_cast (by omega : n ≠ 0)]
      ]
    ring
  have hdetF : ‖(fourierMatrix n).det‖ ^ 2 = (n : ℝ) ^ n := by
    have hdet := congrArg Matrix.det
      (fourierMatrix_mul_conjTranspose (by omega : 0 < n))
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_smul,
      Matrix.det_one, mul_one] at hdet
    have hnorm := congrArg norm hdet
    simpa [norm_mul, pow_two] using hnorm
  have hdet : (Matrix.vandermonde (regularPoint n θ)).det =
      (∏ k : Fin n, c ^ (k : ℕ)) * (fourierMatrix n).det := by
    rw [hmatrix, Matrix.det_mul_row]
  unfold vandermondeSq
  rw [hdet, norm_mul, mul_pow, hdetF]
  have hc : ‖c‖ = rho n := by
    simp [c, abs_of_pos (rho_pos hn)]
  rw [show ‖∏ k : Fin n, c ^ (k : ℕ)‖ ^ 2 =
      rho n ^ (n * (n - 1)) by
    rw [norm_prod]
    simp_rw [norm_pow, hc]
    rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => k) n,
      Finset.sum_range_id]
    exact Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one n)]
  ring

theorem regularPoint_boundaryProduct
    {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    boundaryProduct (regularPoint n θ)
      = (1 - rho n ^ (2 * n)) ^ n := by
  classical
  unfold boundaryProduct regularPoint regularAngle
  -- For each fixed i:
  --   prod_j (1 - rho^2 * omega^(i-j)) = 1-rho^(2n).
  have hrootprod :
      ∀ i : Fin n,
        ∏ j : Fin n,
          (1 -
            regularPoint n θ i *
              conj (regularPoint n θ j))
          = 1 - (rho n : ℂ) ^ (2 * n) := by
    intro i
    let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
    let ω : ℂ := ζ⁻¹
    let α : ℂ := ζ ^ (i : ℕ)
    let r : ℂ := (rho n : ℂ) ^ 2 * α
    have hζ : IsPrimitiveRoot ζ n := by
      exact Complex.isPrimitiveRoot_exp n (by omega)
    have hω : IsPrimitiveRoot ω n := by
      exact hζ.inv
    have hfactor : ∀ j : Fin n,
        regularPoint n θ i * conj (regularPoint n θ j) =
          ω ^ (j : ℕ) * r := by
      intro j
      unfold regularPoint regularAngle
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
      rw [show conj (Complex.I *
            ((θ + 2 * Real.pi * (j : ℕ) / (n : ℝ) : ℝ) : ℂ)) =
          -(Complex.I *
            ((θ + 2 * Real.pi * (j : ℕ) / (n : ℝ) : ℝ) : ℂ)) by
        apply Complex.ext <;> simp]
      rw [show
        (rho n : ℂ) * Complex.exp
              (Complex.I * ((θ + 2 * Real.pi * (i : ℕ) / (n : ℝ) : ℝ) : ℂ)) *
            ((rho n : ℂ) * Complex.exp
              (-(Complex.I * ((θ + 2 * Real.pi * (j : ℕ) /
                (n : ℝ) : ℝ) : ℂ)))) =
          (rho n : ℂ) ^ 2 *
            (Complex.exp
                (Complex.I * ((θ + 2 * Real.pi * (i : ℕ) /
                  (n : ℝ) : ℝ) : ℂ)) *
              Complex.exp
                (-(Complex.I * ((θ + 2 * Real.pi * (j : ℕ) /
                  (n : ℝ) : ℝ) : ℂ)))) by ring]
      rw [← Complex.exp_add]
      simp only [ζ, ω, α, r]
      rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
      rw [← Complex.exp_nat_mul]
      rw [show
        Complex.exp ((j : ℕ) * -(2 * Real.pi * Complex.I / (n : ℂ))) *
            ((rho n : ℂ) ^ 2 *
              Complex.exp ((i : ℕ) * (2 * Real.pi * Complex.I / (n : ℂ)))) =
          (rho n : ℂ) ^ 2 *
            (Complex.exp ((j : ℕ) * -(2 * Real.pi * Complex.I / (n : ℂ))) *
              Complex.exp ((i : ℕ) * (2 * Real.pi * Complex.I / (n : ℂ)))) by ring]
      apply mul_left_cancel₀ (pow_ne_zero 2
        (Complex.ofReal_ne_zero.mpr (rho_pos hn).ne'))
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    simp_rw [hfactor]
    rw [primitive_root_fin_product (by omega) hω]
    congr 1
    simp only [r, α, mul_pow]
    have halpha : (ζ ^ (i : ℕ)) ^ n = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [halpha, mul_one, ← pow_mul]
  calc
    ∏ i : Fin n, ∏ j : Fin n,
        ‖1 - regularPoint n θ i * conj (regularPoint n θ j)‖
      = ∏ i : Fin n,
          ‖∏ j : Fin n,
            (1 - regularPoint n θ i * conj (regularPoint n θ j))‖ := by
          simp [norm_prod]
    _ = ∏ i : Fin n, ‖1 - (rho n : ℂ) ^ (2 * n)‖ := by
          simp [hrootprod]
    _ = (1 - rho n ^ (2 * n)) ^ n := by
          have hlt : rho n ^ (2 * n) < 1 := by
            exact pow_lt_one₀ (rho_nonneg hn) (rho_lt_one hn) (by omega)
          have hcast :
              1 - (rho n : ℂ) ^ (2 * n) =
                ((1 - rho n ^ (2 * n) : ℝ) : ℂ) := by
            push_cast
            rfl
          rw [hcast, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr hlt.le)]
          simp

theorem rho_pow_two_n
    {n : ℕ} (hn : 2 ≤ n) :
    rho n ^ (2 * n) = q n := by
  unfold rho
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn))
  calc
    (q n).rpow (1 / (2 * (n : ℝ))) ^ (2 * n) =
        (q n).rpow ((1 / (2 * (n : ℝ))) * (2 * n : ℕ)) :=
      (Real.rpow_mul_natCast (q_nonneg hn) _ _).symm
    _ = (q n).rpow 1 := by
      congr 1
      push_cast
      field_simp [hn0]
    _ = q n := Real.rpow_one _

theorem regularPoint_attains_upperBound
    {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    objective (regularPoint n θ) = upperBound n := by
  rw [objective, regularPoint_vandermondeSq hn θ,
    regularPoint_boundaryProduct hn θ, rho_pow_two_n hn]
  unfold upperBound
  have hrhoq :
      rho n ^ (n * (n - 1)) =
        Real.rpow (q n) (((n : ℝ) - 1) / 2) := by
    unfold rho
    calc
      (q n).rpow (1 / (2 * (n : ℝ))) ^ (n * (n - 1)) =
          (q n).rpow
            ((1 / (2 * (n : ℝ))) * (n * (n - 1) : ℕ)) :=
        (Real.rpow_mul_natCast (q_nonneg hn) _ _).symm
      _ = (q n).rpow (((n : ℝ) - 1) / 2) := by
        congr 1
        push_cast
        rw [Nat.cast_sub (by omega)]
        field_simp
        ring
  rw [hrhoq]

/-! ### Assemble the maximization theorem -/

theorem vandermondeSq_nonneg
    {n : ℕ} (z : Fin n → ℂ) :
    0 ≤ vandermondeSq z := by
  unfold vandermondeSq
  positivity

theorem objective_le_upperBound
    {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (hz : InUnitDisk z) :
    objective z ≤ upperBound n := by
  calc
    objective z
        = vandermondeSq z * boundaryProduct z := rfl
    _ ≤ vandermondeSq z * radialProduct z :=
      mul_le_mul_of_nonneg_left
        (boundaryProduct_le_radialProduct hn z hz)
        (vandermondeSq_nonneg z)
    _ ≤ upperBound n :=
      weighted_vandermonde_bound hn z hz

theorem objective_eq_upperBound_implies_weighted_eq
    {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (hz : InUnitDisk z)
    (heq : objective z = upperBound n) :
    vandermondeSq z * radialProduct z = upperBound n := by
  have h1 :
      objective z ≤ vandermondeSq z * radialProduct z := by
    exact mul_le_mul_of_nonneg_left
      (boundaryProduct_le_radialProduct hn z hz)
      (vandermondeSq_nonneg z)
  have h2 :
      vandermondeSq z * radialProduct z ≤ upperBound n :=
    weighted_vandermonde_bound hn z hz
  linarith

theorem equality_forces_regular
    {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (hz : InUnitDisk z)
    (heq : objective z = upperBound n) :
    IsRegularMaximizer z := by
  exact weighted_equality_forces_regular hn z hz
    (objective_eq_upperBound_implies_weighted_eq hn z hz heq)

theorem objective_eq_of_perm {n : ℕ}
    (z w : Fin n → ℂ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ j, z (σ j) = w j) : objective z = objective w := by
  classical
  have hmat : Matrix.vandermonde w =
      (Matrix.vandermonde z).submatrix σ id := by
    ext i k
    simp [Matrix.vandermonde_apply, hσ]
  have hv : vandermondeSq z = vandermondeSq w := by
    unfold vandermondeSq
    have hd := Matrix.det_permute σ (Matrix.vandermonde z)
    rw [← hmat] at hd
    have hn := congrArg norm hd
    have hsign : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
      have hunit :
          (Equiv.Perm.sign σ : ℤ) *
              (↑((Equiv.Perm.sign σ)⁻¹) : ℤ) = 1 := by
        simp
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with hs | hs <;>
        simp [hs]
    have hn' : ‖(Matrix.vandermonde w).det‖ =
        ‖(Matrix.vandermonde z).det‖ := by
      rw [norm_mul, hsign, one_mul] at hn
      exact hn
    exact congrArg (fun x : ℝ => x ^ 2) hn'.symm
  have hb : boundaryProduct z = boundaryProduct w := by
    unfold boundaryProduct
    calc
      (∏ i, ∏ j, ‖1 - z i * conj (z j)‖) =
          ∏ i, ∏ j, ‖1 - z (σ i) * conj (z (σ j))‖ := by
        symm
        apply Fintype.prod_equiv σ
        intro i
        apply Fintype.prod_equiv σ
        intro j
        rfl
      _ = ∏ i, ∏ j, ‖1 - w i * conj (w j)‖ := by
        simp_rw [hσ]
  unfold objective
  rw [hv, hb]

theorem regular_is_equality
    {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (hz : InUnitDisk z)
    (hreg : IsRegularMaximizer z) :
    objective z = upperBound n := by
  rcases hreg with ⟨θ, σ, hσ⟩
  have hperm :
      objective z = objective (regularPoint n θ) := by
    exact objective_eq_of_perm z (regularPoint n θ) σ hσ
  rw [hperm]
  exact regularPoint_attains_upperBound hn θ

theorem objective_eq_upperBound_iff_regular
    {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (hz : InUnitDisk z) :
    objective z = upperBound n ↔ IsRegularMaximizer z := by
  constructor
  · exact equality_forces_regular hn z hz
  · exact regular_is_equality hn z hz

/-! ### Part (ii): the maximizing radius tends to 1 -/

theorem log_q_tendsto_neg_log_three :
    Tendsto
      (fun n : ℕ => Real.log (q (n + 2)))
      atTop
      (𝓝 (-Real.log 3)) := by
  have hq :
      Tendsto (fun n : ℕ => q (n + 2)) atTop (𝓝 (1 / 3 : ℝ)) := by
    have hinv0 :
        Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    have hinv :
        Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
      (Filter.tendsto_add_atTop_iff_nat 2).mpr hinv0
    have hfrac := (hinv.const_sub (1 : ℝ)).div
      (hinv.const_sub (3 : ℝ)) (by norm_num : (3 : ℝ) - 0 ≠ 0)
    convert hfrac using 1
    · funext n
      unfold q
      have hn2 : (((n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
      simp only [Pi.div_apply]
      field_simp [hn2]
    · norm_num
  have hpos : (0 : ℝ) < 1 / 3 := by norm_num
  have := (Real.continuousAt_log hpos.ne').tendsto.comp hq
  simpa [Real.log_div, Real.log_one, Function.comp_def] using this

theorem rho_tendsto_one :
    Tendsto rho atTop (𝓝 1) := by
  have hlog :
      Tendsto
        (fun n : ℕ =>
          (1 / (2 * ((n + 2 : ℕ) : ℝ))) *
            Real.log (q (n + 2)))
        atTop (𝓝 0) := by
    have hzero :
        Tendsto
          (fun n : ℕ => 1 / (2 * ((n + 2 : ℕ) : ℝ)))
          atTop (𝓝 0) := by
      have hnat : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ)) atTop atTop :=
        (Filter.tendsto_add_atTop_iff_nat 2).mpr tendsto_natCast_atTop_atTop
      simpa [Function.comp_def, one_div] using
        (tendsto_inv_atTop_zero.comp
          (hnat.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
    convert hzero.mul log_q_tendsto_neg_log_three using 1 <;> simp
  have hexp :
      Tendsto
        (fun n : ℕ =>
          Real.exp
            ((1 / (2 * ((n + 2 : ℕ) : ℝ))) *
              Real.log (q (n + 2))))
        atTop (𝓝 1) := by
    simpa [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hrho :
      ∀ n : ℕ,
        rho (n + 2) =
          Real.exp
            ((1 / (2 * ((n + 2 : ℕ) : ℝ))) *
              Real.log (q (n + 2))) := by
    intro n
    unfold rho
    calc
      Real.rpow (q (n + 2)) (1 / (2 * ((n + 2 : ℕ) : ℝ))) =
          Real.exp (Real.log (q (n + 2)) *
            (1 / (2 * ((n + 2 : ℕ) : ℝ)))) :=
        Real.rpow_def_of_pos (q_pos (by omega : 2 ≤ n + 2)) _
      _ = Real.exp ((1 / (2 * ((n + 2 : ℕ) : ℝ))) *
            Real.log (q (n + 2))) := by
        congr 1
        ring
  have hshift :
      Tendsto (fun n : ℕ => rho (n + 2)) atTop (𝓝 1) := by
    simpa [hrho] using hexp
  exact (Filter.tendsto_add_atTop_iff_nat 2).mp hshift

/-- Part (ii) in the form needed for any chosen sequence of maximizers. -/
theorem maximizing_min_radius_tendsto_one
    (a : ℕ → ℝ)
    (ha : ∀ n, 2 ≤ n → a n = rho n) :
    Tendsto a atTop (𝓝 1) := by
  apply rho_tendsto_one.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  symm
  exact ha n hn

/-!
Audit targets.  If Lean reaches these commands, all preceding declarations
have elaborated and kernel-checked.
-/

#print axioms objective_le_upperBound
#print axioms objective_eq_upperBound_iff_regular
#print axioms rho_tendsto_one

end RomanianOpenProblemStrict
