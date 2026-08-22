import Mathlib

open scoped BigOperators
open Polynomial

namespace RomanianProblem.ScalarRow

noncomputable def q (n : ℕ) : ℝ := ((n : ℝ) - 1) / (3 * (n : ℝ) - 1)

noncomputable def rowFactor (n : ℕ) (t : ℝ) : ℝ :=
  (1 - q n * t ^ n) * (∑ k ∈ Finset.range n, t ^ k)

noncomputable def geomPoly (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range n, Polynomial.X ^ k

noncomputable def coeffB (n m : ℕ) : ℝ :=
  if m ≤ n - 2 then
    ((3 * (n : ℝ) - 1) / 2) * (m + 1) * (m + 2)
  else
    (((n : ℝ) - 1) / 2) *
      (2 * (n : ℝ) * (2 * (n : ℝ) - 1) - (m + 1) * (m + 2))

noncomputable def qPoly (n : ℕ) : ℝ[X] :=
  ∑ m ∈ Finset.range (2 * n - 2), Polynomial.C (coeffB n m) * Polynomial.X ^ m

lemma geomPoly_coeff (n k : ℕ) :
    (geomPoly n).coeff k = if k < n then 1 else 0 := by
  simp [geomPoly]

lemma geomPoly_derivative_coeff (n k : ℕ) :
    (geomPoly n).derivative.coeff k = if k + 1 < n then (k + 1 : ℝ) else 0 := by
  rw [coeff_derivative, geomPoly_coeff]
  simp

theorem polynomial_factorization {n : ℕ} (hn : 2 ≤ n) :
    Polynomial.C (3 * (n : ℝ) - 1) * (geomPoly n).derivative -
        Polynomial.C ((n : ℝ) - 1) *
          (Polynomial.X ^ n * (geomPoly n).derivative +
            Polynomial.C (n : ℝ) * Polynomial.X ^ (n - 1) * geomPoly n) =
      (1 - Polynomial.X) * qPoly n := by
  ext k
  simp only [coeff_sub, coeff_add, coeff_C_mul, geomPoly_derivative_coeff]
  rw [coeff_X_pow_mul']
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  rw [show (1 - X) * qPoly n = qPoly n - X * qPoly n by ring, coeff_sub]
  rw [← pow_one X, coeff_X_pow_mul']
  simp only [geomPoly_derivative_coeff]
  by_cases hlow : k + 1 < n
  · have hklt : k < 2 * n - 2 := by omega
    have hkle : k ≤ n - 2 := by omega
    by_cases hk0 : k = 0
    · subst k
      simp [qPoly, coeffB, geomPoly_coeff, hn]
      split_ifs <;> try omega
      all_goals aesop
    · have hkpos : 1 ≤ k := by omega
      have hkpred : k - 1 ≤ n - 2 := by omega
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub hkpos]
        norm_num
      simp [qPoly, coeffB, geomPoly_coeff, hlow, hklt, hkle, hkpos, hkpred, hcast]
      split_ifs <;> try omega
      all_goals ring
  · by_cases hkn : k < n
    · have hk : k = n - 1 := by omega
      subst k
      have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have hc2 : ((n - 1 - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
        rw [show n - 1 - 1 = n - 2 by omega, Nat.cast_sub hn]
        norm_num
      simp [qPoly, coeffB, geomPoly_coeff, hn]
      split_ifs <;> try omega
      all_goals rw [hc1, hc2]; ring
    · have hnk : n ≤ k := by omega
      by_cases htop : k < 2 * n - 2
      · have hknot : ¬ k ≤ n - 2 := by omega
        have hkpred : ¬ k - 1 ≤ n - 2 := by omega
        have hkpredtop : k - 1 < 2 * n - 2 := by omega
        have hkpos : 1 ≤ k := by omega
        have hc1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub hkpos]
          norm_num
        have hcn : ((k - n : ℕ) : ℝ) = (k : ℝ) - n := by
          rw [Nat.cast_sub hnk]
        simp [qPoly, coeffB, geomPoly_coeff, hlow, hkn, hnk, htop,
          hknot, hkpred, hkpredtop, hkpos, hc1, hcn]
        split_ifs <;> try omega
        all_goals ring
      · have hklarge : 2 * n - 2 ≤ k := by omega
        have hkpredlarge : 2 * n - 2 ≤ k - 1 ∨ k = 2 * n - 2 := by omega
        rcases hkpredlarge with hp | rfl
        · simp [qPoly, coeffB, geomPoly_coeff, hlow, hkn, hnk, htop, hp]
          split_ifs <;> try omega
          all_goals ring
        · have hc1 : (((2 * n - 2 - n : ℕ)) : ℝ) = (n : ℝ) - 2 := by
            rw [show 2 * n - 2 - n = n - 2 by omega, Nat.cast_sub hn]
            norm_num
          have hc2 : (((2 * n - 2 - 1 : ℕ)) : ℝ) = 2 * (n : ℝ) - 3 := by
            rw [show 2 * n - 2 - 1 = 2 * n - 3 by omega,
              Nat.cast_sub (by omega : 3 ≤ 2 * n)]
            push_cast
            ring
          simp [qPoly, coeffB, geomPoly_coeff, hn]
          split_ifs <;> try omega
          all_goals rw [hc1, hc2]; ring

theorem coeffB_pos {n m : ℕ} (hn : 2 ≤ n) (hm : m < 2 * n - 2) :
    0 < coeffB n m := by
  unfold coeffB
  by_cases hlow : m ≤ n - 2
  · rw [if_pos hlow]
    have hnR : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hn)
    have hfac : 0 < (3 * (n : ℝ) - 1) / 2 := by nlinarith
    have hm1 : (0 : ℝ) < m + 1 := by positivity
    have hm2 : (0 : ℝ) < m + 2 := by positivity
    positivity
  · rw [if_neg hlow]
    have hnR : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hn)
    have hmR : (m : ℝ) ≤ 2 * (n : ℝ) - 3 := by
      have hmn : m ≤ 2 * n - 3 := by omega
      have hc : (m : ℝ) ≤ (2 * n - 3 : ℕ) := by exact_mod_cast hmn
      rw [Nat.cast_sub (by omega : 3 ≤ 2 * n)] at hc
      push_cast at hc
      exact hc
    have hgap :
        (m + 1 : ℝ) * (m + 2) < 2 * (n : ℝ) * (2 * (n : ℝ) - 1) := by
      nlinarith [sq_nonneg ((m : ℝ) - (2 * (n : ℝ) - 3))]
    positivity

theorem qPoly_eval_pos {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    0 < (qPoly n).eval t := by
  change 0 < Polynomial.evalRingHom t (qPoly n)
  rw [qPoly, map_sum]
  apply Finset.sum_pos'
  · intro m hm
    simp only [Finset.mem_range] at hm
    simpa using mul_nonneg (coeffB_pos hn hm).le (pow_nonneg ht m)
  · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    simp [coeffB, hn]
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith

lemma geomPoly_eval (n : ℕ) (t : ℝ) :
    (geomPoly n).eval t = ∑ k ∈ Finset.range n, t ^ k := by
  simp [geomPoly]

lemma geomPoly_derivative_eval (n : ℕ) (t : ℝ) :
    (geomPoly n).derivative.eval t =
      ∑ k ∈ Finset.range n, (k : ℝ) * t ^ (k - 1) := by
  rw [geomPoly, derivative_sum]
  simp_rw [derivative_X_pow]
  change Polynomial.evalRingHom t (∑ k ∈ Finset.range n,
    Polynomial.C (k : ℝ) * Polynomial.X ^ (k - 1)) = _
  rw [map_sum]
  simp

theorem rowFactor_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (rowFactor n)
      ((∑ k ∈ Finset.range n, (k : ℝ) * t ^ (k - 1)) * (1 - q n * t ^ n) -
        q n * (n : ℝ) * t ^ (n - 1) * (∑ k ∈ Finset.range n, t ^ k)) t := by
  have ha : HasDerivAt (fun x : ℝ ↦ 1 - q n * x ^ n)
      (0 - q n * ((n : ℝ) * t ^ (n - 1))) t :=
    (hasDerivAt_const t 1).sub ((hasDerivAt_pow n t).const_mul (q n))
  have hb : HasDerivAt (fun x : ℝ ↦ ∑ k ∈ Finset.range n, x ^ k)
      (∑ k ∈ Finset.range n, (k : ℝ) * t ^ (k - 1)) t := by
    have h := HasDerivAt.sum (u := Finset.range n) (fun k _ ↦ hasDerivAt_pow k t)
    rw [Finset.sum_fn] at h
    exact h
  unfold rowFactor
  change HasDerivAt
    ((fun x : ℝ ↦ 1 - q n * x ^ n) *
      (fun x : ℝ ↦ ∑ k ∈ Finset.range n, x ^ k)) _ t
  exact (ha.mul hb).congr_deriv (by ring)

theorem rowFactor_derivative_factor {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    (3 * (n : ℝ) - 1) * deriv (rowFactor n) t =
      (1 - t) * (qPoly n).eval t := by
  have hp := congrArg (Polynomial.eval t) (polynomial_factorization hn)
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one, geomPoly_eval, geomPoly_derivative_eval] at hp
  rw [(rowFactor_hasDerivAt n t).deriv]
  unfold q
  have hden : (3 * (n : ℝ) - 1) ≠ 0 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp [hden]
  linear_combination hp

theorem rowFactor_derivative_pos {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) : 0 < deriv (rowFactor n) t := by
  have hden : 0 < 3 * (n : ℝ) - 1 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hq := qPoly_eval_pos hn ht
  have hf := rowFactor_derivative_factor hn t
  nlinarith

theorem rowFactor_derivative_one {n : ℕ} (hn : 2 ≤ n) :
    deriv (rowFactor n) 1 = 0 := by
  have hden : 0 < 3 * (n : ℝ) - 1 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hf := rowFactor_derivative_factor hn 1
  norm_num at hf
  rcases hf with hbad | hzero
  · linarith
  · exact hzero

theorem rowFactor_derivative_neg {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht1 : 1 < t) : deriv (rowFactor n) t < 0 := by
  have hden : 0 < 3 * (n : ℝ) - 1 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hq := qPoly_eval_pos hn (le_trans (by norm_num) ht1.le)
  have hf := rowFactor_derivative_factor hn t
  nlinarith

theorem rowFactor_continuous (n : ℕ) : Continuous (rowFactor n) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (rowFactor_hasDerivAt n t).continuousAt

theorem rowFactor_value_one (n : ℕ) :
    rowFactor n 1 = (n : ℝ) * (1 - q n) := by
  simp [rowFactor]
  ring

set_option maxHeartbeats 200000 in
theorem scalar_row_bound {n : ℕ} (hn : 2 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    rowFactor n t ≤ (n : ℝ) * (1 - q n) := by
  rw [← rowFactor_value_one n]
  by_cases ht1 : t < 1
  · have hmono : StrictMonoOn (rowFactor n) (Set.Icc 0 1) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      · exact (rowFactor_continuous n).continuousOn
      · intro x hx
        rw [interior_Icc] at hx
        exact rowFactor_derivative_pos hn hx.1.le hx.2
    have htmem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht, ht1.le⟩
    have h1mem : (1 : ℝ) ∈ Set.Icc 0 1 := by constructor <;> norm_num
    exact (hmono htmem h1mem ht1).le
  · have h1t : 1 ≤ t := le_of_not_gt ht1
    by_cases heq : t = 1
    · rw [heq]
    · have hanti : StrictAntiOn (rowFactor n) (Set.Ici 1) := by
        apply strictAntiOn_of_deriv_neg (convex_Ici 1)
        · exact (rowFactor_continuous n).continuousOn
        · intro x hx
          rw [interior_Ici] at hx
          exact rowFactor_derivative_neg hn hx
      have h1mem : (1 : ℝ) ∈ Set.Ici 1 := by
        change (1 : ℝ) ≤ 1
        exact le_rfl
      have htmem : t ∈ Set.Ici (1 : ℝ) := h1t
      exact (hanti h1mem htmem (lt_of_le_of_ne h1t (Ne.symm heq))).le

set_option maxHeartbeats 200000 in
theorem scalar_row_bound_eq_iff {n : ℕ} (hn : 2 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    rowFactor n t = (n : ℝ) * (1 - q n) ↔ t = 1 := by
  rw [← rowFactor_value_one n]
  constructor
  · intro heq
    by_cases ht1 : t < 1
    · have hmono : StrictMonoOn (rowFactor n) (Set.Icc 0 1) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
        · exact (rowFactor_continuous n).continuousOn
        · intro x hx
          rw [interior_Icc] at hx
          exact rowFactor_derivative_pos hn hx.1.le hx.2
      have htmem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht, ht1.le⟩
      have h1mem : (1 : ℝ) ∈ Set.Icc 0 1 := by constructor <;> norm_num
      exact False.elim ((hmono htmem h1mem ht1).ne heq)
    · have h1t : 1 ≤ t := le_of_not_gt ht1
      rcases h1t.eq_or_lt with h | h
      · exact h.symm
      · have hanti : StrictAntiOn (rowFactor n) (Set.Ici 1) := by
          apply strictAntiOn_of_deriv_neg (convex_Ici 1)
          · exact (rowFactor_continuous n).continuousOn
          · intro x hx
            rw [interior_Ici] at hx
            exact rowFactor_derivative_neg hn hx
        have h1mem : (1 : ℝ) ∈ Set.Ici 1 := by
          change (1 : ℝ) ≤ 1
          exact le_rfl
        have htmem : t ∈ Set.Ici (1 : ℝ) := h.le
        exact False.elim ((hanti h1mem htmem h).ne heq)
  · rintro rfl
    rfl

end RomanianProblem.ScalarRow
