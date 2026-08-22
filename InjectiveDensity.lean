import Mathlib

open scoped ComplexConjugate Topology

namespace RomanianProblem.InjectiveDensity

def InUnitDisk {n : ℕ} (z : Fin n → ℂ) : Prop :=
  ∀ i, ‖z i‖ < 1

theorem dense_injective_tuples_in_open_disk {n : ℕ} (z : Fin n → ℂ)
    (hz : InUnitDisk z) :
    z ∈ closure {w : Fin n → ℂ | Function.Injective w ∧ InUnitDisk w} := by
  classical
  rw [mem_closure_iff]
  intro U hU hzU
  let disk : Set (Fin n → ℂ) := {w | InUnitDisk w}
  have hdiskOpen : IsOpen disk := by
    simp only [disk, InUnitDisk, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i ↦
      isOpen_lt (continuous_norm.comp (continuous_apply i)) continuous_const
  let F : ℂ → (Fin n → ℂ) := fun t i ↦ z i + t * (i.val : ℂ)
  have hF : Continuous F := by
    exact continuous_pi fun i ↦
      continuous_const.add (continuous_id.mul continuous_const)
  have hF0 : F 0 = z := by
    ext i
    simp [F]
  let V : Set ℂ := F ⁻¹' (U ∩ disk)
  have hVopen : IsOpen V := (hU.inter hdiskOpen).preimage hF
  have hVnonempty : V.Nonempty := by
    refine ⟨0, ?_⟩
    change F 0 ∈ U ∩ disk
    rw [hF0]
    exact ⟨hzU, hz⟩
  let bad : Finset ℂ := Finset.univ.image fun p : Fin n × Fin n ↦
    (z p.2 - z p.1) / ((p.1.val : ℂ) - (p.2.val : ℂ))
  have hdense : Dense ((Set.univ : Set ℂ) \ (bad : Set ℂ)) :=
    dense_univ.sdiff_finset bad
  obtain ⟨t, htbad, htV⟩ := hdense.exists_mem_open hVopen hVnonempty
  refine ⟨F t, htV.1, ?_, htV.2⟩
  intro i j hij
  by_cases hij' : i = j
  · exact hij'
  · have hden : ((i.val : ℂ) - (j.val : ℂ)) ≠ 0 := by
      have hv : i.val ≠ j.val := fun h ↦ hij' (Fin.ext h)
      have hc : (i.val : ℂ) ≠ (j.val : ℂ) := by exact_mod_cast hv
      exact sub_ne_zero.mpr hc
    have htval :
        t = (z j - z i) / ((i.val : ℂ) - (j.val : ℂ)) := by
      apply (eq_div_iff hden).2
      dsimp [F] at hij
      linear_combination hij
    have htmem : t ∈ bad := by
      rw [htval]
      exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩
    exact False.elim (htbad.2 htmem)

end RomanianProblem.InjectiveDensity
