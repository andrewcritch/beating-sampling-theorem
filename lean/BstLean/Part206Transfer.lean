import BstLean.Part154Fin

/-! Parameterized full and parallel centre transfer. All vectors use one input
mean. This module introduces no event and no probability charge. -/
namespace BstLean.Part206
open Real Matrix
open BstLean.Part130 (normSq)
open BstLean.Part153 (nrm nrm_nonneg nrm_sq)

noncomputable def fullAllowance (deviation radius finite : ℝ) : ℝ :=
  deviation + radius + finite

noncomputable def parallelAllowance (oracleParallel oracleFull finite lower rn : ℝ) : ℝ :=
  oracleParallel + finite * (1 + 2 * oracleFull / (lower * rn))

/-- Radius and finite errors add as amplitudes before squaring. -/
theorem full_centre_transfer {k : ℕ} (a h bo b : Fin k → ℝ)
    {s X deviation radius finite : ℝ} (hs : 0 ≤ s)
    (hD : s * nrm (h - bo) ≤ X * deviation)
    (hR : s * nrm (a - h) ≤ X * radius)
    (hF : s * nrm (b - bo) ≤ X * finite) :
    s * nrm (a - b) ≤ X * fullAllowance deviation radius finite := by
  have e : a - b = (a - h) + (h - bo) + (bo - b) := by abel
  have en : nrm (bo - b) = nrm (b - bo) := by
    unfold nrm normSq
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  have h1 := BstLean.Part153.nrm_add_le ((a - h) + (h - bo)) (bo - b)
  have h2 := BstLean.Part153.nrm_add_le (a - h) (h - bo)
  rw [← e, en] at h1
  have h3 := mul_le_mul_of_nonneg_left h1 hs
  have h4 := mul_le_mul_of_nonneg_left h2 hs
  unfold fullAllowance
  linarith

/-- The parameterized TF theorem includes the normalization guard and both norms. -/
theorem full_parallel_transfer {k : ℕ} (a bo b : Fin k → ℝ)
    {s X oracleFull oracleParallel lower upper finite rn : ℝ}
    (hs : 0 ≤ s) (hX : 0 < X) (hrn : 0 < rn) (hlower : 0 < lower)
    (hfinite : 0 ≤ finite) (hFull0 : 0 ≤ oracleFull)
    (hFull : s * nrm (a - bo) ≤ X * oracleFull)
    (hParallel : |(s • (a - bo)) ⬝ᵥ ((nrm bo)⁻¹ • bo)| ≤ X * oracleParallel)
    (hLower : X * rn * lower ≤ s * nrm bo)
    (hUpper : s * nrm bo ≤ X * rn * upper)
    (hFinite : s * nrm (b - bo) ≤ X * finite)
    (hGuard : finite / rn < lower) :
    s ^ 2 * normSq (a - b) ≤ X ^ 2 * (oracleFull + finite) ^ 2 ∧
    |(s • (a - b)) ⬝ᵥ ((nrm b)⁻¹ • b)| ^ 2 ≤
      X ^ 2 * parallelAllowance oracleParallel oracleFull finite lower rn ^ 2 ∧
    X * rn * (lower - finite / rn) ≤ s * nrm b ∧
    s * nrm b ≤ X * rn * (upper + finite / rn) ∧ b ≠ 0 := by
  obtain ⟨hf, hp, hl, hu, hb⟩ := BstLean.Part154.TF_vec a bo b hs hX hrn hlower
    hfinite hFull0 hFull hParallel hLower hUpper hFinite hGuard
  have hf2 := pow_le_pow_left₀ (mul_nonneg hs (nrm_nonneg _)) hf 2
  have hp2 := pow_le_pow_left₀ (abs_nonneg _) hp 2
  rw [mul_pow, mul_pow, nrm_sq] at hf2
  rw [mul_pow] at hp2
  refine ⟨hf2, hp2, hl, hu, ?_⟩
  intro he
  subst b
  simpa [nrm, normSq] using hb

/-- MP's parallel allowance follows from a norm gap and the full vector error. -/
theorem parallel_from_norm_gap {k : ℕ} (a bo : Fin k → ℝ)
    {lower deviation gap : ℝ} (hl : 0 < lower) (hb : lower ≤ nrm bo)
    (hd : nrm (a - bo) ≤ deviation) (hg : |nrm a - nrm bo| ≤ gap) :
    |(a - bo) ⬝ᵥ ((nrm bo)⁻¹ • bo)| ≤
      (1 + deviation / (2 * lower)) * gap + deviation ^ 2 / (2 * lower) := by
  have hb0 : 0 < nrm bo := hl.trans_le hb
  have hd0 : 0 ≤ deviation := (nrm_nonneg _).trans hd
  have hg0 : 0 ≤ gap := (abs_nonneg _).trans hg
  have ht : nrm a ≤ nrm bo + nrm (a - bo) := by
    have h := BstLean.Part153.abs_nrm_sub_le a bo
    linarith [(abs_le.mp h).2]
  have hid : 2 * ((a - bo) ⬝ᵥ bo) = normSq a - normSq bo - normSq (a - bo) := by
    simp only [dotProduct, normSq, Pi.sub_apply]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hid' : 2 * ((a - bo) ⬝ᵥ bo) =
      (nrm a - nrm bo) * (nrm a + nrm bo) - nrm (a - bo) ^ 2 := by
    rw [hid, ← nrm_sq a, ← nrm_sq bo, ← nrm_sq (a - bo)]
    ring
  have habs := abs_sub ((nrm a - nrm bo) * (nrm a + nrm bo)) (nrm (a - bo) ^ 2)
  rw [← hid', abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_mul, abs_of_nonneg (add_nonneg (nrm_nonneg a) (nrm_nonneg bo)),
    abs_of_nonneg (sq_nonneg (nrm (a - bo)))] at habs
  have hp := mul_le_mul hg (show nrm a + nrm bo ≤ 2 * nrm bo + deviation by linarith)
    (add_nonneg (nrm_nonneg a) (nrm_nonneg bo)) hg0
  have hd2 := pow_le_pow_left₀ (nrm_nonneg (a - bo)) hd 2
  have h1 : 2 * |(a - bo) ⬝ᵥ bo| ≤ gap * (2 * nrm bo + deviation) + deviation ^ 2 :=
    habs.trans (add_le_add hp hd2)
  rw [dotProduct_smul, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hb0)]
  have he : (nrm bo)⁻¹ * |(a - bo) ⬝ᵥ bo| = |(a - bo) ⬝ᵥ bo| / nrm bo := by ring
  rw [he]
  have h2 : |(a - bo) ⬝ᵥ bo| / nrm bo ≤
      gap + (deviation * gap + deviation ^ 2) / (2 * nrm bo) := by
    rw [div_le_iff₀ hb0]
    field_simp
    nlinarith only [h1]
  have h3 : (deviation * gap + deviation ^ 2) / (2 * nrm bo) ≤
      (deviation * gap + deviation ^ 2) / (2 * lower) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  refine h2.trans ?_
  calc gap + (deviation * gap + deviation ^ 2) / (2 * nrm bo)
      ≤ gap + (deviation * gap + deviation ^ 2) / (2 * lower) := add_le_add le_rfl h3
    _ = _ := by ring

/-- A parameterized MP mean gap retains the exact variance denominators. -/
theorem MP_mean_gap {rh rb Eh Eb cross varianceH varianceB : ℝ}
    (hrh : 0 < rh) (hrb : 0 < rb) (hEh : 0 ≤ Eh) (hEb : 0 ≤ Eb)
    (hJh : Eh ^ 2 ≤ rh ^ 2) (hJb : Eb ^ 2 ≤ rb ^ 2)
    (hCross : |rh ^ 2 - rb ^ 2| ≤ cross)
    (hVarH : rh ^ 2 - Eh ^ 2 ≤ varianceH)
    (hVarB : rb ^ 2 - Eb ^ 2 ≤ varianceB) :
    |Eh - Eb| ≤ cross / (rh + rb) +
      varianceH / (rh + Eh) + varianceB / (rb + Eb) := by
  have hhr : Eh ≤ rh := by nlinarith
  have hbr : Eb ≤ rb := by nlinarith
  have hR : |rh - rb| ≤ cross / (rh + rb) := by
    rw [le_div_iff₀ (by positivity : 0 < rh + rb)]
    calc
      |rh - rb| * (rh + rb) = |rh ^ 2 - rb ^ 2| := by
        rw [← abs_of_pos (by positivity : 0 < rh + rb), ← abs_mul]
        congr 1
        ring
      _ ≤ cross := hCross
  have hH : rh - Eh ≤ varianceH / (rh + Eh) := by
    rw [le_div_iff₀ (by positivity : 0 < rh + Eh)]
    nlinarith only [hVarH]
  have hB : rb - Eb ≤ varianceB / (rb + Eb) := by
    rw [le_div_iff₀ (by positivity : 0 < rb + Eb)]
    nlinarith only [hVarB]
  have hGap : |Eh - Eb| ≤ |rh - rb| + (rh - Eh) + (rb - Eb) := by
    rw [abs_le]
    have h := abs_le.mp (le_refl |rh - rb|)
    constructor <;> linarith
  exact hGap.trans (add_le_add (add_le_add hR hH) hB)

/-- The original norm deviations give a norm-gap bound without independence. -/
theorem MP_deviation_gap {Ph Pb Eh Eb meanGap devH devB : ℝ}
    (hMean : |Eh - Eb| ≤ meanGap) (hH : |Ph - Eh| ≤ devH)
    (hB : |Pb - Eb| ≤ devB) : |Ph - Pb| ≤ meanGap + devH + devB := by
  have he : Ph - Pb = (Eh - Eb) + (Ph - Eh) + (Eb - Pb) := by ring
  rw [he]
  have h := abs_add_three (Eh - Eb) (Ph - Eh) (Eb - Pb)
  rw [abs_sub_comm Eb Pb] at h
  exact h.trans (add_le_add (add_le_add hMean hH) hB)

#print axioms full_centre_transfer
#print axioms full_parallel_transfer
#print axioms parallel_from_norm_gap
#print axioms MP_mean_gap
#print axioms MP_deviation_gap
end BstLean.Part206
