import BstLean.Part201ConstC

/-! Part 201: the existing series and perturbation proofs with dimension guards from 4096. -/

namespace BstLean.Part201
open Real Set
open BstLean.Part130 BstLean.Part159
open BstLean.Part137 (cN q1)
open BstLean.Part140 (kap1)
open BstLean.Part141 (cN_nonneg cN_le_half)
open BstLean.Part157 (cNt piT rNt kapT Tkap QTsum)

theorem kapT_close {n : ℕ} (hn : 4096 ≤ n) :
    |kapT n - kap1 (2 * n)| ≤
      2 * (3 / (10 ^ 24 * (n : ℝ) ^ 2)) + 1 / (10 ^ 23 * (n : ℝ) ^ 2) +
        1 / (10 ^ 5 * (n : ℝ) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d2
  -- `r`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = cN (2 * n) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; exact cN_nonneg _
  have hc1 : c ≤ 1 / 2 := by rw [hc]; exact cN_le_half (by omega)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 2 * (2 * (n : ℝ)) * c ^ 2 := ⟨_, rfl⟩
  have hq : q1 (e0 (2 * n)) = r := by
    rw [q1_eq_cN (by omega), hNcast, hr, hc]
  obtain ⟨hr1, hr2strict⟩ := BstLean.Part201.rN_even_window hn
  have hre : 4 * (n : ℝ) * cN (2 * n) ^ 2 = r := by rw [hr, hc]; ring
  rw [hre] at hr1 hr2strict
  have hr2 : r ≤ 31835 / 100000 := hr2strict.le
  -- `r̃`
  have hcl := cNt_close hn1
  rw [← hc] at hcl
  obtain ⟨ct, hct⟩ : ∃ ct : ℝ, ct = cNt n := ⟨_, rfl⟩
  rw [← hct] at hcl
  obtain ⟨-, hcw⟩ := cN_even_window hn
  rw [← hc] at hcw
  have hcn : c ^ 2 * (n : ℝ) ≤ 8 / 100 := by
    rw [le_div_iff₀ (by positivity)] at hcw
    linarith only [hcw]
  obtain ⟨rt, hrt⟩ : ∃ rt : ℝ, rt = rNt n := ⟨_, rfl⟩
  have hrte : rt = 2 * (2 * (n : ℝ)) * ct ^ 2 := by rw [hrt, hct]; rfl
  have hdr : |rt - r| ≤ 3 / (10 ^ 24 * (n : ℝ) ^ 2) := by
    have e : rt - r = 2 * (2 * (n : ℝ)) * ((ct - c) * (ct + c)) := by rw [hrte, hr]; ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * (2 * (n : ℝ))), abs_mul]
    have hsm : c / (3 * 10 ^ 23 * (n : ℝ) ^ 2) ≤ c / 100 :=
      div_le_div_of_nonneg_left hc0 (by norm_num) (by nlinarith)
    have h1 : |ct + c| ≤ 201 / 100 * c := by
      have h2 := abs_add_le (ct - c) (2 * c)
      have e2 : ct - c + 2 * c = ct + c := by ring
      rw [e2, abs_of_nonneg (by linarith only [hc0] : (0 : ℝ) ≤ 2 * c)] at h2
      linarith only [h2, hcl, hsm]
    have h3 : |ct - c| * |ct + c| ≤ c / (3 * 10 ^ 23 * (n : ℝ) ^ 2) * (201 / 100 * c) :=
      mul_le_mul hcl h1 (abs_nonneg _) (by positivity)
    have h4 : 2 * (2 * (n : ℝ)) * (c / (3 * 10 ^ 23 * (n : ℝ) ^ 2) * (201 / 100 * c)) ≤
        3 / (10 ^ 24 * (n : ℝ) ^ 2) := by
      have e3 : 2 * (2 * (n : ℝ)) * (c / (3 * 10 ^ 23 * (n : ℝ) ^ 2) * (201 / 100 * c)) =
          (c ^ 2 * (n : ℝ)) * (804 / 100 / (3 * 10 ^ 23)) / (n : ℝ) ^ 2 := by
        field_simp
        ring
      rw [e3, div_le_div_iff₀ (by positivity) (by positivity)]
      have h5 : c ^ 2 * (n : ℝ) * (804 / 100 / (3 * 10 ^ 23)) ≤
          8 / 100 * (804 / 100 / (3 * 10 ^ 23)) :=
        mul_le_mul_of_nonneg_right hcn (by norm_num)
      have h6 : (8 : ℝ) / 100 * (804 / 100 / (3 * 10 ^ 23)) ≤ 3 / 10 ^ 24 := by norm_num
      have hn2pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      nlinarith
    exact (mul_le_mul_of_nonneg_left h3 (by positivity)).trans h4
  have hdrs : 3 / (10 ^ 24 * (n : ℝ) ^ 2) ≤ 1 / 10 ^ 23 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_pos hnpos hnpos]
  obtain ⟨hrta, hrtb⟩ := abs_le.mp hdr
  have hrt1 : 316 / 1000 ≤ rt := by
    have : (1 : ℝ) / 10 ^ 23 ≤ 1 / 1000 := by norm_num
    linarith
  have hrt2 : rt ≤ 3184 / 10000 := by
    have : (1 : ℝ) / 10 ^ 23 ≤ 5 / 100000 := by norm_num
    linarith
  -- `π̃`
  have hdp := piT_close hn1
  obtain ⟨Pt, hPt⟩ : ∃ Pt : ℝ, Pt = piT n := ⟨_, rfl⟩
  rw [← hPt] at hdp
  have hdps : 1 / (10 ^ 23 * (n : ℝ) ^ 2) ≤ 1 / 10 ^ 23 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨hPa, hPb⟩ := abs_le.mp hdp
  have hPt1 : 313 / 100 ≤ Pt := by
    have : (1 : ℝ) / 10 ^ 23 ≤ 1 / 1000 := by norm_num
    linarith
  have hPt2 : Pt ≤ 316 / 100 := by
    have : (1 : ℝ) / 10 ^ 23 ≤ 1 / 1000 := by norm_num
    linarith
  have hr0 : (0 : ℝ) ≤ r := le_trans (by norm_num) hr1
  have hrh : r ≤ 1 / 2 := hr2.trans (by norm_num)
  have hrt0 : (0 : ℝ) ≤ rt := le_trans (by norm_num) hrt1
  have hrth : rt ≤ 1 / 2 := hrt2.trans (by norm_num)
  have hrtlt : rt < 1 := lt_of_le_of_lt hrt2 (by norm_num)
  -- the square roots and the inverse sines
  have hS := sqrt_lip (a := rt) (b := r) hrt0 hrth hr0 hrh
  have has := arcsin_lip (a := 0) (b := r) le_rfl hr0 hrh
  rw [Real.arcsin_zero, sub_zero, sub_zero] at has
  have hast : |arcsin rt - arcsin r| ≤ 2 * (3 / (10 ^ 24 * (n : ℝ) ^ 2)) := by
    rcases le_total r rt with h | h
    · obtain ⟨a1, a2⟩ := arcsin_lip (a := r) (b := rt) hr0 h hrth
      rw [abs_of_nonneg a1]
      have h5 : rt - r ≤ 3 / (10 ^ 24 * (n : ℝ) ^ 2) := (le_abs_self _).trans hdr
      linarith only [a2, h5]
    · obtain ⟨a1, a2⟩ := arcsin_lip (a := rt) (b := r) hrt0 h hrh
      rw [abs_sub_comm, abs_of_nonneg a1]
      have h5 : r - rt ≤ 3 / (10 ^ 24 * (n : ℝ) ^ 2) := by
        have h6 := neg_abs_le (rt - r)
        linarith only [h6, hdr]
      linarith only [a2, h5]
  -- the partial sum
  obtain ⟨hT1, hT2⟩ := Tkap_spec hn1
  obtain ⟨q1', q2'⟩ := QTsum_err hT1 (v := rt) hrt0 hrtlt
  have hrt2sq : rt ^ 2 ≤ 1014 / 10000 :=
    (pow_le_pow_left₀ hrt0 hrt2 2).trans (by norm_num)
  have htail : rt * (rt ^ 2) ^ Tkap n / (1 - rt ^ 2) ≤ 1 / (10 ^ 5 * (n : ℝ) ^ 2) := by
    refine le_trans ?_ hT2
    have h1 : (rt ^ 2) ^ Tkap n ≤ (1014 / 10000 : ℝ) ^ Tkap n :=
      pow_le_pow_left₀ (sq_nonneg _) hrt2sq _
    have h2 : (0 : ℝ) < 1 - rt ^ 2 := by linarith only [hrt2sq]
    rw [div_le_iff₀ h2]
    have h3 : rt ≤ 355 / 1000 * (1 - rt ^ 2) := by linarith only [hrt2sq, hrt2]
    have hp : (0 : ℝ) ≤ (1014 / 10000 : ℝ) ^ Tkap n := by positivity
    have hp2 : (0 : ℝ) ≤ (rt ^ 2) ^ Tkap n := by positivity
    calc rt * (rt ^ 2) ^ Tkap n ≤ 355 / 1000 * (1 - rt ^ 2) * (rt ^ 2) ^ Tkap n :=
          mul_le_mul_of_nonneg_right h3 hp2
      _ ≤ 355 / 1000 * (1 - rt ^ 2) * (1014 / 10000 : ℝ) ^ Tkap n :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 355 / 1000 * (1014 / 10000 : ℝ) ^ Tkap n * (1 - rt ^ 2) := by ring
  have hQabs : |QTsum (Tkap n) rt - arcsin rt| ≤ 1 / (10 ^ 5 * (n : ℝ) ^ 2) := by
    rw [abs_sub_comm, abs_of_nonneg q1']
    exact q2'.trans htail
  have hQ0 := QTsum_nonneg (Tkap n) (v := rt) hrt0
  have hastle : arcsin rt ≤ 1 := by
    obtain ⟨-, a2⟩ := arcsin_lip (a := 0) (b := rt) le_rfl hrt0 hrth
    rw [Real.arcsin_zero, sub_zero, sub_zero] at a2
    linarith only [a2, hrth]
  have hQ2 : QTsum (Tkap n) rt ≤ 2 := by linarith only [q1', hastle]
  -- assemble
  have hS1 : (0 : ℝ) ≤ √(1 - r ^ 2) := Real.sqrt_nonneg _
  have hS2 : √(1 - r ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith only [sq_nonneg r]
  have key := kappa_pert (r := r) (rt := rt) (P := π) (Pt := Pt) (Q := QTsum (Tkap n) rt)
    (S := √(1 - r ^ 2)) (St := √(1 - rt ^ 2)) (as := arcsin r) (ast := arcsin rt)
    (dr := 3 / (10 ^ 24 * (n : ℝ) ^ 2)) (dp := 1 / (10 ^ 23 * (n : ℝ) ^ 2))
    (dq := 1 / (10 ^ 5 * (n : ℝ) ^ 2))
    hr0 hrh (by linarith only [hpi1]) (by linarith only [hpi2]) hPt1 hPt2 hS1 hS2 has.1
    (by linarith only [has.2, hrh])
    hQ0 hQ2 hdr hdp (hS.trans hdr) hQabs hast
  have e1 : kapT n = (√(1 - rt ^ 2) + rt * (Pt / 2 + QTsum (Tkap n) rt)) / Pt := by
    rw [hrt, hPt]; rfl
  have e2 : kap1 (2 * n) = (√(1 - r ^ 2) + r * (π / 2 + arcsin r)) / π := by
    unfold kap1
    rw [hq, kappa_arcsin]
  rw [e1, e2]
  exact key

theorem kapT_close_strong {n : ℕ} (hn : 4096 ≤ n) :
    |kapT n - kap1 (2 * n)| ≤ 2 / (10 ^ 5 * (n : ℝ) ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk := kapT_close hn
  refine hk.trans (le_of_eq_of_le (b := (2 * (3 / 10 ^ 24) + 1 / 10 ^ 23 + 1 / 10 ^ 5) /
    (n : ℝ) ^ 2) ?_ ?_)
  · field_simp
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hn2pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    nlinarith

/-- The hypothesis `ConstK n` holds for every dimension from 4096. -/
theorem constK {n : ℕ} (hn : 4096 ≤ n) : ConstK n := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hm2 : mW n ≤ n ^ 4 := by
    rw [mW_le_iff]
    calc n ^ 7 ≤ n ^ 7 * n := Nat.le_mul_of_pos_right _ (by omega)
      _ = (n ^ 4) ^ 2 := by ring
  have hm2' : (mW n : ℝ) ≤ (n : ℝ) ^ 4 := by exact_mod_cast hm2
  have hm0 : (0 : ℝ) ≤ mW n := Nat.cast_nonneg _
  have hB := kapT_close_strong hn
  have hsq : (kapT n - kap1 (2 * n)) ^ 2 ≤ (2 / (10 ^ 5 * (n : ℝ) ^ 2)) ^ 2 := by
    rw [← sq_abs (kapT n - kap1 (2 * n))]
    exact pow_le_pow_left₀ (abs_nonneg _) hB 2
  unfold ConstK
  have h1 : (kapT n - kap1 (2 * n)) ^ 2 * (mW n : ℝ) ≤
      (2 / (10 ^ 5 * (n : ℝ) ^ 2)) ^ 2 * (n : ℝ) ^ 4 :=
    mul_le_mul hsq hm2' hm0 (sq_nonneg _)
  refine h1.trans (le_of_eq_of_le (b := (4 : ℝ) / 10 ^ 10) ?_ (by norm_num))
  field_simp
  norm_num


end BstLean.Part201
#print axioms BstLean.Part201.kapT_close
#print axioms BstLean.Part201.constK
#print axioms BstLean.Part201.kapT_close_strong
