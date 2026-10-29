import BstLean.Part228Root
import BstLean.Part228Normalized

/-! The World window supplies the endpoint guards throughout the frontier interval. -/
namespace BstLean.Part228
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157 BstLean.Part161

theorem window_bulk_bounds {n : ℕ} (hn : 4096 ≤ n) (D : Design n) (c : Ret n)
    (h : WINDOW D c) :
    0 < bulkLower D c ∧ bulkLower D c < bulkUpper D c ∧ bulkUpper D c ≤ 7 / 8 := by
  obtain ⟨_, hτ, hθl, hθu⟩ := h
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  let R := √(normSq c.1.2 + n * D.tau0 c ^ 2)
  let a := √(normSq c.1.2)
  have hR : 0 < R := sqrt_pos.mpr (by
    exact add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by linarith) (sq_pos_of_pos hτ)))
  have hR2 : R ^ 2 = normSq c.1.2 + n * D.tau0 c ^ 2 :=
    sq_sqrt (add_nonneg (normSq_nonneg _) (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)))
  have ha2 : a ^ 2 = normSq c.1.2 := sq_sqrt (normSq_nonneg _)
  have ha0 : 0 ≤ a := sqrt_nonneg _
  have haL : (3 / 5 : ℝ) * R ≤ a := by
    apply (pow_le_pow_iff_left₀ (by positivity) ha0 two_ne_zero).mp
    rw [mul_pow, hR2, ha2]
    nlinarith
  have haU : a ≤ (4 / 5 : ℝ) * R := by
    apply (pow_le_pow_iff_left₀ ha0 (by positivity) two_ne_zero).mp
    rw [mul_pow, hR2, ha2]
    nlinarith
  have htU : D.tau0 c ≤ (1 / 80 : ℝ) * R := by
    apply (pow_le_pow_iff_left₀ hτ.le (by positivity) two_ne_zero).mp
    rw [mul_pow, hR2]
    nlinarith [mul_le_mul_of_nonneg_right hnR (sq_nonneg (D.tau0 c))]
  have hAL : (3 / 5 : ℝ) ≤ a / R := (le_div_iff₀ hR).mpr haL
  have hAU : a / R ≤ (4 / 5 : ℝ) := (div_le_iff₀ hR).mpr haU
  have hTU : D.tau0 c / R ≤ (1 / 80 : ℝ) := (div_le_iff₀ hR).mpr htU
  have hT0 : 0 < D.tau0 c / R := div_pos hτ hR
  change 0 < a / R - 6 * D.tau0 c / R ∧
    a / R - 6 * D.tau0 c / R < a / R + 6 * D.tau0 c / R ∧
      a / R + 6 * D.tau0 c / R ≤ 7 / 8
  simp only [mul_div_assoc]
  constructor
  · linarith
  · constructor <;> linarith

theorem window_bulk_frontier {n : ℕ} (hn : 4096 ≤ n) (D : Design n) (c : Ret n)
    (h : WINDOW D c) :
    0 < bulkLower D c ∧ bulkLower D c < bulkUpper D c ∧ bulkUpper D c < 1 := by
  obtain ⟨hlo, hord, hhi⟩ := window_bulk_bounds hn D c h
  exact ⟨hlo, hord, by linarith⟩

/-- The chosen normalized tilts give a domain without an old dimension floor. -/
theorem bulk_domain_of_normalized_tilts {n : ℕ} (hn : 4096 ≤ n) (D : Design n) (c : Ret n)
    (hW : WINDOW D c) {ul uu : ℝ} (hul : ul ≤ 0) (huu : 0 ≤ uu)
    (hlax : 0 < 1 - ul) (huax : 0 < 1 - uu)
    (hltr : 0 < 1 + endpointRatio (bulkLower D c) * ul)
    (hutr : 0 < 1 + endpointRatio (bulkUpper D c) * uu) :
    BulkChernoffDomain D c (ul / (2 * D.tau0 c ^ 2)) (uu / (2 * D.tau0 c ^ 2)) := by
  obtain ⟨hlo, hord, hhi1⟩ := window_bulk_frontier hn D c hW
  have hτ := hW.2.1
  have ht0 : 0 < 2 * D.tau0 c ^ 2 := by positivity
  have hu (u : ℝ) : 2 * (u / (2 * D.tau0 c ^ 2)) * D.tau0 c ^ 2 = u := by
    field_simp
  have hb (b u : ℝ) : 2 * (u / (2 * D.tau0 c ^ 2)) * endpointRatio b * D.tau0 c ^ 2 =
      endpointRatio b * u := by field_simp
  exact ⟨hτ, hlo, lt_trans hord hhi1, lt_trans hlo hord, hhi1,
    div_nonpos_of_nonpos_of_nonneg hul ht0.le, div_nonneg huu ht0.le,
    by rw [hu]; exact hlax, by rw [hb]; exact hltr,
    by rw [hu]; exact huax, by rw [hb]; exact hutr⟩

theorem bulk_domain_explicit {n : ℕ} (hn : 4096 ≤ n) (D : Design n) (c : Ret n)
    (hW : WINDOW D c) :
    BulkChernoffDomain D c (-(8 / √(n : ℝ)) / (2 * D.tau0 c ^ 2))
      ((8 / √(n : ℝ)) / (2 * D.tau0 c ^ 2)) := by
  obtain ⟨hlo, hord, hhiU⟩ := window_bulk_bounds hn D c hW
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsN : (64 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by nlinarith)
  have hr0 : 0 ≤ (8 : ℝ) / √(n : ℝ) := by positivity
  have hrU : (8 : ℝ) / √(n : ℝ) ≤ 1 / 8 := by
    rw [div_le_iff₀ (sqrt_pos.mpr hn0)]
    linarith
  obtain ⟨_, hAlU⟩ := endpointRatio_le_four hlo.le (hord.le.trans hhiU)
  obtain ⟨hAu0, _⟩ := endpointRatio_le_four (lt_trans hlo hord).le hhiU
  have hprod : endpointRatio (bulkLower D c) * (8 / √(n : ℝ)) ≤ 1 / 2 := by
    calc _ ≤ 4 * (8 / √(n : ℝ)) := mul_le_mul_of_nonneg_right hAlU hr0
      _ ≤ 4 * (1 / 8) := mul_le_mul_of_nonneg_left hrU (by norm_num)
      _ = _ := by norm_num
  exact bulk_domain_of_normalized_tilts hn D c hW (neg_nonpos.mpr hr0) hr0
    (by linarith) (by linarith) (by rw [mul_neg]; linarith) (by positivity)

noncomputable def frontierTailRoot {n : ℕ} (D : Design n) (c : Ret n) : ℝ :=
  bulkTailRoot D c (-(8 / √(n : ℝ)) / (2 * D.tau0 c ^ 2))
    ((8 / √(n : ℝ)) / (2 * D.tau0 c ^ 2))

theorem replacement_root_frontier {n : ℕ} (hn : 4096 ≤ n) (D : Design n) (t : ℝ) (c : Ret n)
    (hW : WINDOW D c) (d : SplitData n) {ε δ slow hfl hb : ℝ}
    (hF : FLUCT_chi_hyp D c d ε δ slow hfl) (hB : BIAS_hyp D c d hb) :
    |√(QStand D t c) - √(qTilde D t c)| ≤ hfl + hb + frontierTailRoot D c :=
  repla_root_of_split (by omega) D t c hW.1 hW.2.1 d (fluct_of_chi D t c d hF) hB
    (tail_hyp_chernoff D c (bulk_domain_explicit hn D c hW))

/-- A selected certified block supplies the actual replacement tail price. -/
theorem replacement_root_block {n : ℕ} (hn : 2 ≤ n) (D : Design n) (t : ℝ) (c : Ret n)
    (hc : c.1.2 ≠ 0) (d : SplitData n) {ε δ slow hfl hb : ℝ}
    (hF : FLUCT_chi_hyp D c d ε δ slow hfl) (hB : BIAS_hyp D c d hb)
    (B : LatitudeBlock n (√(normSq c.1.2)) (D.tau0 c) (bulkLower D c) (bulkUpper D c)) :
    |√(QStand D t c) - √(qTilde D t c)| ≤ hfl + hb + B.root := by
  have hT : TAIL_hyp D c B.mass := B.mass_bound
  exact repla_root_of_split hn D t c hc B.tau_pos d (fluct_of_chi D t c d hF) hB hT

end BstLean.Part228
