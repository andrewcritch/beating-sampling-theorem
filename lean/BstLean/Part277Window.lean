import BstLean.Part263WorldWindow

/-! Part 277, window: the World window `[.46, a(n0)]` on a base dimension `n0 ≥ 8000`.
The top `windowTopP R` is an explicit rational function of a rational `R` with `12 ≤ R² n0`
(`R` stands for an upper bound of `√(12/n0)`). -/
namespace BstLean.Part277
open Real Set BstLean.Part263

/-- Top of the World noise window, as a function of an upper bound `R` for `√(12/n0)`. -/
noncomputable def windowTopP (R : ℝ) : ℝ :=
  (202831 / 100000 - 1) / ((1 - 2 * R) + (202831 / 100000 - 1))

theorem noise_upper_leP {n0 n : ℕ} (hn : n0 ≤ n) (h8 : 8000 ≤ n0) {R : ℝ}
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1 / 2) (hR : 12 ≤ R ^ 2 * n0) :
    BstLean.Part227.noiseUpper n (202831 / 100000) ≤ windowTopP R := by
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hroot : √(12 / (n : ℝ)) ≤ R := by
    apply sqrt_le_iff.mpr
    refine ⟨hR0, ?_⟩
    apply (div_le_iff₀ hnpos).mpr
    exact hR.trans (mul_le_mul_of_nonneg_left hnn (sq_nonneg R))
  have hden : 0 < (1 - 2 * R) + (202831 / 100000 - 1) := by linarith
  unfold BstLean.Part227.noiseUpper windowTopP
  exact div_le_div_of_nonneg_left (by norm_num) hden (by linarith)

/-- A grid on the window `[.46, a]` with a parameter top. `a` is any cap of `windowTopP R`. -/
noncomputable def worldGridP {n0 n : ℕ} (hn : n0 ≤ n) (h8 : 8000 ≤ n0) {R a : ℝ}
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1 / 2) (hR : 12 ≤ R ^ 2 * n0)
    (ha : windowTopP R ≤ a) (top : ℝ) (htop : 46 / 100 < top)
    (hlower : noiseNode top 10 < (472080 / 10 ^ 6 : ℝ))
    (hupper : a < noiseNode top 53) : Grid where
  top := top
  worldLower := BstLean.Part227.noiseLower (202225 / 100000)
  worldUpper := BstLean.Part227.noiseUpper n (202831 / 100000)
  top_pos := htop
  lower_node := hlower.trans_le (le_trans (by norm_num) BstLean.Part250.noiselo.1)
  upper_node := ((noise_upper_leP hn h8 hR0 hR1 hR).trans ha).trans_lt hupper

theorem worldGridP_domain {n0 n : ℕ} (hn : n0 ≤ n) (h8 : 8000 ≤ n0) {R a : ℝ}
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1 / 2) (hR : 12 ≤ R ^ 2 * n0)
    (ha : windowTopP R ≤ a) (top : ℝ) (htop : 46 / 100 < top)
    (hlower : noiseNode top 10 < (472080 / 10 ^ 6 : ℝ))
    (hupper : a < noiseNode top 53) :
    Icc (worldGridP hn h8 hR0 hR1 hR ha top htop hlower hupper).worldLower
      (worldGridP hn h8 hR0 hR1 hR ha top htop hlower hupper).worldUpper =
    Icc (BstLean.Part227.noiseLower (202225 / 100000))
      (BstLean.Part227.noiseUpper n (202831 / 100000)) := rfl

/-! Instances. -/

theorem windowTop_8000_le : windowTopP (3873 / 10 ^ 5) ≤ (527109 / 10 ^ 6 : ℝ) := by
  unfold windowTopP; norm_num
theorem windowTop_11883_le : windowTopP (31779 / 10 ^ 6) ≤ (523380 / 10 ^ 6 : ℝ) := by
  unfold windowTopP; norm_num
theorem windowTop_12000_le : windowTopP (31623 / 10 ^ 6) ≤ (523296 / 10 ^ 6 : ℝ) := by
  unfold windowTopP; norm_num
theorem windowTop_12225_le : windowTopP (31331 / 10 ^ 6) ≤ (523141 / 10 ^ 6 : ℝ) := by
  unfold windowTopP; norm_num

theorem world_upper_8000 {n : ℕ} (hn : 8000 ≤ n) :
    BstLean.Part227.noiseUpper n (202831 / 100000) ≤ (527109 / 10 ^ 6 : ℝ) :=
  (noise_upper_leP hn le_rfl (R := 3873 / 10 ^ 5) (by norm_num) (by norm_num) (by norm_num)).trans
    windowTop_8000_le

theorem world_upper_11883 {n : ℕ} (hn : 11883 ≤ n) :
    BstLean.Part227.noiseUpper n (202831 / 100000) ≤ (523380 / 10 ^ 6 : ℝ) :=
  (noise_upper_leP hn (by norm_num) (R := 31779 / 10 ^ 6) (by norm_num) (by norm_num)
    (by norm_num)).trans windowTop_11883_le

theorem world_upper_12000 {n : ℕ} (hn : 12000 ≤ n) :
    BstLean.Part227.noiseUpper n (202831 / 100000) ≤ (523296 / 10 ^ 6 : ℝ) :=
  (noise_upper_leP hn (by norm_num) (R := 31623 / 10 ^ 6) (by norm_num) (by norm_num)
    (by norm_num)).trans windowTop_12000_le

/-- The old lemma `Part263.world_upper_le`, as an instance (same constant). -/
theorem world_upper_12225 {n : ℕ} (hn : 12225 ≤ n) :
    BstLean.Part227.noiseUpper n (202831 / 100000) ≤ (523141 / 10 ^ 6 : ℝ) :=
  (noise_upper_leP hn (by norm_num) (R := 31331 / 10 ^ 6) (by norm_num) (by norm_num)
    (by norm_num)).trans windowTop_12225_le

/-- Each top is below the old cap `.528` and the cap `.532`. -/
theorem world_upper_8000_le_528 {n : ℕ} (hn : 8000 ≤ n) :
    BstLean.Part227.noiseUpper n (202831 / 100000) ≤ (528 / 1000 : ℝ) :=
  (world_upper_8000 hn).trans (by norm_num)

end BstLean.Part277
