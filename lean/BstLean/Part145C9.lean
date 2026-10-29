import BstLean.Part145C8

/-!
# Part 145, helper `C9`: the window bound of `κ^{∘4}` and the localized chord

`q = κ(κ(0))`, `Q = κ^{∘6}(0) = κ^{∘4}(q)`, `σ₄ = sig4 = (1 − Q)/(1 − q)`. `κ^{∘4}` is convex and
increasing on `[−1, 1]`. For the window `w = wW = 1 / 5` and the slope
`s_w = (κ^{∘4}(q + w) − Q)/w ≤ sW = 0.3095`:
`|κ^{∘4}(t) − Q| ≤ sW·|t − q|` for `t ≤ q + w`, and `|κ^{∘4}(t) − Q| ≤ σ₄·|t − q|` with
`1 ≤ (t − q)²/w²` for `t > q + w`. (Made by `gen_c9.py`.)

* `k4_window_le`: `κ^{∘4}(q + w) ≤ 0.838995` (four steps of `kappa_le_step`); `sW_le_sig4`.
* **`iter4_window`**: for `t ∈ [−1, 1]`,
  `(κ^{∘4}(t) − Q)² ≤ sW²·(t − q)² + (σ₄² − sW²)·(t − q)⁴/wW²`.
* `chord_loc_gen` (all widths); `pWC n = √(sW²·tau143sC n² + (σ₄² − sW²)·m4C n²/wW²)`;
  **`chord_pW_loc`**: `‖κ^{∘4}(tX) − Q‖₂ ≤ pWC n` at the widths of the Focus, `n ≥ 4096`.
* `eHid_inv`: `eHid (m_W) ≤ 0.026493/n` and `epsW (m_W) ≤ 3.81471e-05/n²` for `n ≥ 4096`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
open BstLean.Part142 BstLean.Part143

/-! ## The window -/

/-- The window of the localized chord. -/
noncomputable def wW : ℝ := 1 / 5

/-- The slope of the secant of `κ^{∘4}` on the window (a certified upper bound). -/
noncomputable def sW : ℝ := 619 / 2000

lemma wW_pos : 0 < wW := by unfold wW; norm_num

lemma sW_pos : 0 < sW := by unfold sW; norm_num

/-- `κ^{∘4}(κ(κ(0)) + wW) ≤ 0.838995`. -/
lemma k4_window_le : kappa^[4] (kappa (kappa 0) + wW) ≤ 167799 / 200000 := by
  have hq0 := kappa2_zero_pos
  have hq1 := kappa2_zero_le
  have h : kappa^[4] (kappa (kappa 0) + wW) =
      kappa (kappa (kappa (kappa (kappa (kappa 0) + wW)))) := rfl
  rw [h]
  have hw : wW = 1 / 5 := rfl
  have m0 : -1 ≤ kappa (kappa 0) + wW ∧ kappa (kappa 0) + wW ≤ 1 := by
    rw [hw]; constructor <;> linarith
  have m1 := kappa_mem m0.1 m0.2
  have m2 := kappa_mem (by linarith [m1.1]) m1.2
  have m3 := kappa_mem (by linarith [m2.1]) m2.2
  have k1 : kappa (kappa (kappa 0) + wW) ≤ 4659 / 6250 :=
    kappa_le_step (a := 2168 / 3125) (r := 720207 / 1000000) (c := 383349 / 500000)
      (by rw [hw]; linarith) (by rw [hw]; linarith)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have k2 : kappa (kappa (kappa (kappa 0) + wW)) ≤ 784497 / 1000000 :=
    kappa_le_step (a := 4659 / 6250) (r := 666573 / 1000000) (c := 210299 / 250000)
      m1.1 k1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have k3 : kappa (kappa (kappa (kappa (kappa 0) + wW))) ≤ 814857 / 1000000 :=
    kappa_le_step (a := 784497 / 1000000) (r := 620133 / 1000000) (c := 901887 / 1000000)
      m2.1 k2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have k4 : kappa (kappa (kappa (kappa (kappa (kappa 0) + wW)))) ≤ 167799 / 200000 :=
    kappa_le_step (a := 814857 / 1000000) (r := 579663 / 1000000) (c := 476243 / 500000)
      m3.1 k3
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  exact k4

/-- `sW ≤ sig4`. -/
lemma sW_le_sig4 : sW ≤ sig4 := by
  have h1 : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have h2 := kappa2_zero_ge
  have h3 := kappa2_zero_le
  unfold sig4 sW
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- **The window bound of `κ^{∘4}` at `q = κ(κ(0))`.** -/
theorem iter4_window : ∀ t ∈ Icc (-1 : ℝ) 1,
    (kappa^[4] t - kappa^[6] 0) ^ 2 ≤ sW ^ 2 * (t - kappa (kappa 0)) ^ 2 +
      (sig4 ^ 2 - sW ^ 2) * (t - kappa (kappa 0)) ^ 4 / wW ^ 2 := by
  intro t ht
  have hG : KGood (kappa^[4]) := kGood_iterate 3
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = kappa (kappa 0) := ⟨_, rfl⟩
  have hq0 : 0 < q := hq ▸ kappa2_zero_pos
  have hq1 : q ≤ 49376 / 100000 := hq ▸ kappa2_zero_le
  have e6 : kappa^[6] 0 = kappa^[4] q := by rw [hq]; rfl
  have hk4 := k4_window_le
  have hQ : 7771 / 10000 ≤ kappa^[4] q := e6 ▸ kappa6_zero_ge'
  have hs := sW_le_sig4
  have hs0 := sW_pos
  have hw0 := wW_pos
  rw [e6, ← hq]
  rw [← hq] at hk4
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = wW := ⟨_, rfl⟩
  rw [← hw] at hk4 hw0 ⊢
  have hwv : w = 1 / 5 := hw
  have hsv : sW = 619 / 2000 := rfl
  have hslope : kappa^[4] (q + w) - kappa^[4] q ≤ sW * w := by
    rw [hsv, hwv]
    rw [hwv] at hk4
    linarith
  have hqm : q ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hqwm : q + w ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by rw [hwv]; linarith⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = t - q := ⟨_, rfl⟩
  rw [← hd]
  have hC : 0 ≤ sig4 ^ 2 - sW ^ 2 := by nlinarith
  have hd4 : 0 ≤ d ^ 4 / w ^ 2 := by positivity
  rcases le_or_gt t (q + w) with h | h
  · -- inside the window: the slope `sW`
    have hin : |kappa^[4] t - kappa^[4] q| ≤ sW * |d| := by
      rcases le_total q t with hqt | hqt
      · have hmono := hG.mono hqm ht hqt
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by rw [hd]; linarith)]
        have hc := hG.conv.2 hqm hqwm (show (0 : ℝ) ≤ (q + w - t) / w from
          div_nonneg (by linarith) hw0.le) (show (0 : ℝ) ≤ (t - q) / w from
          div_nonneg (by linarith) hw0.le) (by field_simp; ring)
        have e : ((q + w - t) / w) • q + ((t - q) / w) • (q + w) = t := by
          simp only [smul_eq_mul]
          field_simp
          ring
        rw [e] at hc
        simp only [smul_eq_mul] at hc
        have h2 := mul_le_mul_of_nonneg_right hc hw0.le
        have e2 : ((q + w - t) / w * kappa^[4] q + (t - q) / w * kappa^[4] (q + w)) * w =
            (q + w - t) * kappa^[4] q + (t - q) * kappa^[4] (q + w) := by
          field_simp
        rw [e2] at h2
        have h3 : (t - q) * (kappa^[4] (q + w) - kappa^[4] q) ≤ (t - q) * (sW * w) :=
          mul_le_mul_of_nonneg_left hslope (by linarith)
        have h4 : (kappa^[4] t - kappa^[4] q) * w ≤ sW * d * w := by
          rw [hd]; linarith
        exact le_of_mul_le_mul_right h4 hw0
      · have hmono := hG.mono ht hqm hqt
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by rw [hd]; linarith)]
        have hL : 0 < q + w - t := by linarith
        have hc := hG.conv.2 ht hqwm (show (0 : ℝ) ≤ w / (q + w - t) from
          div_nonneg hw0.le hL.le) (show (0 : ℝ) ≤ (q - t) / (q + w - t) from
          div_nonneg (by linarith) hL.le) (by field_simp; ring)
        have e : (w / (q + w - t)) • t + ((q - t) / (q + w - t)) • (q + w) = q := by
          simp only [smul_eq_mul]
          field_simp
          ring
        rw [e] at hc
        simp only [smul_eq_mul] at hc
        have h2 := mul_le_mul_of_nonneg_right hc hL.le
        have e2 : (w / (q + w - t) * kappa^[4] t +
            (q - t) / (q + w - t) * kappa^[4] (q + w)) * (q + w - t) =
            w * kappa^[4] t + (q - t) * kappa^[4] (q + w) := by
          field_simp
        rw [e2] at h2
        have h3 : (q - t) * (kappa^[4] (q + w) - kappa^[4] q) ≤ (q - t) * (sW * w) :=
          mul_le_mul_of_nonneg_left hslope (by linarith)
        have h4 : -(kappa^[4] t - kappa^[4] q) * w ≤ sW * -d * w := by
          rw [hd]; linarith
        exact le_of_mul_le_mul_right h4 hw0
    have h5 : (kappa^[4] t - kappa^[4] q) ^ 2 ≤ (sW * |d|) ^ 2 := by
      rw [← sq_abs (kappa^[4] t - kappa^[4] q)]
      exact pow_le_pow_left₀ (abs_nonneg _) hin 2
    rw [mul_pow, sq_abs] at h5
    have h6 : 0 ≤ (sig4 ^ 2 - sW ^ 2) * (d ^ 4 / w ^ 2) := mul_nonneg hC hd4
    have e7 : (sig4 ^ 2 - sW ^ 2) * d ^ 4 / w ^ 2 = (sig4 ^ 2 - sW ^ 2) * (d ^ 4 / w ^ 2) := by
      ring
    rw [e7]
    linarith
  · -- outside the window: the chord `σ₄`
    have hch := iter4_chord ht
    rw [e6, ← hq, ← hd] at hch
    have h5 : (kappa^[4] t - kappa^[4] q) ^ 2 ≤ (sig4 * |d|) ^ 2 := by
      rw [← sq_abs (kappa^[4] t - kappa^[4] q)]
      exact pow_le_pow_left₀ (abs_nonneg _) hch 2
    rw [mul_pow, sq_abs] at h5
    have hdw : w ≤ d := by rw [hd]; linarith
    have h6 : w ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hw0.le hdw 2
    have h7 : d ^ 2 ≤ d ^ 4 / w ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left h6 (sq_nonneg d)
      calc d ^ 2 * w ^ 2 ≤ d ^ 2 * d ^ 2 := this
        _ = d ^ 4 := by ring
    have h8 := mul_le_mul_of_nonneg_left h7 hC
    have e7 : (sig4 ^ 2 - sW ^ 2) * d ^ 4 / w ^ 2 = (sig4 ^ 2 - sW ^ 2) * (d ^ 4 / w ^ 2) := by
      ring
    rw [e7]
    linarith

/-! ## The localized chord -/

/-- **The localized chord, all widths**: from `‖tX − q‖₂ ≤ τ` and `‖(tX − q)²‖₂ ≤ M`. -/
theorem chord_loc_gen {N mW n : ℕ} (hn : 1 ≤ n) {τ M : ℝ}
    (hT : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0)) τ)
    (hM : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        (tX z - kappa (kappa 0)) ^ 2) M) :
    L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        kappa^[4] (tX z) - kappa^[6] 0)
      (√(sW ^ 2 * τ ^ 2 + (sig4 ^ 2 - sW ^ 2) * M ^ 2 / wW ^ 2)) := by
  have hs := sW_le_sig4
  have hs0 := sW_pos
  have hw0 := wW_pos
  have hC : 0 ≤ sig4 ^ 2 - sW ^ 2 := by nlinarith
  have hCw : 0 ≤ (sig4 ^ 2 - sW ^ 2) / wW ^ 2 := by positivity
  have hk4 : Measurable (kappa^[4]) := (continuous_kappa.iterate 4).measurable
  have mtX : Measurable (tX (N := N) (mW := mW) (n := n)) := measurable_tX
  have i1 : Integrable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      sW ^ 2 * (tX z - kappa (kappa 0)) ^ 2) ((lawU2 N).prod (mlpGauss N mW n)) :=
    hT.int_sq.const_mul _
  have i2 : Integrable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      (sig4 ^ 2 - sW ^ 2) / wW ^ 2 * ((tX z - kappa (kappa 0)) ^ 2) ^ 2)
      ((lawU2 N).prod (mlpGauss N mW n)) := hM.int_sq.const_mul _
  have i12 : Integrable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      sW ^ 2 * (tX z - kappa (kappa 0)) ^ 2 +
        (sig4 ^ 2 - sW ^ 2) / wW ^ 2 * ((tX z - kappa (kappa 0)) ^ 2) ^ 2)
      ((lawU2 N).prod (mlpGauss N mW n)) := i1.add i2
  refine L2le.of_sq_le ((hk4.comp mtX).sub measurable_const).aestronglyMeasurable i12
    (fun z => ?_) ?_
  · have h := iter4_window (tX z) (tX_mem hn z)
    have e : (sig4 ^ 2 - sW ^ 2) * (tX z - kappa (kappa 0)) ^ 4 / wW ^ 2 =
        (sig4 ^ 2 - sW ^ 2) / wW ^ 2 * ((tX z - kappa (kappa 0)) ^ 2) ^ 2 := by ring
    rw [e] at h
    exact h
  · rw [integral_add i1 i2, integral_const_mul, integral_const_mul, Real.sq_sqrt (by positivity)]
    have b1 := mul_le_mul_of_nonneg_left hT.le (sq_nonneg sW)
    have b2 := mul_le_mul_of_nonneg_left hM.le hCw
    have e2 : (sig4 ^ 2 - sW ^ 2) * M ^ 2 / wW ^ 2 = (sig4 ^ 2 - sW ^ 2) / wW ^ 2 * M ^ 2 := by
      ring
    rw [e2]
    linarith

/-- **The bound of `‖κ^{∘4}(tX) − κ^{∘6}(0)‖₂` with the window**, at the widths of the Focus. -/
noncomputable def pWC (n : ℕ) : ℝ :=
  √(sW ^ 2 * tau143sC n ^ 2 + (sig4 ^ 2 - sW ^ 2) * m4C n ^ 2 / wW ^ 2)

lemma pWC_nonneg (n : ℕ) : 0 ≤ pWC n := Real.sqrt_nonneg _

/-- **The localized chord**: `‖κ^{∘4}(⟨x(u), x(u′)⟩) − κ^{∘6}(0)‖₂ ≤ pWC n`, `n ≥ 4096`. -/
theorem chord_pW_loc {n : ℕ} (hn : 4096 ≤ n) :
    L2le ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (fun z : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n =>
        kappa^[4] (tX z) - kappa^[6] 0) (pWC n) :=
  chord_loc_gen (by omega) (tX_L2_145C hn) (tX_L4_145C hn)

/-! ## The hidden layers of `W` at the scale `1/n` -/

/-- `eHid (m_W) ≤ 0.026493/n` and `epsW (m_W) ≤ 3.81471e-05/n²` for `n ≥ 4096`. -/
lemma eHid_inv {n : ℕ} (hn : 4096 ≤ n) :
    eHid (mW n) ≤ 26493 / 1000000 * (1 / (n : ℝ)) ∧
      epsW (mW n) ≤ 381471 / 10000000000 * (1 / (n : ℝ)) ^ 2 := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hm := mW_geR hn
  have hm0 : (0 : ℝ) < mW n := by linarith
  have h2 := mW_ge_sq hn
  have hk := kappa_zero_le
  have hk0 : 0 ≤ kappa 0 := (kappa_mem (t := 0) (by norm_num) (by norm_num)).1
  have h6 := Part133.sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 / (n : ℝ) := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; positivity
  rw [← hy]
  have hym : 1 / (mW n : ℝ) ≤ 1 / 262144 * y ^ 2 := by
    rw [hy, div_le_iff₀ hm0]
    have e : 1 / 262144 * (1 / (n : ℝ)) ^ 2 * (mW n : ℝ) = (mW n : ℝ) / (262144 * (n : ℝ) ^ 2) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  have hym0 : 0 ≤ 1 / (mW n : ℝ) := by positivity
  have h25 : 25 / (mW n : ℝ) ≤ 1 / 100000 := by
    rw [div_le_iff₀ hm0]; linarith
  have h250 : 0 ≤ 25 / (mW n : ℝ) := by positivity
  have he : epsW (mW n) = (10 + 25 / (mW n : ℝ)) * (1 / (mW n : ℝ)) := by
    unfold epsW
    field_simp
    ring
  have hE : epsW (mW n) ≤ 381471 / 10000000000 * y ^ 2 := by
    rw [he]
    have := mul_le_mul (by linarith : 10 + 25 / (mW n : ℝ) ≤ 10 + 1 / 100000) hym hym0
      (by norm_num)
    nlinarith [sq_nonneg y]
  have hε0 := epsW_nonneg (mW n)
  have s1 : √(5 * epsW (mW n)) ≤ 34527 / 2500000 * y := by
    refine sqrt_le_of_sq (by positivity) ?_
    nlinarith [sq_nonneg y]
  have hsW : 512 * (n : ℝ) ≤ √(mW n : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    calc (512 * (n : ℝ)) ^ 2 = 262144 * (n : ℝ) ^ 2 := by ring
      _ ≤ _ := h2
  have hiW : 1 / √(mW n : ℝ) ≤ 1 / 512 * y := by
    rw [hy, div_mul_div_comm, mul_one]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsW
  have hiW0 : 0 ≤ 1 / √(mW n : ℝ) := by positivity
  have h5 : 5 / (mW n : ℝ) ≤ 1 / 1000 := by
    rw [div_le_iff₀ hm0]; linarith
  have s3 : √(1 + 5 / (mW n : ℝ)) ≤ 1 + 1 / 1000 := sqrt_le_of_sq (by norm_num) (by linarith)
  have s30 := Real.sqrt_nonneg (1 + 5 / (mW n : ℝ))
  have t2 : √6 * √(1 + 5 / (mW n : ℝ)) / √(mW n : ℝ) ≤
      24495 / 10000 * (1 + 1 / 1000) * (1 / 512 * y) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul h6 s3 s30 (by norm_num)) hiW hiW0 (by norm_num)
  have t3 : (5 * kappa 0 + √6) / √(mW n : ℝ) ≤
      (5 * (31831 / 100000) + 24495 / 10000) * (1 / 512 * y) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hiW hiW0 (by norm_num)
  refine ⟨?_, hE⟩
  unfold eHid
  linarith

end BstLean.Part145

open BstLean.Part145 in
#print axioms iter4_window
open BstLean.Part145 in
#print axioms chord_pW_loc
