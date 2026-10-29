import BstLean.Part151VAprob

/-!
# Part 151, Proposition VA (b), stage (c), second file: the probability of each bad event

Each event of `Part151VAprob` is paid in its conditional step:
`prob_X12`, `prob_X3` (the hypotheses on the `A` stage), `prob_ON` (`2e^{−u_F²/2}`),
`prob_Tm`, `prob_FE`, `prob_JU` (`chF n δ` each; `θF` integrated), `prob_s` (`e^{−L_c}`; `η`
integrated), `prob_U` (`2e^{−L_c}`; `A₃` integrated).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part132 (nrm nrm_sq nrm_nonneg)
open BstLean.Part134 (lam res sig)
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part139 (gamK)
open BstLean.Part149 (thA tauOutOf measurable_thA)
open BstLean.Part150 (CMap)
open BstLean.Part152 (gaussConc_mat_upper_sharp)

section probs

variable {k n : ℕ} {bh : CMap n}

lemma wX_A3 (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (A₃ A₃' : Matrix (Fin n) (Fin (mA n)) ℝ)
    (θF : HidParam n (mF n)) (k : ℕ) (η : Fin k → Fin n → ℝ) (c : Fin n → ℝ) :
    wX bh W (A₁, A₂, A₃) θF k η c = wX bh W (A₁, A₂, A₃') θF k η c := rfl

lemma cAv_A3 (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (A₃ : Matrix (Fin n) (Fin (mA n)) ℝ) :
    cAv bh W (A₁, A₂, A₃) = A₃.mulVec (bh (W, (A₁, A₂))) := rfl

theorem prob_X12 {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))}
    (h : MeasurableSet X12) {p12 : ℝ}
    (hp : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ p12) :
    (fixP k n).real (B12 k X12) ≤ p12 := by
  have e := prob_marg (fixP k n) _ m12' (fix_map_W12 (k := k) (n := n)) h.compl
  exact (le_of_eq e).trans hp

theorem prob_X3 {X3 : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n)}
    (h : MeasurableSet X3) {p3 : ℝ}
    (hp : ((mlpGauss (2 * n) (mW n) n).prod (mlpGauss n (mA n) n)).real X3ᶜ ≤ p3) :
    (fixP k n).real (B3 k X3) ≤ p3 := by
  have e := prob_marg (fixP k n) _ (mW'.prodMk mA') (fix_map_WA (k := k) (n := n)) h.compl
  exact (le_of_eq e).trans hp

theorem prob_ON (hn : 1 ≤ n) {uF : ℝ} (huF : 0 ≤ uF) :
    (fixP k n).real (BON (n := n) k uF) ≤ 2 * Real.exp (-uF ^ 2 / 2) := by
  refine prob_slice (fixP k n) _ _ measurable_eTh' measurable_eTh fix_map_theta eTh_eTh'
    (BON_meas uF) (by positivity) (fun x => ?_)
  exact EON_prob hn (mF_pos hn) huF

lemma chF_nonneg (n : ℕ) (δ : ℝ) : 0 ≤ chF n δ := by unfold chF; positivity

theorem prob_Tm (hn : 1 ≤ n) (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h : MeasurableSet X12)
    (hb : ∀ x ∈ X12, bh x ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    (fixP k n).real (BTm k bh X12 δ) ≤ chF n δ := by
  refine prob_slice (fixP k n) _ _ measurable_eTh' measurable_eTh fix_map_theta eTh_eTh'
    (BTm_meas hbh h δ) (chF_nonneg n δ) (fun x => ?_)
  by_cases hx : (x.1.1, thA x.1.2) ∈ X12
  · have hb' : cenB bh x.1.1 x.1.2 ≠ 0 := hb _ hx
    refine (measureReal_mono ?_).trans (lemmaTm bh x.1.1 x.1.2 hn hb' hδ hδ)
    intro θ hθ
    exact hθ.2
  · have hemp : {y : HidParam n (mF n) | eTh (x, y) ∈ BTm k bh X12 δ} ⊆ ∅ :=
      fun θ hθ => hx hθ.1
    exact (measureReal_mono hemp).trans (by simpa using chF_nonneg n δ)

theorem prob_FE (hn : 1 ≤ n) (hbh : Measurable bh) {δ : ℝ} (hδ : 0 < δ) :
    (fixP k n).real (BFE k bh δ) ≤ chF n δ := by
  refine prob_slice (fixP k n) _ _ measurable_eTh' measurable_eTh fix_map_theta eTh_eTh'
    (BFE_meas hbh δ) (chF_nonneg n δ) (fun x => ?_)
  exact lemmaFE_gauss hn (mF_pos hn) (cAv bh x.1.1 x.1.2) (sigP bh x.1.1 x.1.2) hδ hδ

theorem prob_JU (hn : 1 ≤ n) (hbh : Measurable bh) {δ : ℝ} (hδ : 0 < δ) :
    (fixP k n).real (BJU k bh δ) ≤ chF n δ := by
  refine prob_slice (fixP k n) _ _ measurable_eTh' measurable_eTh fix_map_theta eTh_eTh'
    (BJU_meas hbh δ) (chF_nonneg n δ) (fun x => ?_)
  exact lemmaU_JU bh x.1.1 x.1.2.1 x.1.2.2.1 hn (cAv bh x.1.1 x.1.2) hδ hδ

lemma ellS_pos (hn : 1 ≤ n) (hk : 1 ≤ k) {LF : ℝ} (hLF : 0 < LF) : 0 < ellS n k LF := by
  have hmF : 1 ≤ mF n := mF_pos hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) < mF n := by exact_mod_cast hmF
  unfold ellS
  exact Real.sqrt_pos.mpr (by positivity)

lemma tauOutOf_sq_le (hn : 1 ≤ n) {m : ℕ} (b : Fin m → ℝ) : tauOutOf n b ^ 2 ≤ 2 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold tauOutOf
  rw [Real.sq_sqrt (le_max_left _ _)]
  refine max_le (by positivity) ?_
  have : 0 ≤ 2 / (m : ℝ) * normSq b := mul_nonneg (by positivity) (normSq_nonneg _)
  linarith

theorem prob_s (hn : 1 ≤ n) (hk : 1 ≤ k) (hbh : Measurable bh) {uF Lc : ℝ} (huF : 0 ≤ uF)
    (hLc : 0 ≤ Lc) : (fixP k n).real (Bs k bh uF Lc) ≤ Real.exp (-Lc) := by
  have hid : (fixP k n).map (id : Fix k n → Fix k n) =
      ((mlpGauss (2 * n) (mW n) n).prod ((mlpGauss n (mA n) n).prod (hidGauss n (mF n)))).prod
        (gamK k n) := by
    rw [Measure.map_id]; rfl
  refine prob_slice (fixP k n) _ _ measurable_id measurable_id hid (fun _ => rfl)
    (Bs_meas hbh uF Lc) (Real.exp_pos _).le (fun x => ?_)
  set θ := x.2.2 with hθd
  set c := cAv bh x.1 x.2.1 with hc
  set σ := sigP bh x.1 x.2.1 with hσ
  by_cases hθ : θ ∈ EON n (mF n) uF
  swap
  · have hemp : {y : Fin k → Fin n → ℝ | id (x, y) ∈ Bs k bh uF Lc} ⊆ ∅ := fun η hη => hθ hη.1
    exact (measureReal_mono hemp).trans (by simpa using (Real.exp_pos (-Lc)).le)
  have hL0 := LFc_pos hn huF
  have hL : ∀ y y', normSq (hid2 θ.1 θ.2 y - hid2 θ.1 θ.2 y') ≤ LFc n uF ^ 2 * normSq (y - y') :=
    fun y y' => lip_of_EON hθ y y'
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hmF : 1 ≤ mF n := mF_pos hn
  have hm0 : (0 : ℝ) < mF n := by exact_mod_cast hmF
  have hell := ellS_pos (k := k) hn hk hL0
  have hσ2 : σ ^ 2 ≤ 2 / (n : ℝ) := tauOutOf_sq_le hn _
  have hcoef : √(2 / (mF n : ℝ)) * LFc n uF * |σ| / √(k : ℝ) ≤ ellS n k (LFc n uF) := by
    unfold ellS
    refine Real.le_sqrt_of_sq_le ?_
    have hsk : √(k : ℝ) ^ 2 = k := Real.sq_sqrt hk0.le
    have hsm : √(2 / (mF n : ℝ)) ^ 2 = 2 / (mF n : ℝ) := Real.sq_sqrt (by positivity)
    rw [div_pow, mul_pow, mul_pow, hsk, hsm, sq_abs]
    refine div_le_div_of_nonneg_right ?_ hk0.le
    exact mul_le_mul_of_nonneg_left hσ2 (by positivity)
  have hlip : ∀ M M' : Matrix (Fin k) (Fin n) ℝ,
      |Ts θ c σ k M - Ts θ c σ k M'| ≤
        ellS n k (LFc n uF) * √(∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
    intro M M'
    refine (lemmaSA_lip θ c σ hk hL0.le hL M M').trans ?_
    exact mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
  have conc := gaussConc_mat_upper_sharp (m := k) (k := n)
    (g := fun M : Matrix (Fin k) (Fin n) ℝ => Ts θ c σ k M) hell.le hlip (v := 1) (by norm_num)
    (t := uS n k (LFc n uF) Lc) (uS_nonneg _ _ _ _)
  rw [one_mul, ← gamK_eq_gaussMat] at conc
  have e : Real.exp (-uS n k (LFc n uF) Lc ^ 2 / (2 * ellS n k (LFc n uF) ^ 2)) =
      Real.exp (-Lc) := by
    unfold uS
    exact exp_paper hLc hell
  rw [e] at conc
  refine (measureReal_mono ?_).trans conc
  intro η hη
  have h2 := hη.2
  have h3 := Ts_mean_le θ c σ hk
  show ∫ M, Ts θ c σ k M ∂gamK k n + uS n k (LFc n uF) Lc ≤ Ts θ c σ k η
  have h2' : √(2 / (mF n : ℝ) * ((∫ γ, normSq (zS θ c σ γ) ∂stdGauss (Fin n)) / k)) +
      uS n k (LFc n uF) Lc ≤ Ts θ c σ k η := h2
  linarith

theorem prob_U (hn : 1 ≤ n) (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h : MeasurableSet X12)
    (hb : ∀ x ∈ X12, bh x ≠ 0) {Mr : ℝ} (hMr0 : 0 < Mr)
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 → CrOK bh W A₁ A₂ Mr) {uF Lc : ℝ} (huF : 0 ≤ uF) (hLc : 0 ≤ Lc) :
    (fixP k n).real (BU k bh X12 uF Mr Lc) ≤ 2 * Real.exp (-Lc) := by
  refine prob_slice (fixP k n) _ _ measurable_eA3' measurable_eA3 fix_map_A3 eA3_eA3'
    (BU_meas hbh h uF Mr Lc) (by positivity) (fun x => ?_)
  set W := x.1.1 with hW
  set A₁ := x.1.2.1.1 with hA₁
  set A₂ := x.1.2.1.2 with hA₂
  set θ := x.1.2.2 with hθd
  set η := x.2 with hηd
  by_cases hx : (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12
  swap
  · have hemp : {y : Matrix (Fin n) (Fin (mA n)) ℝ | eA3 (x, y) ∈ BU k bh X12 uF Mr Lc} ⊆ ∅ :=
      fun A₃ hA => hx hA.1
    exact (measureReal_mono hemp).trans (by simp; positivity)
  by_cases hθ : θ ∈ EON n (mF n) uF
  swap
  · have hemp : {y : Matrix (Fin n) (Fin (mA n)) ℝ | eA3 (x, y) ∈ BU k bh X12 uF Mr Lc} ⊆ ∅ :=
      fun A₃ hA => hθ hA.2.1
    exact (measureReal_mono hemp).trans (by simp; positivity)
  have hb' : bh (W, (A₁, A₂)) ≠ 0 := hb _ hx
  have hMr : CrOK bh W A₁ A₂ Mr := hCr W A₁ A₂ hx
  have hL0 := LFc_pos hn huF
  have hLF : ∀ y y', normSq (hid2 θ.1 θ.2 y - hid2 θ.1 θ.2 y') ≤
      LFc n uF ^ 2 * normSq (y - y') := fun y y' => lip_of_EON hθ y y'
  have hmF : 1 ≤ mF n := mF_pos hn
  have hm0 : (0 : ℝ) < mF n := by exact_mod_cast hmF
  have hell : 0 < ellU n (LFc n uF) Mr := by
    unfold ellU
    exact Real.sqrt_pos.mpr (mul_pos (mul_pos (div_pos two_pos hm0) (pow_pos hL0 2)) hMr0)
  set w : (Fin n → ℝ) → Fin (mF n) → ℝ :=
    fun c => wX bh W (A₁, A₂, (0 : Matrix (Fin n) (Fin (mA n)) ℝ)) θ k η c with hw
  have hwm : Measurable w := by
    refine measurable_pi_iff.mpr fun i => ?_
    exact meas_wX (fW := fun _ : Fin n → ℝ => W)
      (fA := fun _ => (A₁, A₂, (0 : Matrix (Fin n) (Fin (mA n)) ℝ))) (fθ := fun _ => θ)
      (fη := fun _ => η) (fc := fun c => c) hbh measurable_const measurable_const
      measurable_const measurable_const measurable_id i
  have hw1 : ∀ c, normSq (w c) ≤ 1 := fun c => wdir_le _
  have ev := lemmaU_events_sharp bh W A₁ A₂ hn hb' θ hMr0.le hLF hMr hwm hw1
    (u := uU n (LFc n uF) Mr Lc) (uU_nonneg _ _ _ _)
  have e : Real.exp (-uU n (LFc n uF) Mr Lc ^ 2 / (2 * ellU n (LFc n uF) Mr ^ 2)) =
      Real.exp (-Lc) := by
    unfold uU
    exact exp_paper hLc hell
  rw [e] at ev
  refine (measureReal_mono ?_).trans ev
  intro A₃ hA
  have hA3 := hA.2.2
  intro hcon
  apply hA3
  refine ⟨lt_of_lt_of_le hcon.1 ?_, hcon.2⟩
  have hi := lemmaU_i bh W A₁ A₂ hn hb' θ hMr0.le hMr (A₃.mulVec (bh (W, (A₁, A₂))))
  have h5 := Real.sqrt_le_sqrt hi
  exact add_le_add h5 le_rfl

end probs

end BstLean.Part151
