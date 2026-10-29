import BstLean.Part245Moment

/-! Part 273: the fourth-moment payment on a base dimension `n0 ≥ 8000`.
The payment `momentPay n0` is an explicit function of `n0`. It holds for every `n ≥ n0`.
The 11883 instance is below `5e-5`; the 8000 instance is below `2e-6`. -/
namespace BstLean.Part273
open MeasureTheory Real BstLean.Part153
open BstLean.Part157 BstLean.Part160 BstLean.Part152 BstLean.Part130

/-- An explicit upper bound for `jS n 160 (6/1000)`, valid for each `n ≥ n0 ≥ 8000`. -/
noncomputable def jBound (n0 : ℕ) : ℝ :=
  (1006 / 1000 + 141422 / 100000 * (1 / √(n0 : ℝ)) + 141422 / 100000 * (18 / (n0 : ℝ)) +
    15 / 10 ^ 7) ^ 2 +
  (1 + 141422 / 100000 * (18 / (n0 : ℝ))) * (141422 / 100000 * (1 + 18 / √(n0 : ℝ))) *
    (1 / √(n0 : ℝ))

/-- The moment payment at base `n0`. -/
noncomputable def momentPay (n0 : ℕ) : ℝ :=
  (jBound n0 ^ 2 * n0 / (((n0 : ℝ) - 321) * (13 / 10))) ^ 160

theorem jBound_nonneg (n0 : ℕ) : 0 ≤ jBound n0 := by
  unfold jBound
  positivity

theorem momentPay_nonneg {n0 : ℕ} (h0 : 8000 ≤ n0) : 0 ≤ momentPay n0 := by
  have : (8000 : ℝ) ≤ n0 := by exact_mod_cast h0
  unfold momentPay
  apply pow_nonneg
  apply div_nonneg (mul_nonneg (sq_nonneg _) (by linarith))
  apply mul_nonneg (by linarith) (by norm_num)

lemma exp_neg_14_le : Real.exp (-14) ≤ 1 / 10 ^ 6 := by
  have h1 : (2.7 : ℝ) ^ 14 ≤ Real.exp 14 := by
    have e : Real.exp 14 = Real.exp 1 ^ 14 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [e]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 14
  rw [Real.exp_neg]
  calc (Real.exp 14)⁻¹ ≤ ((2.7 : ℝ) ^ 14)⁻¹ := inv_anti₀ (by positivity) h1
    _ ≤ 1 / 10 ^ 6 := by norm_num

theorem jS_le_jBound {n0 n : ℕ} (h0 : 8000 ≤ n0) (hn : n0 ≤ n) :
    jS n 160 (6 / 1000) ≤ jBound n0 := by
  have h0r : (8000 : ℝ) ≤ n0 := by exact_mod_cast h0
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hnr : (8000 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hn00 : (0 : ℝ) < n0 := by linarith
  have hs89 : (89 : ℝ) ≤ √(n0 : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  have hs0 : (0 : ℝ) < √(n0 : ℝ) := by linarith
  have hsn : √(n0 : ℝ) ≤ √(n : ℝ) := Real.sqrt_le_sqrt hnn
  have hsn0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hg0 := gaussMomConst_nonneg 160
  have hg := gaussMomConst_160_le
  obtain ⟨g, hgdef⟩ : ∃ g, g = gaussMomConst 160 := ⟨_, rfl⟩
  rw [← hgdef] at hg0 hg
  have hr0 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hr : √(2 : ℝ) ≤ 141422 / 100000 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hq0 : (0 : ℝ) ≤ √(1 + 2 * (6 / 1000)) := Real.sqrt_nonneg _
  have hq : √(1 + 2 * (6 / 1000) : ℝ) ≤ 1006 / 1000 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  -- base quantities at n0
  obtain ⟨U, hUd⟩ : ∃ U, U = 1 / √(n0 : ℝ) := ⟨_, rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V, V = 18 / (n0 : ℝ) := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G, G = 18 / √(n0 : ℝ) := ⟨_, rfl⟩
  have hU0 : 0 ≤ U := by rw [hUd]; positivity
  have hV0 : 0 ≤ V := by rw [hVd]; positivity
  have hG0 : 0 ≤ G := by rw [hGd]; positivity
  have hU89 : U ≤ 1 / 89 := by rw [hUd]; exact one_div_le_one_div_of_le (by norm_num) hs89
  have hV8 : V ≤ 18 / 8000 := by
    rw [hVd, div_le_div_iff₀ hn00 (by norm_num)]
    linarith
  have hu0 : (0 : ℝ) ≤ 1 / √(n : ℝ) := by positivity
  have hu : 1 / √(n : ℝ) ≤ U := by rw [hUd]; exact one_div_le_one_div_of_le hs0 hsn
  have hw0 : (0 : ℝ) ≤ g / n := by positivity
  have hw : g / (n : ℝ) ≤ V := by
    rw [hVd, div_le_div_iff₀ hn0 hn00]
    nlinarith
  have hgu0 : (0 : ℝ) ≤ g / √(n : ℝ) := by positivity
  have hgu : g / √(n : ℝ) ≤ G := by
    rw [hGd, div_le_div_iff₀ hsn0 hs0]
    nlinarith
  have he0 : 0 ≤ epsS n 160 (6 / 1000) := (Real.exp_pos _).le
  have he : epsS n 160 (6 / 1000) ≤ 1 / 10 ^ 6 := by
    refine le_trans ?_ exp_neg_14_le
    unfold epsS
    rw [show ((160 : ℕ) : ℝ) = 160 by norm_num]
    refine Real.exp_le_exp.2 ?_
    have : (8000 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnr 2
    have h15 : (14 : ℝ) ≤ (6 / 1000) ^ 2 * (n : ℝ) ^ 2 / 160 := by
      rw [le_div_iff₀ (by norm_num)]
      linarith
    linarith
  obtain ⟨r2, hr2⟩ : ∃ r2, r2 = √(2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q, q = √(1 + 2 * (6 / 1000) : ℝ) := ⟨_, rfl⟩
  obtain ⟨u, hud⟩ : ∃ u, u = 1 / √(n : ℝ) := ⟨_, rfl⟩
  obtain ⟨w, hwd⟩ : ∃ w, w = g / (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨gu, hgud⟩ : ∃ gu, gu = g / √(n : ℝ) := ⟨_, rfl⟩
  obtain ⟨e, hed⟩ : ∃ e, e = epsS n 160 (6 / 1000) := ⟨_, rfl⟩
  have key : jS n 160 (6 / 1000) = (q + r2 * u + r2 * w + e * (r2 * (1 + u + w))) ^ 2 +
      (1 + r2 * w) * (r2 * (1 + gu)) * u := by
    unfold jS n2S n1S b2S rcS rchiS
    rw [← hgdef, ← hed, hqd, hr2, hud, hwd, hgud]
    ring
  have keyB : jBound n0 = (1006 / 1000 + 141422 / 100000 * U + 141422 / 100000 * V +
      15 / 10 ^ 7) ^ 2 + (1 + 141422 / 100000 * V) * (141422 / 100000 * (1 + G)) * U := by
    rw [hUd, hVd, hGd]
    unfold jBound
    ring
  rw [key, keyB]
  rw [← hr2] at hr0 hr
  rw [← hqd] at hq0 hq
  rw [← hud] at hu0 hu
  rw [← hwd] at hw0 hw
  rw [← hgud] at hgu0 hgu
  rw [← hed] at he0 he
  have h1 : r2 * u ≤ 141422 / 100000 * U := mul_le_mul hr hu hu0 (by norm_num)
  have h2 : r2 * w ≤ 141422 / 100000 * V := mul_le_mul hr hw hw0 (by norm_num)
  have h10 : 0 ≤ r2 * u := mul_nonneg hr0 hu0
  have h20 : 0 ≤ r2 * w := mul_nonneg hr0 hw0
  have hb0 : 0 ≤ r2 * (1 + u + w) := mul_nonneg hr0 (by linarith)
  have hb : r2 * (1 + u + w) ≤ 15 / 10 := by
    have : r2 * (1 + u + w) ≤ 141422 / 100000 * (1 + 1 / 89 + 18 / 8000) :=
      mul_le_mul hr (by linarith) (by linarith) (by norm_num)
    refine this.trans ?_
    norm_num
  have heb : e * (r2 * (1 + u + w)) ≤ 1 / 10 ^ 6 * (15 / 10) :=
    mul_le_mul he hb hb0 (by norm_num)
  have heb0 : 0 ≤ e * (r2 * (1 + u + w)) := mul_nonneg he0 hb0
  have hn20 : 0 ≤ q + r2 * u + r2 * w + e * (r2 * (1 + u + w)) := by linarith
  have hn2 : q + r2 * u + r2 * w + e * (r2 * (1 + u + w)) ≤
      1006 / 1000 + 141422 / 100000 * U + 141422 / 100000 * V + 15 / 10 ^ 7 := by
    norm_num at heb ⊢
    linarith
  have hn2sq := pow_le_pow_left₀ hn20 hn2 2
  have hrc0 : 0 ≤ 1 + r2 * w := by linarith
  have hrc : 1 + r2 * w ≤ 1 + 141422 / 100000 * V := by linarith
  have hrchi0 : 0 ≤ r2 * (1 + gu) := mul_nonneg hr0 (by linarith)
  have hrchi : r2 * (1 + gu) ≤ 141422 / 100000 * (1 + G) :=
    mul_le_mul hr (by linarith) (by linarith) (by norm_num)
  have hprod : (1 + r2 * w) * (r2 * (1 + gu)) ≤
      (1 + 141422 / 100000 * V) * (141422 / 100000 * (1 + G)) :=
    mul_le_mul hrc hrchi hrchi0 (by positivity)
  have hprod0 : 0 ≤ (1 + r2 * w) * (r2 * (1 + gu)) := mul_nonneg hrc0 hrchi0
  have hpu : (1 + r2 * w) * (r2 * (1 + gu)) * u ≤
      (1 + 141422 / 100000 * V) * (141422 / 100000 * (1 + G)) * U :=
    mul_le_mul hprod hu hu0 (by positivity)
  linarith

/-- **The moment bound on base `n0`.** For every `n ≥ n0 ≥ 8000`, every centre and every
positive scale: `Pr(Ξ₄ > (13/10)·(2/n)/n) ≤ momentPay n0`. -/
theorem moment_M12_base {n0 n : ℕ} (h0 : 8000 ≤ n0) (hn : n0 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {a | (13 / 10 : ℝ) * (2 / (n : ℝ)) / n < Xi4 a.1 a.2 c τ}
      ≤ momentPay n0 := by
  have h0r : (8000 : ℝ) ≤ n0 := by exact_mod_cast h0
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have h := lemmaPP_Xi4_sharp (n := n) (P := 160) (by norm_num) (by omega) c hτ
    (M := 13 / 10) (by norm_num) (η := 6 / 1000) (by norm_num)
  refine h.trans ?_
  rw [show ((160 : ℕ) : ℝ) = 160 by norm_num]
  unfold momentPay
  have hj0 := jS_nonneg n 160 (6 / 1000)
  have hj := jS_le_jBound h0 hn
  have hj2 : jS n 160 (6 / 1000) ^ 2 ≤ jBound n0 ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hd : (0 : ℝ) < ((n : ℝ) - 1 - 2 * 160) * (13 / 10) := by
    have : (0 : ℝ) < (n : ℝ) - 1 - 2 * 160 := by linarith
    positivity
  have hd0 : (0 : ℝ) < ((n0 : ℝ) - 321) * (13 / 10) := by
    have : (0 : ℝ) < (n0 : ℝ) - 321 := by linarith
    positivity
  have hr0 : 0 ≤ jS n 160 (6 / 1000) ^ 2 * n / (((n : ℝ) - 1 - 2 * 160) * (13 / 10)) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hd.le
  apply pow_le_pow_left₀ hr0
  rw [div_le_div_iff₀ hd hd0]
  have hB0 : 0 ≤ jBound n0 ^ 2 := sq_nonneg _
  have hA0 : 0 ≤ jS n 160 (6 / 1000) ^ 2 := sq_nonneg _
  have e1 : jS n 160 (6 / 1000) ^ 2 * n * (((n0 : ℝ) - 321) * (13 / 10)) ≤
      jBound n0 ^ 2 * n * (((n0 : ℝ) - 321) * (13 / 10)) := by
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hj2 (by linarith))
    exact hd0.le
  have e2 : jBound n0 ^ 2 * n * (((n0 : ℝ) - 321) * (13 / 10)) ≤
      jBound n0 ^ 2 * n0 * (((n : ℝ) - 1 - 2 * 160) * (13 / 10)) := by
    have : (n : ℝ) * ((n0 : ℝ) - 321) ≤ n0 * ((n : ℝ) - 1 - 2 * 160) := by nlinarith
    nlinarith
  linarith

/-- Retained-data integration pays the moment charge once, on base `n0`. -/
theorem moment_M12_ret_base {n0 n : ℕ} (h0 : 8000 ≤ n0) (hn : n0 ≤ n) (D : Design n)
    (hτ : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (BstLean.Part245.MomentM12 n))ᶜ ≤ momentPay n0 := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτ (BstLean.Part245.measurableSet_MomentM12 n)
    (momentPay_nonneg h0)
  intro c τ hτ
  simpa only [BstLean.Part245.MomentM12, Set.mem_setOf_eq, not_le] using
    moment_M12_base h0 hn c hτ

/-! ## Instances -/

/-- A rational lower bound `s ≤ √n0` gives a rational upper bound for `jBound n0`. -/
theorem jBound_le_of_sqrt {n0 : ℕ} {s : ℝ} (hs0 : 0 < s) (hs : s ≤ √(n0 : ℝ)) :
    jBound n0 ≤ (1006 / 1000 + 141422 / 100000 * (1 / s) + 141422 / 100000 * (18 / (n0 : ℝ)) +
      15 / 10 ^ 7) ^ 2 +
      (1 + 141422 / 100000 * (18 / (n0 : ℝ))) * (141422 / 100000 * (1 + 18 / s)) * (1 / s) := by
  have hU : 1 / √(n0 : ℝ) ≤ 1 / s := one_div_le_one_div_of_le hs0 hs
  have hU0 : 0 ≤ 1 / √(n0 : ℝ) := by positivity
  have hG : 18 / √(n0 : ℝ) ≤ 18 / s := div_le_div_of_nonneg_left (by norm_num) hs0 hs
  have hV0 : 0 ≤ 18 / (n0 : ℝ) := by positivity
  unfold jBound
  have hA : (1006 / 1000 + 141422 / 100000 * (1 / √(n0 : ℝ)) +
      141422 / 100000 * (18 / (n0 : ℝ)) + 15 / 10 ^ 7) ≤
      1006 / 1000 + 141422 / 100000 * (1 / s) + 141422 / 100000 * (18 / (n0 : ℝ)) +
        15 / 10 ^ 7 := by
    have := mul_le_mul_of_nonneg_left hU (by norm_num : (0 : ℝ) ≤ 141422 / 100000)
    linarith
  have hA0 : 0 ≤ (1006 / 1000 + 141422 / 100000 * (1 / √(n0 : ℝ)) +
      141422 / 100000 * (18 / (n0 : ℝ)) + 15 / 10 ^ 7) := by positivity
  have hA2 := pow_le_pow_left₀ hA0 hA 2
  have hR : 141422 / 100000 * (1 + 18 / √(n0 : ℝ)) ≤ 141422 / 100000 * (1 + 18 / s) :=
    mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
  have hP : (1 + 141422 / 100000 * (18 / (n0 : ℝ))) *
      (141422 / 100000 * (1 + 18 / √(n0 : ℝ))) * (1 / √(n0 : ℝ)) ≤
      (1 + 141422 / 100000 * (18 / (n0 : ℝ))) * (141422 / 100000 * (1 + 18 / s)) *
        (1 / s) := by
    apply mul_le_mul _ hU hU0 (by positivity)
    exact mul_le_mul_of_nonneg_left hR (by positivity)
  linarith

theorem jBound_8000_le : jBound 8000 ≤ 10697 / 10000 := by
  refine (jBound_le_of_sqrt (s := 8944 / 100) (by norm_num)
    (Real.le_sqrt_of_sq_le (by norm_num))).trans ?_
  norm_num

theorem momentPay_8000_le : momentPay 8000 ≤ 2 / 10 ^ 6 := by
  unfold momentPay
  have hj0 := jBound_nonneg 8000
  have hj2 := pow_le_pow_left₀ hj0 jBound_8000_le 2
  have hx0 : 0 ≤ jBound 8000 ^ 2 * ((8000 : ℕ) : ℝ) / ((((8000 : ℕ) : ℝ) - 321) * (13 / 10)) := by
    apply div_nonneg (mul_nonneg (sq_nonneg _) (by norm_num)) (by norm_num)
  have hx : jBound 8000 ^ 2 * ((8000 : ℕ) : ℝ) / ((((8000 : ℕ) : ℝ) - 321) * (13 / 10)) ≤
      92 / 100 := by
    rw [div_le_iff₀ (by norm_num)]
    norm_num at hj2 ⊢
    linarith
  calc (jBound 8000 ^ 2 * ((8000 : ℕ) : ℝ) / ((((8000 : ℕ) : ℝ) - 321) * (13 / 10))) ^ 160
      ≤ (92 / 100 : ℝ) ^ 160 := pow_le_pow_left₀ hx0 hx 160
    _ ≤ 2 / 10 ^ 6 := by norm_num

theorem jBound_11883_le : jBound 11883 ≤ 10579 / 10000 := by
  refine (jBound_le_of_sqrt (s := 109) (by norm_num)
    (Real.le_sqrt_of_sq_le (by norm_num))).trans ?_
  norm_num

theorem momentPay_11883_le : momentPay 11883 ≤ 1 / 10 ^ 7 := by
  unfold momentPay
  have hj0 := jBound_nonneg 11883
  have hj2 := pow_le_pow_left₀ hj0 jBound_11883_le 2
  have hx0 : 0 ≤ jBound 11883 ^ 2 * ((11883 : ℕ) : ℝ) /
      ((((11883 : ℕ) : ℝ) - 321) * (13 / 10)) := by
    apply div_nonneg (mul_nonneg (sq_nonneg _) (by norm_num)) (by norm_num)
  have hx : jBound 11883 ^ 2 * ((11883 : ℕ) : ℝ) / ((((11883 : ℕ) : ℝ) - 321) * (13 / 10)) ≤
      9 / 10 := by
    rw [div_le_iff₀ (by norm_num)]
    norm_num at hj2 ⊢
    linarith
  calc (jBound 11883 ^ 2 * ((11883 : ℕ) : ℝ) / ((((11883 : ℕ) : ℝ) - 321) * (13 / 10))) ^ 160
      ≤ (9 / 10 : ℝ) ^ 160 := pow_le_pow_left₀ hx0 hx 160
    _ ≤ 1 / 10 ^ 7 := by norm_num

/-- The 11883 instance: the original Part245 payment `5e-5` follows from the base form. -/
theorem moment_M12_11883 {n : ℕ} (hn : 11883 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {a | (13 / 10 : ℝ) * (2 / (n : ℝ)) / n < Xi4 a.1 a.2 c τ}
      ≤ 5 / 100000 :=
  (moment_M12_base (by norm_num) hn c hτ).trans (momentPay_11883_le.trans (by norm_num))

/-- The 8000 instance of the moment bound, with the same `5e-5` payment. -/
theorem moment_M12_8000 {n : ℕ} (hn : 8000 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {a | (13 / 10 : ℝ) * (2 / (n : ℝ)) / n < Xi4 a.1 a.2 c τ}
      ≤ 5 / 100000 :=
  (moment_M12_base (le_refl 8000) hn c hτ).trans (momentPay_8000_le.trans (by norm_num))

theorem moment_M12_ret_11883 {n : ℕ} (hn : 11883 ≤ n) (D : Design n) (hτ : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (BstLean.Part245.MomentM12 n))ᶜ ≤ 5 / 100000 :=
  (moment_M12_ret_base (by norm_num) hn D hτ).trans (momentPay_11883_le.trans (by norm_num))

theorem moment_M12_ret_8000 {n : ℕ} (hn : 8000 ≤ n) (D : Design n) (hτ : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (BstLean.Part245.MomentM12 n))ᶜ ≤ 5 / 100000 :=
  (moment_M12_ret_base (le_refl 8000) hn D hτ).trans (momentPay_8000_le.trans (by norm_num))

end BstLean.Part273
