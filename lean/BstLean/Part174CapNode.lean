import BstLean.Part174CapNum

/-!
# Part 174 (file `CapNode`): the node statistics with Markov thresholds scaled by `κ ≥ 1`

No proof is left open; no `native_decide` or `axiom` is used.

Part 172's `V2N_of_tan`, `piN_of_tan` with the tangential bounds `κ·K₃` in place of `K₃` and
`DstN ≤ κ·16/n³`: then `V2N ≤ κ²·64/n⁴` and (if `48 900κ² ≤ n`) `piN ≤ 1/n⁴`.
-/

namespace BstLean.Part174.Cap

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part172
open BstLean.Part134 (res)
open BstLean.Part161 (xLat momN)
open BstLean.Part162 (tanSq cLS cLS_pos ls_lat ls_lat_mom_sharp xLatH)
open BstLean.Part170 (hB tA aLat)
open BstLean.Part53 (unitF53)

variable {n : ℕ}

/-- `nd_numV` scaled by `κ ≥ 1`. -/
lemma nd_numVK {N x b D κ : ℝ} (hN : 80000 ≤ N) (hκ : 1 ≤ κ) (hx0 : 0 ≤ x)
    (hx : x ≤ κ * (42742 / 10000 * (32 / (5 * N ^ 2)) / (N - 5))) (hb0 : 0 ≤ b)
    (hb : b ^ 2 ≤ 4 * (12 / (5 * N)) * (κ * (32 / (5 * N ^ 2))) / (N - 2)) (hD0 : 0 ≤ D)
    (hD : D ≤ κ * (16 / N ^ 3)) :
    (x + b) ^ 2 + D ^ 2 ≤ κ ^ 2 * (64 / N ^ 4) := by
  have hκ0 : 0 < κ := by linarith
  have hN0 : 0 < N := by linarith
  have h1 : x / κ ≤ 42742 / 10000 * (32 / (5 * N ^ 2)) / (N - 5) := by
    rw [div_le_iff₀ hκ0]; linarith
  have h2 : (b / κ) ^ 2 ≤ 4 * (12 / (5 * N)) * (32 / (5 * N ^ 2)) / (N - 2) := by
    rw [div_pow]
    have hN2 : 0 < N - 2 := by linarith
    have e : 4 * (12 / (5 * N)) * (κ * (32 / (5 * N ^ 2))) / (N - 2) =
        κ * (4 * (12 / (5 * N)) * (32 / (5 * N ^ 2)) / (N - 2)) := by ring
    rw [e] at hb
    have hP : 0 ≤ 4 * (12 / (5 * N)) * (32 / (5 * N ^ 2)) / (N - 2) := by positivity
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h3 : D / κ ≤ 16 / N ^ 3 := by rw [div_le_iff₀ hκ0]; linarith
  have H := BstLean.Part172.nd_numV hN (by positivity) h1 (by positivity) h2 (by positivity) h3
  have e : (x + b) ^ 2 + D ^ 2 = κ ^ 2 * ((x / κ + b / κ) ^ 2 + (D / κ) ^ 2) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left H (by positivity)

/-- `nd_numP` scaled by `κ ≥ 1`, for `48 900κ² ≤ N`. -/
lemma nd_numPK {N α β γ den κ : ℝ} (hN : 80000 ≤ N) (hκ : 1 ≤ κ) (hκN : 48900 * κ ^ 2 ≤ N)
    (hα0 : 0 ≤ α) (hα : α ≤ κ * (1519 / 100 * (32 / (5 * N ^ 2)) / (N - 17))) (hβ0 : 0 ≤ β)
    (hβ : β ^ 2 ≤ 4 * (12 / (5 * N)) * (7905 / 1000) * (κ * (32 / (5 * N ^ 2))) / (N - 9))
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ κ * (32 / (5 * N ^ 2) / (N - 2)))
    (hden : 1 / (10 * N) - κ * (16 / N ^ 3) ≤ den) :
    (α + β + γ) ^ 8 / den ^ 8 ≤ 1 / N ^ 4 := by
  have hN0 : 0 < N := by linarith
  have hκ0 : 0 < κ := by linarith
  set w := 1 / N with hw
  have hw0 : 0 < w := by positivity
  have hNw : N * w = 1 := by rw [hw]; field_simp
  have hw1 : w ≤ 1 / 80000 := by rw [hw]; exact one_div_le_one_div_of_le (by norm_num) hN
  have hκw : 48900 * κ ^ 2 * w ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hκN hw0.le; linarith
  have hκk : κ ≤ κ ^ 2 := by nlinarith
  have hα' : α ≤ κ * (13 / 10000 * w ^ 2) := by
    refine hα.trans (mul_le_mul_of_nonneg_left ?_ hκ0.le)
    rw [hw, div_le_iff₀ (by linarith)]
    field_simp
    nlinarith
  have hγ' : γ ≤ κ * (1 / 10000 * w ^ 2) := by
    refine hγ.trans (mul_le_mul_of_nonneg_left ?_ hκ0.le)
    rw [hw, div_le_iff₀ (by linarith)]
    field_simp
    nlinarith
  have hβ' : β ^ 2 ≤ κ * (4858 / 10 * w ^ 4) := by
    refine hβ.trans ?_
    rw [show 4 * (12 / (5 * N)) * (7905 / 1000) * (κ * (32 / (5 * N ^ 2))) / (N - 9) =
      κ * (4 * (12 / (5 * N)) * (7905 / 1000) * (32 / (5 * N ^ 2)) / (N - 9)) by ring]
    refine mul_le_mul_of_nonneg_left ?_ hκ0.le
    rw [hw, div_le_iff₀ (by linarith)]
    field_simp
    nlinarith
  have hβ2 : β ≤ κ * (2205 / 100 * w ^ 2) := by
    by_contra hcon
    have h := not_le.mp hcon
    have hp : 0 ≤ κ * (2205 / 100 * w ^ 2) := by positivity
    have : (κ * (2205 / 100 * w ^ 2)) ^ 2 < β ^ 2 := by nlinarith
    have hw4 : 0 < w ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hκk hw4.le]
  have hden' : 998 / 10000 * w ≤ den := by
    refine le_trans ?_ hden
    have e1 : 1 / (10 * N) = w / 10 := by rw [hw]; field_simp
    have e2 : κ * (16 / N ^ 3) = 16 * κ * w ^ 3 := by rw [hw]; field_simp
    rw [e1, e2]
    have : κ * w ^ 2 ≤ 2 / 10000 / 16 := by
      have h1 : κ * w ≤ 1 := by nlinarith
      have h2 : κ * w ^ 2 ≤ w := by nlinarith
      linarith
    nlinarith
  have hd0 : 0 < den := lt_of_lt_of_le (by positivity) hden'
  have hsum : α + β + γ ≤ κ * (22064 / 1000 * w ^ 2) := by linarith
  have hs0 : 0 ≤ α + β + γ := by positivity
  have hsq : (α + β + γ) ^ 2 ≤ den ^ 2 * w := by
    have h1 : (α + β + γ) ^ 2 ≤ (κ * (22064 / 1000 * w ^ 2)) ^ 2 := pow_le_pow_left₀ hs0 hsum 2
    have h2 : (998 / 10000 * w) ^ 2 ≤ den ^ 2 := pow_le_pow_left₀ (by positivity) hden' 2
    have h3 : (κ * (22064 / 1000 * w ^ 2)) ^ 2 ≤ (998 / 10000 * w) ^ 2 * w := by
      have hw3 : 0 < w ^ 3 := by positivity
      have hk : κ ^ 2 * w * (22064 / 1000) ^ 2 ≤ (998 / 10000) ^ 2 := by
        have e : κ ^ 2 * w * (22064 / 1000) ^ 2 = (48900 * κ ^ 2 * w) * ((22064 / 1000) ^ 2 / 48900) := by
          ring
        rw [e]
        calc (48900 * κ ^ 2 * w) * ((22064 / 1000) ^ 2 / 48900) ≤ 1 * ((22064 / 1000) ^ 2 / 48900) :=
              mul_le_mul_of_nonneg_right hκw (by norm_num)
          _ ≤ _ := by norm_num
      calc (κ * (22064 / 1000 * w ^ 2)) ^ 2 = w ^ 3 * (κ ^ 2 * w * (22064 / 1000) ^ 2) := by ring
        _ ≤ w ^ 3 * (998 / 10000) ^ 2 := mul_le_mul_of_nonneg_left hk hw3.le
        _ = (998 / 10000 * w) ^ 2 * w := by ring
    calc (α + β + γ) ^ 2 ≤ (κ * (22064 / 1000 * w ^ 2)) ^ 2 := h1
      _ ≤ (998 / 10000 * w) ^ 2 * w := h3
      _ ≤ den ^ 2 * w := mul_le_mul_of_nonneg_right h2 hw0.le
  have h8 : (α + β + γ) ^ 8 ≤ den ^ 8 * w ^ 4 := by
    have := pow_le_pow_left₀ (by positivity) hsq 4
    calc (α + β + γ) ^ 8 = ((α + β + γ) ^ 2) ^ 4 := by ring
      _ ≤ (den ^ 2 * w) ^ 4 := this
      _ = den ^ 8 * w ^ 4 := by ring
  rw [div_le_iff₀ (by positivity)]
  calc (α + β + γ) ^ 8 ≤ den ^ 8 * w ^ 4 := h8
    _ = 1 / N ^ 4 * den ^ 8 := by rw [hw]; ring

section node2

variable (c : Ret n) (g : ℕ)

/-- **`V2N ≤ 64/n⁴`** from the tangential statistics of `S` (paper `t7:p08:statistics`,
line 2). -/
theorem V2N_of_tanK (hn : 80000 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ) (hs : nodeS c g ^ 2 ≤ 1) (h1 : OpB (A1 c) (O1n n))
    (hσu : vsig2 c (nodeS c g) ≤ 12 / (5 * (n : ℝ))) (hDst : DstN c g ≤ κ * DmN n)
    (hT1 : ∫ v, tanSq (SN c g) c (nodeS c g) v ∂stdGauss (Fin (n - 1)) ≤ κ * K3N n)
    (hT2 : ∫ v, |√(tanSq (SN c g) c (nodeS c g) v)| ^ (2 * 2) ∂stdGauss (Fin (n - 1)) ≤
      (κ * K3N n) ^ 2) :
    V2N c g ≤ κ ^ 2 * VmN n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hK : 0 ≤ κ * K3N n := by unfold K3N; positivity
  have h4 := BstLean.Part172.nd_mom c g hn hs h1 (q := 2) (by norm_num) (by omega) hK hT2
  have h2 := BstLean.Part172.nd_var c g hn hs h1 hT1
  have hμ := BstLean.Part172.nd_mu c g hn hs h1 hσu
  set μ0 := ∫ v, √(wT c g v) ∂stdGauss (Fin (n - 1))
  set x := cLS 2 ^ 2 * (κ * K3N n) * ((n : ℝ) - 5)⁻¹ with hx
  set y := √(κ * K3N n / ((n : ℝ) - 2)) with hy
  have hn5 : (0 : ℝ) < (n : ℝ) - 5 := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have h4' : ∫ v, (√(wT c g v) - μ0) ^ 4 ∂stdGauss (Fin (n - 1)) ≤ x ^ 2 := by
    refine h4.trans (le_of_eq ?_)
    rw [hx]; push_cast; ring_nf
  have h2' : ∫ v, (√(wT c g v) - μ0) ^ 2 ∂stdGauss (Fin (n - 1)) ≤ y ^ 2 := by
    rw [hy, Real.sq_sqrt (by positivity)]; exact h2
  have HV := mo_var_sq (μ := stdGauss (Fin (n - 1))) (measurable_wT c g).sqrt
    (BstLean.Part172.nd_S_bdd c g hn1 hs h1) hx0 (Real.sqrt_nonneg _) h4' h2'
  rw [V2N_eq hn1 c g hs (O1n_nonneg n) h1, BstLean.Part172.nd_wT_S c g hn1 hs h1]
  refine (add_le_add HV le_rfl).trans ?_
  have hc2 : cLS 2 ^ 2 ≤ 42742 / 10000 := by
    have := cLS2_le; have h0 := (cLS_pos (q := 2) (by norm_num)).le; nlinarith
  refine nd_numVK hnR hκ hx0 ?_ (by positivity) ?_ (DstN_nonneg c g) (by unfold DmN at hDst; exact hDst)
  · rw [hx, ← div_eq_mul_inv]
    unfold K3N
    rw [show cLS 2 ^ 2 * (κ * (32 / (5 * (n : ℝ) ^ 2))) / ((n : ℝ) - 5) =
      κ * (cLS 2 ^ 2 * (32 / (5 * (n : ℝ) ^ 2)) / ((n : ℝ) - 5)) by ring]
    gcongr
  · rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), sq_abs]
    change 2 ^ 2 * μ0 ^ 2 * (κ * K3N n / ((n : ℝ) - 2)) ≤ _
    unfold K3N
    have : (2 : ℝ) ^ 2 * μ0 ^ 2 ≤ 4 * (12 / (5 * n)) := by nlinarith
    have hκ0 : (0 : ℝ) ≤ κ := by linarith
    calc 2 ^ 2 * μ0 ^ 2 * (κ * (32 / (5 * (n : ℝ) ^ 2)) / ((n : ℝ) - 2)) ≤
        4 * (12 / (5 * n)) * (κ * (32 / (5 * (n : ℝ) ^ 2)) / ((n : ℝ) - 2)) := by gcongr
      _ = _ := by ring

/-- **`piN ≤ 1/n⁴`** from the tangential statistics of `S` (paper `t7:p08:statistics`, line 3,
and Markov of order eight). -/
theorem piN_of_tanK (hn : 80000 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ) (hκN : 48900 * κ ^ 2 ≤ (n : ℝ)) (hs : nodeS c g ^ 2 ≤ 1) (h1 : OpB (A1 c) (O1n n))
    (hσl : SminN n ≤ vsig2 c (nodeS c g)) (hσu : vsig2 c (nodeS c g) ≤ 12 / (5 * (n : ℝ)))
    (hDst : DstN c g ≤ κ * DmN n)
    (hT1 : ∫ v, tanSq (SN c g) c (nodeS c g) v ∂stdGauss (Fin (n - 1)) ≤ κ * K3N n)
    (hT4 : ∫ v, |√(tanSq (SN c g) c (nodeS c g) v)| ^ (2 * 4) ∂stdGauss (Fin (n - 1)) ≤
      (κ * K3N n) ^ 4)
    (hT8 : ∫ v, |√(tanSq (SN c g) c (nodeS c g) v)| ^ (2 * 8) ∂stdGauss (Fin (n - 1)) ≤
      (κ * K3N n) ^ 8) :
    piN c g ≤ PmN n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hK : 0 ≤ κ * K3N n := by unfold K3N; positivity
  have hK0 : 0 < κ * K3N n := by unfold K3N; positivity
  have hm8 := BstLean.Part172.nd_mom c g hn hs h1 (q := 8) (by norm_num) (by omega) hK hT8
  have hm4 := BstLean.Part172.nd_mom c g hn hs h1 (q := 4) (by norm_num) (by omega) hK hT4
  have h2 := BstLean.Part172.nd_var c g hn hs h1 hT1
  have hμ := BstLean.Part172.nd_mu c g hn hs h1 hσu
  set μ0 := ∫ v, √(wT c g v) ∂stdGauss (Fin (n - 1))
  have hDlt : DstN c g < vsig2 c (nodeS c g) / 2 := by
    have : κ * DmN n < SminN n / 2 := by
      unfold DmN SminN
      rw [show κ * (16 / (n : ℝ) ^ 3) = 16 * κ / (n : ℝ) ^ 3 by ring, div_div,
        div_lt_div_iff₀ (by positivity) (by positivity)]
      have hκn : κ ≤ n := by nlinarith
      have h3 : (160 : ℝ) * n * n < (n : ℝ) ^ 3 := by nlinarith [mul_pos hn0 hn0]
      nlinarith [mul_le_mul_of_nonneg_left hκn (by positivity : (0:ℝ) ≤ 160 * n)]
    linarith
  have HP := piN_le hn1 c g hs (O1n_nonneg n) h1 hDlt
  rw [BstLean.Part172.nd_wT_S c g hn1 hs h1] at HP
  have hn17 : (0 : ℝ) < (n : ℝ) - 17 := by linarith
  have hn9 : (0 : ℝ) < (n : ℝ) - 9 := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  set α := cLS 8 ^ 2 * (κ * K3N n) * ((n : ℝ) - 17)⁻¹ with hα
  set β := 2 * √(12 / (5 * (n : ℝ))) * (cLS 4 * √(κ * K3N n) * √(((n : ℝ) - 9)⁻¹)) with hβ
  set γ := κ * K3N n / ((n : ℝ) - 2) with hγ
  have hc8 := (cLS_pos (q := 8) (by norm_num))
  have hc4 := (cLS_pos (q := 4) (by norm_num))
  have hα0 : 0 < α := by rw [hα]; positivity
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have hγ0 : 0 < γ := by rw [hγ]; positivity
  have h16 : ∫ v, (√(wT c g v) - μ0) ^ 16 ∂stdGauss (Fin (n - 1)) ≤ α ^ 8 := by
    refine hm8.trans (le_of_eq ?_)
    rw [hα]; push_cast; ring_nf
  have hμa : |μ0| ≤ √(12 / (5 * (n : ℝ))) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hμ
  have h8 : (2 * |μ0|) ^ 8 * ∫ v, (√(wT c g v) - μ0) ^ 8 ∂stdGauss (Fin (n - 1)) ≤ β ^ 8 := by
    have hm4' : ∫ v, (√(wT c g v) - μ0) ^ 8 ∂stdGauss (Fin (n - 1)) ≤
        cLS 4 ^ 8 * (κ * K3N n) ^ 4 * (((n : ℝ) - 9)⁻¹) ^ 4 := by
      refine hm4.trans (le_of_eq ?_); push_cast; ring_nf
    have hI0 : 0 ≤ ∫ v, (√(wT c g v) - μ0) ^ 8 ∂stdGauss (Fin (n - 1)) :=
      integral_nonneg fun _ => by positivity
    calc (2 * |μ0|) ^ 8 * ∫ v, (√(wT c g v) - μ0) ^ 8 ∂stdGauss (Fin (n - 1)) ≤
        (2 * √(12 / (5 * (n : ℝ)))) ^ 8 * (cLS 4 ^ 8 * (κ * K3N n) ^ 4 * (((n : ℝ) - 9)⁻¹) ^ 4) := by
          refine mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith [hμa]) 8) hm4' hI0
            (by positivity)
      _ = β ^ 8 := by
          rw [hβ]
          have e1 : √(κ * K3N n) ^ 8 = (κ * K3N n) ^ 4 := by
            rw [show √(κ * K3N n) ^ 8 = (√(κ * K3N n) ^ 2) ^ 4 by ring, Real.sq_sqrt hK]
          have e2 : √(((n : ℝ) - 9)⁻¹) ^ 8 = (((n : ℝ) - 9)⁻¹) ^ 4 := by
            rw [show √(((n : ℝ) - 9)⁻¹) ^ 8 = (√(((n : ℝ) - 9)⁻¹) ^ 2) ^ 4 by ring,
              Real.sq_sqrt (by positivity)]
          simp only [mul_pow, e1, e2]
  have HE := mo_eight_sq (μ := stdGauss (Fin (n - 1))) (measurable_wT c g).sqrt
    (BstLean.Part172.nd_S_bdd c g hn1 hs h1) hα0 hβ0 hγ0 h16 h8 h2
  refine HP.trans ?_
  have hden : 1 / (10 * (n : ℝ)) - κ * (16 / (n : ℝ) ^ 3) ≤ vsig2 c (nodeS c g) / 2 - DstN c g := by
    have e : SminN n / 2 = 1 / (10 * (n : ℝ)) := by unfold SminN; field_simp; ring
    have : DstN c g ≤ κ * (16 / (n : ℝ) ^ 3) := hDst
    linarith
  have hd0 : 0 < vsig2 c (nodeS c g) / 2 - DstN c g := by linarith
  calc (∫ v, (√(wT c g v) ^ 2 - ∫ w, √(wT c g w) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 8
        ∂stdGauss (Fin (n - 1))) / (vsig2 c (nodeS c g) / 2 - DstN c g) ^ 8 ≤
      (α + β + γ) ^ 8 / (vsig2 c (nodeS c g) / 2 - DstN c g) ^ 8 := by gcongr
    _ ≤ 1 / (n : ℝ) ^ 4 := by
      refine nd_numPK hnR hκ hκN hα0.le ?_ hβ0.le ?_ hγ0.le (by rw [hγ]; unfold K3N; exact le_of_eq (by ring)) hden
      · have hc8' : cLS 8 ^ 2 ≤ 1519 / 100 :=
          (pow_le_pow_left₀ hc8.le cLS8_le 2).trans (by norm_num)
        rw [hα, ← div_eq_mul_inv]; unfold K3N
        rw [show cLS 8 ^ 2 * (κ * (32 / (5 * (n : ℝ) ^ 2))) / ((n : ℝ) - 17) =
          κ * (cLS 8 ^ 2 * (32 / (5 * (n : ℝ) ^ 2)) / ((n : ℝ) - 17)) by ring]
        gcongr
      · have hc4' : cLS 4 ^ 2 ≤ 7905 / 1000 :=
          (pow_le_pow_left₀ hc4.le cLS4_le 2).trans (by norm_num)
        rw [hβ, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
          Real.sq_sqrt hK, Real.sq_sqrt (by positivity)]
        unfold K3N
        rw [div_eq_mul_inv _ ((n : ℝ) - 9)]
        have : (0:ℝ) ≤ 32 / (5 * (n : ℝ) ^ 2) := by positivity
        have hκ0 : (0 : ℝ) ≤ κ := by linarith
        calc 2 ^ 2 * (12 / (5 * ↑n)) * (cLS 4 ^ 2 * (κ * (32 / (5 * ↑n ^ 2))) * ((n : ℝ) - 9)⁻¹) ≤
            2 ^ 2 * (12 / (5 * ↑n)) * (7905 / 1000 * (κ * (32 / (5 * ↑n ^ 2))) * ((n : ℝ) - 9)⁻¹) := by
              gcongr
          _ = _ := by ring
    _ = PmN n := by unfold PmN; rfl

end node2

end BstLean.Part174.Cap
