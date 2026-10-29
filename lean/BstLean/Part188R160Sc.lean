import BstLean.Part187All
import BstLean.Part160Sc
import BstLean.Part188R143HidC
import BstLean.Part188R143HidC2
import BstLean.Part188R153PPs4
import BstLean.Part188R153Final
import BstLean.Part188R154C16
import BstLean.Part188R154NumA16
import BstLean.Part188R154NumB16
import BstLean.Part188R154Num16
import BstLean.Part188R160Event
import BstLean.Part188R160Cov
import BstLean.Part188R160ScEv





namespace BstLean.Part188.Base160_R
open BstLean.Part160 BstLean.Part160.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC hO gO sO2 bO bT rhoC_sqP rhoC_posP)
open BstLean.Part153 (nrm nuA GoodAs Pb)
open BstLean.Part154 (GoodC16 csC)

variable {n : ℕ}

/-- **The first-layer energy on `GoodAs`, `n ≥ 16200`**: `|Γ − γ_Aρ²| ≤ (1/1000)·γ_Aρ²`. -/
theorem energy16 (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ}
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodAs n c τ) :
    |gO A₁ c τ - 2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)| ≤
      1 / 1000 * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) := by
  have hn1 : 1 ≤ n := by omega
  have hm := BstLean.Part130.one_le_mA hn1
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hup, hlo⟩ := BstLean.Part153.Ee_bounds (by omega : 2 ≤ n) c τ (Lc := 12) (by norm_num)
    (BstLean.Part153.GoodA_unpack h).2.1
  rw [BstLean.Part153.GamS_eq_gO hm] at hup hlo
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by
    rw [hX]; exact mul_nonneg (by positivity) (add_nonneg (normSq_nonneg c) (by positivity))
  rw [← hX] at hup hlo ⊢
  have h12 : √(12 : ℝ) ≤ 4 := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 2 * √(12 : ℝ) / n := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu1 : u ≤ 8 / 16200 := by
    rw [hu, div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 - 2 / (n : ℝ) ^ 2 := ⟨_, rfl⟩
  have hy1 : y ≤ 1 := by rw [hy]; have : (0 : ℝ) ≤ 2 / (n : ℝ) ^ 2 := by positivity
                         linarith
  have hy0 : 1 - 2 / 16200 ^ 2 ≤ y := by
    rw [hy]
    have : 2 / (n : ℝ) ^ 2 ≤ 2 / 16200 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) hnR 2)
    linarith
  have hy00 : (0 : ℝ) ≤ y := by linarith [show (0 : ℝ) ≤ 1 - 2 / 16200 ^ 2 by norm_num]
  have hw : y ≤ √y := by
    have h1 : √y ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hy1
    have h2 : √y * √y = y := Real.mul_self_sqrt hy00
    nlinarith [Real.sqrt_nonneg y]
  rw [← hu] at hup hlo
  rw [← hy] at hlo
  have hlo' := hlo (by linarith [show (8 : ℝ) / 16200 ≤ 1 - 2 / 16200 ^ 2 by norm_num])
  have hwu : (9995 : ℝ) / 10000 ≤ √y - u := by
    have : (9995 : ℝ) / 10000 ≤ 1 - 2 / 16200 ^ 2 - 8 / 16200 := by norm_num
    linarith
  have hsq1 : (999 : ℝ) / 1000 ≤ (√y - u) ^ 2 := by nlinarith
  have hsq2 : (1 + u) ^ 2 ≤ 1001 / 1000 := by nlinarith
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- **The number of `eb_le_quad`** at `δ = 1/1000`, `L_c = 12`, `n ≥ 16200`, for `a ≤ x ≤ b`. -/
lemma eb_num_gen (hn : 16200 ≤ n) {x a b E : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (hE : (1001 / 1000 : ℝ) * (1 + 16 / 16200 + 48 / 16200 ^ 2) -
        (3 / 2 - 2 * (31832 / 100000)) * a +
        (1 / 2 - 3183 / 10000) * b ^ 2 / (1001 / 1000) ≤ E) :
    (1 + 1 / 1000 : ℝ) * (1 + (4 * √12 / (n : ℝ) + 4 * 12 / (n : ℝ) ^ 2)) -
        (3 / 2 - 2 / π) * x + (1 / 2 - 1 / π) * x ^ 2 / (1 + 1 / 1000) ≤ E := by
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h12 : √(12 : ℝ) ≤ 4 := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hq1 : 4 * √(12 : ℝ) / n ≤ 16 / 16200 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith
  have hq2 : 4 * (12 : ℝ) / (n : ℝ) ^ 2 ≤ 48 / 16200 ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 1 / π := ⟨_, rfl⟩
  have hp1 : (3183 : ℝ) / 10000 ≤ p := by
    rw [hp, div_le_div_iff₀ (by norm_num) Real.pi_pos]
    nlinarith [Real.pi_lt_d4]
  have hp2 : p ≤ 31832 / 100000 := by
    rw [hp, div_le_div_iff₀ Real.pi_pos (by norm_num)]
    nlinarith [Real.pi_gt_d4]
  have e2 : (2 : ℝ) / π = 2 * p := by rw [hp]; ring
  rw [e2, ← hp]
  have hx0 : 0 ≤ x := ha.trans hax
  have t1 : (3 / 2 - 2 * (31832 / 100000)) * a ≤ (3 / 2 - 2 * p) * x := by
    have : (3 / 2 - 2 * (31832 / 100000 : ℝ)) * a ≤ (3 / 2 - 2 * (31832 / 100000)) * x :=
      mul_le_mul_of_nonneg_left hax (by norm_num)
    nlinarith
  have t2 : (1 / 2 - p) * x ^ 2 / (1 + 1 / 1000) ≤
      (1 / 2 - 3183 / 10000) * b ^ 2 / (1001 / 1000) := by
    rw [show (1 + 1 / 1000 : ℝ) = 1001 / 1000 by norm_num]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    have hx2 : x ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hx0 hxb 2
    have : (1 / 2 - p) * x ^ 2 ≤ (1 / 2 - 3183 / 10000) * x ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg x)
    nlinarith
  have t3 : (1 + 1 / 1000 : ℝ) * (1 + (4 * √12 / (n : ℝ) + 4 * 12 / (n : ℝ) ^ 2)) ≤
      1001 / 1000 * (1 + 16 / 16200 + 48 / 16200 ^ 2) := by nlinarith
  linarith

/-- The oracle centre energy on `GoodC16` and `SSc`: `e_b° ≤ 0.7313`. -/
theorem ebO16_sharp (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ SSc n) :
    2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * rhoC c τ ^ 2) ≤
      7313 / 10000 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hAs : (A₁, A₂) ∈ GoodAs n c τ := h.1.1
  have hρ2 := rhoC_sqP c τ
  have hρ : 0 < normSq c + (n : ℝ) * τ ^ 2 := by
    have := rhoC_posP hn1 c hτ
    rw [← hρ2]; positivity
  have hE := energy16 hn hAs
  have hs := sO2_ge_of_SSc hn hτ hθ0 hθ1 hS
  have hbe := BstLean.Part153.GoodA_be hAs
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = normSq c + (n : ℝ) * τ ^ 2 := ⟨_, rfl⟩
  have hτ2 : 0 < τ ^ 2 := by positivity
  rw [hρ2, ← hR]
  rw [← hR] at hρ hE hs
  obtain ⟨θ, hθd⟩ : ∃ θ : ℝ, θ = (n : ℝ) * τ ^ 2 / R := ⟨_, rfl⟩
  have hθpos : 0 < θ := by rw [hθd]; positivity
  have hsc : 67507 / 100000 / θ * τ ^ 2 ≤ sO2 A₁ c τ := by
    refine le_trans (le_of_eq ?_) hs
    rw [hθd]; field_simp
  have key := eb_le_quad hn1 A₁ A₂ c τ (Lc := 12) (δ := 1 / 1000) (cs := 67507 / 100000 / θ)
    (θlo := θ) (by rw [← hR]; exact hρ) (by norm_num) (by norm_num) (by rw [← hR]; exact hE)
    (by positivity) hθpos hsc (by rw [← hR, hθd]) hbe
  rw [← hR] at key
  have ex : 67507 / 100000 / θ * θ / 2 = 337535 / 1000000 := by field_simp; norm_num
  rw [ex] at key
  exact key.trans (eb_num_gen hn (x := 337535 / 1000000) (a := 337535 / 1000000)
    (b := 337535 / 1000000) (by norm_num) le_rfl le_rfl (by norm_num))

/-- **The transfer from the oracle centre to the computed centre** on `GoodC16`
(`n ≥ 16200`, the window): if `e_b° ≤ Eo ≤ e²` then `t_A|b|² ≤ γ_A·(e + 6·10⁻⁵)²`. -/
theorem eb_transfer (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) {Eo e : ℝ}
    (hO : 2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * rhoC c τ ^ 2) ≤ Eo)
    (he : 0 ≤ e) (hEe : Eo ≤ e ^ 2) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (e + 6 / 100000) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hρ := rhoC_posP hn1 c hτ
  obtain ⟨-, -, -, g4, -, -, -, -⟩ := BstLean.Part188.Base154_R.GoodC16_centre hn hn1 hτ h
    (BstLean.Part188.Base154_R.rhoBar_lt16 hn) (BstLean.Part188.Base154_R.eMP_le16 hn hθ0 hθ1) (θlo := 46 / 100) hθ0
  obtain ⟨hε0, hε⟩ := BstLean.Part188.Base154_R.epsJ_le16 hn
  have hrn : (127 : ℝ) ≤ √(n : ℝ) := by
    rw [show (127 : ℝ) = √(127 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hrn0 : 0 < √(n : ℝ) := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = √(2 / ((mA n : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 / ((mA n : ℕ) : ℝ) := by rw [hs]; exact Real.sq_sqrt (by positivity)
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = √(2 / (n : ℝ)) := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; exact Real.sqrt_pos.mpr (by positivity)
  have hg2 : g ^ 2 = 2 / (n : ℝ) := by rw [hg]; exact Real.sq_sqrt (by positivity)
  have hX : √(2 / (n : ℝ) / n) = g / √(n : ℝ) := by
    rw [hg, Real.sqrt_div (by positivity)]
  rw [← hs, hX] at g4
  obtain ⟨bo, hbo⟩ : ∃ bo, bo = bO A₁ A₂ c τ := ⟨_, rfl⟩
  obtain ⟨bt, hbt⟩ : ∃ bt, bt = bT n n A₁ A₂ c τ := ⟨_, rfl⟩
  obtain ⟨ρ, hρd⟩ : ∃ ρ : ℝ, ρ = rhoC c τ := ⟨_, rfl⟩
  rw [← hbo, ← hbt, ← hρd] at g4
  rw [← hbo, ← hρd] at hO
  rw [← hbt, ← hρd]
  rw [← hρd] at hρ
  have hρi : 0 < 1 / ρ := by positivity
  have h1 : s * nrm ((1 / ρ) • bo) ≤ g * e := by
    have h0 : 0 ≤ s * nrm ((1 / ρ) • bo) := mul_nonneg hs0 (BstLean.Part153.nrm_nonneg _)
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [mul_pow, hs2, BstLean.Part153.nrm_sq, mul_pow, hg2]
    have e' : normSq ((1 / ρ) • bo) = normSq bo / ρ ^ 2 := by
      unfold normSq
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      field_simp
    rw [e']
    have h2 : 2 / ((mA n : ℕ) : ℝ) * normSq bo ≤ Eo * (2 / (n : ℝ) * ρ ^ 2) :=
      (div_le_iff₀ (by positivity)).mp hO
    have h3 : 2 / ((mA n : ℕ) : ℝ) * (normSq bo / ρ ^ 2) =
        2 / ((mA n : ℕ) : ℝ) * normSq bo / ρ ^ 2 := by ring
    rw [h3, div_le_iff₀ (by positivity)]
    have h4 : (0 : ℝ) ≤ 2 / (n : ℝ) * ρ ^ 2 := by positivity
    nlinarith
  have h2 : s * nrm ((1 / ρ) • bt - (1 / ρ) • bo) ≤ g * (6 / 100000) := by
    have e' : (1 / ρ) • bt - (1 / ρ) • bo = (1 / ρ) • (bt - bo) := by rw [smul_sub]
    rw [e', BstLean.Part153.nrm_smul, abs_of_pos hρi]
    have e2 : s * (1 / ρ * nrm (bt - bo)) = s * nrm (bt - bo) / ρ := by ring
    rw [e2]
    refine g4.trans ?_
    have h3 : BstLean.Part150.epsJ n n n (BstLean.Part153.wn n) csC (11 / 1000)
        (BstLean.Part154.deltaChi n 12) * (g / √(n : ℝ)) ≤ 752 / 100000 * (g / √(n : ℝ)) :=
      mul_le_mul_of_nonneg_right hε (by positivity)
    refine h3.trans ?_
    rw [show (752 : ℝ) / 100000 * (g / √(n : ℝ)) = g * (752 / 100000 / √(n : ℝ)) by ring]
    refine mul_le_mul_of_nonneg_left ?_ hg0.le
    rw [div_le_iff₀ hrn0]
    linarith
  have h3 : s * nrm ((1 / ρ) • bt) ≤ g * (e + 6 / 100000) := by
    have e' : (1 / ρ) • bt = (1 / ρ) • bo + ((1 / ρ) • bt - (1 / ρ) • bo) := by abel
    have h4 := BstLean.Part153.nrm_add_le ((1 / ρ) • bo) ((1 / ρ) • bt - (1 / ρ) • bo)
    rw [← e'] at h4
    have h5 := mul_le_mul_of_nonneg_left h4 hs0
    linarith
  have h4 := pow_le_pow_left₀ (mul_nonneg hs0 (BstLean.Part153.nrm_nonneg _)) h3 2
  rw [mul_pow, hs2, BstLean.Part153.nrm_sq, mul_pow, hg2] at h4
  exact h4

/-- **The energy of the computed centre on `GoodC16` and `SSc`**: `t_A|b|² ≤ 0.7315·γ_A`. -/
theorem eb16_sharp (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (7315 / 10000) := by
  have h1 := eb_transfer hn hτ hθ0 hθ1 h (ebO16_sharp hn hτ hθ0 hθ1 h hS)
    (e := 85517 / 100000) (by norm_num) (by norm_num)
  refine h1.trans (mul_le_mul_of_nonneg_left (by norm_num) (by positivity))

end BstLean.Part188.Base160_R

