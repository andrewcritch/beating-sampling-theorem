import BstLean.Part188Kap
import BstLean.Part188Sc97
import BstLean.Part188R160Sc



namespace BstLean.Part188
open BstLean.Part187

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150
open BstLean.Part153 (nrm Pb GoodAs)
open BstLean.Part154 (GoodC16)

/-- The numbers of `eb_le_kap` at `δ = 1/1000`, `L_c = 12`, `n ≥ 16 384`. -/
lemma eb97_num {n : ℕ} (hn : 16200 ≤ n) {K Eo : ℝ}
    (hE : (1001 / 1000 : ℝ) * (K + 16 / 16200 + 48 / 16200 ^ 2) ≤ Eo) :
    (1 + 1 / 1000 : ℝ) * (K + (4 * √12 / (n : ℝ) + 4 * 12 / (n : ℝ) ^ 2)) ≤ Eo := by
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
  nlinarith

/-- **The computed-centre energy with the exact kernel** on `GoodC16` and `SSc` for
`θ_lo ≤ θ_in ≤ 0.55`, `n ≥ 16 384`, with free numbers (the analogue of
`BstLean.Part160.eb16_sharp_gen`; the quadratic surrogate is replaced by `κ(1 − X/1.001) ≤ K`). -/
theorem eb97_gen {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    {θlo K' X d S K Eo e Eb : ℝ}
    (hlo : 46 / 100 ≤ θlo) (hlo1 : θlo ≤ 1) (hθ0 : θlo ≤ thetaC c τ)
    (hθ1 : thetaC c τ ≤ 55 / 100)
    (hK' : (1 - θlo) * (1 - θlo + 55 / 100 / 16200) / ((1 - 3 / 100) ^ 2 * (99996 / 100000)) +
      (1 - θlo) * (1504 / 10 ^ 6) ^ 2 + 55 / 100 / 16200 ≤ K')
    (hX0 : 0 < X)
    (hX : X ≤ 97 / 100 * (1 - 31832 / 100000 - (1 - θlo) / 2 - (1 / 2 - 3183 / 10000) * K'))
    (hX1 : X ≤ 1001 / 1000)
    (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hr : 1 - X / (1001 / 1000) ≤ 1 / 2 * (1 - d ^ 2 / 2) + 1732 / 1000 / 2 * (d - d ^ 3 / 6))
    (hS0 : 0 ≤ S) (hS : 1 - (1 - X / (1001 / 1000)) ^ 2 ≤ S ^ 2)
    (hK : S / (314159 / 100000) + (1 - X / (1001 / 1000)) * (2 / 3 + d / (314159 / 100000)) ≤ K)
    (hEo : (1001 / 1000 : ℝ) * (K + 16 / 16200 + 48 / 16200 ^ 2) ≤ Eo)
    (he : 0 ≤ e) (hEe : Eo ≤ e ^ 2) (hEb : (e + 6 / 100000) ^ 2 ≤ Eb)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS' : ((c, τ), (A₁, A₂)) ∈ BstLean.Part188.Sc.SSc97 n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤ 2 / (n : ℝ) * Eb := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hAs : (A₁, A₂) ∈ GoodAs n c τ := h.1.1
  have hρ2 := rhoC_sqP c τ
  have hρ : 0 < normSq c + (n : ℝ) * τ ^ 2 := by
    have := rhoC_posP hn1 c hτ
    rw [← hρ2]; positivity
  have hE := BstLean.Part188.Base160_R.energy16 hn hAs
  have hs := BstLean.Part188.Sc.sO2_ge_gen97 hn hτ hlo hlo1 hθ0 hθ1 hK' hX hS'
  have hbe := BstLean.Part153.GoodA_be hAs
  have hrr0 : 0 ≤ 1 - X / (1001 / 1000) := by
    have : X / (1001 / 1000) ≤ 1 := by rw [div_le_one (by norm_num)]; exact hX1
    linarith
  have hrr1 : 1 - X / (1001 / 1000) ≤ 1 := by
    have : 0 ≤ X / (1001 / 1000) := by positivity
    linarith
  have hKk := kappa_le_num hrr0 hrr1 hd0 hd1 hr hS0 hS hK
  have hO : 2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * rhoC c τ ^ 2) ≤ Eo := by
    obtain ⟨R, hR⟩ : ∃ R : ℝ, R = normSq c + (n : ℝ) * τ ^ 2 := ⟨_, rfl⟩
    have hτ2 : 0 < τ ^ 2 := by positivity
    rw [hρ2, ← hR]
    rw [← hR] at hρ hE hs
    obtain ⟨θ, hθd⟩ : ∃ θ : ℝ, θ = (n : ℝ) * τ ^ 2 / R := ⟨_, rfl⟩
    have hθpos : 0 < θ := by rw [hθd]; positivity
    have hsc : 2 * X / θ * τ ^ 2 ≤ sO2 A₁ c τ := by
      refine le_trans (le_of_eq ?_) hs
      rw [hθd]; field_simp
    have ex : 2 * X / θ * θ / 2 = X := by field_simp
    have key := eb_le_kap hn1 A₁ A₂ c τ (Lc := 12) (δ := 1 / 1000) (cs := 2 * X / θ)
      (θlo := θ) (K := K) (by rw [← hR]; exact hρ) (by norm_num) (by norm_num)
      (by rw [← hR]; exact hE) (by positivity) hθpos hsc (by rw [← hR, hθd]) hbe
      (by rw [ex]; linarith) (by rw [ex]; norm_num; norm_num at hKk; exact hKk)
    rw [← hR] at key
    exact key.trans (eb97_num hn hEo)
  have h1 := BstLean.Part188.Base160_R.eb_transfer hn hτ (hlo.trans hθ0) hθ1 h hO he hEe
  exact h1.trans (mul_le_mul_of_nonneg_left hEb (by positivity))

theorem eb97_46 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ)
    (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part188.Sc.SSc97 n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (71923 / 100000) :=
  eb97_gen hn hτ (θlo := 46 / 100) (K' := 9687 / 31250) (X := 68939 / 200000)
    (d := 383 / 2000) (S := 377533 / 500000) (K := 717411 / 1000000) (Eo := 359559 / 500000) (e := 848009 / 1000000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

theorem eb97_47 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 47 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ)
    (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part188.Sc.SSc97 n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (2857 / 4000) :=
  eb97_gen hn hτ (θlo := 47 / 100) (K' := 298611 / 1000000) (X := 351549 / 1000000)
    (d := 73 / 400) (S := 380479 / 500000) (K := 356223 / 500000) (Eo := 178537 / 250000) (e := 845073 / 1000000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

theorem eb97_48 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 48 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ)
    (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part188.Sc.SSc97 n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (70933 / 100000) :=
  eb97_gen hn hτ (θlo := 48 / 100) (K' := 5749 / 20000) (X := 179183 / 500000)
    (d := 217 / 1250) (S := 95839 / 125000) (K := 707523 / 1000000) (Eo := 35461 / 50000) (e := 842153 / 1000000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

theorem eb97_49 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 49 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ)
    (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part188.Sc.SSc97 n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (17611 / 25000) :=
  eb97_gen hn hτ (θlo := 49 / 100) (K' := 276503 / 1000000) (X := 182573 / 500000)
    (d := 103 / 625) (S := 772333 / 1000000) (K := 702643 / 1000000) (Eo := 140867 / 200000) (e := 839247 / 1000000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

theorem eb97_50 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 50 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ)
    (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part188.Sc.SSc97 n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (1749 / 2500) :=
  eb97_gen hn hτ (θlo := 50 / 100) (K' := 265767 / 1000000) (X := 23243 / 62500)
    (d := 1561 / 10000) (S := 777823 / 1000000) (K := 697807 / 1000000) (Eo := 349747 / 500000) (e := 418179 / 500000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

theorem eb97_51 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 51 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ)
    (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part188.Sc.SSc97 n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (1737 / 2500) :=
  eb97_gen hn hτ (θlo := 51 / 100) (K' := 51049 / 200000) (X := 11831 / 31250)
    (d := 59 / 400) (S := 195797 / 250000) (K := 138603 / 200000) (Eo := 694697 / 1000000) (e := 166697 / 200000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

theorem eb97_52 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 52 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ)
    (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part188.Sc.SSc97 n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (13801 / 20000) :=
  eb97_gen hn hτ (θlo := 52 / 100) (K' := 48987 / 200000) (X := 19263 / 50000)
    (d := 139 / 1000) (S := 78843 / 100000) (K := 137653 / 200000) (Eo := 689943 / 1000000) (e := 830629 / 1000000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

theorem eb97_53 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 53 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ)
    (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part188.Sc.SSc97 n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (34267 / 50000) :=
  eb97_gen hn hτ (θlo := 53 / 100) (K' := 234837 / 1000000) (X := 391889 / 1000000)
    (d := 653 / 5000) (S := 49597 / 62500) (K := 683561 / 1000000) (Eo := 342617 / 500000) (e := 827789 / 1000000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

theorem eb97_54 {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 54 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ)
    (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part188.Sc.SSc97 n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (68069 / 100000) :=
  eb97_gen hn hτ (θlo := 54 / 100) (K' := 28119 / 125000) (X := 199241 / 500000)
    (d := 153 / 1250) (S := 4991 / 6250) (K := 678919 / 1000000) (Eo := 680587 / 1000000) (e := 824977 / 1000000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

end BstLean.Part188
