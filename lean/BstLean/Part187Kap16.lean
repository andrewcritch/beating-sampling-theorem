import BstLean.Part187Kap
import BstLean.Part187R160Sc
import BstLean.Part187R160ScTab

/-!
# Part 187 (file `Kap16`): the sharp-kernel centre energy table at `n ≥ 16 250`

No proof is left open; no `native_decide` or `axiom` is used. The same argument as file `Kap`
(`eb_le_kap`, `kappa_le_num`) with the base lemmas `energy16`, `sO2_ge_gen`, `eb_transfer` re-proved
at the floor `16 250` (Fork B, files `Part187R160Sc`, `Part187R160ScTab`).
* `eb16K_gen16`, `eb16K16_46 … _54`: `E` = 0.72442 at `θ ≥ 0.46` (16 384: 0.72441).
-/

namespace BstLean.Part187

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150
open BstLean.Part153 (nrm Pb GoodAs)
open BstLean.Part154 (GoodC16)

/-- The numbers of `eb_le_kap` at `δ = 1/1000`, `L_c = 12`, `n ≥ 16 384`. -/
lemma ebK_num16 {n : ℕ} (hn : 16250 ≤ n) {K Eo : ℝ}
    (hE : (1001 / 1000 : ℝ) * (K + 16 / 16250 + 48 / 16250 ^ 2) ≤ Eo) :
    (1 + 1 / 1000 : ℝ) * (K + (4 * √12 / (n : ℝ) + 4 * 12 / (n : ℝ) ^ 2)) ≤ Eo := by
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h12 : √(12 : ℝ) ≤ 4 := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hq1 : 4 * √(12 : ℝ) / n ≤ 16 / 16250 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith
  have hq2 : 4 * (12 : ℝ) / (n : ℝ) ^ 2 ≤ 48 / 16250 ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  nlinarith

/-- **The computed-centre energy with the exact kernel** on `GoodC16` and `SSc` for
`θ_lo ≤ θ_in ≤ 0.55`, `n ≥ 16 384`, with free numbers (the analogue of
`BstLean.Part160.eb16_sharp_gen`; the quadratic surrogate is replaced by `κ(1 − X/1.001) ≤ K`). -/
theorem eb16K_gen16 {n : ℕ} (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    {θlo K' X d S K Eo e Eb : ℝ}
    (hlo : 46 / 100 ≤ θlo) (hlo1 : θlo ≤ 1) (hθ0 : θlo ≤ thetaC c τ)
    (hθ1 : thetaC c τ ≤ 55 / 100)
    (hK' : (1 - θlo) * (1 - θlo + 55 / 100 / 16250) / ((1 - 3 / 100) ^ 2 * (99996 / 100000)) +
      (1 - θlo) * (1504 / 10 ^ 6) ^ 2 + 55 / 100 / 16250 ≤ K')
    (hX0 : 0 < X)
    (hX : X ≤ 95 / 100 * (1 - 31832 / 100000 - (1 - θlo) / 2 - (1 / 2 - 3183 / 10000) * K'))
    (hX1 : X ≤ 1001 / 1000)
    (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hr : 1 - X / (1001 / 1000) ≤ 1 / 2 * (1 - d ^ 2 / 2) + 1732 / 1000 / 2 * (d - d ^ 3 / 6))
    (hS0 : 0 ≤ S) (hS : 1 - (1 - X / (1001 / 1000)) ^ 2 ≤ S ^ 2)
    (hK : S / (314159 / 100000) + (1 - X / (1001 / 1000)) * (2 / 3 + d / (314159 / 100000)) ≤ K)
    (hEo : (1001 / 1000 : ℝ) * (K + 16 / 16250 + 48 / 16250 ^ 2) ≤ Eo)
    (he : 0 ≤ e) (hEe : Eo ≤ e ^ 2) (hEb : (e + 6 / 100000) ^ 2 ≤ Eb)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS' : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤ 2 / (n : ℝ) * Eb := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hAs : (A₁, A₂) ∈ GoodAs n c τ := h.1.1
  have hρ2 := rhoC_sqP c τ
  have hρ : 0 < normSq c + (n : ℝ) * τ ^ 2 := by
    have := rhoC_posP hn1 c hτ
    rw [← hρ2]; positivity
  have hE := BstLean.Part160.R.energy16 hn hAs
  have hs := BstLean.Part160.R.sO2_ge_gen hn hτ hlo hlo1 hθ0 hθ1 hK' hX hS'
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
    exact key.trans (ebK_num16 hn hEo)
  have h1 := BstLean.Part160.R.eb_transfer hn hτ (hlo.trans hθ0) hθ1 h hO he hEe
  exact h1.trans (mul_le_mul_of_nonneg_left hEb (by positivity))

/-- `t_A|b|² ≤ 0.72442·γ_A` on `GoodC16` and `SSc` for `46/100 ≤ θ_in ≤ 0.55`, `n ≥ 16 250`. -/
theorem eb16K16_46 {n : ℕ} (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (36221 / 50000) :=
  eb16K_gen16 hn hτ (θlo := 46 / 100) (K' := 309983 / 1000000) (X := 84397 / 250000) (d := 201 / 1000)
    (S := 374421 / 500000) (K := 3613 / 5000) (Eo := 724309 / 1000000) (e := 106383 / 125000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.71953·γ_A` on `GoodC16` and `SSc` for `47/100 ≤ θ_in ≤ 0.55`, `n ≥ 16 250`. -/
theorem eb16K16_47 {n : ℕ} (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 47 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (71953 / 100000) :=
  eb16K_gen16 hn hτ (θlo := 47 / 100) (K' := 298611 / 1000000) (X := 344301 / 1000000) (d := 1921 / 10000)
    (S := 188681 / 250000) (K := 358857 / 500000) (Eo := 359709 / 500000) (e := 424093 / 500000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.71468·γ_A` on `GoodC16` and `SSc` for `48/100 ≤ θ_in ≤ 0.55`, `n ≥ 16 250`. -/
theorem eb16K16_48 {n : ℕ} (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 48 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (17867 / 25000) :=
  eb16K_gen16 hn hτ (θlo := 48 / 100) (K' := 5749 / 20000) (X := 350977 / 1000000) (d := 1833 / 10000)
    (S := 76047 / 100000) (K := 71287 / 100000) (Eo := 714569 / 1000000) (e := 422661 / 500000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.70987·γ_A` on `GoodC16` and `SSc` for `49/100 ≤ θ_in ≤ 0.55`, `n ≥ 16 250`. -/
theorem eb16K16_49 {n : ℕ} (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 49 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (70987 / 100000) :=
  eb16K_gen16 hn hτ (θlo := 49 / 100) (K' := 138251 / 500000) (X := 357617 / 1000000) (d := 873 / 5000)
    (S := 153217 / 200000) (K := 177017 / 250000) (Eo := 354881 / 500000) (e := 421237 / 500000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.70511·γ_A` on `GoodC16` and `SSc` for `50/100 ≤ θ_in ≤ 0.55`, `n ≥ 16 250`. -/
theorem eb16K16_50 {n : ℕ} (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 50 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (70511 / 100000) :=
  eb16K_gen16 hn hτ (θlo := 50 / 100) (K' := 265767 / 1000000) (X := 18211 / 50000) (d := 83 / 500)
    (S := 771571 / 1000000) (K := 703309 / 1000000) (Eo := 704999 / 1000000) (e := 839643 / 1000000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.70038·γ_A` on `GoodC16` and `SSc` for `51/100 ≤ θ_in ≤ 0.55`, `n ≥ 16 250`. -/
theorem eb16K16_51 {n : ℕ} (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 51 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (35019 / 50000) :=
  eb16K_gen16 hn hτ (θlo := 51 / 100) (K' := 63811 / 250000) (X := 370787 / 1000000) (d := 63 / 400)
    (S := 776933 / 1000000) (K := 21831 / 31250) (Eo := 700277 / 1000000) (e := 418413 / 500000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.69570·γ_A` on `GoodC16` and `SSc` for `52/100 ≤ θ_in ≤ 0.55`, `n ≥ 16 250`. -/
theorem eb16K16_52 {n : ℕ} (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 52 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (6957 / 10000) :=
  eb16K_gen16 hn hτ (θlo := 52 / 100) (K' := 122467 / 500000) (X := 94329 / 250000) (d := 1491 / 10000)
    (S := 391087 / 500000) (K := 693919 / 1000000) (Eo := 695599 / 1000000) (e := 417013 / 500000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.69109·γ_A` on `GoodC16` and `SSc` for `53/100 ≤ θ_in ≤ 0.55`, `n ≥ 16 250`. -/
theorem eb16K16_53 {n : ℕ} (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 53 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (69109 / 100000) :=
  eb16K_gen16 hn hτ (θlo := 53 / 100) (K' := 234837 / 1000000) (X := 383809 / 1000000) (d := 1409 / 10000)
    (S := 787297 / 1000000) (K := 172327 / 250000) (Eo := 86373 / 125000) (e := 166251 / 200000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.68650·γ_A` on `GoodC16` and `SSc` for `54/100 ≤ θ_in ≤ 0.55`, `n ≥ 16 250`. -/
theorem eb16K16_54 {n : ℕ} (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 54 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (1373 / 2000) :=
  eb16K_gen16 hn hτ (θlo := 54 / 100) (K' := 28119 / 125000) (X := 78053 / 200000) (d := 1327 / 10000)
    (S := 396153 / 500000) (K := 684721 / 1000000) (Eo := 85799 / 125000) (e := 103561 / 125000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

end BstLean.Part187

#print axioms BstLean.Part187.eb16K16_46
