import BstLean.Part160MFB4
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2
import BstLean.Part187R153PPs4
import BstLean.Part187R153Final
import BstLean.Part187R154C16
import BstLean.Part187R154NumA16
import BstLean.Part187R154NumB16
import BstLean.Part187R154Num16
import BstLean.Part187R160Lib
import BstLean.Part187R160Event
import BstLean.Part187R160MFNum
import BstLean.Part187R160MFB3

/-! Part 187 (file `Part187R160MFB4`): copy of `Part160MFB4` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part160.R

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part160.MFB
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm jacT XiS Xi4 N2 sq2 hid2Mean_cr Pb wn N22bar)

/-- The mean bound with change (B), from the certificates. -/
theorem mean_B_gen {n : ℕ} (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ)
    {n1 θlo θhi u Jlo sm y s k d r sx : ℝ} (hn1 : 16250 ≤ n1) (hn1n : n1 ≤ n)
    (hlo0 : 0 < θlo) (hlo : θlo ≤ thetaC c τ) (hhi : thetaC c τ ≤ θhi)
    (hu0 : 0 < u) (hu1 : 2 * u < 1) (hu : 12 ≤ u ^ 2 * n1) (hJ0 : 0 ≤ Jlo)
    (hJ : Jlo ^ 2 * (1 + 2 * (1 - θlo) / (θlo * (1 - 2 * u))) ≤ 1) (hsm0 : 0 ≤ sm)
    (hsm : (1 - Jlo / 2 + 216 / 100000) * (1 - Jlo / 2 * (1 - 1 / n1) + 216 / 100000) +
      1 / (2 * n1) ≤ sm ^ 2)
    (hy0 : 0 ≤ y) (hy : 4 * ((sm + 247 / 100000) ^ 2 + 247 / 1000000) ≤ y ^ 4)
    (hs0 : 0 < s) (hs : s ^ 2 ≤ θlo) (hk0 : 0 < k) (hk : k ^ 4 ≤ n1 ^ 3) (hd0 : 0 ≤ d)
    (hd : 98 / 10 ≤ d * s * k)
    (hr0 : 0 ≤ r) (hr : θhi ≤ r ^ 2)
    (hsx : 26973 / 100000 * ((y + d) ^ 4 / 4) * (θhi * r) + 369 / 100000 ≤ sx ^ 2) :
    ∫ A₂, dC A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * sx ^ 2 := by
  have hA : A₁ ∉ BadH n c τ 12 := h.1.2.1
  have hHS := hsH_le_B hn c hτ hA hn1 hn1n hlo0 hlo hθ1 hu0 hu1 hu hJ0 hJ hsm0 hsm hy0 hy
    hs0 hs hk0 hk hd0 hd
  have hCb : 0 ≤ (y + d) ^ 4 / 4 := by positivity
  have hx := xiCI_B_gen hn hθ0 hθ1 hhi hr0 hr hCb
  exact mean_gen hn hτ h hHS (hx.trans hsx)

/-- The last numeric step: the radius term and the square. -/
theorem centre_fin_gen {n : ℕ} (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ}
    (hθ0 : 46 / 100 ≤ thetaC c τ)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    {n1 θhi cd sqn q xr X ξ : ℝ} (hn1 : 16250 ≤ n1) (hn1n : n1 ≤ n)
    (hhi : thetaC c τ ≤ θhi) (hcd0 : 0 ≤ cd)
    (hcore : √(2 / ((mA n : ℕ) : ℝ)) *
        nrm (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      √(2 / (n : ℝ) / n) * (cd + xiNr n (thetaC c τ) (11911 / 10000) +
        epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12)))
    (hsqn0 : 0 < sqn) (hsqn : sqn ^ 2 ≤ n1) (hq0 : 0 ≤ q) (hq : 11911 / 10000 * θhi ≤ q ^ 2)
    (hxr : θhi * (1 + 18334 / 1000 / n1) + q ≤ xr * sqn)
    (hX : cd + xr + 752 / 100000 ≤ X) (hξ : X ^ 2 ≤ ξ) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      ξ * (2 / (n : ℝ)) / n := by
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn10 : (0 : ℝ) < n1 := by linarith
  obtain ⟨hε0, hε⟩ := BstLean.Part154.R.epsJ_le16 hn
  obtain ⟨hNb0, hNb, -, -⟩ := BstLean.Part154.R.Nbar_le16 hn
  have hθp : 0 ≤ thetaC c τ := by linarith
  have hθhi0 : 0 ≤ θhi := by linarith
  have hsn : sqn ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' hsqn0]; linarith
  have hsq : √(11911 / 10000 * thetaC c τ) ≤ q := by
    rw [Real.sqrt_le_iff]
    refine ⟨hq0, ?_⟩
    nlinarith
  have hNb' : N22bar n 12 ≤ 18334 / 1000 / n1 := by
    refine hNb.trans ?_
    exact div_le_div_of_nonneg_left (by norm_num) hn10 hn1n
  have hxi : xiNr n (thetaC c τ) (11911 / 10000) ≤ xr := by
    unfold xiNr
    rw [div_le_iff₀ (lt_of_lt_of_le hsqn0 hsn)]
    have hp : thetaC c τ * (1 + N22bar n 12) ≤ θhi * (1 + 18334 / 1000 / n1) :=
      mul_le_mul hhi (by linarith) (by linarith) hθhi0
    have hxr0 : 0 ≤ xr := by
      have : 0 ≤ θhi * (1 + 18334 / 1000 / n1) + q := by positivity
      exact nonneg_of_mul_nonneg_left (this.trans hxr) hsqn0
    have : xr * sqn ≤ xr * √(n : ℝ) := mul_le_mul_of_nonneg_left hsn hxr0
    linarith
  have hN0 : 0 ≤ xiNr n (thetaC c τ) (11911 / 10000) := by unfold xiNr; positivity
  refine sq_form (by omega) _ (x := cd + xiNr n (thetaC c τ) (11911 / 10000) +
    epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12)) (by linarith) ?_ hcore
  have hb : cd + xiNr n (thetaC c τ) (11911 / 10000) +
      epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12) ≤ X := by linarith
  exact (pow_le_pow_left₀ (by linarith) hb 2).trans hξ

/-- **The generic numeric form with changes (A), (B), (C), (D)** (events of Part 154 and
`SD'`). -/
theorem centre_BD_gen {n : ℕ} (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n)
    {n1 θlo θhi u Jlo sm y s k d r sx dv sqn q xr X ξ : ℝ} (hn1 : 16250 ≤ n1) (hn1n : n1 ≤ n)
    (hlo0 : 0 < θlo) (hlo : θlo ≤ thetaC c τ) (hhi : thetaC c τ ≤ θhi)
    (hu0 : 0 < u) (hu1 : 2 * u < 1) (hu : 12 ≤ u ^ 2 * n1) (hJ0 : 0 ≤ Jlo)
    (hJ : Jlo ^ 2 * (1 + 2 * (1 - θlo) / (θlo * (1 - 2 * u))) ≤ 1) (hsm0 : 0 ≤ sm)
    (hsm : (1 - Jlo / 2 + 216 / 100000) * (1 - Jlo / 2 * (1 - 1 / n1) + 216 / 100000) +
      1 / (2 * n1) ≤ sm ^ 2)
    (hy0 : 0 ≤ y) (hy : 4 * ((sm + 247 / 100000) ^ 2 + 247 / 1000000) ≤ y ^ 4)
    (hs0 : 0 < s) (hs : s ^ 2 ≤ θlo) (hk0 : 0 < k) (hk : k ^ 4 ≤ n1 ^ 3) (hd0 : 0 ≤ d)
    (hd : 98 / 10 ≤ d * s * k)
    (hr0 : 0 ≤ r) (hr : θhi ≤ r ^ 2) (hsx0 : 0 ≤ sx)
    (hsx : 26973 / 100000 * ((y + d) ^ 4 / 4) * (θhi * r) + 369 / 100000 ≤ sx ^ 2)
    (hdv0 : 0 ≤ dv)
    (hdv : 48 * (1011 / 1000 - (129521 / 100000 - 4 * (1031745 / 1000000) / n1) * θlo / 2) ≤
      dv ^ 2 * n1)
    (hsqn0 : 0 < sqn) (hsqn : sqn ^ 2 ≤ n1) (hq0 : 0 ≤ q) (hq : 11911 / 10000 * θhi ≤ q ^ 2)
    (hxr : θhi * (1 + 18334 / 1000 / n1) + q ≤ xr * sqn)
    (hX : sx + dv + xr + 752 / 100000 ≤ X) (hξ : X ^ 2 ≤ ξ) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      ξ * (2 / (n : ℝ)) / n := by
  have hn8 : 8192 ≤ n := by omega
  have hn1' : 1 ≤ n := by omega
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn10 : (0 : ℝ) < n1 := by linarith
  have hm := BstLean.Part130.one_le_mA hn1'
  have hmean := mean_B_gen hn hτ hθ0 hθ1 h hn1 hn1n hlo0 hlo hhi hu0 hu1 hu hJ0 hJ hsm0 hsm
    hy0 hy hs0 hs hk0 hk hd0 hd hr0 hr hsx
  obtain ⟨⟨-, hop2, -⟩, hΓ, -, hsc0⟩ := BstLean.Part153.AStage_bounds hn8 h.1.1
  have hsc : csC * τ ^ 2 ≤ sO2 A₁ c τ := hsc0
  have hρ2 := rhoC_sqP c τ
  rw [← hρ2] at hΓ
  have hΓ' : gO A₁ c τ ≤ (1 + 11 / 1000) * (2 / (n : ℝ)) * rhoC c τ ^ 2 := by
    rw [← BstLean.Part153.GamS_eq_gO hm]
    have := (abs_le.mp hΓ).2
    linarith
  obtain ⟨hw1, hw⟩ := BstLean.Part154.R.wn_bounds_NumA16 hn
  obtain ⟨hcs1, hcs2⟩ := csC_bounds_NumA
  have hinv : 1 / (n : ℝ) ≤ 1 / n1 := one_div_le_one_div_of_le hn10 hn1n
  have hg : 129521 / 100000 - 4 * (1031745 / 1000000) / n1 ≤ csC - 4 * wn n / n := by
    have e1 : 4 * wn n / (n : ℝ) = 4 * wn n * (1 / n) := by ring
    have e2 : 4 * (1031745 / 1000000 : ℝ) / n1 = 4 * (1031745 / 1000000) * (1 / n1) := by ring
    rw [e1, e2]
    have : 4 * wn n * (1 / (n : ℝ)) ≤ 4 * (1031745 / 1000000) * (1 / n1) :=
      mul_le_mul (by linarith) hinv (by positivity) (by norm_num)
    linarith
  have hg0 : 0 ≤ 129521 / 100000 - 4 * (1031745 / 1000000 : ℝ) / n1 := by
    have : 4 * (1031745 / 1000000 : ℝ) / n1 ≤ 4 * (1031745 / 1000000) / 16250 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn1
    have h2 : 4 * (1031745 / 1000000 : ℝ) / 16250 ≤ 1 := by norm_num
    linarith
  have hprod : (129521 / 100000 - 4 * (1031745 / 1000000) / n1) * θlo ≤
      (csC - 4 * wn n / n) * thetaC c τ := mul_le_mul hg hlo hlo0.le (hg0.trans hg)
  have hdv' : 48 * (1 + 11 / 1000 - (csC - 4 * wn n / n) * thetaC c τ / 2) ≤ dv ^ 2 * n := by
    have h3 : dv ^ 2 * n1 ≤ dv ^ 2 * n := mul_le_mul_of_nonneg_left hn1n (sq_nonneg _)
    linarith
  have hD' : A₂ ∉ BadD' A₁ c τ 12 := fun hb => hD hb
  have c1 := dC_le_D hn1' A₁ A₂ c hτ (sq_nonneg sx) hdv0 hmean hop2 hsc hΓ' hdv' hD'
  rw [Real.sqrt_sq hsx0] at c1
  have hcore := centre_from_dC hn hτ hθ0 hθ1 h c1
  exact centre_fin_gen hn hθ0 hn1 hn1n hhi (by linarith) hcore hsqn0 hsqn hq0 hq hxr hX hξ

end BstLean.Part160.R

