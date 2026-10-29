import BstLean.Part154Lip
import BstLean.Part154Rad

/-!
# Part 154: Lemma MA (ii), (iv) and Lemma MP (deterministic steps on the events)

`U = ρ·√(γ_A/n)` with `γ_A = 2/n`; in Lean `rhoC c τ * √(2 / n / n)`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm GamS wn Eop Pb XiS N2 hid2Mean_cr)

/-- `𝖼_d = √ξ_c + √(16L_c(1 + δ_e)/n)`. -/
noncomputable def cD (n : ℕ) (Lc δe ξc : ℝ) : ℝ := √ξc + √(16 * Lc * (1 + δe) / n)

/-- `p_low = √((1 − δ_e)/π)·(1 − 13/n)`. -/
noncomputable def plow (n : ℕ) (δe : ℝ) : ℝ := √((1 - δe) / π) * (1 - 13 / (n : ℝ))

/-- `𝖾 = 2√(π b_n/(n(1 − δ_e))) + π ξ_c/(n(1 − δ_e))`. -/
noncomputable def eMP (n : ℕ) (δe ξc bn : ℝ) : ℝ :=
  2 * √(π * bn / (n * (1 - δe))) + π * ξc / (n * (1 - δe))

/-- `Π̄`. -/
noncomputable def PiBarMP (n : ℕ) (Lc δe ξc bn : ℝ) : ℝ :=
  (√bn + ξc * √π / (2 * √(n * (1 - δe)))) * (1 + eMP n δe ξc bn) + 8 / ((n : ℝ) * √(n : ℝ)) +
    √(16 * Lc * (1 + δe) / n)

/-- The bound of `|Λ|/U_r`: `(1 + ς_d)·Π̄ + 𝖼_d²/(2 p_low √n)`, `ς_d = 𝖼_d/(2 p_low √n)`. -/
noncomputable def LamMP (n : ℕ) (Lc δe ξc bn : ℝ) : ℝ :=
  (1 + cD n Lc δe ξc / (2 * plow n δe * √(n : ℝ))) * PiBarMP n Lc δe ξc bn +
    cD n Lc δe ξc ^ 2 / (2 * plow n δe * √(n : ℝ))

open BstLean.Part153 (nrm_nonneg nrm_sq nrm_smul nrm_add_le abs_nrm_sub_le abs_dot_le_nrm mA_cast
  GamS_nonneg GamS_eq_gO rb_bounds Pb_nonneg)

/-! ## Auxiliary lemmas (real numbers) -/

private lemma le_of_sq_le_MP {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hc
  push Not at hc
  nlinarith [mul_pos (sub_pos.mpr hc) (by linarith : 0 < a + b)]

private lemma sqrt_nn_MP {N : ℝ} (hN : 0 < N) : √(2 / N / N) = √2 / N := by
  rw [div_div, Real.sqrt_div (by norm_num), Real.sqrt_mul_self hN.le]

private lemma sqrt_n_MP (N : ℝ) : √(2 / N) = √2 / √N := Real.sqrt_div (by norm_num) N

private lemma U_sq_MP {N : ℝ} (ρ : ℝ) (hN : 0 < N) :
    (ρ * √(2 / N / N)) ^ 2 = ρ ^ 2 * (2 / N / N) := by
  rw [mul_pow, Real.sq_sqrt (by positivity)]

private lemma sqrt_n_split_MP {N : ℝ} (hN : 0 < N) : √(2 / N) = √(2 / N / N) * √N := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

/-- The deviation `√(2L_c t)·2√Γ ≤ U·√(16L_c(1 + δ_e)/n)`. -/
private lemma dev_MP {N t ρ Lc δe Γ : ℝ} (ht : t = 2 / N ^ 2) (hN : 0 < N) (hρ : 0 ≤ ρ)
    (hLc : 0 ≤ Lc) (hδe : 0 ≤ δe) (hΓ0 : 0 ≤ Γ) (hΓ : Γ ≤ (1 + δe) * (2 / N) * ρ ^ 2) :
    √(2 * Lc * t) * (2 * √Γ) ≤ ρ * √(2 / N / N) * √(16 * Lc * (1 + δe) / N) := by
  subst ht
  apply le_of_sq_le_MP (by positivity)
  have e1 : (√(2 * Lc * (2 / N ^ 2)) * (2 * √Γ)) ^ 2 = 2 * Lc * (2 / N ^ 2) * (4 * Γ) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hΓ0]; norm_num
  have e2 : (ρ * √(2 / N / N) * √(16 * Lc * (1 + δe) / N)) ^ 2 =
      ρ ^ 2 * (2 / N / N) * (16 * Lc * (1 + δe) / N) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  rw [e1, e2]
  have h1 : 2 * Lc * (2 / N ^ 2) * (4 * Γ) ≤
      2 * Lc * (2 / N ^ 2) * (4 * ((1 + δe) * (2 / N) * ρ ^ 2)) := by gcongr
  have e3 : 2 * Lc * (2 / N ^ 2) * (4 * ((1 + δe) * (2 / N) * ρ ^ 2)) =
      ρ ^ 2 * (2 / N / N) * (16 * Lc * (1 + δe) / N) := by
    field_simp
    ring
  linarith

private lemma MPa_core {N t Γ rb2 E P : ℝ} (ht : t = 2 / N ^ 2) (hN : 8192 ≤ N) (hΓ0 : 0 ≤ Γ)
    (hΓ : Γ ≤ π * rb2) (hE : 0 ≤ E) (hvar : rb2 - E ^ 2 ≤ t * Γ)
    (hP : E - √(2 * 12 * t) * √Γ ≤ P) : √rb2 * (1 - 13 / N) ≤ P := by
  subst ht
  have hN0 : (0 : ℝ) < N := by linarith
  have hπ := Real.pi_pos
  have hπ2 := Real.pi_lt_d2
  have hrb0 : 0 ≤ rb2 := by
    by_contra h
    push Not at h
    nlinarith
  obtain ⟨r, hrd⟩ : ∃ r, r = √rb2 := ⟨_, rfl⟩
  rw [← hrd]
  have hr0 : 0 ≤ r := by rw [hrd]; exact Real.sqrt_nonneg _
  have hr2 : r ^ 2 = rb2 := by rw [hrd]; exact Real.sq_sqrt hrb0
  obtain ⟨x, hx⟩ : ∃ x, x = 2 * π / N ^ 2 := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hxN : x ≤ 0.7 / N := by
    rw [hx, div_le_div_iff₀ (by positivity) hN0]
    nlinarith
  have hN1 : 0.7 / N ≤ 1 := by
    rw [div_le_one hN0]; linarith
  have hx1 : x ≤ 1 := hxN.trans hN1
  have h1 : r * (1 - x) ≤ E := by
    apply le_of_sq_le_MP hE
    have h3 : 2 / N ^ 2 * Γ ≤ x * r ^ 2 := by
      rw [hx, hr2]
      calc 2 / N ^ 2 * Γ ≤ 2 / N ^ 2 * (π * rb2) := by gcongr
        _ = _ := by ring
    nlinarith [mul_nonneg (mul_nonneg hx0 (sub_nonneg.mpr hx1)) (sq_nonneg r)]
  have h2 : √(2 * 12 * (2 / N ^ 2)) * √Γ ≤ 12.3 / N * r := by
    apply le_of_sq_le_MP (mul_nonneg (by positivity) hr0)
    have e1 : (√(2 * 12 * (2 / N ^ 2)) * √Γ) ^ 2 = 2 * 12 * (2 / N ^ 2) * Γ := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hΓ0]
    rw [e1, mul_pow, hr2]
    calc 2 * 12 * (2 / N ^ 2) * Γ ≤ 2 * 12 * (2 / N ^ 2) * (π * rb2) := by gcongr
      _ = (48 * π) / N ^ 2 * rb2 := by ring
      _ ≤ (12.3 : ℝ) ^ 2 / N ^ 2 * rb2 := by gcongr; nlinarith
      _ = _ := by ring
  have h4 : r * x ≤ r * (0.7 / N) := mul_le_mul_of_nonneg_left hxN hr0
  have e5 : r * (1 - 13 / N) = r * (1 - x) - 12.3 / N * r + (r * x - r * (0.7 / N)) := by ring
  rw [e5]
  linarith

private lemma root_diff_MP {rh rb q : ℝ} (hrb : 0 < rb) (hrh : 0 ≤ rh) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2) (h : |rh ^ 2 - rb ^ 2| ≤ q * rb ^ 2) :
    |rh - rb| ≤ q * rb / 2 * (1 + q) := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have hv0 : 0 ≤ q * rb / 2 * (1 + q) := by positivity
  rw [abs_le]
  constructor
  · by_contra hc
    push Not at hc
    obtain ⟨v, hv⟩ : ∃ v, v = q * rb / 2 * (1 + q) := ⟨_, rfl⟩
    rw [← hv] at hc hv0
    have hw : 0 < (rb - rh) - v := by linarith
    have hqq : q * (1 + q) ≤ 3 / 4 := by nlinarith
    have hvr : v ≤ 3 / 8 * rb := by
      calc v = q * (1 + q) / 2 * rb := by rw [hv]; ring
        _ ≤ 3 / 4 / 2 * rb := by gcongr
        _ = _ := by ring
    have hprod : 0 < ((rb - rh) - v) * (2 * rb - (rb - rh) - v) := mul_pos hw (by linarith)
    have hvq : q * rb ^ 2 ≤ v * (2 * rb - v) := by
      have e : v * (2 * rb - v) - q * rb ^ 2 = rb ^ 2 * q ^ 2 * ((1 - q) * (3 + q)) / 4 := by
        rw [hv]; ring
      have h3 : 0 ≤ (1 - q) * (3 + q) := mul_nonneg (by linarith) (by linarith)
      have h4 : 0 ≤ rb ^ 2 * q ^ 2 * ((1 - q) * (3 + q)) / 4 :=
        div_nonneg (mul_nonneg (by positivity) h3) (by norm_num)
      linarith
    have hid : ((rb - rh) - v) * (2 * rb - (rb - rh) - v) =
        (rb ^ 2 - rh ^ 2) - v * (2 * rb - v) := by ring
    linarith
  · by_cases hle : rh ≤ rb
    · linarith
    · push Not at hle
      have h3 : (rh - rb) * (2 * rb) ≤ q * rb ^ 2 := by nlinarith
      have h4 : rh - rb ≤ q * rb ^ 2 / (2 * rb) := (le_div_iff₀ (by positivity)).mpr h3
      have e : q * rb ^ 2 / (2 * rb) = q * rb / 2 := by field_simp
      have h5 : 0 ≤ q * rb / 2 * q := by positivity
      rw [e] at h4
      have e2 : q * rb / 2 * (1 + q) = q * rb / 2 + q * rb / 2 * q := by ring
      linarith

private lemma mean_core_MP {U sb ξ μ rb rh D2 T Eh Eb N sN : ℝ} (hU : 0 < U) (hsb : 0 ≤ sb)
    (hξ : 0 ≤ ξ) (hμ : 0 < μ) (hrb : 0 < rb) (hrh : 0 ≤ rh) (hN : 0 < N) (hsN : 0 < sN)
    (hUμ : U ≤ μ * rb) (he : 2 * μ * sb + μ ^ 2 * ξ ≤ 1 / 10)
    (hcross : |rh ^ 2 - rb ^ 2| ≤ 2 * (U * sb) * rb + D2) (hD : D2 ≤ U ^ 2 * ξ)
    (hEh : 0 ≤ Eh) (hEb : 0 ≤ Eb) (hJh : Eh ^ 2 ≤ rh ^ 2) (hJb : Eb ^ 2 ≤ rb ^ 2)
    (hvh : rh ^ 2 - Eh ^ 2 ≤ T) (hvb : rb ^ 2 - Eb ^ 2 ≤ T) (hT : T ≤ 2.022 * U ^ 2 / N)
    (hμs : μ * sN ≤ 1.9) :
    |Eh - Eb| ≤ U * ((sb + ξ * μ / 2) * (1 + (2 * μ * sb + μ ^ 2 * ξ)) + 8 / (N * sN)) := by
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = U / rb := ⟨_, rfl⟩
  have hUl : U = lam * rb := by rw [hlam]; field_simp
  have hl0 : 0 < lam := by rw [hlam]; positivity
  have hlμ : lam ≤ μ := by rw [hlam, div_le_iff₀ hrb]; exact hUμ
  obtain ⟨q, hq⟩ : ∃ q, q = 2 * lam * sb + lam ^ 2 * ξ := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hqe : q ≤ 2 * μ * sb + μ ^ 2 * ξ := by rw [hq]; gcongr
  have hq10 : q ≤ 1 / 10 := hqe.trans he
  have hc' : |rh ^ 2 - rb ^ 2| ≤ q * rb ^ 2 := by
    refine hcross.trans ?_
    have e : 2 * (U * sb) * rb + U ^ 2 * ξ = q * rb ^ 2 := by rw [hq, hUl]; ring
    linarith
  have hD1 := root_diff_MP hrb hrh hq0 (by linarith) hc'
  have hX : q * rb / 2 = U * (sb + lam * ξ / 2) := by rw [hq, hUl]; ring
  have hA : |rh - rb| ≤ U * ((sb + ξ * μ / 2) * (1 + (2 * μ * sb + μ ^ 2 * ξ))) := by
    refine hD1.trans ?_
    rw [hX, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hU.le
    have h7 := mul_le_mul_of_nonneg_right hlμ hξ
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  have hrh94 : 0.94 * rb ≤ rh := by
    apply le_of_sq_le_MP hrh
    have h8 := (abs_le.mp hc').1
    nlinarith [mul_nonneg (sub_nonneg.mpr hq10) (sq_nonneg rb)]
  have hrh0 : 0 < rh := by linarith [mul_pos (by norm_num : (0 : ℝ) < 0.94) hrb]
  have hEbr : Eb ≤ rb := le_of_sq_le_MP hrb.le hJb
  have hEhr : Eh ≤ rh := le_of_sq_le_MP hrh hJh
  have hT' : T ≤ 2.022 * U * lam / N * rb := by
    refine hT.trans (le_of_eq ?_)
    rw [hUl]; ring
  have hcb : rb - Eb ≤ 2.022 * U * μ / N := by
    have h1 : (rb - Eb) * rb ≤ 2.022 * U * lam / N * rb := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hEbr) hEb]
    have h2 := le_of_mul_le_mul_right h1 hrb
    refine h2.trans ?_
    gcongr
  have hch : rh - Eh ≤ 2.16 * U * μ / N := by
    have h1 : (rh - Eh) * rh ≤ 2.16 * U * lam / N * rh := by
      have h0 : (rh - Eh) * rh ≤ T := by nlinarith [mul_nonneg (sub_nonneg.mpr hEhr) hEh]
      have h3 : 2.022 * U * lam / N * rb ≤ 2.16 * U * lam / N * rh := by
        have hc0 : 0 ≤ U * lam / N := by positivity
        calc 2.022 * U * lam / N * rb = (U * lam / N) * (2.022 * rb) := by ring
          _ ≤ (U * lam / N) * (2.16 * rh) := mul_le_mul_of_nonneg_left (by linarith) hc0
          _ = _ := by ring
      linarith
    have h2 := le_of_mul_le_mul_right h1 hrh0
    refine h2.trans ?_
    gcongr
  have hμ' : μ ≤ 1.9 / sN := by rw [le_div_iff₀ hsN]; exact hμs
  have hfin : 2.022 * U * μ / N + 2.16 * U * μ / N ≤ U * (8 / (N * sN)) := by
    calc 2.022 * U * μ / N + 2.16 * U * μ / N = 4.182 * U / N * μ := by ring
      _ ≤ 4.182 * U / N * (1.9 / sN) := mul_le_mul_of_nonneg_left hμ' (by positivity)
      _ = U * (7.9458 / (N * sN)) := by ring
      _ ≤ _ := by gcongr; norm_num
  have h9 : |Eh - Eb| ≤ |rh - rb| + (rh - Eh) + (rb - Eb) := by
    rw [abs_le]
    obtain ⟨a1, a2⟩ := abs_le.mp (le_refl |rh - rb|)
    constructor <;> linarith
  rw [mul_add]
  linarith

private lemma mean_MP {n : ℕ} {t U ξ bn Γ rh2 rb2 D2 Eh Eb : ℝ} (ht : t = 2 / (n : ℝ) ^ 2)
    (hN : (8192 : ℝ) ≤ n) (hU : 0 < U) (hξ : 0 ≤ ξ) (hbn : 0 ≤ bn)
    (he : eMP n (11 / 1000) ξ bn ≤ 1 / 10)
    (hΓl : (1 - 11 / 1000) * (U ^ 2 * n) ≤ Γ) (hΓu : Γ ≤ (1 + 11 / 1000) * (U ^ 2 * n))
    (hΓπ : Γ ≤ π * rb2) (hrh2 : 0 ≤ rh2) (hD : D2 ≤ U ^ 2 * ξ)
    (hcross : |rh2 - rb2| ≤ 2 * (U * √bn) * √rb2 + D2)
    (hEh : 0 ≤ Eh) (hEb : 0 ≤ Eb) (hJh : Eh ^ 2 ≤ rh2) (hJb : Eb ^ 2 ≤ rb2)
    (hvh : rh2 - Eh ^ 2 ≤ t * Γ) (hvb : rb2 - Eb ^ 2 ≤ t * Γ) :
    |Eh - Eb| ≤ U * ((√bn + ξ * √π / (2 * √((n : ℝ) * (1 - 11 / 1000)))) *
      (1 + eMP n (11 / 1000) ξ bn) + 8 / ((n : ℝ) * √(n : ℝ))) := by
  subst ht
  have hN0 : (0 : ℝ) < n := by linarith
  have hπ := Real.pi_pos
  have hK0 : 0 < (n : ℝ) * (1 - 11 / 1000) := mul_pos hN0 (by norm_num)
  have hrb2 : 0 < rb2 := by
    have h1 : 0 < (1 - 11 / 1000) * (U ^ 2 * n) :=
      mul_pos (by norm_num) (mul_pos (pow_pos hU 2) hN0)
    by_contra h
    push Not at h
    nlinarith
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = √π / √((n : ℝ) * (1 - 11 / 1000)) := ⟨_, rfl⟩
  have hμ0 : 0 < μ := by
    rw [hμd]; exact div_pos (Real.sqrt_pos.mpr hπ) (Real.sqrt_pos.mpr hK0)
  have hμ2 : μ ^ 2 = π / ((n : ℝ) * (1 - 11 / 1000)) := by
    rw [hμd, div_pow, Real.sq_sqrt hπ.le, Real.sq_sqrt hK0.le]
  have heq : eMP n (11 / 1000) ξ bn = 2 * μ * √bn + μ ^ 2 * ξ := by
    unfold eMP
    rw [hμ2, Real.sqrt_div (mul_nonneg hπ.le hbn), Real.sqrt_mul hπ.le, hμd]
    ring
  have hμs : μ * √(n : ℝ) ≤ 1.9 := by
    apply le_of_sq_le_MP (by norm_num)
    rw [mul_pow, hμ2, Real.sq_sqrt hN0.le, div_mul_eq_mul_div, div_le_iff₀ hK0]
    nlinarith [mul_pos (sub_pos.mpr Real.pi_lt_d2) hN0]
  have hrb : 0 < √rb2 := Real.sqrt_pos.mpr hrb2
  have hrbsq : √rb2 ^ 2 = rb2 := Real.sq_sqrt hrb2.le
  have hrhsq : √rh2 ^ 2 = rh2 := Real.sq_sqrt hrh2
  have hUμ : U ≤ μ * √rb2 := by
    apply le_of_sq_le_MP (mul_nonneg hμ0.le hrb.le)
    rw [mul_pow, hμ2, hrbsq, div_mul_eq_mul_div, le_div_iff₀ hK0]
    linarith
  have hT : 2 / (n : ℝ) ^ 2 * Γ ≤ 2.022 * U ^ 2 / n := by
    calc 2 / (n : ℝ) ^ 2 * Γ ≤ 2 / (n : ℝ) ^ 2 * ((1 + 11 / 1000) * (U ^ 2 * n)) := by gcongr
      _ = _ := by
        rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
        ring
  have hcore := mean_core_MP (U := U) (sb := √bn) (ξ := ξ) (μ := μ) (rb := √rb2) (rh := √rh2)
    (D2 := D2) (T := 2 / (n : ℝ) ^ 2 * Γ) (Eh := Eh) (Eb := Eb) (N := n) (sN := √(n : ℝ))
    hU (Real.sqrt_nonneg _) hξ hμ0 hrb (Real.sqrt_nonneg _) hN0 (Real.sqrt_pos.mpr hN0)
    hUμ (by rw [← heq]; exact he) (by rw [hrhsq, hrbsq]; exact hcross) hD hEh hEb
    (by rw [hrhsq]; exact hJh) (by rw [hrbsq]; exact hJb)
    (by rw [hrhsq]; exact hvh) (by rw [hrbsq]; exact hvb) hT hμs
  rw [heq]
  have e : ξ * √π / (2 * √((n : ℝ) * (1 - 11 / 1000))) = ξ * μ / 2 := by rw [hμd]; ring
  rw [e]
  exact hcore

private lemma lam_core_MP {Λ Pb Ph dC U Pi0 cd p sN : ℝ} (hPb : 0 < Pb) (hU : 0 < U) (hp : 0 < p)
    (hsN : 0 < sN) (hdC0 : 0 ≤ dC) (hΔd : |Ph - Pb| ≤ dC) (hΔ : |Ph - Pb| ≤ U * Pi0)
    (hd : dC ≤ U * cd) (hlow : U * sN * p ≤ Pb)
    (hΛ : Λ * Pb = (Ph ^ 2 - Pb ^ 2 - dC ^ 2) / 2) :
    |Λ| ≤ U * ((1 + cd / (2 * p * sN)) * Pi0 + cd ^ 2 / (2 * p * sN)) := by
  have hcd : 0 ≤ cd := by
    by_contra h
    push Not at h
    nlinarith
  have hPi0 : 0 ≤ Pi0 := by
    have := abs_nonneg (Ph - Pb)
    by_contra h
    push Not at h
    nlinarith
  obtain ⟨i, hi⟩ : ∃ i, i = 1 / (2 * Pb) := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, j = 1 / (2 * p * sN) := ⟨_, rfl⟩
  have hi0 : 0 ≤ i := by rw [hi]; positivity
  have hij : U * i ≤ j := by
    rw [hi, hj, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have eΛ : Λ = (Ph - Pb) * (1 + (Ph - Pb) * i) - dC ^ 2 * i := by
    have e1 : Λ = (Ph ^ 2 - Pb ^ 2 - dC ^ 2) / 2 / Pb := by
      rw [← hΛ]; field_simp
    rw [e1, hi]
    field_simp
    ring
  obtain ⟨a, ha⟩ : ∃ a, a = |Ph - Pb| := ⟨_, rfl⟩
  rw [← ha] at hΔd hΔ
  have ha0 : 0 ≤ a := by rw [ha]; exact abs_nonneg _
  have hb1 : |Λ| ≤ a * (1 + a * i) + dC ^ 2 * i := by
    rw [eΛ]
    have h1 := abs_sub ((Ph - Pb) * (1 + (Ph - Pb) * i)) (dC ^ 2 * i)
    have h2 : |dC ^ 2 * i| = dC ^ 2 * i := abs_of_nonneg (by positivity)
    have h3 : |1 + (Ph - Pb) * i| ≤ 1 + a * i := by
      have h4 := abs_add_le 1 ((Ph - Pb) * i)
      rw [abs_one, abs_mul, abs_of_nonneg hi0, ← ha] at h4
      exact h4
    have h5 : |(Ph - Pb) * (1 + (Ph - Pb) * i)| ≤ a * (1 + a * i) := by
      rw [abs_mul, ← ha]
      exact mul_le_mul_of_nonneg_left h3 ha0
    linarith
  have s1 : a * (1 + a * i) ≤ (U * Pi0) * (1 + (U * cd) * i) :=
    mul_le_mul hΔ (by linarith [mul_le_mul_of_nonneg_right (hΔd.trans hd) hi0])
      (add_nonneg zero_le_one (mul_nonneg ha0 hi0)) (mul_nonneg hU.le hPi0)
  have s2 : dC ^ 2 * i ≤ (U * cd) ^ 2 * i :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hdC0 hd 2) hi0
  have s3 : (U * Pi0) * (1 + (U * cd) * i) + (U * cd) ^ 2 * i =
      U * (Pi0 * (1 + cd * (U * i)) + cd ^ 2 * (U * i)) := by ring
  have s4 : U * (Pi0 * (1 + cd * (U * i)) + cd ^ 2 * (U * i)) ≤
      U * (Pi0 * (1 + cd * j) + cd ^ 2 * j) :=
    mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left (by linarith [mul_le_mul_of_nonneg_left hij hcd]) hPi0)
      (mul_le_mul_of_nonneg_left hij (sq_nonneg cd))) hU.le
  have s5 : U * ((1 + cd / (2 * p * sN)) * Pi0 + cd ^ 2 / (2 * p * sN)) =
      U * (Pi0 * (1 + cd * j) + cd ^ 2 * j) := by rw [hj]; ring
  rw [s5]
  linarith

private lemma lam_id_MP {ι : Type*} [Fintype ι] (s : ℝ) (h b : ι → ℝ) (hb : 0 < nrm b) :
    ((s • (h - b)) ⬝ᵥ ((nrm b)⁻¹ • b)) * (s * nrm b) =
      ((s * nrm h) ^ 2 - (s * nrm b) ^ 2 - (s * nrm (h - b)) ^ 2) / 2 := by
  have hns : normSq h = normSq b + 2 * ((h - b) ⬝ᵥ b) + normSq (h - b) := by
    unfold normSq dotProduct
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
  have hinv : (nrm b)⁻¹ * nrm b = 1 := inv_mul_cancel₀ hb.ne'
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, mul_pow, mul_pow, mul_pow,
    nrm_sq, nrm_sq, nrm_sq, hns]
  linear_combination (s ^ 2 * ((h - b) ⬝ᵥ b)) * hinv

private lemma nrm_unit_le_MP {ι : Type*} [Fintype ι] (b : ι → ℝ) : nrm ((nrm b)⁻¹ • b) ≤ 1 := by
  rw [nrm_smul, abs_of_nonneg (inv_nonneg.mpr (nrm_nonneg _))]
  by_cases h : nrm b = 0
  · rw [h]; simp
  · rw [inv_mul_cancel₀ h]

/-- Lemma MA (iii) in the unit `√(γ_A/n)`, with the bounds of `N₂₂` and `Ξ`. -/
private lemma rad_MP {n : ℕ} (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {Nb MP : ℝ} (hMP : 0 ≤ MP)
    (hN : N2 2 A₁ A₂ c τ ≤ Nb) (hXi : XiS A₁ A₂ c τ ≤ MP * (2 / (n : ℝ)) / n) :
    √(2 / ((mA n : ℕ) : ℝ)) *
        nrm (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • hbar2 A₁ A₂ c τ) ≤
      √(2 / (n : ℝ) / n) * ((thetaC c τ * (1 + Nb) + √(MP * thetaC c τ)) / √(n : ℝ)) := by
  have hN0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hθ := (thetaC_bounds (by omega) c hτ).1
  have h := radius_le hn A₁ A₂ c hτ
  have hθn : 0 ≤ thetaC c τ / n := div_nonneg hθ.le hN0.le
  have e1 : √(2 / (n : ℝ)) * (1 + Nb) * (thetaC c τ / n) =
      √(2 / (n : ℝ) / n) * (thetaC c τ * (1 + Nb) / √(n : ℝ)) := by
    rw [sqrt_nn_MP hN0, sqrt_n_MP]
    ring
  have e2 : √(MP * (2 / (n : ℝ)) / n * (thetaC c τ / n)) =
      √(2 / (n : ℝ) / n) * (√(MP * thetaC c τ) / √(n : ℝ)) := by
    rw [← Real.sqrt_div (mul_nonneg hMP hθ.le), ← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  have a1 : √(2 / (n : ℝ)) * (1 + N2 2 A₁ A₂ c τ) * (thetaC c τ / n) ≤
      √(2 / (n : ℝ)) * (1 + Nb) * (thetaC c τ / n) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)) hθn
  have a2 : √(XiS A₁ A₂ c τ * (thetaC c τ / n)) ≤
      √(MP * (2 / (n : ℝ)) / n * (thetaC c τ / n)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hXi hθn)
  rw [e1] at a1
  rw [e2] at a2
  have e3 : √(2 / (n : ℝ) / n) * ((thetaC c τ * (1 + Nb) + √(MP * thetaC c τ)) / √(n : ℝ)) =
      √(2 / (n : ℝ) / n) * (thetaC c τ * (1 + Nb) / √(n : ℝ)) +
        √(2 / (n : ℝ) / n) * (√(MP * thetaC c τ) / √(n : ℝ)) := by ring
  rw [e3]
  linarith

/-- **Lemma MA (ii)**, the bound on `E_D`: `|𝐝| ≤ U_r·𝖼_d`. -/
theorem MA_ii {n : ℕ} (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) {Lc δe ξc : ℝ}
    (hLc : 0 ≤ Lc) (hδe : 0 ≤ δe) (hξ : 0 ≤ ξc)
    (hmean : ∫ A₂, dC A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * ξc)
    (hΓ : GamS A₁ c τ ≤ (1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2)
    (hD : A₂ ∉ BadD A₁ c τ Lc) :
    dC A₁ A₂ c τ ≤ rhoC c τ * √(2 / (n : ℝ) / n) * cD n Lc δe ξc := by
  have hN0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := one_le_mA hn
  have hmc := mA_cast n
  have ht : 2 / ((mA n : ℕ) : ℝ) = 2 / (n : ℝ) ^ 2 := by rw [hmc]
  have hρ0 : 0 ≤ rhoC c τ := by unfold rhoC; exact Real.sqrt_nonneg _
  obtain ⟨hi1, hi2⟩ := dC_integrable hm A₁ c τ
  simp only [BadD, Set.mem_ofPred_eq, not_lt] at hD
  have hJ := BstLean.Part133.sq_integral_le hi2
  have h1 : ∫ A₂, dC A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤ rhoC c τ * √(2 / (n : ℝ) / n) * √ξc := by
    apply le_of_sq_le_MP (by positivity)
    rw [mul_pow, U_sq_MP _ hN0, Real.sq_sqrt hξ]
    exact hJ.trans hmean
  have h2 := dev_MP ht hN0 hρ0 hLc hδe (GamS_nonneg A₁ c τ) hΓ
  unfold cD
  rw [mul_add]
  linarith

/-- **Lemma MA (iv)**: `√t·|ā₂ − b°| ≤ √(γ_A/n)·(𝖼_d + (θ(1 + N̄₂₂) + √(M_P θ))/√n)`. -/
theorem MA_iv {n : ℕ} (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {cd Nb MP : ℝ} (hMP : 0 ≤ MP)
    (hd : dC A₁ A₂ c τ ≤ rhoC c τ * √(2 / (n : ℝ) / n) * cd)
    (hN : N2 2 A₁ A₂ c τ ≤ Nb) (hXi : XiS A₁ A₂ c τ ≤ MP * (2 / (n : ℝ)) / n) :
    √(2 / ((mA n : ℕ) : ℝ)) *
        nrm (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ) ≤
      √(2 / (n : ℝ) / n) * (cd + (thetaC c τ * (1 + Nb) + √(MP * thetaC c τ)) / √(n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hρ := rhoC_posP hn1 c hτ
  have hr := rad_MP hn A₁ A₂ c hτ hMP hN hXi
  have hs0 : 0 ≤ √(2 / ((mA n : ℕ) : ℝ)) := Real.sqrt_nonneg _
  have e : hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ =
      (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • hbar2 A₁ A₂ c τ) +
        (rhoC c τ)⁻¹ • (hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ) := by
    rw [smul_sub]; abel
  have h1 := nrm_add_le (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • hbar2 A₁ A₂ c τ)
    ((rhoC c τ)⁻¹ • (hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ))
  rw [← e, nrm_smul, abs_of_pos (inv_pos.mpr hρ)] at h1
  have h2 : √(2 / ((mA n : ℕ) : ℝ)) *
      ((rhoC c τ)⁻¹ * nrm (hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ)) ≤ √(2 / (n : ℝ) / n) * cd := by
    have e2 : √(2 / ((mA n : ℕ) : ℝ)) *
        ((rhoC c τ)⁻¹ * nrm (hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ)) =
        (rhoC c τ)⁻¹ * dC A₁ A₂ c τ := by unfold dC; ring
    rw [e2, inv_mul_le_iff₀ hρ]
    linarith
  have h3 := mul_le_mul_of_nonneg_left h1 hs0
  rw [mul_add] at h3 ⊢
  linarith

/-- **Lemma MP (a)**: the lower norm of the oracle centre on `E_e ∩ E_Pb` (level `L_c = 12`,
`δ_e = 11/1000`). -/
theorem MP_a {n : ℕ} (hn : 8192 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hΓ : |GamS A₁ c τ - 2 / (n : ℝ) * rhoC c τ ^ 2| ≤ 11 / 1000 * (2 / (n : ℝ) * rhoC c τ ^ 2))
    (hPb : A₂ ∉ BadPb A₁ c τ 12) :
    rhoC c τ * √(2 / (n : ℝ)) * plow n (11 / 1000) ≤ Pb A₁ c τ A₂ := by
  have hn1 : 1 ≤ n := by omega
  have hN : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hm := one_le_mA hn1
  have hmc := mA_cast n
  have ht : 2 / ((mA n : ℕ) : ℝ) = 2 / (n : ℝ) ^ 2 := by rw [hmc]
  have hρ := rhoC_posP hn1 c hτ
  have hπ := Real.pi_pos
  obtain ⟨hb1, hb2, hbv⟩ := Pb_var hm A₁ c τ
  have hrb := (rb_bounds hm A₁ c τ).2.1
  rw [← GamS_eq_gO hm] at hrb
  simp only [BadPb, Set.mem_ofPred_eq, not_lt] at hPb
  have hΓ0 := GamS_nonneg A₁ c τ
  have hcore := MPa_core ht hN hΓ0 ((div_le_iff₀' hπ).mp hrb)
    (integral_nonneg fun A₂ => Pb_nonneg A₁ c τ A₂) hbv hPb
  have hlow : rhoC c τ * √(2 / (n : ℝ)) * √((1 - 11 / 1000) / π) ≤
      √(∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) := by
    apply Real.le_sqrt_of_sq_le
    have e1 : (rhoC c τ * √(2 / (n : ℝ)) * √((1 - 11 / 1000) / π)) ^ 2 =
        rhoC c τ ^ 2 * (2 / (n : ℝ)) * ((1 - 11 / 1000) / π) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity),
        Real.sq_sqrt (div_nonneg (by norm_num) hπ.le)]
    rw [e1]
    have h3 := (abs_le.mp hΓ).1
    calc rhoC c τ ^ 2 * (2 / (n : ℝ)) * ((1 - 11 / 1000) / π) =
          ((1 - 11 / 1000) * (2 / (n : ℝ) * rhoC c τ ^ 2)) / π := by ring
      _ ≤ GamS A₁ c τ / π := by gcongr; linarith
      _ ≤ _ := hrb
  have h13 : 0 ≤ 1 - 13 / (n : ℝ) := sub_nonneg.mpr ((div_le_one hN0).mpr (by linarith))
  unfold plow
  calc rhoC c τ * √(2 / (n : ℝ)) * (√((1 - 11 / 1000) / π) * (1 - 13 / (n : ℝ))) =
        (rhoC c τ * √(2 / (n : ℝ)) * √((1 - 11 / 1000) / π)) * (1 - 13 / (n : ℝ)) := by ring
    _ ≤ √(∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) * (1 - 13 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hlow h13
    _ ≤ _ := hcore

/-- **Lemma MP (b), the main step**: `|Λ| ≤ U_r·((1 + ς_d)Π̄ + 𝖼_d²/(2p_low√n))`,
`Λ = ⟨√t(h̄₂ − b′°), b̂°⟩`. The hypotheses `hmean`, `hcross` are the conclusions of `MA_i`,
`MA_cross`; `he` is the numerical condition `𝖾 ≤ 0.1`. -/
theorem MP_b {n : ℕ} (hn : 8192 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {ξc bn : ℝ} (hξ : 0 ≤ ξc) (hbn : 0 ≤ bn) (he : eMP n (11 / 1000) ξc bn ≤ 1 / 10)
    (hΓ : |GamS A₁ c τ - 2 / (n : ℝ) * rhoC c τ ^ 2| ≤ 11 / 1000 * (2 / (n : ℝ) * rhoC c τ ^ 2))
    (hmean : ∫ A₂, dC A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * ξc)
    (hcross : |∫ A₂, Ph A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) -
        ∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))| ≤
      2 * (rhoC c τ * √(2 / (n : ℝ) / n) * √bn) *
          √(∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) +
        ∫ A₂, dC A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)))
    (hD : A₂ ∉ BadD A₁ c τ 12) (hPi : A₂ ∉ BadPi A₁ c τ 12) (hPb : A₂ ∉ BadPb A₁ c τ 12) :
    |(√(2 / ((mA n : ℕ) : ℝ)) • (hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ)) ⬝ᵥ
        ((nrm (bO A₁ A₂ c τ))⁻¹ • bO A₁ A₂ c τ)| ≤
      rhoC c τ * √(2 / (n : ℝ) / n) * LamMP n 12 (11 / 1000) ξc bn := by
  have hn1 : 1 ≤ n := by omega
  have hN : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hm := one_le_mA hn1
  have hmc := mA_cast n
  have ht : 2 / ((mA n : ℕ) : ℝ) = 2 / (n : ℝ) ^ 2 := by rw [hmc]
  have hρ := rhoC_posP hn1 c hτ
  have hΓ0 := GamS_nonneg A₁ c τ
  obtain ⟨hΓl, hΓu⟩ := abs_le.mp hΓ
  have hΓu' : GamS A₁ c τ ≤ (1 + 11 / 1000) * (2 / (n : ℝ)) * rhoC c τ ^ 2 := by linarith
  have hd := MA_ii hn1 A₁ A₂ c τ (by norm_num : (0 : ℝ) ≤ 12)
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) hξ hmean hΓu' hD
  have hpa := MP_a hn A₁ A₂ c hτ hΓ hPb
  obtain ⟨hh1, hh2, hhv⟩ := Ph_var hm A₁ c τ
  obtain ⟨hb1, hb2, hbv⟩ := Pb_var hm A₁ c τ
  have hrb := (rb_bounds hm A₁ c τ).2.1
  rw [← GamS_eq_gO hm] at hrb
  simp only [BadPi, Set.mem_ofPred_eq, not_lt] at hPi
  have hdev := dev_MP ht hN0 hρ.le (by norm_num : (0 : ℝ) ≤ 12)
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) hΓ0 hΓu'
  have hint : ∫ A₂, DelP A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) =
      ∫ A₂, Ph A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) - ∫ A₂, Pb A₁ c τ A₂ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) := by
    unfold DelP
    exact integral_sub hh1 hb1
  rw [hint] at hPi
  have hUn : rhoC c τ * √(2 / (n : ℝ)) = rhoC c τ * √(2 / (n : ℝ) / n) * √(n : ℝ) := by
    rw [sqrt_n_split_MP hN0]; ring
  obtain ⟨U, hUd⟩ : ∃ U, U = rhoC c τ * √(2 / (n : ℝ) / n) := ⟨_, rfl⟩
  have hU : 0 < U := by rw [hUd]; exact mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  have hU2 : U ^ 2 = rhoC c τ ^ 2 * (2 / (n : ℝ) / n) := by rw [hUd]; exact U_sq_MP _ hN0
  have hU2n : U ^ 2 * n = 2 / (n : ℝ) * rhoC c τ ^ 2 := by
    rw [hU2]; field_simp
  rw [← hUd] at hd hcross hdev hUn ⊢
  rw [← hU2] at hmean
  rw [hUn] at hpa
  have hPh0 : ∀ A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ, 0 ≤ Ph A₁ A₂ c τ := fun A₂ => by
    unfold Ph; exact mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _)
  have hmean_abs := mean_MP (Γ := GamS A₁ c τ) ht hN hU hξ hbn he
    (by rw [hU2n]; linarith) (by rw [hU2n]; linarith) ((div_le_iff₀' Real.pi_pos).mp hrb)
    (integral_nonneg fun _ => sq_nonneg _) hmean hcross
    (integral_nonneg hPh0) (integral_nonneg fun A₂ => Pb_nonneg A₁ c τ A₂)
    (BstLean.Part133.sq_integral_le hh2) (BstLean.Part133.sq_integral_le hb2) hhv hbv
  have hΔ : |Ph A₁ A₂ c τ - Pb A₁ c τ A₂| ≤ U * PiBarMP n 12 (11 / 1000) ξc bn := by
    have h1 := abs_add_le (DelP A₁ A₂ c τ - (∫ A₂, Ph A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) - ∫ A₂, Pb A₁ c τ A₂ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))))
      (∫ A₂, Ph A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) - ∫ A₂, Pb A₁ c τ A₂ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)))
    rw [sub_add_cancel] at h1
    change |DelP A₁ A₂ c τ| ≤ _
    unfold PiBarMP
    rw [mul_add]
    linarith
  have hpl : 0 < plow n (11 / 1000) := by
    unfold plow
    exact mul_pos (Real.sqrt_pos.mpr (div_pos (by norm_num) Real.pi_pos))
      (sub_pos.mpr ((div_lt_one hN0).mpr (by linarith)))
  have hsN : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hN0
  have hPbpos : 0 < Pb A₁ c τ A₂ := lt_of_lt_of_le (mul_pos (mul_pos hU hsN) hpl) hpa
  have hnb : 0 < nrm (bO A₁ A₂ c τ) := by
    by_contra h
    have h0 : nrm (bO A₁ A₂ c τ) = 0 := le_antisymm (not_lt.mp h) (nrm_nonneg _)
    have h1 : Pb A₁ c τ A₂ = 0 := by unfold Pb; rw [h0, mul_zero]
    linarith
  have hdC0 : 0 ≤ dC A₁ A₂ c τ := by
    unfold dC; exact mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _)
  have hΔd : |Ph A₁ A₂ c τ - Pb A₁ c τ A₂| ≤ dC A₁ A₂ c τ := by
    unfold Ph Pb dC
    rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (abs_nrm_sub_le _ _) (Real.sqrt_nonneg _)
  unfold LamMP
  exact lam_core_MP hPbpos hU hpl hsN hdC0 hΔd hΔ hd hpa
    (lam_id_MP (√(2 / ((mA n : ℕ) : ℝ))) (hbar2 A₁ A₂ c τ) (bO A₁ A₂ c τ) hnb)

/-- **Lemma MP (b)**: the parallel centre error of the oracle centre `b° = b′°/ρ`. -/
theorem MP_b_final {n : ℕ} (hn : 8192 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {lam Nb MP : ℝ} (hMP : 0 ≤ MP)
    (hΛ : |(√(2 / ((mA n : ℕ) : ℝ)) • (hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ)) ⬝ᵥ
        ((nrm (bO A₁ A₂ c τ))⁻¹ • bO A₁ A₂ c τ)| ≤ rhoC c τ * √(2 / (n : ℝ) / n) * lam)
    (hN : N2 2 A₁ A₂ c τ ≤ Nb) (hXi : XiS A₁ A₂ c τ ≤ MP * (2 / (n : ℝ)) / n) :
    |(√(2 / ((mA n : ℕ) : ℝ)) • (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ)) ⬝ᵥ
        ((nrm (bO A₁ A₂ c τ))⁻¹ • bO A₁ A₂ c τ)| ≤
      √(2 / (n : ℝ) / n) * (lam + (thetaC c τ * (1 + Nb) + √(MP * thetaC c τ)) / √(n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hN0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := rhoC_posP hn1 c hτ
  have hr := rad_MP (by omega : 6 ≤ n) A₁ A₂ c hτ hMP hN hXi
  have hs0 : 0 ≤ √(2 / ((mA n : ℕ) : ℝ)) := Real.sqrt_nonneg _
  have e : (√(2 / ((mA n : ℕ) : ℝ)) • (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ)) ⬝ᵥ
        ((nrm (bO A₁ A₂ c τ))⁻¹ • bO A₁ A₂ c τ) =
      (√(2 / ((mA n : ℕ) : ℝ)) •
          (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • hbar2 A₁ A₂ c τ)) ⬝ᵥ
        ((nrm (bO A₁ A₂ c τ))⁻¹ • bO A₁ A₂ c τ) +
      (rhoC c τ)⁻¹ * ((√(2 / ((mA n : ℕ) : ℝ)) • (hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ)) ⬝ᵥ
        ((nrm (bO A₁ A₂ c τ))⁻¹ • bO A₁ A₂ c τ)) := by
    simp only [smul_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  rw [e]
  have h1 := abs_dot_le_nrm
    (√(2 / ((mA n : ℕ) : ℝ)) • (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • hbar2 A₁ A₂ c τ))
    ((nrm (bO A₁ A₂ c τ))⁻¹ • bO A₁ A₂ c τ)
  rw [nrm_smul, abs_of_nonneg hs0] at h1
  have h2 := mul_le_mul_of_nonneg_left (nrm_unit_le_MP (bO A₁ A₂ c τ))
    (mul_nonneg hs0 (nrm_nonneg (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • hbar2 A₁ A₂ c τ)))
  rw [mul_one] at h2
  have h3 : (rhoC c τ)⁻¹ * |(√(2 / ((mA n : ℕ) : ℝ)) • (hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ)) ⬝ᵥ
        ((nrm (bO A₁ A₂ c τ))⁻¹ • bO A₁ A₂ c τ)| ≤ √(2 / (n : ℝ) / n) * lam := by
    rw [inv_mul_le_iff₀ hρ]
    linarith
  have h4 := abs_add_le
    ((√(2 / ((mA n : ℕ) : ℝ)) • (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • hbar2 A₁ A₂ c τ)) ⬝ᵥ
        ((nrm (bO A₁ A₂ c τ))⁻¹ • bO A₁ A₂ c τ))
    ((rhoC c τ)⁻¹ * ((√(2 / ((mA n : ℕ) : ℝ)) • (hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ)) ⬝ᵥ
        ((nrm (bO A₁ A₂ c τ))⁻¹ • bO A₁ A₂ c τ)))
  rw [abs_mul, abs_of_pos (inv_pos.mpr hρ)] at h4
  rw [mul_add]
  linarith

end BstLean.Part154
