import BstLean.Part211Terms

/-! The MP mean correction with no fixed dimension floor. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC gO sO2)
open BstLean.Part153 (nrm GamS Pb)
open BstLean.Part154
open BstLean.Part150 (bO)
open BstLean.Part153 (nrm_smul nrm_nonneg nrm_sq nrm_add_le abs_nrm_sub_le abs_dot_le_nrm
  mA_cast GamS_nonneg GamS_eq_gO rb_bounds Pb_nonneg N2 XiS hid2Mean_cr)

lemma le_of_square_bound {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith

lemma root_difference {rh rb q : ℝ} (hrb : 0 < rb) (hrh : 0 ≤ rh) (hq0 : 0 ≤ q)
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

theorem MP_mean_core {U sb ξ μ rb rh D2 T Eh Eb N sN : ℝ} (hU : 0 < U) (hsb : 0 ≤ sb)
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
  have hD1 := root_difference hrb hrh hq0 (by linarith) hc'
  have hX : q * rb / 2 = U * (sb + lam * ξ / 2) := by rw [hq, hUl]; ring
  have hA : |rh - rb| ≤ U * ((sb + ξ * μ / 2) * (1 + (2 * μ * sb + μ ^ 2 * ξ))) := by
    refine hD1.trans ?_
    rw [hX, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hU.le
    have h7 := mul_le_mul_of_nonneg_right hlμ hξ
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  have hrh94 : 0.94 * rb ≤ rh := by
    apply le_of_square_bound hrh
    have h8 := (abs_le.mp hc').1
    nlinarith [mul_nonneg (sub_nonneg.mpr hq10) (sq_nonneg rb)]
  have hrh0 : 0 < rh := by linarith [mul_pos (by norm_num : (0 : ℝ) < 0.94) hrb]
  have hEbr : Eb ≤ rb := le_of_square_bound hrb.le hJb
  have hEhr : Eh ≤ rh := le_of_square_bound hrh hJh
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


theorem MP_mean_formula {n : ℕ} {t U ξ bn Γ rh2 rb2 D2 Eh Eb δe : ℝ} (ht : t = 2 / (n : ℝ) ^ 2)
    (hN : (1 : ℝ) ≤ n) (hδ0 : 0 ≤ δe) (hδ1 : δe ≤ 11 / 1000) (hU : 0 < U) (hξ : 0 ≤ ξ) (hbn : 0 ≤ bn)
    (he : eMP n δe ξ bn ≤ 1 / 10)
    (hΓl : (1 - δe) * (U ^ 2 * n) ≤ Γ) (hΓu : Γ ≤ (1 + δe) * (U ^ 2 * n))
    (hΓπ : Γ ≤ π * rb2) (hrh2 : 0 ≤ rh2) (hD : D2 ≤ U ^ 2 * ξ)
    (hcross : |rh2 - rb2| ≤ 2 * (U * √bn) * √rb2 + D2)
    (hEh : 0 ≤ Eh) (hEb : 0 ≤ Eb) (hJh : Eh ^ 2 ≤ rh2) (hJb : Eb ^ 2 ≤ rb2)
    (hvh : rh2 - Eh ^ 2 ≤ t * Γ) (hvb : rb2 - Eb ^ 2 ≤ t * Γ) :
    |Eh - Eb| ≤ U * ((√bn + ξ * √π / (2 * √((n : ℝ) * (1 - δe)))) *
      (1 + eMP n δe ξ bn) + 8 / ((n : ℝ) * √(n : ℝ))) := by
  subst ht
  have hN0 : (0 : ℝ) < n := by linarith
  have hπ := Real.pi_pos
  have hK0 : 0 < (n : ℝ) * (1 - δe) := mul_pos hN0 (by linarith)
  have hrb2 : 0 < rb2 := by
    have h1 : 0 < (1 - δe) * (U ^ 2 * n) :=
      mul_pos (by linarith) (mul_pos (pow_pos hU 2) hN0)
    by_contra h
    push Not at h
    nlinarith
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = √π / √((n : ℝ) * (1 - δe)) := ⟨_, rfl⟩
  have hμ0 : 0 < μ := by
    rw [hμd]; exact div_pos (Real.sqrt_pos.mpr hπ) (Real.sqrt_pos.mpr hK0)
  have hμ2 : μ ^ 2 = π / ((n : ℝ) * (1 - δe)) := by
    rw [hμd, div_pow, Real.sq_sqrt hπ.le, Real.sq_sqrt hK0.le]
  have heq : eMP n δe ξ bn = 2 * μ * √bn + μ ^ 2 * ξ := by
    unfold eMP
    rw [hμ2, Real.sqrt_div (mul_nonneg hπ.le hbn), Real.sqrt_mul hπ.le, hμd]
    ring
  have hμs : μ * √(n : ℝ) ≤ 1.9 := by
    apply le_of_square_bound (by norm_num)
    rw [mul_pow, hμ2, Real.sq_sqrt hN0.le, div_mul_eq_mul_div, div_le_iff₀ hK0]
    nlinarith [mul_pos (sub_pos.mpr Real.pi_lt_d2) hN0,
      mul_nonneg (show 0 ≤ 11 / 1000 - δe by linarith) hN0.le]
  have hrb : 0 < √rb2 := Real.sqrt_pos.mpr hrb2
  have hrbsq : √rb2 ^ 2 = rb2 := Real.sq_sqrt hrb2.le
  have hrhsq : √rh2 ^ 2 = rh2 := Real.sq_sqrt hrh2
  have hUμ : U ≤ μ * √rb2 := by
    apply le_of_square_bound (mul_nonneg hμ0.le hrb.le)
    rw [mul_pow, hμ2, hrbsq, div_mul_eq_mul_div, le_div_iff₀ hK0]
    linarith
  have hT : 2 / (n : ℝ) ^ 2 * Γ ≤ 2.022 * U ^ 2 / n := by
    calc 2 / (n : ℝ) ^ 2 * Γ ≤ 2 / (n : ℝ) ^ 2 * ((1 + δe) * (U ^ 2 * n)) := by gcongr
      _ = 2 * (1 + δe) * U ^ 2 / n := by field_simp
      _ ≤ _ := by gcongr; linarith
  have hcore := MP_mean_core (U := U) (sb := √bn) (ξ := ξ) (μ := μ) (rb := √rb2) (rh := √rh2)
    (D2 := D2) (T := 2 / (n : ℝ) ^ 2 * Γ) (Eh := Eh) (Eb := Eb) (N := n) (sN := √(n : ℝ))
    hU (Real.sqrt_nonneg _) hξ hμ0 hrb (Real.sqrt_nonneg _) hN0 (Real.sqrt_pos.mpr hN0)
    hUμ (by rw [← heq]; exact he) (by rw [hrhsq, hrbsq]; exact hcross) hD hEh hEb
    (by rw [hrhsq]; exact hJh) (by rw [hrbsq]; exact hJb)
    (by rw [hrhsq]; exact hvh) (by rw [hrbsq]; exact hvb) hT hμs
  rw [heq]
  have e : ξ * √π / (2 * √((n : ℝ) * (1 - δe))) = ξ * μ / 2 := by rw [hμd]; ring
  rw [e]
  exact hcore



theorem MP_norm_gap_on_source {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) {τ δe ξ bn : ℝ} (hτ : 0 < τ)
    (hδ0 : 0 ≤ δe) (hδ1 : δe ≤ 11 / 1000) (hξ : 0 ≤ ξ) (hbn : 0 ≤ bn)
    (he : eMP n δe ξ bn ≤ 1 / 10)
    (hGlo : (1 - δe) * (2 / n) * rhoC c τ ^ 2 ≤ gO A c τ)
    (hGhi : gO A c τ ≤ (1 + δe) * (2 / n) * rhoC c τ ^ 2)
    (hMoment : (∫ M, dC A M c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) ≤
      rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * ξ)
    (hCross : |(∫ M, Ph A M c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) -
      (∫ M, Pb A c τ M ^ 2 ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ)))| ≤
      2 * (rhoC c τ * √(2 / (n : ℝ) / n) * √bn) *
        √(∫ M, Pb A c τ M ^ 2 ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) +
      (∫ M, dC A M c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))))
    (hPi : M ∉ BadPi A c τ 12) :
    |Ph A M c τ - Pb A c τ M| ≤
      rhoC c τ * √(2 / (n : ℝ) / n) * PiBarMP n 12 δe ξ bn := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn c hτ
  have hm := one_le_mA hn
  have hmR : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  let U := rhoC c τ * √(2 / (n : ℝ) / n)
  have hU : 0 < U := by dsimp [U]; positivity
  have hU2 : U ^ 2 = rhoC c τ ^ 2 * (2 / (n : ℝ) / n) := by
    dsimp [U]
    rw [mul_pow, sq_sqrt (by positivity)]
  have hU2n : U ^ 2 * n = 2 / (n : ℝ) * rhoC c τ ^ 2 := by rw [hU2]; field_simp
  obtain ⟨hh1, hh2, hhv⟩ := Ph_var hm A c τ
  obtain ⟨hb1, hb2, hbv⟩ := Pb_var hm A c τ
  have hrb := (BstLean.Part153.rb_bounds hm A c τ).2.1
  have hΓ0 := BstLean.Part153.GamS_nonneg A c τ
  rw [← BstLean.Part153.GamS_eq_gO hm] at hGlo hGhi hrb
  have hMean := MP_mean_formula (by rw [hmR]) (by exact_mod_cast hn) hδ0 hδ1 hU hξ hbn he
    (by rw [hU2n]; nlinarith only [hGlo]) (by rw [hU2n]; nlinarith only [hGhi])
    ((div_le_iff₀' pi_pos).mp hrb) (integral_nonneg fun _ => sq_nonneg _)
    (by simpa only [hU2] using hMoment) hCross
    (integral_nonneg fun M => mul_nonneg (sqrt_nonneg _) (BstLean.Part153.nrm_nonneg _))
    (integral_nonneg fun M => BstLean.Part153.Pb_nonneg A c τ M)
    (BstLean.Part133.sq_integral_le hh2) (BstLean.Part133.sq_integral_le hb2) hhv hbv
  have hDev : √(2 * 12 * (2 / (mA n : ℝ))) * (2 * √(GamS A c τ)) ≤
      U * √(16 * 12 * (1 + δe) / n) := by
    apply le_of_square_bound (by positivity)
    rw [mul_pow, mul_pow, sq_sqrt (by positivity), sq_sqrt hΓ0, mul_pow,
      sq_sqrt (by positivity), hU2, hmR]
    have h := mul_le_mul_of_nonneg_left hGhi
      (show 0 ≤ 96 * (2 / (n : ℝ) ^ 2) by positivity)
    convert h using 1 <;> field_simp <;> ring
  simp only [BadPi, mem_setOf_eq, not_lt] at hPi
  have hInt : (∫ M, DelP A M c τ ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) =
      (∫ M, Ph A M c τ ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) -
      (∫ M, Pb A c τ M ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) :=
    integral_sub hh1 hb1
  rw [hInt] at hPi
  have htri := abs_add_le
    (DelP A M c τ - ((∫ M, Ph A M c τ ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) -
      (∫ M, Pb A c τ M ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ)))))
    ((∫ M, Ph A M c τ ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) -
      (∫ M, Pb A c τ M ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))))
  rw [sub_add_cancel] at htri
  change |(∫ M, Ph A M c τ ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) -
    (∫ M, Pb A c τ M ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ)))| ≤ _ at hMean
  change |DelP A M c τ| ≤ U * PiBarMP n 12 δe ξ bn
  unfold PiBarMP
  nlinarith only [htri, hPi, hMean, hDev]

theorem scaled_parallel_from_gap {m : ℕ} (h bo : Fin m → ℝ)
    {s X rn p cd gap : ℝ} (hs : 0 < s) (hX : 0 < X) (hrn : 0 < rn) (hp : 0 < p)
    (hD : s * nrm (h - bo) ≤ X * cd)
    (hGap : |s * nrm h - s * nrm bo| ≤ X * gap)
    (hLower : X * rn * p ≤ s * nrm bo) :
    |(s • (h - bo)) ⬝ᵥ ((nrm bo)⁻¹ • bo)| ≤
      X * ((1 + cd / (2 * p * rn)) * gap + cd ^ 2 / (2 * p * rn)) := by
  have hd : nrm (h - bo) ≤ X * cd / s := by rw [le_div_iff₀ hs]; nlinarith only [hD]
  have hg : |nrm h - nrm bo| ≤ X * gap / s := by
    rw [← mul_sub, abs_mul, abs_of_pos hs] at hGap
    rw [le_div_iff₀ hs]
    nlinarith only [hGap]
  have hb : X * rn * p / s ≤ nrm bo := by rw [div_le_iff₀ hs]; nlinarith only [hLower]
  have h := BstLean.Part206.parallel_from_norm_gap h bo (by positivity) hb hd hg
  have hh := mul_le_mul_of_nonneg_left h hs.le
  rw [smul_dotProduct, smul_eq_mul, abs_mul, abs_of_pos hs]
  convert hh using 1 <;> field_simp <;> ring

lemma MP_lower_core {N t Γ rb2 E P : ℝ} (ht : t = 2 / N ^ 2) (hN : 14 ≤ N) (hΓ0 : 0 ≤ Γ)
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
    apply le_of_square_bound hE
    have h3 : 2 / N ^ 2 * Γ ≤ x * r ^ 2 := by
      rw [hx, hr2]
      calc 2 / N ^ 2 * Γ ≤ 2 / N ^ 2 * (π * rb2) := by gcongr
        _ = _ := by ring
    nlinarith [mul_nonneg (mul_nonneg hx0 (sub_nonneg.mpr hx1)) (sq_nonneg r)]
  have h2 : √(2 * 12 * (2 / N ^ 2)) * √Γ ≤ 12.3 / N * r := by
    apply le_of_square_bound (mul_nonneg (by positivity) hr0)
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


theorem MP_oracle_lower {n : ℕ} (hn : 14 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hΓ : |GamS A₁ c τ - 2 / (n : ℝ) * rhoC c τ ^ 2| ≤ 11 / 1000 * (2 / (n : ℝ) * rhoC c τ ^ 2))
    (hPb : A₂ ∉ BadPb A₁ c τ 12) :
    rhoC c τ * √(2 / (n : ℝ)) * plow n (11 / 1000) ≤ Pb A₁ c τ A₂ := by
  have hn1 : 1 ≤ n := by omega
  have hN : (14 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hm := one_le_mA hn1
  have hmc := mA_cast n
  have ht : 2 / ((mA n : ℕ) : ℝ) = 2 / (n : ℝ) ^ 2 := by rw [hmc]
  have hρ := BstLean.Part150.rhoC_posP hn1 c hτ
  have hπ := Real.pi_pos
  obtain ⟨hb1, hb2, hbv⟩ := Pb_var hm A₁ c τ
  have hrb := (rb_bounds hm A₁ c τ).2.1
  rw [← GamS_eq_gO hm] at hrb
  simp only [BadPb, Set.mem_ofPred_eq, not_lt] at hPb
  have hΓ0 := GamS_nonneg A₁ c τ
  have hcore := MP_lower_core ht hN hΓ0 ((div_le_iff₀' hπ).mp hrb)
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

lemma sqrt_double_inverse {N : ℝ} (hN : 0 < N) : √(2 / N / N) = √2 / N := by
  rw [div_div, ← sq, sqrt_div (by norm_num), sqrt_sq hN.le]

lemma sqrt_double_div (N : ℝ) : √(2 / N) = √2 / √N := sqrt_div (by norm_num) N

lemma unit_norm_le_one {ι : Type*} [Fintype ι] (b : ι → ℝ) : nrm ((nrm b)⁻¹ • b) ≤ 1 := by
  rw [nrm_smul, abs_of_nonneg (inv_nonneg.mpr (nrm_nonneg _))]
  by_cases h : nrm b = 0
  · rw [h]; simp
  · rw [inv_mul_cancel₀ h]

/-- Lemma MA (iii) in the unit `√(γ_A/n)`, with the bounds of `N₂₂` and `Ξ`. -/
theorem radius_transfer {n : ℕ} (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {Nb MP : ℝ} (hMP : 0 ≤ MP)
    (hN : N2 2 A₁ A₂ c τ ≤ Nb) (hXi : XiS A₁ A₂ c τ ≤ MP * (2 / (n : ℝ)) / n) :
    √(2 / ((mA n : ℕ) : ℝ)) *
        nrm (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • hbar2 A₁ A₂ c τ) ≤
      √(2 / (n : ℝ) / n) * ((thetaC c τ * (1 + Nb) + √(MP * thetaC c τ)) / √(n : ℝ)) := by
  have hN0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hθ := (BstLean.Part150.thetaC_bounds (by omega) c hτ).1
  have h := radius_le hn A₁ A₂ c hτ
  have hθn : 0 ≤ thetaC c τ / n := div_nonneg hθ.le hN0.le
  have e1 : √(2 / (n : ℝ)) * (1 + Nb) * (thetaC c τ / n) =
      √(2 / (n : ℝ) / n) * (thetaC c τ * (1 + Nb) / √(n : ℝ)) := by
    rw [sqrt_double_inverse hN0, sqrt_double_div]
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

theorem oracle_parallel_radius {n : ℕ} (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
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
  have hρ := BstLean.Part150.rhoC_posP hn1 c hτ
  have hr := radius_transfer (by omega : 6 ≤ n) A₁ A₂ c hτ hMP hN hXi
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
  have h2 := mul_le_mul_of_nonneg_left (unit_norm_le_one (bO A₁ A₂ c τ))
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

#print axioms MP_oracle_lower
#print axioms radius_transfer
#print axioms oracle_parallel_radius
#print axioms scaled_parallel_from_gap
#print axioms MP_norm_gap_on_source
#print axioms MP_mean_formula
end BstLean.Part211
