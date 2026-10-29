import BstLean.Part211Terms
import BstLean.Part211Deviation

/-! The complete sharp MA moment formula on its original first-layer source events. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC sO2 gO hO)
open BstLean.Part153 (wn Eop)
open BstLean.Part154
open BstLean.Part194 (gap tail)

noncomputable def gammaRatio (n : ℕ) (δe Θ : ℝ) : ℝ :=
  2 * wn n * Θ / ((1 - δe) * n)

noncomputable def restAllowance (cs δe k k3 S : ℝ) : ℝ :=
  4 * K0 * √(k * k3) * S / √(2 * cs * (1 - δe))

noncomputable def linearAllowance (n : ℕ) (cs Θ : ℝ) : ℝ :=
  4 * wn n * ((2 * Θ * rhoBar n cs +
    (6863 / 10000) * rhoBar n cs * n * nuR (rhoBar n cs)) / π + Θ * piBar (rhoBar n cs))

noncomputable def badAllowance (n : ℕ) (cs δe k k3 Θ : ℝ) : ℝ :=
  wn n * n * (tail 2 (rhoBar n cs) k / √k + tail 1 (gammaRatio n δe Θ) k3 / √k3)

noncomputable def momentAllowance (n : ℕ) (cs δe k k3 Θ S : ℝ) : ℝ :=
  restAllowance cs δe k k3 S + linearAllowance n cs Θ + bN n cs Θ +
    badAllowance n cs δe k k3 Θ

lemma linearAllowance_mono {n : ℕ} {cs θ Θ : ℝ} (hcs : 0 < cs) (hθ : θ ≤ Θ) :
    linearAllowance n cs θ ≤ linearAllowance n cs Θ := by
  have hw : 0 ≤ wn n := by unfold wn; positivity
  have hr : 0 ≤ rhoBar n cs := by unfold rhoBar; positivity
  have hp := piBar_nonneg (rhoBar n cs)
  unfold linearAllowance
  gcongr

lemma bN_mono_endpoint {n : ℕ} {cs θ Θ : ℝ} (hcs : 0 < cs) (hθ : θ ≤ Θ) :
    bN n cs θ ≤ bN n cs Θ := by
  have hw : 0 ≤ wn n := by unfold wn; positivity
  have hr : 0 ≤ rhoBar n cs := by unfold rhoBar; positivity
  have hq : 0 ≤ QB (rhoBar n cs) (piBar (rhoBar n cs)) := by
    have p0 := (BstLean.Part153.phiG_pos 0).le
    have p1 := (BstLean.Part153.phiG_pos 1).le
    have hν : 0 ≤ nuR (rhoBar n cs) := by unfold nuR; positivity
    have h0 : 0 ≤ cc0 (rhoBar n cs) (piBar (rhoBar n cs)) := by unfold cc0; positivity
    have h1 : 0 ≤ cc1 (rhoBar n cs) (piBar (rhoBar n cs)) := by unfold cc1; positivity
    have h2 : 0 ≤ cc2 (rhoBar n cs) := by unfold cc2; positivity
    unfold QB
    positivity
  unfold bN
  gcongr

/-- The scalar supremum certificate covers every latitude in the retained interval. -/
theorem MA_moment_on_source {n : ℕ} (hn : 4096 ≤ n) (hn1 : n ≤ 16384)
    (c : Fin n → ℝ) (hc : 0 < normSq c) {τ cs δe k k3 θlo Θ S : ℝ}
    (hτ : 0 < τ) (hcs : 0 < cs) (hδ : δe < 1) (hk : 1 < k) (hk3 : 1 < k3)
    (hlo : 1 / 4 ≤ θlo) (hθlo : θlo ≤ thetaC c τ) (hθhi : thetaC c τ ≤ Θ)
    (v : ℝ → ℝ) (hv : ∀ θ ∈ Icc θlo Θ, 0 < v θ)
    (hSup : ∀ θ ∈ Icc θlo Θ, hsProfile n θ (v θ) * (θ * √θ) ≤ S)
    (hr : rhoBar n cs < 1 / 4) (hrG : gammaRatio n δe Θ ≤ 1)
    (hgap : 0 < gap 2 (rhoBar n cs) k) (hgapG : 0 < gap 1 (gammaRatio n δe Θ) k3)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ} (hop : A ∈ Eop n)
    (hsc : cs * τ ^ 2 ≤ sO2 A c τ)
    (hGlo : (1 - δe) * (2 / n) * rhoC c τ ^ 2 ≤ gO A c τ)
    (hH : A ∉ BadH n c τ 12) :
    (∫ M, dC A M c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) ≤
      rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * momentAllowance n cs δe k k3 Θ S := by
  have hn0 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm := one_le_mA hn0
  have hρ := BstLean.Part150.rhoC_posP hn0 c hτ
  have hw : 0 < wn n := by unfold wn; positivity
  have hθ := (BstLean.Part150.thetaC_bounds hn0 c hτ).1
  have hΘ : 0 < Θ := hθ.trans_le hθhi
  have hU := BstLean.Part160.Uθ_I hn0 c hτ
  have hHS := HS_profile_on_source hn hn1 c hc hτ (hv _ ⟨hθlo, hθhi⟩)
    (hlo.trans hθlo) hH
  have hop2 := BstLean.Part153.Eop_sq hn0 hop
  obtain ⟨L, r, hL, hre, hr0, hrr, H, hB⟩ :=
    BstLean.Part160.setupMA_I hn0 A c hτ hcs hr hop2 hsc
  have hs : 0 < sO2 A c τ := (mul_pos hcs (sq_pos_of_pos hτ)).trans_le hsc
  have hG : 0 < gO A c τ := (by positivity : 0 < (1 - δe) * (2 / n) * rhoC c τ ^ 2).trans_le hGlo
  have hrb := BstLean.Part160.rhoBar_posI hn0 hcs
  have hrg : 0 < gammaRatio n δe Θ := by unfold gammaRatio; positivity
  have hLip : √(2 / (mA n : ℝ)) * (|τ| * BstLean.Part152.opN A) ≤ L := by
    apply BstLean.Part160.le_of_sq_le_A H.hℓ.le
    rw [mul_pow, mul_pow, sq_sqrt (by positivity), sq_abs, hL]
    have := mul_le_mul_of_nonneg_left hop2 (sq_nonneg τ)
    convert this using 1 <;> ring
  have ht : τ ^ 2 ≤ rhoC c τ ^ 2 * Θ / n := by
    have he : τ ^ 2 = rhoC c τ ^ 2 * thetaC c τ / n := by unfold thetaC; field_simp
    rw [he]
    gcongr
  have hRatioG : L ^ 2 / GamF (stdGauss (Fin n)) (fA A c τ) ≤ gammaRatio n δe Θ := by
    rw [GamF_fA hm, div_le_iff₀ hG, hL]
    have h1 := mul_le_mul_of_nonneg_left hGlo hrg.le
    have h2 := mul_le_mul_of_nonneg_left ht (show 0 ≤ 4 * wn n / n by positivity)
    have he : gammaRatio n δe Θ * ((1 - δe) * (2 / n) * rhoC c τ ^ 2) =
        (4 * wn n / n) * (rhoC c τ ^ 2 * Θ / n) := by
      unfold gammaRatio
      have : 1 - δe ≠ 0 := by linarith
      field_simp
      ring
    rw [he] at h1
    convert h2.trans h1 using 1 <;> ring
  have hMF := BstLean.Part206.MA_second_from_MF hm A c τ H
    (BstLean.Part194.fA_vector_lipschitz A c hLip) hrb hrg hk hk3
    (by rw [sF2_fA hm, ← hre]; exact hrr) hRatioG (by linarith) (by linarith) hgap hgapG
  dsimp only at hMF
  have hsFe : sF (stdGauss (Fin n)) (fA A c τ) = √(sO2 A c τ) := by
    unfold sF
    rw [sF2_fA hm]
  rw [hsFe, sF2_fA hm, GamF_fA hm, ← hre] at hMF
  have hhs : hsF (stdGauss (Fin n)) (fA A c τ) = hsH A c τ := rfl
  rw [hhs] at hMF
  have hhs0 : 0 ≤ hsH A c τ := by unfold hsH hsF; positivity
  have e1 := MA_rest_term (sq_pos_of_pos hρ) hnR hτ hcs hδ (by linarith : 0 < k)
    (by linarith : 0 < k3) hU hsc hGlo hhs0 hHS (hSup _ ⟨hθlo, hθhi⟩)
  have hGu : gO A c τ ≤ 4 * wn n / n * rhoC c τ ^ 2 := by
    rw [← BstLean.Part153.GamS_eq_gO hm, BstLean.Part150.rhoC_sqP]
    exact BstLean.Part153.GamS_le_Eop hn0 hop c τ
  have hb0 : 0 ≤ GamBarF (stdGauss (Fin n)) (fA A c τ) := normSq_nonneg _
  have hbg : GamBarF (stdGauss (Fin n)) (fA A c τ) ≤ gO A c τ := by
    rw [GamBarF_fA]
    exact BstLean.Part153.GamBar_le A c τ
  have hsg : sO2 A c τ ≤ gO A c τ := by
    unfold sO2
    have : 0 ≤ 2 / (mA n : ℝ) * ∑ i, hO A c τ i ^ 2 := by positivity
    linarith
  have e2 := MA_tail_term (sq_nonneg (rhoC c τ)) hnR hw.le hs.le hsg hGu
    (by linarith : 0 < k) (by linarith : 0 < k3)
    (show 0 ≤ tail 2 (rhoBar n cs) k by unfold tail; positivity)
    (show 0 ≤ tail 1 (gammaRatio n δe Θ) k3 by unfold tail; positivity)
  have e3 := MA_linear_term (sq_pos_of_pos hρ) hnR hτ hcs hw.le hU hL hr0.le hrr rfl
    hb0 (hbg.trans hGu) hsc (pb := piBar (rhoBar n cs))
  have e3' := mul_le_mul_of_nonneg_left (linearAllowance_mono (n := n) hcs hθhi)
    (show 0 ≤ rhoC c τ ^ 2 * (2 / (n : ℝ) / n) by positivity)
  have e4 := mul_le_mul_of_nonneg_left (bN_mono_endpoint (n := n) hcs hθhi)
    (show 0 ≤ rhoC c τ ^ 2 * (2 / (n : ℝ) / n) by positivity)
  unfold momentAllowance
  dsimp only [restAllowance, linearAllowance, badAllowance] at e3' ⊢
  ring_nf at hMF e1 e2 e3 hB e3' e4 ⊢
  linarith only [hMF, e1, e2, e3, hB, e3', e4]

#print axioms MA_moment_on_source
end BstLean.Part211
