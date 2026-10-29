import BstLean.Part211MA
import BstLean.Part211FullEvent

/-! The actual computed-centre full error with scalar endpoint certificates. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC gO sO2 bT bO)
open BstLean.Part153 (nrm hid2Mean_cr N22bar)
open BstLean.Part154 (csC xiNr)

/-- Each field concerns an explicit scalar formula, independent of the Agent matrices. -/
structure MomentCertificate (n : ℕ) (δe k k3 θlo Θ S : ℝ) (v : ℝ → ℝ) : Prop where
  delta_nonneg : 0 ≤ δe
  delta_lt : δe < 1
  k_gt : 1 < k
  k3_gt : 1 < k3
  theta_lower : 1 / 4 ≤ θlo
  v_pos : ∀ θ ∈ Icc θlo Θ, 0 < v θ
  supremum : ∀ θ ∈ Icc θlo Θ, hsProfile n θ (v θ) * (θ * √θ) ≤ S
  ratio : BstLean.Part154.rhoBar n csC < 1 / 4
  ratio_gamma : gammaRatio n δe Θ ≤ 1
  gap : 0 < BstLean.Part194.gap 2 (BstLean.Part154.rhoBar n csC) k
  gap_gamma : 0 < BstLean.Part194.gap 1 (gammaRatio n δe Θ) k3

noncomputable def fullFormula (n J : ℕ) (δe k k3 θlo Θ S MP : ℝ) : ℝ :=
  (√(momentAllowance n csC δe k k3 Θ S) + sharpDeviation n csC δe θlo Θ +
    xiNr n Θ MP + finiteEnergy n J δe) ^ 2

theorem actual_full_transfer {n J : ℕ} (hn : 6 ≤ n) (hJ : 1 ≤ J)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) {τ δe θlo Θ ξ MP : ℝ} (hτ : 0 < τ) (hδe : 0 ≤ δe)
    (hθlo : θlo ≤ thetaC c τ) (hθhi : thetaC c τ ≤ Θ) (hξ : 0 ≤ ξ) (hMP : 0 ≤ MP)
    (hop : A ∈ BstLean.Part153.Eop n) (hsc : csC * τ ^ 2 ≤ sO2 A c τ)
    (hEe : gO A c τ ≤ (1 + δe) * (2 / n) * rhoC c τ ^ 2)
    (hMoment : (∫ M, BstLean.Part154.dC A M c τ ^ 2
      ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) ≤ rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * ξ)
    (hMA : M ∈ SharpMA n c τ A) (hN : BstLean.Part153.N2 2 A M c τ ≤ N22bar n 12)
    (hXi : BstLean.Part153.XiS A M c τ ≤ MP * (2 / (n : ℝ)) / n)
    (hChi : M ∉ BstLean.Part154.BadChi n J A c τ 12) :
    (2 / (mA n : ℝ)) * normSq (hid2Mean_cr A M c τ - (rhoC c τ)⁻¹ • bT J J A M c τ) ≤
      (2 / (n : ℝ) / n) *
        (√ξ + sharpDeviation n csC δe θlo Θ + xiNr n Θ MP + finiteEnergy n J δe) ^ 2 := by
  have hn0 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn0 c hτ
  have hd := MA_on_sharp_source hn0 A c hτ csC_positive.le hθlo hθhi hξ hsc hEe hMoment hMA
  have hO := BstLean.Part154.MA_iv hn A M c hτ hMP hd hN hXi
  have hRad : xiNr n (thetaC c τ) MP ≤ xiNr n Θ MP := by
    have hb := BstLean.Part153.N12bar_nonneg n (12 : ℝ)
    have hnb : 0 ≤ N22bar n 12 := by unfold N22bar; positivity
    unfold xiNr
    gcongr
  have hO' := hO.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl hRad) (sqrt_nonneg _))
  have hF := BstLean.Part154.FC_iii hn0 hJ A M c hτ csC_positive hδe
    (by norm_num) hop hsc hEe hChi
  have hFn : √(2 / (mA n : ℝ)) *
      nrm ((rhoC c τ)⁻¹ • bT J J A M c τ - (rhoC c τ)⁻¹ • bO A M c τ) ≤
      √(2 / (n : ℝ) / n) * finiteEnergy n J δe := by
    rw [← smul_sub, BstLean.Part153.nrm_smul, abs_of_pos (inv_pos.mpr hρ)]
    convert hF using 1 <;> (try simp only [finiteEnergy]) <;> ring
  have ht := BstLean.Part206.full_centre_transfer (hid2Mean_cr A M c τ)
    (hid2Mean_cr A M c τ) ((rhoC c τ)⁻¹ • bO A M c τ)
    ((rhoC c τ)⁻¹ • bT J J A M c τ) (sqrt_nonneg _) hO'
    (radius := 0) (by simp [BstLean.Part153.nrm, normSq]) hFn
  simp only [BstLean.Part206.fullAllowance, add_zero] at ht
  have hsq := pow_le_pow_left₀ (mul_nonneg (sqrt_nonneg _) (BstLean.Part153.nrm_nonneg _)) ht 2
  simpa only [mul_pow, sq_sqrt (by positivity : 0 ≤ 2 / (mA n : ℝ)),
    sq_sqrt (by positivity : 0 ≤ 2 / (n : ℝ) / n), BstLean.Part153.nrm_sq] using hsq

/-- All matrix-dependent premises come from the fixed full-error source event. -/
theorem full_error_on_source {n J : ℕ} (hn : 4096 ≤ n) (hn1 : n ≤ 16384) (hJ : 1 ≤ J)
    (c : Fin n → ℝ) (hc : 0 < normSq c) {τ δe k k3 θlo Θ S MP : ℝ}
    (hτ : 0 < τ) (hMP : 0 ≤ MP) (v : ℝ → ℝ)
    (C : MomentCertificate n δe k k3 θlo Θ S v)
    (hθlo : θlo ≤ thetaC c τ) (hθhi : thetaC c τ ≤ Θ)
    (hGroot : 2 * √12 / (n : ℝ) ≤ √(1 - 2 / (n : ℝ) ^ 2))
    (hGlo : 1 - δe ≤ gMinus n) (hGhi : gPlus n ≤ 1 + δe)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ} {M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hSource : (A, M) ∈ FullSource n J c τ MP) :
    (2 / (mA n : ℝ)) * normSq (hid2Mean_cr A M c τ - (rhoC c τ)⁻¹ • bT J J A M c τ) ≤
      (2 / (n : ℝ) / n) * fullFormula n J δe k k3 θlo Θ S MP := by
  have hn0 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn0 c hτ
  have hA : A ∈ BstLean.Part153.Eop n ∧ csC * τ ^ 2 ≤ sO2 A c τ ∧
      A ∉ BstLean.Part153.BadE n c τ := by
    have h := hSource.1.1
    simp only [FirstEnergyBad, mem_union, mem_compl_iff, mem_setOf_eq, not_or, not_not,
      not_lt] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩
  have hM : M ∉ BstLean.Part154.BadChi n J A c τ 12 := by
    have h := hSource.1.2
    simp only [SecondEnergyBad, mem_union, not_or] at h
    exact h.2
  obtain ⟨hLo, hHi⟩ := energy_on_source (by omega : 2 ≤ n) c τ hA.2.2 hGroot
  have hscale : 0 ≤ (2 / n * rhoC c τ ^ 2) := by positivity
  have hLow : (1 - δe) * (2 / n) * rhoC c τ ^ 2 ≤ gO A c τ := by
    have := mul_le_mul_of_nonneg_left hGlo hscale
    nlinarith only [hLo, this]
  have hHigh : gO A c τ ≤ (1 + δe) * (2 / n) * rhoC c τ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hGhi hscale
    nlinarith only [hHi, this]
  have hMoment := MA_moment_on_source hn hn1 c hc hτ csC_positive C.delta_lt C.k_gt C.k3_gt
    C.theta_lower hθlo hθhi v C.v_pos C.supremum C.ratio C.ratio_gamma C.gap C.gap_gamma
    hA.1 hA.2.1 hLow hSource.2.1
  have hξ : 0 ≤ momentAllowance n csC δe k k3 Θ S := by
    have hi : 0 ≤ ∫ M, BstLean.Part154.dC A M c τ ^ 2
        ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ)) := integral_nonneg fun _ => sq_nonneg _
    have hp : 0 < rhoC c τ ^ 2 * (2 / (n : ℝ) / n) := by positivity
    nlinarith only [hi, hMoment, hp]
  exact actual_full_transfer (by omega) hJ A M c hτ C.delta_nonneg hθlo hθhi hξ hMP
    hA.1 hA.2.1 hHigh hMoment hSource.2.2.2.1
    (BstLean.Part153.N22_le_bar hn0 hSource.2.2.1 hSource.2.2.2.2.1)
    hSource.2.2.2.2.2 hM

#print axioms actual_full_transfer
#print axioms full_error_on_source
end BstLean.Part211
