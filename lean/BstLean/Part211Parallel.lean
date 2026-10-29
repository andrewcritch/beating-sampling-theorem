import BstLean.Part211Full
import BstLean.Part211MP

/-! The parallel computed-centre transfer on the original norm-difference event. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC gO sO2 bT bO)
open BstLean.Part153 (nrm Pb GamS hid2Mean_cr N22bar)
open BstLean.Part154

lemma unit_positive_smul {m : ℕ} (b : Fin m → ℝ) {r : ℝ} (hr : 0 < r) :
    (nrm (r • b))⁻¹ • (r • b) = (nrm b)⁻¹ • b := by
  rw [BstLean.Part153.nrm_smul, abs_of_pos hr, smul_smul, _root_.mul_inv_rev]
  congr 1
  rw [mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]

noncomputable def parallelOracle (n : ℕ) (δe ξ bn cd : ℝ) : ℝ :=
  (1 + cd / (2 * plow n (11 / 1000) * √(n : ℝ))) * PiBarMP n 12 δe ξ bn +
    cd ^ 2 / (2 * plow n (11 / 1000) * √(n : ℝ))

noncomputable def parallelFormula (n J : ℕ) (δe ξ bn cd Θ MP : ℝ) : ℝ :=
  BstLean.Part206.parallelAllowance (parallelOracle n δe ξ bn cd + xiNr n Θ MP)
    (cd + xiNr n Θ MP) (finiteEnergy n J δe) (plow n (11 / 1000)) (√(n : ℝ)) ^ 2

/-- All analytic error supplies refer to the same Gaussian stand-in input distribution. -/
theorem actual_parallel_transfer {n J : ℕ} (hn : 14 ≤ n) (hJ : 1 ≤ J)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) {τ δe θlo Θ ξ MP : ℝ} (hτ : 0 < τ)
    (hδ0 : 0 ≤ δe) (hδ1 : δe ≤ 11 / 1000) (hξ : 0 ≤ ξ) (hMP : 0 ≤ MP)
    (hθlo : θlo ≤ thetaC c τ) (hθhi : thetaC c τ ≤ Θ)
    (hr : rhoBar n csC < 1 / 4)
    (he : eMP n δe ξ (bN n csC Θ) ≤ 1 / 10)
    (hGuard : finiteEnergy n J δe / √(n : ℝ) < plow n (11 / 1000))
    (hop : A ∈ BstLean.Part153.Eop n) (hsc : csC * τ ^ 2 ≤ sO2 A c τ)
    (hGlo : (1 - δe) * (2 / n) * rhoC c τ ^ 2 ≤ gO A c τ)
    (hGhi : gO A c τ ≤ (1 + δe) * (2 / n) * rhoC c τ ^ 2)
    (hMoment : (∫ M, dC A M c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) ≤
      rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * ξ)
    (hMA : M ∈ SharpMA n c τ A) (hPi : M ∉ BadPi A c τ 12) (hPb : M ∉ BadPb A c τ 12)
    (hN : BstLean.Part153.N2 2 A M c τ ≤ N22bar n 12)
    (hXi : BstLean.Part153.XiS A M c τ ≤ MP * (2 / (n : ℝ)) / n)
    (hChi : M ∉ BadChi n J A c τ 12) :
    |(√(2 / (mA n : ℝ)) • (hid2Mean_cr A M c τ - (rhoC c τ)⁻¹ • bT J J A M c τ)) ⬝ᵥ
      ((nrm ((rhoC c τ)⁻¹ • bT J J A M c τ))⁻¹ • ((rhoC c τ)⁻¹ • bT J J A M c τ))| ^ 2 ≤
      (2 / (n : ℝ) / n) * parallelFormula n J δe ξ (bN n csC Θ)
        (√ξ + sharpDeviation n csC δe θlo Θ) Θ MP ∧
    √(2 / (n : ℝ)) * (plow n (11 / 1000) - finiteEnergy n J δe / √(n : ℝ)) ≤
      √(2 / (mA n : ℝ)) * nrm ((rhoC c τ)⁻¹ • bT J J A M c τ) ∧
    (rhoC c τ)⁻¹ • bT J J A M c τ ≠ 0 := by
  have hn0 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn0 c hτ
  have hm := one_le_mA hn0
  have hθ := (BstLean.Part150.thetaC_bounds hn0 c hτ).1
  have hΘ : 0 < Θ := hθ.trans_le hθhi
  have hbn : 0 ≤ bN n csC Θ := by
    have h := bN_mono_endpoint (n := n) csC_positive hΘ.le
    simpa only [bN, mul_zero, zero_mul, zero_div] using h
  let X := √(2 / (n : ℝ) / n)
  let U := rhoC c τ * X
  let cd := √ξ + sharpDeviation n csC δe θlo Θ
  let bn := bN n csC Θ
  have hX : 0 < X := by dsimp [X]; positivity
  have hU : 0 < U := mul_pos hρ hX
  have hmR : (0 : ℝ) < mA n := by exact_mod_cast (by omega : 0 < mA n)
  have hs : 0 < √(2 / (mA n : ℝ)) := by positivity
  have hsplit : X * √(n : ℝ) = √(2 / (n : ℝ)) := by
    rw [← sqrt_mul (by positivity : 0 ≤ 2 / (n : ℝ) / n)]
    congr 1
    field_simp
  have hbd := bN_mono_endpoint (n := n) csC_positive hθhi
  have hCross0 := MA_cross hn0 A c hτ csC_positive hr (BstLean.Part153.Eop_sq hn0 hop) hsc
  have hCross : |(∫ M, Ph A M c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) -
      (∫ M, Pb A c τ M ^ 2 ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ)))| ≤
      2 * (U * √bn) * √(∫ M, Pb A c τ M ^ 2 ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) +
        (∫ M, dC A M c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) := by
    refine hCross0.trans ?_
    dsimp [U, X, bn]
    gcongr
  have hGap := MP_norm_gap_on_source hn0 A M c hτ hδ0 hδ1 hξ hbn he hGlo hGhi hMoment hCross hPi
  have hΓ : |GamS A c τ - 2 / (n : ℝ) * rhoC c τ ^ 2| ≤
      11 / 1000 * (2 / (n : ℝ) * rhoC c τ ^ 2) := by
    rw [BstLean.Part153.GamS_eq_gO hm, abs_le]
    have h := mul_le_mul_of_nonneg_right hδ1
      (show 0 ≤ 2 / (n : ℝ) * rhoC c τ ^ 2 by positivity)
    constructor <;> nlinarith only [hGlo, hGhi, h]
  have hLo := MP_oracle_lower hn A M c hτ hΓ hPb
  have hp : 0 < plow n (11 / 1000) := by
    unfold plow
    have hn14 : (13 : ℝ) < n := by exact_mod_cast (by omega : 13 < n)
    exact mul_pos (sqrt_pos.mpr (by positivity)) (sub_pos.mpr ((div_lt_one hnR).mpr hn14))
  have hLo' : U * √(n : ℝ) * plow n (11 / 1000) ≤ Pb A c τ M := by
    have huSplit : U * √(n : ℝ) = rhoC c τ * √(2 / (n : ℝ)) := by
      dsimp [U]
      rw [mul_assoc, hsplit]
    rw [huSplit]
    exact hLo
  have hd := MA_on_sharp_source hn0 A c hτ csC_positive.le hθlo hθhi hξ hsc hGhi hMoment hMA
  have hLam := scaled_parallel_from_gap (hbar2 A M c τ) (bO A M c τ) hs hU
    (sqrt_pos.mpr hnR) hp hd hGap hLo'
  have hFull := MA_iv (by omega : 6 ≤ n) A M c hτ hMP hd hN hXi
  have hPar := oracle_parallel_radius (by omega : 6 ≤ n) A M c hτ hMP hLam hN hXi
  have hRad : xiNr n (thetaC c τ) MP ≤ xiNr n Θ MP := by
    have hb := BstLean.Part153.N12bar_nonneg n (12 : ℝ)
    have hnb : 0 ≤ N22bar n 12 := by unfold N22bar; positivity
    unfold xiNr
    gcongr
  have hFull' := hFull.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hRad) hX.le)
  have hPar' := hPar.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl hRad) hX.le)
  have hFin := FC_iii hn0 hJ A M c hτ csC_positive hδ0 (by norm_num) hop hsc hGhi hChi
  have hFn : √(2 / (mA n : ℝ)) * nrm ((rhoC c τ)⁻¹ • bT J J A M c τ -
      (rhoC c τ)⁻¹ • bO A M c τ) ≤ X * finiteEnergy n J δe := by
    rw [← smul_sub, BstLean.Part153.nrm_smul, abs_of_pos (inv_pos.mpr hρ)]
    convert hFin using 1 <;> (try simp only [X, finiteEnergy]) <;> ring
  have hLower : X * √(n : ℝ) * plow n (11 / 1000) ≤
      √(2 / (mA n : ℝ)) * nrm ((rhoC c τ)⁻¹ • bO A M c τ) := by
    rw [BstLean.Part153.nrm_smul, abs_of_pos (inv_pos.mpr hρ)]
    have h := div_le_div_of_nonneg_right hLo' hρ.le
    convert h using 1 <;> dsimp [U, Pb] <;> field_simp
  rw [← unit_positive_smul (bO A M c τ) (inv_pos.mpr hρ)] at hPar'
  have hF0 : 0 ≤ cd + xiNr n Θ MP := by
    have h0 := mul_nonneg (sqrt_nonneg (2 / (mA n : ℝ)))
      (BstLean.Part153.nrm_nonneg (hid2Mean_cr A M c τ - (rhoC c τ)⁻¹ • bO A M c τ))
    nlinarith only [hFull', h0, hX]
  have hTransfer := BstLean.Part206.full_parallel_transfer (hid2Mean_cr A M c τ)
    ((rhoC c τ)⁻¹ • bO A M c τ) ((rhoC c τ)⁻¹ • bT J J A M c τ)
    hs.le hX (sqrt_pos.mpr hnR) hp (finiteEnergy_nonneg n J hδ0) hF0 hFull' hPar' hLower
    (upper := √(2 / (mA n : ℝ)) * nrm ((rhoC c τ)⁻¹ • bO A M c τ) / (X * √(n : ℝ)))
    (by field_simp; exact le_rfl) hFn hGuard
  refine ⟨?_, ?_, hTransfer.2.2.2.2⟩
  · simpa only [X, sq_sqrt (by positivity : 0 ≤ 2 / (n : ℝ) / n),
      parallelFormula, parallelOracle, cd, bn] using hTransfer.2.1
  · simpa only [hsplit] using hTransfer.2.2.1

def CentreSource (n J : ℕ) (c : Fin n → ℝ) (τ MP : ℝ) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  {p | p ∈ FullSource n J c τ MP ∧ p.2 ∉ BadPi p.1 c τ 12}

theorem centre_source_charge {n J P : ℕ} (hn : 4096 ≤ n) (hP : 1 ≤ P)
    (hnP : 2 * P + 1 < n) (c : Fin n → ℝ) {τ MP η : ℝ} (hτ : 0 < τ)
    (hMP : 0 < MP) (hη : 0 ≤ η) (hr : rhoBar n csC < 1 / 4) :
    (BstLean.Part153.nuA n).real (CentreSource n J c τ MP)ᶜ ≤
      exp (-(n : ℝ) / 2) + 3445 / (n : ℝ) ^ 2 + 13 * exp (-12) +
        (BstLean.Part153.jS n P η ^ 2 * n / (((n : ℝ) - 1 - 2 * P) * MP)) ^ P := by
  have hn0 : 1 ≤ n := by omega
  let B := {p : Matrix (Fin (mA n)) (Fin n) ℝ ×
    Matrix (Fin (mA n)) (Fin (mA n)) ℝ | p.2 ∈ BadPi p.1 c τ 12}
  have hB : (BstLean.Part153.nuA n).real B ≤ 2 * exp (-12) :=
    BstLean.Part153.prod_real_le_of_fibre (measurableSet_BadPi_joint (one_le_mA hn0) c τ 12)
      (by positivity) (fun A => EPi_prob (one_le_mA hn0) A c τ (by norm_num))
  have he : (CentreSource n J c τ MP)ᶜ = (FullSource n J c τ MP)ᶜ ∪ B := by
    ext p
    simp only [CentreSource, B, mem_compl_iff, mem_setOf_eq, mem_union, not_and_or, not_not]
  rw [he]
  have h := measureReal_union_le (μ := BstLean.Part153.nuA n) (FullSource n J c τ MP)ᶜ B
  have hF := full_source_charge (J := J) hn hP hnP c hτ hMP hη hr
  linarith

/-- The scalar certificates and the charged centre event supply the actual parallel formula. -/
theorem parallel_error_on_source {n J : ℕ} (hn : 4096 ≤ n) (hn1 : n ≤ 16384) (hJ : 1 ≤ J)
    (c : Fin n → ℝ) (hc : 0 < normSq c) {τ δe k k3 θlo Θ S MP : ℝ}
    (hτ : 0 < τ) (hMP : 0 ≤ MP) (v : ℝ → ℝ)
    (C : MomentCertificate n δe k k3 θlo Θ S v) (hδ1 : δe ≤ 11 / 1000)
    (hθlo : θlo ≤ thetaC c τ) (hθhi : thetaC c τ ≤ Θ)
    (he : eMP n δe (momentAllowance n csC δe k k3 Θ S) (bN n csC Θ) ≤ 1 / 10)
    (hGuard : finiteEnergy n J δe / √(n : ℝ) < plow n (11 / 1000))
    (hGroot : 2 * √12 / (n : ℝ) ≤ √(1 - 2 / (n : ℝ) ^ 2))
    (hGlo : 1 - δe ≤ gMinus n) (hGhi : gPlus n ≤ 1 + δe)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ} {M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hSource : (A, M) ∈ CentreSource n J c τ MP) :
    |(√(2 / (mA n : ℝ)) • (hid2Mean_cr A M c τ - (rhoC c τ)⁻¹ • bT J J A M c τ)) ⬝ᵥ
      ((nrm ((rhoC c τ)⁻¹ • bT J J A M c τ))⁻¹ • ((rhoC c τ)⁻¹ • bT J J A M c τ))| ^ 2 ≤
      (2 / (n : ℝ) / n) * parallelFormula n J δe (momentAllowance n csC δe k k3 Θ S)
        (bN n csC Θ) (√(momentAllowance n csC δe k k3 Θ S) + sharpDeviation n csC δe θlo Θ) Θ MP ∧
    √(2 / (n : ℝ)) * (plow n (11 / 1000) - finiteEnergy n J δe / √(n : ℝ)) ≤
      √(2 / (mA n : ℝ)) * nrm ((rhoC c τ)⁻¹ • bT J J A M c τ) ∧
    (rhoC c τ)⁻¹ • bT J J A M c τ ≠ 0 := by
  have hn0 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn0 c hτ
  have hA : A ∈ BstLean.Part153.Eop n ∧ csC * τ ^ 2 ≤ sO2 A c τ ∧
      A ∉ BstLean.Part153.BadE n c τ := by
    have h := hSource.1.1.1
    simp only [FirstEnergyBad, mem_union, mem_compl_iff, mem_setOf_eq, not_or, not_not,
      not_lt] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩
  have hM : M ∉ BadPb A c τ 12 ∧ M ∉ BadChi n J A c τ 12 := by
    have h := hSource.1.1.2
    simp only [SecondEnergyBad, mem_union, not_or] at h
    exact ⟨h.1.2, h.2⟩
  obtain ⟨hLo, hHi⟩ := energy_on_source (by omega : 2 ≤ n) c τ hA.2.2 hGroot
  have hscale : 0 ≤ (2 / n * rhoC c τ ^ 2) := by positivity
  have hLow : (1 - δe) * (2 / n) * rhoC c τ ^ 2 ≤ gO A c τ := by
    have := mul_le_mul_of_nonneg_left hGlo hscale
    nlinarith only [hLo, this]
  have hHigh : gO A c τ ≤ (1 + δe) * (2 / n) * rhoC c τ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hGhi hscale
    nlinarith only [hHi, this]
  have hMoment := MA_moment_on_source (by omega : 4096 ≤ n) hn1 c hc hτ csC_positive
    C.delta_lt C.k_gt C.k3_gt C.theta_lower hθlo hθhi v C.v_pos C.supremum
    C.ratio C.ratio_gamma C.gap C.gap_gamma hA.1 hA.2.1 hLow hSource.1.2.1
  have hξ : 0 ≤ momentAllowance n csC δe k k3 Θ S := by
    have hi : 0 ≤ ∫ M, dC A M c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ)) :=
      integral_nonneg fun _ => sq_nonneg _
    have hp : 0 < rhoC c τ ^ 2 * (2 / (n : ℝ) / n) := by positivity
    nlinarith only [hi, hMoment, hp]
  exact actual_parallel_transfer (by omega) hJ A M c hτ C.delta_nonneg hδ1 hξ hMP hθlo hθhi C.ratio
    he hGuard hA.1 hA.2.1 hLow hHigh hMoment hSource.1.2.2.2.1 hSource.2 hM.1
    (BstLean.Part153.N22_le_bar hn0 hSource.1.2.2.1 hSource.1.2.2.2.2.1)
    hSource.1.2.2.2.2.2 hM.2

#print axioms actual_parallel_transfer
#print axioms centre_source_charge
#print axioms parallel_error_on_source
end BstLean.Part211
