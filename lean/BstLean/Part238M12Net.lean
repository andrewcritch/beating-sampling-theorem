import BstLean.Part238M12

/-! Part 238: the sharp covariance route instantiated on the M1/M2 range `n ≥ 11883` with the
Part 235 windows `(6, 20, 8)` and `(2.8, 7.5, 3.2)`, retained `θ ∈ [.46, .528]`, and core cap `.63`.
All geometric premises are discharged. The TI hypotheses, the fourth-moment bound and the scalar
bound remain explicit premises. -/
namespace BstLean.Part238
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part157 BstLean.Part160 BstLean.Part182
  BstLean.Part208
open BstLean.Part199 (Window radiusMinus exampleCore exampleWide example_nested pairRowBound
  outsideBound)
open BstLean.Part150 (thetaC)
open BstLean.Part153 (nrm Xi4)

/-- **Retained charge on M1/M2.** The joint wide/mode event costs `ε` once, given the wide
operator TI hypothesis on overlaps `[.34, .73]` and the three-mode TI hypothesis on `[.40, .63]`. -/
theorem SharpCovEvent_ret_charge_M12 {n : ℕ} (hn : 11883 ≤ n) (D : Design n) (hτ : TauWorld D)
    {lam₀ kE ko ks δ ε : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hlam : ta_lam kE ko ks ≤ lam₀) (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hTI₀ : TI_hyp n (34 / 100) (73 / 100) lam₀ δ)
    (hTI₁ : TI3_hyp n (40 / 100) (63 / 100) kE ko ks δ) :
    (retDist D.toCentres).real
      (agentEv D (SharpCovEvent n exampleWide exampleCore (46 / 100) (528 / 1000) lam₀
        kE ko ks (63 / 100) (δ / ε)))ᶜ ≤ ε :=
  SharpCovEvent_ret_charge (by omega) D hτ exampleWide exampleCore example_nested
    hkE hko hks (by norm_num) hlam hδ hε
    (fun θ hθ => BstLean.Part235.wide_overlap_guard hn hθ.1 hθ.2)
    (fun θ hθ => BstLean.Part235.core_overlap_guard hn hθ.1 hθ.2) hTI₀ hTI₁

/-- The sharp coefficient is monotone in the gain. -/
lemma sharpK_mono {kE ko ks χ χ' : ℝ} (hko : 0 ≤ ko) (hks : 0 ≤ ks) (hχ : 0 ≤ χ)
    (h : χ ≤ χ') : sharpK kE ko ks χ ≤ sharpK kE ko ks χ' := by
  unfold sharpK
  have h1 : √χ ≤ √χ' := Real.sqrt_le_sqrt h
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * ko)
  have h3 := mul_le_mul_of_nonneg_left h hks
  linarith

/-- The scalar is monotone in the core coefficient. -/
lemma sharpScalar_mono_K {n : ℕ} {θ : ℝ} {w₀ w₁ : Window} {K K' lam₀ E M h : ℝ}
    (hθ : 0 ≤ θ) (hE : 0 ≤ E) (hK : K ≤ K') :
    sharpScalar n θ w₀ w₁ K lam₀ E M h ≤ sharpScalar n θ w₀ w₁ K' lam₀ E M h := by
  unfold sharpScalar
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK hE) hθ
  nlinarith

/-- **Sharp covariance transfer on M1/M2.** For `n ≥ 11883`, retained `θ ∈ [.46, .528]`, the
joint event, and the fourth-moment bound, the scalar with core coefficient
`min(kE + 2 ko √0.51 + 0.51 ks, λ₁)` bounds `COV_at`. -/
theorem cov_at_sharp_M12 {n : ℕ} (hn : 11883 ≤ n) (D : Design n) (k : Ret n)
    (hτ : 0 < D.tau0 k) {kE ko ks lam₀ M b N : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hl₀ : 0 ≤ lam₀) (hM : 0 ≤ M)
    (hw : thetaC k.1.2 (D.tau0 k) ∈ Set.Icc (46 / 100) (528 / 1000))
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤ M * (2 / (n : ℝ)) / n)
    (hC : ((k.1.2, D.tau0 k), (k.2.1.1.1, k.2.1.1.2)) ∈
      SharpCovEvent n exampleWide exampleCore (46 / 100) (528 / 1000) lam₀ kE ko ks (63 / 100) b)
    (hN : sharpScalar n (thetaC k.1.2 (D.tau0 k)) exampleWide exampleCore
        (min (sharpK kE ko ks (51 / 100)) (ta_lam kE ko ks))
        lam₀ (1 - 4 * thetaC k.1.2 (D.tau0 k) / n)⁻¹ M
        (2 * exp (-exampleWide.pair ^ 2 / 2) + 2 * b) ≤ N) : COV_at D k N := by
  have hn6 : 6 ≤ n := by omega
  have hn0 : 0 < n := by omega
  set θ := thetaC k.1.2 (D.tau0 k) with hθd
  have hθ1 : θ < 1 := lt_of_le_of_lt hw.2 (by norm_num)
  have hc : k.1.2 ≠ 0 := ne_zero_of_thetaC_lt hn0 hτ hθ1
  obtain ⟨hR, hat, hchi⟩ := chi_core_M12 hn k.1.2 hτ hw.1 hw.2
  obtain ⟨hr₀, -⟩ := BstLean.Part235.wide_radius_caps hn hw.1 hw.2
  obtain ⟨hr₁, -⟩ := BstLean.Part235.core_radius_caps hn hw.1 hw.2
  obtain ⟨hcau, ha, hu⟩ := centre_decomp hc
  have hθ0 : 0 ≤ θ := by linarith [hw.1]
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hE : 0 ≤ (1 - 4 * θ / n)⁻¹ := by
    apply inv_nonneg.mpr
    have : 4 * θ / (n : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith [hw.2]
    linarith
  have hsm1 := axialProjLower_le_one n ha hτ exampleCore.t_nonneg exampleCore.z_nonneg hat
  have hχ0 : 0 ≤ chiCore n (nrm k.1.2) (D.tau0 k) exampleCore.t exampleCore.z
      (axialProjLower n (nrm k.1.2) (D.tau0 k) exampleCore.t exampleCore.z) (63 / 100) := by
    unfold chiCore
    exact chi_nonneg hR (by norm_num) hsm1
  have hK : min (sharpK kE ko ks (chiCore n (nrm k.1.2) (D.tau0 k) exampleCore.t exampleCore.z
      (axialProjLower n (nrm k.1.2) (D.tau0 k) exampleCore.t exampleCore.z) (63 / 100)))
      (ta_lam kE ko ks) ≤ min (sharpK kE ko ks (51 / 100)) (ta_lam kE ko ks) :=
    min_le_min_right _ (sharpK_mono hko hks hχ0 hchi)
  exact cov_at_sharp_centre hn6 D k hτ hc exampleWide exampleCore example_nested hkE hko hks
    hl₀ hM hw (by norm_num) (by linarith) (by linarith) hat hR (by norm_num) hX hC
    ((sharpScalar_mono_K hθ0 hE hK).trans hN)

end BstLean.Part238
