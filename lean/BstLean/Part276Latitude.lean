import BstLean.Part252All
import BstLean.Part228Scale

/-! The order-twelve latitude moment of the program node measure.
The exact latitude moment, the grid width and the certified bulk tail give
a sharp node moment, valid for every dimension from 8000 under the World window. -/
namespace BstLean.Part276
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169

theorem qB_nonneg_8000 {n : ℕ} (hn : 8000 ≤ n) : 0 ≤ qB n := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (n : ℝ)) ≤ 83 / 10000 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) := by positivity
  unfold qB
  nlinarith

/-- The World window as a latitude-parameter interval. -/
theorem window_theta {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hW : WINDOW (paperDesignP n) c) :
    46 / 100 ≤ BstLean.Part150.thetaC c.1.2 (tauR c) ∧
      BstLean.Part150.thetaC c.1.2 (tauR c) ≤ 54 / 100 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hτ : 0 < tauR c := hW.2.1
  have hden : 0 < normSq c.1.2 + (n : ℝ) * tauR c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hτ))
  unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  rw [sq_sqrt hden.le]
  exact ⟨(le_div_iff₀ hden).mpr hW.2.2.1, (div_le_iff₀ hden).mpr hW.2.2.2⟩

/-- Pointwise splitting with a free ratio `δ`. -/
theorem split_pow12 {q x y δ : ℝ} (hq : 0 ≤ q) (hx : 0 ≤ x) (hy : 0 ≤ y) (hδ : 0 < δ)
    (h : q ≤ x + y) : q ^ 12 ≤ (1 + δ) ^ 12 * (x ^ 12 + (y / δ) ^ 12) := by
  have hyd : 0 ≤ y / δ := div_nonneg hy hδ.le
  have hyδ : y = δ * (y / δ) := by field_simp
  rcases le_total (y / δ) x with hc | hc
  · have hb : q ≤ (1 + δ) * x := by nlinarith
    have hp := pow_le_pow_left₀ hq hb 12
    rw [mul_pow] at hp
    have : 0 ≤ (1 + δ) ^ 12 * (y / δ) ^ 12 := by positivity
    nlinarith
  · have hb : q ≤ (1 + δ) * (y / δ) := by nlinarith
    have hp := pow_le_pow_left₀ hq hb 12
    rw [mul_pow] at hp
    have : 0 ≤ (1 + δ) ^ 12 * x ^ 12 := by positivity
    nlinarith

/-- Pointwise node bound inside the bulk. -/
theorem node_q_le {n : ℕ} (hn : 8000 ≤ n) (c : Ret n) (hW : WINDOW (paperDesignP n) c)
    {s : ℝ} (hs1 : nodeL c ≤ s) (hs2 : s ≤ nodeH c) :
    0 ≤ 1 - nodeS c (gIdx c s) ^ 2 ∧ 1 - nodeS c (gIdx c s) ^ 2 ≤ (1 - s ^ 2) + nodeD c := by
  have hθ := window_theta (by omega) c hW
  obtain ⟨hLH, hbulk, -⟩ := bulk_of_window (by omega) c hW.2.1 hθ.1 (by linarith [hθ.2])
  have hq := qB_nonneg_8000 hn
  obtain ⟨hnear, hlt⟩ := gIdx_near (by omega) c hLH hs1 hs2
  obtain ⟨hg1, hg2⟩ := nodeS_mem c hLH hlt
  set g := nodeS c (gIdx c s)
  have hg := hbulk g hg1 hg2
  have hss := hbulk s hs1 hs2
  have hab := abs_le.mp hnear
  have hD : 0 ≤ nodeD c := by
    unfold nodeD Js
    have : 0 < nodeH c - nodeL c := by linarith
    positivity
  have hs_abs : |s| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have hg_abs : |g| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  refine ⟨by linarith, ?_⟩
  have hsum : |s + g| ≤ 2 := (abs_add_le s g).trans (by linarith)
  have hprod : s ^ 2 - g ^ 2 ≤ nodeD c := by
    have he : s ^ 2 - g ^ 2 = (s - g) * (s + g) := by ring
    rw [he]
    calc (s - g) * (s + g) ≤ |(s - g) * (s + g)| := le_abs_self _
      _ = |s - g| * |s + g| := abs_mul _ _
      _ ≤ (nodeD c / 2) * 2 :=
        mul_le_mul hnear hsum (abs_nonneg _) (by positivity)
      _ = nodeD c := by ring
  linarith

/-- The node order-twelve moment, before numerical evaluation. -/
theorem node_latitude_moment12 {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    (hW : WINDOW (paperDesignP n) c) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ a, ENNReal.ofReal ((1 - nodeS c (gIdx c (latC (paperDesignP n) c a)) ^ 2) ^ 12)
        ∂muI n ≤
      ENNReal.ofReal ((1 + δ) ^ 12 *
          BstLean.Part212.latitudeCoefficient n 12
            (BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c)) ^ 12 +
        (1 + δ) ^ 12 * (nodeD c / δ) ^ 12 +
        BstLean.Part228.bulkTailMass (paperDesignP n) c
          (-(8 / √(n : ℝ)) / (2 * (paperDesignP n).tau0 c ^ 2))
          ((8 / √(n : ℝ)) / (2 * (paperDesignP n).tau0 c ^ 2))) := by
  set D := paperDesignP n
  set B := bulkIx D c with hB
  set mt := BstLean.Part228.bulkTailMass D c
    (-(8 / √(n : ℝ)) / (2 * D.tau0 c ^ 2)) ((8 / √(n : ℝ)) / (2 * D.tau0 c ^ 2))
  set Θ := BstLean.Part212.latitudeCoefficient n 12
    (BstLean.Part150.thetaC c.1.2 (D.tau0 c))
  set y := nodeD c
  have hτ : 0 < D.tau0 c := hW.2.1
  have hθ := window_theta (by omega) c hW
  obtain ⟨hLH, hbulk, -⟩ := bulk_of_window (by omega) c hW.2.1 hθ.1 (by linarith [hθ.2])
  have hq0 := qB_nonneg_8000 hn
  have hy : 0 ≤ y := by
    change 0 ≤ nodeD c
    unfold nodeD Js
    have : 0 < nodeH c - nodeL c := by linarith
    positivity
  have hBm : MeasurableSet B := measurableSet_bulkIx D c
  have hlatm : Measurable (fun a => (1 - latC D c a ^ 2) ^ 12) :=
    (measurable_const.sub ((measurable_latC D c).pow_const 2)).pow_const 12
  -- pointwise bound
  have hpt : ∀ a, ENNReal.ofReal ((1 - nodeS c (gIdx c (latC D c a)) ^ 2) ^ 12) ≤
      (ENNReal.ofReal ((1 + δ) ^ 12) * ENNReal.ofReal ((1 - latC D c a ^ 2) ^ 12) +
        ENNReal.ofReal ((1 + δ) ^ 12 * (y / δ) ^ 12)) + Bᶜ.indicator 1 a := by
    intro a
    by_cases ha : a ∈ B
    · rw [indicator_of_notMem (show a ∉ Bᶜ from fun h => h ha), add_zero,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hab : latC D c a ∈ Icc (nodeL c) (nodeH c) := ha
      obtain ⟨h0, h1⟩ := node_q_le hn c hW hab.1 hab.2
      have hl := BstLean.Part162.latitude_sq_le (n := n) (√(normSq c.1.2)) (D.tau0 c) a
      have hx : 0 ≤ 1 - latC D c a ^ 2 := by
        change 0 ≤ 1 - BstLean.Part157.latitude (√(normSq c.1.2)) (D.tau0 c) a ^ 2
        linarith
      have := split_pow12 h0 hx hy hδ h1
      linarith
    · rw [indicator_of_mem (show a ∈ Bᶜ from ha), Pi.one_apply]
      refine le_add_left (ENNReal.ofReal_le_one.mpr ?_)
      obtain ⟨hg1, hg2⟩ := nodeS_mem c hLH (gIdx_lt c (by omega) (latC D c a))
      have hg := hbulk _ hg1 hg2
      have h0 : 0 ≤ 1 - nodeS c (gIdx c (latC D c a)) ^ 2 := by linarith
      have h1 : 1 - nodeS c (gIdx c (latC D c a)) ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (nodeS c (gIdx c (latC D c a)))]
      exact pow_le_one₀ h0 h1
  -- integrate
  have hm1 : Measurable (fun a => ENNReal.ofReal ((1 + δ) ^ 12) *
      ENNReal.ofReal ((1 - latC D c a ^ 2) ^ 12)) :=
    (ENNReal.measurable_ofReal.comp hlatm).const_mul _
  have hm12 : Measurable (fun a => ENNReal.ofReal ((1 + δ) ^ 12) *
      ENNReal.ofReal ((1 - latC D c a ^ 2) ^ 12) +
        ENNReal.ofReal ((1 + δ) ^ 12 * (y / δ) ^ 12)) := hm1.add measurable_const
  have hint := lintegral_mono (μ := muI n) hpt
  rw [lintegral_add_left hm12, lintegral_add_left hm1, lintegral_const_mul' _ _
    ENNReal.ofReal_ne_top, lintegral_const, measure_univ, mul_one,
    lintegral_indicator_one hBm.compl] at hint
  have hlat : ∫⁻ a, ENNReal.ofReal ((1 - latC D c a ^ 2) ^ 12) ∂muI n ≤
      ENNReal.ofReal (Θ ^ 12) :=
    BstLean.Part212.latitude_moment_exact (p := 12) (by norm_num) (by omega) c.1.2 hτ
  have ht := BstLean.Part228.tail_hyp_chernoff D c
    (BstLean.Part228.bulk_domain_explicit (by omega) D c hW)
  have htail : muI n Bᶜ ≤ ENNReal.ofReal mt := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (muI n) Bᶜ)]
    exact ENNReal.ofReal_le_ofReal ht
  have hmt : 0 ≤ mt := measureReal_nonneg.trans ht
  have hA : (0 : ℝ) ≤ (1 + δ) ^ 12 := by positivity
  have hΘ : (0 : ℝ) ≤ Θ ^ 12 := by positivity
  have hb : (0 : ℝ) ≤ (1 + δ) ^ 12 * (y / δ) ^ 12 := by positivity
  refine hint.trans ?_
  calc
    _ ≤ ENNReal.ofReal ((1 + δ) ^ 12) * ENNReal.ofReal (Θ ^ 12) +
        ENNReal.ofReal ((1 + δ) ^ 12 * (y / δ) ^ 12) + ENNReal.ofReal mt :=
      add_le_add (add_le_add (by gcongr) le_rfl) htail
    _ = _ := by
      rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_add (mul_nonneg hA hΘ) hb,
        ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hA hΘ) hb) hmt]

/-- The certified tail mass is below `5e-17` from dimension 8000. -/
theorem bulkTailMass_small {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    (hW : WINDOW (paperDesignP n) c) :
    BstLean.Part228.bulkTailMass (paperDesignP n) c
      (-(8 / √(n : ℝ)) / (2 * (paperDesignP n).tau0 c ^ 2))
      ((8 / √(n : ℝ)) / (2 * (paperDesignP n).tau0 c ^ 2)) ≤ 5 / 10 ^ 17 := by
  have h := BstLean.Part228.frontierTailRoot_lt hn (paperDesignP n) c hW
  unfold BstLean.Part228.frontierTailRoot BstLean.Part228.bulkTailRoot at h
  have h2 := (Real.sqrt_lt' (by norm_num)).mp h
  norm_num at h2
  linarith

end BstLean.Part276
