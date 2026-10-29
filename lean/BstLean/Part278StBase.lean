import BstLean.Part278Good16
import BstLean.Part164End
import BstLean.Part169In

/-!
# Part 278 (O5): hand-written base of the generated `_st` chains

* `BstLean.Part164.goodA_univ`: `goodA n D EA ⊆ goodA n D univ` (the free event drops out).
* `BstLean.Part163.classifier_paper_free23_fluct_st`: the stated-design form of
  `classifier_paper_free23_fluct` for any tables `fT wT`. The premises FLUCT and BIAS are for
  `D = paperDesign n fT wT`. The premise `hodd` compares `statedDesign n` with `D` on the same good
  set. The proof spends the reserve `10⁻²⁰`.
* `BstLean.Part278.odd_root_goodA`: for odd `n ≥ 16 384` and `c ∈ goodA n (paperDesignP n) univ`,
  the odd root is `≤ 10⁻²⁰`. This discharges `hodd` at the top of every generated chain.
-/

namespace BstLean.Part164

open BstLean.Part157

variable {n : ℕ}

theorem goodA_univ {D : Design n} {EA : Set (Ret n)} {c : Ret n} (hc : c ∈ goodA n D EA) :
    c ∈ goodA n D Set.univ := by
  unfold goodA goodSet at hc ⊢
  exact ⟨hc.1, ⟨hc.2.1.1, ⟨⟨Set.mem_univ c, hc.2.1.2.1.2⟩, hc.2.1.2.2⟩⟩, hc.2.2⟩

end BstLean.Part164

namespace BstLean.Part163

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part156 BstLean.Part160
open BstLean.Part161 (FLUCT_chi_hyp BIAS_hyp SplitData)

variable {n : ℕ}

theorem classifier_paper_free23_fluct_st (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomA)
    (hFl : ∀ c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (d : SplitData n) (ε₀ δ₀ slow : ℝ),
        FLUCT_chi_hyp (paperDesign n fT wT hf hw) c d ε₀ δ₀ slow (2159 / 10 ^ 6) ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c d (4295 / 10 ^ 6))
    (hodd : ∀ c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL,
      |√(qTilde (BstLean.Part272.statedDesign n) t c) -
        √(qTilde (paperDesign n fT wT hf hw) t c)| ≤ 1 / 10 ^ 20) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t aL (10 ^ 12) x.1 x.2)} := by
  have h0 : REPLA_mix_hyp (paperDesign n fT wT hf hw) t (6583 / 10 ^ 6)
      (goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL) := by
    intro c hc
    obtain ⟨d, ε₀, δ₀, slow, hF, hB⟩ := hFl c hc
    have hwc : BstLean.Part161.WINDOW (paperDesign n fT wT hf hw) c :=
      BstLean.Part161.window_paper (by omega) fT wT hf hw hc.1.1 hc.2.1.1.1 hc.2.1.1.2
    have h := BstLean.Part161.repla_root_of_split (by omega) (paperDesign n fT wT hf hw) t c
      hwc.1 hwc.2.1 d (BstLean.Part161.fluct_of_chi (paperDesign n fT wT hf hw) t c d hF) hB
      (BstLean.Part161.tail_of_window (by omega) (paperDesign n fT wT hf hw) c hwc)
    have ht := BstLean.Part161.tail_root_num
    linarith
  have h1 := BstLean.Part278.repla_transfer (D := paperDesign n fT wT hf hw)
    (D' := BstLean.Part272.statedDesign n) (fun c => rfl) h0 hodd
  have hRA : REPLA_mix_hyp (paperDesign n BstLean.Part272.passFSt BstLean.Part272.passWSt
      BstLean.Part272.measurable_passFSt BstLean.Part272.measurable_passWSt) t hAL
      (goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩
          Eframe (paperDesign n BstLean.Part272.passFSt BstLean.Part272.passWSt
            BstLean.Part272.measurable_passFSt BstLean.Part272.measurable_passWSt))
        (HbarW (paperDesign n BstLean.Part272.passFSt BstLean.Part272.passWSt
          BstLean.Part272.measurable_passFSt BstLean.Part272.measurable_passWSt)) hWL) := by
    unfold hAL
    exact h1
  exact classifier_paper_free23 hn BstLean.Part272.passFSt BstLean.Part272.passWSt
    BstLean.Part272.measurable_passFSt BstLean.Part272.measurable_passWSt t hEA hA hroom hRA

end BstLean.Part163

namespace BstLean.Part278

open Real
open BstLean.Part130 (normSq normSq_nonneg mA)
open BstLean.Part157 (Ret qTilde Js)
open BstLean.Part169 (A1 A2 OpB Jz nodeS eR O1n O2n paperDesignP tauR bR passF passW
  measurable_passF measurable_passW bulk_of_window)
open BstLean.Part272 (statedDesign)

variable {n : ℕ}

/-- The odd root from the operator bounds directly (the body of `odd_root_good`). -/
theorem odd_root_ops (hn : 16200 ≤ n) (ho : Odd n) (t : ℝ) (c : Ret n)
    (h1 : OpB (A1 c) (O1n n)) (h2 : OpB (A2 c) (O2n n)) (hτ : 0 < tauR c)
    (hθ0 : 46 / 100 ≤ BstLean.Part150.thetaC c.1.2 (tauR c))
    (hθ1 : BstLean.Part150.thetaC c.1.2 (tauR c) ≤ 55 / 100)
    {χ : ℝ} (he : 0 < eR c) (hc : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * χ)
    (hχ0 : 0 ≤ χ) (hχ : χ ≤ n) :
    |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤ 1 / 10 ^ 20 := by
  obtain ⟨hLH, hs, -⟩ := bulk_of_window (by omega) c hτ hθ0 hθ1
  have hq := qB_nonneg16200 hn
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  refine odd_root_lt (by omega) ho (Jz_pos (by omega)) t c
    (OpB_mono h2 O2n_nonneg (O2n_le (by omega))) (fun g hg => ?_) he hc hχ0 hχ
  obtain ⟨hL, hH⟩ := nodeS_mem (by omega) c hLH g hg
  have hs1 : (nodeS c g) ^ 2 ≤ 1 := by have := hs _ hL hH; linarith
  have hO1 := O1n_sq_le (n := n) (by omega)
  have hF := frob_le c h1
  calc ∑ i, aw c (nodeS c g) i ^ 2 ≤ ∑ i, 2 * ∑ j, A1 c i j ^ 2 :=
        Finset.sum_le_sum fun i _ => aw_sq_le (by omega) c _ hs1 i
    _ = 2 * ∑ i, ∑ j, A1 c i j ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * (n * O1n n ^ 2) := by linarith
    _ ≤ 2 * (n * (8 * n)) := by
        have := mul_le_mul_of_nonneg_left hO1 (by linarith : (0:ℝ) ≤ n)
        linarith
    _ ≤ 16 * (n : ℝ) ^ 3 := by
        have : (n:ℝ) ^ 2 ≤ (n:ℝ) ^ 3 := pow_le_pow_right₀ hnR (by norm_num)
        nlinarith

/-- **The odd root on `goodA n (paperDesignP n) univ`** (`n ≥ 16 384`). -/
theorem odd_root_goodA (hn : 16384 ≤ n) (ho : Odd n) (t : ℝ) (c : Ret n)
    (hc : c ∈ BstLean.Part164.goodA n (paperDesignP n) Set.univ) :
    |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤ 1 / 10 ^ 20 := by
  obtain ⟨hτ, hθ0, hθ1⟩ := BstLean.Part164.window_goodA hn passF passW measurable_passF
    measurable_passW _ c hc
  have h1 := BstLean.Part164.eop_of_goodC16 (BstLean.Part164.goodC16_of_goodA hn passF passW
    measurable_passF measurable_passW hc)
  have h2 : c ∈ BstLean.Part164.Eop2 n := hc.2.1.2.2
  have hO1 := BstLean.Part169.opB_of_opN _ h1
  have hO2 := BstLean.Part169.opB_of_opN _ h2
  -- `e_b > 0` and `|c_A|² ≤ 2 e_b χ`: the proof of `Part169.cA_input`, on `goodA`
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hE : c ∈ BstLean.Part164.EcA (BstLean.Part157.paperCentres n) := hc.2.1.2.1.2
  have hpos := (BstLean.Part164.cA_of_good hn passF passW measurable_passF measurable_passW
    hc).1
  obtain ⟨hb1, -⟩ := hE
  have hb : normSq ((BstLean.Part157.paperCentres n).bA c.1 c.2.1.1) = normSq (bR c) := rfl
  rw [hb] at hb1
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hm] at hb1
  have hup : 0 < BstLean.Part164.chiUp n := by unfold BstLean.Part164.chiUp; positivity
  have he : 0 < eR c := by
    unfold eR
    have : 0 < normSq (bR c) := by
      by_contra hneg
      have h0 : normSq (bR c) = 0 := le_antisymm (le_of_not_gt hneg) (normSq_nonneg _)
      rw [h0] at hb1; simp at hb1; linarith
    positivity
  have hcA : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * (BstLean.Part164.chiUp n / n) := by
    refine hb1.trans (le_of_eq ?_)
    unfold eR
    field_simp
  have hχ0 : 0 ≤ BstLean.Part164.chiUp n / n := by positivity
  have hχ : BstLean.Part164.chiUp n / n ≤ n := by
    rw [div_le_iff₀ hnR]
    unfold BstLean.Part164.chiUp
    have hs : √((n:ℝ) * 12) ≤ (n:ℝ) * 12 := by
      have h12 : (1:ℝ) ≤ (n:ℝ) * 12 := by
        have : (16384:ℝ) ≤ n := by exact_mod_cast hn
        linarith
      calc √((n:ℝ) * 12) ≤ √(((n:ℝ) * 12) ^ 2) :=
            sqrt_le_sqrt (by nlinarith)
        _ = (n:ℝ) * 12 := sqrt_sq (by linarith)
    have : (16384:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  exact odd_root_ops (by omega) ho t c hO1 hO2 hτ hθ0 hθ1 he hcA hχ0 hχ

end BstLean.Part278
