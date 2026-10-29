import BstLean.Part278StBase2
import BstLean.Part188R164End
import BstLean.Part161Fl

/-! Part 278 (O5): `odd_root_goodA16200`, the discharge of `hodd` on `goodA` from `n ≥ 16 200`. -/

namespace BstLean.Part278

open Real
open BstLean.Part130 (normSq normSq_nonneg mA)
open BstLean.Part157 (Ret qTilde Js)
open BstLean.Part169 (A1 A2 OpB Jz nodeS eR O1n O2n paperDesignP tauR bR passF passW
  measurable_passF measurable_passW bulk_of_window)
open BstLean.Part272 (statedDesign)

variable {n : ℕ}

/-- **The odd root on `goodA n (paperDesignP n) univ`** (`n ≥ 16 200`, re-based `Part188.Base164_R` lemmas). -/
theorem odd_root_goodA16200 (hn : 16200 ≤ n) (ho : Odd n) (t : ℝ) (c : Ret n)
    (hc : c ∈ BstLean.Part164.goodA n (paperDesignP n) Set.univ) :
    |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤ 1 / 10 ^ 20 := by
  obtain ⟨hτ, hθ0, hθ1⟩ := BstLean.Part188.Base164_R.window_goodA hn passF passW measurable_passF
    measurable_passW _ c hc
  have h1 := BstLean.Part164.eop_of_goodC16 (BstLean.Part188.Base164_R.goodC16_of_goodA hn passF passW
    measurable_passF measurable_passW hc)
  have h2 : c ∈ BstLean.Part164.Eop2 n := hc.2.1.2.2
  have hO1 := BstLean.Part169.opB_of_opN _ h1
  have hO2 := BstLean.Part169.opB_of_opN _ h2
  -- `e_b > 0` and `|c_A|² ≤ 2 e_b χ`: the proof of `Part169.cA_input`, on `goodA`
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hE : c ∈ BstLean.Part164.EcA (BstLean.Part157.paperCentres n) := hc.2.1.2.1.2
  have hpos := (BstLean.Part188.Base164_R.cA_of_good hn passF passW measurable_passF measurable_passW
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
        have : (16200:ℝ) ≤ n := by exact_mod_cast hn
        linarith
      calc √((n:ℝ) * 12) ≤ √(((n:ℝ) * 12) ^ 2) :=
            sqrt_le_sqrt (by nlinarith)
        _ = (n:ℝ) * 12 := sqrt_sq (by linarith)
    have : (16200:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  exact odd_root_ops (by omega) ho t c hO1 hO2 hτ hθ0 hθ1 he hcA hχ0 hχ

/-- `repla_st_hsum` with the chi form of the fluctuation hypothesis. -/
theorem repla_st_hsum_chi (hn : 16200 ≤ n) (D : BstLean.Part157.Design n) (t : ℝ)
    {E : Set (Ret n)} {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hw : ∀ c ∈ E, BstLean.Part161.WINDOW D c)
    (hd : ∀ c ∈ E, ∃ (d : BstLean.Part161.SplitData n) (ε₀ δ₀ slow : ℝ),
      BstLean.Part161.FLUCT_chi_hyp D c d ε₀ δ₀ slow hfl ∧ BstLean.Part161.BIAS_hyp D c d hb)
    (hodd : ∀ c ∈ E,
      |√(qTilde (BstLean.Part272.statedDesign n) t c) - √(qTilde D t c)| ≤ 1 / 10 ^ 20)
    (hQ : ∀ c, BstLean.Part157.QStand (BstLean.Part272.statedDesign n) t c =
      BstLean.Part157.QStand D t c) :
    BstLean.Part157.REPLA_mix_hyp (BstLean.Part272.statedDesign n) t BstLean.Part156.hAL E :=
  repla_st_hsum hn D t hsum hw (fun c hc => by
    obtain ⟨d, ε₀, δ₀, slow, hF, hB⟩ := hd c hc
    exact ⟨d, BstLean.Part161.fluct_of_chi D t c d hF, hB⟩) hodd hQ

end BstLean.Part278
