import BstLean.Part188All
import BstLean.Part186RA5
import BstLean.Part186Def
import BstLean.Part190RAa




namespace BstLean.Part190.RA
open BstLean.Part186 BstLean.Part186.RA BstLean.Part186.RA.R

open Real BstLean.Part186.RA


theorem finalF {m : ℕ} {N y K μ Kb μb ε T Bb : ℝ} (hy0 : 0 < y) (hy : y ≤ 1 / 127)
    (hN : N * y ^ 2 = 1) (hm : (m : ℝ) * y ^ 4 = 1)
    (hK0 : 0 ≤ K) (hK : K ≤ Kb * y ^ 10) (hμ0 : 0 ≤ μ) (hμ : μ ≤ μb * y ^ 10)
    (hε : 0 < ε) (hT : 0 < T) (hBb : 0 ≤ Bb)
    (hnum : (1 + ε) ^ 3 * μb ^ 4 + (1 + 1 / ε) ^ 3 *
      ((105 * sk Kb μb 384 2 ^ 4 * (1 / 127) ^ 8 +
        490 * sk Kb μb 384 2 ^ 2 * sk Kb μb 10321920 4 * (1 / 127) ^ 12 +
        (63 * sk Kb μb 10321920 4 ^ 2 + 56 * sk Kb μb 384 2 * sk Kb μb 1961990553600 6) *
          (1 / 127) ^ 16 + sk Kb μb 1371195958099968000 8 * (1 / 127) ^ 20) / (2 * T) +
        T * (1 / 127) ^ 8 / 2) ≤ Bb ^ 8) :
    N ^ 4 * ((1 + ε) ^ 3 * ((m : ℝ) * μ) ^ 4 +
      (1 + 1 / ε) ^ 3 * (M8 m K μ / (2 * (T * y ^ 32)) + T * y ^ 32 / 2)) ≤ (Bb / N) ^ 8 := by
  have hKb : 0 ≤ Kb := by
    by_contra h; push Not at h; have := mul_neg_of_neg_of_pos h (pow_pos hy0 10); linarith
  have hμb : 0 ≤ μb := by
    by_contra h; push Not at h; have := mul_neg_of_neg_of_pos h (pow_pos hy0 10); linarith
  have s2 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 384) 2 (e := 16) (by norm_num)
  have s4 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 10321920) 4 (e := 36)
    (by norm_num)
  have s6 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 1961990553600) 6 (e := 56)
    (by norm_num)
  have s8 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 1371195958099968000) 8
    (e := 76) (by norm_num)
  set S2 := sk Kb μb 384 2
  set S4 := sk Kb μb 10321920 4
  set S6 := sk Kb μb 1961990553600 6
  set S8 := sk Kb μb 1371195958099968000 8
  have hS2 : 0 ≤ S2 := by unfold S2 sk; positivity
  have hS4 : 0 ≤ S4 := by unfold S4 sk; positivity
  have hS6 : 0 ≤ S6 := by unfold S6 sk; positivity
  have hS8 : 0 ≤ S8 := by unfold S8 sk; positivity
  have q2 := Sb_nonneg (m := m) hK0 hμ0 (by norm_num : (0 : ℝ) ≤ 384) 2
  have q4 := Sb_nonneg (m := m) hK0 hμ0 (by norm_num : (0 : ℝ) ≤ 10321920) 4
  have q6 := Sb_nonneg (m := m) hK0 hμ0 (by norm_num : (0 : ℝ) ≤ 1961990553600) 6
  have hM8 : M8 m K μ ≤ 105 * (S2 * y ^ 16) ^ 4 + 490 * (S2 * y ^ 16) ^ 2 * (S4 * y ^ 36) +
      63 * (S4 * y ^ 36) ^ 2 + 56 * (S2 * y ^ 16) * (S6 * y ^ 56) + S8 * y ^ 76 := by
    unfold M8; gcongr
  have hMμ : (m : ℝ) * μ ≤ μb * y ^ 6 := by
    calc (m : ℝ) * μ ≤ (m : ℝ) * (μb * y ^ 10) := by gcongr
      _ = μb * y ^ 6 * ((m : ℝ) * y ^ 4) := by ring
      _ = μb * y ^ 6 := by rw [hm, mul_one]
  have hMμ0 : 0 ≤ (m : ℝ) * μ := by positivity
  have hy' : 0 ≤ y := hy0.le
  have hp : ∀ k : ℕ, y ^ k ≤ (1 / 127) ^ k := fun k => pow_le_pow_left₀ hy' hy k
  have hNe : N = 1 / y ^ 2 := by field_simp; linarith
  have hc1 : 0 ≤ (1 + ε) ^ 3 := by positivity
  have hc2 : 0 ≤ (1 + 1 / ε) ^ 3 := by positivity
  -- the bracket
  have key : (1 + ε) ^ 3 * ((m : ℝ) * μ) ^ 4 +
      (1 + 1 / ε) ^ 3 * (M8 m K μ / (2 * (T * y ^ 32)) + T * y ^ 32 / 2) ≤
      y ^ 24 * ((1 + ε) ^ 3 * μb ^ 4 + (1 + 1 / ε) ^ 3 *
        ((105 * S2 ^ 4 * y ^ 8 + 490 * S2 ^ 2 * S4 * y ^ 12 + (63 * S4 ^ 2 + 56 * S2 * S6) * y ^ 16 +
          S8 * y ^ 20) / (2 * T) + T * y ^ 8 / 2)) := by
    have a1 : ((m : ℝ) * μ) ^ 4 ≤ (μb * y ^ 6) ^ 4 := pow_le_pow_left₀ hMμ0 hMμ 4
    have a2 : M8 m K μ / (2 * (T * y ^ 32)) ≤ (105 * (S2 * y ^ 16) ^ 4 +
        490 * (S2 * y ^ 16) ^ 2 * (S4 * y ^ 36) + 63 * (S4 * y ^ 36) ^ 2 +
        56 * (S2 * y ^ 16) * (S6 * y ^ 56) + S8 * y ^ 76) / (2 * (T * y ^ 32)) := by
      gcongr
    calc _ ≤ (1 + ε) ^ 3 * (μb * y ^ 6) ^ 4 + (1 + 1 / ε) ^ 3 * ((105 * (S2 * y ^ 16) ^ 4 +
          490 * (S2 * y ^ 16) ^ 2 * (S4 * y ^ 36) + 63 * (S4 * y ^ 36) ^ 2 +
          56 * (S2 * y ^ 16) * (S6 * y ^ 56) + S8 * y ^ 76) / (2 * (T * y ^ 32)) +
          T * y ^ 32 / 2) := by gcongr
      _ = _ := by field_simp; ring
  have key2 : (1 + ε) ^ 3 * μb ^ 4 + (1 + 1 / ε) ^ 3 *
        ((105 * S2 ^ 4 * y ^ 8 + 490 * S2 ^ 2 * S4 * y ^ 12 + (63 * S4 ^ 2 + 56 * S2 * S6) * y ^ 16 +
          S8 * y ^ 20) / (2 * T) + T * y ^ 8 / 2) ≤ Bb ^ 8 := by
    refine le_trans ?_ hnum
    have := hp 8; have := hp 12; have := hp 16; have := hp 20
    gcongr
  rw [hNe]
  calc (1 / y ^ 2) ^ 4 * ((1 + ε) ^ 3 * ((m : ℝ) * μ) ^ 4 +
        (1 + 1 / ε) ^ 3 * (M8 m K μ / (2 * (T * y ^ 32)) + T * y ^ 32 / 2))
      ≤ (1 / y ^ 2) ^ 4 * (y ^ 24 * Bb ^ 8) := by
        gcongr; exact key.trans (mul_le_mul_of_nonneg_left key2 (by positivity))
    _ = (Bb / (1 / y ^ 2)) ^ 8 := by field_simp


theorem finalW {m : ℕ} {N y K μ Kb μb ε Bb : ℝ} (hy0 : 0 < y) (hy : y ≤ 1 / 127)
    (hN : N * y ^ 2 = 1) (hm : (m : ℝ) * y ^ 4 = 1)
    (hK0 : 0 ≤ K) (hK : K ≤ Kb * y ^ 6) (hμ0 : 0 ≤ μ) (hμ : μ ≤ μb * y ^ 6)
    (hε : 0 < ε) (hBb : 0 ≤ Bb)
    (hnum : (1 + ε) ^ 7 * μb ^ 8 + (1 + 1 / ε) ^ 7 *
      (105 * sk Kb μb 384 2 ^ 4 * (1 / 127) ^ 16 +
        490 * sk Kb μb 384 2 ^ 2 * sk Kb μb 10321920 4 * (1 / 127) ^ 20 +
        (63 * sk Kb μb 10321920 4 ^ 2 + 56 * sk Kb μb 384 2 * sk Kb μb 1961990553600 6) *
          (1 / 127) ^ 24 + sk Kb μb 1371195958099968000 8 * (1 / 127) ^ 28) ≤ Bb ^ 8) :
    (1 + ε) ^ 7 * ((m : ℝ) * μ) ^ 8 + (1 + 1 / ε) ^ 7 * M8 m K μ ≤ (Bb / N) ^ 8 := by
  have hKb : 0 ≤ Kb := by
    by_contra h; push Not at h; have := mul_neg_of_neg_of_pos h (pow_pos hy0 6); linarith
  have hμb : 0 ≤ μb := by
    by_contra h; push Not at h; have := mul_neg_of_neg_of_pos h (pow_pos hy0 6); linarith
  have s2 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 384) 2 (e := 8) (by norm_num)
  have s4 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 10321920) 4 (e := 20)
    (by norm_num)
  have s6 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 1961990553600) 6 (e := 32)
    (by norm_num)
  have s8 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 1371195958099968000) 8
    (e := 44) (by norm_num)
  set S2 := sk Kb μb 384 2
  set S4 := sk Kb μb 10321920 4
  set S6 := sk Kb μb 1961990553600 6
  set S8 := sk Kb μb 1371195958099968000 8
  have hS2 : 0 ≤ S2 := by unfold S2 sk; positivity
  have hS4 : 0 ≤ S4 := by unfold S4 sk; positivity
  have hS6 : 0 ≤ S6 := by unfold S6 sk; positivity
  have hS8 : 0 ≤ S8 := by unfold S8 sk; positivity
  have q2 := Sb_nonneg (m := m) hK0 hμ0 (by norm_num : (0 : ℝ) ≤ 384) 2
  have q4 := Sb_nonneg (m := m) hK0 hμ0 (by norm_num : (0 : ℝ) ≤ 10321920) 4
  have q6 := Sb_nonneg (m := m) hK0 hμ0 (by norm_num : (0 : ℝ) ≤ 1961990553600) 6
  have hM8 : M8 m K μ ≤ 105 * (S2 * y ^ 8) ^ 4 + 490 * (S2 * y ^ 8) ^ 2 * (S4 * y ^ 20) +
      63 * (S4 * y ^ 20) ^ 2 + 56 * (S2 * y ^ 8) * (S6 * y ^ 32) + S8 * y ^ 44 := by
    unfold M8; gcongr
  have hMμ : (m : ℝ) * μ ≤ μb * y ^ 2 := by
    calc (m : ℝ) * μ ≤ (m : ℝ) * (μb * y ^ 6) := by gcongr
      _ = μb * y ^ 2 * ((m : ℝ) * y ^ 4) := by ring
      _ = μb * y ^ 2 := by rw [hm, mul_one]
  have hMμ0 : 0 ≤ (m : ℝ) * μ := by positivity
  have hy' : 0 ≤ y := hy0.le
  have hp : ∀ k : ℕ, y ^ k ≤ (1 / 127) ^ k := fun k => pow_le_pow_left₀ hy' hy k
  have hNe : N = 1 / y ^ 2 := by field_simp; linarith
  have a1 : ((m : ℝ) * μ) ^ 8 ≤ (μb * y ^ 2) ^ 8 := pow_le_pow_left₀ hMμ0 hMμ 8
  have key : (1 + ε) ^ 7 * ((m : ℝ) * μ) ^ 8 + (1 + 1 / ε) ^ 7 * M8 m K μ ≤
      y ^ 16 * ((1 + ε) ^ 7 * μb ^ 8 + (1 + 1 / ε) ^ 7 *
        (105 * S2 ^ 4 * y ^ 16 + 490 * S2 ^ 2 * S4 * y ^ 20 + (63 * S4 ^ 2 + 56 * S2 * S6) * y ^ 24 +
          S8 * y ^ 28)) := by
    calc _ ≤ (1 + ε) ^ 7 * (μb * y ^ 2) ^ 8 + (1 + 1 / ε) ^ 7 * (105 * (S2 * y ^ 8) ^ 4 +
          490 * (S2 * y ^ 8) ^ 2 * (S4 * y ^ 20) + 63 * (S4 * y ^ 20) ^ 2 +
          56 * (S2 * y ^ 8) * (S6 * y ^ 32) + S8 * y ^ 44) := by gcongr
      _ = _ := by ring
  have key2 : (1 + ε) ^ 7 * μb ^ 8 + (1 + 1 / ε) ^ 7 *
        (105 * S2 ^ 4 * y ^ 16 + 490 * S2 ^ 2 * S4 * y ^ 20 + (63 * S4 ^ 2 + 56 * S2 * S6) * y ^ 24 +
          S8 * y ^ 28) ≤ Bb ^ 8 := by
    refine le_trans ?_ hnum
    have := hp 16; have := hp 20; have := hp 24; have := hp 28
    gcongr
  rw [hNe]
  calc _ ≤ y ^ 16 * Bb ^ 8 := key.trans (mul_le_mul_of_nonneg_left key2 (by positivity))
    _ = (Bb / (1 / y ^ 2)) ^ 8 := by field_simp


end BstLean.Part190.RA

namespace BstLean.Part190
open BstLean.Part188
open BstLean.Part187

open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part170 (tA windowW mkR BiasMomF BiasMomW)
open BstLean.Part186 BstLean.Part186.RA

variable {n : ℕ}

lemma qB_nonneg16 (hn : 16200 ≤ n) : 0 ≤ qB n := by
  unfold qB
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : √(54 / 100 : ℝ) ≤ 734847 / 1000000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 : √(55 / 100 / (n : ℝ)) ≤ 5827 / 1000000 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by linarith)]; nlinarith
  have h3 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) := by positivity
  have h4 : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) ≤ 77 / 100 := by linarith
  nlinarith


lemma node_bulk16 (hn : 16200 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
    (hg : g < Js n) : nodeS (mkR wr θ) g ^ 2 ≤ 1 := by
  obtain ⟨hτ, hθ0, hθ1⟩ := hw
  obtain ⟨hLH, hb, -⟩ := bulk_of_window (by omega) (mkR wr θ) hτ hθ0 hθ1
  have hq := qB_nonneg16 hn
  have hJ : (0 : ℝ) < Js n := by exact_mod_cast (show 0 < Js n by unfold Js; omega)
  have hD : 0 ≤ nodeD (mkR wr θ) := div_nonneg (by linarith) hJ.le
  have hg' : (g : ℝ) + 1 / 2 ≤ Js n := by
    have : (g : ℝ) + 1 ≤ Js n := by exact_mod_cast hg
    linarith
  have h1 : nodeL (mkR wr θ) ≤ nodeS (mkR wr θ) g := by
    unfold nodeS; have : 0 ≤ ((g : ℝ) + 1 / 2) * nodeD (mkR wr θ) := by positivity
    linarith
  have h2 : nodeS (mkR wr θ) g ≤ nodeH (mkR wr θ) := by
    unfold nodeS
    have e : nodeH (mkR wr θ) = nodeL (mkR wr θ) + (Js n : ℝ) * nodeD (mkR wr θ) := by
      unfold nodeD; field_simp; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hg' hD
    linarith
  have := hb _ h1 h2
  linarith

lemma cF_le {A0 A1 A2 a0 a1 a2 y : ℝ} (hy : 0 < y) (h0 : 0 ≤ A0) (h1 : 0 ≤ A1) (h2 : 0 ≤ A2)
    (k0 : A0 ≤ a0 * y ^ 5) (k1 : A1 ≤ a1 * y ^ 5) (k2 : A2 ≤ a2 * y ^ 5) :
    cF0 A0 A1 A2 + cF1 A0 A1 A2 + cF2 A0 A1 A2 ≤
      (cF0 a0 a1 a2 + cF1 a0 a1 a2 + cF2 a0 a1 a2) * y ^ 10 ∧
    cF0 A0 A1 A2 + 2 * cF1 A0 A1 A2 + 8 * cF2 A0 A1 A2 ≤
      (cF0 a0 a1 a2 + 2 * cF1 a0 a1 a2 + 8 * cF2 a0 a1 a2) * y ^ 10 := by
  have hy5 : 0 < y ^ 5 := by positivity
  have g0 : 0 ≤ a0 * y ^ 5 := h0.trans k0
  have g1 : 0 ≤ a1 * y ^ 5 := h1.trans k1
  have g2 : 0 ≤ a2 * y ^ 5 := h2.trans k2
  have ha : (0 : ℝ) < aa := by unfold aa; norm_num
  have c0 : cF0 A0 A1 A2 ≤ cF0 (a0 * y ^ 5) (a1 * y ^ 5) (a2 * y ^ 5) := by
    unfold cF0; gcongr
  have c1 : cF1 A0 A1 A2 ≤ cF1 (a0 * y ^ 5) (a1 * y ^ 5) (a2 * y ^ 5) := by
    unfold cF1; gcongr
  have c2 : cF2 A0 A1 A2 ≤ cF2 (a0 * y ^ 5) (a1 * y ^ 5) (a2 * y ^ 5) := by
    unfold cF2; gcongr
  have e0 : cF0 (a0 * y ^ 5) (a1 * y ^ 5) (a2 * y ^ 5) = cF0 a0 a1 a2 * y ^ 10 := by
    unfold cF0; ring
  have e1 : cF1 (a0 * y ^ 5) (a1 * y ^ 5) (a2 * y ^ 5) = cF1 a0 a1 a2 * y ^ 10 := by
    unfold cF1; field_simp
  have e2 : cF2 (a0 * y ^ 5) (a1 * y ^ 5) (a2 * y ^ 5) = cF2 a0 a1 a2 * y ^ 10 := by
    unfold cF2; ring
  constructor <;> nlinarith

lemma cW_le {A0 A1 A2 a0 a1 a2 y : ℝ} (_hy : 0 < y) (_h1 : 0 ≤ A1)
    (k0 : A0 ≤ a0 * y ^ 6) (k1 : A1 ≤ a1 * y ^ 6) (k2 : A2 ≤ a2 * y ^ 6) :
    cW0 A0 A1 A2 + cW1 A0 A1 A2 + 0 ≤ (cW0 a0 a1 a2 + cW1 a0 a1 a2) * y ^ 6 ∧
    cW0 A0 A1 A2 + 2 * cW1 A0 A1 A2 + 8 * 0 ≤ (cW0 a0 a1 a2 + 2 * cW1 a0 a1 a2) * y ^ 6 := by
  have ha : (0 : ℝ) < aa := by unfold aa; norm_num
  have c0 : cW0 A0 A1 A2 ≤ cW0 a0 a1 a2 * y ^ 6 := by
    unfold cW0
    have : A1 * aa / 2 ≤ a1 * y ^ 6 * aa / 2 := by gcongr
    nlinarith
  have c1 : cW1 A0 A1 A2 ≤ cW1 a0 a1 a2 * y ^ 6 := by
    unfold cW1
    have : A1 / (2 * aa) ≤ a1 * y ^ 6 / (2 * aa) := by gcongr
    have e : (a1 / (2 * aa) + a2) * y ^ 6 = a1 * y ^ 6 / (2 * aa) + a2 * y ^ 6 := by ring
    nlinarith
  constructor <;> nlinarith


theorem BiasRA_gen16200 (hn : 16200 ≤ n) {Pm : ℝ} (hP0 : 0 ≤ Pm) (hP : Pm ≤ 82 * PmN n)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    (hGb : Gb ⊆ StatEv n (SminN n) (SmaxN n) (DmN n) (DmN n) (VmN n) Pm) :
    BiasMomF (O1n n) Gb (194 / n) ∧ BiasMomW (O1n n) Gb (148 / n) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hbulk : ∀ wr : WRet n, windowW wr → ∀ (θ : AHid n) (g : ℕ), g < Js n →
      nodeS (mkR wr θ) g ^ 2 ≤ 1 := fun wr hw θ g hg => node_bulk16 hn hw θ hg
  have hSm : 0 < SminN n := by unfold SminN; positivity
  have hO : 0 ≤ O1n n := O1n_nonneg n
  obtain ⟨hr, hr2, -⟩ := BstLean.Part190.RA.r_facts16 hn
  set r := √(n : ℝ) with hrd
  have hr0 : 0 < r := by linarith
  set y := 1 / r with hyd
  have hy0 : 0 < y := by positivity
  have hy : y ≤ 1 / 127 := by rw [hyd]; gcongr
  have hNy : (n : ℝ) * y ^ 2 = 1 := by rw [hyd, ← hr2]; field_simp
  have hmy : ((mA n : ℕ) : ℝ) * y ^ 4 = 1 := by
    have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
    rw [hmA, hyd, ← hr2]; field_simp
  have hy5 : ∀ a : ℝ, a / r ^ 5 = a * y ^ 5 := fun a => by rw [hyd]; field_simp
  have hy6 : ∀ a : ℝ, a / r ^ 6 = a * y ^ 6 := fun a => by rw [hyd]; field_simp
  obtain ⟨f0, f0', f1, f1', f2, f2'⟩ := BstLean.Part190.RA.coefF hn hP0 hP
  obtain ⟨w0, w0', w1, w1', w2, w2'⟩ := BstLean.Part190.RA.coefW hn hP0 hP
  rw [hy5] at f0' f1' f2'
  rw [hy6] at w0' w1' w2'
  constructor
  · obtain ⟨hK, hμ⟩ := cF_le hy0 f0 f1 f2 f0' f1' f2'
    refine biasMomF_RA_of_stat hn1 hbulk hO hSm hGb f0 f1 f2 rfl rfl rfl
      (ε := 1 / 20) (t := 10 ^ 26 * y ^ 32) (by norm_num) (by positivity) ?_
    refine BstLean.Part190.RA.finalF hy0 hy hNy hmy (by unfold cF0 cF1 cF2 aa; positivity) hK
      (by unfold cF0 cF1 cF2 aa; positivity) hμ (by norm_num) (by norm_num) (by norm_num) ?_
    unfold sk cF0 cF1 cF2 aa
    norm_num
  · obtain ⟨hK, hμ⟩ := cW_le hy0 w1 w0' w1' w2'
    refine biasMomW_RA_of_stat hn1 hbulk hO hSm hGb w0 w1 w2 rfl rfl (ε := 1 / 50)
      (by norm_num) ?_
    refine BstLean.Part190.RA.finalW hy0 hy hNy hmy (by unfold cW0 cW1 aa; positivity) hK
      (by unfold cW0 cW1 aa; positivity) hμ (by norm_num) (by norm_num) ?_
    unfold sk cW0 cW1 aa
    norm_num


theorem BiasRA82_16200 : ∀ {n : ℕ}, 16200 ≤ n → ∀ {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)},
    Gb ⊆ StatEv n (SminN n) (SmaxN n) (DmN n) (DmN n) (VmN n) (82 * PmN n) →
    BiasMomF (O1n n) Gb (194 / n) ∧ BiasMomW (O1n n) Gb (148 / n) :=
  fun hn _ hGb => BiasRA_gen16200 hn (by unfold PmN; positivity) le_rfl hGb

end BstLean.Part190

#print axioms BstLean.Part190.BiasRA_gen16200
#print axioms BstLean.Part190.BiasRA82_16200
