import BstLean.Part278Row
import BstLean.Part281SharpSource

namespace BstLean.Part281
open Real
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part278
open BstLean.Part272 (statedDesign)

theorem qB_nonneg_m2 {n : ℕ} (hn : 11883 ≤ n) : 0 ≤ BstLean.Part169.qB n := by
  unfold BstLean.Part169.qB
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have h2 : √(55 / 100 / (n : ℝ)) ≤ 7 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by linarith)]
    nlinarith
  have h3 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) := by positivity
  have h4 : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) ≤ 777 / 1000 := by
    linarith
  nlinarith

theorem odd_root_ops_m2 {n : ℕ} (hn : 11883 ≤ n) (ho : Odd n) (t : ℝ) (c : Ret n)
    (h1 : OpB (A1 c) (O1n n)) (h2 : OpB (A2 c) (O2n n)) (hτ : 0 < tauR c)
    (hθ0 : 46/100 ≤ BstLean.Part150.thetaC c.1.2 (tauR c))
    (hθ1 : BstLean.Part150.thetaC c.1.2 (tauR c) ≤ 55/100)
    {χ : ℝ} (he : 0 < eR c) (hc : normSq c.2.1.2 ≤ 2/(n : ℝ)*eR c*n*χ)
    (hχ0 : 0 ≤ χ) (hχ : χ ≤ n) :
    |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤ 1/10^20 := by
  obtain ⟨hLH,hs,-⟩ := bulk_of_window (by omega) c hτ hθ0 hθ1
  have hq := qB_nonneg_m2 hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  refine odd_root_lt (by omega) ho (BstLean.Part278.Jz_pos (by omega)) t c
    (OpB_mono h2 O2n_nonneg (O2n_le (by omega))) (fun g hg => ?_) he hc hχ0 hχ
  obtain ⟨hL,hH⟩ := nodeS_mem (by omega) c hLH g hg
  have hs1 : (nodeS c g)^2 ≤ 1 := by have := hs _ hL hH; linarith
  have hO1 := O1n_sq_le (n := n) (by omega)
  have hF := frob_le c h1
  calc ∑ i, aw c (nodeS c g) i ^ 2 ≤ ∑ i, 2 * ∑ j, A1 c i j ^ 2 :=
        Finset.sum_le_sum fun i _ => aw_sq_le (by omega) c _ hs1 i
    _ = 2 * ∑ i, ∑ j, A1 c i j ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * (n * O1n n ^ 2) := by linarith
    _ ≤ 2 * (n * (8 * n)) := by
        have := mul_le_mul_of_nonneg_left hO1 (by linarith : (0 : ℝ) ≤ n)
        linarith
    _ ≤ 16 * (n : ℝ)^3 := by
        have : (n : ℝ)^2 ≤ (n : ℝ)^3 := pow_le_pow_right₀ hnR (by norm_num)
        nlinarith

theorem odd_root_paid {n : ℕ} (hn : 11883 ≤ n) (ho : Odd n) (t : ℝ) (c : Ret n)
    (hc : c ∈ BstLean.Part262.paidSourceBase n)
    (hw : BstLean.Part161.WINDOW (paperDesignP n) c) (he : 0 < eR c) :
    |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤ 1/10^20 := by
  have hp : c ∈ BstLean.Part262.passEvent n := hc.1.1.1.1.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlo : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hτ : 0 < tauR c := hw.2.1
  have hS : 0 < normSq c.1.2 + (n : ℝ)*tauR c^2 := by
    have := normSq_nonneg c.1.2; positivity
  have hθ : BstLean.Part150.thetaC c.1.2 (tauR c) =
      (n : ℝ)*tauR c^2/(normSq c.1.2+(n : ℝ)*tauR c^2) := by
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    rw [sq_sqrt hS.le]
  have hθ0 : 46/100 ≤ BstLean.Part150.thetaC c.1.2 (tauR c) := by
    rw [hθ,le_div_iff₀ hS]; exact hw.2.2.1
  have hw2 : (n : ℝ)*tauR c^2 ≤ 54/100*(normSq c.1.2+(n : ℝ)*tauR c^2) :=
    hw.2.2.2
  have hθ1 : BstLean.Part150.thetaC c.1.2 (tauR c) ≤ 55/100 := by
    rw [hθ,div_le_iff₀ hS]; nlinarith [hw2]
  have hO1 : OpB (A1 c) (O1n n) := opB_of_opN _ (hp.1.1.2 hτ)
  have hO2 : OpB (A2 c) (O2n n) := opB_of_opN _ hp.1.2
  have hb : normSq c.2.1.2 ≤ 2/(mA n : ℝ)*normSq (bR c)*BstLean.Part164.chiUp n := hp.2
  have hm : (mA n : ℝ) = (n : ℝ)^2 := by unfold mA; push_cast; ring
  rw [hm] at hb
  have hA : normSq c.2.1.2 ≤ 2/(n : ℝ)*eR c*n*(BstLean.Part164.chiUp n/n) := by
    refine hb.trans (le_of_eq ?_)
    unfold eR
    field_simp
  have hχ0 : 0 ≤ BstLean.Part164.chiUp n/n := by unfold BstLean.Part164.chiUp; positivity
  have hχ : BstLean.Part164.chiUp n/n ≤ n := by
    rw [div_le_iff₀ hnR]
    unfold BstLean.Part164.chiUp
    have hs : √((n : ℝ)*12) ≤ (n : ℝ)*12 := by
      calc √((n : ℝ)*12) ≤ √(((n : ℝ)*12)^2) := sqrt_le_sqrt (by nlinarith)
        _ = (n : ℝ)*12 := sqrt_sq (by linarith)
    nlinarith
  exact odd_root_ops_m2 hn ho t c hO1 hO2 hτ hθ0 hθ1 he hA hχ0 hχ

theorem classifier_from_sharp_row {n : ℕ} (R : BstLean.Part259.RowInputs n)
    (hb : R.baseEvent ⊆ BstLean.Part262.paidSourceBase n) (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (statedDesign n) t BstLean.Part156.aL (10^12) x.1 x.2)} := by
  rcases Nat.even_or_odd n with hE | hO
  · rw [BstLean.Part272.statedDesign_even (by have := R.dimension; omega) hE]
    exact BstLean.Part259.classifier_from_row R t
  · apply classifier_from_row_st R t
    intro c hc
    obtain ⟨P⟩ := R.root t c hc
    exact odd_root_paid R.dimension hO t c (hb hc.2.1) P.window P.passes.he

end BstLean.Part281
