import BstLean.Part188All
import BstLean.Part190MEnd
import BstLean.Part190CmbK16
import BstLean.Part186Uncond



namespace BstLean.Part190
open BstLean.Part188
open BstLean.Part187

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_16200 {n : ℕ} (hn : 16200 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  by_cases h1 : n < 16384
  · exact BstLean.Part190.classifier_paper_uncond_16200HB ⟨BstLean.Part180.hq_proved, FREE16200K_proved⟩
      BstLean.Part184.EnB_proved BstLean.Part184.EnFB_proved BstLean.Part190.M.BiasRA82_proved hn (by omega) t
  · exact BstLean.Part186.classifier_paper_uncond_16384 (by omega) t

theorem uncond_16200_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_16200 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_16200_eq_186 {n : ℕ} (hn : 16384 ≤ n) (t : ℝ) :
    classifier_paper_uncond_16200 (by omega) t = BstLean.Part186.classifier_paper_uncond_16384 hn t :=
  rfl

end BstLean.Part190

#print axioms BstLean.Part190.classifier_paper_uncond_16200
#print axioms BstLean.Part190.uncond_16200_eq_172
#print axioms BstLean.Part190.uncond_16200_eq_186
