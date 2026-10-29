import BstLean.Part56Low_Heat
import BstLean.Part53Floor_Correction

namespace BstLean.Part56.LowScale

open BstLean.Part41 BstLean.Part53 BstLean.Part53.FloorHeat

variable {n : ℕ}

noncomputable def scaleT (s : ℝ) (A : Tens n) : Tens n := fun c w => s ^ c * A c w

lemma trace_scaled (i c : ℕ) (s : ℝ) (A : Tens n) (w : Fin c → Fin n) :
    traceFamily i (scaleT s A) c w = s ^ (c + 2 * i) * traceFamily i A c w := by
  classical
  unfold traceFamily trL scaleT
  rw [Finset.mul_sum]

lemma heatWeight_scaled (c i : ℕ) (s v : ℝ) :
    heatWeight c i (s ^ 2 * v) * s ^ c = heatWeight c i v * s ^ (c + 2 * i) := by
  unfold heatWeight
  rw [show s ^ 2 * v / 2 = s ^ 2 * (v / 2) by ring, mul_pow, pow_add, pow_mul]
  ring

lemma heat_scaled (k c : ℕ) (s v : ℝ) (A : Tens n) :
    heatA k v (scaleT s A) c = fun w => s ^ c * heatA k (s ^ 2 * v) A c w := by
  classical
  funext w
  change (∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
      heatWeight c i v * traceFamily i (scaleT s A) c w) =
    s ^ c * ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
      heatWeight c i (s ^ 2 * v) * traceFamily i A c w
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [trace_scaled]
  have hh := heatWeight_scaled c i s v
  nlinarith [congrArg (fun z : ℝ => z * traceFamily i A c w) hh]

lemma frob_scaled (c : ℕ) (s : ℝ) (A : Tens n) :
    frob (scaleT s A c) = s ^ (2 * c) * frob (A c) := by
  classical
  unfold frob scaleT
  simp_rw [mul_pow, ← pow_mul, mul_comm c 2]
  rw [Finset.mul_sum]

lemma heated_frob_scaled (k c : ℕ) (s v : ℝ) (A : Tens n) :
    frob (heatA k v (scaleT s A) c) = s ^ (2 * c) * frob (heatA k (s ^ 2 * v) A c) := by
  rw [heat_scaled]
  exact frob_scaled c s (heatA k (s ^ 2 * v) A)

lemma normalized_frob (d k j : ℕ) (hn : 1 ≤ n) (hj0 : 1 ≤ j) (hjk : j ≤ k)
    (f0 : ℝ) (T : Tens n) :
    frob (scaleT (sg n d) (TF k f0 T) j) = frob (T j) / BstLean.Part36.DD n d ^ j := by
  rw [frob_scaled, FloorCorrection.sg_pow_even hn]
  have hTF : TF k f0 T j = T j := by
    funext w
    simp only [TF, show j ≠ 0 by omega, hjk, ite_false, ite_true]
  rw [hTF]
  ring


end BstLean.Part56.LowScale
