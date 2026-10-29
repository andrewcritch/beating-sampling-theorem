import BstLean.Part107P5c

/-!
# Part 107 (P5): `E κ(x·x′) ≤ v̄` and `n · E(κ(x·x′) − c)² ≤ J_*`
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105

theorem p5_part2 (hT : TwoPoint107) (h3 : P3_107) (h4 : P4_107) (hS : SphStat107)
    (hK : KapFacts107) (n dA : ℕ) (σ : ℝ) (hn : 3 ≤ n) (hd : dA = 3 ∨ dA = 4) (hσ : σ ≠ 0) :
    (n : ℝ) * twoPt (2 * n) n (2 * dA) σ (fun a => (kap dA a - cStar n dA) ^ 2) ≤ Jstar dA n := by
  obtain ⟨hder, hrange, -, hlip, hck⟩ := hK dA hd
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hκm := measurable_kap hder
  have hκB := kap_clamp_BM hder hrange
  have hκint := kap_aR_integrable hder hrange n
  obtain ⟨c, hc⟩ : ∃ c, c = cStar n dA := ⟨_, rfl⟩
  rw [← hc]
  have hcdef : c = ∫ p, kap dA (aR (1 / (2 * (dA : ℝ) + 1)) p) ∂gg n := hc
  have hc0 : 0 ≤ c ∧ c ≤ (dA : ℝ) + 1 := by
    rw [hcdef]
    constructor
    · exact integral_nonneg fun p => (hrange _ (abs_aR_le _ p)).1
    · calc ∫ p, kap dA (aR (1 / (2 * (dA : ℝ) + 1)) p) ∂gg n
          ≤ ∫ _p, ((dA : ℝ) + 1) ∂gg n :=
            integral_mono (hκint _) (integrable_const _) fun p => (hrange _ (abs_aR_le _ p)).2
        _ = (dA : ℝ) + 1 := by simp
  have hΨK : ∀ a : ℝ, |a| ≤ 1 → (kap dA a - c) ^ 2 ≤ ((dA : ℝ) + 1) ^ 2 := fun a ha => by
    obtain ⟨h0, h1⟩ := hrange a ha
    exact sq_le_sq' (by linarith [hc0.2]) (by linarith [hc0.1])
  have hΨB : BM (clampF (fun a => (kap dA a - c) ^ 2)) :=
    clampF_BM ((hκm.sub_const c).pow_const 2) (((dA : ℝ) + 1) ^ 2) fun a ha => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact hΨK a ha
  obtain ⟨hrp1, hrp2, hrp0⟩ := rPlus_facts hd
  have hcK := cKap_pos hd
  have hL := Lsq_nonneg hd hn
  have hr00 : (0 : ℝ) ≤ 1 / (2 * (dA : ℝ) + 1) := by positivity
  have hLip0 : 0 ≤ LipK dA := by unfold LipK; positivity
  obtain ⟨c3, hc3⟩ : ∃ c3 : ℝ, c3 = cKap dA * (2 + 2 * rPlus dA) / ((n : ℝ) - 2) := ⟨_, rfl⟩
  have hc30 : 0 ≤ c3 := by
    rw [hc3]; exact div_nonneg (mul_nonneg hcK.le (by linarith)) (by linarith)
  have hpt : ∀ t : ℝ, |t| ≤ 1 →
      Mr n (clampF (fun a => (kap dA a - c) ^ 2)) (rW (2 * dA) t) ≤
        (c3 + ((dA : ℝ) + 1) ^ 2 * (if 1 / 10 < |t| then (1 : ℝ) else 0)) +
          Lsq dA n * (rW (2 * dA) t - 1 / (2 * (dA : ℝ) + 1)) ^ 2 := by
    intro t ht
    rw [Mr_clamp]
    have hLt := mul_nonneg hL (sq_nonneg (rW (2 * dA) t - 1 / (2 * (dA : ℝ) + 1)))
    have hrabs := abs_rW_le (2 * dA) ht
    have hΨint : Integrable (fun p => (kap dA (aR (n := n) (rW (2 * dA) t) p) - c) ^ 2) (gg n) :=
      ((BM_aR hΨB (rW (2 * dA) t) (n := n)).integrable (gg n)).congr
        (Filter.Eventually.of_forall fun p => clampF_eq _ (abs_aR_le _ p))
    by_cases h10 : 1 / 10 < |t|
    · rw [if_pos h10]
      have : Mr n (fun a => (kap dA a - c) ^ 2) (rW (2 * dA) t) ≤ ((dA : ℝ) + 1) ^ 2 := by
        calc Mr n (fun a => (kap dA a - c) ^ 2) (rW (2 * dA) t)
            ≤ ∫ _p, ((dA : ℝ) + 1) ^ 2 ∂gg n :=
              integral_mono hΨint (integrable_const _) fun p => hΨK _ (abs_aR_le _ p)
          _ = ((dA : ℝ) + 1) ^ 2 := by simp
      linarith
    · rw [if_neg h10]
      have h10 := not_lt.mp h10
      have hr0 : 0 ≤ rW (2 * dA) t := rW_nonneg hd (abs_le.mp ht).1
      have hr1 : rW (2 * dA) t ≤ rPlus dA := rW_le_rPlus dA h10
      generalize rW (2 * dA) t = r at hr0 hr1 hrabs hLt hΨint ⊢
      have hdec := var_decomp (gg n) (BM_aR hκB r (n := n)) c
      simp_rw [clampF_eq (kap dA) (abs_aR_le _ _)] at hdec
      have hv := h3 n r (cKap dA) (kap dA) (kap' dA) hn hrabs hder (continuous_kap' dA) hck
      have hm := h4 n r (1 / (2 * (dA : ℝ) + 1)) (rPlus dA) (LipK dA) (kap dA) hn hr0 hr1 hr00
        hrp1 hrp2 hLip0 hκm hlip
      rw [← hcdef] at hm
      have hm' : (∫ p, kap dA (aR r p) ∂gg n - c) ^ 2 ≤
          Lsq dA n * (r - 1 / (2 * (dA : ℝ) + 1)) ^ 2 := hm
      have hv' : cKap dA * (2 + 2 * |r|) / ((n : ℝ) - 2) ≤ c3 := by
        rw [hc3, abs_of_nonneg hr0]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hcK.le)
          (by linarith)
      have hM : Mr n (fun a => (kap dA a - c) ^ 2) r =
          ∫ p, (kap dA (aR r p) - c) ^ 2 ∂gg n := rfl
      rw [hM, hdec]
      linarith
  rw [← twoPt_clamp]
  have hf1 := rW_sq_integrable hN (2 * dA) (1 / (2 * (dA : ℝ) + 1))
  have hf2 : Integrable (fun z : (Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ) =>
      (if 1 / 10 < |dot z.1 z.2| then (1 : ℝ) else 0))
      ((uniformSphere (2 * n)).prod (uniformSphere (2 * n))) := by
    refine int_of_unit_bdd hN (Measurable.ite (measurableSet_lt measurable_const
      (continuous_abs.measurable.comp measurable_dot2)) measurable_const measurable_const) 1
      fun z _ _ => ?_
    split_ifs <;> norm_num
  have hf3 := integral_affine ((uniformSphere (2 * n)).prod (uniformSphere (2 * n))) hf2 c3
    (((dA : ℝ) + 1) ^ 2)
  have hle := twoPt_le hT hN hσ hΨB
    (fun z => (c3 + ((dA : ℝ) + 1) ^ 2 * (if 1 / 10 < |dot z.1 z.2| then (1 : ℝ) else 0)) +
      Lsq dA n * (rW (2 * dA) (dot z.1 z.2) - 1 / (2 * (dA : ℝ) + 1)) ^ 2)
    (((integrable_const _).add (hf2.const_mul _)).add (hf1.const_mul _))
    (fun z h1 h2 => hpt _ (abs_dot_le_one _ _ h1 h2))
  have hsplit : ∫ z : (Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ),
      ((c3 + ((dA : ℝ) + 1) ^ 2 * (if 1 / 10 < |dot z.1 z.2| then (1 : ℝ) else 0)) +
        Lsq dA n * (rW (2 * dA) (dot z.1 z.2) - 1 / (2 * (dA : ℝ) + 1)) ^ 2)
      ∂(uniformSphere (2 * n)).prod (uniformSphere (2 * n)) =
      ∫ z : (Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ),
        (c3 + ((dA : ℝ) + 1) ^ 2 * (if 1 / 10 < |dot z.1 z.2| then (1 : ℝ) else 0))
        ∂(uniformSphere (2 * n)).prod (uniformSphere (2 * n)) +
      Lsq dA n * ∫ z : (Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ),
        (rW (2 * dA) (dot z.1 z.2) - 1 / (2 * (dA : ℝ) + 1)) ^ 2
        ∂(uniformSphere (2 * n)).prod (uniformSphere (2 * n)) := by
    rw [← integral_const_mul]
    exact integral_add ((integrable_const _).add (hf2.const_mul _)) (hf1.const_mul _)
  rw [hsplit, hf3] at hle
  obtain ⟨-, hS2, hS3⟩ := hS (2 * n) dA hN hd
  have hS2' := (integral_prod _ hf1).trans_le hS2
  have hS3' := (integral_prod _ hf2).trans_le hS3
  have hK2 : (0 : ℝ) ≤ ((dA : ℝ) + 1) ^ 2 := by positivity
  have h5 := mul_le_mul_of_nonneg_left hS2' hL
  have h6 := mul_le_mul_of_nonneg_left hS3' hK2
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have h7 := mul_le_mul_of_nonneg_left (hle.trans (add_le_add (add_le_add le_rfl h6) h5)) hn0
  refine h7.trans (le_of_eq ?_)
  unfold Jstar p0
  rw [hc3]
  ring

/-- **(P2) and (P5)** from the interface statements. -/
theorem p5_107 (hT : TwoPoint107) (h1 : P1_107) (h3 : P3_107) (h4 : P4_107) (hS : SphStat107)
    (hK : KapFacts107) : P5_107 := fun n dA σ hn hd hσ =>
  ⟨p5_part1 hT h1 hS hK n dA σ hn hd hσ, p5_part2 hT h3 h4 hS hK n dA σ hn hd hσ⟩

end BstLean.Part107

#print axioms BstLean.Part107.p5_107
