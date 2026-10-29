import BstLean.Part187All
import BstLean.Part159Frame
import BstLean.Part188R143HidC
import BstLean.Part188R143HidC2
import BstLean.Part188R159Hat
import BstLean.Part188R159Win

/-! Part 187 (file `Part188R159Frame`): copy of `Part159Frame` re-proved at the floor `16200 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part188.Base159_R
open BstLean.Part159 BstLean.Part159.R

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 BstLean.Part140
open BstLean.Part157 (WHid)

variable {n : ℕ}

/-- **The frame bound for a centre near the computed centre (every `n ≥ 16 384`).** If
`θ ∈ goodHat n` and `t_W|bc − b̂|² ≤ γ·e₁/n` with `e₁ ≤ 10⁻¹⁰`, then the unit residual
directions orthogonal to `bc` have the frame bound `1.36/n`. -/
theorem pert_frame (hn : 16200 ≤ n) {θ : WHid n} (hθ : θ ∈ goodHat n) {bc : Fin (mW n) → ℝ}
    {e₁ : ℝ} (he1 : e₁ ≤ 1 / 10 ^ 10)
    (hb : 2 / (mW n : ℝ) * normSq (bc - bhat θ) ≤ 2 / ((2 * n : ℕ) : ℝ) * (e₁ / n))
    (w : Fin (mW n) → ℝ) :
    ∫ u, (∑ j, eDir bc (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
      136 / 100 / (n : ℝ) * ∑ j, w j ^ 2 := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn4
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by rw [hNcast]; linarith
  have := uniformSphere_isProbability (2 * n) hN
  obtain ⟨hk1, hk2⟩ := kap1_window hn4
  obtain ⟨bq, hb0, hb1, hmodel⟩ := kk_three
  set S0 : ℝ := (mW n : ℝ) / ((2 * n : ℕ) : ℝ) with hS0
  have hS0pos : 0 < S0 := by positivity
  set δ : Fin (mW n) → ℝ := bc - bhat θ with hδ
  -- `|δ|² ≤ S0·e₁/n`
  have hδn : normSq δ ≤ S0 * (e₁ / n) := by
    have h1 := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ (mW n : ℝ) / 2)
    have e2 : (mW n : ℝ) / 2 * (2 / (mW n : ℝ) * normSq δ) = normSq δ := by field_simp
    have e3 : (mW n : ℝ) / 2 * (2 / ((2 * n : ℕ) : ℝ) * (e₁ / n)) = S0 * (e₁ / n) := by
      rw [hS0]; field_simp
    linarith
  have hδ0 : 0 ≤ normSq δ := normSq_nonneg _
  have hen : e₁ / (n : ℝ) ≤ 1 / 10 ^ 10 / (n : ℝ) := div_le_div_of_nonneg_right he1 hnpos.le
  -- the distance of `b̂` to the exact centre
  have hξhat : normSq (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) - bhat θ) ≤
      S0 * ((3 / 8) / (n : ℝ)) := by
    have hd : dist2 (2 * n) (mW n) θ ≤
        2 / ((2 * n : ℕ) : ℝ) * (3 / 4 / ((2 * n : ℕ) : ℝ)) := hθ.1.2
    have e : normSq (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) - bhat θ) =
        normSq (bhat θ - hbarW θ) := by
      rw [normSq_sub_comm]
      rfl
    rw [e]
    unfold dist2 at hd
    rw [hS0]
    rw [hNcast] at hd ⊢
    have h1 : normSq (bhat θ - hbarW θ) ≤
        (mW n : ℝ) / 2 * (2 / (2 * (n : ℝ)) * (3 / 4 / (2 * (n : ℝ)))) := by
      have := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ (mW n : ℝ) / 2)
      have e2 : (mW n : ℝ) / 2 * (2 / (mW n : ℝ) * normSq (bhat θ - hbarW θ)) =
          normSq (bhat θ - hbarW θ) := by field_simp
      linarith
    refine h1.trans (le_of_eq ?_)
    field_simp
    ring
  -- (1) the distance of `bc` to the exact centre
  have hξ : ∑ j, (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) j - bc j) ^ 2 ≤
      S0 * ((37538 / 100000) / (n : ℝ)) := by
    have e : (fun j => hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) j - bc j) =
        (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) - bhat θ) + (-δ) := by
      funext j
      simp only [hδ, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
      ring
    have h1 := normSq_add_eta (η := 1 / 1000) (by norm_num)
      (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) - bhat θ) (-δ)
    rw [← e] at h1
    have hneg : normSq (-δ) = normSq δ := by simp [normSq]
    rw [hneg] at h1
    have h2 : (1 + 1 / 1000) * normSq (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) - bhat θ) ≤
        (1 + 1 / 1000) * (S0 * ((3 / 8) / (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hξhat (by norm_num)
    have h3 : (1 + 1 / (1 / 1000 : ℝ)) * normSq δ ≤
        (1 + 1 / (1 / 1000 : ℝ)) * (S0 * (1 / 10 ^ 10 / (n : ℝ))) :=
      mul_le_mul_of_nonneg_left (hδn.trans (mul_le_mul_of_nonneg_left hen hS0pos.le))
        (by norm_num)
    have h4 : (1 + 1 / 1000) * (S0 * ((3 / 8) / (n : ℝ))) +
        (1 + 1 / (1 / 1000 : ℝ)) * (S0 * (1 / 10 ^ 10 / (n : ℝ))) ≤
        S0 * ((37538 / 100000) / (n : ℝ)) := by
      have e4 : (1 + 1 / 1000) * (S0 * ((3 / 8) / (n : ℝ))) +
          (1 + 1 / (1 / 1000 : ℝ)) * (S0 * (1 / 10 ^ 10 / (n : ℝ))) =
          S0 * (((1 + 1 / 1000) * (3 / 8) + (1 + 1 / (1 / 1000 : ℝ)) * (1 / 10 ^ 10)) /
            (n : ℝ)) := by ring
      rw [e4]
      refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hnpos.le) hS0pos.le
      norm_num
    have h5 : ∑ j, (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) j - bc j) ^ 2 =
        normSq (fun j => hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) j - bc j) := rfl
    rw [h5]
    linarith
  -- (2) the integrated error of `⟨h(u), bc⟩`
  have hXhat : ∫ u, (∑ j, hid2 θ.1 θ.2 u j * bhat θ j - S0 * kap1 (2 * n)) ^ 2
      ∂uniformSphere (2 * n) ≤ S0 ^ 2 * ((1 / 400000) / (n : ℝ)) := by
    have hT : (n : ℝ) * errT θ ≤ (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * (1 / 400000) := hθ.2
    have e : ∀ u : Fin (2 * n) → ℝ, (∑ j, hid2 θ.1 θ.2 u j * bhat θ j -
        S0 * kap1 (2 * n)) ^ 2 =
        ((mW n : ℝ) / 2) ^ 2 *
          (That (2 * n) (mW n) u θ - 2 / ((2 * n : ℕ) : ℝ) * kap1 (2 * n)) ^ 2 := by
      intro u
      have e1 : That (2 * n) (mW n) u θ =
          2 / (mW n : ℝ) * ∑ j, hid2 θ.1 θ.2 u j * bhat θ j := rfl
      rw [e1, hS0]
      field_simp
    simp_rw [e]
    rw [integral_const_mul]
    change ((mW n : ℝ) / 2) ^ 2 * errT θ ≤ _
    have h1 : errT θ ≤ (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * (1 / 400000) / (n : ℝ) := by
      rw [le_div_iff₀ hnpos]
      linarith
    refine (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)).trans (le_of_eq ?_)
    rw [hS0, hNcast]
    field_simp
  have hcont1 : Continuous (fun u : Fin (2 * n) → ℝ =>
      ∑ j, hid2 θ.1 θ.2 u j * bhat θ j - S0 * kap1 (2 * n)) :=
    (continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp (continuous_hid2 θ.1 θ.2)).mul continuous_const).sub
      continuous_const
  have hcont2 : Continuous (fun u : Fin (2 * n) → ℝ => ∑ j, hid2 θ.1 θ.2 u j * δ j) :=
    continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp (continuous_hid2 θ.1 θ.2)).mul continuous_const
  have hcN : Continuous (fun u : Fin (2 * n) → ℝ => normSq (hid2 θ.1 θ.2 u)) :=
    continuous_normSq.comp (continuous_hid2 θ.1 θ.2)
  have hY : ∫ u, (∑ j, hid2 θ.1 θ.2 u j * δ j) ^ 2 ∂uniformSphere (2 * n) ≤
      S0 ^ 2 * (2 * (1 / 10 ^ 10) / (n : ℝ)) := by
    have hpt : ∀ u : Fin (2 * n) → ℝ, (∑ j, hid2 θ.1 θ.2 u j * δ j) ^ 2 ≤
        normSq δ * normSq (hid2 θ.1 θ.2 u) := fun u => by
      have := dotL_sq_le (hid2 θ.1 θ.2 u) δ
      linarith
    have i2' : Integrable (fun u : Fin (2 * n) → ℝ => (∑ j, hid2 θ.1 θ.2 u j * δ j) ^ 2)
        (uniformSphere (2 * n)) := sphere_cont_integrable hN (hcont2.pow 2)
    have h1 : ∫ u, (∑ j, hid2 θ.1 θ.2 u j * δ j) ^ 2 ∂uniformSphere (2 * n) ≤
        ∫ u, normSq δ * normSq (hid2 θ.1 θ.2 u) ∂uniformSphere (2 * n) :=
      integral_mono i2' ((sphere_cont_integrable hN hcN).const_mul (normSq δ)) hpt
    rw [integral_const_mul] at h1
    have h2 := sphere_energy_le hn4 hθ.1.1
    have h3 : normSq δ * ∫ u, normSq (hid2 θ.1 θ.2 u) ∂uniformSphere (2 * n) ≤
        S0 * (1 / 10 ^ 10 / (n : ℝ)) * (2 * S0) :=
      mul_le_mul (hδn.trans (mul_le_mul_of_nonneg_left hen hS0pos.le)) h2
        (integral_nonneg fun u => normSq_nonneg _) (by positivity)
    refine (h1.trans h3).trans (le_of_eq ?_)
    ring
  have hX : ∫ u, (∑ j, hid2 θ.1 θ.2 u j * bc j - S0 * kap1 (2 * n)) ^ 2
      ∂uniformSphere (2 * n) ≤ S0 ^ 2 * ((2546 / 10 ^ 9) / (n : ℝ)) := by
    have hsplit : ∀ u : Fin (2 * n) → ℝ, (∑ j, hid2 θ.1 θ.2 u j * bc j - S0 * kap1 (2 * n)) ^ 2 ≤
        (1 + 1 / 100) * (∑ j, hid2 θ.1 θ.2 u j * bhat θ j - S0 * kap1 (2 * n)) ^ 2 +
          (1 + 1 / (1 / 100 : ℝ)) * (∑ j, hid2 θ.1 θ.2 u j * δ j) ^ 2 := by
      intro u
      have e : ∑ j, hid2 θ.1 θ.2 u j * bc j - S0 * kap1 (2 * n) =
          (∑ j, hid2 θ.1 θ.2 u j * bhat θ j - S0 * kap1 (2 * n)) +
            ∑ j, hid2 θ.1 θ.2 u j * δ j := by
        have : ∑ j, hid2 θ.1 θ.2 u j * bc j =
            ∑ j, hid2 θ.1 θ.2 u j * bhat θ j + ∑ j, hid2 θ.1 θ.2 u j * δ j := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [hδ, Pi.sub_apply]
          ring
        rw [this]; ring
      rw [e]
      exact sq_add_eta (by norm_num) _ _
    have i1 : Integrable (fun u : Fin (2 * n) → ℝ =>
        (∑ j, hid2 θ.1 θ.2 u j * bhat θ j - S0 * kap1 (2 * n)) ^ 2) (uniformSphere (2 * n)) :=
      sphere_cont_integrable hN (hcont1.pow 2)
    have i2 : Integrable (fun u : Fin (2 * n) → ℝ => (∑ j, hid2 θ.1 θ.2 u j * δ j) ^ 2)
        (uniformSphere (2 * n)) := sphere_cont_integrable hN (hcont2.pow 2)
    have hcont3 : Continuous (fun u : Fin (2 * n) → ℝ =>
        ∑ j, hid2 θ.1 θ.2 u j * bc j - S0 * kap1 (2 * n)) :=
      (continuous_finsetSum _ fun j _ =>
        ((continuous_apply j).comp (continuous_hid2 θ.1 θ.2)).mul continuous_const).sub
        continuous_const
    have i3 : Integrable (fun u : Fin (2 * n) → ℝ =>
        (∑ j, hid2 θ.1 θ.2 u j * bc j - S0 * kap1 (2 * n)) ^ 2) (uniformSphere (2 * n)) :=
      sphere_cont_integrable hN (hcont3.pow 2)
    have h1 : ∫ u, (∑ j, hid2 θ.1 θ.2 u j * bc j - S0 * kap1 (2 * n)) ^ 2
        ∂uniformSphere (2 * n) ≤
        ∫ u, ((1 + 1 / 100) * (∑ j, hid2 θ.1 θ.2 u j * bhat θ j - S0 * kap1 (2 * n)) ^ 2 +
          (1 + 1 / (1 / 100 : ℝ)) * (∑ j, hid2 θ.1 θ.2 u j * δ j) ^ 2) ∂uniformSphere (2 * n) :=
      integral_mono i3 ((i1.const_mul _).add (i2.const_mul _)) hsplit
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
      integral_const_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left hXhat (by norm_num : (0 : ℝ) ≤ 1 + 1 / 100)
    have h3 := mul_le_mul_of_nonneg_left hY (by norm_num : (0 : ℝ) ≤ 1 + 1 / (1 / 100 : ℝ))
    have h4 : (1 + 1 / 100) * (S0 ^ 2 * ((1 / 400000) / (n : ℝ))) +
        (1 + 1 / (1 / 100 : ℝ)) * (S0 ^ 2 * (2 * (1 / 10 ^ 10) / (n : ℝ))) ≤
        S0 ^ 2 * ((2546 / 10 ^ 9) / (n : ℝ)) := by
      have e4 : (1 + 1 / 100) * (S0 ^ 2 * ((1 / 400000) / (n : ℝ))) +
          (1 + 1 / (1 / 100 : ℝ)) * (S0 ^ 2 * (2 * (1 / 10 ^ 10) / (n : ℝ))) =
          S0 ^ 2 * (((1 + 1 / 100) * (1 / 400000) +
            (1 + 1 / (1 / 100 : ℝ)) * (2 * (1 / 10 ^ 10))) / (n : ℝ)) := by ring
      rw [e4]
      refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hnpos.le) (sq_nonneg _)
      norm_num
    linarith
  -- (3) the length of `bc`
  have hβb : S0 * (4863 / 10000) ≤ normSq bc := by
    obtain ⟨hBl, -⟩ := Bh_window_16 hn hθ
    have hbh : S0 * (48685 / 100000) ≤ normSq (bhat θ) := by
      unfold Bh at hBl
      have h1 := mul_le_mul_of_nonneg_left hBl (by positivity : (0 : ℝ) ≤ (mW n : ℝ) / 2)
      have e2 : (mW n : ℝ) / 2 * (2 / (mW n : ℝ) * normSq (bhat θ)) = normSq (bhat θ) := by
        field_simp
      have e3 : (mW n : ℝ) / 2 * (2 / ((2 * n : ℕ) : ℝ) * (48685 / 100000)) =
          S0 * (48685 / 100000) := by
        rw [hS0]; field_simp
      linarith
    have e : bhat θ = bc + (-δ) := by
      funext j
      simp only [hδ, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
      ring
    have h1 := normSq_add_eta (η := 1 / 1000) (by norm_num) bc (-δ)
    rw [← e] at h1
    have hneg : normSq (-δ) = normSq δ := by simp [normSq]
    rw [hneg] at h1
    have h3 : (1 + 1 / (1 / 1000 : ℝ)) * normSq δ ≤
        (1 + 1 / (1 / 1000 : ℝ)) * (S0 * (1 / 10 ^ 10 / 16200)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine hδn.trans (mul_le_mul_of_nonneg_left (hen.trans ?_) hS0pos.le)
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn'
    nlinarith [normSq_nonneg bc]
  have hsle : (4683 : ℝ) / 10000 ≤
      1 - 21 / 2000 - (kap1 (2 * n) + 24 / 2500) ^ 2 / (4863 / 10000) := by
    have h1 : (kap1 (2 * n) + 24 / 2500) ^ 2 ≤ (4938 / 10000 + 24 / 2500) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : (kap1 (2 * n) + 24 / 2500) ^ 2 / (4863 / 10000) ≤
        (4938 / 10000 + 24 / 2500) ^ 2 / (4863 / 10000) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have h3 : (4938 / 10000 + 24 / 2500 : ℝ) ^ 2 / (4863 / 10000) ≤ 52111 / 100000 := by norm_num
    linarith
  exact frameB_num (n := n) (n0 := 16200) (by norm_num) hn (b := bq) (c2 := 138 / 1000)
    (η := 1 / 1000) (K₃ := 2 / 5) (r0 := 243 / 500000000) (k0 := 412 / 125000)
    (k6 := 10759 / 1000000) (sp := 4 / 100) (ε₁ := 21 / 2000) (ε₂ := 24 / 2500)
    (s := 4683 / 10000)
    (p₂ := 4 / 10000) (D0 := 1751393 / 20000000) (C := 136 / 100) (ξ₀ := 37538 / 100000)
    (a := kap1 (2 * n)) (dT := 2546 / 10 ^ 9) (β := 4863 / 10000)
    hb0 hb1 (by norm_num) (by norm_num) (by norm_num) hmodel
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by norm_num) hsle (by norm_num) hθ.1.1 hξ hX hβb w

end BstLean.Part188.Base159_R

