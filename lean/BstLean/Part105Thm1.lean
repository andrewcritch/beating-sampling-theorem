import BstLean.Part105Abstract
import BstLean.Part105BW
import BstLean.Part105Law

/-!
# Part 105: Theorem 1 of round oaW1 for the Gaussian version of the World polynomial

`W : ℝ^N → ℝ^n` of degree `d ≥ 2`, `N ≥ 1` (the case of the north star: `N = r·n`, `d = r·d_A`).
The coefficients of degree `0` and `1` are fixed (`b0`); the coefficients `c` of degree `2` to `d`
have the Gaussian version of the Bombieri–Weyl distribution with parameter `σ`
(`W = mixW b0 c`, `c ∼ bwGauss N n d σ`; `mixW` reads only the coefficients of degree `≥ 2` of
`c`). `φ` is a bounded measurable function on `ℝⁿ` (only its values on the unit sphere matter).
`τ = √(d−1)·σ`.

* `thm1_mean` (a): `E_R E_{μ_W} φ = E_{ν_W} φ`.
* `thm1_var` (b): `E_R (E_{μ_W} φ − E_{ν_W} φ)² ≤ λ_0 · Var_{ν_W} φ`.
* `thm1_var_noise`: the sharper form with the mean noise variance.
* `lam0_six`, `lam0_bound` (c): the value of `λ_0` at `d = 6` and `λ_0 ≤ (1/(10n))(1 + 2/n)` at
  `N = 2n`.
* `thm1_r2_dA3`: the case `r = 2`, `d_A = 3`.
* `thm1_var_full`: the same bound with `(W_0, W_1)` random too (all coefficients Gaussian).

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part105

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)

/-! ## Measurability -/

lemma monoVal_eq_prod {k d : ℕ} (x : Fin k → ℝ) (m : MonoIdx k d) :
    monoVal x m = ∏ l ∈ m.2.1.toFinset, x l ^ m.2.1.count l :=
  Finset.prod_multiset_map_count _ _

lemma measurable_monoVal {k d : ℕ} (m : MonoIdx k d) :
    Measurable (fun x : Fin k → ℝ => monoVal x m) := by
  simp_rw [monoVal_eq_prod]
  exact Finset.measurable_prod _ (fun l _ => (measurable_pi_apply l).pow_const _)

lemma measurable_bwEval2 {k q d : ℕ} :
    Measurable (fun p : (CoefIdx k q d → ℝ) × (Fin k → ℝ) => bwEval p.1 p.2) := by
  refine measurable_pi_iff.mpr fun a => ?_
  unfold bwEval
  exact Finset.measurable_sum _ fun m _ =>
    ((measurable_pi_apply (a, m)).comp measurable_fst).mul
      ((measurable_monoVal m).comp measurable_snd)

lemma measurable_bwEval_comp {k q d : ℕ} {α : Type*} [MeasurableSpace α]
    {F : α → CoefIdx k q d → ℝ} {G : α → Fin k → ℝ} (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun a => bwEval (F a) (G a)) :=
  measurable_bwEval2.comp (hF.prodMk hG)

lemma measurable_mixW_right {k q d : ℕ} (b0 : CoefIdx k q d → ℝ) :
    Measurable (fun c : CoefIdx k q d → ℝ => mixW b0 c) := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold mixW
  split_ifs
  · exact measurable_pi_apply i
  · exact measurable_const

lemma measurable_mixW_left {k q d : ℕ} (c : CoefIdx k q d → ℝ) :
    Measurable (fun b0 : CoefIdx k q d → ℝ => mixW b0 c) := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold mixW
  split_ifs
  · exact measurable_const
  · exact measurable_pi_apply i

lemma bwEval_mix {k q d : ℕ} (b0 c : CoefIdx k q d → ℝ) (x : Fin k → ℝ) :
    bwEval (mixW b0 c) x = bwEval (mixW b0 0) x + bwEval (mixW 0 c) x := by
  funext a
  simp only [bwEval, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold mixW
  split_ifs <;> simp

lemma measurable_sphProj {n : ℕ} : Measurable (sphProj (n := n)) := by
  unfold sphProj
  exact (measurable_const.div
    (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2).sqrt).smul measurable_id

lemma measurable_dot2 {N : ℕ} : Measurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => dot p.1 p.2) := by
  unfold dot
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp measurable_fst).mul ((measurable_pi_apply i).comp measurable_snd)

lemma measurable_rho (d : ℕ) : Measurable (rho d) := by
  unfold rho
  exact (Finset.measurable_sum _ fun j _ => measurable_id.pow_const j).div_const _

/-! ## Unit vectors -/

variable {N n d : ℕ}

/-- A fixed unit vector. -/
def e0 (hN : 1 ≤ N) : Fin N → ℝ := Pi.single ⟨0, hN⟩ 1

lemma dot_e0 (hN : 1 ≤ N) : dot (e0 hN) (e0 hN) = 1 := by
  simp [dot, e0, Pi.single_apply]

/-- `u` if `u` is a unit vector, a fixed unit vector if not. The uniform distribution on the
sphere does not see the difference (`fixU_ae`). -/
noncomputable def fixU (hN : 1 ≤ N) (u : Fin N → ℝ) : Fin N → ℝ :=
  if dot u u = 1 then u else e0 hN

lemma dot_fixU (hN : 1 ≤ N) (u : Fin N → ℝ) : dot (fixU hN u) (fixU hN u) = 1 := by
  unfold fixU
  split_ifs with h
  · exact h
  · exact dot_e0 hN

lemma measurable_fixU (hN : 1 ≤ N) : Measurable (fixU hN) := by
  unfold fixU
  refine Measurable.ite ?_ measurable_id measurable_const
  exact measurableSet_eq_fun (measurable_dot2.comp (measurable_id.prodMk measurable_id))
    measurable_const

lemma fixU_ae (hN : 1 ≤ N) : ∀ᵐ u ∂uniformSphere N, fixU hN u = u := by
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere N] with u hu
  simp [fixU, dot_self_eq, hu]

/-! ## The instance of the abstract theorem -/

/-- `τ = √(d−1)·σ`. -/
noncomputable def tauOf (d : ℕ) (σ : ℝ) : ℝ := Real.sqrt ((d : ℝ) - 1) * σ

/-- The field `R(u)`: the terms of degree `2` to `d`. -/
noncomputable def Rf (hN : 1 ≤ N) (c : CoefIdx N n d → ℝ) (u : Fin N → ℝ) : Fin n → ℝ :=
  bwEval (mixW 0 c) (fixU hN u)

/-- The correlation `ρ(u·u′)`. -/
noncomputable def rhoF (hN : 1 ≤ N) (d : ℕ) (u u' : Fin N → ℝ) : ℝ :=
  rho d (dot (fixU hN u) (fixU hN u'))

/-- `f_u(z) = φ(π(W_0 + W_1 u + z))`. -/
noncomputable def fF (hN : 1 ≤ N) (b0 : CoefIdx N n d → ℝ) (φ : (Fin n → ℝ) → ℝ)
    (u : Fin N → ℝ) (z : Fin n → ℝ) : ℝ :=
  φ (sphProj (bwEval (mixW b0 0) (fixU hN u) + z))

section main

variable (hN : 1 ≤ N) (hd : 2 ≤ d) (σ : ℝ) (b0 : CoefIdx N n d → ℝ) {φ : (Fin n → ℝ) → ℝ}
  (hφ : BM φ)

lemma hR_F : Measurable (fun p : (CoefIdx N n d → ℝ) × (Fin N → ℝ) => Rf hN p.1 p.2) :=
  measurable_bwEval_comp ((measurable_mixW_right 0).comp measurable_fst)
    ((measurable_fixU hN).comp measurable_snd)

lemma hρm_F : Measurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => rhoF hN d p.1 p.2) :=
  (measurable_rho d).comp (measurable_dot2.comp
    (((measurable_fixU hN).comp measurable_fst).prodMk ((measurable_fixU hN).comp measurable_snd)))

include hd in
lemma hρ_F (u u' : Fin N → ℝ) : 0 ≤ rhoF hN d u u' ∧ rhoF hN d u u' ≤ 1 :=
  rhoBounds105 d _ hd (abs_dot_le_one _ _ (dot_fixU hN u) (dot_fixU hN u'))

lemma hlam_F (u : Fin N → ℝ) : ∫ u', rhoF hN d u u' ∂uniformSphere N = lam0 N d := by
  rw [← lamRow105 N d (fixU hN u) hN (dot_fixU hN u)]
  refine integral_congr_ae ?_
  filter_upwards [fixU_ae hN] with u' hu'
  simp only [rhoF, hu']

include hd in
lemma hlaw_F (u u' : Fin N → ℝ) :
    (bwGauss N n d σ).map (fun c => (Rf hN c u, Rf hN c u')) =
      ((stdGauss (Fin n)).prod (stdGauss (Fin n))).map
        (fun p => (tauOf d σ • p.1,
          tauOf d σ • (rhoF hN d u u' • p.1 + sC (rhoF hN d u u') • p.2))) :=
  pairLaw105_of multinomial105 N n d σ (fixU hN u) (fixU hN u') hd (dot_fixU hN u)
    (dot_fixU hN u')

include hφ in
lemma hf_F : BM (fun p : (Fin N → ℝ) × (Fin n → ℝ) => fF hN b0 φ p.1 p.2) := by
  have h1 : Measurable (fun p : (Fin N → ℝ) × (Fin n → ℝ) =>
      bwEval (mixW b0 0) (fixU hN p.1)) :=
    measurable_bwEval_comp measurable_const ((measurable_fixU hN).comp measurable_fst)
  have h2 : Measurable (fun p : (Fin N → ℝ) × (Fin n → ℝ) => p.2) := measurable_snd
  exact hφ.comp (measurable_sphProj.comp (h1.add h2))

lemma measurable_muMap (W : CoefIdx N n d → ℝ) :
    Measurable (fun u : Fin N → ℝ => sphProj (bwEval W u)) :=
  measurable_sphProj.comp (measurable_bwEval_comp measurable_const measurable_id)

lemma measurable_nuMap (τ : ℝ) :
    Measurable (fun p : (Fin N → ℝ) × (Fin n → ℝ) =>
      sphProj (bwEval (mixW b0 0) p.1 + τ • p.2)) := by
  have h1 : Measurable (fun p : (Fin N → ℝ) × (Fin n → ℝ) => bwEval (mixW b0 0) p.1) :=
    measurable_bwEval_comp measurable_const measurable_fst
  have h2 : Measurable (fun p : (Fin N → ℝ) × (Fin n → ℝ) => τ • p.2) :=
    measurable_snd.const_smul τ
  exact measurable_sphProj.comp (h1.add h2)

include hφ in
/-- `E_{μ_W} φ` is the abstract `Bmu`. -/
lemma Bmu_eq (c : CoefIdx N n d → ℝ) :
    Bmu (uniformSphere N) (Rf hN) (fF hN b0 φ) c = ∫ x, φ x ∂muW (mixW b0 c) := by
  unfold muW Bmu
  rw [integral_map (measurable_muMap _).aemeasurable hφ.meas.aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [fixU_ae hN] with u hu
  simp only [fF, Rf, hu]
  rw [← bwEval_mix]

include hN in
/-- An integral under `ν_W`. -/
lemma nu_integral (τ : ℝ) {ψ : (Fin n → ℝ) → ℝ} (hψ : BM ψ) :
    ∫ x, ψ x ∂nuW b0 τ =
      ∫ u, ∫ g, fF hN b0 ψ u (τ • g) ∂stdGauss (Fin n) ∂uniformSphere N := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  unfold nuW
  rw [integral_map (measurable_nuMap b0 τ).aemeasurable hψ.meas.aestronglyMeasurable,
    integral_prod _ ((hψ.comp (measurable_nuMap b0 τ)).integrable _)]
  refine integral_congr_ae ?_
  filter_upwards [fixU_ae hN] with u hu
  simp only [fF, hu]

include hφ in
lemma Bnu_eq (τ : ℝ) : Bnu (uniformSphere N) τ (fF hN b0 φ) = ∫ x, φ x ∂nuW b0 τ :=
  (nu_integral hN b0 τ hφ).symm

include hN in
lemma nuW_prob (τ : ℝ) : IsProbabilityMeasure (nuW b0 τ) := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  unfold nuW
  infer_instance

include hφ in
lemma Vnu_eq (τ : ℝ) : Vnu (uniformSphere N) τ (fF hN b0 φ) = Var[φ; nuW b0 τ] := by
  have := nuW_prob hN b0 τ
  rw [variance_eq_integral hφ.meas.aemeasurable,
    nu_integral hN b0 τ ((hφ.sub (BM.const _)).sq)]
  unfold Vnu
  rw [Bnu_eq hN b0 hφ τ]
  rfl

include hN hd hφ in
/-- **Theorem 1 (a)**: `E_R E_{μ_W} φ = E_{ν_W} φ`. -/
theorem thm1_mean :
    ∫ c, (∫ x, φ x ∂muW (mixW b0 c)) ∂bwGauss N n d σ = ∫ x, φ x ∂nuW b0 (tauOf d σ) := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  have h := abstract_mean (uniformSphere N) (bwGauss N n d σ) (Rf hN) (rhoF hN d) (tauOf d σ)
    (fF hN b0 φ) (hR_F hN) (hlaw_F hN hd σ) (hf_F hN b0 hφ)
  rw [Bnu_eq hN b0 hφ] at h
  rw [← h]
  congr 1
  funext c
  exact (Bmu_eq hN b0 hφ c).symm

include hN hd in
lemma lam0_nonneg : 0 ≤ lam0 N d := by
  rw [← hlam_F (d := d) hN (e0 hN)]
  exact integral_nonneg fun u' => (hρ_F hN hd _ _).1

include hN hd hφ in
/-- **Theorem 1 (b), sharp form**: `E_R (E_{μ_W} φ − E_{ν_W} φ)² ≤ λ_0 · V_noise`, with
`V_noise = E_u Var_g φ(π(W_0 + W_1 u + τ g))`. -/
theorem thm1_var_noise :
    ∫ c, (∫ x, φ x ∂muW (mixW b0 c) - ∫ x, φ x ∂nuW b0 (tauOf d σ)) ^ 2 ∂bwGauss N n d σ ≤
      lam0 N d * Vnoise (uniformSphere N) (tauOf d σ) (fF hN b0 φ) := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  have h := abstract_var (uniformSphere N) (bwGauss N n d σ) (Rf hN) (rhoF hN d) (tauOf d σ)
    (lam0 N d) (fF hN b0 φ) (hR_F hN) (hρm_F hN) (fun u u' => (hρ_F hN hd u u').1)
    (fun u u' => (hρ_F hN hd u u').2)
    (fun u u' => by simp only [rhoF]; rw [dot_comm'])
    (fun u => (hlam_F hN u).le) (hlaw_F hN hd σ) (hf_F hN b0 hφ)
  rw [Bnu_eq hN b0 hφ] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  funext c
  rw [Bmu_eq hN b0 hφ c]

include hN hd hφ in
/-- **Theorem 1 (b)**: `E_R (E_{μ_W} φ − E_{ν_W} φ)² ≤ λ_0 · Var_{ν_W} φ`. -/
theorem thm1_var :
    ∫ c, (∫ x, φ x ∂muW (mixW b0 c) - ∫ x, φ x ∂nuW b0 (tauOf d σ)) ^ 2 ∂bwGauss N n d σ ≤
      lam0 N d * Var[φ; nuW b0 (tauOf d σ)] := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  refine (thm1_var_noise hN hd σ b0 hφ).trans ?_
  rw [← Vnu_eq hN b0 hφ]
  exact mul_le_mul_of_nonneg_left
    (Vnoise_le_Vnu (uniformSphere N) (tauOf d σ) (fF hN b0 φ) (hf_F hN b0 hφ))
    (lam0_nonneg hN hd)

end main

/-! ## The value of `λ_0` -/

/-- **Theorem 1 (c), value** at degree `6`. -/
theorem lam0_six (N : ℕ) (hN : 1 ≤ N) :
    lam0 N 6 = (1 / (N : ℝ) + 3 / ((N : ℝ) * (N + 2)) + 15 / ((N : ℝ) * (N + 2) * (N + 4))) / 5 :=
  lamValue105 N hN

/-- **Theorem 1 (c), bound** at `r = 2`, `d = 6`: `λ_0 ≤ (1/(10n))(1 + 2/n)`. -/
theorem lam0_bound (n : ℕ) (hn : 1 ≤ n) :
    lam0 (2 * n) 6 ≤ 1 / (10 * (n : ℝ)) * (1 + 2 / (n : ℝ)) := by
  rw [lam0_six (2 * n) (by omega)]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  rw [div_le_iff₀ (by norm_num)]
  have h1 : (0 : ℝ) < n := by linarith
  rw [show 1 / (10 * (n : ℝ)) * (1 + 2 / (n : ℝ)) * 5 = (n + 2) / (2 * (n : ℝ) ^ 2) by
    field_simp; ring]
  rw [show 1 / (2 * (n : ℝ)) + 3 / (2 * (n : ℝ) * (2 * n + 2)) +
      15 / (2 * (n : ℝ) * (2 * n + 2) * (2 * n + 4)) =
      (4 * (n : ℝ) ^ 2 + 18 * n + 35) / (8 * n * (n + 1) * (n + 2)) by field_simp; ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos h1 h1, mul_pos (mul_pos h1 h1) h1, mul_pos (mul_pos h1 h1) (mul_pos h1 h1)]

end BstLean.Part105
