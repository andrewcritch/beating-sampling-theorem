import BstLean.Part143World
import BstLean.Part145C2

/-!
# Part 145, helper `C3`: the World chain with the cosine link `jCosC`

This file repeats the definitions and theorems of `Part143World` that contain the second-order
term `jCos` of the cosine link, with `jCosC` of `Part145C2` (`lin_cos_L2c`) in its place. The
proofs are the proofs of `Part143World` (made by `gen_c3.py`). The link of the inputs `sU2` and
the general lemma `tX_L2_bias` do not change.

* `eWsmallC n m = jCosC n + (1 + 2/√n)·eHid m + 2·√(epsW m)`.
* `betaLinC n = 2K₄(n)/n + (1/√n + jCosC n)·(√2/√n + 2K₄(n)/n)`; `lin_bias_unitC`, `lin_biasC`.
* `betaWC n m = betaLinC n + 2·epsW m + eHid m`; `world_biasC`.
* `eWr2C N n m = (1/√n)·(1 − κ(κ(0))² + 2·sU2 N) + eWsmallC n m`; `tX_L2_gen2C`.
* `tau143sC n = √(eWr2C(2n, n, m_W)² + sU2(2n)² + 2·sU2(2n)·betaWC n m_W)`; **`tX_L2_145C`**:
  `‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂ ≤ tau143sC n` at the widths of the Focus, `n ≥ 4096`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
open BstLean.Part142 BstLean.Part143

/-- The small terms of the World link, with `jCosC`. -/
noncomputable def eWsmallC (n mW : ℕ) : ℝ :=
  jCosC n + (1 + 2 / √(n : ℝ)) * eHid mW + 2 * √(epsW mW)

lemma eWsmallC_nonneg (n mW : ℕ) : 0 ≤ eWsmallC n mW := by
  have := eHid_nonneg mW
  have := jCosC_nonneg n
  unfold eWsmallC
  positivity

/-! ## The bias of the last matrix: second order -/

/-- The bound of the bias of the cosine link of one linear layer with `n` rows. -/
noncomputable def betaLinC (n : ℕ) : ℝ :=
  2 * K4 n / (n : ℝ) + (1 / √(n : ℝ) + jCosC n) * (√2 / √(n : ℝ) + 2 * K4 n / (n : ℝ))

lemma betaLinC_nonneg (n : ℕ) : 0 ≤ betaLinC n := by
  have := K4_nonneg n
  have := jCosC_nonneg n
  unfold betaLinC
  positivity

section Lin

variable {n k : ℕ}

/-- **The bias of the cosine of a linear layer, unit inputs.** -/
theorem lin_bias_unitC {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) {h h' : Fin k → ℝ}
    (hh : normSq h = 1) (hh' : normSq h' = 1) :
    |∫ M : Matrix (Fin n) (Fin k) ℝ,
      (dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - dotp h h') ∂gaussMat n k v| ≤
      betaLinC n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = dotp h h' := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (n : ℝ) * v := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ mul_pos hn0 hv
  have hK0 := K4_nonneg n
  have hτ : |τ| ≤ 1 := by
    have := abs_dotp_le_nrm h h'
    rwa [nrm_of_normSq_one hh, nrm_of_normSq_one hh', mul_one, ← hτdef] at this
  have hτ' := abs_le.mp hτ
  have hτ2 : 0 ≤ 1 - τ ^ 2 := by nlinarith
  have hJ0 : 0 ≤ jCosC n := jCosC_nonneg n
  -- `D`
  have hD : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - τ) (1 / √(n : ℝ) + jCosC n) := by
    have h0 := lin_cos_unit_L2c (n := n) hv hn hh hh'
    rw [← hτdef] at h0
    refine h0.mono (add_nonneg (div_nonneg hτ2 hsn.le) hJ0) ?_
    have : (1 - τ ^ 2) / √(n : ℝ) ≤ 1 / √(n : ℝ) :=
      div_le_div_of_nonneg_right (by nlinarith [sq_nonneg τ]) hsn.le
    linarith
  -- `δ`
  have hdl0 : dlt h h' = 0 := by
    unfold dlt
    rw [hh, hh', nrm_of_normSq_one hh, nrm_of_normSq_one hh']
    norm_num
  have hδ : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dlt (M.mulVec h) (M.mulVec h') / s) (2 * K4 n / (n : ℝ)) := by
    have h0 := (linDltStmt hv hn h h').const_mul_nonneg (c := 1 / s) (by positivity)
    rw [hdl0, hh, hh'] at h0
    refine (h0.congr_fun fun M => ?_).congr_bound ?_
    · ring
    · rw [hs]
      have hv' := hv.ne'
      simp only [sub_self, abs_zero, mul_zero, add_zero]
      field_simp
      ring
  -- `P⁺ − 1`
  have h2n : √(2 * (n : ℝ)) = √2 * √(n : ℝ) := Real.sqrt_mul (by norm_num) _
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
  have hP : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec h) + normSq (M.mulVec h')) / 2 / s - 1) (√2 / √(n : ℝ)) := by
    have a1 := (lin_c2 (m := n) hv.le h).const_mul_nonneg (c := 1 / (2 * s)) (by positivity)
    have a2 := (lin_c2 (m := n) hv.le h').const_mul_nonneg (c := 1 / (2 * s)) (by positivity)
    rw [hh] at a1
    rw [hh'] at a2
    refine ((a1.add0 a2 (by positivity) (by positivity)).congr_fun fun M => ?_).congr_bound ?_
    · rw [hs]
      have hv' := hv.ne'
      field_simp
      ring
    · rw [hs, h2n]
      have hv' := hv.ne'
      field_simp
      nlinarith [hss]
  -- `1 − Pn`
  have h1p : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      1 - nrm (M.mulVec h) * nrm (M.mulVec h') / s) (√2 / √(n : ℝ) + 2 * K4 n / (n : ℝ)) := by
    refine (hP.neg.add0 hδ (by positivity) (by positivity)).congr_fun fun M => ?_
    unfold dlt
    ring
  -- the pointwise identity
  have hpt : ∀ M : Matrix (Fin n) (Fin k) ℝ,
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - τ =
        (dotp (M.mulVec h) (M.mulVec h') -
          τ * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) / s +
        τ * (dlt (M.mulVec h) (M.mulVec h') / s) +
        (dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - τ) *
          (1 - nrm (M.mulVec h) * nrm (M.mulVec h') / s) := by
    intro M
    have hcs := abs_dotp_le_nrm (M.mulVec h) (M.mulVec h')
    have key : (dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - τ) *
        (nrm (M.mulVec h) * nrm (M.mulVec h')) =
        dotp (M.mulVec h) (M.mulVec h') - τ * (nrm (M.mulVec h) * nrm (M.mulVec h')) := by
      by_cases hx : normSq (M.mulVec h) = 0
      · have h0 : nrm (M.mulVec h) = 0 := by unfold nrm; rw [hx, Real.sqrt_zero]
        rw [h0, zero_mul] at hcs ⊢
        have := abs_nonpos_iff.mp hcs
        rw [this]; ring
      by_cases hy : normSq (M.mulVec h') = 0
      · have h0 : nrm (M.mulVec h') = 0 := by unfold nrm; rw [hy, Real.sqrt_zero]
        rw [h0, mul_zero] at hcs ⊢
        have := abs_nonpos_iff.mp hcs
        rw [this]; ring
      rw [dotp_sphPt _ _ hx hy]
      have := (nrm_pos_of_ne hx).ne'
      have := (nrm_pos_of_ne hy).ne'
      field_simp
    have key2 : dotp (M.mulVec h) (M.mulVec h') =
        (dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - τ) *
          (nrm (M.mulVec h) * nrm (M.mulVec h')) +
          τ * (nrm (M.mulVec h) * nrm (M.mulVec h')) := by linarith
    unfold dlt
    rw [key2]
    have hs' := hs0.ne'
    field_simp
    ring
  -- the integrals
  obtain ⟨iC, eC⟩ := layer_dot_lin (m := n) hv.le h h'
  obtain ⟨iX, eX⟩ := layer_lin_sq (m := n) hv.le h
  obtain ⟨iY, eY⟩ := layer_lin_sq (m := n) hv.le h'
  have iS : Integrable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      normSq (M.mulVec h) + normSq (M.mulVec h')) (gaussMat n k v) := iX.add iY
  have iS2 : Integrable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      τ * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) (gaussMat n k v) :=
    (iS.div_const 2).const_mul τ
  have iE1 : Integrable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dotp (M.mulVec h) (M.mulVec h') -
        τ * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) (gaussMat n k v) := iC.sub iS2
  have iE : Integrable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (dotp (M.mulVec h) (M.mulVec h') -
        τ * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) / s) (gaussMat n k v) :=
    iE1.div_const s
  have eE : ∫ M : Matrix (Fin n) (Fin k) ℝ, (dotp (M.mulVec h) (M.mulVec h') -
        τ * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) / s ∂gaussMat n k v = 0 := by
    rw [integral_div, integral_sub iC iS2, integral_const_mul, integral_div,
      integral_add iX iY, eC, eX, eY, hh, hh', ← hτdef]
    ring
  have iδ := l2_integrable hδ
  have iδτ : Integrable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      τ * (dlt (M.mulVec h) (M.mulVec h') / s)) (gaussMat n k v) := iδ.const_mul τ
  have iEδ : Integrable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (dotp (M.mulVec h) (M.mulVec h') -
        τ * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) / s +
        τ * (dlt (M.mulVec h) (M.mulVec h') / s)) (gaussMat n k v) := iE.add iδτ
  have iR := l2_mul_integrable hD h1p
  have e0 : ∫ M : Matrix (Fin n) (Fin k) ℝ,
      (dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - τ) ∂gaussMat n k v =
      τ * ∫ M : Matrix (Fin n) (Fin k) ℝ, dlt (M.mulVec h) (M.mulVec h') / s ∂gaussMat n k v +
      ∫ M : Matrix (Fin n) (Fin k) ℝ, (dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - τ) *
          (1 - nrm (M.mulVec h) * nrm (M.mulVec h') / s) ∂gaussMat n k v := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add iEδ iR, integral_add iE iδτ, eE, integral_const_mul]
    ring
  rw [← hτdef, e0]
  have b1 := l2_abs_integral_le (by positivity) hδ
  have b2 := l2_abs_integral_mul_le (by positivity) (by positivity) hD h1p
  have b3 : |τ * ∫ M : Matrix (Fin n) (Fin k) ℝ,
      dlt (M.mulVec h) (M.mulVec h') / s ∂gaussMat n k v| ≤ 2 * K4 n / (n : ℝ) := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hτ).trans b1
  unfold betaLinC
  exact (abs_add_le _ _).trans (add_le_add b3 b2)

/-- **The bias of the cosine of a linear layer**, nonzero inputs. -/
theorem lin_biasC {n k : ℕ} {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) (h h' : Fin k → ℝ)
    (hh : normSq h ≠ 0) (hh' : normSq h' ≠ 0) :
    |∫ M : Matrix (Fin n) (Fin k) ℝ,
      (dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - cosv h h') ∂gaussMat n k v| ≤
      betaLinC n := by
  have hp := nrm_pos_of_ne hh
  have hp' := nrm_pos_of_ne hh'
  set g : Fin k → ℝ := (1 / nrm h) • h with hg
  set g' : Fin k → ℝ := (1 / nrm h') • h' with hg'
  have hg1 : normSq g = 1 := by
    rw [hg, normSq_smul, ← nrm_sq h]; field_simp
  have hg1' : normSq g' = 1 := by
    rw [hg', normSq_smul, ← nrm_sq h']; field_simp
  have hcos : dotp g g' = cosv h h' := by
    rw [hg, hg', dotp_smul_smul]; unfold cosv; field_simp
  have e : h = nrm h • g := by
    rw [hg, smul_smul]; field_simp; simp
  have e' : h' = nrm h' • g' := by
    rw [hg', smul_smul]; field_simp; simp
  have key := lin_bias_unitC (n := n) hv hn hg1 hg1'
  rw [hcos] at key
  have ef : (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - cosv h h') =
      fun M => dotp (sphPt (M.mulVec g)) (sphPt (M.mulVec g')) - cosv h h' := by
    funext M
    have e1 : M.mulVec h = nrm h • M.mulVec g := by
      conv_lhs => rw [e]
      rw [Matrix.mulVec_smul]
    have e2 : M.mulVec h' = nrm h' • M.mulVec g' := by
      conv_lhs => rw [e']
      rw [Matrix.mulVec_smul]
    rw [e1, e2, sphPt_smul hp, sphPt_smul hp']
  rw [ef]
  exact key

end Lin

/-! ## The bias of the World link -/

section World

variable {N m n : ℕ}

/-- The bound of the bias of the World link. -/
noncomputable def betaWC (n m : ℕ) : ℝ := betaLinC n + 2 * epsW m + eHid m

lemma betaWC_nonneg (n m : ℕ) : 0 ≤ betaWC n m := by
  have := betaLinC_nonneg n
  have := epsW_nonneg m
  have := eHid_nonneg m
  unfold betaWC
  positivity

/-- **The bias of the World link**: for unit inputs `u, u′`,
`|E_W (⟨x(u), x(u′)⟩ − κ(κ(⟨u, u′⟩)))| ≤ betaWC n m`. -/
theorem world_biasC (hN : 1 ≤ N) (hm : 1 ≤ m) (hn : 1 ≤ n) {u u' : Fin N → ℝ}
    (hu : normSq u = 1) (hu' : normSq u' = 1) :
    |∫ W : MlpParam N m n, (dotp (xW W u) (xW W u') - kappa (kappa (dotp u u')))
      ∂mlpGauss N m n| ≤ betaWC n m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hβ := betaLinC_nonneg n
  have heH := eHid_nonneg m
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = kappa (kappa (dotp u u')) := ⟨_, rfl⟩
  have h23 := hid_cos_L2 (m := m) hN hm hu hu'
  rw [← hcdef] at h23 ⊢
  have hmeasC : Measurable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')) := measurable_cosv_hid2 u u'
  have hmeas1 : Measurable (fun z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
        Matrix (Fin n) (Fin m) ℝ =>
      dotp (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u))) (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u'))) -
        cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u')) :=
    (measurable_lastStep u u').sub (hmeasC.comp measurable_fst)
  -- the part of the last matrix
  have iF1 : Integrable (fun z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
        Matrix (Fin n) (Fin m) ℝ =>
      dotp (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u))) (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u'))) -
        cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u'))
      (((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
        (gaussMat n m (2 / (m : ℝ)))) := by
    refine Integrable.mono' (integrable_const (2 : ℝ)) hmeas1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have hc := cosv_mem (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u')
    have h1 := dotp_sphPt_ge hn (z.2.mulVec (hid2 z.1.1 z.1.2 u))
      (z.2.mulVec (hid2 z.1.1 z.1.2 u'))
    have h2 := dotp_sphPt_le hn (z.2.mulVec (hid2 z.1.1 z.1.2 u))
      (z.2.mulVec (hid2 z.1.1 z.1.2 u'))
    constructor <;> linarith [hc.1, hc.2]
  have ig : Integrable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      betaLinC n + ((if normSq (hid2 θ.1 θ.2 u) = 0 then (1 : ℝ) else 0) +
        (if normSq (hid2 θ.1 θ.2 u') = 0 then (1 : ℝ) else 0)))
      ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) :=
    (integrable_const _).add ((integrable_zero_ind u).add (integrable_zero_ind u'))
  have eg : ∫ θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ,
      (betaLinC n + ((if normSq (hid2 θ.1 θ.2 u) = 0 then (1 : ℝ) else 0) +
        (if normSq (hid2 θ.1 θ.2 u') = 0 then (1 : ℝ) else 0)))
      ∂((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) ≤
      betaLinC n + 2 * epsW m := by
    have iuu : Integrable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        (if normSq (hid2 θ.1 θ.2 u) = 0 then (1 : ℝ) else 0) +
          (if normSq (hid2 θ.1 θ.2 u') = 0 then (1 : ℝ) else 0))
        ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) :=
      (integrable_zero_ind u).add (integrable_zero_ind u')
    rw [integral_add (integrable_const _) iuu,
      integral_add (integrable_zero_ind u) (integrable_zero_ind u')]
    have z1 := hid2_zero (m := m) hN hm hu
    have z2 := hid2_zero (m := m) hN hm hu'
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith
  have b1 : |∫ z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
        Matrix (Fin n) (Fin m) ℝ,
      (dotp (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u))) (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u'))) -
        cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u'))
      ∂(((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
        (gaussMat n m (2 / (m : ℝ))))| ≤ betaLinC n + 2 * epsW m := by
    rw [integral_prod _ iF1, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le ig (Filter.Eventually.of_forall fun θ => ?_)).trans eg
    rw [Real.norm_eq_abs]
    by_cases hz : normSq (hid2 θ.1 θ.2 u) = 0 ∨ normSq (hid2 θ.1 θ.2 u') = 0
    · have hb : L2le (gaussMat n m (2 / (m : ℝ))) (fun M₃ : Matrix (Fin n) (Fin m) ℝ =>
          dotp (sphPt (M₃.mulVec (hid2 θ.1 θ.2 u))) (sphPt (M₃.mulVec (hid2 θ.1 θ.2 u'))) -
            cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')) 1 := by
        refine L2le.of_bound (hmeas1.comp measurable_prodMk_left).aestronglyMeasurable
          (fun M₃ => ?_)
        simp only [Function.comp]
        rw [cosv_of_zero hz, sub_zero, abs_le]
        exact ⟨dotp_sphPt_ge hn _ _, dotp_sphPt_le hn _ _⟩
      have h1 := l2_abs_integral_le zero_le_one hb
      refine h1.trans ?_
      rcases hz with hz | hz
      · simp only [hz, ↓reduceIte]
        have : (0 : ℝ) ≤ if normSq (hid2 θ.1 θ.2 u') = 0 then (1 : ℝ) else 0 := by
          split_ifs <;> norm_num
        linarith
      · simp only [hz, ↓reduceIte]
        have : (0 : ℝ) ≤ if normSq (hid2 θ.1 θ.2 u) = 0 then (1 : ℝ) else 0 := by
          split_ifs <;> norm_num
        linarith
    · have hz : normSq (hid2 θ.1 θ.2 u) ≠ 0 ∧ normSq (hid2 θ.1 θ.2 u') ≠ 0 :=
        ⟨fun h => hz (Or.inl h), fun h => hz (Or.inr h)⟩
      have hb := lin_biasC (n := n) (v := 2 / (m : ℝ)) (by positivity) hn
        (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') hz.1 hz.2
      simp only [hz.1, hz.2, ↓reduceIte, add_zero]
      exact hb
  -- the part of the hidden layers
  have h23' := h23.comp_fst (ν := gaussMat n m (2 / (m : ℝ)))
  have b2 := l2_abs_integral_le heH h23'
  have iF2 := l2_integrable h23'
  -- the change of variables
  have hmap : (mlpGauss N m n).map (MeasurableEquiv.prodAssoc (α := Matrix (Fin m) (Fin N) ℝ)
      (β := Matrix (Fin m) (Fin m) ℝ) (γ := Matrix (Fin n) (Fin m) ℝ)).symm =
      ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
        (gaussMat n m (2 / (m : ℝ))) := by
    unfold mlpGauss
    rw [← Measure.prodAssoc_prod, MeasurableEquiv.map_symm_map]
  have hint : ∫ W : MlpParam N m n, (dotp (xW W u) (xW W u') - c) ∂mlpGauss N m n =
      ∫ z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) × Matrix (Fin n) (Fin m) ℝ,
        ((dotp (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u)))
          (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u'))) -
          cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u')) +
          (cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u') - c))
        ∂(((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
          (gaussMat n m (2 / (m : ℝ)))) := by
    rw [← hmap, integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    change dotp (xW W u) (xW W u') - c =
      dotp (sphPt (W.2.2.mulVec (hid2 W.1 W.2.1 u))) (sphPt (W.2.2.mulVec (hid2 W.1 W.2.1 u'))) -
        cosv (hid2 W.1 W.2.1 u) (hid2 W.1 W.2.1 u') +
        (cosv (hid2 W.1 W.2.1 u) (hid2 W.1 W.2.1 u') - c)
    have : dotp (xW W u) (xW W u') = dotp (sphPt (W.2.2.mulVec (hid2 W.1 W.2.1 u)))
        (sphPt (W.2.2.mulVec (hid2 W.1 W.2.1 u'))) := rfl
    rw [this]
    ring
  rw [hint, integral_add iF1 iF2]
  unfold betaWC
  exact (abs_add_le _ _).trans (by linarith)

end World

/-! ## The widths of the Focus -/

/-- The World link after the average over the inputs, with the sharper link of the inputs. -/
noncomputable def eWr2C (N n mW : ℕ) : ℝ :=
  1 / √(n : ℝ) * (1 - kappa (kappa 0) ^ 2 + 2 * sU2 N) + eWsmallC n mW

lemma eWr2C_nonneg (N n mW : ℕ) : 0 ≤ eWr2C N n mW := by
  have hq := q_mem
  have hsU := sU2_nonneg N
  have hsm := eWsmallC_nonneg n mW
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  unfold eWr2C
  positivity

/-- **`‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂ ≤ √(eWr2C² + sU2² + 2·sU2·betaWC)`**, all widths. -/
theorem tX_L2_gen2C {N mW n : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) (hmW : 1 ≤ mW) :
    L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0))
      (√(eWr2C N n mW ^ 2 + sU2 N ^ 2 + 2 * sU2 N * betaWC n mW)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmW' : (0 : ℝ) < mW := by exact_mod_cast hmW
  have hsU := sU2_nonneg N
  have hsm := eWsmallC_nonneg n mW
  have := lawU2_prob hN
  have hU : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) (sU2 N) := sphere_kk_L2s hN
  have hW : ∀ v v' : Fin N → ℝ, normSq v = 1 → normSq v' = 1 →
      L2le (mlpGauss N mW n)
        (fun W : MlpParam N mW n => dotp (xW W v) (xW W v') - kappa (kappa (dotp v v')))
        ((fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmallC n mW) (dotp v v')) := by
    intro v v' hv hv'
    have hJ : 0 ≤ jCosC n := jCosC_nonneg n
    have h := world_cos_L2g hN hmW hn hJ (fun h h' hh hh' =>
      lin_cos_L2c (v := 2 / (mW : ℝ)) (by positivity) hn h h' hh hh') hv hv'
    refine h.congr_bound ?_
    unfold eWsmallC
    ring
  have hgW : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      (fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmallC n mW) (dotp uu.1 uu.2))
      (eWr2C N n mW) := by
    have h1 := sphere_gW_L2_of hN (1 / √(n : ℝ)) (by positivity) hsU hU
    have h2 : L2le (lawU2 N) (fun _ : (Fin N → ℝ) × (Fin N → ℝ) => eWsmallC n mW)
        (eWsmallC n mW) := ⟨aestronglyMeasurable_const, integrable_const _, by simp⟩
    have hq := q_mem
    have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
    have h3 := h1.add0 h2 (by positivity) hsm
    exact h3
  exact tX_L2_bias (gW := fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmallC n mW)
    hN (eWr2C_nonneg N n mW) hsU (betaWC_nonneg n mW) hW hgW hU
    (fun v v' hv hv' => world_biasC hN hmW hn hv hv')

/-- The sharper bound of `‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂` at the widths of the Focus, `r = 2`. -/
noncomputable def tau143sC (n : ℕ) : ℝ :=
  √(eWr2C (2 * n) n (mW n) ^ 2 + sU2 (2 * n) ^ 2 + 2 * sU2 (2 * n) * betaWC n (mW n))

lemma tau143sC_nonneg (n : ℕ) : 0 ≤ tau143sC n := Real.sqrt_nonneg _

/-- **`‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂ ≤ tau143sC n`** at the widths of the Focus, `n ≥ 4096`. -/
theorem tX_L2_145C {n : ℕ} (hn : 4096 ≤ n) :
    L2le ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (fun z : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n =>
        tX z - kappa (kappa 0)) (tau143sC n) := by
  have hmW : 1 ≤ mW n := by have := mW_ge hn; omega
  exact tX_L2_gen2C (by omega) (by omega) hmW

end BstLean.Part145

open BstLean.Part145 in
#print axioms lin_biasC
open BstLean.Part145 in
#print axioms world_biasC
open BstLean.Part145 in
#print axioms tX_L2_145C
