import BstLean.Part142Final

/-!
# Part 143, helper `world`: the squares of the World link and of the link of the inputs add

`tX z = ⟨x(u), x(u′)⟩`, `x(u) = W(u)/|W(u)|`, `q = κ(κ(0))`. Part 142 (`tX_L2_focus`) has
`‖tX − q‖₂ ≤ eWr + sU` by the triangle inequality for `tX − q = X + U`,
`X = tX − κ(κ(⟨u, u′⟩))`, `U = κ(κ(⟨u, u′⟩)) − q`. Here `E(X + U)² = E X² + E U² + 2·E[U·b]`
with `b(u, u′) = E_W X` the bias of the World link, and `|b| ≤ betaW`.

* `l2_abs_integral_le`, `l2_abs_integral_mul_le` (Cauchy–Schwarz for `L2le`).
* `betaLin n = 2K₄(n)/n + (1/√n + jCos n)·(√2/√n + 2K₄(n)/n)`; `lin_bias_unit`, `lin_bias`:
  `|E_M (⟨sphPt (M h), sphPt (M h′)⟩ − cos(h, h′))| ≤ betaLin n` (second order).
* `betaW n m = betaLin n + 2·epsW m + eHid m`; `world_bias`:
  `|E_W (⟨x(v), x(v′)⟩ − κ(κ(⟨v, v′⟩)))| ≤ betaW n m` for unit `v, v′`.
* `tX_L2_bias`: the general lemma, bound `√(w² + u² + 2·u·β)`.
* `tau143 n = √(eWr(2n, n, m_W)² + sU(2n)² + 2·sU(2n)·betaW n m_W)`; **`tX_L2_143`**;
  **`tau143_le`**: `tau143 n ≤ 1.055/√n` for `n ≥ 16384` (Part 142: `eWr + sU`, `1.3264/√n`).
  Numbers for `n ≥ 16384`: `sU(2n) ≤ 0.3607/√n`, `eWr ≤ 0.9657/√n`, `betaLin n ≤ 8.698/n`,
  `betaW n m_W ≤ 0.0684/√n`.
* Sharper link of the inputs (secant of `κ∘κ` on `[0, 1/8]`): `kk_eighth_le`
  (`κ(κ(1/8)) ≤ 0.5337`), `kk_abs2` (`|κκ(s) − κκ(0)| ≤ 0.32|s| + 1.49024·s²`),
  `sU2 N = 0.32/√N + 1.49024·√3/N`, `sphere_kk_L2s`, `eWr2` (`eWr` with `sU2`),
  `tau143s n = √(eWr2² + sU2² + 2·sU2·betaW)`; **`tX_L2_143s`** (`n ≥ 4096`);
  **`tau143s_le`**: `tau143s n ≤ 1.009/√n` for `n ≥ 16384` (`sU2(2n) ≤ 0.2364/√n`,
  `eWr2 ≤ 0.9638/√n`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
open BstLean.Part142

/-! ## Generic facts on `L2le` -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma l2_integrable [IsFiniteMeasure μ] {f : Ω → ℝ} {a : ℝ} (h : L2le μ f a) :
    Integrable f μ := by
  refine Integrable.mono' (h.int_sq.add (integrable_const (1 : ℝ))) h.aesm
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (|f ω| - 1), sq_abs (f ω), abs_nonneg (f ω)]

lemma l2_abs_integral_le [IsProbabilityMeasure μ] {f : Ω → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : L2le μ f a) : |∫ ω, f ω ∂μ| ≤ a :=
  abs_le_of_sq_le_sq ((sq_integral_le h.int_sq).trans h.le) ha

lemma l2_mul_integrable {f g : Ω → ℝ} {a b : ℝ} (hf : L2le μ f a) (hg : L2le μ g b) :
    Integrable (fun ω => f ω * g ω) μ := by
  refine Integrable.mono' (hf.int_sq.add hg.int_sq) (hf.aesm.mul hg.aesm)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (|f ω| - |g ω|), sq_abs (f ω), sq_abs (g ω),
    mul_nonneg (abs_nonneg (f ω)) (abs_nonneg (g ω))]

/-- **Cauchy–Schwarz** for `L2le`. -/
lemma l2_abs_integral_mul_le {f g : Ω → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : L2le μ f a) (hg : L2le μ g b) : |∫ ω, f ω * g ω ∂μ| ≤ a * b := by
  have hfg := l2_mul_integrable hf hg
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∫ ω, f ω ^ 2 ∂μ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∫ ω, g ω ^ 2 ∂μ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∫ ω, f ω * g ω ∂μ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := hA ▸ integral_nonneg fun ω => sq_nonneg _
  have hB0 : 0 ≤ B := hB ▸ integral_nonneg fun ω => sq_nonneg _
  have hAa : A ≤ a ^ 2 := hA ▸ hf.le
  have hBb : B ≤ b ^ 2 := hB ▸ hg.le
  have hq : ∀ t : ℝ, 0 ≤ A * (t * t) + (-(2 * C)) * t + B := by
    intro t
    have e : (fun ω => (t * f ω - g ω) ^ 2) =
        fun ω => t ^ 2 * f ω ^ 2 - 2 * t * (f ω * g ω) + g ω ^ 2 := by
      funext ω; ring
    have h0 : 0 ≤ ∫ ω, (t * f ω - g ω) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have i1 : Integrable (fun ω => t ^ 2 * f ω ^ 2) μ := hf.int_sq.const_mul _
    have i2 : Integrable (fun ω => 2 * t * (f ω * g ω)) μ := hfg.const_mul _
    have i12 : Integrable (fun ω => t ^ 2 * f ω ^ 2 - 2 * t * (f ω * g ω)) μ := i1.sub i2
    rw [e, integral_add i12 hg.int_sq, integral_sub i1 i2, integral_const_mul,
      integral_const_mul, ← hA, ← hB, ← hC] at h0
    linarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  rw [← hC]
  have h1 : A * B ≤ a ^ 2 * b ^ 2 := mul_le_mul hAa hBb hB0 (sq_nonneg a)
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg ha hb)
  nlinarith

end Generic

/-! ## The bias of the last matrix: second order -/

/-- The bound of the bias of the cosine link of one linear layer with `n` rows. -/
noncomputable def betaLin (n : ℕ) : ℝ :=
  2 * K4 n / (n : ℝ) + (1 / √(n : ℝ) + jCos n) * (√2 / √(n : ℝ) + 2 * K4 n / (n : ℝ))

lemma betaLin_nonneg (n : ℕ) : 0 ≤ betaLin n := by
  have := K4_nonneg n
  unfold betaLin jCos
  positivity

variable {n k : ℕ}

/-- **The bias of the cosine of a linear layer, unit inputs.** -/
theorem lin_bias_unit {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) {h h' : Fin k → ℝ}
    (hh : normSq h = 1) (hh' : normSq h' = 1) :
    |∫ M : Matrix (Fin n) (Fin k) ℝ,
      (dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - dotp h h') ∂gaussMat n k v| ≤
      betaLin n := by
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
  have hJ0 : 0 ≤ jCos n := by unfold jCos; positivity
  -- `D`
  have hD : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - τ) (1 / √(n : ℝ) + jCos n) := by
    have h0 := lin_cos_unit_L2b (n := n) hv hn hh hh'
    rw [← hτdef] at h0
    refine h0.mono (by positivity) ?_
    have : (1 - τ ^ 2) / √(n : ℝ) ≤ 1 / √(n : ℝ) :=
      div_le_div_of_nonneg_right (by nlinarith [sq_nonneg τ]) hsn.le
    unfold jCos
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
  unfold betaLin
  exact (abs_add_le _ _).trans (add_le_add b3 b2)

/-- **The bias of the cosine of a linear layer**, nonzero inputs. -/
theorem lin_bias {n k : ℕ} {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) (h h' : Fin k → ℝ)
    (hh : normSq h ≠ 0) (hh' : normSq h' ≠ 0) :
    |∫ M : Matrix (Fin n) (Fin k) ℝ,
      (dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - cosv h h') ∂gaussMat n k v| ≤
      betaLin n := by
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
  have key := lin_bias_unit (n := n) hv hn hg1 hg1'
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

/-! ## The bias of the World link -/

section World

variable {N m n : ℕ}

/-- The hidden layers of `W` in `L²` (the steps (ii), (iii) of `world_cos_L2g`). -/
lemma hid_cos_L2 (hN : 1 ≤ N) (hm : 1 ≤ m) {u u' : Fin N → ℝ} (hu : normSq u = 1)
    (hu' : normSq u' = 1) :
    L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
      (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') - kappa (kappa (dotp u u'))) (eHid m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := sH_pos hN hm
  have heps := epsW_pos hm
  have hk0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = kappa (kappa (dotp u u')) := ⟨_, rfl⟩
  obtain ⟨cH, hcH⟩ : ∃ c : ℝ, c = √6 * √(1 + 5 / (m : ℝ)) / √(m : ℝ) +
      (5 * kappa 0 + √6) / √(m : ℝ) := ⟨_, rfl⟩
  have hcHpos : 0 < cH := by
    rw [hcH]
    have h6 : (0 : ℝ) < √6 := by positivity
    have : 0 < (5 * kappa 0 + √6) / √(m : ℝ) := div_pos (by linarith) (by positivity)
    have : 0 ≤ √6 * √(1 + 5 / (m : ℝ)) / √(m : ℝ) := by positivity
    linarith
  have hmeasC : Measurable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')) := measurable_cosv_hid2 u u'
  have h2 : L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
      (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') -
          dotp (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') / sH N m) (√(5 * epsW m)) := by
    obtain ⟨iP, uP⟩ := hid2_pair hN hm hu hu'
    have hmd : Measurable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        dotp (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')) :=
      measurable_dotp_comp (continuous_hid2_param u).measurable
        (continuous_hid2_param u').measurable
    refine L2le.of_sq_le (hmeasC.sub (hmd.div_const _)).aestronglyMeasurable
      (iP.const_mul (1 / sH N m ^ 2)) (fun θ => ?_) ?_
    · have hc := cosv_mem (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')
      have hc2 : cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') ^ 2 ≤ 1 := by nlinarith [hc.1, hc.2]
      rw [dotp_eq_cosv_mul (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')]
      have e : (cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') -
          cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') *
            (nrm (hid2 θ.1 θ.2 u) * nrm (hid2 θ.1 θ.2 u')) / sH N m) ^ 2 =
          cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') ^ 2 * (1 / sH N m ^ 2 *
            (nrm (hid2 θ.1 θ.2 u) * nrm (hid2 θ.1 θ.2 u') - sH N m) ^ 2) := by
        have : sH N m ≠ 0 := hs.ne'
        field_simp
        ring
      rw [e]
      exact mul_le_of_le_one_left (by positivity) hc2
    · rw [integral_const_mul, Real.sq_sqrt (by positivity)]
      have := mul_le_mul_of_nonneg_left uP (by positivity : (0 : ℝ) ≤ 1 / sH N m ^ 2)
      refine this.trans (le_of_eq ?_)
      have : sH N m ≠ 0 := hs.ne'
      field_simp
  have h3 : L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
      (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        dotp (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') / sH N m - c) cH := by
    have h := (hid2_dot_L2 (two_div_nonneg N) (two_div_nonneg m) hm hm u u').const_mul_nonneg
      (c := 1 / sH N m) (by positivity)
    rw [psi_unit _ hu hu', nrm_of_normSq_one hu, nrm_of_normSq_one hu'] at h
    have hne : sH N m ≠ 0 := hs.ne'
    refine (h.congr_fun fun θ => ?_).congr_bound ?_
    · simp only [Function.comp, hcdef]
      unfold sH at hne ⊢
      field_simp
    · rw [hcH]
      unfold sH at hne ⊢
      field_simp
  rw [← hcdef]
  have := h2.add h3 (by positivity) hcHpos
  refine (this.congr_fun fun θ => by ring).congr_bound ?_
  unfold eHid
  rw [hcH]

/-- The bound of the bias of the World link. -/
noncomputable def betaW (n m : ℕ) : ℝ := betaLin n + 2 * epsW m + eHid m

lemma betaW_nonneg (n m : ℕ) : 0 ≤ betaW n m := by
  have := betaLin_nonneg n
  have := epsW_nonneg m
  have := eHid_nonneg m
  unfold betaW
  positivity

/-- **The bias of the World link**: for unit inputs `u, u′`,
`|E_W (⟨x(u), x(u′)⟩ − κ(κ(⟨u, u′⟩)))| ≤ betaW n m`. -/
theorem world_bias (hN : 1 ≤ N) (hm : 1 ≤ m) (hn : 1 ≤ n) {u u' : Fin N → ℝ}
    (hu : normSq u = 1) (hu' : normSq u' = 1) :
    |∫ W : MlpParam N m n, (dotp (xW W u) (xW W u') - kappa (kappa (dotp u u')))
      ∂mlpGauss N m n| ≤ betaW n m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hβ := betaLin_nonneg n
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
      betaLin n + ((if normSq (hid2 θ.1 θ.2 u) = 0 then (1 : ℝ) else 0) +
        (if normSq (hid2 θ.1 θ.2 u') = 0 then (1 : ℝ) else 0)))
      ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) :=
    (integrable_const _).add ((integrable_zero_ind u).add (integrable_zero_ind u'))
  have eg : ∫ θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ,
      (betaLin n + ((if normSq (hid2 θ.1 θ.2 u) = 0 then (1 : ℝ) else 0) +
        (if normSq (hid2 θ.1 θ.2 u') = 0 then (1 : ℝ) else 0)))
      ∂((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) ≤
      betaLin n + 2 * epsW m := by
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
        (gaussMat n m (2 / (m : ℝ))))| ≤ betaLin n + 2 * epsW m := by
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
      have hb := lin_bias (n := n) (v := 2 / (m : ℝ)) (by positivity) hn
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
  unfold betaW
  exact (abs_add_le _ _).trans (by linarith)

end World

/-! ## The squares add, up to the bias -/

/-- **The cosine of the two inputs of `A` around its centre, with the squares added**:
`‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂ ≤ √(w² + u² + 2·u·β)`, from the World link (`w`), the link of the
inputs (`u`) and a bound `β` of the bias of the World link. -/
theorem tX_L2_bias {N mW n : ℕ} {w u β : ℝ} {gW : ℝ → ℝ} (hN : 1 ≤ N) (hw : 0 ≤ w)
    (hu : 0 ≤ u) (hβ : 0 ≤ β)
    (hW : ∀ v v' : Fin N → ℝ, normSq v = 1 → normSq v' = 1 →
      L2le (mlpGauss N mW n)
        (fun W : MlpParam N mW n => dotp (xW W v) (xW W v') - kappa (kappa (dotp v v')))
        (gW (dotp v v')))
    (hgW : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => gW (dotp uu.1 uu.2)) w)
    (hU : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) u)
    (hb : ∀ v v' : Fin N → ℝ, normSq v = 1 → normSq v' = 1 →
      |∫ W : MlpParam N mW n, (dotp (xW W v) (xW W v') - kappa (kappa (dotp v v')))
        ∂mlpGauss N mW n| ≤ β) :
    L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0))
      (√(w ^ 2 + u ^ 2 + 2 * u * β)) := by
  have := lawU2_prob hN
  have hkk : Measurable (fun t : ℝ => kappa (kappa t)) :=
    (continuous_kappa.comp continuous_kappa).measurable
  have md : Measurable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      dotp z.1.1 z.1.2) :=
    measurable_dotp_comp (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)
  have m2 : Measurable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      tX z - kappa (kappa (dotp z.1.1 z.1.2))) := measurable_tX.sub (hkk.comp md)
  have A2 : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        tX z - kappa (kappa (dotp z.1.1 z.1.2))) w := by
    refine L2le.prod' m2.aestronglyMeasurable hgW ?_
    filter_upwards [lawU2_ae_unit hN] with uu huu
    exact hW uu.1 uu.2 huu.1 huu.2
  have A3 : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        kappa (kappa (dotp z.1.1 z.1.2)) - kappa (kappa 0)) u :=
    hU.comp_fst (ν := mlpGauss N mW n)
  have hsum : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0))
      (w + u) := (A2.add0 A3 hw hu).congr_fun fun z => by ring
  refine ⟨hsum.aesm, hsum.int_sq, ?_⟩
  rw [Real.sq_sqrt (by positivity)]
  have iUX : Integrable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      (kappa (kappa (dotp z.1.1 z.1.2)) - kappa (kappa 0)) *
        (tX z - kappa (kappa (dotp z.1.1 z.1.2)))) ((lawU2 N).prod (mlpGauss N mW n)) :=
    l2_mul_integrable A3 A2
  have e1 : (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      (tX z - kappa (kappa 0)) ^ 2) = fun z =>
      ((tX z - kappa (kappa (dotp z.1.1 z.1.2))) ^ 2 +
        (kappa (kappa (dotp z.1.1 z.1.2)) - kappa (kappa 0)) ^ 2) +
      2 * ((kappa (kappa (dotp z.1.1 z.1.2)) - kappa (kappa 0)) *
        (tX z - kappa (kappa (dotp z.1.1 z.1.2)))) := by
    funext z; ring
  have i1 : Integrable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      (tX z - kappa (kappa (dotp z.1.1 z.1.2))) ^ 2 +
        (kappa (kappa (dotp z.1.1 z.1.2)) - kappa (kappa 0)) ^ 2)
      ((lawU2 N).prod (mlpGauss N mW n)) := A2.int_sq.add A3.int_sq
  have i2 : Integrable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      2 * ((kappa (kappa (dotp z.1.1 z.1.2)) - kappa (kappa 0)) *
        (tX z - kappa (kappa (dotp z.1.1 z.1.2))))) ((lawU2 N).prod (mlpGauss N mW n)) :=
    iUX.const_mul 2
  rw [e1, integral_add i1 i2, integral_add A2.int_sq A3.int_sq, integral_const_mul]
  -- the cross term
  have iU : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      β * |kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)|) (lawU2 N) :=
    (l2_integrable (Part142.L2le.abs' hU)).const_mul β
  have bU : ∫ uu : (Fin N → ℝ) × (Fin N → ℝ),
      β * |kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)| ∂lawU2 N ≤ β * u := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (l2_abs_integral_le hu (Part142.L2le.abs' hU))) hβ
  have hcross : |∫ z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n,
      (kappa (kappa (dotp z.1.1 z.1.2)) - kappa (kappa 0)) *
        (tX z - kappa (kappa (dotp z.1.1 z.1.2))) ∂((lawU2 N).prod (mlpGauss N mW n))| ≤
      β * u := by
    rw [integral_prod _ iUX, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le iU ?_).trans bU
    filter_upwards [lawU2_ae_unit hN] with uu huu
    have e : ∫ W : MlpParam N mW n, (kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) *
        (tX (uu, W) - kappa (kappa (dotp uu.1 uu.2))) ∂mlpGauss N mW n =
        (kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) *
          ∫ W : MlpParam N mW n, (dotp (xW W uu.1) (xW W uu.2) -
            kappa (kappa (dotp uu.1 uu.2))) ∂mlpGauss N mW n := by
      rw [← integral_const_mul]
      rfl
    rw [Real.norm_eq_abs]
    refine (le_of_eq (congrArg abs e)).trans ?_
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hb uu.1 uu.2 huu.1 huu.2) (abs_nonneg _)
  have h1 := A2.le
  have h2 := A3.le
  have h3 := (abs_le.mp hcross).2
  linarith

/-! ## The widths of the Focus -/

/-- The bound of `‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂` of Part 143 at the widths of the Focus, `r = 2`. -/
noncomputable def tau143 (n : ℕ) : ℝ :=
  √(eWr (2 * n) n (mW n) ^ 2 + sU (2 * n) ^ 2 + 2 * sU (2 * n) * betaW n (mW n))

lemma tau143_nonneg (n : ℕ) : 0 ≤ tau143 n := Real.sqrt_nonneg _

/-- **`‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂ ≤ √(eWr² + sU² + 2·sU·betaW)`**, all widths. -/
theorem tX_L2_gen {N mW n : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) (hmW : 1 ≤ mW) :
    L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0))
      (√(eWr N n mW ^ 2 + sU N ^ 2 + 2 * sU N * betaW n mW)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmW' : (0 : ℝ) < mW := by exact_mod_cast hmW
  have hq := q_mem
  have hsU := sU_nonneg N
  have hsm := eWsmall_nonneg n mW
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  have := lawU2_prob hN
  have hW : ∀ v v' : Fin N → ℝ, normSq v = 1 → normSq v' = 1 →
      L2le (mlpGauss N mW n)
        (fun W : MlpParam N mW n => dotp (xW W v) (xW W v') - kappa (kappa (dotp v v')))
        ((fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmall n mW) (dotp v v')) := by
    intro v v' hv hv'
    have hJ : 0 ≤ jCos n := by unfold jCos; positivity
    have h := world_cos_L2g hN hmW hn hJ (fun h h' hh hh' =>
      lin_cos_L2b (v := 2 / (mW : ℝ)) (by positivity) hn h h' hh hh') hv hv'
    refine h.congr_bound ?_
    unfold eWsmall
    ring
  have hgW : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      (fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmall n mW) (dotp uu.1 uu.2))
      (eWr N n mW) := by
    have h1 := sphere_gW_L2 hN (1 / √(n : ℝ)) (by positivity)
    have h2 : L2le (lawU2 N) (fun _ : (Fin N → ℝ) × (Fin N → ℝ) => eWsmall n mW)
        (eWsmall n mW) := ⟨aestronglyMeasurable_const, integrable_const _, by simp⟩
    have h3 := h1.add0 h2 (by unfold sU at hsU; positivity) hsm
    exact h3
  have hU : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) (sU N) := sphere_kk_L2r hN
  have hW0 : 0 ≤ eWr N n mW := by unfold eWr; positivity
  exact tX_L2_bias (gW := fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmall n mW)
    hN hW0 hsU (betaW_nonneg n mW) hW hgW hU
    (fun v v' hv hv' => world_bias hN hmW hn hv hv')

/-- **`‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂ ≤ tau143 n`** at the widths of the Focus, `n ≥ 4096`. -/
theorem tX_L2_143' {n : ℕ} (hn : 4096 ≤ n) :
    L2le ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (fun z : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n =>
        tX z - kappa (kappa 0)) (tau143 n) := by
  have hmW : 1 ≤ mW n := by have := mW_ge hn; omega
  exact tX_L2_gen (by omega) (by omega) hmW

/-- **`‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂ ≤ tau143 n`** at the widths of the Focus. -/
theorem tX_L2_143 {n : ℕ} (hn : 16384 ≤ n) :
    L2le ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (fun z : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n =>
        tX z - kappa (kappa 0)) (tau143 n) :=
  tX_L2_143' (by omega)

/-! ## The numbers for `n ≥ 16384` -/

section num

variable {n : ℕ} (hn : 16384 ≤ n)

include hn

lemma nR_ge16W : (16384 : ℝ) ≤ n := by exact_mod_cast hn

lemma sqrt_n_ge16W : (128 : ℝ) ≤ √(n : ℝ) := by
  have hx := nR_ge16W hn
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- `y = 1/n`, `z = 1/√n`, `r = 1/√(2n)` for `n ≥ 16384`. -/
lemma yz16W : ∃ y z r : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧ r = 1 / √(2 * (n : ℝ)) ∧
    0 < y ∧ 0 < z ∧ 0 < r ∧ z ≤ 1 / 128 ∧ r ≤ 707107 / 1000000 * z ∧
    y = z * z ∧ y ≤ 1 / 128 * z := by
  have hx := nR_ge16W hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge16W hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h2 : (14142135 : ℝ) / 10000000 ≤ √2 := (Real.le_sqrt' (by norm_num)).2 (by norm_num)
  have h20 : (0 : ℝ) < √2 := by linarith
  have e2 : √(2 * (n : ℝ)) = √2 * √(n : ℝ) := Real.sqrt_mul (by norm_num) _
  have hz1 : 1 / √(n : ℝ) ≤ 1 / 128 := one_div_le_one_div_of_le (by norm_num) hs
  have hyz : 1 / (n : ℝ) = 1 / √(n : ℝ) * (1 / √(n : ℝ)) := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hx0.le]
  have hz0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  refine ⟨1 / (n : ℝ), 1 / √(n : ℝ), 1 / √(2 * (n : ℝ)), rfl, rfl, rfl, by positivity,
    hz0, by positivity, hz1, ?_, hyz, ?_⟩
  · rw [e2, div_le_iff₀ (by positivity)]
    have e : 707107 / 1000000 * (1 / √(n : ℝ)) * (√2 * √(n : ℝ)) = 707107 / 1000000 * √2 := by
      field_simp
    rw [e]
    nlinarith
  · rw [hyz]
    exact mul_le_mul_of_nonneg_right hz1 hz0.le

lemma K4_le16W : K4 n ≤ 34646 / 10000 := by
  have hx := nR_ge16W hn
  unfold K4
  refine sqrt_le_of_sq (by norm_num) ?_
  have : 48 / (n : ℝ) ≤ 48 / 16384 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this ⊢
  linarith

/-- `sU(2n) ≤ 0.3607/√n` for `n ≥ 16384`. -/
lemma sU_16W : sU (2 * n) ≤ 3607 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yz16W hn
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h3 := Part133.sqrt3_le
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  unfold sU
  rw [hc]
  refine le_trans (le_of_eq (?_ : _ = 507 / 1000 * r + 8 / 25 * √3 / 2 * y)) ?_
  · rw [hr, hy]; ring
  · refine le_trans (?_ : _ ≤ 3607 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    have p : 8 / 25 * √3 / 2 * y ≤ 8 / 25 * (17321 / 10000) / 2 * (1 / 128 * z) :=
      mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
    linarith

/-- The hidden layers of `W`: `eHid (m_W) ≤ (429/10⁶)/√n`, `√(epsW m_W) ≤ (102/10⁶)/√n` and
`epsW m_W ≤ (11/2³⁰)/n` (as `eHid_u` of Part 142). -/
lemma eHid_16W :
    eHid (mW n) ≤ 429 / 1000000 * (1 / √(n : ℝ)) ∧
      √(epsW (mW n)) ≤ 102 / 1000000 * (1 / √(n : ℝ)) ∧
      epsW (mW n) ≤ 11 / 1073741824 * (1 / (n : ℝ)) := by
  have hn4 : 4096 ≤ n := by omega
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn4
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hε := epsW_scale hn4
  have hε0 := epsW_nonneg (mW n)
  have hsW := sqrt_mW_scale hn4
  have hsW0 : (0 : ℝ) < √(mW n : ℝ) := by nlinarith
  have hm := mW_geR hn4
  have hm0 : (0 : ℝ) < mW n := by linarith
  have hk := kappa_zero_le
  have hk0 : 0 ≤ kappa 0 := (kappa_mem (t := 0) (by norm_num) (by norm_num)).1
  have h6 := Part133.sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  set u : ℝ := 1 / √(n : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have s1 : √(5 * epsW (mW n)) ≤ 23 / 100000 * u := by
    have := sqrt_le_div_s hn4 (x := 5 * epsW (mW n)) (c := 23 / 100000) (by norm_num)
      (by nlinarith)
    rwa [div_eq_mul_one_div, ← hu] at this
  have s2 : √(epsW (mW n)) ≤ 102 / 1000000 * u := by
    have := sqrt_le_div_s hn4 (x := epsW (mW n)) (c := 102 / 1000000) (by norm_num)
      (by nlinarith)
    rwa [div_eq_mul_one_div, ← hu] at this
  have h5 : 5 / (mW n : ℝ) ≤ 1 / 1000 := by
    rw [div_le_iff₀ hm0]; linarith
  have s3 : √(1 + 5 / (mW n : ℝ)) ≤ 1 + 1 / 1000 := sqrt_le_of_sq (by norm_num) (by linarith)
  have s30 := Real.sqrt_nonneg (1 + 5 / (mW n : ℝ))
  have hiW : 1 / √(mW n : ℝ) ≤ 1 / 32768 * u := by
    rw [hu, div_mul_div_comm, mul_one]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsW
  have hiW0 : 0 ≤ 1 / √(mW n : ℝ) := by positivity
  have t2 : √6 * √(1 + 5 / (mW n : ℝ)) / √(mW n : ℝ) ≤
      24495 / 10000 * (1 + 1 / 1000) * (1 / 32768 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul h6 s3 s30 (by norm_num)) hiW hiW0 (by norm_num)
  have t3 : (5 * kappa 0 + √6) / √(mW n : ℝ) ≤
      (5 * (31831 / 100000) + 24495 / 10000) * (1 / 32768 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hiW hiW0 (by norm_num)
  refine ⟨?_, s2, ?_⟩
  · unfold eHid
    linarith
  · rw [mul_one_div, le_div_iff₀ hx0]
    exact hε

/-- `jCos n ≤ 0.2031/√n` for `n ≥ 16384`. -/
lemma jCos_16W : jCos n ≤ 2031 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yz16W hn
  have hK := K4_le16W hn
  have hK0 := K4_nonneg n
  have t1 : 15 / 2 * K4 n * y ≤ 15 / 2 * (34646 / 10000) * (1 / 128 * z) :=
    mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
  unfold jCos
  refine le_trans (le_of_eq (?_ : _ = 15 / 2 * K4 n * y)) ?_
  · rw [hy]; unfold K4; ring
  · refine le_trans (?_ : _ ≤ 2031 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    linarith

/-- `eWsmall n m_W ≤ 0.2038/√n` for `n ≥ 16384`. -/
lemma eWsmall_16W : eWsmall n (mW n) ≤ 2038 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yz16W hn
  obtain ⟨hH, hE, -⟩ := eHid_16W hn
  rw [← hz] at hH hE
  have hH0 := eHid_nonneg (mW n)
  have hJ := jCos_16W hn
  have eJ : (2031 : ℝ) / 10000 / √(n : ℝ) = 2031 / 10000 * z := by rw [hz]; ring
  rw [eJ] at hJ
  have t5 : (1 + 2 * z) * eHid (mW n) ≤ (1 + 2 / 128) * (429 / 1000000 * z) :=
    mul_le_mul (by linarith) hH hH0 (by norm_num)
  unfold eWsmall
  refine le_trans (le_of_eq (?_ : _ = jCos n + (1 + 2 * z) * eHid (mW n) +
    2 * √(epsW (mW n)))) ?_
  · rw [hz]; ring
  · refine le_trans (?_ : _ ≤ 2038 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    linarith

/-- `eWr(2n, n, m_W) ≤ 0.9657/√n` for `n ≥ 16384`. -/
lemma eWr_16W : eWr (2 * n) n (mW n) ≤ 9657 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yz16W hn
  have h1 := sU_16W hn
  have h10 := sU_nonneg (2 * n)
  have h2 := eWsmall_16W hn
  have hq := kappa2_zero_ge
  have hq1 := q_mem.2
  have hq2 : 1 - kappa (kappa 0) ^ 2 ≤ 1 - (49372 / 100000) ^ 2 := by nlinarith
  have e1 : (3607 : ℝ) / 10000 / √(n : ℝ) = 3607 / 10000 * z := by rw [hz]; ring
  have e2 : (2038 : ℝ) / 10000 / √(n : ℝ) = 2038 / 10000 * z := by rw [hz]; ring
  rw [e1] at h1
  rw [e2] at h2
  have h1' : sU (2 * n) ≤ 3607 / 10000 / 128 := by linarith
  have t2 : z * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) ≤
      z * (1 - (49372 / 100000) ^ 2 + 2 * (3607 / 10000 / 128)) :=
    mul_le_mul_of_nonneg_left (by linarith) hz0.le
  unfold eWr
  refine le_trans (le_of_eq (?_ : _ = z * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) +
    eWsmall n (mW n))) ?_
  · rw [hz]
  · refine le_trans (?_ : _ ≤ 9657 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    nlinarith

/-- `betaLin n ≤ 8.698/n` for `n ≥ 16384`. -/
lemma betaLin_16W : betaLin n ≤ 8698 / 1000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yz16W hn
  have hK := K4_le16W hn
  have hK0 := K4_nonneg n
  have hJ := jCos_16W hn
  have hJ0 : 0 ≤ jCos n := by unfold jCos; positivity
  have eJ : (2031 : ℝ) / 10000 / √(n : ℝ) = 2031 / 10000 * z := by rw [hz]; ring
  rw [eJ] at hJ
  have h2 := Part133.sqrt2_le
  have h20 := Real.sqrt_nonneg (2 : ℝ)
  have a1 : 2 * K4 n * y ≤ 2 * (34646 / 10000) * y :=
    mul_le_mul_of_nonneg_right (by linarith) hy0.le
  have a2 : z + jCos n ≤ 12031 / 10000 * z := by linarith
  have a3 : √2 * z + 2 * K4 n * y ≤ 14684 / 10000 * z := by
    have b1 : √2 * z ≤ 141422 / 100000 * z := mul_le_mul_of_nonneg_right h2 hz0.le
    have b2 : 2 * K4 n * y ≤ 2 * (34646 / 10000) * (1 / 128 * z) :=
      mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
    linarith
  have a4 : (z + jCos n) * (√2 * z + 2 * K4 n * y) ≤
      12031 / 10000 * z * (14684 / 10000 * z) :=
    mul_le_mul a2 a3 (by positivity) (by positivity)
  unfold betaLin
  refine le_trans (le_of_eq (?_ : _ = 2 * K4 n * y +
    (z + jCos n) * (√2 * z + 2 * K4 n * y))) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 8698 / 1000 * y) (le_of_eq (by rw [hy]; ring))
    have e : 12031 / 10000 * z * (14684 / 10000 * z) = 12031 / 10000 * (14684 / 10000) * y := by
      rw [hyz]; ring
    rw [e] at a4
    linarith

/-- `betaW n m_W ≤ 0.0684/√n` for `n ≥ 16384` (`betaLin` is `≤ 8.698/n`; the bound of the
hidden layers `eHid` is stated with `1/√n`). -/
lemma betaW_16W : betaW n (mW n) ≤ 684 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yz16W hn
  obtain ⟨hH, -, hE⟩ := eHid_16W hn
  have hB := betaLin_16W hn
  have eB : (8698 : ℝ) / 1000 / (n : ℝ) = 8698 / 1000 * y := by rw [hy]; ring
  rw [eB] at hB
  rw [← hz] at hH
  rw [← hy] at hE
  unfold betaW
  refine le_trans (?_ : _ ≤ 684 / 10000 * z) (le_of_eq (by rw [hz]; ring))
  linarith

/-- **`tau143 n ≤ 1.055/√n`** for `n ≥ 16384` (Part 142: `eWr + sU ≤ 1.3264/√n`). -/
theorem tau143_le : tau143 n ≤ 1055 / 1000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yz16W hn
  have h1 := eWr_16W hn
  have h2 := sU_16W hn
  have h3 := betaW_16W hn
  have e1 : (9657 : ℝ) / 10000 / √(n : ℝ) = 9657 / 10000 * z := by rw [hz]; ring
  have e2 : (3607 : ℝ) / 10000 / √(n : ℝ) = 3607 / 10000 * z := by rw [hz]; ring
  have e3 : (684 : ℝ) / 10000 / √(n : ℝ) = 684 / 10000 * z := by rw [hz]; ring
  have e4 : (1055 : ℝ) / 1000 / √(n : ℝ) = 1055 / 1000 * z := by rw [hz]; ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4]
  have hs0 := sU_nonneg (2 * n)
  have hb0 := betaW_nonneg n (mW n)
  have hq := q_mem
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  have hsm := eWsmall_nonneg n (mW n)
  have hw0 : 0 ≤ eWr (2 * n) n (mW n) := by unfold eWr; positivity
  unfold tau143
  refine sqrt_le_of_sq (by positivity) ?_
  have p1 : eWr (2 * n) n (mW n) ^ 2 ≤ (9657 / 10000 * z) ^ 2 := pow_le_pow_left₀ hw0 h1 2
  have p2 : sU (2 * n) ^ 2 ≤ (3607 / 10000 * z) ^ 2 := pow_le_pow_left₀ hs0 h2 2
  have p3 : sU (2 * n) * betaW n (mW n) ≤ 3607 / 10000 * z * (684 / 10000 * z) :=
    mul_le_mul h2 h3 hb0 (by positivity)
  nlinarith [sq_nonneg z]

end num

/-! ## A sharper link of the inputs (secant of `κ∘κ` on `[0, 1/8]`) -/

/-- `κ(κ(1/8)) ≤ 0.5337`. -/
lemma kk_eighth_le : kappa (kappa (1 / 8)) ≤ 5337 / 10000 := by
  have h0 := (kappa_mem (t := 1 / 8) (by norm_num) (by norm_num)).1
  have h1 : kappa (1 / 8) ≤ 38331 / 100000 :=
    kappa_le_of_le (a := 1 / 8) (by norm_num) le_rfl (by norm_num) (by norm_num)
  exact kappa_le_of_le (a := 38331 / 100000) h0 h1 (by norm_num) (by norm_num)

/-- **The secant bound of `κ∘κ` at `0`**: for `s ∈ [−1, 1]`,
`|κ(κ(s)) − κ(κ(0))| ≤ 0.32·|s| + 1.49024·s²` (slope of the secant on `[0, 1/8]` at most `0.32`;
`1.49024 = 8·(0.50628 − 0.32)`, `1 − κ(κ(0)) ≤ 0.50628`). -/
lemma kk_abs2 {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    |kappa (kappa s) - kappa (kappa 0)| ≤ 8 / 25 * |s| + 149024 / 100000 * s ^ 2 := by
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  obtain ⟨a', b', -, -, hb0, -, heq, hsup⟩ := hG.support (t := 0) ⟨by norm_num, by norm_num⟩
  simp only [Function.comp, mul_zero, add_zero] at heq hsup
  have q1 := kappa2_zero_le
  have q2 := kappa2_zero_ge
  have k8 := kk_eighth_le
  have u8 := hsup (1 / 8) ⟨by norm_num, by norm_num⟩
  have hb' : b' ≤ 31984 / 100000 := by linarith
  have l1 := hsup s hs
  have h0m : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h8m : (1 / 8 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1m : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_refl _⟩
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  rcases le_total 0 s with h0 | h0
  · have hmono := hG.mono h0m hs h0
    simp only [Function.comp] at hmono
    rw [abs_of_nonneg h0, abs_of_nonneg (by linarith)]
    rcases le_total s (1 / 8) with h8 | h8
    · have hc := hG.conv.2 h0m h8m (show (0 : ℝ) ≤ 1 - 8 * s by linarith)
        (show (0 : ℝ) ≤ 8 * s by linarith) (by ring)
      have e : (1 - 8 * s) • (0 : ℝ) + (8 * s) • (1 / 8 : ℝ) = s := by
        simp only [smul_eq_mul]; ring
      rw [e] at hc
      simp only [smul_eq_mul, Function.comp] at hc
      have h3 : 8 * s * (kappa (kappa (1 / 8)) - kappa (kappa 0)) ≤ 8 * s * (3998 / 100000) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    · have hc := hG.conv.2 h0m h1m (show (0 : ℝ) ≤ 1 - s by linarith [hs.2])
        (show (0 : ℝ) ≤ s by linarith) (by ring)
      have e : (1 - s) • (0 : ℝ) + s • (1 : ℝ) = s := by
        simp only [smul_eq_mul]; ring
      rw [e, hG.one] at hc
      simp only [smul_eq_mul, Function.comp] at hc
      have h3 : s * (1 - kappa (kappa 0)) ≤ s * (50628 / 100000) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have h4 : 0 ≤ (s - 1 / 8) * s := mul_nonneg (by linarith) (by linarith)
      nlinarith
  · have hmono := hG.mono hs h0m h0
    simp only [Function.comp] at hmono
    rw [abs_of_nonpos h0, abs_of_nonpos (by linarith)]
    have h3 : 0 ≤ (31984 / 100000 - b') * (-s) := mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- The sharper link of the inputs: `‖κ(κ(⟨u, u′⟩)) − κ(κ(0))‖₂ ≤ sU2 N`. -/
noncomputable def sU2 (N : ℕ) : ℝ := 8 / 25 / √(N : ℝ) + 149024 / 100000 * √3 / (N : ℝ)

lemma sU2_nonneg (N : ℕ) : 0 ≤ sU2 N := by unfold sU2; positivity

/-- **The link of the inputs with the secant slope `0.32`**:
`‖κ(κ(⟨u, u′⟩)) − κ(κ(0))‖₂ ≤ 0.32/√N + 1.49024·√3/N`. -/
theorem sphere_kk_L2s {N : ℕ} (hN : 1 ≤ N) :
    L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) (sU2 N) := by
  have := lawU2_prob hN
  have := uniformSphere_isProbability N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨iD, eD⟩ := lawU2_dot_sq hN
  have hmd : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => dotp uu.1 uu.2) :=
    continuous_dotp.measurable
  have hmeas : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) :=
    ((continuous_kappa.comp (continuous_kappa.comp continuous_dotp)).measurable).sub
      measurable_const
  have hd : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => |dotp uu.1 uu.2|)
      (1 / √(N : ℝ)) := by
    refine L2le.of_sq_le hmd.abs.aestronglyMeasurable iD (fun uu => by rw [sq_abs]) ?_
    rw [eD, div_pow, Real.sq_sqrt hN'.le]
    simp
  have hd4 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => dotp uu.1 uu.2 ^ 2)
      (√3 / (N : ℝ)) := by
    unfold lawU2
    refine L2le.prod_const_left (hmd.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere N] with y hy
    exact sphere_dot4 hN hy
  have hg := (hd.const_mul_nonneg (c := 8 / 25) (by norm_num)).add'
    (hd4.const_mul_nonneg (c := 149024 / 100000) (by norm_num)) (by positivity) (by positivity)
  refine (L2le.abs_le_ae_R hmeas.aestronglyMeasurable hg ?_).congr_bound (by unfold sU2; ring)
  filter_upwards [lawU2_ae_unit hN] with uu huu
  have h := kk_abs2 (unit_dot_mem huu.1 huu.2)
  refine h.trans (le_abs_self _)

/-- `sphere_gW_L2` of Part 133 for any bound `su` of the link of the inputs. -/
theorem sphere_gW_L2_of {N : ℕ} (hN : 1 ≤ N) (c : ℝ) (hc : 0 ≤ c) {su : ℝ} (hsu : 0 ≤ su)
    (hU : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) su) :
    L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      c * (1 - kappa (kappa (dotp uu.1 uu.2)) ^ 2))
      (c * (1 - kappa (kappa 0) ^ 2 + 2 * su)) := by
  have := lawU2_prob hN
  have hq := kk_mem (s := 0) ⟨by norm_num, by norm_num⟩
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  have hmk : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2))) :=
    (continuous_kappa.comp (continuous_kappa.comp continuous_dotp)).measurable
  have h1 : L2le (lawU2 N) (fun _ : (Fin N → ℝ) × (Fin N → ℝ) =>
      c * (1 - kappa (kappa 0) ^ 2)) (c * (1 - kappa (kappa 0) ^ 2)) := by
    have := L2le.const (μ := lawU2 N) (c * (1 - kappa (kappa 0) ^ 2))
    rwa [abs_of_nonneg (mul_nonneg hc hq2)] at this
  have h2 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      c * (kappa (kappa 0) ^ 2 - kappa (kappa (dotp uu.1 uu.2)) ^ 2)) (c * 2 * su) := by
    have h0 := hU.const_mul_nonneg (c := c * 2) (by positivity)
    refine L2le.abs_le_ae_R
      (((measurable_const.sub (hmk.pow_const 2)).const_mul c).aestronglyMeasurable) h0 ?_
    filter_upwards [lawU2_ae_unit hN] with uu huu
    have hk := kk_mem (unit_dot_mem huu.1 huu.2)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hc
    have e : kappa (kappa 0) ^ 2 - kappa (kappa (dotp uu.1 uu.2)) ^ 2 =
        (kappa (kappa 0) + kappa (kappa (dotp uu.1 uu.2))) *
          (kappa (kappa 0) - kappa (kappa (dotp uu.1 uu.2))) := by ring
    rw [e, abs_mul, abs_sub_comm (kappa (kappa 0))]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [abs_of_nonneg (by linarith [hq.1, hk.1])]
    linarith [hq.2, hk.2]
  have h12 := h1.add' h2 (mul_nonneg hc hq2) (by positivity)
  exact (h12.congr_fun fun uu => by ring).congr_bound (by ring)

/-- The World link after the average over the inputs, with the sharper link of the inputs. -/
noncomputable def eWr2 (N n mW : ℕ) : ℝ :=
  1 / √(n : ℝ) * (1 - kappa (kappa 0) ^ 2 + 2 * sU2 N) + eWsmall n mW

lemma eWr2_nonneg (N n mW : ℕ) : 0 ≤ eWr2 N n mW := by
  have hq := q_mem
  have hsU := sU2_nonneg N
  have hsm := eWsmall_nonneg n mW
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  unfold eWr2
  positivity

/-- **`‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂ ≤ √(eWr2² + sU2² + 2·sU2·betaW)`**, all widths. -/
theorem tX_L2_gen2 {N mW n : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) (hmW : 1 ≤ mW) :
    L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0))
      (√(eWr2 N n mW ^ 2 + sU2 N ^ 2 + 2 * sU2 N * betaW n mW)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmW' : (0 : ℝ) < mW := by exact_mod_cast hmW
  have hsU := sU2_nonneg N
  have hsm := eWsmall_nonneg n mW
  have := lawU2_prob hN
  have hU : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) (sU2 N) := sphere_kk_L2s hN
  have hW : ∀ v v' : Fin N → ℝ, normSq v = 1 → normSq v' = 1 →
      L2le (mlpGauss N mW n)
        (fun W : MlpParam N mW n => dotp (xW W v) (xW W v') - kappa (kappa (dotp v v')))
        ((fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmall n mW) (dotp v v')) := by
    intro v v' hv hv'
    have hJ : 0 ≤ jCos n := by unfold jCos; positivity
    have h := world_cos_L2g hN hmW hn hJ (fun h h' hh hh' =>
      lin_cos_L2b (v := 2 / (mW : ℝ)) (by positivity) hn h h' hh hh') hv hv'
    refine h.congr_bound ?_
    unfold eWsmall
    ring
  have hgW : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      (fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmall n mW) (dotp uu.1 uu.2))
      (eWr2 N n mW) := by
    have h1 := sphere_gW_L2_of hN (1 / √(n : ℝ)) (by positivity) hsU hU
    have h2 : L2le (lawU2 N) (fun _ : (Fin N → ℝ) × (Fin N → ℝ) => eWsmall n mW)
        (eWsmall n mW) := ⟨aestronglyMeasurable_const, integrable_const _, by simp⟩
    have hq := q_mem
    have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
    have h3 := h1.add0 h2 (by positivity) hsm
    exact h3
  exact tX_L2_bias (gW := fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmall n mW)
    hN (eWr2_nonneg N n mW) hsU (betaW_nonneg n mW) hW hgW hU
    (fun v v' hv hv' => world_bias hN hmW hn hv hv')

/-- The sharper bound of `‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂` at the widths of the Focus, `r = 2`. -/
noncomputable def tau143s (n : ℕ) : ℝ :=
  √(eWr2 (2 * n) n (mW n) ^ 2 + sU2 (2 * n) ^ 2 + 2 * sU2 (2 * n) * betaW n (mW n))

lemma tau143s_nonneg (n : ℕ) : 0 ≤ tau143s n := Real.sqrt_nonneg _

/-- **`‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂ ≤ tau143s n`** at the widths of the Focus, `n ≥ 4096`. -/
theorem tX_L2_143s {n : ℕ} (hn : 4096 ≤ n) :
    L2le ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (fun z : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n =>
        tX z - kappa (kappa 0)) (tau143s n) := by
  have hmW : 1 ≤ mW n := by have := mW_ge hn; omega
  exact tX_L2_gen2 (by omega) (by omega) hmW

section num2

variable {n : ℕ} (hn : 16384 ≤ n)

include hn

/-- `sU2(2n) ≤ 0.2364/√n` for `n ≥ 16384`. -/
lemma sU2_16W : sU2 (2 * n) ≤ 2364 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yz16W hn
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h3 := Part133.sqrt3_le
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  unfold sU2
  rw [hc]
  refine le_trans (le_of_eq (?_ : _ = 8 / 25 * r + 149024 / 100000 * √3 / 2 * y)) ?_
  · rw [hr, hy]; ring
  · refine le_trans (?_ : _ ≤ 2364 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    have p : 149024 / 100000 * √3 / 2 * y ≤
        149024 / 100000 * (17321 / 10000) / 2 * (1 / 128 * z) :=
      mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
    linarith

/-- `eWr2(2n, n, m_W) ≤ 0.9638/√n` for `n ≥ 16384`. -/
lemma eWr2_16W : eWr2 (2 * n) n (mW n) ≤ 9638 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yz16W hn
  have h1 := sU2_16W hn
  have h10 := sU2_nonneg (2 * n)
  have h2 := eWsmall_16W hn
  have hq := kappa2_zero_ge
  have hq1 := q_mem.2
  have hq2 : 1 - kappa (kappa 0) ^ 2 ≤ 1 - (49372 / 100000) ^ 2 := by nlinarith
  have e1 : (2364 : ℝ) / 10000 / √(n : ℝ) = 2364 / 10000 * z := by rw [hz]; ring
  have e2 : (2038 : ℝ) / 10000 / √(n : ℝ) = 2038 / 10000 * z := by rw [hz]; ring
  rw [e1] at h1
  rw [e2] at h2
  have h1' : sU2 (2 * n) ≤ 2364 / 10000 / 128 := by linarith
  have t2 : z * (1 - kappa (kappa 0) ^ 2 + 2 * sU2 (2 * n)) ≤
      z * (1 - (49372 / 100000) ^ 2 + 2 * (2364 / 10000 / 128)) :=
    mul_le_mul_of_nonneg_left (by linarith) hz0.le
  unfold eWr2
  refine le_trans (le_of_eq (?_ : _ = z * (1 - kappa (kappa 0) ^ 2 + 2 * sU2 (2 * n)) +
    eWsmall n (mW n))) ?_
  · rw [hz]
  · refine le_trans (?_ : _ ≤ 9638 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    nlinarith

/-- **`tau143s n ≤ 1.009/√n`** for `n ≥ 16384`. -/
theorem tau143s_le : tau143s n ≤ 1009 / 1000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yz16W hn
  have h1 := eWr2_16W hn
  have h2 := sU2_16W hn
  have h3 := betaW_16W hn
  have e1 : (9638 : ℝ) / 10000 / √(n : ℝ) = 9638 / 10000 * z := by rw [hz]; ring
  have e2 : (2364 : ℝ) / 10000 / √(n : ℝ) = 2364 / 10000 * z := by rw [hz]; ring
  have e3 : (684 : ℝ) / 10000 / √(n : ℝ) = 684 / 10000 * z := by rw [hz]; ring
  have e4 : (1009 : ℝ) / 1000 / √(n : ℝ) = 1009 / 1000 * z := by rw [hz]; ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4]
  have hs0 := sU2_nonneg (2 * n)
  have hb0 := betaW_nonneg n (mW n)
  have hw0 := eWr2_nonneg (2 * n) n (mW n)
  unfold tau143s
  refine sqrt_le_of_sq (by positivity) ?_
  have p1 : eWr2 (2 * n) n (mW n) ^ 2 ≤ (9638 / 10000 * z) ^ 2 := pow_le_pow_left₀ hw0 h1 2
  have p2 : sU2 (2 * n) ^ 2 ≤ (2364 / 10000 * z) ^ 2 := pow_le_pow_left₀ hs0 h2 2
  have p3 : sU2 (2 * n) * betaW n (mW n) ≤ 2364 / 10000 * z * (684 / 10000 * z) :=
    mul_le_mul h2 h3 hb0 (by positivity)
  nlinarith [sq_nonneg z]

end num2

end BstLean.Part143

open BstLean.Part143 in
#print axioms lin_bias
open BstLean.Part143 in
#print axioms world_bias
open BstLean.Part143 in
#print axioms tX_L2_bias
open BstLean.Part143 in
#print axioms tX_L2_143
open BstLean.Part143 in
#print axioms tau143_le
open BstLean.Part143 in
#print axioms tau143_nonneg
open BstLean.Part143 in
#print axioms kk_abs2
open BstLean.Part143 in
#print axioms sphere_kk_L2s
open BstLean.Part143 in
#print axioms tX_L2_143s
open BstLean.Part143 in
#print axioms tau143s_le
