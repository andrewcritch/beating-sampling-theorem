import BstLean.Part142Stmt

/-!
# Part 142: one linear Gaussian layer for the distance form

Role: `delegations/statements/p142-spec.md`, item 2. This file proves the three statements
`LinEDStmt`, `LinDltStmt`, `LinPhiStmt` of `Part142Stmt` for a Gaussian matrix `M` with `m` rows
and entry variance `v`, scale `s = m·v`:

* `linEDStmt`: `‖e(Mh, Mh′) − s·e(h, h′)‖₂ ≤ (√m/√2)·v·|h − h′|²`.
* `linDltStmt`: `‖δ(Mh, Mh′) − s·δ(h, h′)‖₂ ≤ s·((K₄/m)(|h|² + |h′|²) + (√2/√m)||h|² − |h′|²|)`.
* `linPhiStmt`: the distance form `Φ_G`, for `⟨h, h′⟩ ≥ 0`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133

variable {m k : ℕ}

/-- `‖|Mh|² − m·v|h|²‖₂ ≤ √(2m)·v|h|²`. -/
lemma lin_c2 {v : ℝ} (hv : 0 ≤ v) (h : Fin k → ℝ) :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => normSq (M.mulVec h) - (m : ℝ) * (v * normSq h))
      (√(2 * (m : ℝ)) * (v * normSq h)) := by
  obtain ⟨i1, e1⟩ := layer_lin_sq (m := m) hv h
  obtain ⟨i2, e2⟩ := layer_lin_four (m := m) hv h
  set c : ℝ := (m : ℝ) * (v * normSq h) with hc
  have hmeas : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => normSq (M.mulVec h) - c) :=
    (measurable_normSq.comp (measurable_mulVec_right h)).sub measurable_const
  have hG : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      normSq (M.mulVec h) ^ 2 - 2 * c * normSq (M.mulVec h) + c ^ 2) (gaussMat m k v) :=
    (i2.sub (i1.const_mul _)).add (integrable_const _)
  refine L2le.of_sq_le hmeas.aestronglyMeasurable hG (fun M => le_of_eq (by ring)) ?_
  have hA : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      normSq (M.mulVec h) ^ 2 - 2 * c * normSq (M.mulVec h)) (gaussMat m k v) :=
    i2.sub (i1.const_mul _)
  rw [integral_add hA (integrable_const _), integral_sub i2 (i1.const_mul _),
    integral_const_mul, e1, e2]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have e : (√(2 * (m : ℝ)) * (v * normSq h)) ^ 2 = 2 * (m : ℝ) * (v * normSq h) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [e]
  apply le_of_eq
  rw [hc]
  ring

/-- `‖(|Mh|² − m·v|h|²)²‖₂ ≤ m·K₄(m)·(v|h|²)²`. -/
lemma lin_c4 {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m) (h : Fin k → ℝ) :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        (normSq (M.mulVec h) - (m : ℝ) * (v * normSq h)) ^ 2)
      ((m : ℝ) * K4 m * (v * normSq h) ^ 2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨i4, e4⟩ := lin_sq_four (m := m) hv h
  have hmeas : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (M.mulVec h) - (m : ℝ) * (v * normSq h)) ^ 2) :=
    ((measurable_normSq.comp (measurable_mulVec_right h)).sub measurable_const).pow_const 2
  refine L2le.of_sq_le hmeas.aestronglyMeasurable i4 (fun M => le_of_eq (by ring)) ?_
  have e : ((m : ℝ) * K4 m * (v * normSq h) ^ 2) ^ 2 =
      (m : ℝ) ^ 2 * K4 m ^ 2 * (v * normSq h) ^ 4 := by ring
  rw [e4, e, K4_sq]
  apply le_of_eq
  field_simp

lemma mulVec_sub' (M : Matrix (Fin m) (Fin k) ℝ) (h h' : Fin k → ℝ) :
    M.mulVec h - M.mulVec h' = M.mulVec (h - h') := (Matrix.mulVec_sub M h h').symm

/-- **`LinEDStmt`.** -/
theorem linEDStmt : LinEDStmt := by
  intro m k v hv hm h h'
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h0 := (lin_c2 (m := m) hv.le (h - h')).const_mul_nonneg (c := 1 / 2) (by norm_num)
  refine (h0.congr_fun fun M => ?_).congr_bound ?_
  · rw [eD_eq, eD_eq, mulVec_sub']
    ring
  · rw [Real.sqrt_mul (by norm_num) (m : ℝ)]
    have h2 : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h2p : (0 : ℝ) < √2 := by positivity
    have u : 1 / 2 * √2 = 1 / √2 := by
      rw [eq_div_iff h2p.ne']
      calc 1 / 2 * √2 * √2 = 1 / 2 * (√2 * √2) := by ring
        _ = 1 := by rw [h2]; norm_num
    calc 1 / 2 * (√2 * √(m : ℝ) * (v * normSq (h - h')))
        = 1 / 2 * √2 * √(m : ℝ) * (v * normSq (h - h')) := by ring
      _ = _ := by rw [u]; ring

section dlt

lemma measurable_dlt_lin (h h' : Fin k → ℝ) :
    Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => dlt (M.mulVec h) (M.mulVec h')) := by
  unfold dlt
  exact (((measurable_normSq.comp (measurable_mulVec_right h)).add
    (measurable_normSq.comp (measurable_mulVec_right h'))).div_const 2).sub
    ((continuous_nrm.measurable.comp (measurable_mulVec_right h)).mul
      (continuous_nrm.measurable.comp (measurable_mulVec_right h')))

lemma dlt_comm {ι : Type*} [Fintype ι] (y y' : ι → ℝ) : dlt y y' = dlt y' y := by
  unfold dlt; ring

lemma dlt_zero_leftL {ι : Type*} [Fintype ι] (y' : ι → ℝ) :
    dlt (0 : ι → ℝ) y' = normSq y' / 2 := by
  have h0 : normSq (0 : ι → ℝ) = 0 := by simp [normSq]
  unfold dlt
  rw [nrm_zero_of h0, h0]
  ring

lemma sqrt2m_pos (hm : 1 ≤ m) : 0 < √(2 * (m : ℝ)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  positivity

/-- The degenerate case `h = 0`. -/
lemma lin_dlt_zero {v : ℝ} (hv : 0 < v) (hm : 1 ≤ m) (h' : Fin k → ℝ) :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        dlt (M.mulVec (0 : Fin k → ℝ)) (M.mulVec h') - (m : ℝ) * v * dlt 0 h')
      ((m : ℝ) * v * (K4 m / (m : ℝ) * (normSq (0 : Fin k → ℝ) + normSq h') +
        √2 / √(m : ℝ) * |normSq (0 : Fin k → ℝ) - normSq h'|)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h0 : normSq (0 : Fin k → ℝ) = 0 := by simp [normSq]
  have hN := normSq_nonneg h'
  have hK := K4_nonneg m
  have hb := (lin_c2 (m := m) hv.le h').const_mul_nonneg (c := 1 / 2) (by norm_num)
  have hb' := hb.congr_fun (g := fun M : Matrix (Fin m) (Fin k) ℝ =>
      dlt (M.mulVec (0 : Fin k → ℝ)) (M.mulVec h') - (m : ℝ) * v * dlt 0 h') (fun M => by
    rw [Matrix.mulVec_zero, dlt_zero_leftL, dlt_zero_leftL]; ring)
  refine hb'.mono (by positivity) ?_
  rw [h0, zero_add, zero_sub, abs_neg, abs_of_nonneg hN,
    Real.sqrt_mul (by norm_num) (m : ℝ)]
  have hsm : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt hm'.le
  have hsm0 : (0 : ℝ) < √(m : ℝ) := Real.sqrt_pos.mpr hm'
  have e : (m : ℝ) * v * (K4 m / (m : ℝ) * normSq h' + √2 / √(m : ℝ) * normSq h') =
      K4 m * v * normSq h' + √2 * √(m : ℝ) * (v * normSq h') := by
    have : (m : ℝ) / √(m : ℝ) = √(m : ℝ) := by
      rw [div_eq_iff hsm0.ne']; exact hsm.symm
    calc (m : ℝ) * v * (K4 m / (m : ℝ) * normSq h' + √2 / √(m : ℝ) * normSq h')
        = K4 m * v * normSq h' * ((m : ℝ) / m) + √2 * ((m : ℝ) / √(m : ℝ)) * (v * normSq h') := by
          ring
      _ = _ := by rw [this, div_self hm'.ne']; ring
  rw [e]
  have h1 : 0 ≤ √2 * √(m : ℝ) * (v * normSq h') := by positivity
  have h2 : 0 ≤ K4 m * v * normSq h' := by positivity
  linarith

/-- **`LinDltStmt`.** -/
theorem linDltStmt : LinDltStmt := by
  intro m k v hv hm h h'
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hz : normSq h = 0
  · have : h = 0 := normSq_eq_zero hz
    subst this
    exact lin_dlt_zero hv hm h'
  by_cases hz' : normSq h' = 0
  · have : h' = 0 := normSq_eq_zero hz'
    subst this
    have h0 := lin_dlt_zero (m := m) hv hm h
    refine (h0.congr_fun fun M => ?_).congr_bound ?_
    · rw [dlt_comm (M.mulVec 0), dlt_comm 0]
    · rw [add_comm (normSq (0 : Fin k → ℝ)) (normSq h),
        abs_sub_comm (normSq (0 : Fin k → ℝ)) (normSq h)]
  -- the main case
  have hx : 0 < nrm h := nrm_pos_of_ne hz
  have hx' : 0 < nrm h' := nrm_pos_of_ne hz'
  set s : ℝ := (m : ℝ) * v with hs
  have hs0 : 0 < s := by positivity
  set r : ℝ := √s with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hs0
  have hrr : r * r = s := Real.mul_self_sqrt hs0.le
  set x := nrm h with hxd
  set x' := nrm h' with hxd'
  have eN : normSq h = x ^ 2 := (nrm_sq h).symm
  have eN' : normSq h' = x' ^ 2 := (nrm_sq h').symm
  have ea : (r * x) ^ 2 = (m : ℝ) * (v * normSq h) := by
    rw [mul_pow, eN, sq r, hrr, hs]; ring
  have ea' : (r * x') ^ 2 = (m : ℝ) * (v * normSq h') := by
    rw [mul_pow, eN', sq r, hrr, hs]; ring
  have c2 := lin_c2 (m := m) hv.le h
  have c2' := lin_c2 (m := m) hv.le h'
  have c4 := lin_c4 (m := m) hv.le hm h
  have c4' := lin_c4 (m := m) hv.le hm h'
  rw [← ea] at c2 c4
  rw [← ea'] at c2' c4'
  have hK := K4_nonneg m
  have hN := normSq_nonneg h
  have hN' := normSq_nonneg h'
  have key := delta_L2_core (μ := gaussMat m k v)
    (Y := fun M : Matrix (Fin m) (Fin k) ℝ => M.mulVec h)
    (Y' := fun M : Matrix (Fin m) (Fin k) ℝ => M.mulVec h')
    (measurable_dlt_lin h h').aestronglyMeasurable (a₀ := r * x) (b₀ := r * x')
    (by positivity) (by positivity) c2 c2' c4 c4'
    (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hv.le hN))
    (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hv.le hN'))
    (mul_nonneg (mul_nonneg hm'.le hK) (sq_nonneg _))
    (mul_nonneg (mul_nonneg hm'.le hK) (sq_nonneg _))
  refine (key.congr_fun fun M => ?_).congr_bound ?_
  · rw [dlt_eq h h']
    have : (r * x - r * x') ^ 2 = s * (x - x') ^ 2 := by rw [← hrr]; ring
    rw [this]; ring
  · have hsq : √(2 * (m : ℝ)) = √2 * √(m : ℝ) := Real.sqrt_mul (by norm_num) _
    have hsm : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt hm'.le
    have hsm0 : (0 : ℝ) < √(m : ℝ) := Real.sqrt_pos.mpr hm'
    have habs : |r * x - r * x'| * (x + x') = r * |x ^ 2 - x' ^ 2| := by
      have e1 : r * x - r * x' = r * (x - x') := by ring
      have e2 : x ^ 2 - x' ^ 2 = (x - x') * (x + x') := by ring
      rw [e1, e2, abs_mul, abs_mul, abs_of_pos hr0, abs_of_pos (by linarith : 0 < x + x')]
      ring
    rw [eN, eN', hsq]
    have t1 : (m : ℝ) * K4 m * (v * x ^ 2) ^ 2 / (r * x) ^ 2 = K4 m * v * x ^ 2 := by
      rw [mul_pow r x, sq r, hrr, hs]
      field_simp
    have t1' : (m : ℝ) * K4 m * (v * x' ^ 2) ^ 2 / (r * x') ^ 2 = K4 m * v * x' ^ 2 := by
      rw [mul_pow r x', sq r, hrr, hs]
      field_simp
    have t2 : (√2 * √(m : ℝ) * (v * x ^ 2) / (r * x) + √2 * √(m : ℝ) * (v * x' ^ 2) / (r * x')) *
        |r * x - r * x'| = √2 * √(m : ℝ) * v * |x ^ 2 - x' ^ 2| := by
      have e : √2 * √(m : ℝ) * (v * x ^ 2) / (r * x) + √2 * √(m : ℝ) * (v * x' ^ 2) / (r * x') =
          √2 * √(m : ℝ) * v / r * (x + x') := by
        field_simp
      rw [e, mul_assoc, mul_comm (x + x'), habs]
      field_simp
    rw [t1, t1', t2]
    have t3 : (m : ℝ) * v * (√2 / √(m : ℝ) * |x ^ 2 - x' ^ 2|) =
        √2 * √(m : ℝ) * v * |x ^ 2 - x' ^ 2| := by
      have : (m : ℝ) / √(m : ℝ) = √(m : ℝ) := by
        rw [div_eq_iff hsm0.ne']; exact hsm.symm
      calc (m : ℝ) * v * (√2 / √(m : ℝ) * |x ^ 2 - x' ^ 2|)
          = √2 * ((m : ℝ) / √(m : ℝ)) * v * |x ^ 2 - x' ^ 2| := by ring
        _ = _ := by rw [this]
    have t4 : (m : ℝ) * v * (K4 m / (m : ℝ) * (x ^ 2 + x' ^ 2)) =
        K4 m * v * x ^ 2 + K4 m * v * x' ^ 2 := by
      field_simp
    rw [mul_add, t3, t4]

end dlt

lemma measurable_phiD_lin {G : ℝ → ℝ} (hG : Continuous G) (h h' : Fin k → ℝ) :
    Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => phiD G (M.mulVec h) (M.mulVec h')) := by
  unfold phiD
  exact (((measurable_normSq.comp (measurable_mulVec_right h)).add
    (measurable_normSq.comp (measurable_mulVec_right h'))).div_const 2).sub
    (measurable_psi_lin hG h h')

/-- **`LinPhiStmt`.** -/
theorem linPhiStmt : LinPhiStmt := by
  intro m k G hG v hv hm h h' hd
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set s : ℝ := (m : ℝ) * v with hs
  have hs0 : 0 < s := by positivity
  have hnn := nrm_mul_nonneg h h'
  have hN := normSq_nonneg h
  have hN' := normSq_nonneg h'
  have hK := K4_nonneg m
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  have hbb := bG_nonneg hG
  have hdl := dlt_nonneg h h'
  set P : ℝ := s * ((normSq h + normSq h') / 2) with hP
  set pb : ℝ := s * (nrm h * nrm h') with hpb
  set t : ℝ := cosv h h' with ht
  have hpb0 : 0 ≤ pb := by positivity
  have hPb : pb ≤ P := mul_le_mul_of_nonneg_left (nrm_mul_le h h') hs0.le
  have ht1 : t ≤ 1 := (cosv_mem h h').2
  have ht0 : 0 ≤ t := by
    rw [ht]; unfold cosv
    exact div_nonneg hd hnn
  have edot : dotp h h' = t * (nrm h * nrm h') := dotp_eq_cosv_mul h h'
  -- e
  have hE : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      eD (M.mulVec h) (M.mulVec h') - (P - pb * t))
      (√(m : ℝ) / √2 * v * normSq (h - h')) := by
    refine (linEDStmt hv hm h h').congr_fun fun M => ?_
    have : (m : ℝ) * v * eD h h' = P - pb * t := by
      unfold eD; rw [edot, hP, hpb, hs]; ring
    rw [this]
  -- p⁺
  have hPp : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (M.mulVec h) + normSq (M.mulVec h')) / 2 - P)
      (1 / 2 * (√(2 * (m : ℝ)) * (v * normSq h)) + 1 / 2 * (√(2 * (m : ℝ)) * (v * normSq h'))) := by
    have a1 := (lin_c2 (m := m) hv.le h).const_mul_nonneg (c := 1 / 2) (by norm_num)
    have a2 := (lin_c2 (m := m) hv.le h').const_mul_nonneg (c := 1 / 2) (by norm_num)
    refine (a1.add0 a2 (by positivity) (by positivity)).congr_fun fun M => ?_
    rw [hP, hs]; ring
  -- δ
  set bd : ℝ := (m : ℝ) * v * (K4 m / (m : ℝ) * (normSq h + normSq h') +
      √2 / √(m : ℝ) * |normSq h - normSq h'|) with hbd
  have hbd0 : 0 ≤ bd := by positivity
  have hD : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dlt (M.mulVec h) (M.mulVec h') + (P - pb)) (bd + |2 * (s * dlt h h')|) := by
    have a1 := linDltStmt hv hm h h'
    have a2 : L2le (gaussMat m k v) (fun _ : Matrix (Fin m) (Fin k) ℝ => 2 * (s * dlt h h'))
        |2 * (s * dlt h h')| := L2le.const _
    refine (a1.add0 a2 hbd0 (abs_nonneg _)).congr_fun fun M => ?_
    rw [hP, hpb, hs]; unfold dlt; ring
  have key := phiD_L2_core2 (μ := gaussMat m k v) hG
    (Y := fun M : Matrix (Fin m) (Fin k) ℝ => M.mulVec h)
    (Y' := fun M : Matrix (Fin m) (Fin k) ℝ => M.mulVec h')
    (measurable_phiD_lin hG.cont h h').aestronglyMeasurable hpb0 hPb ht0 ht1 hE hPp hD
    (mul_nonneg (mul_nonneg (by positivity) hv.le) (normSq_nonneg _))
    (by positivity) (add_nonneg hbd0 (abs_nonneg _))
  refine (key.congr_fun fun M => ?_).congr_bound ?_
  · have : (m : ℝ) * v * phiD G h h' = P - pb * G t := by
      unfold phiD psi; rw [hP, hpb, hs, ht]; ring
    rw [this]
  · rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 * (s * dlt h h') by positivity), hbd]
    have hsq : √(2 * (m : ℝ)) = √2 * √(m : ℝ) := Real.sqrt_mul (by norm_num) _
    have hsm : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt hm'.le
    have hsm0 : (0 : ℝ) < √(m : ℝ) := Real.sqrt_pos.mpr hm'
    have h22 : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h2p : (0 : ℝ) < √2 := by positivity
    have u1 : √(m : ℝ) / √2 = (m : ℝ) / (√2 * √(m : ℝ)) := by
      rw [div_eq_div_iff h2p.ne' (by positivity)]
      calc √(m : ℝ) * (√2 * √(m : ℝ)) = √2 * (√(m : ℝ) * √(m : ℝ)) := by ring
        _ = (m : ℝ) * √2 := by rw [hsm]; ring
    have u2 : 1 / 2 * (√2 * √(m : ℝ)) = (m : ℝ) / (√2 * √(m : ℝ)) := by
      rw [eq_div_iff (by positivity)]
      calc 1 / 2 * (√2 * √(m : ℝ)) * (√2 * √(m : ℝ))
          = 1 / 2 * (√2 * √2) * (√(m : ℝ) * √(m : ℝ)) := by ring
        _ = (m : ℝ) := by rw [h22, hsm]; ring
    rw [hsq]
    have e1 : √(m : ℝ) / √2 * v * normSq (h - h') =
        (m : ℝ) * v * (normSq (h - h') / (√2 * √(m : ℝ))) := by rw [u1]; ring
    have e2 : 1 / 2 * (√2 * √(m : ℝ) * (v * normSq h)) +
        1 / 2 * (√2 * √(m : ℝ) * (v * normSq h')) =
        (m : ℝ) * v * ((normSq h + normSq h') / (√2 * √(m : ℝ))) := by
      calc _ = 1 / 2 * (√2 * √(m : ℝ)) * (v * (normSq h + normSq h')) := by ring
        _ = _ := by rw [u2]; ring
    rw [e1, e2, hs]
    ring

end BstLean.Part142

open BstLean.Part142 in
#print axioms linEDStmt
open BstLean.Part142 in
#print axioms linDltStmt
open BstLean.Part142 in
#print axioms linPhiStmt
