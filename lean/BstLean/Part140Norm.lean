import BstLean.Part137Hat2

/-!
# Part 140, tools: the squared length of the computed centre `b̂ = ψ_s(M₂ h̄₁)`

Role: `delegations/statements/p140-spec.md` (item 1). `N` inputs, hidden width `m`, `t = 2/m`,
`γ = 2/N`, `θ = (M₁, M₂)`.

* `Bh N m θ = t|b̂|²`; `kap1 N = κ(q₁(e₀))`, `q₁(u₀) = E_u κ(⟨u₀, u⟩)`.
* `q1_eq`: `q₁` has the same value at every unit vector.
* `kap1_ge`, `kap1_le`: `κ(κ(0)) ≤ κ(q₁) ≤ q_N` (Jensen, two times).
* `sq_row`, `sq_layer`: one Gaussian row and one Gaussian layer against `ψ_s²`
  (two more Gaussian coordinates and the row formula).
* `bhatNorm_cond`: given `M₁`, `t|b̂|²` has mean `Ψ_B` over `M₂` and
  `E_{M₂}(t|b̂|² − Ψ_B)² ≤ (6/m)·Γ*²`.
* **`bhatNorm_L2`**: `‖t|b̂|² − γ·κ(q₁)‖_{L²(θ)} ≤ γ·cB N m`,
  `cB N m² = (6(1 + 5/m) + (κ(0)√(2/N) + √((1 + 2/N)/2))²)/m`.
* `cB_sq_le`: `cB N m² ≤ 6.51/m` for `N ≥ 8192`, `m ≥ 10⁶`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part140

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part73 (IsOrth uniformSphere_orth)
open BstLean.Part80 (dot_mulVec')
open BstLean.Part105 (sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137

variable {N m : ℕ}

/-! ## Definitions -/

/-- `t|b̂|²`. -/
noncomputable def Bh (N m : ℕ) (θ : HidParam N m) : ℝ := 2 / (m : ℝ) * normSq (bhat θ)

/-- `κ(q₁(e₀))`. -/
noncomputable def kap1 (N : ℕ) : ℝ := kappa (q1 (e0 N))

/-- The constant of the squared length of the computed centre. -/
noncomputable def cB (N m : ℕ) : ℝ :=
  √(6 * (1 + 5 / (m : ℝ)) / (m : ℝ) +
    (kappa 0 * √(2 / (N : ℝ)) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 / (m : ℝ))

lemma measurable_Bh (hN : 1 ≤ N) : Measurable (Bh N m) :=
  (measurable_normSq.comp (measurable_bhat hN)).const_mul _

/-! ## The constant `κ(q₁)` -/

/-- `q₁(u) = q₁(e₀)` at every unit vector `u`. -/
theorem q1_eq (hN : 1 ≤ N) {u : Fin N → ℝ} (hu : normSq u = 1) : q1 u = q1 (e0 N) := by
  obtain ⟨O, hO, hOu⟩ := exists_orth_map hN hu (Part137.normSq_e0 hN)
  have hmO : Measurable (fun u : Fin N → ℝ => O.transpose.mulVec u) := by fun_prop
  have hc : Continuous (fun y : Fin N → ℝ => kappa (dotp (e0 N) y)) := continuous_kappa_dot _
  have h := integral_map (μ := uniformSphere N) hmO.aemeasurable
    (f := fun y => kappa (dotp (e0 N) y)) hc.aestronglyMeasurable
  rw [uniformSphere_orth O.transpose hO.t] at h
  unfold q1
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u' => ?_)
  have e : dotp u u' = dotp (e0 N) (O.transpose.mulVec u') := by
    rw [← hOu, dotp_comm' (O.mulVec (e0 N)) u', dotp_comm' (e0 N)]
    exact dot_mulVec' O u' (e0 N)
  change kappa (dotp u u') = kappa (dotp (e0 N) (O.transpose.mulVec u'))
  rw [e]

/-- `κ(0) ≤ q₁(e₀)`. -/
lemma q1_ge (hN : 1 ≤ N) : kappa 0 ≤ q1 (e0 N) := by
  have := uniformSphere_isProbability N hN
  obtain ⟨a, b, -, -, -, -, heq, hab⟩ := kGood_kappa.support (t := 0) ⟨by norm_num, by norm_num⟩
  simp only [mul_zero, add_zero] at heq
  have i1 : Integrable (fun u' : Fin N → ℝ => a + b * dotp (e0 N) u') (uniformSphere N) :=
    sphere_cont_integrable hN (continuous_const.add (continuous_const.mul (continuous_dotp_e0 N)))
  have h : ∫ u', (a + b * dotp (e0 N) u') ∂uniformSphere N ≤ q1 (e0 N) := by
    refine integral_mono_ae i1 (sphere_cont_integrable hN (continuous_kappa_dot (e0 N))) ?_
    filter_upwards [uniformSphere_ae_sphere N] with u' hu'
    exact hab _ (dotp_unit_mem' (Part137.normSq_e0 hN) hu')
  rw [integral_add (integrable_const _)
    ((sphere_cont_integrable hN (continuous_dotp_e0 N)).const_mul _), integral_const_mul,
    int_dotp_e0 hN] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero] at h
  linarith

/-- `κ(κ(0)) ≤ κ(q₁)`. -/
theorem kap1_ge (hN : 1 ≤ N) : kappa (kappa 0) ≤ kap1 N := by
  obtain ⟨hq0, hq1⟩ := q1_mem hN (Part137.normSq_e0 hN)
  have hk := kappa_mem (t := 0) (by norm_num) (by norm_num)
  exact kGood_kappa.mono ⟨by linarith [hk.1], hk.2⟩ ⟨by linarith, hq1⟩ (q1_ge hN)

/-- `κ(q₁) ≤ q_N` (Jensen). -/
theorem kap1_le (hN : 1 ≤ N) : kap1 N ≤ qN N := by
  have := uniformSphere_isProbability N hN
  obtain ⟨hq0, hq1⟩ := q1_mem hN (Part137.normSq_e0 hN)
  obtain ⟨a, b, -, -, -, -, heq, hab⟩ :=
    kGood_kappa.support (t := q1 (e0 N)) ⟨by linarith, hq1⟩
  have ic := sphere_cont_integrable hN (continuous_kappa_dot (e0 N))
  have i1 : Integrable (fun u' : Fin N → ℝ => a + b * kappa (dotp (e0 N) u'))
      (uniformSphere N) := (integrable_const _).add (ic.const_mul _)
  have h : ∫ u', (a + b * kappa (dotp (e0 N) u')) ∂uniformSphere N ≤ qN N := by
    unfold qN
    refine integral_mono_ae i1 (sphere_cont_integrable hN (continuous_kk_e0 N)) ?_
    filter_upwards [uniformSphere_ae_sphere N] with u' hu'
    have hd := dotp_unit_mem' (Part137.normSq_e0 hN) hu'
    have hk := kappa_mem hd.1 hd.2
    exact hab _ ⟨by linarith [hk.1], hk.2⟩
  rw [integral_add (integrable_const _) (ic.const_mul _), integral_const_mul] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  unfold kap1
  rw [← heq]
  exact h

/-! ## A standard Gaussian vector with two more coordinates -/

section aug2

variable {k : ℕ}

/-- The two first coordinates and the rest. -/
def split2 (ξ : Fin (k + 1 + 1) → ℝ) : ℝ × (ℝ × (Fin k → ℝ)) :=
  (ξ 0, (ξ 1, fun j => ξ j.succ.succ))

lemma aug2_integral (G : ℝ × (ℝ × (Fin k → ℝ)) → ℝ) :
    ∫ ξ : Fin (k + 1 + 1) → ℝ, G (split2 ξ) ∂stdGauss (Fin (k + 1 + 1)) =
      ∫ p, G p ∂((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (stdGauss (Fin k)))) := by
  have h1 := aug_integral (k := k + 1)
    (fun q : ℝ × (Fin (k + 1) → ℝ) => G (q.1, (q.2 0, fun j => q.2 j.succ)))
  have e1 : (fun ξ : Fin (k + 1 + 1) → ℝ => G (split2 ξ)) = fun ξ =>
      (fun q : ℝ × (Fin (k + 1) → ℝ) => G (q.1, (q.2 0, fun j => q.2 j.succ)))
        (ξ 0, fun j => ξ j.succ) := by
    funext ξ
    rfl
  rw [e1, h1]
  -- the second step on the second factor
  have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => gaussianReal 0 1) 0
  have mp2 := (MeasurePreserving.id (gaussianReal 0 1)).prod mp
  have emb : MeasurableEmbedding (Prod.map (id : ℝ → ℝ)
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0)) :=
    MeasurableEmbedding.id.prodMap (MeasurableEquiv.measurableEmbedding _)
  have h := mp2.integral_comp emb G
  unfold stdGauss
  rw [← h]
  rfl

lemma aug2_integrable (G : ℝ × (ℝ × (Fin k → ℝ)) → ℝ) :
    Integrable (fun ξ : Fin (k + 1 + 1) → ℝ => G (split2 ξ)) (stdGauss (Fin (k + 1 + 1))) ↔
      Integrable G ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (stdGauss (Fin k)))) := by
  have h1 := aug_integrable (k := k + 1)
    (fun q : ℝ × (Fin (k + 1) → ℝ) => G (q.1, (q.2 0, fun j => q.2 j.succ)))
  have e1 : (fun ξ : Fin (k + 1 + 1) → ℝ => G (split2 ξ)) = fun ξ =>
      (fun q : ℝ × (Fin (k + 1) → ℝ) => G (q.1, (q.2 0, fun j => q.2 j.succ)))
        (ξ 0, fun j => ξ j.succ) := by
    funext ξ
    rfl
  rw [e1, h1]
  have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => gaussianReal 0 1) 0
  have mp2 := (MeasurePreserving.id (gaussianReal 0 1)).prod mp
  have emb : MeasurableEmbedding (Prod.map (id : ℝ → ℝ)
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0)) :=
    MeasurableEmbedding.id.prodMap (MeasurableEquiv.measurableEmbedding _)
  have h := mp2.integrable_comp_emb emb (g := G)
  unfold stdGauss
  rw [← h]
  rfl

/-- Fubini with the vector outermost. -/
lemma fub3 {F : ℝ × (ℝ × (Fin k → ℝ)) → ℝ}
    (hF : Integrable F ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (stdGauss (Fin k))))) :
    Integrable (fun ξ : Fin k → ℝ => ∫ z', (∫ z, F (z, (z', ξ)) ∂gaussianReal 0 1)
      ∂gaussianReal 0 1) (stdGauss (Fin k)) ∧
    ∫ p, F p ∂((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (stdGauss (Fin k)))) =
      ∫ ξ : Fin k → ℝ, (∫ z', (∫ z, F (z, (z', ξ)) ∂gaussianReal 0 1) ∂gaussianReal 0 1)
        ∂stdGauss (Fin k) := by
  have h1 : Integrable (fun q : ℝ × (Fin k → ℝ) => ∫ z, F (z, q) ∂gaussianReal 0 1)
      ((gaussianReal 0 1).prod (stdGauss (Fin k))) := hF.integral_prod_right
  refine ⟨h1.integral_prod_right, ?_⟩
  rw [integral_prod_symm _ hF, integral_prod_symm _ h1]

end aug2

/-! ## One row -/

section row

variable {k : ℕ}

/-- The term of one row `w`: `ψ_s(⟨w, ḡ⟩)²`. -/
noncomputable def fQ (s : ℝ) (gb : Fin k → ℝ) (w : Fin k → ℝ) : ℝ :=
  psiS s (∑ j, w j * gb j) ^ 2

lemma measurable_fQ (s : ℝ) (gb : Fin k → ℝ) : Measurable (fQ s gb) := by
  have h1 : Measurable (fun w : Fin k → ℝ => ∑ j, w j * gb j) :=
    Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _
  exact (measurable_psiS.comp (measurable_const.prodMk h1)).pow_const 2

/-- The first augmented vector `(s/√v, 0, ḡ)`. -/
noncomputable def hP1 (v s : ℝ) (gb : Fin k → ℝ) : Fin (k + 1 + 1) → ℝ :=
  Fin.cons (s / √v) (Fin.cons 0 gb : Fin (k + 1) → ℝ)

/-- The second augmented vector `(0, s/√v, ḡ)`. -/
noncomputable def hP2 (v s : ℝ) (gb : Fin k → ℝ) : Fin (k + 1 + 1) → ℝ :=
  Fin.cons 0 (Fin.cons (s / √v) gb : Fin (k + 1) → ℝ)

/-- The mean of the term of one Gaussian row. -/
noncomputable def cQ (v s : ℝ) (gb : Fin k → ℝ) : ℝ :=
  v * kernelPhi (hP1 v s gb) (hP2 v s gb) / 2

lemma normSq_hP1 {v : ℝ} (hv : 0 < v) (s : ℝ) (gb : Fin k → ℝ) :
    normSq (hP1 v s gb) = s ^ 2 / v + normSq gb := by
  unfold hP1
  rw [normSq_cons, normSq_cons, div_pow, Real.sq_sqrt hv.le]
  ring

lemma normSq_hP2 {v : ℝ} (hv : 0 < v) (s : ℝ) (gb : Fin k → ℝ) :
    normSq (hP2 v s gb) = s ^ 2 / v + normSq gb := by
  unfold hP2
  rw [normSq_cons, normSq_cons, div_pow, Real.sq_sqrt hv.le]
  ring

lemma dotp_self (g : Fin k → ℝ) : dotp g g = normSq g := by
  unfold dotp normSq
  exact Finset.sum_congr rfl fun j _ => by rw [sq]

lemma dotp_hP (v s : ℝ) (gb : Fin k → ℝ) : dotp (hP1 v s gb) (hP2 v s gb) = normSq gb := by
  unfold hP1 hP2
  rw [dotp_cons, dotp_cons, dotp_self]
  ring

/-- **One Gaussian row against `ψ_s²`** (`w = √v·ξ`, `v > 0`): the mean of `ψ_s(⟨w, ḡ⟩)²` is
`cQ`, and its variance is at most `(3/2)·v²·(s²/v + |ḡ|²)²`. -/
theorem sq_row {v : ℝ} (hv : 0 < v) (s : ℝ) (gb : Fin k → ℝ) :
    Integrable (fun ξ : Fin k → ℝ => fQ s gb (√v • ξ)) (stdGauss (Fin k)) ∧
    ∫ ξ : Fin k → ℝ, fQ s gb (√v • ξ) ∂stdGauss (Fin k) = cQ v s gb ∧
    Integrable (fun ξ : Fin k → ℝ => fQ s gb (√v • ξ) ^ 2) (stdGauss (Fin k)) ∧
    ∫ ξ : Fin k → ℝ, fQ s gb (√v • ξ) ^ 2 ∂stdGauss (Fin k) ≤
      3 / 2 * v ^ 2 * (s ^ 2 / v + normSq gb) ^ 2 + cQ v s gb ^ 2 := by
  have hsv : 0 < √v := Real.sqrt_pos.mpr hv
  set c : ℝ := cQ v s gb with hc
  have hcdef : c = v * kernelPhi (hP1 v s gb) (hP2 v s gb) / 2 := rfl
  set ν := (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (stdGauss (Fin k))) with hν
  let D : (Fin k → ℝ) → ℝ := fun ξ => ∑ j, (√v • ξ) j * gb j
  have hDm : Measurable D := Finset.measurable_sum _ fun j _ =>
    ((measurable_pi_apply j).const_mul _).mul_const _
  let H : ℝ × (ℝ × (Fin k → ℝ)) → ℝ := fun p =>
    relu (D p.2.2 + s * p.1) * relu (D p.2.2 + s * p.2.1)
  have hHm : Measurable H := by
    have hD2 : Measurable (fun p : ℝ × (ℝ × (Fin k → ℝ)) => D p.2.2) :=
      hDm.comp (measurable_snd.comp measurable_snd)
    exact (measurable_relu.comp (hD2.add (measurable_fst.const_mul s))).mul
      (measurable_relu.comp (hD2.add ((measurable_fst.comp measurable_snd).const_mul s)))
  have key : ∀ ξ : Fin (k + 1 + 1) → ℝ,
      relu (∑ j, (√v • ξ) j * hP1 v s gb j) * relu (∑ j, (√v • ξ) j * hP2 v s gb j) =
        H (split2 ξ) := by
    intro ξ
    simp only [H, D, split2, hP1, hP2]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, mul_zero, zero_add]
    have e0 : √v * ξ 0 * (s / √v) = s * ξ 0 := by field_simp
    have e1 : √v * ξ (Fin.succ 0) * (s / √v) = s * ξ 1 := by
      have : (Fin.succ 0 : Fin (k + 1 + 1)) = 1 := rfl
      rw [this]
      field_simp
    rw [e0, e1, add_comm (s * ξ 0), add_comm (s * ξ 1)]
  obtain ⟨i1, e1, i2, u2⟩ := rowPair137 hv.le (hP1 v s gb) (hP2 v s gb)
  rw [← hcdef] at e1 i2 u2
  simp_rw [key] at i1 e1 i2 u2
  rw [aug2_integrable] at i1
  rw [aug2_integral] at e1
  have i2' : Integrable (fun p => (H p - c) ^ 2) ν := (aug2_integrable (fun p => (H p - c) ^ 2)).mp i2
  have u2' : ∫ p, (H p - c) ^ 2 ∂ν ≤
      3 / 2 * v ^ 2 * normSq (hP1 v s gb) * normSq (hP2 v s gb) := by
    rw [hν, ← aug2_integral (fun p => (H p - c) ^ 2)]
    exact u2
  rw [normSq_hP1 hv, normSq_hP2 hv] at u2'
  have eH2 : (fun p => H p ^ 2) = fun p => (H p - c) ^ 2 + (2 * c * H p - c ^ 2) := by
    funext p
    ring
  have iA : Integrable (fun p => 2 * c * H p) ν := i1.const_mul _
  have iC : Integrable (fun p => 2 * c * H p - c ^ 2) ν := iA.sub (integrable_const _)
  have iH2 : Integrable (fun p => H p ^ 2) ν := by
    rw [eH2]
    exact i2'.add iC
  have vH2 : ∫ p, H p ^ 2 ∂ν = ∫ p, (H p - c) ^ 2 ∂ν + c ^ 2 := by
    rw [eH2, integral_add i2' iC, integral_sub iA (integrable_const _), integral_const_mul, e1]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  -- the inner integrals
  set M2 : (Fin k → ℝ) → ℝ := fun ξ => ∫ z, relu (D ξ + s * z) ^ 2 ∂gaussianReal 0 1 with hM2
  have in1 : ∀ ξ : Fin k → ℝ, ∫ z', (∫ z, H (z, (z', ξ)) ∂gaussianReal 0 1) ∂gaussianReal 0 1 =
      fQ s gb (√v • ξ) := by
    intro ξ
    simp only [H, fQ, psiS]
    simp_rw [integral_mul_const]
    rw [integral_const_mul, sq]
  have in2 : ∀ ξ : Fin k → ℝ,
      ∫ z', (∫ z, H (z, (z', ξ)) ^ 2 ∂gaussianReal 0 1) ∂gaussianReal 0 1 = M2 ξ ^ 2 := by
    intro ξ
    simp only [H, hM2]
    simp_rw [mul_pow, integral_mul_const]
    rw [integral_const_mul, sq]
  obtain ⟨j1, f1⟩ := fub3 i1
  obtain ⟨j2, f2⟩ := fub3 iH2
  simp_rw [in1] at j1 f1
  simp_rw [in2] at j2 f2
  have hfm : Measurable (fun ξ : Fin k → ℝ => fQ s gb (√v • ξ)) :=
    (measurable_fQ s gb).comp (measurable_const_smul _)
  have hle : ∀ ξ : Fin k → ℝ, fQ s gb (√v • ξ) ^ 2 ≤ M2 ξ ^ 2 := by
    intro ξ
    have h := psiS_sq_le s (D ξ)
    have h0 : 0 ≤ psiS s (D ξ) ^ 2 := sq_nonneg _
    change (psiS s (D ξ) ^ 2) ^ 2 ≤ M2 ξ ^ 2
    exact pow_le_pow_left₀ h0 h 2
  have i4 : Integrable (fun ξ : Fin k → ℝ => fQ s gb (√v • ξ) ^ 2) (stdGauss (Fin k)) := by
    refine Integrable.mono' j2 (hfm.pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hle ξ
  refine ⟨j1, f1.symm.trans e1, i4, ?_⟩
  calc ∫ ξ : Fin k → ℝ, fQ s gb (√v • ξ) ^ 2 ∂stdGauss (Fin k)
      ≤ ∫ ξ : Fin k → ℝ, M2 ξ ^ 2 ∂stdGauss (Fin k) := integral_mono i4 j2 hle
    _ = ∫ p, H p ^ 2 ∂ν := f2.symm
    _ = ∫ p, (H p - c) ^ 2 ∂ν + c ^ 2 := vH2
    _ ≤ 3 / 2 * v ^ 2 * (s ^ 2 / v + normSq gb) ^ 2 + c ^ 2 := by
        have : 3 / 2 * v ^ 2 * (s ^ 2 / v + normSq gb) * (s ^ 2 / v + normSq gb) =
            3 / 2 * v ^ 2 * (s ^ 2 / v + normSq gb) ^ 2 := by ring
        linarith

end row

/-! ## One layer -/

/-- **One Gaussian layer against `ψ_s²`**: for an `m × k` Gaussian matrix `M` of entry variance
`v > 0`, `S(M) = Σ_i ψ_s((M ḡ)_i)²` has mean `m·cQ`, and
`E (S − m·cQ)² ≤ m·(3/2)·v²·(s²/v + |ḡ|²)²`. -/
theorem sq_layer {m k : ℕ} {v : ℝ} (hv : 0 < v) (s : ℝ) (gb : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      normSq (fun i => psiS s ((M.mulVec gb) i))) (gaussMat m k v) ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ, normSq (fun i => psiS s ((M.mulVec gb) i))
      ∂gaussMat m k v = (m : ℝ) * cQ v s gb ∧
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (fun i => psiS s ((M.mulVec gb) i)) - (m : ℝ) * cQ v s gb) ^ 2) (gaussMat m k v) ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ, (normSq (fun i => psiS s ((M.mulVec gb) i)) -
        (m : ℝ) * cQ v s gb) ^ 2 ∂gaussMat m k v ≤
      (m : ℝ) * (3 / 2 * v ^ 2 * (s ^ 2 / v + normSq gb) ^ 2) := by
  obtain ⟨i1, e1, i2, u2⟩ := sq_row hv s gb
  have hf := measurable_fQ s gb
  have hsum : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      normSq (fun i => psiS s ((M.mulVec gb) i)) = ∑ i, fQ s gb (rowOf i M) := fun M => rfl
  simp_rw [hsum]
  set c := cQ v s gb with hc
  have hrow : ∀ i : Fin m, Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => fQ s gb (rowOf i M))
      (gaussMat m k v) := fun i => (row_integrable_iff (m := m) v i hf).mpr i1
  have iS : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => ∑ i, fQ s gb (rowOf i M))
      (gaussMat m k v) := integrable_finsetSum _ fun i _ => hrow i
  have eS : ∫ M : Matrix (Fin m) (Fin k) ℝ, ∑ i, fQ s gb (rowOf i M) ∂gaussMat m k v =
      (m : ℝ) * c := by
    rw [integral_finsetSum _ fun i _ => hrow i]
    simp_rw [row_integral (m := m) v _ hf, e1]
    simp
  obtain ⟨iQ, eQ⟩ := rows_sum_sq (m := m) v (fQ s gb) hf i2
  rw [e1] at eQ
  have hexp : (fun M : Matrix (Fin m) (Fin k) ℝ => (∑ i, fQ s gb (rowOf i M) - (m : ℝ) * c) ^ 2) =
      fun M => (∑ i, fQ s gb (rowOf i M)) ^ 2 -
        2 * ((m : ℝ) * c) * (∑ i, fQ s gb (rowOf i M)) + ((m : ℝ) * c) ^ 2 := by
    funext M
    ring
  have iB : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      2 * ((m : ℝ) * c) * (∑ i, fQ s gb (rowOf i M))) (gaussMat m k v) := iS.const_mul _
  refine ⟨iS, eS, ?_, ?_⟩
  · rw [hexp]
    exact (iQ.sub iB).add (integrable_const _)
  · have iQB : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => (∑ i, fQ s gb (rowOf i M)) ^ 2 -
        2 * ((m : ℝ) * c) * (∑ i, fQ s gb (rowOf i M))) (gaussMat m k v) := iQ.sub iB
    rw [hexp, integral_add iQB (integrable_const _), integral_sub iQ iB,
      integral_const_mul, eS, eQ]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have := mul_le_mul_of_nonneg_left u2 hm0
    nlinarith

/-! ## Given `M₁` -/

/-- The conditional mean of `t|b̂|²` given `M₁`. -/
noncomputable def PsiB (M₁ : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  2 / (m : ℝ) * kernelPhi (hP1 (2 / (m : ℝ)) (sS M₁) (h1bar M₁))
    (hP2 (2 / (m : ℝ)) (sS M₁) (h1bar M₁))

/-- **Given `M₁`**: `t|b̂|²` has mean `Ψ_B` over `M₂`, and
`E_{M₂}(t|b̂|² − Ψ_B)² ≤ (6/m)·Γ*²`. -/
theorem bhatNorm_cond (hN : 1 ≤ N) (hm : 1 ≤ m) (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    Integrable (fun M₂ : Matrix (Fin m) (Fin m) ℝ => Bh N m (M₁, M₂) - PsiB M₁)
      (gaussMat m m (2 / (m : ℝ))) ∧
    ∫ M₂ : Matrix (Fin m) (Fin m) ℝ, (Bh N m (M₁, M₂) - PsiB M₁)
      ∂gaussMat m m (2 / (m : ℝ)) = 0 ∧
    Integrable (fun M₂ : Matrix (Fin m) (Fin m) ℝ => (Bh N m (M₁, M₂) - PsiB M₁) ^ 2)
      (gaussMat m m (2 / (m : ℝ))) ∧
    ∫ M₂ : Matrix (Fin m) (Fin m) ℝ, (Bh N m (M₁, M₂) - PsiB M₁) ^ 2
      ∂gaussMat m m (2 / (m : ℝ)) ≤ 6 / (m : ℝ) * GamS M₁ ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  set v : ℝ := 2 / (m : ℝ) with hvdef
  set gb : Fin m → ℝ := h1bar M₁ with hgb
  set s : ℝ := sS M₁ with hs
  obtain ⟨i1, e1, i2, u2⟩ := sq_layer (m := m) hv s gb
  have hT : ∀ M₂ : Matrix (Fin m) (Fin m) ℝ, Bh N m (M₁, M₂) - PsiB M₁ =
      v * (normSq (fun i => psiS s ((M₂.mulVec gb) i)) - (m : ℝ) * cQ v s gb) := by
    intro M₂
    have e : Bh N m (M₁, M₂) = v * normSq (fun i => psiS s ((M₂.mulVec gb) i)) := rfl
    have e' : PsiB M₁ = v * ((m : ℝ) * cQ v s gb) := by
      unfold PsiB cQ
      rw [← hvdef, ← hgb, ← hs]
      rw [hvdef]
      field_simp
    rw [e, e']
    ring
  simp_rw [hT]
  have iR : Integrable (fun M₂ : Matrix (Fin m) (Fin m) ℝ =>
      normSq (fun i => psiS s ((M₂.mulVec gb) i)) - (m : ℝ) * cQ v s gb)
      (gaussMat m m v) := i1.sub (integrable_const _)
  refine ⟨iR.const_mul v, ?_, ?_, ?_⟩
  · rw [integral_const_mul, integral_sub i1 (integrable_const _), e1]
    simp
  · simp_rw [mul_pow]
    exact i2.const_mul _
  · simp_rw [mul_pow]
    rw [integral_const_mul]
    refine (mul_le_mul_of_nonneg_left u2 (sq_nonneg v)).trans (le_of_eq ?_)
    have hG : s ^ 2 / v + normSq gb = GamS M₁ / v := by
      rw [hs, sS_sq hN, ← hvdef, ← hgb]
      field_simp
      ring
    rw [hG, hvdef]
    field_simp
    ring

/-! ## Over `M₁` -/

/-- `‖t|h̄₁|² − γ·q₁(e₀)‖₂ ≤ γ√((1 + 2/N)/(2m))` over `M₁`. -/
lemma h1bar_L2 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le (gaussMat m N (2 / (N : ℝ)))
      (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
        2 / (m : ℝ) * normSq (h1bar M₁) - 2 / (N : ℝ) * q1 (e0 N))
      (2 / (N : ℝ) * √((1 + 2 / (N : ℝ)) / (2 * m))) := by
  have := uniformSphere_isProbability N hN
  let f : Matrix (Fin m) (Fin N) ℝ × (Fin N → ℝ) → ℝ := fun p =>
    2 / (m : ℝ) * dotp (reluV (p.1.mulVec p.2)) (h1bar p.1) - 2 / (N : ℝ) * q1 (e0 N)
  have hfm : Measurable f :=
    ((continuous_dotp.measurable.comp (continuous_h1.measurable.prodMk
      ((measurable_h1bar hN).comp measurable_fst))).const_mul _).sub_const _
  have h1 : L2le ((gaussMat m N (2 / (N : ℝ))).prod (uniformSphere N)) f
      (2 / (N : ℝ) * √((1 + 2 / (N : ℝ)) / (2 * m))) := by
    refine L2le.prod_const_left hfm.aestronglyMeasurable ?_
    filter_upwards [uniformSphere_ae_sphere N] with u hu
    have hu' : normSq u = 1 := hu
    have h := cov_L2x (m := m) hN hm hu'
    rw [q1_eq hN hu'] at h
    exact h
  refine h1.integral_right.congr_fun fun M₁ => ?_
  change ∫ u, (2 / (m : ℝ) * dotp (reluV (M₁.mulVec u)) (h1bar M₁) -
      2 / (N : ℝ) * q1 (e0 N)) ∂uniformSphere N = _
  have iA : Integrable (fun u : Fin N → ℝ =>
      2 / (m : ℝ) * dotp (reluV (M₁.mulVec u)) (h1bar M₁)) (uniformSphere N) :=
    sphere_cont_integrable hN (continuous_const.mul
      (continuous_dotp.comp ((continuous_h1_u M₁).prodMk continuous_const)))
  rw [integral_sub iA (integrable_const _), integral_const_mul]
  have e : ∫ u, dotp (reluV (M₁.mulVec u)) (h1bar M₁) ∂uniformSphere N = normSq (h1bar M₁) := by
    rw [← dotp_self, dotp_h1bar hN]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    exact dotp_comm' _ _
  rw [e]
  simp

/-- **The squared length of the computed centre**: `‖t|b̂|² − γ·κ(q₁)‖_{L²(θ)} ≤ γ·cB N m`,
every `N, m ≥ 1`. -/
theorem bhatNorm_L2 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le (hidGauss N m) (fun θ => Bh N m θ - 2 / (N : ℝ) * kap1 N) (2 / (N : ℝ) * cB N m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hγ : (0 : ℝ) < 2 / (N : ℝ) := by positivity
  have hk0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  obtain ⟨hq0, hq1⟩ := q1_mem hN (Part137.normSq_e0 hN)
  obtain ⟨-, hG2⟩ := GamS_L2 (N := N) (m := m) hN hm
  have hG1 := GamS_L2x (N := N) (m := m) hN hm
  have hC := h1bar_L2 (m := m) hN hm
  set aG : ℝ := 2 / (N : ℝ) * √(2 / ((N : ℝ) * m)) with haG
  set aC : ℝ := 2 / (N : ℝ) * √((1 + 2 / (N : ℝ)) / (2 * m)) with haC
  have haG0 : 0 ≤ aG := by rw [haG]; positivity
  have haC0 : 0 ≤ aC := by rw [haC]; positivity
  have hTm : Measurable (Bh N m) := measurable_Bh hN
  -- the conditional mean is measurable
  have hPm : Measurable (fun M₁ : Matrix (Fin m) (Fin N) ℝ => PsiB M₁) := by
    have e : (fun M₁ : Matrix (Fin m) (Fin N) ℝ => PsiB M₁) = fun M₁ =>
        ∫ M₂ : Matrix (Fin m) (Fin m) ℝ, Bh N m (M₁, M₂) ∂gaussMat m m (2 / (m : ℝ)) := by
      funext M₁
      obtain ⟨i1, e1, -, -⟩ := bhatNorm_cond hN hm M₁
      have i0 : Integrable (fun M₂ : Matrix (Fin m) (Fin m) ℝ => Bh N m (M₁, M₂))
          (gaussMat m m (2 / (m : ℝ))) := by
        have := i1.add (integrable_const (PsiB M₁))
        refine this.congr (Filter.Eventually.of_forall fun M₂ => ?_)
        simp
      rw [integral_sub i0 (integrable_const _)] at e1
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at e1
      linarith
    rw [e]
    exact (hTm.stronglyMeasurable.integral_prod_right').measurable
  -- `B`: the conditional mean minus the constant
  have hB : L2le (gaussMat m N (2 / (N : ℝ)))
      (fun M₁ : Matrix (Fin m) (Fin N) ℝ => PsiB M₁ - 2 / (N : ℝ) * kap1 N)
      (kappa 0 * aG + aC) := by
    have habs : ∀ {f : Matrix (Fin m) (Fin N) ℝ → ℝ} {a : ℝ},
        L2le (gaussMat m N (2 / (N : ℝ))) f a →
        L2le (gaussMat m N (2 / (N : ℝ))) (fun M₁ => |f M₁|) a := fun {f a} h =>
      L2le.of_abs_le (continuous_abs.comp_aestronglyMeasurable h.aesm) h
        (fun ω => le_of_eq (abs_abs _))
    have hsum := ((habs hG1).const_mul_nonneg hk0).add' (habs hC) (mul_nonneg hk0 haG0) haC0
    refine L2le.of_abs_le (hPm.sub_const _).aestronglyMeasurable hsum fun M₁ => ?_
    rw [abs_of_nonneg (add_nonneg (mul_nonneg hk0 (abs_nonneg _)) (abs_nonneg _))]
    set gP := hP1 (2 / (m : ℝ)) (sS M₁) (h1bar M₁) with hgP
    set gbP := hP2 (2 / (m : ℝ)) (sS M₁) (h1bar M₁) with hgbP
    have hpb : (0 : ℝ) ≤ 2 / (N : ℝ) / (2 / (m : ℝ)) := by positivity
    have hp := psi_abs_sub kGood_kappa gP gbP hpb
      (show |q1 (e0 N)| ≤ 1 by rw [abs_of_nonneg hq0]; exact hq1)
    have hGv : sS M₁ ^ 2 / (2 / (m : ℝ)) + normSq (h1bar M₁) = GamS M₁ / (2 / (m : ℝ)) := by
      rw [sS_sq hN]
      field_simp
      ring
    have hn1 : normSq gP = GamS M₁ / (2 / (m : ℝ)) := by rw [hgP, normSq_hP1 hv, hGv]
    have hn2 : normSq gbP = GamS M₁ / (2 / (m : ℝ)) := by rw [hgbP, normSq_hP2 hv, hGv]
    have hd : dotp gP gbP = normSq (h1bar M₁) := dotp_hP _ _ _
    have hnr : nrm gP * nrm gbP = GamS M₁ / (2 / (m : ℝ)) := by
      unfold nrm
      rw [hn1, hn2]
      exact Real.mul_self_sqrt (div_nonneg (GamS_nonneg M₁) hv.le)
    have hPsi : PsiB M₁ = 2 / (m : ℝ) * psi kappa gP gbP := rfl
    rw [hnr, hd] at hp
    have e3 : PsiB M₁ - 2 / (N : ℝ) * kap1 N =
        2 / (m : ℝ) * (psi kappa gP gbP - 2 / (N : ℝ) / (2 / (m : ℝ)) * kappa (q1 (e0 N))) := by
      rw [hPsi]
      unfold kap1
      field_simp
    have e4 : GamS M₁ - 2 / (N : ℝ) =
        2 / (m : ℝ) * (GamS M₁ / (2 / (m : ℝ)) - 2 / (N : ℝ) / (2 / (m : ℝ))) := by
      field_simp
    have e5 : 2 / (m : ℝ) * normSq (h1bar M₁) - 2 / (N : ℝ) * q1 (e0 N) =
        2 / (m : ℝ) * (normSq (h1bar M₁) - 2 / (N : ℝ) / (2 / (m : ℝ)) * q1 (e0 N)) := by
      field_simp
    rw [e3, abs_mul, abs_of_pos hv, e4, abs_mul, abs_of_pos hv, e5, abs_mul, abs_of_pos hv]
    have h7 := mul_le_mul_of_nonneg_left hp hv.le
    linarith
  -- the conditional standard deviation
  have hg : L2le (gaussMat m N (2 / (N : ℝ)))
      (fun M₁ : Matrix (Fin m) (Fin N) ℝ => √(6 / (m : ℝ) * GamS M₁ ^ 2))
      (2 / (N : ℝ) * √(6 * (1 + 5 / (m : ℝ)) / (m : ℝ))) := by
    refine L2le.of_sq_le (G := fun M₁ => 6 / (m : ℝ) * GamS M₁ ^ 2)
      ((((measurable_GamS hN).pow_const 2).const_mul _).sqrt.aestronglyMeasurable)
      (hG2.int_sq.const_mul _) (fun M₁ => ?_) ?_
    · rw [Real.sq_sqrt (by positivity)]
    · rw [integral_const_mul]
      have a2 := hG2.le
      rw [mul_pow, Real.sq_sqrt (by positivity)] at a2
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      calc 6 / (m : ℝ) * ∫ M₁ : Matrix (Fin m) (Fin N) ℝ, GamS M₁ ^ 2 ∂gaussMat m N (2 / (N : ℝ))
          ≤ 6 / (m : ℝ) * ((2 / (N : ℝ)) ^ 2 * (1 + 5 / (m : ℝ))) :=
            mul_le_mul_of_nonneg_left a2 (by positivity)
        _ = _ := by ring
  have hRm : Measurable (fun z : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      Bh N m z - PsiB z.1) := hTm.sub (hPm.comp measurable_fst)
  have key := L2le.prod_orth (μ := gaussMat m N (2 / (N : ℝ))) (ν := gaussMat m m (2 / (m : ℝ)))
    hRm.aestronglyMeasurable hB hg (fun M₁ => by
      obtain ⟨i1, e1, i2, u2⟩ := bhatNorm_cond hN hm M₁
      refine ⟨i1, e1, i2, u2.trans (le_of_eq ?_)⟩
      rw [Real.sq_sqrt (by positivity)])
  have key' : L2le (hidGauss N m) (fun z : HidParam N m => Bh N m z - PsiB z.1 +
      (PsiB z.1 - 2 / (N : ℝ) * kap1 N)) _ := key
  refine (key'.congr_fun fun θ => by ring).congr_bound ?_
  unfold cB
  have hsm : √(m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hm').ne'
  have r2 : √(2 / ((N : ℝ) * m)) = √(2 / (N : ℝ)) / √(m : ℝ) := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  have r3 : √((1 + 2 / (N : ℝ)) / (2 * m)) = √((1 + 2 / (N : ℝ)) / 2) / √(m : ℝ) := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  have e5 : kappa 0 * aG + aC =
      2 / (N : ℝ) * ((kappa 0 * √(2 / (N : ℝ)) + √((1 + 2 / (N : ℝ)) / 2)) / √(m : ℝ)) := by
    rw [haG, haC, r2, r3]
    ring
  have hs1 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 * (1 + 5 / (m : ℝ)) / (m : ℝ) by positivity)
  have hs2 := Real.sq_sqrt hm'.le
  have e6 : (2 / (N : ℝ) * √(6 * (1 + 5 / (m : ℝ)) / (m : ℝ))) ^ 2 + (kappa 0 * aG + aC) ^ 2 =
      (2 / (N : ℝ)) ^ 2 * (6 * (1 + 5 / (m : ℝ)) / (m : ℝ) +
        (kappa 0 * √(2 / (N : ℝ)) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 / (m : ℝ)) := by
    rw [e5]
    calc (2 / (N : ℝ) * √(6 * (1 + 5 / (m : ℝ)) / (m : ℝ))) ^ 2 +
          (2 / (N : ℝ) * ((kappa 0 * √(2 / (N : ℝ)) + √((1 + 2 / (N : ℝ)) / 2)) /
            √(m : ℝ))) ^ 2
        = (2 / (N : ℝ)) ^ 2 * (√(6 * (1 + 5 / (m : ℝ)) / (m : ℝ)) ^ 2 +
            (kappa 0 * √(2 / (N : ℝ)) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 /
              √(m : ℝ) ^ 2) := by ring
      _ = _ := by rw [hs1, hs2]
  rw [e6, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hγ.le]

/-- `cB N m² ≤ 6.51/m` for `N ≥ 8192`, `m ≥ 10⁶`. -/
lemma cB_sq_le {N m : ℕ} (hN : 8192 ≤ N) (hm : 1000000 ≤ m) :
    cB N m ^ 2 ≤ 651 / 100 / (m : ℝ) := by
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hN' : (8192 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : (0 : ℝ) < m := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have k1 := kappa_zero_le
  have k0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  have hNle : 2 / (N : ℝ) ≤ 2 / 8192 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN'
  have sN : √(2 / (N : ℝ)) ≤ 1 / 64 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have sN0 : 0 ≤ √(2 / (N : ℝ)) := Real.sqrt_nonneg _
  have sH : √((1 + 2 / (N : ℝ)) / 2) ≤ 7072 / 10000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have sH0 : 0 ≤ √((1 + 2 / (N : ℝ)) / 2) := Real.sqrt_nonneg _
  unfold cB
  rw [Real.sq_sqrt (by positivity)]
  have h1 : 5 / (m : ℝ) ≤ 5 / 1000000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm'
  have h3 : kappa 0 * √(2 / (N : ℝ)) ≤ 31831 / 100000 * (1 / 64) :=
    mul_le_mul k1 sN sN0 (by norm_num)
  have h2 : (kappa 0 * √(2 / (N : ℝ)) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 ≤
      (31831 / 100000 * (1 / 64) + 7072 / 10000) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ hm0.le
  nlinarith

end BstLean.Part140

open BstLean.Part140 in
#print axioms q1_eq
open BstLean.Part140 in
#print axioms kap1_ge
open BstLean.Part140 in
#print axioms kap1_le
open BstLean.Part140 in
#print axioms bhatNorm_L2
open BstLean.Part140 in
#print axioms cB_sq_le
