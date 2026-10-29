import BstLean.Part132Cross

/-!
# Part 132, item 3: a sharper upper bound of `b₁₁` (second-order in the cosine)

Role: `delegations/statements/p132-spec.md`. Paper source: `onW4c-cx.md` §3 ("Upper bound of
b₁₁": `g(t) ≤ q + g′(0)t + 2.76t²`, `E t² = 1/n`).

The theorems of this file take a quadratic upper bound of `κ∘κ` as a hypothesis
(`QuadBound b C`: `κ(κ(t)) ≤ κ(κ(0)) + b·t + C·t²` on `[−1, 1]`); `Part132Quad` proves it with
`C = 8/25`.

* `psi_quad`, `sq_div_le`: the pointwise bounds.
* `agentB_upper2`, `kern_cross_upper2`, **`b11_upper2`**:
  `b11 ≤ (4/n)·(q + cF m_F + C·(3/(2n) + eps4 n m_A/2))`, `eps4 = (1 + 5/m_A)²(1 + 2/n) − 1`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part132

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131

/-- A quadratic upper bound of `κ∘κ` around `0`, on `[−1, 1]`. -/
def QuadBound (b C : ℝ) : Prop :=
  ∀ t ∈ Icc (-1 : ℝ) 1, kappa (kappa t) ≤ kappa (kappa 0) + b * t + C * t ^ 2

lemma quad_scal {P D q b C : ℝ} (hP : P ≠ 0) :
    P * (q + b * (D / P) + C * (D / P) ^ 2) = q * P + b * D + C * (D ^ 2 / P) := by
  field_simp

lemma psi_quad {ι : Type*} [Fintype ι] {b C : ℝ} (hq : QuadBound b C) (y y' : ι → ℝ) :
    psi (kappa ∘ kappa) y y' ≤ kappa (kappa 0) * (nrm y * nrm y') + b * dotp y y' +
      C * (dotp y y' ^ 2 / (nrm y * nrm y')) := by
  have hp := nrm_mul_nonneg y y'
  rcases eq_or_lt_of_le hp with h | h
  · have hd : dotp y y' = 0 := by
      have := abs_dotp_le_nrm y y'
      rw [← h] at this
      exact abs_nonpos_iff.mp this
    unfold psi
    rw [← h, hd]; simp
  · have h1 := hq _ (cosv_mem y y')
    have h2 := mul_le_mul_of_nonneg_left h1 hp
    have e : nrm y * nrm y' * (kappa (kappa 0) + b * cosv y y' + C * cosv y y' ^ 2) =
        kappa (kappa 0) * (nrm y * nrm y') + b * dotp y y' +
          C * (dotp y y' ^ 2 / (nrm y * nrm y')) := by
      unfold cosv
      exact quad_scal h.ne'
    rw [e] at h2
    exact h2

/-- `c²/p ≤ (3/2)·c²/p̄ + (p − p̄)²/(2p̄)` for `|c| ≤ p`, `p̄ > 0`. -/
lemma sq_div_le {c p pb : ℝ} (hp : 0 ≤ p) (hc : |c| ≤ p) (hpb : 0 < pb) :
    c ^ 2 / p ≤ 3 / 2 * c ^ 2 / pb + (p - pb) ^ 2 / (2 * pb) := by
  rcases eq_or_lt_of_le hp with h | h
  · rw [← h]; simp only [div_zero]; positivity
  · rw [div_le_iff₀ h]
    have e : (3 / 2 * c ^ 2 / pb + (p - pb) ^ 2 / (2 * pb)) * p =
        p * (3 * c ^ 2 + (p - pb) ^ 2) / (2 * pb) := by field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have h1 : c ^ 2 = |c| ^ 2 := (sq_abs c).symm
    have h2 : pb - p ≤ |p - pb| := by rw [abs_sub_comm]; exact le_abs_self _
    have h3 : (p - pb) ^ 2 = |p - pb| ^ 2 := (sq_abs _).symm
    have ha := abs_nonneg c
    have hd := abs_nonneg (p - pb)
    have k1 : |c| ^ 2 * (pb - p) ≤ |c| ^ 2 * |p - pb| := mul_le_mul_of_nonneg_left h2 (by positivity)
    have k2 : |c| ^ 2 * |p - pb| ≤ |c| * p * |p - pb| := by
      have := mul_le_mul_of_nonneg_left hc (mul_nonneg ha hd)
      nlinarith
    have k3 : |c| * p * |p - pb| ≤ p * (|c| ^ 2 + |p - pb| ^ 2) / 2 := by
      nlinarith [sq_nonneg (|c| - |p - pb|)]
    rw [h1, h3]
    nlinarith

variable {n mA mF : ℕ}

/-- The relative variance of `|A(x)|²`: `(1 + 5/m_A)²(1 + 2/n) − 1`. -/
noncomputable def eps4 (n mA : ℕ) : ℝ :=
  (1 + 5 / (mA : ℝ)) ^ 2 * (1 + 2 / (n : ℝ)) - 1

lemma eps4_nonneg (n mA : ℕ) : 0 ≤ eps4 n mA := by
  unfold eps4
  have h1 : (0 : ℝ) ≤ 5 / (mA : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h1) h2]

/-- `E(|A(x)|² − 2)² = 4·eps4` for a unit `x`. -/
lemma agent_sq_var (hn : 1 ≤ n) (hmA : 1 ≤ mA) {x : Fin n → ℝ} (hx : normSq x = 1) :
    Integrable (fun a : MlpParam n mA n => (normSq (mlpEval a x) - 2) ^ 2) (mlpGauss n mA n) ∧
    ∫ a : MlpParam n mA n, (normSq (mlpEval a x) - 2) ^ 2 ∂mlpGauss n mA n = 4 * eps4 n mA := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have i2 := mlp_normSq_integrable (m := mA) (q := n) x
  have i4 := mlp_normSq_sq_integrable (m := mA) (q := n) x
  have e2 := mlp_second_moment (q := n) hmA x
  have e4 := mlp_fourth_moment (q := n) hmA x
  obtain ⟨iR, eR⟩ := integral_lin4 (μ := mlpGauss n mA n) i4 i2 i2 i2 4 1 4 0 0
  have e : (fun a : MlpParam n mA n => (normSq (mlpEval a x) - 2) ^ 2) =
      fun a => 1 * normSq (mlpEval a x) ^ 2 + 4 - 4 * normSq (mlpEval a x) -
        0 * normSq (mlpEval a x) - 0 * normSq (mlpEval a x) := by
    funext a; ring
  rw [e]
  refine ⟨iR, ?_⟩
  rw [eR, e2, e4, hx]
  unfold eps4
  field_simp
  ring

lemma quad_pt {ψ q b C c0 ny nw D X Ny V s : ℝ} (hC : 0 ≤ C) (hny : 0 < ny) (hs0 : 0 < s)
    (hs : s * s = 2) (hNy : Ny = ny * ny)
    (h1 : ψ ≤ q * (ny * nw) + b * D + C * X)
    (h2 : X ≤ 3 / 2 * D ^ 2 / (ny * s) + (ny * nw - ny * s) ^ 2 / (2 * (ny * s)))
    (h3 : (ny * nw - ny * s) ^ 2 ≤ Ny * V / 2) :
    ψ + c0 * (ny * nw) ≤ (q + c0) * ny * nw + 0 - -b * D - -(3 * C * s / (4 * ny)) * D ^ 2 -
      -(C * ny * s / 8) * V := by
  have hinv : 1 / (ny * s) = s / (2 * ny) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (-ny) * hs
  have e1 : 3 / 2 * D ^ 2 / (ny * s) + (ny * nw - ny * s) ^ 2 / (2 * (ny * s)) =
      (3 / 2 * D ^ 2 + (ny * nw - ny * s) ^ 2 / 2) * (1 / (ny * s)) := by ring
  rw [e1, hinv] at h2
  have k1 : (3 / 2 * D ^ 2 + (ny * nw - ny * s) ^ 2 / 2) * (s / (2 * ny)) ≤
      (3 / 2 * D ^ 2 + ny * ny * V / 4) * (s / (2 * ny)) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [hNy] at h3
    linarith
  have e2 : (3 / 2 * D ^ 2 + ny * ny * V / 4) * (s / (2 * ny)) =
      3 * s / (4 * ny) * D ^ 2 + ny * s / 8 * V := by
    field_simp; ring
  have k2 := mul_le_mul_of_nonneg_left (h2.trans (k1.trans (le_of_eq e2))) hC
  have e3 : C * (3 * s / (4 * ny) * D ^ 2 + ny * s / 8 * V) =
      3 * C * s / (4 * ny) * D ^ 2 + C * ny * s / 8 * V := by ring
  rw [e3] at k2
  linarith

lemma dev_sq {r s : ℝ} (hr : 0 ≤ r) (hs0 : 0 < s) (hs : s * s = 2) :
    (r - s) ^ 2 * 2 ≤ (r ^ 2 - 2) ^ 2 := by
  have e : r ^ 2 - 2 = (r - s) * (r + s) := by linear_combination hs
  have h4 : 2 ≤ (r + s) ^ 2 := by nlinarith
  rw [e, mul_pow]
  exact mul_le_mul_of_nonneg_left h4 (sq_nonneg _)

lemma quadB_arith {A ny I1 b C n' ε s : ℝ} (hA : 0 ≤ A) (hny : 0 < ny) (hn : 0 < n')
    (uN : I1 ≤ s) :
    A * ny * I1 + 0 - -b * 0 - -(3 * C * s / (4 * ny)) * (2 / n' * 1 * (ny * ny)) -
      -(C * ny * s / 8) * (4 * ε) ≤ ny * s * (A + C * (3 / (2 * n') + ε / 2)) := by
  have t1 := mul_le_mul_of_nonneg_left uN (mul_nonneg hA hny.le)
  have e : 3 * C * s / (4 * ny) * (2 / n' * 1 * (ny * ny)) = ny * s * (C * (3 / (2 * n'))) := by
    field_simp; ring
  have e' : C * ny * s / 8 * (4 * ε) = ny * s * (C * (ε / 2)) := by ring
  nlinarith

lemma quad_pt_vec {b C : ℝ} (hq : QuadBound b C) (hC : 0 ≤ C) {y : Fin n → ℝ}
    (hy : 0 < nrm y) (w : Fin n → ℝ) (c0 : ℝ) :
    psi (kappa ∘ kappa) y w + c0 * (nrm y * nrm w) ≤
      (kappa (kappa 0) + c0) * nrm y * nrm w + 0 - -b * dotp y w -
        -(3 * C * √2 / (4 * nrm y)) * dotp y w ^ 2 -
        -(C * nrm y * √2 / 8) * (normSq w - 2) ^ 2 := by
  have hs0 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hs : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have h1 := psi_quad hq y w
  have h2 := sq_div_le (nrm_mul_nonneg y w) (abs_dotp_le_nrm y w) (mul_pos hy hs0)
  have h3 : (nrm y * nrm w - nrm y * √2) ^ 2 ≤ normSq y * (normSq w - 2) ^ 2 / 2 := by
    have d := dev_sq (nrm_nonneg w) hs0 hs
    rw [nrm_sq w] at d
    have e1 : (nrm y * nrm w - nrm y * √2) ^ 2 = normSq y * (nrm w - √2) ^ 2 := by
      rw [← nrm_sq y]; ring
    rw [e1]
    have hN := normSq_nonneg y
    nlinarith [mul_le_mul_of_nonneg_left d hN]
  exact quad_pt hC hy hs0 hs (nrm_mul_self y).symm h1 h2 h3

/-- For a fixed vector `y`: the mean over the independent network `A′`, second-order form. -/
theorem agentB_upper2 {b C : ℝ} (hq : QuadBound b C) (hC : 0 ≤ C) (hn : 1 ≤ n) (hmA : 1 ≤ mA)
    (y : Fin n → ℝ) {x' : Fin n → ℝ} (hx' : normSq x' = 1) (c0 : ℝ) (hc0 : 0 ≤ c0) :
    ∫ a' : MlpParam n mA n, (psi (kappa ∘ kappa) y (mlpEval a' x') +
      c0 * (nrm y * nrm (mlpEval a' x'))) ∂mlpGauss n mA n ≤
    nrm y * √2 * (kappa (kappa 0) + c0 + C * (3 / (2 * (n : ℝ)) + eps4 n mA / 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hq0 : 0 ≤ kappa (kappa 0) := hG.nonneg_on KGood.zero_mem
  rcases eq_or_lt_of_le (nrm_nonneg y) with hy | hy
  · -- `y = 0`
    have e : ∀ a' : MlpParam n mA n, psi (kappa ∘ kappa) y (mlpEval a' x') +
        c0 * (nrm y * nrm (mlpEval a' x')) = 0 := by
      intro a'; unfold psi; rw [← hy]; simp
    simp_rw [e]
    rw [← hy]; simp
  obtain ⟨iN, uN⟩ := mlp_nrm_single (q := n) hmA x'
  obtain ⟨iM, eM⟩ := mlp_form_mean (q := n) hmA y x'
  obtain ⟨iS, eS⟩ := mlp_form_sq (q := n) hmA y x'
  obtain ⟨iV, eV⟩ := agent_sq_var hn hmA hx'
  obtain ⟨iB, -⟩ := agentB_upper hn hmA y x' c0 hc0
  obtain ⟨iR, eR⟩ := integral_lin4 (μ := mlpGauss n mA n) iN iM iS iV 0
    ((kappa (kappa 0) + c0) * nrm y) (-b) (-(3 * C * √2 / (4 * nrm y))) (-(C * nrm y * √2 / 8))
  have hmono := integral_mono iB iR (fun a' => quad_pt_vec hq hC hy (mlpEval a' x') c0)
  rw [eR, eM, eS, eV, hx', ← nrm_mul_self y] at hmono
  refine hmono.trans ?_
  have e2n : (2 : ℝ) * (n : ℝ) / n = 2 := by field_simp
  rw [e2n, nrm_of_normSq_one hx', mul_one] at uN
  have := quadB_arith (b := b) (C := C) (ε := eps4 n mA) (by linarith : 0 ≤ kappa (kappa 0) + c0)
    hy hn' uN
  exact this

/-- The inner bound, for a fixed first network `a`. -/
lemma kern_cross_inner2 {b C : ℝ} (hq : QuadBound b C) (hC : 0 ≤ C) (hn : 1 ≤ n) (hmA : 1 ≤ mA)
    (hmF : 1 ≤ mF) (a : MlpParam n mA n) {x x' : Fin n → ℝ} (hx' : normSq x' = 1) :
    ∫ y : MlpParam n mA n × MlpParam n mF 1, kern y.2 a y.1 x x'
      ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) ≤
    2 / (n : ℝ) * (nrm (mlpEval a x) * (√2 *
      (kappa (kappa 0) + cF mF + C * (3 / (2 * (n : ℝ)) + eps4 n mA / 2)))) := by
  obtain ⟨iB, -⟩ := agentB_upper hn hmA (mlpEval a x) x' (cF mF) (cF_nonneg mF)
  have uB := agentB_upper2 hq hC hn hmA (mlpEval a x) hx' (cF mF) (cF_nonneg mF)
  have key := integral_prod_le (kern_cross_inner_integrable hn hmF a x x')
    (g := fun a' : MlpParam n mA n => 2 / (n : ℝ) *
      (psi (kappa ∘ kappa) (mlpEval a x) (mlpEval a' x') +
        cF mF * (nrm (mlpEval a x) * nrm (mlpEval a' x'))))
    (iB.const_mul _) (fun a' => KF_upper hn hmF (mlpEval a x) (mlpEval a' x'))
  refine key.trans ?_
  rw [integral_const_mul]
  rw [mul_assoc] at uB
  exact mul_le_mul_of_nonneg_left uB (by positivity)

/-- **The cross kernel, second-order bound**: for unit vectors `x, x′`,
`E kern F A A′ x x′ ≤ (4/n)·(q + cF m_F + C·(3/(2n) + eps4/2))`. -/
theorem kern_cross_upper2 {b C : ℝ} (hq : QuadBound b C) (hC : 0 ≤ C) (hn : 1 ≤ n)
    (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    ∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1, kern p.2.2 p.1 p.2.1 x x'
      ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) ≤
    4 / (n : ℝ) * (kappa (kappa 0) + cF mF + C * (3 / (2 * (n : ℝ)) + eps4 n mA / 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨iN, uN⟩ := mlp_nrm_single (q := n) hmA x
  set K : ℝ := √2 * (kappa (kappa 0) + cF mF + C * (3 / (2 * (n : ℝ)) + eps4 n mA / 2)) with hK
  have hK0 : 0 ≤ K := by
    have h1 : 0 ≤ kappa (kappa 0) := (kGood_kappa.comp_kappa).nonneg_on KGood.zero_mem
    have h2 := cF_nonneg mF
    have h3 := eps4_nonneg n mA
    rw [hK]; positivity
  have key := integral_prod_le (kern_cross_integrable hn hmA hmF x x')
    (g := fun a : MlpParam n mA n => 2 / (n : ℝ) * (nrm (mlpEval a x) * K))
    ((iN.mul_const _).const_mul _) (fun a => kern_cross_inner2 hq hC hn hmA hmF a hx')
  refine key.trans ?_
  rw [integral_const_mul, integral_mul_const]
  have e : (2 : ℝ) * (n : ℝ) / n = 2 := by field_simp
  rw [e, nrm_of_normSq_one hx, mul_one] at uN
  have h1 := mul_le_mul_of_nonneg_right uN hK0
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 / (n : ℝ))
  refine h2.trans (le_of_eq ?_)
  have s2 : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  rw [hK]
  calc 2 / (n : ℝ) * (√2 * (√2 * (kappa (kappa 0) + cF mF +
        C * (3 / (2 * (n : ℝ)) + eps4 n mA / 2))))
      = 2 / (n : ℝ) * ((√2 * √2) * (kappa (kappa 0) + cF mF +
        C * (3 / (2 * (n : ℝ)) + eps4 n mA / 2))) := by ring
    _ = _ := by rw [s2]; ring

variable {N mW : ℕ}

lemma kgen_ftf_section2 {b C : ℝ} (hq : QuadBound b C) (hC : 0 ≤ C) (hn : 1 ≤ n) (hmA : 1 ≤ mA)
    (hmF : 1 ≤ mF) (uu : (Fin N → ℝ) × (Fin N → ℝ)) (w : MlpParam N mW n) :
    ∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1, kgen false true false (uu, (w, p))
      ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) ≤
    4 / (n : ℝ) * (kappa (kappa 0) + cF mF + C * (3 / (2 * (n : ℝ)) + eps4 n mA / 2)) := by
  simp only [kgen_ftf_eq]
  exact kern_cross_upper2 hq hC hn hmA hmF (normSq_xW hn w uu.1) (normSq_xW hn w uu.2)

/-- **The upper bound of `b₁₁`, second-order form** (paper: `b₁₁ ≤ S(q + 2.76/n + c₀/√m_F)`):
`b11 ≤ (4/n)·(q + cF m_F + C·(3/(2n) + eps4 n m_A/2))` for every quadratic bound `C` of `κ∘κ`. -/
theorem b11_upper2 {b C : ℝ} (hq : QuadBound b C) (hC : 0 ≤ C) (hN : 1 ≤ N) (hn : 1 ≤ n)
    (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) :
    b11 N mW n mA mF ≤
      4 / (n : ℝ) * (kappa (kappa 0) + cF mF + C * (3 / (2 * (n : ℝ)) + eps4 n mA / 2)) := by
  have := uniformSphere_isProbability N hN
  have hprob : IsProbabilityMeasure (lawU2 N) := by unfold lawU2; infer_instance
  rw [b11_eq]
  exact integral_le_of_sections (lawU2 N) (mlpGauss N mW n)
    ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
    (f := kgen false true false) (kgen_integrable hn hN false true false)
    (kgen_ftf_section2 hq hC hn hmA hmF)

end BstLean.Part132

open BstLean.Part132 in
#print axioms b11_upper2
