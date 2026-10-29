import BstLean.Part142Stmt
import BstLean.Part139Scale

/-!
# Part 142: the link `F` of the distance kernel

Role: `delegations/statements/p142-spec.md`, item 2 (sharper kernel bounds). The two hidden
layers of `F` for the DISTANCE form: with `H(y) = hid2 F₁ F₂ y = ReLU(F₂ ReLU(F₁ y))`,
`e = eD` (`|a − b|²/2`), `Φ_G = phiD G`, `δ = dlt`:

* `F_dist_L2_of`: `‖(2/m_F)·e(H(y), H(y′)) − (2/n)·Φ_{κ∘κ}(y, y′)‖₂ ≤
    (2/n)·(f1·|y − y′|² + f2·(|y|² + |y′|²) + f3·||y|² − |y′|²| + f4·δ(y, y′))`, for ALL `y, y′`.
  The one-layer links `ReluEDStmt`, `ReluPhiStmt` of `Part142Stmt` are hypotheses.
* `f1 = 2√3/√m_F + 6/m_F`, `f2 = b_κ·√5/(2√m_F) + κ(0)·4K_r/m_F`, `f3 = κ(0)·√5/√m_F`,
  `f4 = 2κ(0)`; at the Focus width, `n ≥ 4096`: `f1 ≤ 0.4345/√n`, `f2 ≤ 0.0515/√n`,
  `f3 ≤ 0.089/√n`, `f4 ≤ 0.63662`.
* `kernD_eq`: `(k(x, x) + k(x′, x′))/2 − k(x, x′) = (2/m_F)·e(H(A x), H(A x′))`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133

/-! ## Pointwise facts -/

section pointwise

variable {ι : Type*} [Fintype ι]

lemma dotp_le_psi_kappa (y y' : ι → ℝ) : dotp y y' ≤ psi kappa y y' := by
  have h := kGood_kappa.self_le (cosv_mem y y')
  have hp := nrm_mul_nonneg y y'
  rw [dotp_eq_cosv_mul]
  unfold psi
  nlinarith

lemma phiD_kappa_le_eD (y y' : ι → ℝ) : phiD kappa y y' ≤ eD y y' := by
  unfold phiD eD
  linarith [dotp_le_psi_kappa y y']

lemma phiD_kappa_nonneg (y y' : ι → ℝ) : 0 ≤ phiD kappa y y' := by
  unfold phiD
  linarith [psi_le_nrm kGood_kappa y y', nrm_mul_le y y']

end pointwise

/-! ## The constants -/

/-- The coefficient of `|y − y′|²`. -/
noncomputable def f1 (mF : ℕ) : ℝ := 2 * √3 / √(mF : ℝ) + 6 / (mF : ℝ)

/-- The coefficient of `|y|² + |y′|²`. -/
noncomputable def f2 (mF : ℕ) : ℝ :=
  bG kappa * (√5 / (2 * √(mF : ℝ))) + kappa 0 * (4 * Kr mF / (mF : ℝ))

/-- The coefficient of `||y|² − |y′|²|`. -/
noncomputable def f3 (mF : ℕ) : ℝ := kappa 0 * (√5 / √(mF : ℝ))

/-- The coefficient of `δ(y, y′)`. -/
noncomputable def f4 : ℝ := 2 * kappa 0

lemma kappa0_nonneg : 0 ≤ kappa 0 := (kappa_mem (t := 0) (by norm_num) (by norm_num)).1

lemma f1_nonneg (mF : ℕ) : 0 ≤ f1 mF := by unfold f1; positivity

lemma f2_nonneg (mF : ℕ) : 0 ≤ f2 mF := by
  have := bG_nonneg kGood_kappa
  have := kappa0_nonneg
  have := Kr_nonneg mF
  unfold f2
  positivity

lemma f3_nonneg (mF : ℕ) : 0 ≤ f3 mF := by
  have := kappa0_nonneg
  unfold f3
  positivity

lemma f4_nonneg : 0 ≤ f4 := by
  have := kappa0_nonneg
  unfold f4
  positivity

/-! ## The link -/

section link

variable {n mF : ℕ}

/-- The two hidden layers, on the product of the two Gaussian matrices. -/
theorem hid2_dist_L2_of (hRE : ReluEDStmt) (hRP : ReluPhiStmt) (hn : 1 ≤ n) (hmF : 1 ≤ mF)
    (y y' : Fin n → ℝ) :
    L2le ((gaussMat mF n (2 / (n : ℝ))).prod (gaussMat mF mF (2 / (mF : ℝ))))
      (fun θ : Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ =>
        2 / (mF : ℝ) * eD (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y') -
          2 / (n : ℝ) * phiD (kappa ∘ kappa) y y')
      (2 / (n : ℝ) * (f1 mF * normSq (y - y') + f2 mF * (normSq y + normSq y') +
        f3 mF * |normSq y - normSq y'| + f4 * dlt y y')) := by
  have hm0 : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv1 : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hv2 : (0 : ℝ) < 2 / (mF : ℝ) := by positivity
  set s : ℝ := √(mF : ℝ) with hsd
  set t : ℝ := √3 with htd
  have hs0 : 0 < s := Real.sqrt_pos.mpr hm0
  have hss : s * s = (mF : ℝ) := Real.mul_self_sqrt hm0.le
  have htt : t * t = 3 := Real.mul_self_sqrt (by norm_num)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  set N : ℝ := normSq (y - y') with hN
  have hN0 : 0 ≤ N := normSq_nonneg _
  have hk0 := kappa0_nonneg
  have hb0 := bG_nonneg kGood_kappa
  have hKr := Kr_nonneg mF
  have hdl := dlt_nonneg y y'
  have hS0 : 0 ≤ normSq y + normSq y' := add_nonneg (normSq_nonneg _) (normSq_nonneg _)
  -- the first layer: the `L²` norm of `|h₁ − h₁′|²`
  have hE1 := hRE (m := mF) (k := n) hv1 hmF y y'
  set c : ℝ := (mF : ℝ) / 2 * (2 / (n : ℝ)) * phiD kappa y y' with hc
  have hc0 : 0 ≤ c := mul_nonneg (by positivity) (phiD_kappa_nonneg y y')
  have hcle : c ≤ (mF : ℝ) / 2 * (2 / (n : ℝ)) * (N / 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hN, ← eD_eq]
    exact phiD_kappa_le_eD y y'
  have hcc : L2le (gaussMat mF n (2 / (n : ℝ))) (fun _ : Matrix (Fin mF) (Fin n) ℝ => c) |c| :=
    L2le.const c
  rw [abs_of_nonneg hc0] at hcc
  set K : ℝ := t / 2 * s * (2 / (mF : ℝ)) * 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hE1' : L2le (gaussMat mF n (2 / (n : ℝ)))
      (fun M : Matrix (Fin mF) (Fin n) ℝ =>
        eD (reluV (M.mulVec y)) (reluV (M.mulVec y')) - c)
      (t / 2 * s * (2 / (n : ℝ)) * N) := hE1
  have hg0 := ((hE1'.add0 hcc (by positivity) hc0).const_mul_nonneg hK0).mono
    (by positivity)
    (show K * (t / 2 * s * (2 / (n : ℝ)) * N + c) ≤
      K * (t / 2 * s * (2 / (n : ℝ)) * N + (mF : ℝ) / 2 * (2 / (n : ℝ)) * (N / 2)) from
      mul_le_mul_of_nonneg_left (by linarith) hK0)
  have eK : K * (t / 2 * s * (2 / (n : ℝ)) * N + (mF : ℝ) / 2 * (2 / (n : ℝ)) * (N / 2)) =
      6 * (N / (n : ℝ)) + t * s * (N / (n : ℝ)) := by
    have e : K * (t / 2 * s * (2 / (n : ℝ)) * N + (mF : ℝ) / 2 * (2 / (n : ℝ)) * (N / 2)) =
        (t * t) * ((s * s) / (mF : ℝ)) * (2 * (N / (n : ℝ))) +
          t * s * (N / (n : ℝ)) * ((mF : ℝ) / (mF : ℝ)) := by
      rw [hK]; ring
    rw [e, htt, hss, div_self hm0.ne']
    ring
  have hg : L2le (gaussMat mF n (2 / (n : ℝ)))
      (fun M₁ : Matrix (Fin mF) (Fin n) ℝ => t / 2 * s * (2 / (mF : ℝ)) *
        normSq (reluV (M₁.mulVec y) - reluV (M₁.mulVec y')))
      (6 * (N / (n : ℝ)) + t * s * (N / (n : ℝ))) := by
    refine (hg0.congr_fun fun M₁ => ?_).congr_bound eK
    rw [eD_eq, hK]
    ring
  -- bracket A: the last hidden layer
  have cE : Continuous (fun θ : Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ =>
      eD (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y')) := by
    unfold eD
    exact (((continuous_normSq.comp (continuous_hid2_param y)).add
      (continuous_normSq.comp (continuous_hid2_param y'))).div_const 2).sub
      (continuous_dotp.comp ((continuous_hid2_param y).prodMk (continuous_hid2_param y')))
  have mP : Measurable (fun M₁ : Matrix (Fin mF) (Fin n) ℝ =>
      phiD kappa (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y'))) := by
    unfold phiD
    exact (((measurable_normSq.comp (measurable_reluV.comp (measurable_mulVec_right y))).add
      (measurable_normSq.comp (measurable_reluV.comp (measurable_mulVec_right y')))).div_const
      2).sub (measurable_psi_relu continuous_kappa y y')
  have mA : Measurable (fun θ : Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ =>
      eD (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y') -
        (mF : ℝ) / 2 * (2 / (mF : ℝ)) *
          phiD kappa (reluV (θ.1.mulVec y)) (reluV (θ.1.mulVec y'))) :=
    cE.measurable.sub ((mP.comp measurable_fst).const_mul _)
  have hA : L2le ((gaussMat mF n (2 / (n : ℝ))).prod (gaussMat mF mF (2 / (mF : ℝ))))
      (fun θ : Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ =>
        eD (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y') -
          (mF : ℝ) / 2 * (2 / (mF : ℝ)) *
            phiD kappa (reluV (θ.1.mulVec y)) (reluV (θ.1.mulVec y')))
      (6 * (N / (n : ℝ)) + t * s * (N / (n : ℝ))) := by
    refine L2le.prod' mA.aestronglyMeasurable hg (Filter.Eventually.of_forall fun M₁ => ?_)
    exact hRE (m := mF) (k := mF) hv2 hmF (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y'))
  -- bracket B: the first hidden layer
  have hB := (hRP (m := mF) (k := n) kGood_kappa hv1 hmF y y').comp_fst
    (ν := gaussMat mF mF (2 / (mF : ℝ)))
  have hsum := (hA.add0 hB (by positivity) (by positivity)).const_mul_nonneg
    (c := 2 / (mF : ℝ)) (by positivity)
  refine (hsum.congr_fun fun θ => ?_).congr_bound ?_
  · field_simp
    ring
  · unfold f1 f2 f3 f4
    rw [← hsd, ← htd]
    have hm2 : (mF : ℝ) = s ^ 2 := by rw [← hss]; ring
    rw [hm2]
    field_simp
    ring

/-- **The link `F` of the distance kernel**, for all `y, y′`. -/
theorem F_dist_L2_of (hRE : ReluEDStmt) (hRP : ReluPhiStmt) (hn : 1 ≤ n) (hmF : 1 ≤ mF)
    (y y' : Fin n → ℝ) :
    L2le (mlpGauss n mF 1)
      (fun F : MlpParam n mF 1 =>
        2 / (mF : ℝ) * eD (hid2 F.1 F.2.1 y) (hid2 F.1 F.2.1 y') -
          2 / (n : ℝ) * phiD (kappa ∘ kappa) y y')
      (2 / (n : ℝ) * (f1 mF * normSq (y - y') + f2 mF * (normSq y + normSq y') +
        f3 mF * |normSq y - normSq y'| + f4 * dlt y y')) :=
  (hid2_dist_L2_of hRE hRP hn hmF y y').comp_map (P := mlpGauss n mF 1)
    (φ := fun θ : MlpParam n mF 1 => (θ.1, θ.2.1)) (by fun_prop)
    (by unfold mlpGauss; exact map_drop3)

end link

/-! ## The distance kernel -/

/-- `(k(x, x) + k(x′, x′))/2 − k(x, x′) = (2/m_F)·e(H(A x), H(A x′))`. -/
theorem kernD_eq {n mA mF : ℕ} (F : MlpParam n mF 1) (A : MlpParam n mA n) (x x' : Fin n → ℝ) :
    (kern F A A x x + kern F A A x' x') / 2 - kern F A A x x' =
      2 / (mF : ℝ) * eD (hid2 F.1 F.2.1 (mlpEval A x)) (hid2 F.1 F.2.1 (mlpEval A x')) := by
  unfold kern hidF eD
  rw [dotp_self, dotp_self]
  ring

/-! ## The numbers at the Focus -/

lemma sqrt5_le : √(5 : ℝ) ≤ 223607 / 100000 := sqrt_le_of_sq (by norm_num) (by norm_num)

lemma bG_kappa_le : bG kappa ≤ 363382 / 1000000 := by
  have := kappa_zero_ge
  unfold bG
  rw [kappa_neg_one]
  linarith

section numbers

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

/-- `1/√m_F ≤ (1/8)·(1/√n)` and `1/m_F ≤ (1/4096)·(1/√n)`. -/
lemma inv_mF_scale :
    1 / √(mF n : ℝ) ≤ 1 / 8 * (1 / √(n : ℝ)) ∧ 1 / (mF n : ℝ) ≤ 1 / 4096 * (1 / √(n : ℝ)) := by
  have hx := nR_ge hn
  have hs := sqrt_n_ge hn
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (by linarith)
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hms := BstLean.Part139.mF_ge_s hn
  have hm0 : (0 : ℝ) < mF n := by nlinarith
  have h8 : 8 * √(n : ℝ) ≤ √(mF n : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith
  constructor
  · rw [div_le_iff₀ (by linarith)]
    have e : 1 / 8 * (1 / √(n : ℝ)) * √(mF n : ℝ) = √(mF n : ℝ) / (8 * √(n : ℝ)) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  · rw [div_le_iff₀ hm0]
    have e : 1 / 4096 * (1 / √(n : ℝ)) * (mF n : ℝ) = (mF n : ℝ) / (4096 * √(n : ℝ)) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith

lemma f1_scale : f1 (mF n) ≤ 4345 / 10000 / √(n : ℝ) := by
  obtain ⟨ha, hb⟩ := inv_mF_scale hn
  have hs := sqrt_n_ge hn
  have hr0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  have ha0 : (0 : ℝ) ≤ 1 / √(mF n : ℝ) := by positivity
  have h3 := sqrt3_le
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  have e : f1 (mF n) = 2 * (√3 * (1 / √(mF n : ℝ))) + 6 * (1 / (mF n : ℝ)) := by
    unfold f1; ring
  have e2 : 4345 / 10000 / √(n : ℝ) = 4345 / 10000 * (1 / √(n : ℝ)) := by ring
  rw [e, e2]
  have p1 : √3 * (1 / √(mF n : ℝ)) ≤ 17321 / 10000 * (1 / 8 * (1 / √(n : ℝ))) :=
    mul_le_mul h3 ha ha0 (by norm_num)
  linarith

lemma Kr_le : Kr (mF n) ≤ 21652 / 10000 := by
  have hm := mF_geR hn
  unfold Kr
  refine sqrt_le_of_sq (by norm_num) ?_
  have : 35 / (mF n : ℝ) ≤ 35 / 262144 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm
  norm_num at this ⊢
  linarith

lemma f2_scale : f2 (mF n) ≤ 515 / 10000 / √(n : ℝ) := by
  obtain ⟨ha, hb⟩ := inv_mF_scale hn
  have hr0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  have ha0 : (0 : ℝ) ≤ 1 / √(mF n : ℝ) := by positivity
  have hb0 : (0 : ℝ) ≤ 1 / (mF n : ℝ) := by positivity
  have h5 := sqrt5_le
  have h50 := Real.sqrt_nonneg (5 : ℝ)
  have hbG := bG_kappa_le
  have hbG0 := bG_nonneg kGood_kappa
  have hk := kappa_zero_le
  have hk0 := kappa0_nonneg
  have hKr := Kr_le hn
  have hKr0 := Kr_nonneg (mF n)
  have e : f2 (mF n) = bG kappa * √5 / 2 * (1 / √(mF n : ℝ)) +
      4 * (kappa 0 * Kr (mF n)) * (1 / (mF n : ℝ)) := by
    unfold f2; ring
  have e2 : 515 / 10000 / √(n : ℝ) = 515 / 10000 * (1 / √(n : ℝ)) := by ring
  rw [e, e2]
  have p0 : bG kappa * √5 ≤ 363382 / 1000000 * (223607 / 100000) :=
    mul_le_mul hbG h5 h50 (by norm_num)
  have p1 : bG kappa * √5 / 2 * (1 / √(mF n : ℝ)) ≤
      363382 / 1000000 * (223607 / 100000) / 2 * (1 / 8 * (1 / √(n : ℝ))) :=
    mul_le_mul (by linarith) ha ha0 (by norm_num)
  have q0 : kappa 0 * Kr (mF n) ≤ 31831 / 100000 * (21652 / 10000) :=
    mul_le_mul hk hKr hKr0 (by norm_num)
  have q1 : 4 * (kappa 0 * Kr (mF n)) * (1 / (mF n : ℝ)) ≤
      4 * (31831 / 100000 * (21652 / 10000)) * (1 / 4096 * (1 / √(n : ℝ))) :=
    mul_le_mul (by linarith) hb hb0 (by norm_num)
  linarith

lemma f3_scale : f3 (mF n) ≤ 890 / 10000 / √(n : ℝ) := by
  obtain ⟨ha, hb⟩ := inv_mF_scale hn
  have hr0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  have ha0 : (0 : ℝ) ≤ 1 / √(mF n : ℝ) := by positivity
  have h5 := sqrt5_le
  have h50 := Real.sqrt_nonneg (5 : ℝ)
  have hk := kappa_zero_le
  have hk0 := kappa0_nonneg
  have e : f3 (mF n) = kappa 0 * √5 * (1 / √(mF n : ℝ)) := by
    unfold f3; ring
  have e2 : 890 / 10000 / √(n : ℝ) = 890 / 10000 * (1 / √(n : ℝ)) := by ring
  rw [e, e2]
  have p0 : kappa 0 * √5 ≤ 31831 / 100000 * (223607 / 100000) :=
    mul_le_mul hk h5 h50 (by norm_num)
  have p1 : kappa 0 * √5 * (1 / √(mF n : ℝ)) ≤
      31831 / 100000 * (223607 / 100000) * (1 / 8 * (1 / √(n : ℝ))) :=
    mul_le_mul p0 ha ha0 (by norm_num)
  linarith

end numbers

lemma f4_le : f4 ≤ 63662 / 100000 := by
  have := kappa_zero_le
  unfold f4
  linarith

end BstLean.Part142

open BstLean.Part142 in
#print axioms F_dist_L2_of
open BstLean.Part142 in
#print axioms kernD_eq
open BstLean.Part142 in
#print axioms f1_scale
open BstLean.Part142 in
#print axioms f2_scale
open BstLean.Part142 in
#print axioms f3_scale
open BstLean.Part142 in
#print axioms f4_le
