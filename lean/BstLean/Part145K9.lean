import BstLean.Part145K7
import BstLean.Part145K8

/-!
# Part 145 (K9): the Agent network and the assembly with the sharper second-order term

`kX n = cDx n/2` (file `Part145K8`) is in the place of `K4 n` in the remainder of the link of
the last matrix of the Agent network, and in the term `δ` of its two outputs.

* `linSecRx`, `rQx`, `rR0x n mA = rQx n mA 0 0 0`; **`agent_rem_L2x`**: the copy of
  `agent_rem_L2` with `rR0x` in the place of `rR0` (`rR1`, `rR1'`, `rR2` do not change).
* `linLx`, `cAdltx n mA = LS mA + kX n/n·SS mA + (1/√(2n))·DS mA`; **`agent_dlt_L2x_of`**:
  the copy of `agent_dlt_L2_of`.
* `rRx_ref_nonneg`: the reference value of the bound of the remainder is `≥ 0`.
* `eDBq bK τ pW n`, **`kernBq`**: `eDBp`, `kernBp` of `Part145K7` with `rR0x`, `cAdltx`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142 BstLean.Part143

open AgD AgS AgC AgK

/-! ## One linear layer in the shapes of the chain -/

section gen

variable {m k : ℕ} {v : ℝ}

/-- `linRem_L2x` in the shape of `comboS`. -/
lemma linSecRx {G : ℝ → ℝ} (hG : KGood G) (hv : 0 < v) (hm : 1 ≤ m) (y y' : Fin k → ℝ)
    (hd : 0 ≤ dotp y y') :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        phiD G (M.mulVec y) (M.mulVec y') - (m : ℝ) * v * phiD G y y' - cLin G m v M y y')
      ((m : ℝ) * v * (fR G y y' / √(m : ℝ) + kX m / (m : ℝ) * (normSq y + normSq y') +
        |normSq y - normSq y'| / √(2 * (m : ℝ)))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hK := kX_nonneg m
  have hf := fR_nonneg hG y y' hd
  have hnn := nrm_mul_nonneg y y'
  have hle := nrm_mul_le y y'
  have h0 := linRem_L2x hG hv hm y y' hd
  have e : (phiD G y y' - dlt y y') - (1 - G (-1)) / 2 * (eD y y' - dlt y y') =
      fR G y y' := rfl
  rw [e] at h0
  refine h0.mono (by positivity) ?_
  have h1 : 2 * kX m / (m : ℝ) * (nrm y * nrm y') ≤
      kX m / (m : ℝ) * (normSq y + normSq y') := by
    have : 2 * kX m / (m : ℝ) * (nrm y * nrm y') = kX m / (m : ℝ) * (2 * (nrm y * nrm y')) := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hs : 0 ≤ (m : ℝ) * v := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hs

/-- `linDltX` in the shape of `comboDlt`. -/
lemma linLx (hv : 0 < v) (hm : 1 ≤ m) (h h' : Fin k → ℝ) :
    L2nn (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => dlt (M.mulVec h) (M.mulVec h'))
      ((m : ℝ) * v * (dlt h h' + kX m / (m : ℝ) * (normSq h + normSq h') +
        1 / √(2 * (m : ℝ)) * |normSq h - normSq h'|)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN := normSq_nonneg h
  have hN' := normSq_nonneg h'
  have hd := dlt_nonneg h h'
  have hK := cDx_nonneg m
  exact (addConst (linDltX hv hm h h') (by positivity) (by positivity)).congr (fun _ => rfl)
    (by unfold kX; ring)

end gen

/-! ## The constants -/

/-- The bound of `agent_rem_L2x` (without the factor `2`): `rQ` with `kX` in the place of
`K4`. -/
noncomputable def rQx (n m : ℕ) (a4 a2 u : ℝ) : ℝ :=
  (a4 - cgS (kappa ∘ kappa) * a2 + q3 m u + cgS (kappa ∘ kappa) * bkS m u + q2 m u +
      cgS (kappa ∘ kappa) * (√3 / √(m : ℝ) * eS m u) +
      (1 + cgS (kappa ∘ kappa)) * LS m) / √(n : ℝ) +
    kX n / (n : ℝ) * SS m + DS m / √(2 * (n : ℝ)) + q2 m u + q3 m u

/-- The constant term of `agent_rem_L2x`. -/
noncomputable def rR0x (n mA : ℕ) : ℝ := rQx n mA 0 0 0

/-- The bound of `agent_dlt_L2x_of` (without the factor `2`). -/
noncomputable def cAdltx (n mA : ℕ) : ℝ :=
  LS mA + kX n / (n : ℝ) * SS mA + 1 / √(2 * (n : ℝ)) * DS mA

lemma rQx_affine (n m : ℕ) (a4 a2 u : ℝ) :
    rQx n m a4 a2 u = rR0x n m + rR1 n * a4 - rR1' n * a2 + rR2 n m * u := by
  unfold rR0x rR1 rR1' rR2 sA1' rQx rQ q2 q3 bkS eS
  ring

lemma rR0x_eq (n m : ℕ) : rR0x n m =
    (q3 m 0 + cgS (kappa ∘ kappa) * nc0 m + q2 m 0 +
      (1 + cgS (kappa ∘ kappa)) * LS m) / √(n : ℝ) +
    kX n / (n : ℝ) * SS m + DS m / √(2 * (n : ℝ)) + q2 m 0 + q3 m 0 := by
  unfold rR0x rQx bkS eS nc0
  ring

/-- `rR0x = rR0 − (K4 n − kX n)/n·SS`. -/
lemma rR0x_eq_sub (n m : ℕ) : rR0x n m = rR0 n m - (K4 n - kX n) / (n : ℝ) * SS m := by
  rw [rR0x_eq, rR0_eq]
  ring

lemma cAdltx_eq (n m : ℕ) :
    cAdltx n m = LS m + cDx n / (2 * (n : ℝ)) * SS m + 1 / √(2 * (n : ℝ)) * DS m := by
  unfold cAdltx kX
  ring

lemma rR0x_nonneg (n m : ℕ) : 0 ≤ rR0x n m := by
  have hcg := cgS_nonneg (kGood_kappa.comp_kappa)
  have := nc0_nn m; have := SS_nn m; have := DS_nn m; have := LS_nn m
  have := kX_nonneg n
  have h2 := q2z_nn m
  have h3 := q3z_nn m
  rw [rR0x_eq]
  positivity

lemma cAdltx_nonneg (n m : ℕ) : 0 ≤ cAdltx n m := by
  have := SS_nn m; have := DS_nn m; have := LS_nn m; have := kX_nonneg n
  unfold cAdltx; positivity

/-! ## The statements -/

section main

variable {n m : ℕ}

/-- **The remainder of the Agent link after the centred part, in `L²`**, in terms of `rQx`. -/
theorem agent_rem_L2x_rQ (hn : 1 ≤ n) (hm : 1 ≤ m) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    L2le (mlpGauss n m n)
      (fun A : MlpParam n m n => phiD (kappa ∘ kappa) (mlpEval A x) (mlpEval A x') -
        2 * (1 - kappa^[4] (dotp x x')) - cAg A x x')
      (2 * rQx n m (1 - kappa^[4] (dotp x x')) (1 - kappa (kappa (dotp x x')))
        (1 - dotp x x')) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  have hb2 := bG_nonneg hG
  have hb3 := bG_nonneg hGk
  have hcg := cgS_nonneg hG
  have hg2 : 0 ≤ (kappa ∘ kappa) 0 := hG.nonneg_on KGood.zero_mem
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have hKm := Kr_nonneg m
  have hK4 := kX_nonneg n
  obtain ⟨hτ, hu⟩ := tau_nonneg hx hx'
  have hv1 : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hv2 : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hc3 : (0 : ℝ) ≤ (n : ℝ) * (2 / (m : ℝ)) := by positivity
  have hc2 : (0 : ℝ) ≤ (m : ℝ) / 2 * (2 / (m : ℝ)) := by positivity
  have hq : (0 : ℝ) ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hi : (0 : ℝ) ≤ √(2 * (n : ℝ)) := Real.sqrt_nonneg _
  have hk : (0 : ℝ) ≤ kX n / (n : ℝ) := by positivity
  have he3 : (0 : ℝ) ≤ √3 / √(m : ℝ) := by positivity
  have hq5 : (0 : ℝ) ≤ √(1 + 5 / (m : ℝ)) := Real.sqrt_nonneg _
  have he5 : (0 : ℝ) ≤ √5 / √(m : ℝ) := by positivity
  have hc5 : (0 : ℝ) ≤ √5 / (2 * √(m : ℝ)) := by positivity
  have hk4 : (0 : ℝ) ≤ 4 * Kr m / (m : ℝ) := by positivity
  have h1c : (0 : ℝ) ≤ 1 + cgS (kappa ∘ kappa) := by positivity
  have hc2e : (m : ℝ) / 2 * (2 / (m : ℝ)) = 1 := by field_simp
  have h31 : (n : ℝ) * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (n : ℝ))) = 2 := by field_simp
  -- the first hidden layer
  have aR := l1RR hn hm hx hx'
  have aE := l1E hn hm hx hx'
  have aS := l1S hn hm hx hx'
  have aD := l1D hn hm hx hx' reluSqStmt
  have aL := l1L hn hm hx hx' reluDltStmt
  have aΦ := l1Phi hn hm hx hx'
  have aLL : L2nn (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ => bL m (reluV (M.mulVec x)) (reluV (M.mulVec x')))
      ((m : ℝ) / 2 * (2 / (n : ℝ)) * LS m) :=
    ((aL.add (aS.smul hk4)).add (aD.smul he5)).congr (fun M => by unfold bL; ring)
      (by unfold LS; ring)
  have F1 : L2nn (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ =>
        bFR (kappa ∘ kappa) m (2 / (m : ℝ)) (reluV (M.mulVec x)) (reluV (M.mulVec x'))) _ :=
    ((((aR.add aΦ).add ((aE.smul he3).smul hcg)).add (aLL.smul h1c)).smul hc2).congr
      (fun M => by unfold bFR; ring) rfl
  have S1 := (aS.smul hq5).smul hc2
  have D1 := ((aS.smul he5).add aD).smul hc2
  -- measurability
  have mH2 : ∀ z : Fin n → ℝ, Measurable (fun A : MlpParam n m n =>
      reluV (A.2.1.mulVec (reluV (A.1.mulVec z)))) := fun z =>
    (continuous_reluV.comp (Continuous.matrix_mulVec (continuous_fst.comp continuous_snd)
      (continuous_reluV.comp
        (Continuous.matrix_mulVec continuous_fst continuous_const)))).measurable
  have mH1 : ∀ z : Fin n → ℝ, Measurable (fun A : MlpParam n m n =>
      reluV (A.1.mulVec z)) := fun z =>
    (continuous_reluV.comp (Continuous.matrix_mulVec continuous_fst continuous_const)).measurable
  have mf1 : Measurable (fun A : MlpParam n m n =>
      phiD (kappa ∘ kappa) (mlpEval A x) (mlpEval A x') -
        (n : ℝ) * (2 / (m : ℝ)) * phiD (kappa ∘ kappa)
          (reluV (A.2.1.mulVec (reluV (A.1.mulVec x))))
          (reluV (A.2.1.mulVec (reluV (A.1.mulVec x')))) - cAg A x x') :=
    ((mPair (m_phiD hG.cont) (measurable_mlpEval_param x) (measurable_mlpEval_param x')).sub
      ((mPair (m_phiD hG.cont) (mH2 x) (mH2 x')).const_mul _)).sub
      (measurable_cAg_param x x')
  have mf2 : Measurable (fun A : MlpParam n m n =>
      (n : ℝ) * (2 / (m : ℝ)) * (phiD (kappa ∘ kappa)
          (reluV (A.2.1.mulVec (reluV (A.1.mulVec x))))
          (reluV (A.2.1.mulVec (reluV (A.1.mulVec x')))) -
        (m : ℝ) / 2 * (2 / (m : ℝ)) * phiD ((kappa ∘ kappa) ∘ kappa)
          (reluV (A.1.mulVec x)) (reluV (A.1.mulVec x')))) :=
    ((mPair (m_phiD hG.cont) (mH2 x) (mH2 x')).sub
      ((mPair (m_phiD hGk.cont) (mH1 x) (mH1 x')).const_mul _)).const_mul _
  -- the last matrix
  have G1 := comboS F1 S1 D1 hc3 hq hk hi
  have T1 := prodNN (μ := gaussMat m n (2 / (n : ℝ)))
    (ν := (gaussMat m m (2 / (m : ℝ))).prod (gaussMat n m (2 / (m : ℝ)))) mf1 G1
    (fun M₁ => (prodNN (μ := gaussMat m m (2 / (m : ℝ))) (ν := gaussMat n m (2 / (m : ℝ)))
      (mf1.comp measurable_prodMk_left)
      (comboS (genFR hG hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x')))
        (genS hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x')))
        (genD reluSqStmt hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x'))) hc3 hq hk hi)
      (fun M₂ => linSecRx hG hv2 hn (reluV (M₂.mulVec (reluV (M₁.mulVec x))))
        (reluV (M₂.mulVec (reluV (M₁.mulVec x')))) (dotp_relu_nonneg _ _))).1)
  -- the second matrix
  have G2 := (comboRelu aE aS aD aL hc2 he3 hb2 hc5 hg2 hk4 he5).smul hc3
  have T2 := prodNN (μ := gaussMat m n (2 / (n : ℝ)))
    (ν := (gaussMat m m (2 / (m : ℝ))).prod (gaussMat n m (2 / (m : ℝ)))) mf2 G2
    (fun M₁ => ((reluPhiStmt hG hv2 hm (reluV (M₁.mulVec x))
      (reluV (M₁.mulVec x'))).const_mul_nonneg hc3).comp_fst)
  -- the first matrix
  have h3 := reluPhiStmt hGk hv1 hm x x'
  rw [normSq_sub_unit hx hx', hx, hx', dlt_unit hx hx', sub_self, abs_zero] at h3
  have T3 := ((h3.const_mul_nonneg hc2).const_mul_nonneg hc3).comp_fst
    (ν := (gaussMat m m (2 / (m : ℝ))).prod (gaussMat n m (2 / (m : ℝ))))
  have n3 : 0 ≤ (n : ℝ) * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (m : ℝ)) *
      ((m : ℝ) / 2 * (2 / (n : ℝ)) * (√3 / √(m : ℝ) * (2 * (1 - dotp x x')) +
        bG ((kappa ∘ kappa) ∘ kappa) * (√5 / (2 * √(m : ℝ))) * (1 + 1) +
        ((kappa ∘ kappa) ∘ kappa) 0 *
          (4 * Kr m / (m : ℝ) * (1 + 1) + √5 / √(m : ℝ) * 0 + 2 * 0)))) := by positivity
  have hsum := (T1.1.add0 T2.1 T1.2 T2.2).add0 T3 (add_nonneg T1.2 T2.2) n3
  have hph : phiD (((kappa ∘ kappa) ∘ kappa) ∘ kappa) x x' = 1 - kappa^[4] (dotp x x') := by
    rw [phiD_unit _ hx hx']; rfl
  unfold mlpGauss
  refine (hsum.congr_fun fun A => ?_).congr_bound ?_
  · rw [hph]
    linear_combination (-((1 - kappa^[4] (dotp x x')) * ((n : ℝ) * (2 / (m : ℝ))) *
      ((m : ℝ) / 2 * (2 / (n : ℝ))))) * hc2e + (-(1 - kappa^[4] (dotp x x'))) * h31
  · linear_combination (norm := (unfold rQx q2 q3 SS DS; ring1))
      (rQx n m (1 - kappa^[4] (dotp x x')) (1 - kappa (kappa (dotp x x'))) (1 - dotp x x') *
        ((n : ℝ) * (2 / (m : ℝ))) * ((m : ℝ) / 2 * (2 / (n : ℝ)))) * hc2e +
      rQx n m (1 - kappa^[4] (dotp x x')) (1 - kappa (kappa (dotp x x'))) (1 - dotp x x') * h31

/-- **`agent_rem_L2x`: the remainder of the Agent link after the centred part, in `L²`**,
with `rR0x`. -/
theorem agent_rem_L2x (hn : 1 ≤ n) (hm : 1 ≤ m) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    L2le (mlpGauss n m n)
      (fun A : MlpParam n m n => phiD (kappa ∘ kappa) (mlpEval A x) (mlpEval A x') -
        2 * (1 - kappa^[4] (dotp x x')) - cAg A x x')
      (2 * (rR0x n m + rR1 n * (1 - kappa^[4] (dotp x x')) -
        rR1' n * (1 - kappa (kappa (dotp x x'))) + rR2 n m * (1 - dotp x x'))) := by
  have h := agent_rem_L2x_rQ hn hm hx hx'
  rwa [rQx_affine] at h

/-- **The term `δ` of the two outputs of the Agent network.** -/
theorem agent_dlt_L2x_of (hRS : ReluSqStmt) (hRD : ReluDltStmt) (hn : 1 ≤ n)
    (hm : 1 ≤ m) {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    L2le (mlpGauss n m n)
      (fun A : MlpParam n m n => dlt (mlpEval A x) (mlpEval A x')) (2 * cAdltx n m) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hKm := Kr_nonneg m
  have hK4 := kX_nonneg n
  have hv2 : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hc3 : (0 : ℝ) ≤ (n : ℝ) * (2 / (m : ℝ)) := by positivity
  have hc2 : (0 : ℝ) ≤ (m : ℝ) / 2 * (2 / (m : ℝ)) := by positivity
  have hk : (0 : ℝ) ≤ kX n / (n : ℝ) := by positivity
  have hr : (0 : ℝ) ≤ 1 / √(2 * (n : ℝ)) := by positivity
  have hq5 : (0 : ℝ) ≤ √(1 + 5 / (m : ℝ)) := Real.sqrt_nonneg _
  have he5 : (0 : ℝ) ≤ √5 / √(m : ℝ) := by positivity
  have hk4 : (0 : ℝ) ≤ 4 * Kr m / (m : ℝ) := by positivity
  have hc2e : (m : ℝ) / 2 * (2 / (m : ℝ)) = 1 := by field_simp
  have h31 : (n : ℝ) * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (n : ℝ))) = 2 := by field_simp
  have aS := l1S hn hm hx hx'
  have aD := l1D hn hm hx hx' hRS
  have aL := l1L hn hm hx hx' hRD
  have S1 := (aS.smul hq5).smul hc2
  have D1 := ((aS.smul he5).add aD).smul hc2
  have L1 := ((aL.add (aS.smul hk4)).add (aD.smul he5)).smul hc2
  have G1 := comboDlt L1 S1 D1 hc3 hk hr
  have mf : Measurable (fun A : MlpParam n m n => dlt (mlpEval A x) (mlpEval A x')) :=
    mPair m_dlt (measurable_mlpEval_param x) (measurable_mlpEval_param x')
  have T := prodNN (μ := gaussMat m n (2 / (n : ℝ)))
    (ν := (gaussMat m m (2 / (m : ℝ))).prod (gaussMat n m (2 / (m : ℝ)))) mf G1
    (fun M₁ => (prodNN (μ := gaussMat m m (2 / (m : ℝ))) (ν := gaussMat n m (2 / (m : ℝ)))
      (mf.comp measurable_prodMk_left)
      (comboDlt (genL hRD hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x')))
        (genS hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x')))
        (genD hRS hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x'))) hc3 hk hr)
      (fun M₂ => (linLx hv2 hn (reluV (M₂.mulVec (reluV (M₁.mulVec x))))
        (reluV (M₂.mulVec (reluV (M₁.mulVec x'))))).1)).1)
  unfold mlpGauss
  refine T.1.congr_bound ?_
  linear_combination (norm := (unfold cAdltx LS SS DS; ring1))
    (cAdltx n m * ((n : ℝ) * (2 / (m : ℝ))) * ((m : ℝ) / 2 * (2 / (n : ℝ)))) * hc2e +
    cAdltx n m * h31

end main

/-! ## The assembly -/

/-- `0 ≤ rR0x + rR1·(1 − κ^{∘6}(0)) − rR1'·(1 − κ^{∘4}(0)) + rR2·(1 − κ(κ(0)))`. -/
lemma rRx_ref_nonneg (n m : ℕ) :
    0 ≤ rR0x n m + rR1 n * (1 - kappa^[6] 0) - rR1' n * (1 - kappa^[4] 0) +
      rR2 n m * (1 - kappa (kappa 0)) := by
  have h0 := rR0x_nonneg n m
  have h2 := mul_nonneg (rR2_nonneg n m) a2_nonneg
  have h6 : 222757 / 1000000 ≤ 1 - kappa^[6] 0 := by have := kappa6_zero_le''; linarith
  have h4 : 1 - kappa^[4] 0 ≤ 319057 / 1000000 := one_sub_k4_le
  have h40 := one_sub_k4_nonneg
  have hc := AgS.cg2_le
  have hc0 := AgS.cgS_nonneg (kGood_kappa.comp_kappa)
  have hs : (0 : ℝ) ≤ 1 / √(n : ℝ) := by positivity
  have e : rR1 n * (1 - kappa^[6] 0) - rR1' n * (1 - kappa^[4] 0) =
      1 / √(n : ℝ) * ((1 - kappa^[6] 0) - AgS.cgS (kappa ∘ kappa) * (1 - kappa^[4] 0)) := by
    unfold rR1 rR1' sA1'; ring
  have h1 : 0 ≤ (1 - kappa^[6] 0) - AgS.cgS (kappa ∘ kappa) * (1 - kappa^[4] 0) := by
    have : AgS.cgS (kappa ∘ kappa) * (1 - kappa^[4] 0) ≤ 1 / 2 * (319057 / 1000000) :=
      mul_le_mul hc h4 h40 (by norm_num)
    linarith
  have := mul_nonneg hs h1
  linarith

/-- The kernel constant of `Part145K7` with `rR0x`, `cAdltx` in the place of `rR0`, `cAdlt`. -/
noncomputable def eDBq (bK τ pW : ℝ) (n : ℕ) : ℝ :=
  √(asmE1 (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) τ ^ 2 +
    asmE2 n (mA n) (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) (cAdltx n (mA n)) τ ^ 2 +
    (bK * ((1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ))) +
      asmE4 (rR0x n (mA n)) (rR1 n) (rR1' n) (rR2 n (mA n)) τ +
      √(asmE3x (cC0x n (mA n)) (cC1 n) (cC1x' n) (cC2x n (mA n)) τ ^ 2 + pW ^ 2)) ^ 2)

lemma eDBq_nonneg (bK τ pW : ℝ) (n : ℕ) : 0 ≤ eDBq bK τ pW n := Real.sqrt_nonneg _

/-- `asmE4` at the new constants is `≥ 0`. -/
lemma asmE4x_focus_nonneg (n m : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ asmE4 (rR0x n m) (rR1 n) (rR1' n) (rR2 n m) τ := by
  have h0 := rRx_ref_nonneg n m
  have := sig4_nonneg
  have := rR1_nonneg n
  have := rR1'_nonneg n
  have := rR2_nonneg n m
  have : 0 ≤ (rR1 n * sig4 + rR1' n + rR2 n m) * τ := by positivity
  unfold asmE4
  linarith

/-- **The kernel bound with three orthogonal blocks, a general World term and the sharper
second-order term**, `n ≥ 4096`. -/
theorem kernBq {n : ℕ} (hn : 4096 ≤ n) {bK : ℝ} (hbK : 0 ≤ bK)
    (hB : ∀ y y' : Fin n → ℝ,
      Integrable (fun F₁ : Matrix (Fin (mF n)) (Fin n) ℝ => rF0 F₁ y y')
        (gaussMat (mF n) n (2 / (n : ℝ))) ∧
      |∫ F₁, rF0 F₁ y y' ∂gaussMat (mF n) n (2 / (n : ℝ))| ≤
        2 / (n : ℝ) * (bK * ((normSq y + normSq y') / 2)))
    {τ pW : ℝ} (hτ : 0 ≤ τ)
    (hT : L2le ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (fun z : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n =>
        tX z - kappa (kappa 0)) τ)
    (hW5 : L2le ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (fun z : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n =>
        kappa^[4] (tX z) - kappa^[6] 0) pW) :
    L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      (4 / (n : ℝ) * eDBq bK τ pW n) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  unfold eDBq
  exact kernDistB_of (cA := cAg) hn1 hN hmA hmF measurable_cAg
    (cC1_nonneg n) (cC1x'_nonneg n) (cC2x_nonneg n (mA n)) (rR1_nonneg n) (rR1'_nonneg n)
    (rR2_nonneg n (mA n)) hτ hbK (cC_ref_nonneg n (mA n)) (rRx_ref_nonneg n (mA n))
    (fun x x' hx hx' => cAg_integral hn1 hmA hx hx')
    (fun x x' hx hx' => cAg_L2x hn1 hmA hx hx')
    (fun x x' hx hx' => agent_rem_L2x hn1 hmA hx hx')
    (dA0_nonneg n (mA n)) (dA1_nonneg n (mA n)) (dA2_nonneg n (mA n)) (cAdltx_nonneg n (mA n))
    (fun x x' hx hx' => agent_diff_L2_of reluEDStmt reluPhiStmt hn1 hmA hx hx')
    (fun x x' hx hx' => agent_dlt_L2x_of reluSqStmt reluDltStmt hn1 hmA hx hx')
    hB hT hW5

end BstLean.Part145

open BstLean.Part145 in
#print axioms agent_rem_L2x
open BstLean.Part145 in
#print axioms agent_dlt_L2x_of
open BstLean.Part145 in
#print axioms kernBq
