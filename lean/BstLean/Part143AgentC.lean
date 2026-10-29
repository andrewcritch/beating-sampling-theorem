import BstLean.Part143LinC
import BstLean.Part142AgentS

/-!
# Part 143: the link of the last matrix of the Agent network, split into a centred part and a
remainder

`A = (A₁, A₂, A₃)` has the distribution `mlpGauss n m n`; `x, x′` are unit vectors,
`t = ⟨x, x′⟩`, `G = κ∘κ`, `h₂ = ReLU(A₂ ReLU(A₁ x))`.

* `cAg A x x′ = cLin G n (2/m) A₃ h₂ h₂′` (file `Part143LinC`): the centred part.
* `measurable_cAg`: measurable in `(A, x, x′)`.
* **`cAg_integral`**: `cAg` is integrable in `A` and `∫ cAg dA = 0`; **`cAg_cond_integral`**:
  for every `(A₁, A₂)`, `∫ cAg dA₃ = 0`.
* **`cAg_L2`**: `‖cAg‖₂ ≤ 2·(cC0 + cC1·(1 − κ^{∘4}(t)) + cC2·(1 − t))`, `cC1 n = √2/√n`.
* **`agent_rem_L2`**: `‖Φ_G(A(x), A(x′)) − 2(1 − κ^{∘4}(t)) − cAg‖₂ ≤
    2·(rR0 + rR1·(1 − κ^{∘4}(t)) − rR1'·(1 − κ(κ(t))) + rR2·(1 − t))`, `rR1 n = 1/√n`,
  `rR1' n = sA1' n`.
* Numbers at `mA n = n²`, `n ≥ 16384`: `cC0 ≤ 0.0153/n`, `cC2 ≤ 0.115/n`, `rR0 ≤ 8.38/n`,
  `rR2 ≤ 10.51/n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part142

open AgD AgS

/-- **The centred part of the link of the last matrix of the Agent network.** -/
noncomputable def cAg {n m : ℕ} (A : MlpParam n m n) (x x' : Fin n → ℝ) : ℝ :=
  cLin (kappa ∘ kappa) n (2 / (m : ℝ)) A.2.2 (hid2 A.1 A.2.1 x) (hid2 A.1 A.2.1 x')

lemma measurable_cAg {n m : ℕ} :
    Measurable (fun p : MlpParam n m n × (Fin n → ℝ) × (Fin n → ℝ) => cAg p.1 p.2.1 p.2.2) := by
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have c1 : Continuous (fun p : MlpParam n m n × (Fin n → ℝ) × (Fin n → ℝ) => p.1.1) :=
    continuous_fst.comp continuous_fst
  have c2 : Continuous (fun p : MlpParam n m n × (Fin n → ℝ) × (Fin n → ℝ) => p.1.2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_fst)
  have m3 : Measurable (fun p : MlpParam n m n × (Fin n → ℝ) × (Fin n → ℝ) => p.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have cx : Continuous (fun p : MlpParam n m n × (Fin n → ℝ) × (Fin n → ℝ) => p.2.1) :=
    continuous_fst.comp continuous_snd
  have cx' : Continuous (fun p : MlpParam n m n × (Fin n → ℝ) × (Fin n → ℝ) => p.2.2) :=
    continuous_snd.comp continuous_snd
  have mh : Measurable (fun p : MlpParam n m n × (Fin n → ℝ) × (Fin n → ℝ) =>
      hid2 p.1.1 p.1.2.1 p.2.1) := by
    unfold hid2
    exact (continuous_reluV.comp (Continuous.matrix_mulVec c2
      (continuous_reluV.comp (Continuous.matrix_mulVec c1 cx)))).measurable
  have mh' : Measurable (fun p : MlpParam n m n × (Fin n → ℝ) × (Fin n → ℝ) =>
      hid2 p.1.1 p.1.2.1 p.2.2) := by
    unfold hid2
    exact (continuous_reluV.comp (Continuous.matrix_mulVec c2
      (continuous_reluV.comp (Continuous.matrix_mulVec c1 cx')))).measurable
  have h := (measurable_cLin (m := n) (k := m) hG.cont (2 / (m : ℝ))).comp
    (m3.prodMk (mh.prodMk mh'))
  exact h

lemma measurable_cAg_param {n m : ℕ} (x x' : Fin n → ℝ) :
    Measurable (fun A : MlpParam n m n => cAg A x x') := by
  have h1 : Measurable (fun A : MlpParam n m n => (A, x, x')) :=
    measurable_id.prodMk measurable_const
  have h := (measurable_cAg (n := n) (m := m)).comp h1
  exact h

namespace AgC

section defs

variable {ι : Type*} [Fintype ι]

/-- The first-order factor of the bound of `linRem_L2`. -/
noncomputable def fR (G : ℝ → ℝ) (y y' : ι → ℝ) : ℝ :=
  (phiD G y y' - dlt y y') - (1 - G (-1)) / 2 * (eD y y' - dlt y y')

/-- The conditional reference of `fR` after one ReLU layer (without the scale). -/
noncomputable def rhoR (G : ℝ → ℝ) (p p' : ι → ℝ) : ℝ :=
  phiD (G ∘ kappa) p p' - cgS G * phiD kappa p p'

/-- The `L²` bound of `fR` after one ReLU layer. -/
noncomputable def bFR (G : ℝ → ℝ) (m : ℕ) (v : ℝ) (p p' : ι → ℝ) : ℝ :=
  (m : ℝ) / 2 * v * (|rhoR G p p'| + bPhi G m p p' +
    cgS G * (√3 / √(m : ℝ) * normSq (p - p')) + (1 + cgS G) * bL m p p')

lemma fR_nonneg {G : ℝ → ℝ} (hG : KGood G) (y y' : ι → ℝ) (hd : 0 ≤ dotp y y') :
    0 ≤ fR G y y' := by
  have hnn := nrm_mul_nonneg y y'
  set τ := cosv y y' with hτ
  have hτ1 : τ ≤ 1 := (cosv_mem y y').2
  have hτ0 : 0 ≤ τ := by rw [hτ]; unfold cosv; exact div_nonneg hd hnn
  have hX := secX_nonneg hG hτ0 hτ1
  have edot : dotp y y' = τ * (nrm y * nrm y') := dotp_eq_cosv_mul y y'
  have e : fR G y y' = nrm y * nrm y' * ((1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) := by
    unfold fR phiD psi eD dlt
    rw [edot]
    ring
  rw [e]
  positivity

end defs

section tools

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma comboC {f : Ω → ℝ} {a : ℝ} (h : L2nn μ f a) {c q : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q) :
    L2nn μ (fun ω => c * (√2 * f ω / q)) (c * (√2 * a / q)) :=
  (h.smul (c := c * (√2 * (1 / q))) (by positivity)).congr (fun ω => by ring) (by ring)

end tools

section gen

variable {m k : ℕ} {v : ℝ}

/-- `linRem_L2` in the shape of `comboS`. -/
lemma linSecR {G : ℝ → ℝ} (hG : KGood G) (hv : 0 < v) (hm : 1 ≤ m) (y y' : Fin k → ℝ)
    (hd : 0 ≤ dotp y y') :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        phiD G (M.mulVec y) (M.mulVec y') - (m : ℝ) * v * phiD G y y' - cLin G m v M y y')
      ((m : ℝ) * v * (fR G y y' / √(m : ℝ) + K4 m / (m : ℝ) * (normSq y + normSq y') +
        |normSq y - normSq y'| / √(2 * (m : ℝ)))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hK := K4_nonneg m
  have hf := fR_nonneg hG y y' hd
  have hnn := nrm_mul_nonneg y y'
  have hle := nrm_mul_le y y'
  have h0 := linRem_L2 hG hv hm y y' hd
  have e : (phiD G y y' - dlt y y') - (1 - G (-1)) / 2 * (eD y y' - dlt y y') =
      fR G y y' := rfl
  rw [e] at h0
  refine h0.mono (by positivity) ?_
  have h1 : 2 * K4 m / (m : ℝ) * (nrm y * nrm y') ≤
      K4 m / (m : ℝ) * (normSq y + normSq y') := by
    have : 2 * K4 m / (m : ℝ) * (nrm y * nrm y') = K4 m / (m : ℝ) * (2 * (nrm y * nrm y')) := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hs : 0 ≤ (m : ℝ) * v := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hs

/-- **`fR` after one ReLU layer, in `L²`.** -/
lemma genFR {G : ℝ → ℝ} (hG : KGood G) (hv : 0 < v) (hm : 1 ≤ m) (p p' : Fin k → ℝ) :
    L2nn (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => fR G (reluV (M.mulVec p)) (reluV (M.mulVec p')))
      (bFR G m v p p') := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 ≤ (m : ℝ) / 2 * v := by positivity
  have hcg := cgS_nonneg hG
  have hbb := bG_nonneg hG
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  have hK := Kr_nonneg m
  have hN := normSq_nonneg p
  have hN' := normSq_nonneg p'
  have hE := normSq_nonneg (p - p')
  have hd := dlt_nonneg p p'
  have P0 := L2le.const (μ := gaussMat m k v) ((m : ℝ) / 2 * v * rhoR G p p')
  have P1 := reluPhiStmt hG hv hm p p'
  have P2 := ((reluEDStmt hv hm p p').const_mul_nonneg hcg).neg
  have gl := genL reluDltStmt hv hm p p'
  have P3 := gl.1.neg
  have P4 := gl.1.const_mul_nonneg hcg
  have s1 := P0.add0 P1 (abs_nonneg _) (by positivity)
  have s2 := s1.add0 P2 (by positivity) (by positivity)
  have s3 := s2.add0 P3 (by positivity) (by positivity)
  have s4 := s3.add0 P4 (by positivity) (by positivity)
  refine ⟨(s4.congr_fun fun M => ?_).congr_bound ?_, ?_⟩
  · unfold fR rhoR cgS
    ring
  · rw [abs_mul, abs_of_nonneg hs]
    have e := sconv (m := (m : ℝ)) (√3 / 2) (v * normSq (p - p'))
    unfold bFR bPhi bL
    linear_combination cgS G * e
  · unfold bFR bPhi bL
    positivity

/-- **`Φ_G − δ` after one ReLU layer, in `L²`.** -/
lemma genPD {G : ℝ → ℝ} (hG : KGood G) (hv : 0 < v) (hm : 1 ≤ m) (p p' : Fin k → ℝ) :
    L2nn (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        phiD G (reluV (M.mulVec p)) (reluV (M.mulVec p')) -
          dlt (reluV (M.mulVec p)) (reluV (M.mulVec p')))
      ((m : ℝ) / 2 * v * (phiD (G ∘ kappa) p p' + bPhi G m p p')) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hbb := bG_nonneg hG
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  have hK := Kr_nonneg m
  have hN := normSq_nonneg p
  have hN' := normSq_nonneg p'
  have hE := normSq_nonneg (p - p')
  have hd := dlt_nonneg p p'
  have hP := phiD_nn hG.comp_kappa p p'
  have hΦ := addConst (reluPhiStmt hG hv hm p p') (by positivity) (by positivity)
  have hmeas : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      phiD G (reluV (M.mulVec p)) (reluV (M.mulVec p')) -
        dlt (reluV (M.mulVec p)) (reluV (M.mulVec p'))) :=
    (mPair (m_phiD hG.cont) (mR p) (mR p')).sub (mPair m_dlt (mR p) (mR p'))
  refine ⟨(L2le.of_abs_le hmeas.aestronglyMeasurable hΦ.1 (fun M => ?_)).congr_bound ?_, ?_⟩
  · have h1 := phiD_sub_dlt_nonneg hG (reluV (M.mulVec p)) (reluV (M.mulVec p'))
    have h2 := dlt_nonneg (reluV (M.mulVec p)) (reluV (M.mulVec p'))
    rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]
    linarith
  · unfold bPhi
    ring
  · unfold bPhi
    positivity

end gen

/-! ## The constants -/

/-- The bound of `cAg_L2` (without the factor `2`), as a function of `a₄ = 1 − κ^{∘4}(t)`,
`u = 1 − t`. -/
noncomputable def cQ (n m : ℕ) (a4 u : ℝ) : ℝ := √2 * (a4 + q3 m u + q2 m u) / √(n : ℝ)

/-- The bound of `agent_rem_L2` (without the factor `2`), as a function of
`a₄ = 1 − κ^{∘4}(t)`, `a₂ = 1 − κ(κ(t))`, `u = 1 − t`. -/
noncomputable def rQ (n m : ℕ) (a4 a2 u : ℝ) : ℝ :=
  (a4 - cgS (kappa ∘ kappa) * a2 + q3 m u + cgS (kappa ∘ kappa) * bkS m u + q2 m u +
      cgS (kappa ∘ kappa) * (√3 / √(m : ℝ) * eS m u) +
      (1 + cgS (kappa ∘ kappa)) * LS m) / √(n : ℝ) +
    K4 n / (n : ℝ) * SS m + DS m / √(2 * (n : ℝ)) + q2 m u + q3 m u

/-! ## The first hidden layer at unit inputs -/

section layer1

variable {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {x x' : Fin n → ℝ} (hx : normSq x = 1)
  (hx' : normSq x' = 1)

include hx hx' in
lemma a4_nn : 0 ≤ 1 - kappa^[4] (dotp x x') := by
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have ht := dotp_unit_mem hx hx'
  have hk := kk_memIcc ht
  have e4 : (kappa ∘ kappa) (kappa (kappa (dotp x x'))) = kappa^[4] (dotp x x') := rfl
  have := hG.le_one hk
  rw [e4] at this
  linarith

include hx hx' in
lemma rho0R_nn : 0 ≤ (1 - kappa^[4] (dotp x x')) -
    cgS (kappa ∘ kappa) * (1 - kappa (kappa (dotp x x'))) := by
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have ht := dotp_unit_mem hx hx'
  have hk := kk_memIcc ht
  have hk0 : 0 ≤ kappa (kappa (dotp x x')) :=
    (kappa_mem (kappa_mem_Icc ht).1 (kappa_mem_Icc ht).2).1
  have hX := secX_nonneg hG hk0 hk.2
  have e4 : (kappa ∘ kappa) (kappa (kappa (dotp x x'))) = kappa^[4] (dotp x x') := rfl
  rw [e4] at hX
  unfold cgS
  linarith

include hn hm hx hx' in
/-- `Φ_{κ∘κ∘κ}` after the first hidden layer. -/
lemma l1P3 :
    L2nn (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ =>
        phiD ((kappa ∘ kappa) ∘ kappa) (reluV (M.mulVec x)) (reluV (M.mulVec x')))
      ((m : ℝ) / 2 * (2 / (n : ℝ)) * ((1 - kappa^[4] (dotp x x')) +
        q3 m (1 - dotp x x'))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  obtain ⟨hτ, hu⟩ := tau_nonneg hx hx'
  have hb3 := bG_nonneg hGk
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have hKr := Kr_nonneg m
  have hv1 : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have h4 := a4_nn hx hx'
  have h3 := reluPhiStmt hGk hv1 hm x x'
  have hph : phiD (((kappa ∘ kappa) ∘ kappa) ∘ kappa) x x' = 1 - kappa^[4] (dotp x x') := by
    rw [phiD_unit _ hx hx']; rfl
  rw [hph, normSq_sub_unit hx hx', hx, hx', dlt_unit hx hx', sub_self, abs_zero] at h3
  refine (addConst h3 (by positivity) (by positivity)).congr (fun _ => rfl) ?_
  unfold q3
  ring

include hn hm hx hx' in
lemma l1RR :
    L2nn (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ =>
        |rhoR (kappa ∘ kappa) (reluV (M.mulVec x)) (reluV (M.mulVec x'))|)
      ((m : ℝ) / 2 * (2 / (n : ℝ)) * ((1 - kappa^[4] (dotp x x')) -
        cgS (kappa ∘ kappa) * (1 - kappa (kappa (dotp x x'))) +
        q3 m (1 - dotp x x') + cgS (kappa ∘ kappa) * bkS m (1 - dotp x x'))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  obtain ⟨hτ, hu⟩ := tau_nonneg hx hx'
  have hcg := cgS_nonneg hG
  have hb3 := bG_nonneg hGk
  have hbk := bG_nonneg kGood_kappa
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have hk0 : 0 ≤ kappa 0 := kGood_kappa.nonneg_on KGood.zero_mem
  have hKr := Kr_nonneg m
  have hv1 : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hρ := rho0R_nn hx hx'
  have h3 := reluPhiStmt hGk hv1 hm x x'
  have hph : phiD (((kappa ∘ kappa) ∘ kappa) ∘ kappa) x x' = 1 - kappa^[4] (dotp x x') := by
    rw [phiD_unit _ hx hx']; rfl
  rw [hph, normSq_sub_unit hx hx', hx, hx', dlt_unit hx hx', sub_self, abs_zero] at h3
  have hk := reluPhiStmt kGood_kappa hv1 hm x x'
  have hph2 : phiD (kappa ∘ kappa) x x' = 1 - kappa (kappa (dotp x x')) := by
    rw [phiD_unit _ hx hx']; rfl
  rw [hph2, normSq_sub_unit hx hx', hx, hx', dlt_unit hx hx', sub_self, abs_zero] at hk
  have comb := h3.add0 ((hk.const_mul_nonneg hcg).neg) (by positivity) (by positivity)
  have comb' : L2le (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ =>
        rhoR (kappa ∘ kappa) (reluV (M.mulVec x)) (reluV (M.mulVec x')) -
          (m : ℝ) / 2 * (2 / (n : ℝ)) * ((1 - kappa^[4] (dotp x x')) -
            cgS (kappa ∘ kappa) * (1 - kappa (kappa (dotp x x'))))) _ :=
    comb.congr_fun fun M => by unfold rhoR; ring
  have r := addConst comb' (by positivity) (by positivity)
  refine ⟨(L2le.abs' r.1).congr_bound ?_, by unfold q3 bkS; positivity⟩
  unfold q3 bkS
  ring

include hn hm hx hx' in
/-- `bPhi` after the first hidden layer. -/
lemma l1Phi :
    L2nn (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ =>
        bPhi (kappa ∘ kappa) m (reluV (M.mulVec x)) (reluV (M.mulVec x')))
      ((m : ℝ) / 2 * (2 / (n : ℝ)) * q2 m (1 - dotp x x')) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hb2 := bG_nonneg hG
  have hg2 : 0 ≤ (kappa ∘ kappa) 0 := hG.nonneg_on KGood.zero_mem
  have hKm := Kr_nonneg m
  have he3 : (0 : ℝ) ≤ √3 / √(m : ℝ) := by positivity
  have he5 : (0 : ℝ) ≤ √5 / √(m : ℝ) := by positivity
  have hbc : (0 : ℝ) ≤ bG (kappa ∘ kappa) * (√5 / (2 * √(m : ℝ))) := by positivity
  have hk4 : (0 : ℝ) ≤ 4 * Kr m / (m : ℝ) := by positivity
  have aE := l1E hn hm hx hx'
  have aS := l1S hn hm hx hx'
  have aD := l1D hn hm hx hx' reluSqStmt
  have aL := l1L hn hm hx hx' reluDltStmt
  exact (((aE.smul he3).add (aS.smul hbc)).add
    ((((aS.smul hk4).add (aD.smul he5)).add (aL.smul (c := 2) (by norm_num))).smul hg2)).congr
    (fun M => by unfold bPhi; ring) (by unfold q2; ring)

end layer1

end AgC

open AgC

/-! ## The constants of the statements -/

/-- The constant term of `cAg_L2`. -/
noncomputable def cC0 (n mA : ℕ) : ℝ := cQ n mA 0 0
/-- The coefficient of `1 − κ^{∘4}(t)` in `cAg_L2`. -/
noncomputable def cC1 (n : ℕ) : ℝ := √2 / √(n : ℝ)
/-- The coefficient of `1 − t` in `cAg_L2`. -/
noncomputable def cC2 (n mA : ℕ) : ℝ := cQ n mA 0 1 - cQ n mA 0 0

/-- The constant term of `agent_rem_L2`. -/
noncomputable def rR0 (n mA : ℕ) : ℝ := rQ n mA 0 0 0
/-- The coefficient of `1 − κ^{∘4}(t)` in `agent_rem_L2`. -/
noncomputable def rR1 (n : ℕ) : ℝ := 1 / √(n : ℝ)
/-- The coefficient (with a MINUS sign) of `1 − κ(κ(t))` in `agent_rem_L2`. -/
noncomputable def rR1' (n : ℕ) : ℝ := sA1' n
/-- The coefficient of `1 − t` in `agent_rem_L2`. -/
noncomputable def rR2 (n mA : ℕ) : ℝ := rQ n mA 0 0 1 - rQ n mA 0 0 0

lemma cQ_affine (n m : ℕ) (a4 u : ℝ) : cQ n m a4 u = cC0 n m + cC1 n * a4 + cC2 n m * u := by
  unfold cC0 cC1 cC2 cQ q2 q3 eS
  ring

lemma rQ_affine (n m : ℕ) (a4 a2 u : ℝ) :
    rQ n m a4 a2 u = rR0 n m + rR1 n * a4 - rR1' n * a2 + rR2 n m * u := by
  unfold rR0 rR1 rR1' rR2 sA1' rQ q2 q3 bkS eS
  ring

lemma cC0_eq (n m : ℕ) : cC0 n m = √2 * (q3 m 0 + q2 m 0) / √(n : ℝ) := by
  unfold cC0 cQ
  ring

lemma cC2_eq (n m : ℕ) : cC2 n m =
    √2 * (2 * √3 / √(m : ℝ) + √3 / √(m : ℝ) * (4 * √(1 + 2 / (m : ℝ)))) / √(n : ℝ) := by
  unfold cC2 cQ q2 q3 eS
  ring

lemma rR0_eq (n m : ℕ) : rR0 n m =
    (q3 m 0 + cgS (kappa ∘ kappa) * nc0 m + q2 m 0 +
      (1 + cgS (kappa ∘ kappa)) * LS m) / √(n : ℝ) +
    K4 n / (n : ℝ) * SS m + DS m / √(2 * (n : ℝ)) + q2 m 0 + q3 m 0 := by
  unfold rR0 rQ bkS eS nc0
  ring

lemma rR2_eq (n m : ℕ) : rR2 n m =
    (1 + cgS (kappa ∘ kappa)) * (2 * √3 / √(m : ℝ) +
      √3 / √(m : ℝ) * (4 * √(1 + 2 / (m : ℝ)))) / √(n : ℝ) +
    √3 / √(m : ℝ) * (4 * √(1 + 2 / (m : ℝ))) + 2 * √3 / √(m : ℝ) := by
  unfold rR2 rQ q2 q3 bkS eS
  ring

/-- `cC1 + rR1 = sA1`: the two coefficients of `1 − κ^{∘4}(t)` add to that of Part 142. -/
lemma cC1_add_rR1 (n : ℕ) : cC1 n + rR1 n = sA1 n := by
  unfold cC1 rR1 sA1
  ring

/-! ## The statements -/

section main

variable {n m : ℕ}

/-- For every `(A₁, A₂)`, the centred part has mean zero over the last matrix `A₃`. -/
theorem cAg_cond_integral (M₁ : Matrix (Fin m) (Fin n) ℝ) (M₂ : Matrix (Fin m) (Fin m) ℝ)
    (x x' : Fin n → ℝ) :
    Integrable (fun M₃ : Matrix (Fin n) (Fin m) ℝ => cAg (M₁, M₂, M₃) x x')
        (gaussMat n m (2 / (m : ℝ))) ∧
      ∫ M₃, cAg (M₁, M₂, M₃) x x' ∂gaussMat n m (2 / (m : ℝ)) = 0 :=
  cLin_integral (m := n) (k := m) (kappa ∘ kappa) (v := 2 / (m : ℝ)) (by positivity)
    (hid2 M₁ M₂ x) (hid2 M₁ M₂ x')

/-- **The centred part, in `L²`**, in terms of `cQ`. -/
theorem cAg_L2_cQ (hn : 1 ≤ n) (hm : 1 ≤ m) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    L2le (mlpGauss n m n) (fun A : MlpParam n m n => cAg A x x')
      (2 * cQ n m (1 - kappa^[4] (dotp x x')) (1 - dotp x x')) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hv2 : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hc3 : (0 : ℝ) ≤ (n : ℝ) * (2 / (m : ℝ)) := by positivity
  have hc2 : (0 : ℝ) ≤ (m : ℝ) / 2 * (2 / (m : ℝ)) := by positivity
  have hq : (0 : ℝ) ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hq0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hn'
  have F1 := ((l1P3 hn hm hx hx').add (l1Phi hn hm hx hx')).smul hc2
  have mf := measurable_cAg_param (m := m) x x'
  have T := prodNN (μ := gaussMat m n (2 / (n : ℝ)))
    (ν := (gaussMat m m (2 / (m : ℝ))).prod (gaussMat n m (2 / (m : ℝ)))) mf
    (comboC F1 hc3 hq)
    (fun M₁ => (prodNN (μ := gaussMat m m (2 / (m : ℝ))) (ν := gaussMat n m (2 / (m : ℝ)))
      (mf.comp measurable_prodMk_left)
      (comboC (genPD hG hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x'))) hc3 hq)
      (fun M₂ => cLin_L2 hG hv2 hn (reluV (M₂.mulVec (reluV (M₁.mulVec x))))
        (reluV (M₂.mulVec (reluV (M₁.mulVec x')))) (dotp_relu_nonneg _ _))).1)
  unfold mlpGauss
  refine T.1.congr_bound ?_
  unfold cQ
  field_simp

/-- **`cAg_L2`: the centred part, in `L²`.** -/
theorem cAg_L2 (hn : 1 ≤ n) (hm : 1 ≤ m) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    L2le (mlpGauss n m n) (fun A : MlpParam n m n => cAg A x x')
      (2 * (cC0 n m + cC1 n * (1 - kappa^[4] (dotp x x')) + cC2 n m * (1 - dotp x x'))) := by
  have h := cAg_L2_cQ hn hm hx hx'
  rwa [cQ_affine] at h

/-- **`cAg_integral`: the centred part has mean zero.** -/
theorem cAg_integral (hn : 1 ≤ n) (hm : 1 ≤ m) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    Integrable (fun A : MlpParam n m n => cAg A x x') (mlpGauss n m n) ∧
      ∫ A, cAg A x x' ∂mlpGauss n m n = 0 := by
  have h2 := cAg_L2_cQ hn hm hx hx'
  have hI : Integrable (fun A : MlpParam n m n => cAg A x x') (mlpGauss n m n) :=
    ((memLp_two_iff_integrable_sq h2.aesm).2 h2.int_sq).integrable one_le_two
  refine ⟨hI, ?_⟩
  unfold mlpGauss at hI ⊢
  have key2 : ∀ (M₁ : Matrix (Fin m) (Fin n) ℝ),
      ∫ y, cAg (M₁, y) x x' ∂((gaussMat m m (2 / (m : ℝ))).prod
        (gaussMat n m (2 / (m : ℝ)))) = 0 := by
    intro M₁
    by_cases hi : Integrable (fun y : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin m) ℝ =>
        cAg (M₁, y) x x') ((gaussMat m m (2 / (m : ℝ))).prod (gaussMat n m (2 / (m : ℝ))))
    · rw [integral_prod _ hi]
      have key3 : ∀ M₂ : Matrix (Fin m) (Fin m) ℝ,
          ∫ M₃, cAg (M₁, M₂, M₃) x x' ∂gaussMat n m (2 / (m : ℝ)) = 0 :=
        fun M₂ => (cAg_cond_integral M₁ M₂ x x').2
      simp only [key3, integral_zero]
    · exact integral_undef hi
  rw [integral_prod _ hI]
  simp only [key2, integral_zero]

/-- **The remainder of the Agent link after the centred part, in `L²`**, in terms of `rQ`. -/
theorem agent_rem_L2_rQ (hn : 1 ≤ n) (hm : 1 ≤ m) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    L2le (mlpGauss n m n)
      (fun A : MlpParam n m n => phiD (kappa ∘ kappa) (mlpEval A x) (mlpEval A x') -
        2 * (1 - kappa^[4] (dotp x x')) - cAg A x x')
      (2 * rQ n m (1 - kappa^[4] (dotp x x')) (1 - kappa (kappa (dotp x x')))
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
  have hK4 := K4_nonneg n
  obtain ⟨hτ, hu⟩ := tau_nonneg hx hx'
  have hv1 : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hv2 : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hc3 : (0 : ℝ) ≤ (n : ℝ) * (2 / (m : ℝ)) := by positivity
  have hc2 : (0 : ℝ) ≤ (m : ℝ) / 2 * (2 / (m : ℝ)) := by positivity
  have hq : (0 : ℝ) ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hi : (0 : ℝ) ≤ √(2 * (n : ℝ)) := Real.sqrt_nonneg _
  have hk : (0 : ℝ) ≤ K4 n / (n : ℝ) := by positivity
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
      (fun M₂ => linSecR hG hv2 hn (reluV (M₂.mulVec (reluV (M₁.mulVec x))))
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
  · linear_combination (norm := (unfold rQ q2 q3 SS DS; ring1))
      (rQ n m (1 - kappa^[4] (dotp x x')) (1 - kappa (kappa (dotp x x'))) (1 - dotp x x') *
        ((n : ℝ) * (2 / (m : ℝ))) * ((m : ℝ) / 2 * (2 / (n : ℝ)))) * hc2e +
      rQ n m (1 - kappa^[4] (dotp x x')) (1 - kappa (kappa (dotp x x'))) (1 - dotp x x') * h31

/-- **`agent_rem_L2`: the remainder of the Agent link after the centred part, in `L²`.** -/
theorem agent_rem_L2 (hn : 1 ≤ n) (hm : 1 ≤ m) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    L2le (mlpGauss n m n)
      (fun A : MlpParam n m n => phiD (kappa ∘ kappa) (mlpEval A x) (mlpEval A x') -
        2 * (1 - kappa^[4] (dotp x x')) - cAg A x x')
      (2 * (rR0 n m + rR1 n * (1 - kappa^[4] (dotp x x')) -
        rR1' n * (1 - kappa (kappa (dotp x x'))) + rR2 n m * (1 - dotp x x'))) := by
  have h := agent_rem_L2_rQ hn hm hx hx'
  rwa [rQ_affine] at h

end main

/-! ## Nonnegativity -/

lemma q2z_nn (m : ℕ) : 0 ≤ q2 m 0 := by
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hb2 := bG_nonneg hG
  have hg2 : 0 ≤ (kappa ∘ kappa) 0 := hG.nonneg_on KGood.zero_mem
  have := sS_nn m; have := dS_nn m; have := lS_nn m
  have := Kr_nonneg m
  unfold q2 eS; positivity

lemma q3z_nn (m : ℕ) : 0 ≤ q3 m 0 := by
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := (kGood_kappa.comp_kappa).comp_kappa
  have hb3 := bG_nonneg hGk
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have := Kr_nonneg m
  unfold q3; positivity

lemma cC0_nonneg (n m : ℕ) : 0 ≤ cC0 n m := by
  have := q2z_nn m; have := q3z_nn m
  rw [cC0_eq]; positivity

lemma cC1_nonneg (n : ℕ) : 0 ≤ cC1 n := by unfold cC1; positivity

lemma cC2_nonneg (n m : ℕ) : 0 ≤ cC2 n m := by rw [cC2_eq]; positivity

lemma rR1_nonneg (n : ℕ) : 0 ≤ rR1 n := by unfold rR1; positivity

lemma rR1'_nonneg (n : ℕ) : 0 ≤ rR1' n := sA1'_nonneg n

lemma rR2_nonneg (n m : ℕ) : 0 ≤ rR2 n m := by
  have := cgS_nonneg (kGood_kappa.comp_kappa)
  rw [rR2_eq]
  positivity

lemma rR0_nonneg (n m : ℕ) : 0 ≤ rR0 n m := by
  have hcg := cgS_nonneg (kGood_kappa.comp_kappa)
  have := nc0_nn m; have := SS_nn m; have := DS_nn m; have := LS_nn m
  have := K4_nonneg n
  have h2 := q2z_nn m
  have h3 := q3z_nn m
  rw [rR0_eq]
  positivity

/-- The whole bound of `cAg_L2` is nonnegative. -/
lemma agentC_bound_nonneg (n m : ℕ) {x x' : Fin n → ℝ} (hx : normSq x = 1)
    (hx' : normSq x' = 1) :
    0 ≤ cC0 n m + cC1 n * (1 - kappa^[4] (dotp x x')) + cC2 n m * (1 - dotp x x') := by
  have h0 := cC0_nonneg n m
  have h1 := cC1_nonneg n
  have h2 := cC2_nonneg n m
  obtain ⟨-, hu⟩ := tau_nonneg hx hx'
  have h4 := a4_nn hx hx'
  positivity

/-- The whole bound of `agent_rem_L2` is nonnegative. -/
lemma agentRem_bound_nonneg (n m : ℕ) {x x' : Fin n → ℝ} (hx : normSq x = 1)
    (hx' : normSq x' = 1) :
    0 ≤ rR0 n m + rR1 n * (1 - kappa^[4] (dotp x x')) -
      rR1' n * (1 - kappa (kappa (dotp x x'))) + rR2 n m * (1 - dotp x x') := by
  have h0 := rR0_nonneg n m
  have h2 := rR2_nonneg n m
  obtain ⟨-, hu⟩ := tau_nonneg hx hx'
  have hρ := rho0R_nn hx hx'
  have e : rR1 n * (1 - kappa^[4] (dotp x x')) - rR1' n * (1 - kappa (kappa (dotp x x'))) =
      ((1 - kappa^[4] (dotp x x')) -
        cgS (kappa ∘ kappa) * (1 - kappa (kappa (dotp x x')))) / √(n : ℝ) := by
    unfold rR1 rR1' sA1'; ring
  have h1 : 0 ≤ rR1 n * (1 - kappa^[4] (dotp x x')) -
      rR1' n * (1 - kappa (kappa (dotp x x'))) := by
    rw [e]; positivity
  have h3 : 0 ≤ rR2 n m * (1 - dotp x x') := mul_nonneg h2 hu
  linarith

/-! ## The numbers at the width `mA n = n²`, `n ≥ 16384` -/

namespace AgC

lemma cg2_le' : cgS (kappa ∘ kappa) ≤ 34085 / 100000 := by
  have := kappa_zero_ge
  rw [cg2_eq]
  linarith

section focus

variable {n : ℕ} (hn : 16384 ≤ n)

include hn

lemma n4096 : 4096 ≤ n := le_trans (by norm_num) hn

/-- `y = 1/n`, `z = 1/√n`, `r = 1/√(2n)` at `n ≥ 16384`. -/
lemma yzr16 : ∃ y z r : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧ r = 1 / √(2 * (n : ℝ)) ∧
    0 < y ∧ 0 < z ∧ 0 < r ∧ y ≤ 1 / 16384 ∧ z ≤ 1 / 128 ∧ r ≤ 707107 / 1000000 * z := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr (n4096 hn)
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (128 : ℝ) ≤ √(n : ℝ) := (Real.le_sqrt' (by norm_num)).2 (by linarith)
  refine ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, ?_, ?_, hr1⟩
  · rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  · rw [hz]; exact one_div_le_one_div_of_le (by norm_num) hs

lemma K4_le16 : K4 n ≤ 34646 / 10000 := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  unfold K4
  refine sqrt_le_of_sq (by norm_num) ?_
  have h : 48 / (n : ℝ) ≤ 48 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have e : ((34646 : ℝ) / 10000) ^ 2 = 1200345316 / 100000000 := by norm_num
  rw [e]
  linarith

lemma Q2_le16 : √(1 + 2 / (mA n : ℝ)) ≤ 10000001 / 10000000 := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (16384 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  refine sqrt_le_of_sq (by norm_num) ?_
  rw [mA_eqR]
  have h : 2 / (n : ℝ) ^ 2 ≤ 2 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  have h2' : (268435456 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h' : 2 / (n : ℝ) ^ 2 ≤ 2 / 268435456 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2'
  have e : ((10000001 : ℝ) / 10000000) ^ 2 = 100000020000001 / 100000000000000 := by norm_num
  rw [e]
  linarith

lemma SS_le16 : SS (mA n) ≤ 20001 / 10000 := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have h2' : (268435456 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h' : 5 / (n : ℝ) ^ 2 ≤ 5 / 268435456 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2'
  have hpos : (0 : ℝ) ≤ 1 + 5 / (mA n : ℝ) := by positivity
  have e : SS (mA n) = 2 * (1 + 5 / (mA n : ℝ)) := by
    unfold SS sS
    calc √(1 + 5 / (mA n : ℝ)) * (2 * √(1 + 5 / (mA n : ℝ)))
        = 2 * (√(1 + 5 / (mA n : ℝ)) * √(1 + 5 / (mA n : ℝ))) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hpos]
  rw [e, mA_eqR]
  linarith

lemma q3z_le16 : q3 (mA n) 0 ≤ 637 / 1000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzr16 hn
  have hn4 := n4096 hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  have hb3 := bG_nonneg hGk
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have b3 := b3_le
  have g3 := g3_le
  have h5 := sqrt5_le'
  have hK := Kr_mA_le hn4
  have hK0 := Kr_nonneg (mA n)
  have hyy : y ^ 2 ≤ y * (1 / 16384) := by nlinarith
  unfold q3
  rw [sqrt_mA, mA_eqR, ← hy]
  refine le_trans (le_of_eq (?_ : _ = bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
    ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2))) ?_
  · rw [hy]; ring
  · calc bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
          ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2)
        ≤ 28416 / 100000 * (223607 / 100000 * (y / 2)) * 2 +
          1 * (4 * (11 / 5) * y ^ 2 * 2) := by gcongr
      _ ≤ 637 / 1000 * y := by nlinarith

lemma q2z_le16 : q2 (mA n) 0 ≤ 743 / 1000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzr16 hn
  have hn4 := n4096 hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hb2 := bG_nonneg hG
  have hg2 : 0 ≤ (kappa ∘ kappa) 0 := hG.nonneg_on KGood.zero_mem
  have b2 := b2_le
  have g2 := g2_le
  have h5 := sqrt5_le'
  have hK := Kr_mA_le hn4
  have hK0 := Kr_nonneg (mA n)
  have a5 := sS_le hn4
  have a6 := dS_le hn4
  have a7 := lS_le hn4
  have n5 := sS_nn (mA n)
  have n6 := dS_nn (mA n)
  have n7 := lS_nn (mA n)
  have hyy : y ^ 2 ≤ y * (1 / 16384) := by nlinarith
  unfold q2 eS
  rw [sqrt_mA, mA_eqR, ← hy]
  rw [← hy] at a6 a7
  refine le_trans (le_of_eq (?_ : _ = bG (kappa ∘ kappa) * (√5 * (y / 2)) * sS (mA n) +
    (kappa ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * sS (mA n) + √5 * y * dS (mA n) +
      2 * lS (mA n)))) ?_
  · rw [hy]; ring
  · calc bG (kappa ∘ kappa) * (√5 * (y / 2)) * sS (mA n) +
          (kappa ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * sS (mA n) + √5 * y * dS (mA n) +
            2 * lS (mA n))
        ≤ 33087 / 100000 * (223607 / 100000 * (y / 2)) * (2002 / 1000) +
          49376 / 100000 * (4 * (11 / 5) * y ^ 2 * (2002 / 1000) +
            223607 / 100000 * y * (447214 / 100000 * y) + 2 * (176 / 10 * y ^ 2)) := by gcongr
      _ ≤ 743 / 1000 * y := by nlinarith

end focus

end AgC

section focusBounds

variable {n : ℕ} (hn : 16384 ≤ n)

include hn

omit hn in
/-- `cC1 ≤ 1.41422/√n`. -/
theorem cC1_le : cC1 n ≤ 141422 / 100000 / √(n : ℝ) := by
  have h2 := sqrt2_le
  unfold cC1
  exact div_le_div_of_nonneg_right h2 (Real.sqrt_nonneg _)

/-- `cC0 ≤ 0.0153/n`. -/
theorem cC0_le : cC0 n (mA n) ≤ 153 / 10000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzr16 hn
  have h2 := sqrt2_le
  have a5 := q2z_le16 hn
  have a6 := q3z_le16 hn
  have n5 := q2z_nn (mA n)
  have n6 := q3z_nn (mA n)
  rw [← hy] at a5 a6
  have hzy : y * z ≤ y * (1 / 128) := mul_le_mul_of_nonneg_left hz1 hy0.le
  rw [cC0_eq]
  refine le_trans (le_of_eq (?_ : _ = √2 * (q3 (mA n) 0 + q2 (mA n) 0) * z)) ?_
  · rw [hz]; ring
  · refine le_trans (?_ : _ ≤ 153 / 10000 * y) (le_of_eq (by rw [hy]; ring))
    calc √2 * (q3 (mA n) 0 + q2 (mA n) 0) * z
        ≤ 141422 / 100000 * (637 / 1000 * y + 743 / 1000 * y) * z := by gcongr
      _ ≤ 153 / 10000 * y := by nlinarith

/-- `cC2 ≤ 0.115/n`. -/
theorem cC2_le : cC2 n (mA n) ≤ 115 / 1000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzr16 hn
  have h3 := sqrt3_le
  have h2 := sqrt2_le
  have hQ := Q2_le16 hn
  have hzy : y * z ≤ y * (1 / 128) := mul_le_mul_of_nonneg_left hz1 hy0.le
  rw [cC2_eq, sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = √2 * (2 * √3 * y +
    √3 * y * (4 * √(1 + 2 / (mA n : ℝ)))) * z)) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 115 / 1000 * y) (le_of_eq (by rw [hy]; ring))
    calc √2 * (2 * √3 * y + √3 * y * (4 * √(1 + 2 / (mA n : ℝ)))) * z
        ≤ 141422 / 100000 * (2 * (17321 / 10000) * y +
          17321 / 10000 * y * (4 * (10000001 / 10000000))) * z := by gcongr
      _ ≤ 115 / 1000 * y := by nlinarith

omit hn in
/-- `rR1 = 1/√n`. -/
theorem rR1_eq : rR1 n = 1 / √(n : ℝ) := rfl

/-- `rR1' ≥ 0.3408/√n` (the coefficient with the minus sign: a LOWER bound). -/
theorem rR1'_ge : 3408 / 10000 / √(n : ℝ) ≤ rR1' n := sA1'_ge (n4096 hn)

/-- `rR2 ≤ 10.51/n`. -/
theorem rR2_le : rR2 n (mA n) ≤ 1051 / 100 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzr16 hn
  have h3 := sqrt3_le
  have hQ := Q2_le16 hn
  have hcg := cgS_nonneg (kGood_kappa.comp_kappa)
  have hcl := cg2_le'
  have hzy : y * z ≤ y * (1 / 128) := mul_le_mul_of_nonneg_left hz1 hy0.le
  rw [rR2_eq, sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = (1 + cgS (kappa ∘ kappa)) * (2 * √3 * y +
    √3 * y * (4 * √(1 + 2 / (mA n : ℝ)))) * z + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))) +
    2 * √3 * y)) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 1051 / 100 * y) (le_of_eq (by rw [hy]; ring))
    calc (1 + cgS (kappa ∘ kappa)) * (2 * √3 * y +
          √3 * y * (4 * √(1 + 2 / (mA n : ℝ)))) * z + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))) +
          2 * √3 * y
        ≤ (1 + 34085 / 100000) * (2 * (17321 / 10000) * y +
          17321 / 10000 * y * (4 * (10000001 / 10000000))) * z +
          17321 / 10000 * y * (4 * (10000001 / 10000000)) + 2 * (17321 / 10000) * y := by
            gcongr
      _ ≤ 1051 / 100 * y := by nlinarith

/-- `rR0 ≤ 8.38/n`. -/
theorem rR0_le : rR0 n (mA n) ≤ 838 / 100 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzr16 hn
  have hn4 := n4096 hn
  have hcg := cgS_nonneg (kGood_kappa.comp_kappa)
  have hcl := cg2_le'
  have hK4 := K4_le16 hn
  have hK40 := K4_nonneg n
  have a1 := nc0_le hn4
  have a2 := SS_le16 hn
  have a3 := DS_le hn4
  have a4 := LS_le hn4
  have a5 := q2z_le16 hn
  have a6 := q3z_le16 hn
  have n1 := nc0_nn (mA n)
  have n2 := SS_nn (mA n)
  have n3 := DS_nn (mA n)
  have n4 := LS_nn (mA n)
  have n5 := q2z_nn (mA n)
  have n6 := q3z_nn (mA n)
  rw [← hy] at a1 a3 a4 a5 a6
  have hzy : y * z ≤ y * (1 / 128) := mul_le_mul_of_nonneg_left hz1 hy0.le
  have hr2 : r ≤ 707107 / 1000000 * (1 / 128) := by linarith
  have hyr : y * r ≤ y * (707107 / 1000000 * (1 / 128)) :=
    mul_le_mul_of_nonneg_left hr2 hy0.le
  rw [rR0_eq]
  refine le_trans (le_of_eq (?_ : _ =
    (q3 (mA n) 0 + cgS (kappa ∘ kappa) * nc0 (mA n) + q2 (mA n) 0 +
      (1 + cgS (kappa ∘ kappa)) * LS (mA n)) * z +
    K4 n * y * SS (mA n) + DS (mA n) * r + q2 (mA n) 0 + q3 (mA n) 0)) ?_
  · rw [hy, hz, hr]; ring
  · refine le_trans (?_ : _ ≤ 838 / 100 * y) (le_of_eq (by rw [hy]; ring))
    calc (q3 (mA n) 0 + cgS (kappa ∘ kappa) * nc0 (mA n) +
          q2 (mA n) 0 + (1 + cgS (kappa ∘ kappa)) * LS (mA n)) * z +
          K4 n * y * SS (mA n) + DS (mA n) * r + q2 (mA n) 0 + q3 (mA n) 0
        ≤ (637 / 1000 * y + 34085 / 100000 * (815 / 1000 * y) +
          743 / 1000 * y + (1 + 34085 / 100000) * (12 / 1000 * y)) * z +
          34646 / 10000 * y * (20001 / 10000) + 895 / 100 * y * r + 743 / 1000 * y +
          637 / 1000 * y := by gcongr
      _ ≤ 838 / 100 * y := by nlinarith

end focusBounds

end BstLean.Part143

open BstLean.Part143 in
#print axioms measurable_cAg
open BstLean.Part143 in
#print axioms cAg_cond_integral
open BstLean.Part143 in
#print axioms cAg_integral
open BstLean.Part143 in
#print axioms cAg_L2
open BstLean.Part143 in
#print axioms agent_rem_L2
open BstLean.Part143 in
#print axioms agentC_bound_nonneg
open BstLean.Part143 in
#print axioms agentRem_bound_nonneg
open BstLean.Part143 in
#print axioms cC0_le
open BstLean.Part143 in
#print axioms cC2_le
open BstLean.Part143 in
#print axioms rR0_le
open BstLean.Part143 in
#print axioms rR2_le
