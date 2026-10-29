import BstLean.Part142LinS
import BstLean.Part142ReluD
import BstLean.Part142AgentD

/-!
# Part 142: the distance form through the Agent network, with the secant link for the last matrix

Role: `delegations/statements/p142-spec.md`, item 2 (sharper kernel bounds). The same chain as
`agent_phi_L2_of` (file `Part142AgentD`), with `phi_lin_S` (file `Part142LinS`) for the last
matrix `A₃` in the place of `LinPhiStmt`, and with the proved one-layer links of
`Part142ReluD`.

`A = (A₁, A₂, A₃)` has the distribution `mlpGauss n mA n`; `x, x′` are unit vectors,
`t = ⟨x, x′⟩`, `G = κ∘κ`, `c_g = (1 − G(−1))/2 = (1 − κ(0))/2`.

* **`agent_phiS_L2`**: `‖Φ_G(A(x), A(x′)) − 2(1 − κ^{∘4}(t))‖₂ ≤
    2·(sA0 + sA1·(1 − κ^{∘4}(t)) − sA1'·(1 − κ(κ(t))) + sA2·(1 − t))`,
  `sA1 n = (1 + √2)/√n`, `sA1' n = c_g/√n`; `sA0`, `sA2` are of order `1/n` at `mA = n²`.
* Numbers at `mA n = n²`, `n ≥ 4096`: `sA0 ≤ 8.6/n`, `sA1 ≤ 2.4143/√n`, `sA1' ≥ 0.3408/√n`,
  `sA2 ≤ 10.9/n`.
The helper lemmas are in the namespace `BstLean.Part142.AgS`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133

open AgD

namespace AgS

/-- `c_g = (1 − G(−1))/2`. -/
noncomputable def cgS (G : ℝ → ℝ) : ℝ := (1 - G (-1)) / 2

lemma cgS_nonneg {G : ℝ → ℝ} (hG : KGood G) : 0 ≤ cgS G := by
  have := hG.le_one (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨le_refl _, by norm_num⟩)
  unfold cgS
  linarith

lemma cg2_eq : cgS (kappa ∘ kappa) = (1 - kappa 0) / 2 := by
  unfold cgS
  simp only [Function.comp_apply, kappa_neg_one]

section defs

variable {ι : Type*} [Fintype ι]

/-- The first-order factor of the bound of `phi_lin_S`. -/
noncomputable def fFun (G : ℝ → ℝ) (y y' : ι → ℝ) : ℝ :=
  (1 + √2) * (phiD G y y' - dlt y y') - (1 - G (-1)) / 2 * (eD y y' - dlt y y')

/-- The conditional reference of `fFun` after one ReLU layer (without the scale). -/
noncomputable def rhoS (G : ℝ → ℝ) (p p' : ι → ℝ) : ℝ :=
  (1 + √2) * phiD (G ∘ kappa) p p' - cgS G * phiD kappa p p'

/-- The bound of `ReluPhiStmt` without the scale. -/
noncomputable def bPhi (G : ℝ → ℝ) (m : ℕ) (p p' : ι → ℝ) : ℝ :=
  √3 / √(m : ℝ) * normSq (p - p') + bG G * (√5 / (2 * √(m : ℝ))) * (normSq p + normSq p') +
    G 0 * (4 * Kr m / (m : ℝ) * (normSq p + normSq p') +
      √5 / √(m : ℝ) * |normSq p - normSq p'| + 2 * dlt p p')

/-- The bound of `δ` after one ReLU layer, without the scale. -/
noncomputable def bL (m : ℕ) (p p' : ι → ℝ) : ℝ :=
  dlt p p' + 4 * Kr m / (m : ℝ) * (normSq p + normSq p') +
    √5 / √(m : ℝ) * |normSq p - normSq p'|

/-- The `L²` bound of `fFun` after one ReLU layer. -/
noncomputable def bF (G : ℝ → ℝ) (m : ℕ) (v : ℝ) (p p' : ι → ℝ) : ℝ :=
  (m : ℝ) / 2 * v * (|rhoS G p p'| + (1 + √2) * bPhi G m p p' +
    cgS G * (√3 / √(m : ℝ) * normSq (p - p')) + (1 + √2 + cgS G) * bL m p p')

lemma fFun_nonneg {G : ℝ → ℝ} (hG : KGood G) (y y' : ι → ℝ) (hd : 0 ≤ dotp y y') :
    0 ≤ fFun G y y' := by
  have hnn := nrm_mul_nonneg y y'
  set τ := cosv y y' with hτ
  have hτ1 : τ ≤ 1 := (cosv_mem y y').2
  have hτ0 : 0 ≤ τ := by rw [hτ]; unfold cosv; exact div_nonneg hd hnn
  have hX := secX_nonneg hG hτ0 hτ1
  have hγ : 0 ≤ 1 - G τ := by
    have := hG.le_one (show τ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, hτ1⟩)
    linarith
  have edot : dotp y y' = τ * (nrm y * nrm y') := dotp_eq_cosv_mul y y'
  have e : fFun G y y' = nrm y * nrm y' *
      (√2 * (1 - G τ) + ((1 - G τ) - (1 - G (-1)) / 2 * (1 - τ))) := by
    unfold fFun phiD psi eD dlt
    rw [edot]
    ring
  rw [e]
  positivity

end defs

section tools

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The shape of the bound of `phi_lin_S` (after `|y||y′| ≤ (|y|² + |y′|²)/2`). -/
lemma comboS {fF fS fD : Ω → ℝ} {aF aS aD : ℝ} (hF : L2nn μ fF aF) (hS : L2nn μ fS aS)
    (hD : L2nn μ fD aD) {c q k i : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q) (hk : 0 ≤ k) (hi : 0 ≤ i) :
    L2nn μ (fun ω => c * (fF ω / q + k * fS ω + fD ω / i)) (c * (aF / q + k * aS + aD / i)) :=
  (((hF.smul (c := c * (1 / q)) (by positivity)).add
    (hS.smul (c := c * k) (by positivity))).add
    (hD.smul (c := c * (1 / i)) (by positivity))).congr (fun ω => by ring) (by ring)

end tools

section gen

variable {m k : ℕ} {v : ℝ}

/-- `phi_lin_S` in the shape of `comboS`. -/
lemma linSec {G : ℝ → ℝ} (hG : KGood G) (hv : 0 < v) (hm : 1 ≤ m) (y y' : Fin k → ℝ)
    (hd : 0 ≤ dotp y y') :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        phiD G (M.mulVec y) (M.mulVec y') - (m : ℝ) * v * phiD G y y')
      ((m : ℝ) * v * (fFun G y y' / √(m : ℝ) + K4 m / (m : ℝ) * (normSq y + normSq y') +
        |normSq y - normSq y'| / √(2 * (m : ℝ)))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hK := K4_nonneg m
  have hf := fFun_nonneg hG y y' hd
  have hnn := nrm_mul_nonneg y y'
  have hle := nrm_mul_le y y'
  have h0 := phi_lin_S hG hv hm y y' hd
  have e : (1 + √2) * (phiD G y y' - dlt y y') - (1 - G (-1)) / 2 * (eD y y' - dlt y y') =
      fFun G y y' := rfl
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

/-- **`fFun` after one ReLU layer, in `L²`.** -/
lemma genF {G : ℝ → ℝ} (hG : KGood G) (hv : 0 < v) (hm : 1 ≤ m) (p p' : Fin k → ℝ) :
    L2nn (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => fFun G (reluV (M.mulVec p)) (reluV (M.mulVec p')))
      (bF G m v p p') := by
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
  have h12 : (0 : ℝ) ≤ 1 + √2 := by positivity
  have P0 := L2le.const (μ := gaussMat m k v) ((m : ℝ) / 2 * v * rhoS G p p')
  have P1 := (reluPhiStmt hG hv hm p p').const_mul_nonneg h12
  have P2 := ((reluEDStmt hv hm p p').const_mul_nonneg hcg).neg
  have gl := genL reluDltStmt hv hm p p'
  have P3 := (gl.1.const_mul_nonneg h12).neg
  have P4 := gl.1.const_mul_nonneg hcg
  have s1 := P0.add0 P1 (abs_nonneg _) (by positivity)
  have s2 := s1.add0 P2 (by positivity) (by positivity)
  have s3 := s2.add0 P3 (by positivity) (by positivity)
  have s4 := s3.add0 P4 (by positivity) (by positivity)
  refine ⟨(s4.congr_fun fun M => ?_).congr_bound ?_, ?_⟩
  · unfold fFun rhoS cgS
    ring
  · rw [abs_mul, abs_of_nonneg hs]
    have e := sconv (m := (m : ℝ)) (√3 / 2) (v * normSq (p - p'))
    unfold bF bPhi bL
    linear_combination cgS G * e
  · unfold bF bPhi bL
    positivity

end gen

/-! ## The constants -/

/-- The constant of `Φ_κ(h₁, h₁′)` at unit inputs, as a function of `u = 1 − t`. -/
noncomputable def bkS (m : ℕ) (u : ℝ) : ℝ :=
  √3 / √(m : ℝ) * (2 * u) + bG kappa * (√5 / (2 * √(m : ℝ))) * (1 + 1) +
    kappa 0 * (4 * Kr m / (m : ℝ) * (1 + 1) + √5 / √(m : ℝ) * 0 + 2 * 0)

/-- The bound of `agent_phiS_L2` (without the factor `2`), as a function of
`a₄ = 1 − κ^{∘4}(t)`, `a₂ = 1 − κ(κ(t))`, `u = 1 − t`. -/
noncomputable def sQ (n m : ℕ) (a4 a2 u : ℝ) : ℝ :=
  ((1 + √2) * a4 - cgS (kappa ∘ kappa) * a2 + (1 + √2) * q3 m u +
      cgS (kappa ∘ kappa) * bkS m u + (1 + √2) * q2 m u +
      cgS (kappa ∘ kappa) * (√3 / √(m : ℝ) * eS m u) +
      (1 + √2 + cgS (kappa ∘ kappa)) * LS m) / √(n : ℝ) +
    K4 n / (n : ℝ) * SS m + DS m / √(2 * (n : ℝ)) + q2 m u + q3 m u

/-! ## The first hidden layer at unit inputs -/

section layer1

variable {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {x x' : Fin n → ℝ} (hx : normSq x = 1)
  (hx' : normSq x' = 1)

include hx hx' in
lemma rho0_nn : 0 ≤ (1 + √2) * (1 - kappa^[4] (dotp x x')) -
    cgS (kappa ∘ kappa) * (1 - kappa (kappa (dotp x x'))) := by
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have ht := dotp_unit_mem hx hx'
  have hk := kk_memIcc ht
  have hk0 : 0 ≤ kappa (kappa (dotp x x')) :=
    (kappa_mem (kappa_mem_Icc ht).1 (kappa_mem_Icc ht).2).1
  have hX := secX_nonneg hG hk0 hk.2
  have e4 : (kappa ∘ kappa) (kappa (kappa (dotp x x'))) = kappa^[4] (dotp x x') := rfl
  rw [e4] at hX
  have h4 : 0 ≤ 1 - kappa^[4] (dotp x x') := by
    have := hG.le_one hk
    rw [e4] at this
    linarith
  have : 0 ≤ √2 * (1 - kappa^[4] (dotp x x')) := by positivity
  unfold cgS
  linarith

include hn hm hx hx' in
lemma l1R :
    L2nn (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ =>
        |rhoS (kappa ∘ kappa) (reluV (M.mulVec x)) (reluV (M.mulVec x'))|)
      ((m : ℝ) / 2 * (2 / (n : ℝ)) * ((1 + √2) * (1 - kappa^[4] (dotp x x')) -
        cgS (kappa ∘ kappa) * (1 - kappa (kappa (dotp x x'))) +
        (1 + √2) * q3 m (1 - dotp x x') + cgS (kappa ∘ kappa) * bkS m (1 - dotp x x'))) := by
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
  have h12 : (0 : ℝ) ≤ 1 + √2 := by positivity
  have hv1 : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hρ := rho0_nn hx hx'
  have h3 := reluPhiStmt hGk hv1 hm x x'
  have hph : phiD (((kappa ∘ kappa) ∘ kappa) ∘ kappa) x x' = 1 - kappa^[4] (dotp x x') := by
    rw [phiD_unit _ hx hx']; rfl
  rw [hph, normSq_sub_unit hx hx', hx, hx', dlt_unit hx hx', sub_self, abs_zero] at h3
  have hk := reluPhiStmt kGood_kappa hv1 hm x x'
  have hph2 : phiD (kappa ∘ kappa) x x' = 1 - kappa (kappa (dotp x x')) := by
    rw [phiD_unit _ hx hx']; rfl
  rw [hph2, normSq_sub_unit hx hx', hx, hx', dlt_unit hx hx', sub_self, abs_zero] at hk
  have comb := (h3.const_mul_nonneg h12).add0 ((hk.const_mul_nonneg hcg).neg)
    (by positivity) (by positivity)
  have comb' : L2le (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ =>
        rhoS (kappa ∘ kappa) (reluV (M.mulVec x)) (reluV (M.mulVec x')) -
          (m : ℝ) / 2 * (2 / (n : ℝ)) * ((1 + √2) * (1 - kappa^[4] (dotp x x')) -
            cgS (kappa ∘ kappa) * (1 - kappa (kappa (dotp x x'))))) _ :=
    comb.congr_fun fun M => by unfold rhoS; ring
  have r := addConst comb' (by positivity) (by positivity)
  refine ⟨(L2le.abs' r.1).congr_bound ?_, by unfold q3 bkS; positivity⟩
  unfold q3 bkS
  ring

end layer1

end AgS

open AgS

/-! ## The constants of the statement -/

/-- The constant term of `agent_phiS_L2`. -/
noncomputable def sA0 (n mA : ℕ) : ℝ := sQ n mA 0 0 0
/-- The coefficient of `1 − κ^{∘4}(t)`. -/
noncomputable def sA1 (n : ℕ) : ℝ := (1 + √2) / √(n : ℝ)
/-- The coefficient (with a MINUS sign) of `1 − κ(κ(t))`. -/
noncomputable def sA1' (n : ℕ) : ℝ := cgS (kappa ∘ kappa) / √(n : ℝ)
/-- The coefficient of `1 − t`. -/
noncomputable def sA2 (n mA : ℕ) : ℝ := sQ n mA 0 0 1 - sQ n mA 0 0 0

lemma sQ_affine (n m : ℕ) (a4 a2 u : ℝ) :
    sQ n m a4 a2 u = sA0 n m + sA1 n * a4 - sA1' n * a2 + sA2 n m * u := by
  unfold sA0 sA1 sA1' sA2 sQ q2 q3 bkS eS
  ring

lemma sA0_eq (n m : ℕ) : sA0 n m =
    ((1 + √2) * q3 m 0 + cgS (kappa ∘ kappa) * nc0 m + (1 + √2) * q2 m 0 +
      (1 + √2 + cgS (kappa ∘ kappa)) * LS m) / √(n : ℝ) +
    K4 n / (n : ℝ) * SS m + DS m / √(2 * (n : ℝ)) + q2 m 0 + q3 m 0 := by
  unfold sA0 sQ bkS eS nc0
  ring

lemma sA2_eq (n m : ℕ) : sA2 n m =
    (1 + √2 + cgS (kappa ∘ kappa)) * (2 * √3 / √(m : ℝ) +
      √3 / √(m : ℝ) * (4 * √(1 + 2 / (m : ℝ)))) / √(n : ℝ) +
    √3 / √(m : ℝ) * (4 * √(1 + 2 / (m : ℝ))) + 2 * √3 / √(m : ℝ) := by
  unfold sA2 sQ q2 q3 bkS eS
  ring

/-! ## The statement -/

section main

variable {n m : ℕ}

/-- **The distance form through the Agent network, with the secant link for `A₃`**, in terms
of `sQ`. -/
theorem agent_phiS_L2_sQ (hn : 1 ≤ n) (hm : 1 ≤ m) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    L2le (mlpGauss n m n)
      (fun A : MlpParam n m n => phiD (kappa ∘ kappa) (mlpEval A x) (mlpEval A x') -
        2 * (1 - kappa^[4] (dotp x x')))
      (2 * sQ n m (1 - kappa^[4] (dotp x x')) (1 - kappa (kappa (dotp x x')))
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
  have hbc : (0 : ℝ) ≤ bG (kappa ∘ kappa) * (√5 / (2 * √(m : ℝ))) := by positivity
  have hk4 : (0 : ℝ) ≤ 4 * Kr m / (m : ℝ) := by positivity
  have h12 : (0 : ℝ) ≤ 1 + √2 := by positivity
  have h12c : (0 : ℝ) ≤ 1 + √2 + cgS (kappa ∘ kappa) := by positivity
  have hc2e : (m : ℝ) / 2 * (2 / (m : ℝ)) = 1 := by field_simp
  have h31 : (n : ℝ) * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (n : ℝ))) = 2 := by field_simp
  -- the first hidden layer
  have aR := l1R hn hm hx hx'
  have aE := l1E hn hm hx hx'
  have aS := l1S hn hm hx hx'
  have aD := l1D hn hm hx hx' reluSqStmt
  have aL := l1L hn hm hx hx' reluDltStmt
  have aΦ : L2nn (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ =>
        bPhi (kappa ∘ kappa) m (reluV (M.mulVec x)) (reluV (M.mulVec x')))
      ((m : ℝ) / 2 * (2 / (n : ℝ)) * q2 m (1 - dotp x x')) :=
    (((aE.smul he3).add (aS.smul hbc)).add
      ((((aS.smul hk4).add (aD.smul he5)).add (aL.smul (c := 2) (by norm_num))).smul hg2)).congr
      (fun M => by unfold bPhi; ring) (by unfold q2; ring)
  have aLL : L2nn (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ => bL m (reluV (M.mulVec x)) (reluV (M.mulVec x')))
      ((m : ℝ) / 2 * (2 / (n : ℝ)) * LS m) :=
    ((aL.add (aS.smul hk4)).add (aD.smul he5)).congr (fun M => by unfold bL; ring)
      (by unfold LS; ring)
  have F1 : L2nn (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ =>
        bF (kappa ∘ kappa) m (2 / (m : ℝ)) (reluV (M.mulVec x)) (reluV (M.mulVec x'))) _ :=
    ((((aR.add (aΦ.smul h12)).add ((aE.smul he3).smul hcg)).add (aLL.smul h12c)).smul hc2).congr
      (fun M => by unfold bF; ring) rfl
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
          (reluV (A.2.1.mulVec (reluV (A.1.mulVec x'))))) :=
    (mPair (m_phiD hG.cont) (measurable_mlpEval_param x) (measurable_mlpEval_param x')).sub
      ((mPair (m_phiD hG.cont) (mH2 x) (mH2 x')).const_mul _)
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
      (comboS (genF hG hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x')))
        (genS hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x')))
        (genD reluSqStmt hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x'))) hc3 hq hk hi)
      (fun M₂ => linSec hG hv2 hn (reluV (M₂.mulVec (reluV (M₁.mulVec x))))
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
  · linear_combination (norm := (unfold sQ q2 q3 SS DS; ring1))
      (sQ n m (1 - kappa^[4] (dotp x x')) (1 - kappa (kappa (dotp x x'))) (1 - dotp x x') *
        ((n : ℝ) * (2 / (m : ℝ))) * ((m : ℝ) / 2 * (2 / (n : ℝ)))) * hc2e +
      sQ n m (1 - kappa^[4] (dotp x x')) (1 - kappa (kappa (dotp x x'))) (1 - dotp x x') * h31

/-- **`agent_phiS_L2`: the distance form through the Agent network, with the secant link for
the last matrix.** For unit `x, x′`, `t = ⟨x, x′⟩`:
`‖Φ_{κ∘κ}(A(x), A(x′)) − 2(1 − κ^{∘4}(t))‖₂ ≤
  2·(sA0 + sA1·(1 − κ^{∘4}(t)) − sA1'·(1 − κ(κ(t))) + sA2·(1 − t))`. -/
theorem agent_phiS_L2 (hn : 1 ≤ n) (hm : 1 ≤ m) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    L2le (mlpGauss n m n)
      (fun A : MlpParam n m n => phiD (kappa ∘ kappa) (mlpEval A x) (mlpEval A x') -
        2 * (1 - kappa^[4] (dotp x x')))
      (2 * (sA0 n m + sA1 n * (1 - kappa^[4] (dotp x x')) -
        sA1' n * (1 - kappa (kappa (dotp x x'))) + sA2 n m * (1 - dotp x x'))) := by
  have h := agent_phiS_L2_sQ hn hm hx hx'
  rwa [sQ_affine] at h

end main

/-! ## Nonnegativity -/

lemma sA1_nonneg (n : ℕ) : 0 ≤ sA1 n := by unfold sA1; positivity

lemma sA1'_nonneg (n : ℕ) : 0 ≤ sA1' n := by
  have := cgS_nonneg (kGood_kappa.comp_kappa)
  unfold sA1'; positivity

lemma sA2_nonneg (n m : ℕ) : 0 ≤ sA2 n m := by
  have := cgS_nonneg (kGood_kappa.comp_kappa)
  rw [sA2_eq]
  positivity

lemma sA0_nonneg (n m : ℕ) : 0 ≤ sA0 n m := by
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  have hb2 := bG_nonneg hG
  have hb3 := bG_nonneg hGk
  have hcg := cgS_nonneg hG
  have hg2 : 0 ≤ (kappa ∘ kappa) 0 := hG.nonneg_on KGood.zero_mem
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have := nc0_nn m; have := sS_nn m; have := dS_nn m; have := lS_nn m
  have := SS_nn m; have := DS_nn m; have := LS_nn m
  have := Kr_nonneg m; have := K4_nonneg n
  have h2 : 0 ≤ q2 m 0 := by unfold q2 eS; positivity
  have h3 : 0 ≤ q3 m 0 := by unfold q3; positivity
  rw [sA0_eq]
  positivity

/-- The whole bound of `agent_phiS_L2` is nonnegative. -/
lemma agentS_bound_nonneg (n m : ℕ) {x x' : Fin n → ℝ} (hx : normSq x = 1)
    (hx' : normSq x' = 1) :
    0 ≤ sA0 n m + sA1 n * (1 - kappa^[4] (dotp x x')) -
      sA1' n * (1 - kappa (kappa (dotp x x'))) + sA2 n m * (1 - dotp x x') := by
  have h0 := sA0_nonneg n m
  have h2 := sA2_nonneg n m
  obtain ⟨-, hu⟩ := tau_nonneg hx hx'
  have hρ := rho0_nn hx hx'
  have e : sA1 n * (1 - kappa^[4] (dotp x x')) - sA1' n * (1 - kappa (kappa (dotp x x'))) =
      ((1 + √2) * (1 - kappa^[4] (dotp x x')) -
        cgS (kappa ∘ kappa) * (1 - kappa (kappa (dotp x x')))) / √(n : ℝ) := by
    unfold sA1 sA1'; ring
  have h1 : 0 ≤ sA1 n * (1 - kappa^[4] (dotp x x')) -
      sA1' n * (1 - kappa (kappa (dotp x x'))) := by
    rw [e]; positivity
  have h3 : 0 ≤ sA2 n m * (1 - dotp x x') := mul_nonneg h2 hu
  linarith

/-! ## The numbers at the width `mA n = n²`, `n ≥ 4096` -/

namespace AgS

lemma cg2_le : cgS (kappa ∘ kappa) ≤ 1 / 2 := by
  have hk0 : 0 ≤ kappa 0 := kGood_kappa.nonneg_on KGood.zero_mem
  rw [cg2_eq]
  linarith

lemma cg2_ge : 3408 / 10000 ≤ cgS (kappa ∘ kappa) := by
  have := kappa_zero_le
  rw [cg2_eq]
  linarith

section focus

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

lemma q3z_le : q3 (mA n) 0 ≤ 64 / 100 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  have hb3 := bG_nonneg hGk
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have b3 := b3_le
  have g3 := g3_le
  have h5 := sqrt5_le'
  have hK := Kr_mA_le hn
  have hK0 := Kr_nonneg (mA n)
  have hyy : y ^ 2 ≤ y * (1 / 4096) := by nlinarith
  unfold q3
  rw [sqrt_mA, mA_eqR, ← hy]
  refine le_trans (le_of_eq (?_ : _ = bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
    ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2))) ?_
  · rw [hy]; ring
  · calc bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
          ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2)
        ≤ 28416 / 100000 * (223607 / 100000 * (y / 2)) * 2 +
          1 * (4 * (11 / 5) * y ^ 2 * 2) := by gcongr
      _ ≤ 64 / 100 * y := by nlinarith

lemma q2z_le : q2 (mA n) 0 ≤ 749 / 1000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hb2 := bG_nonneg hG
  have hg2 : 0 ≤ (kappa ∘ kappa) 0 := hG.nonneg_on KGood.zero_mem
  have b2 := b2_le
  have g2 := g2_le
  have h5 := sqrt5_le'
  have hK := Kr_mA_le hn
  have hK0 := Kr_nonneg (mA n)
  have a5 := sS_le hn
  have a6 := dS_le hn
  have a7 := lS_le hn
  have n5 := sS_nn (mA n)
  have n6 := dS_nn (mA n)
  have n7 := lS_nn (mA n)
  have hyy : y ^ 2 ≤ y * (1 / 4096) := by nlinarith
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
      _ ≤ 749 / 1000 * y := by nlinarith

end focus

end AgS

section focusBounds

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

/-- `sA1 ≤ 2.4143/√n`. -/
theorem sA1_le : sA1 n ≤ 24143 / 10000 / √(n : ℝ) := by
  have h2 := sqrt2_le
  have hs0 : (0 : ℝ) < √(n : ℝ) := by have := sqrt_n_ge hn; linarith
  unfold sA1
  exact div_le_div_of_nonneg_right (by linarith) hs0.le

/-- `sA1' ≥ 0.3408/√n` (the coefficient with the minus sign: a LOWER bound). -/
theorem sA1'_ge : 3408 / 10000 / √(n : ℝ) ≤ sA1' n := by
  have hs0 : (0 : ℝ) < √(n : ℝ) := by have := sqrt_n_ge hn; linarith
  unfold sA1'
  exact div_le_div_of_nonneg_right cg2_ge hs0.le

/-- `sA2 ≤ 10.9/n`. -/
theorem sA2_le : sA2 n (mA n) ≤ 109 / 10 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr hn
  have h3 := sqrt3_le
  have h2 := sqrt2_le
  have hQ := Q2_le hn
  have hcg := cgS_nonneg (kGood_kappa.comp_kappa)
  have hcl := cg2_le
  have hzy : z * y ≤ y * (1 / 64) := by nlinarith
  rw [sA2_eq, sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = (1 + √2 + cgS (kappa ∘ kappa)) * (2 * √3 * y +
    √3 * y * (4 * √(1 + 2 / (mA n : ℝ)))) * z + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))) +
    2 * √3 * y)) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 109 / 10 * y) (le_of_eq (by rw [hy]; ring))
    calc (1 + √2 + cgS (kappa ∘ kappa)) * (2 * √3 * y +
          √3 * y * (4 * √(1 + 2 / (mA n : ℝ)))) * z + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))) +
          2 * √3 * y
        ≤ (1 + 141422 / 100000 + 1 / 2) * (2 * (17321 / 10000) * y +
          17321 / 10000 * y * (4 * (1001 / 1000))) * z +
          17321 / 10000 * y * (4 * (1001 / 1000)) + 2 * (17321 / 10000) * y := by gcongr
      _ ≤ 109 / 10 * y := by nlinarith

/-- `sA0 ≤ 8.6/n`. -/
theorem sA0_le : sA0 n (mA n) ≤ 86 / 10 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr hn
  have h2 := sqrt2_le
  have hcg := cgS_nonneg (kGood_kappa.comp_kappa)
  have hcl := cg2_le
  have hK4 := K4_le hn
  have hK40 := K4_nonneg n
  have a1 := nc0_le hn
  have a2 := SS_le hn
  have a3 := DS_le hn
  have a4 := LS_le hn
  have a5 := q2z_le hn
  have a6 := q3z_le hn
  have n1 := nc0_nn (mA n)
  have n2 := SS_nn (mA n)
  have n3 := DS_nn (mA n)
  have n4 := LS_nn (mA n)
  have n5 : 0 ≤ q2 (mA n) 0 := by
    have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
    have hb2 := bG_nonneg hG
    have hg2 : 0 ≤ (kappa ∘ kappa) 0 := hG.nonneg_on KGood.zero_mem
    have := sS_nn (mA n); have := dS_nn (mA n); have := lS_nn (mA n)
    have := Kr_nonneg (mA n)
    unfold q2 eS; positivity
  have n6 : 0 ≤ q3 (mA n) 0 := by
    have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := (kGood_kappa.comp_kappa).comp_kappa
    have hb3 := bG_nonneg hGk
    have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
    have := Kr_nonneg (mA n)
    unfold q3; positivity
  rw [← hy] at a1 a3 a4 a5 a6
  have hzy : z * y ≤ y * (1 / 64) := by nlinarith
  have hyr : y * r ≤ y * (1 / 90) := mul_le_mul_of_nonneg_left hr2 hy0.le
  rw [sA0_eq]
  refine le_trans (le_of_eq (?_ : _ =
    ((1 + √2) * q3 (mA n) 0 + cgS (kappa ∘ kappa) * nc0 (mA n) + (1 + √2) * q2 (mA n) 0 +
      (1 + √2 + cgS (kappa ∘ kappa)) * LS (mA n)) * z +
    K4 n * y * SS (mA n) + DS (mA n) * r + q2 (mA n) 0 + q3 (mA n) 0)) ?_
  · rw [hy, hz, hr]; ring
  · refine le_trans (?_ : _ ≤ 86 / 10 * y) (le_of_eq (by rw [hy]; ring))
    calc ((1 + √2) * q3 (mA n) 0 + cgS (kappa ∘ kappa) * nc0 (mA n) +
          (1 + √2) * q2 (mA n) 0 + (1 + √2 + cgS (kappa ∘ kappa)) * LS (mA n)) * z +
          K4 n * y * SS (mA n) + DS (mA n) * r + q2 (mA n) 0 + q3 (mA n) 0
        ≤ ((1 + 141422 / 100000) * (64 / 100 * y) + 1 / 2 * (815 / 1000 * y) +
          (1 + 141422 / 100000) * (749 / 1000 * y) +
          (1 + 141422 / 100000 + 1 / 2) * (12 / 1000 * y)) * z +
          3466 / 1000 * y * (2005 / 1000) + 895 / 100 * y * r + 749 / 1000 * y +
          64 / 100 * y := by gcongr
      _ ≤ 86 / 10 * y := by nlinarith

end focusBounds

end BstLean.Part142

open BstLean.Part142 in
#print axioms agent_phiS_L2
open BstLean.Part142 in
#print axioms agentS_bound_nonneg
open BstLean.Part142 in
#print axioms sA0_le
open BstLean.Part142 in
#print axioms sA1_le
open BstLean.Part142 in
#print axioms sA1'_ge
open BstLean.Part142 in
#print axioms sA2_le
