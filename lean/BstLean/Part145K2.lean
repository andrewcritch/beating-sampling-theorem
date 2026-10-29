import BstLean.Part145K1
import BstLean.Part143AgentC

/-!
# Part 145 (K2): the centred part of the Agent link with the exact variance of the last matrix

`cAg` is the centred part of `Part143AgentC` (it is NOT changed). Only its `L²` bound changes:
`cLin_L2x` (file `Part145K1`) is in the place of `cLin_L2`. `G = κ∘κ`, `dK = 55/1000`,
`cK = dK/√2`.

* `dGood_kk`: `DGood (κ∘κ) dK 0.3408455 0.506`.
* `cLin_L2c`: `cLin_L2x` in the shape `m·v·(√2·fRc (δ/√2) G h h′/√m)`,
  `fRc c G = (Φ_G − δ) − c·(e − δ)`.
* `genFRc`: `fRc c G` after one ReLU layer, in `L²` (the copy of `genFR` with a number `c ≥ 0`).
* **`cAg_L2x`**: unit `x, x′`, `t = ⟨x, x′⟩`:
  `‖cAg‖₂ ≤ 2·(cC0x + cC1·(1 − κ^{∘4}(t)) − cC1x'·(1 − κ(κ(t))) + cC2x·(1 − t))`,
  `cC1 n = √2/√n` (of `Part143AgentC`), `cC1x' n = dK/√n`.
* Numbers at `mA n = n²`, `n ≥ 8100`: `cC0x ≤ 0.02243/n`, `cC2x ≤ 0.1697/n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part142
open BstLean.Part143

open AgD AgS AgC

/-! ## The numbers `dK`, `cK` -/

/-- The number `δ` of `cUnit_L2x` for `G = κ∘κ`. -/
noncomputable def dK : ℝ := 55 / 1000

/-- `cK = dK/√2`. -/
noncomputable def cK : ℝ := dK / √2

lemma sqrt2_geK : (14142 : ℝ) / 10000 ≤ √2 := (Real.le_sqrt' (by norm_num)).2 (by norm_num)

lemma dK_nonneg : 0 ≤ dK := by unfold dK; norm_num

lemma cK_nonneg : 0 ≤ cK := by unfold cK dK; positivity

lemma sqrt2_mul_cK : √2 * cK = dK := by
  unfold cK
  field_simp

lemma cK_le : cK ≤ 389 / 10000 := by
  have h := sqrt2_geK
  unfold cK dK
  rw [div_le_iff₀ (by positivity)]
  linarith

lemma cK_le_cg : cK ≤ cgS (kappa ∘ kappa) := by
  have h1 := cK_le
  have h2 := kappa_zero_le
  rw [cg2_eq]
  linarith

/-- **The hypotheses on `δ` for `κ∘κ`**, `δ = 55/1000`, `l₁ = 0.3408455`, `x₀ = 0.506`. -/
theorem dGood_kk : DGood (kappa ∘ kappa) dK (3408455 / 10000000) (506 / 1000) where
  d0 := dK_nonneg
  hl := by
    have h := kappa_zero_ge
    have e : (1 - (kappa ∘ kappa) (-1)) / 2 = cgS (kappa ∘ kappa) := rfl
    rw [e, cg2_eq]
    linarith
  hx := by
    have h := kappa2_zero_le
    simp only [Function.comp_apply]
    linarith
  hlx := by norm_num
  hq := by
    have h := sqrt2_le
    unfold dK
    linarith
  hvx := by
    have h := sqrt2_le
    unfold dK
    linarith
  hd := by
    have h := sqrt2_geK
    unfold dK
    linarith

namespace AgK

section defs

variable {ι : Type*} [Fintype ι]

/-- `(Φ_G − δ) − c·(e − δ)`. -/
noncomputable def fRc (c : ℝ) (G : ℝ → ℝ) (y y' : ι → ℝ) : ℝ :=
  (phiD G y y' - dlt y y') - c * (eD y y' - dlt y y')

/-- The conditional reference of `fRc` after one ReLU layer (without the scale). -/
noncomputable def rhoRc (c : ℝ) (G : ℝ → ℝ) (p p' : ι → ℝ) : ℝ :=
  phiD (G ∘ kappa) p p' - c * phiD kappa p p'

/-- The `L²` bound of `fRc` after one ReLU layer. -/
noncomputable def bFRc (c : ℝ) (G : ℝ → ℝ) (m : ℕ) (v : ℝ) (p p' : ι → ℝ) : ℝ :=
  (m : ℝ) / 2 * v * (|rhoRc c G p p'| + bPhi G m p p' +
    c * (√3 / √(m : ℝ) * normSq (p - p')) + (1 + c) * bL m p p')

end defs

section gen

variable {m k : ℕ} {v : ℝ}

/-- `cLin_L2x` in the shape of `comboC`. -/
lemma cLin_L2c {G : ℝ → ℝ} {δ l₁ x₀ : ℝ} (hG : KGood G) (hD : DGood G δ l₁ x₀) (hv : 0 < v)
    (hm : 1 ≤ m) (h h' : Fin k → ℝ) (hd : 0 ≤ dotp h h') :
    L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ => cLin G m v M h h')
      ((m : ℝ) * v * (√2 * fRc (δ / √2) G h h' / √(m : ℝ))) := by
  have h2 : √2 * (δ / √2) = δ := by field_simp
  refine (cLin_L2x hG hD hv hm h h' hd).congr_bound ?_
  have e : √2 * fRc (δ / √2) G h h' =
      √2 * (phiD G h h' - dlt h h') - √2 * (δ / √2) * (eD h h' - dlt h h') := by
    unfold fRc; ring
  rw [e, h2]

/-- **`fRc` after one ReLU layer, in `L²`.** -/
lemma genFRc {G : ℝ → ℝ} (hG : KGood G) {c : ℝ} (hc : 0 ≤ c) (hv : 0 < v) (hm : 1 ≤ m)
    (p p' : Fin k → ℝ) :
    L2nn (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => fRc c G (reluV (M.mulVec p)) (reluV (M.mulVec p')))
      (bFRc c G m v p p') := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 ≤ (m : ℝ) / 2 * v := by positivity
  have hbb := bG_nonneg hG
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  have hK := Kr_nonneg m
  have hN := normSq_nonneg p
  have hN' := normSq_nonneg p'
  have hE := normSq_nonneg (p - p')
  have hd := dlt_nonneg p p'
  have P0 := L2le.const (μ := gaussMat m k v) ((m : ℝ) / 2 * v * rhoRc c G p p')
  have P1 := reluPhiStmt hG hv hm p p'
  have P2 := ((reluEDStmt hv hm p p').const_mul_nonneg hc).neg
  have gl := genL reluDltStmt hv hm p p'
  have P3 := gl.1.neg
  have P4 := gl.1.const_mul_nonneg hc
  have s1 := P0.add0 P1 (abs_nonneg _) (by positivity)
  have s2 := s1.add0 P2 (by positivity) (by positivity)
  have s3 := s2.add0 P3 (by positivity) (by positivity)
  have s4 := s3.add0 P4 (by positivity) (by positivity)
  refine ⟨(s4.congr_fun fun M => ?_).congr_bound ?_, ?_⟩
  · unfold fRc rhoRc
    ring
  · rw [abs_mul, abs_of_nonneg hs]
    have e := sconv (m := (m : ℝ)) (√3 / 2) (v * normSq (p - p'))
    unfold bFRc bPhi bL
    linear_combination c * e
  · unfold bFRc bPhi bL
    positivity

end gen

/-! ## The constants -/

/-- The bound of `cAg_L2x` (without the factor `2`), as a function of `a₄ = 1 − κ^{∘4}(t)`,
`a₂ = 1 − κ(κ(t))`, `u = 1 − t`. -/
noncomputable def cQx (n m : ℕ) (a4 a2 u : ℝ) : ℝ :=
  √2 * (a4 - cK * a2 + q3 m u + cK * bkS m u + q2 m u + cK * (√3 / √(m : ℝ) * eS m u) +
    (1 + cK) * LS m) / √(n : ℝ)

/-! ## The first hidden layer at unit inputs -/

section layer1

variable {n m : ℕ} {x x' : Fin n → ℝ}

lemma rho0Rc_nn (hx : normSq x = 1) (hx' : normSq x' = 1) :
    0 ≤ (1 - kappa^[4] (dotp x x')) - cK * (1 - kappa (kappa (dotp x x'))) := by
  have h := rho0R_nn hx hx'
  obtain ⟨hτ, -⟩ := tau_nonneg hx hx'
  have := mul_le_mul_of_nonneg_right cK_le_cg hτ
  linarith

lemma l1RRc (hn : 1 ≤ n) (hm : 1 ≤ m) (hx : normSq x = 1) (hx' : normSq x' = 1) :
    L2nn (gaussMat m n (2 / (n : ℝ)))
      (fun M : Matrix (Fin m) (Fin n) ℝ =>
        |rhoRc cK (kappa ∘ kappa) (reluV (M.mulVec x)) (reluV (M.mulVec x'))|)
      ((m : ℝ) / 2 * (2 / (n : ℝ)) * ((1 - kappa^[4] (dotp x x')) -
        cK * (1 - kappa (kappa (dotp x x'))) +
        q3 m (1 - dotp x x') + cK * bkS m (1 - dotp x x'))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  obtain ⟨hτ, hu⟩ := tau_nonneg hx hx'
  have hcg := cK_nonneg
  have hb3 := bG_nonneg hGk
  have hbk := bG_nonneg kGood_kappa
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have hk0 : 0 ≤ kappa 0 := kGood_kappa.nonneg_on KGood.zero_mem
  have hKr := Kr_nonneg m
  have hv1 : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hρ := rho0Rc_nn hx hx'
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
        rhoRc cK (kappa ∘ kappa) (reluV (M.mulVec x)) (reluV (M.mulVec x')) -
          (m : ℝ) / 2 * (2 / (n : ℝ)) * ((1 - kappa^[4] (dotp x x')) -
            cK * (1 - kappa (kappa (dotp x x'))))) _ :=
    comb.congr_fun fun M => by unfold rhoRc; ring
  have r := addConst comb' (by positivity) (by positivity)
  refine ⟨(L2le.abs' r.1).congr_bound ?_, by unfold q3 bkS; positivity⟩
  unfold q3 bkS
  ring

end layer1

end AgK

open AgK

/-! ## The constants of the statement -/

/-- The constant term of `cAg_L2x`. -/
noncomputable def cC0x (n mA : ℕ) : ℝ := cQx n mA 0 0 0
/-- The coefficient (with a MINUS sign) of `1 − κ(κ(t))` in `cAg_L2x`. -/
noncomputable def cC1x' (n : ℕ) : ℝ := dK / √(n : ℝ)
/-- The coefficient of `1 − t` in `cAg_L2x`. -/
noncomputable def cC2x (n mA : ℕ) : ℝ := cQx n mA 0 0 1 - cQx n mA 0 0 0

lemma cQx_affine (n m : ℕ) (a4 a2 u : ℝ) :
    cQx n m a4 a2 u = cC0x n m + cC1 n * a4 - cC1x' n * a2 + cC2x n m * u := by
  have e : cC1x' n = √2 * cK / √(n : ℝ) := by unfold cC1x'; rw [sqrt2_mul_cK]
  rw [e]
  unfold cC0x cC1 cC2x cQx q2 q3 bkS eS
  ring

lemma cC0x_eq (n m : ℕ) : cC0x n m =
    √2 * (q3 m 0 + cK * nc0 m + q2 m 0 + (1 + cK) * LS m) / √(n : ℝ) := by
  unfold cC0x cQx bkS eS nc0
  ring

lemma cC2x_eq (n m : ℕ) : cC2x n m =
    √2 * ((1 + cK) * (2 * √3 / √(m : ℝ) + √3 / √(m : ℝ) * (4 * √(1 + 2 / (m : ℝ))))) /
      √(n : ℝ) := by
  unfold cC2x cQx q2 q3 bkS eS
  ring

/-- `cC1x' n = dK/√n`. -/
theorem cC1x'_eq (n : ℕ) : cC1x' n = dK / √(n : ℝ) := rfl

lemma cC0x_nonneg (n m : ℕ) : 0 ≤ cC0x n m := by
  have := q2z_nn m; have := q3z_nn m; have := nc0_nn m; have := LS_nn m
  have := cK_nonneg
  rw [cC0x_eq]; positivity

lemma cC1x'_nonneg (n : ℕ) : 0 ≤ cC1x' n := by
  have := dK_nonneg
  unfold cC1x'; positivity

lemma cC2x_nonneg (n m : ℕ) : 0 ≤ cC2x n m := by
  have := cK_nonneg
  rw [cC2x_eq]; positivity

/-! ## The statement -/

section main

variable {n m : ℕ}

/-- **The centred part, in `L²`, with the exact variance of the last matrix**, in terms of
`cQx`. -/
theorem cAg_L2x_cQ (hn : 1 ≤ n) (hm : 1 ≤ m) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    L2le (mlpGauss n m n) (fun A : MlpParam n m n => cAg A x x')
      (2 * cQx n m (1 - kappa^[4] (dotp x x')) (1 - kappa (kappa (dotp x x')))
        (1 - dotp x x')) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hcK := cK_nonneg
  have hKm := Kr_nonneg m
  have hv2 : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hc3 : (0 : ℝ) ≤ (n : ℝ) * (2 / (m : ℝ)) := by positivity
  have hc2 : (0 : ℝ) ≤ (m : ℝ) / 2 * (2 / (m : ℝ)) := by positivity
  have hq : (0 : ℝ) ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hq0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hn'
  have he3 : (0 : ℝ) ≤ √3 / √(m : ℝ) := by positivity
  have he5 : (0 : ℝ) ≤ √5 / √(m : ℝ) := by positivity
  have hk4 : (0 : ℝ) ≤ 4 * Kr m / (m : ℝ) := by positivity
  have h1c : (0 : ℝ) ≤ 1 + cK := by positivity
  have aR := l1RRc hn hm hx hx'
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
        bFRc cK (kappa ∘ kappa) m (2 / (m : ℝ)) (reluV (M.mulVec x)) (reluV (M.mulVec x'))) _ :=
    ((((aR.add aΦ).add ((aE.smul he3).smul hcK)).add (aLL.smul h1c)).smul hc2).congr
      (fun M => by unfold bFRc; ring) rfl
  have mf := measurable_cAg_param (m := m) x x'
  have T := prodNN (μ := gaussMat m n (2 / (n : ℝ)))
    (ν := (gaussMat m m (2 / (m : ℝ))).prod (gaussMat n m (2 / (m : ℝ)))) mf
    (comboC F1 hc3 hq)
    (fun M₁ => (prodNN (μ := gaussMat m m (2 / (m : ℝ))) (ν := gaussMat n m (2 / (m : ℝ)))
      (mf.comp measurable_prodMk_left)
      (comboC (genFRc hG hcK hv2 hm (reluV (M₁.mulVec x)) (reluV (M₁.mulVec x'))) hc3 hq)
      (fun M₂ => cLin_L2c hG dGood_kk hv2 hn (reluV (M₂.mulVec (reluV (M₁.mulVec x))))
        (reluV (M₂.mulVec (reluV (M₁.mulVec x')))) (dotp_relu_nonneg _ _))).1)
  unfold mlpGauss
  refine T.1.congr_bound ?_
  unfold cQx
  field_simp

/-- **`cAg_L2x`: the centred part, in `L²`, with the exact variance of the last matrix.** -/
theorem cAg_L2x (hn : 1 ≤ n) (hm : 1 ≤ m) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    L2le (mlpGauss n m n) (fun A : MlpParam n m n => cAg A x x')
      (2 * (cC0x n m + cC1 n * (1 - kappa^[4] (dotp x x')) -
        cC1x' n * (1 - kappa (kappa (dotp x x'))) + cC2x n m * (1 - dotp x x'))) := by
  have h := cAg_L2x_cQ hn hm hx hx'
  rwa [cQx_affine] at h

end main

/-! ## The numbers at the width `mA n = n²`, `n ≥ 8100` -/

namespace AgK

section focus

variable {n : ℕ} (hn : 8100 ≤ n)

include hn

lemma n4096K : 4096 ≤ n := le_trans (by norm_num) hn

/-- `y = 1/n`, `z = 1/√n` at `n ≥ 8100`. -/
lemma yzK : ∃ y z : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧
    0 < y ∧ 0 < z ∧ y ≤ 1 / 8100 ∧ z ≤ 1 / 90 := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr (n4096K hn)
  have hx : (8100 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (90 : ℝ) ≤ √(n : ℝ) := (Real.le_sqrt' (by norm_num)).2 (by linarith)
  refine ⟨y, z, hy, hz, hy0, hz0, ?_, ?_⟩
  · rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  · rw [hz]; exact one_div_le_one_div_of_le (by norm_num) hs

lemma Q2_leK : √(1 + 2 / (mA n : ℝ)) ≤ 10000001 / 10000000 := by
  have hx : (8100 : ℝ) ≤ n := by exact_mod_cast hn
  refine sqrt_le_of_sq (by norm_num) ?_
  rw [mA_eqR]
  have h2' : (65610000 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h' : 2 / (n : ℝ) ^ 2 ≤ 2 / 65610000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2'
  have e : ((10000001 : ℝ) / 10000000) ^ 2 = 100000020000001 / 100000000000000 := by norm_num
  rw [e]
  linarith

lemma q3z_leK : q3 (mA n) 0 ≤ 638 / 1000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, hy, hz, hy0, hz0, hy1, hz1⟩ := yzK hn
  have hn4 := n4096K hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  have hb3 := bG_nonneg hGk
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have b3 := b3_le
  have g3 := g3_le
  have h5 := sqrt5_le'
  have hK := Kr_mA_le hn4
  have hK0 := Kr_nonneg (mA n)
  have hyy : y ^ 2 ≤ y * (1 / 8100) := by nlinarith
  unfold q3
  rw [sqrt_mA, mA_eqR, ← hy]
  refine le_trans (le_of_eq (?_ : _ = bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
    ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2))) ?_
  · rw [hy]; ring
  · calc bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
          ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2)
        ≤ 28416 / 100000 * (223607 / 100000 * (y / 2)) * 2 +
          1 * (4 * (11 / 5) * y ^ 2 * 2) := by gcongr
      _ ≤ 638 / 1000 * y := by nlinarith

lemma q2z_leK : q2 (mA n) 0 ≤ 745 / 1000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, hy, hz, hy0, hz0, hy1, hz1⟩ := yzK hn
  have hn4 := n4096K hn
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
  have hyy : y ^ 2 ≤ y * (1 / 8100) := by nlinarith
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
      _ ≤ 745 / 1000 * y := by nlinarith

end focus

end AgK

section focusBounds

variable {n : ℕ} (hn : 8100 ≤ n)

include hn

/-- `cC0x ≤ 0.02243/n`. -/
theorem cC0x_le : cC0x n (mA n) ≤ 2243 / 100000 / (n : ℝ) := by
  obtain ⟨y, z, hy, hz, hy0, hz0, hy1, hz1⟩ := yzK hn
  have hn4 := n4096K hn
  have h2 := sqrt2_le
  have hc := cK_le
  have hc0 := cK_nonneg
  have a1 := nc0_le hn4
  have a4 := LS_le hn4
  have a5 := q2z_leK hn
  have a6 := q3z_leK hn
  have n1 := nc0_nn (mA n)
  have n4 := LS_nn (mA n)
  have n5 := q2z_nn (mA n)
  have n6 := q3z_nn (mA n)
  rw [← hy] at a1 a4 a5 a6
  have hzy : y * z ≤ y * (1 / 90) := mul_le_mul_of_nonneg_left hz1 hy0.le
  rw [cC0x_eq]
  refine le_trans (le_of_eq (?_ : _ = √2 * (q3 (mA n) 0 + cK * nc0 (mA n) + q2 (mA n) 0 +
    (1 + cK) * LS (mA n)) * z)) ?_
  · rw [hz]; ring
  · refine le_trans (?_ : _ ≤ 2243 / 100000 * y) (le_of_eq (by rw [hy]; ring))
    calc √2 * (q3 (mA n) 0 + cK * nc0 (mA n) + q2 (mA n) 0 + (1 + cK) * LS (mA n)) * z
        ≤ 141422 / 100000 * (638 / 1000 * y + 389 / 10000 * (815 / 1000 * y) +
          745 / 1000 * y + (1 + 389 / 10000) * (12 / 1000 * y)) * z := by gcongr
      _ ≤ 2243 / 100000 * y := by nlinarith

/-- `cC2x ≤ 0.1697/n`. -/
theorem cC2x_le : cC2x n (mA n) ≤ 1697 / 10000 / (n : ℝ) := by
  obtain ⟨y, z, hy, hz, hy0, hz0, hy1, hz1⟩ := yzK hn
  have h3 := sqrt3_le
  have h2 := sqrt2_le
  have hc := cK_le
  have hc0 := cK_nonneg
  have hQ := Q2_leK hn
  have hzy : y * z ≤ y * (1 / 90) := mul_le_mul_of_nonneg_left hz1 hy0.le
  rw [cC2x_eq, sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = √2 * ((1 + cK) * (2 * √3 * y +
    √3 * y * (4 * √(1 + 2 / (mA n : ℝ))))) * z)) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 1697 / 10000 * y) (le_of_eq (by rw [hy]; ring))
    calc √2 * ((1 + cK) * (2 * √3 * y + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))))) * z
        ≤ 141422 / 100000 * ((1 + 389 / 10000) * (2 * (17321 / 10000) * y +
          17321 / 10000 * y * (4 * (10000001 / 10000000)))) * z := by gcongr
      _ ≤ 1697 / 10000 * y := by nlinarith

end focusBounds

end BstLean.Part145

open BstLean.Part145 in
#print axioms dGood_kk
open BstLean.Part145 in
#print axioms cAg_L2x
open BstLean.Part145 in
#print axioms cC0x_le
open BstLean.Part145 in
#print axioms cC2x_le
