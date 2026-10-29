import BstLean.Part143LinC

/-!
# Part 145 (K1): the exact variance of the centred part of the link of one linear Gaussian layer

`M` is a Gaussian matrix with `m` rows and entry variance `v`; `h, h′` are unit vectors,
`τ = ⟨h, h′⟩ ∈ [0, 1]`. `cUnit` is the centred part of `Part143LinC`. The bound `cUnit_L2` of
`Part143LinC` uses the triangle inequality. Here the two squares `|M(h + h′)|²` and
`|M(h − h′)|²` are uncorrelated, and the variance is computed exactly.

* `lin_ac_var`: `E(a·((|Mh|² + |Mh′|²)/2 − m·v) + c·(e(Mh, Mh′) − m·v(1 − τ)))² =
    m·v²·(a²(1 + τ)² + (a + 2c)²(1 − τ)²)/2`.
* `DGood G δ l₁ x₀`: the hypotheses on the number `δ`: `0 ≤ δ`, `(1 − G(−1))/2 ≤ l₁ ≤ x₀ ≤ 1 − G 0`,
  `0 ≤ (3/4)x₀² − (l₁/2 + 2√2·δ)x₀ − l₁²/4 + δ²`, `l₁/2 + 2√2·δ ≤ (3/2)x₀`, `δ ≤ √2·x₀`.
* `DGood.key`: `r²(1 + τ²) + 2c² + 2rc(1 − τ) ≤ (√2·s_hi − δ)²` and `δ ≤ √2·s_hi`.
* **`cUnit_L2x`**: `‖cUnit‖₂ ≤ √m·v·(√2·(1 − G τ) − δ·(1 − τ))`.
* **`cLin_L2x`**: `⟨h, h′⟩ ≥ 0`:
  `‖cLin‖₂ ≤ m·v·(√2·(Φ_G(h, h′) − δ(h, h′)) − δ·(e(h, h′) − δ(h, h′)))/√m`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part142
open BstLean.Part143

variable {m k : ℕ}

/-! ## The exact variance -/

/-- Unit `h, h′`, `τ = ⟨h, h′⟩`: the second moment of
`a·((|Mh|² + |Mh′|²)/2 − m·v) + c·(e(Mh, Mh′) − m·v(1 − τ))`. -/
theorem lin_ac_var {v : ℝ} (hv : 0 ≤ v) {h h' : Fin k → ℝ} (hh : normSq h = 1)
    (hh' : normSq h' = 1) (a c : ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (a * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2 - (m : ℝ) * v) +
        c * (eD (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * (1 - dotp h h'))) ^ 2)
      (gaussMat m k v) ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ,
      (a * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2 - (m : ℝ) * v) +
        c * (eD (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * (1 - dotp h h'))) ^ 2
      ∂gaussMat m k v =
      (m : ℝ) * v ^ 2 * ((a ^ 2 * (1 + dotp h h') ^ 2 +
        (a + 2 * c) ^ 2 * (1 - dotp h h') ^ 2) / 2) := by
  obtain ⟨iP2, eP2⟩ := row_two hv (h + h')
  obtain ⟨iQ2, eQ2⟩ := row_two hv (h - h')
  obtain ⟨iP4, eP4⟩ := row_four hv (h + h')
  obtain ⟨iQ4, eQ4⟩ := row_four hv (h - h')
  obtain ⟨iU4, eU4⟩ := row_four hv h
  obtain ⟨iV4, eV4⟩ := row_four hv h'
  set τ := dotp h h' with hτ
  set α : ℝ := a / 4 with hα
  set β : ℝ := a / 4 + c / 2 with hβ
  set K : ℝ := v * (a + c * (1 - τ)) with hK
  set f : (Fin k → ℝ) → ℝ := fun r =>
    a * ((dotp r h ^ 2 + dotp r h' ^ 2) / 2 - v) +
      c * ((dotp r h ^ 2 + dotp r h' ^ 2) / 2 - dotp r h * dotp r h' - v * (1 - τ)) with hfdef
  have hf : Measurable f := by
    have mU := measurable_dotp_left (k := k) h
    have mV := measurable_dotp_left (k := k) h'
    have mS : Measurable (fun r : Fin k → ℝ => (dotp r h ^ 2 + dotp r h' ^ 2) / 2) :=
      ((mU.pow_const 2).add (mV.pow_const 2)).div_const 2
    exact ((mS.sub measurable_const).const_mul a).add
      (((mS.sub (mU.mul mV)).sub measurable_const).const_mul c)
  have f1 : (fun ξ : Fin k → ℝ => f (Real.sqrt v • ξ)) = fun ξ =>
      α * dotp (Real.sqrt v • ξ) (h + h') ^ 2 + -K -
        -β * dotp (Real.sqrt v • ξ) (h - h') ^ 2 -
        0 * dotp (Real.sqrt v • ξ) (h - h') ^ 2 - 0 * dotp (Real.sqrt v • ξ) (h - h') ^ 2 := by
    funext ξ
    simp only [hfdef, dotp_add_right, dotp_sub_right, hα, hβ, hK]
    ring
  obtain ⟨-, m1⟩ := integral_lin4 (μ := stdGauss (Fin k)) iP2 iQ2 iQ2 iQ2 (-K) α (-β) 0 0
  have mean0 : ∫ ξ : Fin k → ℝ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k) = 0 := by
    rw [f1, m1, eP2, eQ2, normSq_add, normSq_sub, hh, hh', ← hτ, hα, hβ, hK]
    ring
  -- the part of degree four
  set g : (Fin k → ℝ) → ℝ := fun ξ =>
    (α ^ 2 - α * β / 3) * dotp (Real.sqrt v • ξ) (h + h') ^ 4 + 0 -
      -(β ^ 2 - α * β / 3) * dotp (Real.sqrt v • ξ) (h - h') ^ 4 -
      -(8 / 3 * (α * β)) * dotp (Real.sqrt v • ξ) h ^ 4 -
      -(8 / 3 * (α * β)) * dotp (Real.sqrt v • ξ) h' ^ 4 with hgdef
  obtain ⟨ig, mg⟩ := integral_lin4 (μ := stdGauss (Fin k)) iP4 iQ4 iU4 iV4 0
    (α ^ 2 - α * β / 3) (-(β ^ 2 - α * β / 3)) (-(8 / 3 * (α * β))) (-(8 / 3 * (α * β)))
  have f2 : (fun ξ : Fin k → ℝ => f (Real.sqrt v • ξ) ^ 2) = fun ξ =>
      1 * g ξ + K ^ 2 - (2 * K * α) * dotp (Real.sqrt v • ξ) (h + h') ^ 2 -
        (2 * K * β) * dotp (Real.sqrt v • ξ) (h - h') ^ 2 -
        0 * dotp (Real.sqrt v • ξ) (h - h') ^ 2 := by
    funext ξ
    simp only [hfdef, hgdef, dotp_add_right, dotp_sub_right, hα, hβ, hK]
    ring
  obtain ⟨i2, m2⟩ := integral_lin4 (μ := stdGauss (Fin k)) ig iP2 iQ2 iQ2 (K ^ 2)
    1 (2 * K * α) (2 * K * β) 0
  rw [← f2] at i2 m2
  obtain ⟨is, es⟩ := rows_sum_sq (m := m) v f hf i2
  have hN : ∀ (M : Matrix (Fin m) (Fin k) ℝ) (w : Fin k → ℝ),
      normSq (M.mulVec w) = ∑ i, dotp (rowOf i M) w ^ 2 := fun M w => rfl
  have hD : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      dotp (M.mulVec h) (M.mulVec h') = ∑ i, dotp (rowOf i M) h * dotp (rowOf i M) h' :=
    fun M => rfl
  have hsum : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      a * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2 - (m : ℝ) * v) +
        c * (eD (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * (1 - τ)) = ∑ i, f (rowOf i M) := by
    intro M
    unfold eD
    rw [hN, hN, hD]
    simp only [hfdef, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp_rw [hsum]
  refine ⟨is, ?_⟩
  rw [es, mean0, m2, mg, eP4, eQ4, eU4, eV4, eP2, eQ2, normSq_add, normSq_sub, hh, hh', ← hτ,
    hα, hβ, hK]
  ring

/-! ## The number `δ` -/

/-- The hypotheses on the number `δ` of `cUnit_L2x`. `l₁` is an upper bound of the slope
`(1 − G(−1))/2` and `x₀` is a lower bound of the slope `1 − G 0`. -/
structure DGood (G : ℝ → ℝ) (δ l₁ x₀ : ℝ) : Prop where
  d0 : 0 ≤ δ
  hl : (1 - G (-1)) / 2 ≤ l₁
  hx : x₀ ≤ 1 - G 0
  hlx : l₁ ≤ x₀
  hq : 0 ≤ 3 / 4 * x₀ ^ 2 - (l₁ / 2 + 2 * √2 * δ) * x₀ - l₁ ^ 2 / 4 + δ ^ 2
  hvx : l₁ / 2 + 2 * √2 * δ ≤ 3 / 2 * x₀
  hd : δ ≤ √2 * x₀

section key

variable {G : ℝ → ℝ} {δ l₁ x₀ τ : ℝ}

/-- `s_lo(τ) ≤ (1 − G(−1))/2` and `1 − G 0 ≤ s_hi(τ)` for `0 ≤ τ < 1`. -/
lemma secant_ends (hG : KGood G) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    sLo G τ ≤ (1 - G (-1)) / 2 ∧ 1 - G 0 ≤ sHi G τ ∧ 0 ≤ sLo G τ ∧ sLo G τ ≤ sHi G τ ∧
      sHi G τ ≤ 1 := by
  have hX := secX_nonneg hG hτ0 hτ1.le
  have hLo := sLo_mul (G := G) hτ0
  have hHi := sHi_mul (G := G) hτ1
  have hLo0 := sLo_nonneg hG hτ0 hτ1
  have hHi1 := sHi_le_one hG hτ0 hτ1
  obtain ⟨s, a, b, e⟩ := secant_mem hG hτ0 hτ1 (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 from
    ⟨by norm_num, by norm_num⟩)
  refine ⟨?_, ?_, hLo0, by linarith, hHi1⟩
  · by_contra hneg
    push Not at hneg
    nlinarith
  · have e' : 1 - G 0 = sHi G τ * (1 - τ) + s * τ := by rw [hHi]; linarith
    rw [e']
    nlinarith

/-- **The algebra of the improvement.** -/
theorem DGood.key (hG : KGood G) (hD : DGood G δ l₁ x₀) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    δ ≤ √2 * sHi G τ ∧
      rS G τ ^ 2 * (1 + τ ^ 2) + 2 * cS G τ ^ 2 + 2 * rS G τ * cS G τ * (1 - τ) ≤
        (√2 * sHi G τ - δ) ^ 2 := by
  obtain ⟨hl1, hx1, hl0, hlx, hx2⟩ := secant_ends hG hτ0 hτ1
  have h22 : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2p : (0 : ℝ) < √2 := by positivity
  have hδ := hD.d0
  set x := sHi G τ with hxd
  set l := sLo G τ with hld
  set s := √(2 : ℝ) with hsd
  have a1 := hD.hl
  have a2 := hD.hx
  have a3 := hD.hlx
  have a4 := hD.hq
  have a5 := hD.hvx
  have a6 := hD.hd
  have hl1' : l ≤ l₁ := by linarith
  have hx0 : x₀ ≤ x := by linarith
  have hl10 : 0 ≤ l₁ := by linarith
  have hxl : l₁ ≤ x := by linarith
  have hx00 : 0 ≤ x := by linarith
  refine ⟨by nlinarith, ?_⟩
  have T1 : 0 ≤ (1 + τ) / 4 * ((l₁ - l) * (2 * (1 - τ) * x + (1 + τ) * (l + l₁))) := by
    have : 0 ≤ 2 * (1 - τ) * x + (1 + τ) * (l + l₁) := by nlinarith
    have : 0 ≤ (l₁ - l) * (2 * (1 - τ) * x + (1 + τ) * (l + l₁)) :=
      mul_nonneg (by linarith) this
    exact mul_nonneg (by linarith) this
  have T2 : 0 ≤ τ / 4 * ((2 - τ) * ((x - l₁) * (x + l₁)) + 2 * τ * (l₁ * (x - l₁))) := by
    have b1 : 0 ≤ (x - l₁) * (x + l₁) := mul_nonneg (by linarith) (by linarith)
    have b2 : 0 ≤ l₁ * (x - l₁) := mul_nonneg hl10 (by linarith)
    have b3 : 0 ≤ (2 - τ) * ((x - l₁) * (x + l₁)) := mul_nonneg (by linarith) b1
    have b4 : 0 ≤ 2 * τ * (l₁ * (x - l₁)) := mul_nonneg (by linarith) b2
    exact mul_nonneg (by linarith) (by linarith)
  have T3 : 0 ≤ (x - x₀) * (3 / 4 * (x + x₀) - (l₁ / 2 + 2 * s * δ)) :=
    mul_nonneg (by linarith) (by linarith)
  have e : (s * x - δ) ^ 2 - (rS G τ ^ 2 * (1 + τ ^ 2) + 2 * cS G τ ^ 2 +
      2 * rS G τ * cS G τ * (1 - τ)) =
      (1 + τ) / 4 * ((l₁ - l) * (2 * (1 - τ) * x + (1 + τ) * (l + l₁))) +
      τ / 4 * ((2 - τ) * ((x - l₁) * (x + l₁)) + 2 * τ * (l₁ * (x - l₁))) +
      (x - x₀) * (3 / 4 * (x + x₀) - (l₁ / 2 + 2 * s * δ)) +
      (3 / 4 * x₀ ^ 2 - (l₁ / 2 + 2 * s * δ) * x₀ - l₁ ^ 2 / 4 + δ ^ 2) := by
    simp only [rS, cS, ← hxd, ← hld]
    linear_combination (x ^ 2) * h22
  linarith

end key

/-! ## Unit vectors -/

section unit

variable {G : ℝ → ℝ} {v δ l₁ x₀ : ℝ} {h h' : Fin k → ℝ}

/-- **The centred part at unit vectors, in `L²`, from the exact variance.** -/
theorem cUnit_L2x (hG : KGood G) (hD : DGood G δ l₁ x₀) (hv : 0 < v) (hm : 1 ≤ m)
    (hh : normSq h = 1) (hh' : normSq h' = 1) (hd : 0 ≤ dotp h h') :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        cUnit G ((m : ℝ) * v) (dotp h h') (M.mulVec h) (M.mulVec h'))
      (√(m : ℝ) * v * (√2 * (1 - G (dotp h h')) - δ * (1 - dotp h h'))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hτ1, eDh, enh⟩ := unit_facts hh hh'
  set τ := dotp h h' with hτ
  rcases eq_or_lt_of_le hτ1 with h1 | h1
  · have hz : normSq (h - h') = 0 := by rw [enh, h1]; ring
    have he : h = h' := sub_eq_zero.mp (normSq_eq_zero hz)
    refine ((L2le_zero (μ := gaussMat m k v) (le_refl 0)).congr_fun fun M => ?_).congr_bound ?_
    · unfold cUnit
      rw [he, eD_eq, sub_self, h1]
      simp [normSq]
    · rw [h1, hG.one]; ring
  obtain ⟨hk1, hk2⟩ := hD.key hG hd h1
  have hHi := sHi_mul (G := G) h1
  obtain ⟨i, e⟩ := lin_ac_var (m := m) hv.le hh hh' ((1 - τ) * rS G τ) (cS G τ)
  rw [← hτ] at i e
  have hqq : √(m : ℝ) ^ 2 = m := Real.sq_sqrt hm'.le
  refine L2le.mk' (measurable_cUnit_lin (m := m) G ((m : ℝ) * v) τ h h').aestronglyMeasurable
    (i.congr (Filter.Eventually.of_forall fun M => by simp only [cUnit])) ?_
  have e' : ∫ M : Matrix (Fin m) (Fin k) ℝ,
      cUnit G ((m : ℝ) * v) τ (M.mulVec h) (M.mulVec h') ^ 2 ∂gaussMat m k v =
      (m : ℝ) * v ^ 2 * ((((1 - τ) * rS G τ) ^ 2 * (1 + τ) ^ 2 +
        ((1 - τ) * rS G τ + 2 * cS G τ) ^ 2 * (1 - τ) ^ 2) / 2) := by
    rw [← e]
    exact integral_congr_ae (Filter.Eventually.of_forall fun M => by simp only [cUnit])
  rw [e']
  have eB : (√(m : ℝ) * v * (√2 * (1 - G τ) - δ * (1 - τ))) ^ 2 =
      (m : ℝ) * v ^ 2 * ((1 - τ) ^ 2 * (√2 * sHi G τ - δ) ^ 2) := by
    rw [← hHi]
    linear_combination (v ^ 2 * (√2 * (sHi G τ * (1 - τ)) - δ * (1 - τ)) ^ 2) * hqq
  rw [eB]
  have eL : (((1 - τ) * rS G τ) ^ 2 * (1 + τ) ^ 2 +
      ((1 - τ) * rS G τ + 2 * cS G τ) ^ 2 * (1 - τ) ^ 2) / 2 =
      (1 - τ) ^ 2 * (rS G τ ^ 2 * (1 + τ ^ 2) + 2 * cS G τ ^ 2 +
        2 * rS G τ * cS G τ * (1 - τ)) := by ring
  rw [eL]
  have hmv : 0 ≤ (m : ℝ) * v ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk2 (sq_nonneg _)) hmv

end unit

/-! ## All vectors -/

section gen

variable {G : ℝ → ℝ} {v δ l₁ x₀ : ℝ}

/-- The product form of `√2·(Φ_G − δ) − δ·(e − δ)`. -/
lemma fX_eq {ι : Type*} [Fintype ι] (G : ℝ → ℝ) (δ : ℝ) (y y' : ι → ℝ) :
    √2 * (phiD G y y' - dlt y y') - δ * (eD y y' - dlt y y') =
      nrm y * nrm y' * (√2 * (1 - G (cosv y y')) - δ * (1 - cosv y y')) := by
  have edot : dotp y y' = cosv y y' * (nrm y * nrm y') := dotp_eq_cosv_mul y y'
  unfold phiD psi eD dlt
  rw [edot]
  ring

/-- `0 ≤ √2·(Φ_G − δ) − δ·(e − δ)` for `⟨y, y′⟩ ≥ 0`. -/
lemma fX_nonneg {ι : Type*} [Fintype ι] (hG : KGood G) (hD : DGood G δ l₁ x₀) (y y' : ι → ℝ)
    (hd : 0 ≤ dotp y y') :
    0 ≤ √2 * (phiD G y y' - dlt y y') - δ * (eD y y' - dlt y y') := by
  have hnn := nrm_mul_nonneg y y'
  rw [fX_eq]
  set τ := cosv y y' with hτ
  have hτ1 : τ ≤ 1 := (cosv_mem y y').2
  have hτ0 : 0 ≤ τ := by rw [hτ]; unfold cosv; exact div_nonneg hd hnn
  refine mul_nonneg hnn ?_
  rcases eq_or_lt_of_le hτ1 with h1 | h1
  · rw [h1, hG.one]; simp
  · obtain ⟨hk1, -⟩ := hD.key hG hτ0 h1
    have hHi := sHi_mul (G := G) h1
    rw [← hHi]
    nlinarith

/-- **The centred part, in `L²`, from the exact variance.** -/
theorem cLin_L2x (hG : KGood G) (hD : DGood G δ l₁ x₀) (hv : 0 < v) (hm : 1 ≤ m)
    (h h' : Fin k → ℝ) (hd : 0 ≤ dotp h h') :
    L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ => cLin G m v M h h')
      ((m : ℝ) * v * ((√2 * (phiD G h h' - dlt h h') - δ * (eD h h' - dlt h h')) /
        √(m : ℝ))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hpd := fX_nonneg hG hD h h' hd
  have hb0 : 0 ≤ (m : ℝ) * v * ((√2 * (phiD G h h' - dlt h h') - δ * (eD h h' - dlt h h')) /
      √(m : ℝ)) := by positivity
  by_cases hz : normSq h = 0
  · simp only [cLin_zero_left G v _ hz h']
    exact L2le_zero hb0
  by_cases hz' : normSq h' = 0
  · simp only [cLin_zero_right G v _ h hz']
    exact L2le_zero hb0
  have ha0 : 0 < nrm h := nrm_pos_of_ne hz
  have hb0' : 0 < nrm h' := nrm_pos_of_ne hz'
  have hτ0 : 0 ≤ dotp ((nrm h)⁻¹ • h) ((nrm h')⁻¹ • h') := by
    rw [dotp_smul_smul]
    positivity
  have hu := (cUnit_L2x (m := m) hG hD hv hm (normed_unit hz) (normed_unit hz')
    hτ0).const_mul_nonneg (c := nrm h * nrm h') (by positivity)
  simp only [cLin_eq]
  refine hu.congr_bound ?_
  rw [fX_eq, dotp_normed]
  have hq0 : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hm'
  have hqq : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt hm'.le
  have hmq : (m : ℝ) / √(m : ℝ) = √(m : ℝ) := by rw [div_eq_iff hq0.ne']; exact hqq.symm
  calc nrm h * nrm h' * (√(m : ℝ) * v * (√2 * (1 - G (cosv h h')) - δ * (1 - cosv h h')))
      = v * (nrm h * nrm h' * (√2 * (1 - G (cosv h h')) - δ * (1 - cosv h h'))) *
          √(m : ℝ) := by ring
    _ = v * (nrm h * nrm h' * (√2 * (1 - G (cosv h h')) - δ * (1 - cosv h h'))) *
          ((m : ℝ) / √(m : ℝ)) := by rw [hmq]
    _ = _ := by ring

end gen

end BstLean.Part145

open BstLean.Part145 in
#print axioms lin_ac_var
open BstLean.Part145 in
#print axioms DGood.key
open BstLean.Part145 in
#print axioms cUnit_L2x
open BstLean.Part145 in
#print axioms cLin_L2x
