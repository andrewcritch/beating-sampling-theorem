import BstLean.Part169Sig

/-!
# Part 169 (file `Var`): the inputs `V`, `v_max`, `C_v`, `H_f` on the good set

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, formula `t7:p08:inputs`
(`‖Var_v f‖_{L²(s)} ≤ C_*/(n(n − 3))`), the pointwise `v_max = q Λ²/(n(n − 3))`, and the
energy input that gives `‖f̄‖_q ≤ 1 + H_{16}`.

* `fX_eq_lam`: `f = √e_b·λ`; `fX_hom`, `fX_euLip`: `f` is positively 1-homogeneous and
  `Λ/√n`-Lipschitz on the operator events.
* **`VR_eq`**: `V = E_v f² − f̄²` (`= Var_v f`) when `b ≠ 0` (from `S = γ_A(ω − f²)`).
* **`VR_le`**: on `goodD`, `0 ≤ V ≤ vmaxN n = 2(O₂O₁)²/(n(n − 2))` (Lemma LS, `p = 1`).
* **`VR_L2`**: on `goodD`, `∫_K (nV)² ≤ CvN n²`, `CvN n = 5.1·0.7315/(n − 2)`: Part 166's
  latitude certificate (`∫∫Ψ_λ¹² ≤ (5.1/n)¹²`), Part 162's `int_var_psi`, `V = e_b Var_v λ`,
  and `e_b ≤ 0.7315` (Part 160's `eb16_sharp`).
* **`Hf_goodD`**: on `goodD`, `|f̄| ≤ HfN n = O₂O₁/√n` (a crude deterministic bound, about
  `4.03`; the paper's energy event gives about `1.0013`).
* `MomZ`: the exact-rule `L⁸` bounds only; **`classifier_paper_exact80k`**: the end theorem
  where `BIAS_hyp` is replaced by the two exact-rule `L⁸` bounds and the numerical condition.
-/

namespace BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part134
open BstLean.Part161 (latC Ix muI xLat lamX sigX)
open BstLean.Part162 (lbar psiA)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53 measurable_unitF)

variable {n : ℕ}

lemma fX_eq_lam (c : Ret n) (x : Fin n → ℝ) :
    fX c x = √(eR c) * lamX (paperDesignP n) c x := by
  unfold lamX fX lam eR
  rw [paperDesignP_bA]
  by_cases hb : normSq (bR c) = 0
  · rw [hb]; simp
  have hb0 : 0 < normSq (bR c) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hb)
  rw [Real.sqrt_div' _ (Nat.cast_nonneg n)]
  have h1 : √(normSq (bR c)) ^ 2 = normSq (bR c) := Real.sq_sqrt hb0.le
  have h2 : 0 < √(normSq (bR c)) := Real.sqrt_pos.mpr hb0
  field_simp
  rw [h1]

lemma fX_hom (c : Ret n) (t : ℝ) (x : Fin n → ℝ) (ht : 0 < t) : fX c (t • x) = t * fX c x := by
  unfold fX
  rw [BstLean.Part153.hid2_smul _ _ ht.le]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1; refine Finset.sum_congr rfl fun j _ => by ring

lemma fX_euLip (hn : 1 ≤ n) (c : Ret n) {O₁ O₂ : ℝ} (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO₁ : 0 ≤ O₁) (hO₂ : 0 ≤ O₂) :
    BstLean.Part148.EuLip (fX c) (O₂ * O₁ / √(n : ℝ)) := by
  intro x y
  refine (fX_sub_le hn c x y).trans ?_
  have hh := hid2_sub_le h1 h2 x y
  have e : ∑ i, (x i - y i) ^ 2 = normSq (x - y) := rfl
  rw [e]
  have hs : √(normSq (hid2 (A1 c) (A2 c) x - hid2 (A1 c) (A2 c) y)) ≤ O₂ * O₁ * √(normSq (x - y)) := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (normSq_nonneg _)]
    nlinarith [hh]
  calc _ ≤ O₂ * O₁ * √(normSq (x - y)) / √(n : ℝ) :=
        div_le_div_of_nonneg_right hs (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- The latitude field `v ↦ f(x_s(v))` is integrable, and so is its square (bounded). -/
lemma int_fX_lat (hn : 1 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    Integrable (fun v => fX c (xLat c s (unitF53 v))) (stdGauss (Fin (n - 1))) ∧
      Integrable (fun v => fX c (xLat c s (unitF53 v)) ^ 2) (stdGauss (Fin (n - 1))) := by
  have m : Measurable (fun v => fX c (xLat c s (unitF53 v))) :=
    (continuous_fX c).measurable.comp (BstLean.Part161.measurable_xLat_comp c measurable_const
      measurable_unitF)
  have hb : ∀ v, |fX c (xLat c s (unitF53 v))| ≤
      √(BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c)) / √(n : ℝ) :=
    fun v => bdd_fX hn c (normSq_xLat_le' hn c hs v)
  refine ⟨Integrable.mono' (integrable_const _) m.aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hb v), ?_⟩
  refine Integrable.mono' (integrable_const ((√(BstLean.Part131.frob (A2 c) *
    BstLean.Part131.frob (A1 c)) / √(n : ℝ)) ^ 2)) (m.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb v) 2

lemma int_wX_lat (c : Ret n) {s : ℝ} (hn : 1 ≤ n) (hs : s ^ 2 ≤ 1) :
    Integrable (fun v => wX c (xLat c s (unitF53 v))) (stdGauss (Fin (n - 1))) := by
  refine Integrable.mono' (integrable_const (BstLean.Part131.frob (A2 c) *
    BstLean.Part131.frob (A1 c) / n)) ((continuous_wX c).measurable.comp
    (BstLean.Part161.measurable_xLat_comp c measurable_const measurable_unitF)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs]; exact bdd_wX c (normSq_xLat_le' hn c hs v)

/-- **`V = E_v f² − f̄²`** (for `b ≠ 0`). -/
theorem VR_eq (hn : 1 ≤ n) (c : Ret n) (hb : normSq (bR c) ≠ 0) (a : Ix n) :
    VR c a = ∫ v, fX c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) ^ 2
        ∂stdGauss (Fin (n - 1)) - fbR c a ^ 2 := by
  set s := latC (paperDesignP n) c a
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨-, i2⟩ := int_fX_lat hn c hs
  have iw := int_wX_lat c hn hs
  have hS : (dP c).Sb a = 2 / (n : ℝ) * (wbR c a -
      ∫ v, fX c (xLat c s (unitF53 v)) ^ 2 ∂stdGauss (Fin (n - 1))) := by
    show ∫ v, BstLean.Part161.sA (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) = _
    have hpt : ∀ v, BstLean.Part161.sA (paperDesignP n) c a v =
        2 / (n : ℝ) * (wX c (xLat c s (unitF53 v)) - fX c (xLat c s (unitF53 v)) ^ 2) := by
      intro v
      show sigX (paperDesignP n) c (xLat c s (unitF53 v)) ^ 2 = _
      unfold sigX
      rw [paperDesignP_bA, sA_eq (by omega) hb]
      rfl
    simp only [hpt]
    rw [integral_const_mul, integral_sub iw i2, wbR_eq]
    rfl
  unfold VR
  rw [hS]
  field_simp
  ring

/-- `E(F − EF)² = EF² − (EF)²`. -/
lemma var_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {F : α → ℝ} (i1 : Integrable F μ) (i2 : Integrable (fun x => F x ^ 2) μ) :
    ∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ = ∫ x, F x ^ 2 ∂μ - (∫ x, F x ∂μ) ^ 2 := by
  set m := ∫ y, F y ∂μ
  have : (fun x => (F x - m) ^ 2) = fun x => F x ^ 2 - 2 * m * F x + m ^ 2 := by
    funext x; ring
  have hi : Integrable (fun x => F x ^ 2 - 2 * m * F x) μ := i2.sub (i1.const_mul _)
  rw [this, integral_add (f := fun x => F x ^ 2 - 2 * m * F x) hi (integrable_const _),
    integral_sub i2 (i1.const_mul _), integral_const_mul, integral_const, smul_eq_mul,
    probReal_univ, one_mul]
  ring

/-- `v_max = 2(O₂O₁)²/(n(n − 2))`. -/
noncomputable def vmaxN (n : ℕ) : ℝ := 2 * (O2n n * O1n n / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2)

/-- **The pointwise variance bound on the good set**: `0 ≤ V ≤ v_max`. -/
theorem VR_le (hn : 80000 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) (a : Ix n) : 0 ≤ VR c a ∧ VR c a ≤ vmaxN n := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨he, -⟩ := cA_input (by omega) hc
  have hb : normSq (bR c) ≠ 0 := by
    intro h; unfold eR at he; rw [h] at he; simp at he
  obtain ⟨h1, h2⟩ := opB_goodD (by omega) hc
  have hO1 := (O1n_pos (n := n) hn1).le
  have hO2 := (O2n_pos (n := n) hn1).le
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O2n n * O1n n / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O2n n * O1n n / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O2n n * O1n n / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (80000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    unfold vmaxN
    exact div_le_div_of_nonneg_right hpsi h2n.le

/-- `C_v = 5.1·0.7315/(n − 2)`. -/
noncomputable def CvN (n : ℕ) : ℝ := 51 / 10 * (7315 / 10000) / ((n : ℝ) - 2)

/-- `e_b ≤ 0.7315` on the good set (Part 160's `eb16_sharp`). -/
lemma eR_le (hn : 16384 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) : eR c ≤ 7315 / 10000 := by
  obtain ⟨hτ, hθ0, hθ1⟩ := BstLean.Part164.window_goodA hn passF passW measurable_passF
    measurable_passW _ c hc
  have hup := BstLean.Part160.eb16_sharp hn hτ hθ0 hθ1
    (BstLean.Part164.goodC16_of_goodA hn passF passW measurable_passF measurable_passW hc)
    (hc.2.2.1.1.2 hτ)
  have hb := BstLean.Part160.paperDesign_agentCentre passF passW measurable_passF
    measurable_passW c
  rw [← hb] at hup
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hm] at hup
  unfold eR
  have e : normSq (bR c) = normSq ((paperDesign n passF passW measurable_passF
    measurable_passW).bA c.1 c.2.1.1) := rfl
  rw [e, div_le_iff₀ hnR]
  have : 2 / (n : ℝ) ^ 2 * normSq ((paperDesign n passF passW measurable_passF
      measurable_passW).bA c.1 c.2.1.1) * ((n : ℝ) ^ 2 / 2) ≤
      2 / (n : ℝ) * (7315 / 10000) * ((n : ℝ) ^ 2 / 2) :=
    mul_le_mul_of_nonneg_right hup (by positivity)
  have e1 : 2 / (n : ℝ) ^ 2 * normSq ((paperDesign n passF passW measurable_passF
      measurable_passW).bA c.1 c.2.1.1) * ((n : ℝ) ^ 2 / 2) = normSq ((paperDesign n passF passW
      measurable_passF measurable_passW).bA c.1 c.2.1.1) := by field_simp
  have e2 : 2 / (n : ℝ) * (7315 / 10000) * ((n : ℝ) ^ 2 / 2) = 7315 / 10000 * n := by
    field_simp
  linarith

/-- **The `L²` bound of `nV` on the good set**: `∫_K (nV)² ≤ C_v²`, `C_v = 5.1·0.7315/(n − 2)`. -/
theorem VR_L2 (hn : 80000 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) :
    ∫ a in KR c, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ CvN n ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (80000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨he, -⟩ := cA_input (by omega) hc
  have hb : normSq (bR c) ≠ 0 := by
    intro h; unfold eR at he; rw [h] at he; simp at he
  have heR := eR_le (by omega) hc
  -- `V = e_b·Var_v λ`
  set Vl : Ix n → ℝ := fun a => ∫ v, (lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) -
    ∫ w, lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2 ∂stdGauss (Fin (n - 1)) with hVl
  have hVe : ∀ a, VR c a = eR c * Vl a := by
    intro a
    have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
    obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
    have hV := VR_eq hn1 c hb a
    rw [fbR_eq] at hV
    unfold fbarS at hV
    rw [← var_eq i1 i2] at hV
    rw [hV, hVl]
    simp only [fX_eq_lam c]
    have hin : ∫ w, √(eR c) * lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a)
        (unitF53 w)) ∂stdGauss (Fin (n - 1)) = √(eR c) * ∫ w, lamX (paperDesignP n) c
          (xLat c (latC (paperDesignP n) c a) (unitF53 w)) ∂stdGauss (Fin (n - 1)) :=
      integral_const_mul _ _
    rw [hin]
    have e2 : ∀ v, (√(eR c) * lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a)
        (unitF53 v)) - √(eR c) * ∫ w, lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a)
          (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2 =
        eR c * (lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) -
          ∫ w, lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 w))
            ∂stdGauss (Fin (n - 1))) ^ 2 := by
      intro v; rw [← mul_sub, mul_pow, Real.sq_sqrt he.le]
    simp only [e2]
    exact integral_const_mul _ _
  -- the latitude certificate
  have h12 := (BstLean.Part166.certs_of_goodD hn passF passW measurable_passF measurable_passW
    hc).1
  have h2 := BstLean.Part162.psi_low_of_12 (by omega) (paperDesignP n) c (BstLean.Part162.lipLam_nonneg (paperDesignP n) c)
    (BstLean.Part162.lamX_euLip (paperDesignP n) c) (fun t x ht => BstLean.Part162.lamX_hom (paperDesignP n) c t x ht)
    (C := 51 / 10) (by norm_num) h12 (j := 2) (m := 6) (by norm_num) (by norm_num)
  have hint := BstLean.Part162.int_var_psi (by omega) (paperDesignP n) c (BstLean.Part162.lipLam_nonneg (paperDesignP n) c)
    (BstLean.Part162.lamX_euLip (paperDesignP n) c) (fun t x ht => BstLean.Part162.lamX_hom (paperDesignP n) c t x ht)
    (C := 51 / 10) (by norm_num) h2
  -- from `K` to the whole index space
  obtain ⟨MV, bV⟩ := bdd_VR hn1 c
  have mV := measurable_VR c
  have iV : Integrable (fun a => ((n : ℝ) * VR c a) ^ 2) (muI n) := by
    have := intOn_of_bdd ((mV.const_mul (n : ℝ)).pow_const 2) (bdd_pow (bdd_nmul bV) 2)
      Set.univ
    rwa [IntegrableOn, Measure.restrict_univ] at this
  have hK : ∫ a in KR c, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ ∫ a, ((n : ℝ) * VR c a) ^ 2 ∂muI n :=
    setIntegral_le_integral iV (Filter.Eventually.of_forall fun a => sq_nonneg _)
  refine hK.trans ?_
  have e : (fun a => ((n : ℝ) * VR c a) ^ 2) = fun a => ((n : ℝ) * eR c) ^ 2 * Vl a ^ 2 := by
    funext a; rw [hVe a]; ring
  rw [e, integral_const_mul]
  calc ((n : ℝ) * eR c) ^ 2 * ∫ a, Vl a ^ 2 ∂muI n
      ≤ ((n : ℝ) * eR c) ^ 2 * (51 / 10 / n / ((n : ℝ) - 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hint (sq_nonneg _)
    _ = (51 / 10 * eR c / ((n : ℝ) - 2)) ^ 2 := by field_simp
    _ ≤ CvN n ^ 2 := by
        unfold CvN
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        exact div_le_div_of_nonneg_right (by nlinarith) h2n.le

/-- `H_f = O₂O₁/√n` (crude: about `4.03`). -/
noncomputable def HfN (n : ℕ) : ℝ := O2n n * O1n n / √(n : ℝ)

/-- **`|f̄| ≤ H_f` on the good set.** -/
theorem fbR_le (hn : 16384 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) (a : Ix n) : |fbR c a| ≤ HfN n := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨h1, h2⟩ := opB_goodD hn hc
  have hO1 := (O1n_pos (n := n) hn1).le
  have hO2 := (O2n_pos (n := n) hn1).le
  rw [fbR_eq]; unfold fbarS
  refine abs_int_le fun v => ?_
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  have h := fX_sub_le hn1 c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) 0
  have e : fX c 0 = 0 := by unfold fX; rw [hid2_zero']; simp
  rw [e, sub_zero, hid2_zero', sub_zero] at h
  exact h.trans (div_le_div_of_nonneg_right (sqrt_hid2_le hn1 c h1 h2 hO1 hO2 hs v)
    (Real.sqrt_nonneg _))

lemma int_pow_le_of_bdd {F : Ix n → ℝ} {H : ℝ} (hF : ∀ a, |F a| ≤ H) (K : Set (Ix n))
    (mF : Measurable F) (k : ℕ) : ∫ a in K, F a ^ k ∂muI n ≤ H ^ k := by
  have hH : 0 ≤ H := (abs_nonneg _).trans (hF (Classical.arbitrary _))
  have hpt : ∀ a, F a ^ k ≤ H ^ k := fun a =>
    (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hF a) k)
  refine (integral_mono (intOn_of_bdd (mF.pow_const k) (bdd_pow hF k) K) (integrable_const _)
    hpt).trans ?_
  rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
  have h1 : (muI n).real K ≤ 1 := measureReal_le_one
  nlinarith [pow_nonneg hH k, measureReal_nonneg (μ := muI n) (s := K)]

/-- **The exact-rule `L⁸` bounds**: the only moment inputs of Part 08 left after Part 169. -/
structure MomZ (c : Ret n) (Af Aw : ℝ) : Prop where
  hXF : ∫ a in KR c, exF c a ^ 8 ∂muI n ≤ Af ^ 8
  hXW : ∫ a in KR c, exW c a ^ 8 ∂muI n ≤ Aw ^ 8

/-- **The classifier theorem with `BIAS_hyp` reduced to the exact-rule `L⁸` bounds** (every
`n ≥ 80 000`). Remaining: `MomZ` (the `L⁸` bounds `A_f`, `A_ω` of the exact Gaussian-rule
errors `n(f̄(s_g) − f_G(s_g))`, `n(ω̄(s_g) − ω_G(s_g))` on the kept indices) on
`goodD n D (E_A ∩ E_bias)`, the numerical condition `P_B ≤ 0.004295²` with the explicit
constants `vmaxN`, `HfN`, `CvN`, `aFn`, `aWn`, and the charges `δ_A + δ_bias ≤ roomE`. -/
theorem classifier_paper_exact80k (hn : 80000 ≤ n) (t : ℝ)
    {EA Eb : Set (Ret n)} (hEA : MeasurableSet EA) (hEb : MeasurableSet Eb) {δA δb : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hb : (retDist (paperCentres n)).real Ebᶜ ≤ δb)
    (hroom : δA + δb ≤ BstLean.Part167.roomE)
    {ε Af Aw : ℝ} (hε1 : ε < 1) (hT : 0 < ε - vmaxN n / dStar) (hAf : 0 < Af) (hAw : 0 < Aw)
    (hnum : PB n (BstLean.Part164.chiUp n / n) dStar ε (vmaxN n) (aWn n Aw √(sig0sq n))
      (aFn n Af √(sig0sq n)) (HfN n) (CvN n) ≤ (4295 / 10 ^ 6) ^ 2)
    (hM : ∀ c ∈ goodD n (paperDesignP n) (EA ∩ Eb), MomZ c Af Aw) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (80000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hHf : 0 < HfN n := by
    have := O1n_pos (n := n) hn1; have := O2n_pos (n := n) hn1
    unfold HfN; positivity
  have hCv : 0 < CvN n := by unfold CvN; positivity
  refine classifier_paper_momY80k hn t hEA hEb hA hb hroom hε1 hT hAf hAw hHf hCv hnum
    fun c hc => ?_
  have hZ := hM c hc
  have bf := fbR_le (by omega) hc
  refine ⟨fun a _ => ?_, hZ.hXF, hZ.hXW, int_pow_le_of_bdd bf _ (measurable_fbR c) 4,
    int_pow_le_of_bdd bf _ (measurable_fbR c) 24, VR_L2 hn hc⟩
  obtain ⟨h0, h1⟩ := VR_le hn hc a
  rw [abs_of_nonneg h0]; exact h1

end BstLean.Part169
