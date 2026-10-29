import BstLean.Part174U55T171
import BstLean.Part172All

/-!
# Part 174 (file `U55T172`): Part 172's results that need `n ≥ 80 000`, re-proved for `n ≥ 55 000`

No proof is left open; no `native_decide` or `axiom` is used.

A copy of file `T172` (57 000 chain) for `n ≥ 55 000`, namespace `BstLean.Part174.N55`. The
docstrings can carry older numbers; the Lean statements are authoritative.

Changed constants (57 000 → 55 000): `s_g² ≥ 0.4248` (was 0.4253), so `1 − s² ≤ 0.5752`
(`sg_node_lat`, `sg_alg_up5752`: `2·0.5752·2.08 ≤ 2.4`); `sg_num ≤ 7.5·10⁻⁷` with `D ≥ 54 999`
(was `7·10⁻⁷`), so the `ς` charge is `≤ 1.5·10⁻⁶` (was 1.4); `en_num55`: Markov ratios `0.3095`,
`0.3820`, `1.5·10⁻⁶ + 512·10²⁰(2·0.3095⁶⁴ + 0.3820⁶⁴) ≤ 10⁻⁴`; `fr_X_num` with `128q ≤ 0.035n`, the
factors `1.0024`, `2·1.035` (product `≤ 2.125`); `nd_numP` unchanged (`α ≤ 0.0018w²`,
`γ ≤ 0.00012w²`). The statistics charge `≤ 10⁻⁴` and the cap `n ≤ 10²⁰` are unchanged. End theorem
`classifier_paper_uncond55k`.
-/

namespace BstLean.Part174.N55

-- ===== from Part172SNode.lean =====
section SPart172SNode
open BstLean.Part172
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (windowW mkR)
variable {n : ℕ}
theorem sg_node_lat (hn : 55000 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
    (_hg : g < Js n) : 0 ≤ nodeS (mkR wr θ) g ∧ 4248 / 10000 ≤ nodeS (mkR wr θ) g ^ 2 := by
  obtain ⟨hτ, hθ0, hθ1⟩ := hw
  set c := mkR wr θ with hcd
  have hτ' : 0 < tauR c := hτ
  have hθ0' : 46 / 100 ≤ BstLean.Part150.thetaC c.1.2 (tauR c) := hθ0
  have hθ1' : BstLean.Part150.thetaC c.1.2 (tauR c) ≤ 55 / 100 := hθ1
  obtain ⟨hLH, -, -⟩ := bulk_of_window (by omega) c hτ' hθ0' hθ1'
  have hnR : (55000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set ρ := rhoR c with hρ
  have hρ2 : ρ ^ 2 = normSq c.1.2 + n * tauR c ^ 2 := by
    rw [hρ]; unfold rhoR BstLean.Part150.rhoC
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hρ0 : 0 < ρ := by
    rw [hρ]; unfold rhoR BstLean.Part150.rhoC
    exact Real.sqrt_pos.mpr (by have := normSq_nonneg c.1.2; positivity)
  set a := √(normSq c.1.2) / ρ with ha
  set b := tauR c / ρ with hb
  have hb0 : 0 < b := div_pos hτ' hρ0
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hθ : BstLean.Part150.thetaC c.1.2 (tauR c) = n * b ^ 2 := by
    unfold BstLean.Part150.thetaC; rw [← rhoR, ← hρ, hb, div_pow]; ring
  have hab : a ^ 2 + n * b ^ 2 = 1 := by
    rw [ha, hb, div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp; rw [hρ2]
  rw [hθ] at hθ0' hθ1'
  have hL : nodeL c = a - 6 * b := by unfold nodeL; rw [← hρ]; ring
  have ha2 : 45 / 100 ≤ a ^ 2 := by linarith
  have hb2 : b ^ 2 ≤ 55 / 100 / n := by rw [le_div_iff₀ hn0]; linarith
  have hb2' : b ^ 2 ≤ 55 / 100 / 55000 :=
    hb2.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hbs : b ≤ 3163 / 1000000 := by nlinarith
  have has : 6708 / 10000 ≤ a := by nlinarith
  have hD : 0 ≤ nodeD c := by
    unfold nodeD
    exact div_nonneg (by linarith) (by positivity)
  have hS : nodeL c ≤ nodeS c g := by
    unfold nodeS
    have : 0 ≤ ((g : ℝ) + 1 / 2) * nodeD c := mul_nonneg (by positivity) hD
    linarith
  rw [hL] at hS
  have h1 : 0 ≤ a - 6 * b := by linarith
  refine ⟨by linarith, ?_⟩
  have h2 : 65182 / 100000 ≤ a - 6 * b := by linarith
  nlinarith

end SPart172SNode

-- ===== from Part172Sig.lean =====
section SAlg
variable {n : ℕ}
/-- Part 172's `sg_alg_up` with `q ≤ 0.5752` (the latitude bound at `n ≥ 55 000`). -/
lemma sg_alg_up5752 {M D q Y m : ℝ} (hM : 0 < M) (hD : 0 < D) (hm : 0 < m) (hq0 : 0 ≤ q)
    (hq : q ≤ 5752 / 10000) (hY0 : 0 ≤ Y) (hY : Y ≤ 208 / 100 * M * D / m) :
    2 / M * (q / D) * Y ≤ 12 / (5 * m) := by
  have e : 2 / M * (q / D) * Y = 2 * q * Y / (M * D) := by field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [le_div_iff₀ hm] at hY
  nlinarith [mul_le_mul hq hY (by positivity) (by norm_num : (0 : ℝ) ≤ 5752 / 10000),
    mul_nonneg hq0 (mul_nonneg hY0 hm.le)]

/-- Part 172's `en_num` with the budget `10⁻⁴` and the ratios `0.3095`, `0.3820`. -/
lemma en_num55 {N : ℝ} (hN : N ≤ 10 ^ 20) (hN0 : 0 ≤ N) :
    15 / 10 ^ 7 + 512 * N * (2 * (3095 / 10000 : ℝ) ^ 64 + (3820 / 10000) ^ 64) ≤ 1 / 10000 := by
  have h : 512 * N * (2 * (3095 / 10000 : ℝ) ^ 64 + (3820 / 10000) ^ 64) ≤
      512 * 10 ^ 20 * (2 * (3095 / 10000 : ℝ) ^ 64 + (3820 / 10000) ^ 64) := by gcongr
  have h2 : 512 * 10 ^ 20 * (2 * (3095 / 10000 : ℝ) ^ 64 + (3820 / 10000) ^ 64) ≤
      98 / 1000000 := by
    norm_num
  linarith

end SAlg

section SPart172Sig
open BstLean.Part172
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS nodeL nodeH nodeD bulk_of_window qB qB_pos)
open BstLean.Part170 (windowW mkR)
open BstLean.Part171 (SminN)
variable {n : ℕ}
lemma sg_node_q (hn : 55000 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
    (hg : g < Js n) : 43 / 100 ≤ 1 - nodeS (mkR wr θ) g ^ 2 := by
  obtain ⟨hτ, hθ0, hθ1⟩ := hw
  obtain ⟨hLH, hb, -⟩ := bulk_of_window (by omega) (mkR wr θ) hτ hθ0 hθ1
  have hq := qB_pos hn
  have hJ : (0 : ℝ) < Js n := by exact_mod_cast (show 0 < Js n by unfold Js; omega)
  have hD : 0 ≤ nodeD (mkR wr θ) := div_nonneg (by linarith) hJ.le
  have hg' : (g : ℝ) + 1 / 2 ≤ Js n := by
    have : (g : ℝ) + 1 ≤ Js n := by exact_mod_cast hg
    linarith
  have h1 : nodeL (mkR wr θ) ≤ nodeS (mkR wr θ) g := by
    unfold nodeS; have : 0 ≤ ((g : ℝ) + 1 / 2) * nodeD (mkR wr θ) := by positivity
    linarith
  have h2 : nodeS (mkR wr θ) g ≤ nodeH (mkR wr θ) := by
    unfold nodeS
    have e : nodeH (mkR wr θ) = nodeL (mkR wr θ) + (Js n : ℝ) * nodeD (mkR wr θ) := by
      unfold nodeD; field_simp; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hg' hD
    linarith
  have := hb _ h1 h2
  linarith

lemma sg_num {m M D B k : ℝ} (hm : 55000 ≤ m) (hM : M = m ^ 2) (hD : D = m - 1)
    (hB : B ≤ m ^ 2 + 2 * m) (hk : 3 / 100 ≤ k) : M * B / (k * M * D) ^ 2 ≤ 75 / 10 ^ 8 := by
  have hD0 : 54999 ≤ D := by rw [hD]; linarith
  have hM0 : 0 < M := by rw [hM]; positivity
  have hk0 : 0 < k := by linarith
  rw [div_le_iff₀ (by positivity)]
  have h1 : M * B ≤ 2 * M ^ 2 := by
    rw [hM]
    have : m ^ 2 * B ≤ m ^ 2 * (m ^ 2 + 2 * m) := mul_le_mul_of_nonneg_left hB (by positivity)
    nlinarith
  have hk2 : 9 / 10000 ≤ k ^ 2 := by nlinarith
  have hD2 : 54999 ^ 2 ≤ D ^ 2 := by nlinarith
  have h2 : 2 ≤ 75 / 10 ^ 8 * (k ^ 2 * D ^ 2) := by nlinarith [mul_le_mul hk2 hD2 (by norm_num) (by positivity)]
  calc M * B ≤ 2 * M ^ 2 := h1
    _ ≤ 75 / 10 ^ 8 * (k ^ 2 * D ^ 2) * M ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 75 / 10 ^ 8 * (k * M * D) ^ 2 := by ring

/-- **The `ς` event and its charge.** -/
theorem sig_charge (hn : 55000 ≤ n) {wr : WRet n} (hw : windowW wr) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real {A₁ | ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < SminN n ∨
      12 / (5 * (n : ℝ)) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} ≤ 15 / 10 ^ 7 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (55000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hc : wr.2 ≠ 0 := sg_wr_ne hn1 hw
  set u : Fin n → ℝ := uHat (mkR wr ((0 : AHid n).1, 0)) with hud
  have hu : normSq u = 1 := BstLean.Part161.normSq_uHat (c := mkR wr ((0 : AHid n).1, 0)) hc
  set M : ℝ := ((mA n : ℕ) : ℝ) with hMd
  set D : ℝ := ((n - 1 : ℕ) : ℝ) with hDd
  have hMe : M = (n : ℝ) ^ 2 := by rw [hMd]; unfold mA; push_cast; ring
  have hDe : D = (n : ℝ) - 1 := by rw [hDd, Nat.cast_sub hn1]; simp
  have hM : 0 < M := by rw [hMe]; positivity
  have hD : 0 < D := by rw [hDe]; linarith
  -- the deterministic inclusion
  set T : Set (Matrix (Fin (mA n)) (Fin n) ℝ) := {A | ∑ i, sg_phi1 u (A i) < 94 / 100 * M * D / n ∨
    208 / 100 * M * D / n < ∑ i, sg_phi2 u (A i)} with hT
  have hsub : {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < SminN n ∨
      12 / (5 * (n : ℝ)) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} ⊆ T := by
    rintro A ⟨g, hg, hbad⟩
    set c := mkR wr (A, 0)
    have hc' : c.1.2 ≠ 0 := hc
    obtain ⟨hs0, hs2⟩ := sg_node_lat hn hw (A, 0) hg
    have hq := sg_node_q hn hw (A, 0) hg
    set s := nodeS c g
    have hs1 : s ^ 2 ≤ 1 := by linarith
    have hL := sg_vsig2_lower (by omega) c hc' hs0 hs1
    have hU := sg_vsig2_upper (by omega) c hc' hs1
    have e1 : ∑ i, (if 0 ≤ sg_z (uHat c) (A1 c i) then
        normSq (A1 c i) - sg_z (uHat c) (A1 c i) ^ 2 else 0) = ∑ i, sg_phi1 u (A i) := rfl
    have e2 : ∑ i, (normSq (A1 c i) - sg_z (uHat c) (A1 c i) ^ 2) = ∑ i, sg_phi2 u (A i) := rfl
    rw [e1] at hL; rw [e2] at hU
    rcases hbad with h | h
    · left
      by_contra hX
      push_neg at hX
      have := sg_alg_low hM hD hn0 hq hX
      unfold SminN at h
      linarith
    · right
      by_contra hY
      push_neg at hY
      have hY0 : 0 ≤ ∑ i, sg_phi2 u (A i) := Finset.sum_nonneg fun i _ => sg_phi2_nonneg hu _
      have := sg_alg_up5752 (q := 1 - s ^ 2) hM hD hn0 (by linarith) (by linarith) hY0 hY
      linarith
  have hTm : MeasurableSet T := by
    have h1 : Measurable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => ∑ i, sg_phi1 u (A i)) :=
      Finset.measurable_sum _ fun i _ => (sg_meas_phi1 u).comp (measurable_pi_apply i)
    have h2 : Measurable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => ∑ i, sg_phi2 u (A i)) :=
      Finset.measurable_sum _ fun i _ => (sg_meas_phi2 u).comp (measurable_pi_apply i)
    exact (measurableSet_lt h1 measurable_const).union (measurableSet_lt measurable_const h2)
  set μ := Measure.pi fun _ : Fin (mA n) => stdGauss (Fin n) with hμ
  set γ : ℝ := 2 / (n : ℝ) with hγ
  have hγ0 : 0 < γ := by positivity
  have hsγ : 0 < √γ := Real.sqrt_pos.mpr hγ0
  have hsγ2 : √γ ^ 2 = γ := Real.sq_sqrt hγ0.le
  set f : (Fin (mA n) → Fin n → ℝ) → Matrix (Fin (mA n)) (Fin n) ℝ :=
    fun G => Matrix.of fun i j => √γ * G i j with hfd
  have hf : Measurable f := by
    have hc : Continuous (fun G : Fin (mA n) → Fin n → ℝ => fun i j => √γ * G i j) := by fun_prop
    exact hc.measurable
  have hG : gaussMat (mA n) n γ = μ.map f := BstLean.Part167.gaussMat_rows γ
  have hrow : ∀ G i, f G i = √γ • G i := fun G i => by funext j; rfl
  obtain ⟨-, i1sq, b1⟩ := sg_int_bdd (sg_meas_phi1 u) (sg_phi1_nonneg hu) (sg_phi1_le hu)
  obtain ⟨-, i2sq, b2⟩ := sg_int_bdd (sg_meas_phi2 u) (sg_phi2_nonneg hu) (sg_phi2_le u)
  have hE1 := sg_int_phi1 hu
  have hE2 := (sg_int_phi2 hu).2
  set t₁ : ℝ := 3 / 100 * M * D
  set t₂ : ℝ := 4 / 100 * M * D
  have ht₁ : 0 < t₁ := by positivity
  have ht₂ : 0 < t₂ := by positivity
  have hpre : f ⁻¹' T ⊆ {G | t₁ ≤ |∑ i, sg_phi1 u (G i) - (mA n : ℕ) * ∫ g, sg_phi1 u g ∂stdGauss (Fin n)|} ∪
      {G | t₂ ≤ |∑ i, sg_phi2 u (G i) - (mA n : ℕ) * ∫ g, sg_phi2 u g ∂stdGauss (Fin n)|} := by
    intro G hGT
    simp only [Set.mem_preimage, hT, Set.mem_setOf_eq, hrow] at hGT
    simp_rw [sg_phi1_smul hsγ, sg_phi2_smul, hsγ2, ← Finset.mul_sum] at hGT
    rcases hGT with h | h
    · left
      simp only [Set.mem_setOf_eq]
      have hS : ∑ i, sg_phi1 u (G i) < 47 / 100 * M * D := by
        rw [hγ] at h
        have e : 94 / 100 * M * D / n = 2 / n * (47 / 100 * M * D) := by field_simp; ring
        rw [e] at h
        exact lt_of_mul_lt_mul_left h (by positivity)
      have hm : M * (D / 2) ≤ M * ∫ g, sg_phi1 u g ∂stdGauss (Fin n) :=
        mul_le_mul_of_nonneg_left (by rw [hDe]; exact hE1) hM.le
      rw [abs_sub_comm]
      refine le_trans ?_ (le_abs_self _)
      show t₁ ≤ M * ∫ g, sg_phi1 u g ∂stdGauss (Fin n) - ∑ i, sg_phi1 u (G i)
      have et : t₁ = 3 / 100 * M * D := rfl
      have e2 : M * (D / 2) = 50 / 100 * M * D := by ring
      linarith
    · right
      simp only [Set.mem_setOf_eq]
      have hS : 104 / 100 * M * D < ∑ i, sg_phi2 u (G i) := by
        rw [hγ] at h
        have e : 208 / 100 * M * D / n = 2 / n * (104 / 100 * M * D) := by field_simp; ring
        rw [e] at h
        exact lt_of_mul_lt_mul_left h (by positivity)
      refine le_trans ?_ (le_abs_self _)
      show t₂ ≤ ∑ i, sg_phi2 u (G i) - M * ∫ g, sg_phi2 u g ∂stdGauss (Fin n)
      rw [hE2, ← hDe]
      have et : t₂ = 4 / 100 * M * D := rfl
      linarith
  have hc1 := sg_cheb (m := mA n) (sg_meas_phi1 u) i1sq ht₁
  have hc2 := sg_cheb (m := mA n) (sg_meas_phi2 u) i2sq ht₂
  have hn1' := sg_num hnR hMe hDe b1 (k := 3 / 100) le_rfl
  have hn2' := sg_num hnR hMe hDe b2 (k := 4 / 100) (by norm_num)
  have hEμ : gaussMat (mA n) n γ {A₁ | ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < SminN n ∨
      12 / (5 * (n : ℝ)) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} ≤
      ENNReal.ofReal (15 / 10 ^ 7) := by
    refine (measure_mono hsub).trans ?_
    rw [hG, Measure.map_apply hf hTm]
    refine (measure_mono hpre).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add hc1 hc2).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : ((mA n : ℕ) : ℝ) * (∫ g, sg_phi1 u g ^ 2 ∂stdGauss (Fin n)) / t₁ ^ 2 =
        M * (∫ g, sg_phi1 u g ^ 2 ∂stdGauss (Fin n)) / (3 / 100 * M * D) ^ 2 := rfl
    have e2 : ((mA n : ℕ) : ℝ) * (∫ g, sg_phi2 u g ^ 2 ∂stdGauss (Fin n)) / t₂ ^ 2 =
        M * (∫ g, sg_phi2 u g ^ 2 ∂stdGauss (Fin n)) / (4 / 100 * M * D) ^ 2 := rfl
    rw [e1, e2]
    linarith
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hEμ

/-- `sig_charge` with the operator event inside the set (a subset). -/
theorem sig_charge_op (hn : 55000 ≤ n) {wr : WRet n} (hw : windowW wr) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real {A₁ | BstLean.Part169.OpB A₁ (BstLean.Part169.O1n n) ∧
      ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < SminN n ∨
      12 / (5 * (n : ℝ)) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} ≤ 15 / 10 ^ 7 :=
  (measureReal_mono fun _ h => h.2).trans (sig_charge hn hw)

end SPart172Sig

-- ===== from Part172FNum.lean =====
section SPart172FNum
open BstLean.Part172
open Real BstLean.Part130 BstLean.Part168
variable {n : ℕ}
/-- `m^{1/(64q)} ≤ 1.0235` for `q = ⌊log₂ n⌋`. -/
lemma fr_rpow_m (hn : 55000 ≤ n) :
    ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (qn n : ℝ))) ≤ 10235 / 10000 := by
  set q := qn n with hq
  have hq16 : (15 : ℝ) ≤ q := by exact_mod_cast q_ge hn
  have hq0 : (0 : ℝ) < q := by linarith
  have hm : ((mA n : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((2 * q + 2 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    have h := lt_pow_q n
    have h2 : mA n ≤ 2 ^ (2 * q + 2) := by
      unfold mA
      rw [show 2 * q + 2 = (q + 1) * 2 by ring, pow_mul]
      exact Nat.pow_le_pow_left h.le 2
    exact_mod_cast h2
  have h1 := Real.rpow_le_rpow (Nat.cast_nonneg _) hm
    (by positivity : (0 : ℝ) ≤ 1 / (64 * (q : ℝ)))
  rw [← Real.rpow_mul (by norm_num)] at h1
  refine h1.trans ?_
  have hexp : ((2 * q + 2 : ℕ) : ℝ) * (1 / (64 * (q : ℝ))) ≤ 1 / 30 := by
    push_cast
    rw [show (2 * (q : ℝ) + 2) * (1 / (64 * (q : ℝ))) = (2 * q + 2) / (64 * q) by ring,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp).trans ?_
  have h30 : (2 : ℝ) ≤ (10235 / 10000) ^ 30 := by norm_num
  calc (2 : ℝ) ^ ((1 : ℝ) / 30) ≤ ((10235 / 10000 : ℝ) ^ 30) ^ ((1 : ℝ) / 30) :=
        Real.rpow_le_rpow (by norm_num) h30 (by norm_num)
    _ = 10235 / 10000 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

/-- **`X ≤ 4.25/n²`** for `q = ⌊log₂ n⌋`, `B = t_A`, every `n ≥ 55 000`. -/
theorem fr_X_num (hn : 55000 ≤ n) :
    fr_X n (qn n) (2 / ((mA n : ℕ) : ℝ)) ≤ 425 / 100 / (n : ℝ) ^ 2 := by
  set q := qn n with hq
  have hnR : (55000 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : ((n - 1 - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [show n - 1 - 1 = n - 2 by omega]; push_cast [show 2 ≤ n by omega]; ring
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hqn : (128 : ℝ) * q ≤ 35 / 1000 * n := q_lin55 hn
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hR := fr_rpow_m hn
  have hR0 : 0 ≤ ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (q : ℝ))) := Real.rpow_nonneg (by positivity) _
  have f1 : (((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1) ≤ 10024 / 10000 := by
    rw [hd, div_le_iff₀ (by linarith)]; linarith
  have f1' : 0 ≤ (((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1) := by
    rw [hd]; apply div_nonneg <;> linarith
  have f3 : (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) * (2 / (n : ℝ)) ≤ 2 * (1035 / 1000) := by
    rw [hd, mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  have f3' : 0 ≤ (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) * (2 / (n : ℝ)) := by
    rw [hd]; apply mul_nonneg <;> [nlinarith; positivity]
  have e : fr_X n q (2 / ((mA n : ℕ) : ℝ)) =
      ((((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1)) *
      ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (q : ℝ))) *
      ((((n - 1 - 1 : ℕ) : ℝ) + 128 * q) * (2 / (n : ℝ))) * (2 / (n : ℝ) ^ 2) := by
    unfold fr_X; rw [hmR]; ring
  rw [e]
  have hn2 : (0 : ℝ) < 2 / (n : ℝ) ^ 2 := by positivity
  have h := mul_le_mul (mul_le_mul (mul_le_mul f1 hR hR0 (by norm_num)) f3 f3' (by norm_num))
    (le_refl (2 / (n : ℝ) ^ 2)) hn2.le (by norm_num)
  refine h.trans (le_of_eq_of_le rfl ?_)
  rw [show 425 / 100 / (n : ℝ) ^ 2 = 425 / 200 * (2 / (n : ℝ) ^ 2) by ring]
  exact mul_le_mul_of_nonneg_right (by norm_num) hn2.le

end SPart172FNum

-- ===== from Part172Frm.lean =====
section SPart172Frm
open BstLean.Part172
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part151 (mask)
open BstLean.Part161 (uHat xLat)
open BstLean.Part162 (dirW)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part167 (latSq D1A1 Aframe eprime gaussMat_frame frame_reads latSq_vecMul_frame)
variable {n : ℕ}
/-- **The frame moment with the numbers**: for every `n ≥ 55 000` and an admissible direction
with `|e|² ≤ t_A`, `E_{A₁} latSq((D₁A₁)ᵀe)^{64} ≤ (4.25/n²)^{64}`. -/
theorem frame_mom_num (hn : 55000 ≤ n) {c : Ret n} (hc : c.1.2 ≠ 0) {s : ℝ}
    (hs : s ^ 2 ≤ 1) {v : Fin (n - 1) → ℝ} (hv : v ≠ 0)
    (e : Matrix (Fin (mA n)) (Fin n) ℝ → Fin (mA n) → ℝ)
    (hadm : ∀ A A' : Matrix (Fin (mA n)) (Fin n) ℝ, A *ᵥ xLat c s (unitF53 v) =
      A' *ᵥ xLat c s (unitF53 v) → A *ᵥ uHat c = A' *ᵥ uHat c →
      (∀ i, ∑ j, A i j ^ 2 = ∑ j, A' i j ^ 2) → e A = e A')
    (hB : ∀ A, normSq (e A) ≤ BstLean.Part170.tA n) :
    ∫⁻ A₁, ENNReal.ofReal (latSq (vecMul (e A₁) (D1A1 A₁ (xLat c s (unitF53 v)))) (uHat c)
        (dirW c (unitF53 v)) ^ 64) ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal ((425 / 100 / (n : ℝ) ^ 2) ^ 64) := by
  have hq : 1 ≤ BstLean.Part168.qn n := by have := q_ge hn; omega
  have htA : (0 : ℝ) ≤ BstLean.Part170.tA n := BstLean.Part171.tA_nonneg n
  refine (frame_mom (by omega) hq hc hs hv e hadm htA hB).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [fr_X_pow hq]
  have hX0 : 0 ≤ fr_X n (BstLean.Part168.qn n) (BstLean.Part170.tA n) := by
    have hd : (2 : ℝ) ≤ ((n - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 1 - 1 by omega)
    unfold fr_X
    refine mul_nonneg (mul_nonneg ?_ (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_))
      (mul_nonneg (by positivity) htA)
    · apply div_nonneg <;> linarith
    · positivity
  exact pow_le_pow_left₀ hX0 (fr_X_num hn) 64

end SPart172Frm

-- ===== from Part172Mk.lean =====
section SPart172Mk
open BstLean.Part172
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (xLat uHat)
open BstLean.Part162 (dirW)
open BstLean.Part167 (latSq D1A1)
open BstLean.Part170 (tA)
open BstLean.Part53 (unitF53)
variable {n : ℕ}
/-- **Markov of order 64 for a tangential statistic.** -/
theorem mk_markov (hn : 55000 ≤ n) {c₀ : Ret n} (hc : c₀.1.2 ≠ 0) {s : ℝ} (hs : s ^ 2 ≤ 1)
    (F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ)
    (hF : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2))
    (hadm : ∀ v, BstLean.Part172.fr_Adm (xLat c₀ s (unitF53 v)) (uHat c₀) (fun A => F A v))
    (hB : ∀ A v, normSq (F A v) ≤ tA n) {K : ℝ} (hK : 0 < K) :
    gaussMat (mA n) n (2 / (n : ℝ))
        {A | K ^ 64 < ∫ v, |Tf c₀ s F A v| ^ 64 ∂stdGauss (Fin (n - 1))} ≤
      ENNReal.ofReal (((1 - s ^ 2) * (425 / 100 / (n : ℝ) ^ 2)) ^ 64) / ENNReal.ofReal (K ^ 64) := by
  have hn1 : 1 ≤ n := by omega
  set μA := gaussMat (mA n) n (2 / (n : ℝ))
  have hT := mk_meas_Tf c₀ s hF
  set f : Matrix (Fin (mA n)) (Fin n) ℝ → ℝ≥0∞ :=
    fun A => ∫⁻ v, ENNReal.ofReal (|Tf c₀ s F A v| ^ 64) ∂stdGauss (Fin (n - 1)) with hf
  have hG : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      ENNReal.ofReal (|Tf c₀ s F p.1 p.2| ^ 64)) :=
    ENNReal.measurable_ofReal.comp (hT.abs.pow_const 64)
  have hfm : Measurable f := hG.lintegral_prod_right'
  have hsub : {A | K ^ 64 < ∫ v, |Tf c₀ s F A v| ^ 64 ∂stdGauss (Fin (n - 1))} ⊆
      {A | ENNReal.ofReal (K ^ 64) ≤ f A} := by
    intro A hA
    simp only [mem_setOf_eq] at hA ⊢
    have hi : Integrable (fun v => |Tf c₀ s F A v| ^ 64) (stdGauss (Fin (n - 1))) := by
      refine mo_bdd_pow (μ := stdGauss (Fin (n - 1)))
        ((hT.comp (measurable_const.prodMk measurable_id)).abs) (C := |1 - s ^ 2| *
          (tA n * (∑ i, ∑ l, A i l ^ 2) * 3)) (fun v => ?_) 64
      rw [abs_abs]; exact mk_bdd hn1 hc s F hB A v
    rw [hf]
    simp only
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun v => by positivity)]
    exact ENNReal.ofReal_le_ofReal hA.le
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div hfm.aemeasurable (by simp; positivity) ENNReal.ofReal_ne_top).trans ?_
  gcongr
  -- Tonelli and the frame moment
  rw [hf, lintegral_lintegral_swap hG.aemeasurable]
  have hnz : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
    have h0 : stdGauss (Fin (n - 1)) {(0 : Fin (n - 1) → ℝ)} = 0 :=
      BstLean.Part168.stdGauss_zero (by omega)
    rw [ae_iff]; simpa using h0
  have h1s : 0 ≤ 1 - s ^ 2 := by linarith
  calc ∫⁻ v, ∫⁻ A, ENNReal.ofReal (|Tf c₀ s F A v| ^ 64) ∂μA ∂stdGauss (Fin (n - 1)) ≤
      ∫⁻ _v, ENNReal.ofReal (((1 - s ^ 2) * (425 / 100 / (n : ℝ) ^ 2)) ^ 64)
        ∂stdGauss (Fin (n - 1)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hnz] with v hv
        have e : ∀ A, ENNReal.ofReal (|Tf c₀ s F A v| ^ 64) = ENNReal.ofReal ((1 - s ^ 2) ^ 64) *
            ENNReal.ofReal (latSq (vecMul (F A v) (D1A1 A (xLat c₀ s (unitF53 v)))) (uHat c₀)
              (dirW c₀ (unitF53 v)) ^ 64) := by
          intro A
          have e1 : |Tf c₀ s F A v| ^ 64 = (1 - s ^ 2) ^ 64 * latSq (vecMul (F A v)
              (D1A1 A (xLat c₀ s (unitF53 v)))) (uHat c₀) (dirW c₀ (unitF53 v)) ^ 64 := by
            rw [Even.pow_abs ⟨32, by norm_num⟩]
            simp only [Tf]
            rw [mul_pow]
          rw [e1, ENNReal.ofReal_mul (pow_nonneg h1s 64)]
        simp_rw [e]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have hM := frame_mom_num hn hc hs hv (fun A => F A v) (hadm v) (fun A => hB A v)
        calc ENNReal.ofReal ((1 - s ^ 2) ^ 64) * ∫⁻ A, ENNReal.ofReal (latSq (vecMul (F A v)
              (D1A1 A (xLat c₀ s (unitF53 v)))) (uHat c₀) (dirW c₀ (unitF53 v)) ^ 64) ∂μA ≤
            ENNReal.ofReal ((1 - s ^ 2) ^ 64) * ENNReal.ofReal ((425 / 100 / (n : ℝ) ^ 2) ^ 64) :=
              by gcongr
          _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), mul_pow]
    _ = _ := by simp

end SPart172Mk

-- ===== from Part172Node.lean =====
section SPart172Node
open BstLean.Part172
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part134 (res)
open BstLean.Part161 (xLat momN)
open BstLean.Part162 (tanSq cLS cLS_pos ls_lat ls_lat_mom_sharp xLatH)
open BstLean.Part170 (hB tA aLat)
open BstLean.Part53 (unitF53)
variable {n : ℕ}
section
variable (c : Ret n) (g : ℕ)
/-- The centred moments of `S` from LS, order `2q`. -/
lemma nd_mom (hn : 55000 ≤ n) (hs : nodeS c g ^ 2 ≤ 1) (h1 : OpB (A1 c) (O1n n)) {q : ℕ}
    (hq : 1 ≤ q) (hqn : 2 * q < n - 1) {K : ℝ} (hK : 0 ≤ K)
    (hT : ∫ v, |√(tanSq (SN c g) c (nodeS c g) v)| ^ (2 * q) ∂stdGauss (Fin (n - 1)) ≤ K ^ q) :
    ∫ v, (√(wT c g v) - ∫ w, √(wT c g w) ∂stdGauss (Fin (n - 1))) ^ (2 * q)
      ∂stdGauss (Fin (n - 1)) ≤ cLS q ^ (2 * q) * K ^ q * (((n : ℝ) - 1 - 2 * q)⁻¹) ^ q := by
  have hn2 : 2 ≤ n := by omega
  have hO : 0 ≤ O1n n := O1n_nonneg n
  have hL := S_lip (tA n) (hB c) (res (hB c) (a1Bar c (nodeS c g))) hO h1
  have hhom := S_hom (n := n) (tA n) (hB c) (res (hB c) (a1Bar c (nodeS c g))) (A1 c)
  have H := ls_lat_mom_sharp hn2 c hs (by positivity) hL (fun k y hk => hhom k y hk) hq hqn
  have hsq : momN (stdGauss (Fin (n - 1))) (2 * q)
      (fun v => √(BstLean.Part151.gradSq (fun w => SN c g (xLatH c (nodeS c g) w)) v -
        SN c g (xLat c (nodeS c g) (unitF53 v)) ^ 2)) ≤ √K := by
    refine nd_momN_le_of_int (by omega) (Real.sqrt_nonneg _) ?_
    rw [pow_mul, Real.sq_sqrt hK]
    exact hT
  have hn' : (0 : ℝ) < (n : ℝ) - 1 - 2 * q := by
    have : ((2 * q : ℕ) : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hqn
    push_cast at this
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this; linarith
  have ha0 : 0 ≤ (((n : ℝ) - 1 - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
  have H2 : momN (stdGauss (Fin (n - 1))) (2 * q)
      (fun v => SN c g (xLat c (nodeS c g) (unitF53 v)) -
        ∫ w, SN c g (xLat c (nodeS c g) (unitF53 w)) ∂stdGauss (Fin (n - 1))) ≤
      cLS q * (√K * (((n : ℝ) - 1 - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹)) := by
    refine H.trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq ha0) (cLS_pos hq).le
  have H3 := nd_int_le_of_momN (by omega) (by
    have := (cLS_pos hq).le; positivity) H2
  simp_rw [SN_eq] at H3
  have e1 : ∀ v, (√(wT c g v) - ∫ w, √(wT c g w) ∂stdGauss (Fin (n - 1))) ^ (2 * q) =
      |√(wT c g v) - ∫ w, √(wT c g w) ∂stdGauss (Fin (n - 1))| ^ (2 * q) := fun v => by
    rw [pow_mul, pow_mul, sq_abs]
  simp_rw [e1]
  refine H3.trans (le_of_eq ?_)
  have hrr : ((((n : ℝ) - 1 - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹)) ^ 2 = ((n : ℝ) - 1 - 2 * q)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have e2 : (√K) ^ (2 * q) = K ^ q := by rw [pow_mul, Real.sq_sqrt hK]
  have e3 : ((((n : ℝ) - 1 - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹)) ^ (2 * q) = (((n : ℝ) - 1 - 2 * q)⁻¹) ^ q := by
    rw [pow_mul, hrr]
  rw [mul_pow, mul_pow, e2, e3]
  ring

/-- The variance of `S` from LS (`p = 1`). -/
lemma nd_var (hn : 55000 ≤ n) (hs : nodeS c g ^ 2 ≤ 1) (h1 : OpB (A1 c) (O1n n)) {K : ℝ}
    (hT : ∫ v, tanSq (SN c g) c (nodeS c g) v ∂stdGauss (Fin (n - 1)) ≤ K) :
    ∫ v, (√(wT c g v) - ∫ w, √(wT c g w) ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1)) ≤ K / ((n : ℝ) - 2) := by
  have hn2 : 2 ≤ n := by omega
  have hO : 0 ≤ O1n n := O1n_nonneg n
  have hL := S_lip (tA n) (hB c) (res (hB c) (a1Bar c (nodeS c g))) hO h1
  have hhom := S_hom (n := n) (tA n) (hB c) (res (hB c) (a1Bar c (nodeS c g))) (A1 c)
  have H := ls_lat (Φ := SN c g) hn2 c hs (by positivity) hL (fun k y hk => hhom k y hk)
  have hT' : ∫ v, (BstLean.Part151.gradSq (fun w => SN c g (xLatH c (nodeS c g) w)) v -
      SN c g (xLat c (nodeS c g) (unitF53 v)) ^ 2) ∂stdGauss (Fin (n - 1)) ≤ K := hT
  have H' := H.trans hT'
  simp_rw [SN_eq] at H'
  have hn0 : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (55000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [le_div_iff₀ hn0, mul_comm]
  exact H'

end
lemma nd_numV {N x b D : ℝ} (hN : 55000 ≤ N) (hx0 : 0 ≤ x)
    (hx : x ≤ 42742 / 10000 * (32 / (5 * N ^ 2)) / (N - 5)) (hb0 : 0 ≤ b)
    (hb : b ^ 2 ≤ 4 * (12 / (5 * N)) * (32 / (5 * N ^ 2)) / (N - 2)) (hD0 : 0 ≤ D)
    (hD : D ≤ 16 / N ^ 3) :
    (x + b) ^ 2 + D ^ 2 ≤ 64 / N ^ 4 := by
  have hN0 : 0 < N := by linarith
  set w := 1 / N ^ 2 with hw
  have hw0 : 0 < w := by positivity
  have e64 : 64 / N ^ 4 = 64 * w ^ 2 := by rw [hw]; field_simp
  have hx' : x ≤ 1 / 1000 * w := by
    refine hx.trans ?_
    rw [hw, div_le_iff₀ (by linarith)]
    field_simp
    nlinarith
  have hb' : b ^ 2 ≤ 6145 / 100 * w ^ 2 := by
    refine hb.trans ?_
    rw [hw, div_le_iff₀ (by linarith)]
    field_simp
    nlinarith
  have hD' : D ≤ 1 / 1000 * w := by
    refine hD.trans ?_
    rw [hw, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hb8 : b ≤ 8 * w := by
    by_contra hcon
    have := not_le.mp hcon
    nlinarith
  rw [e64]
  nlinarith [mul_le_mul hx' hb8 hb0 (by positivity), mul_le_mul hx' hx' hx0 (by positivity),
    mul_le_mul hD' hD' hD0 (by positivity)]

lemma nd_numP {N α β γ den : ℝ} (hN : 55000 ≤ N) (hα0 : 0 ≤ α)
    (hα : α ≤ 1519 / 100 * (32 / (5 * N ^ 2)) / (N - 17)) (hβ0 : 0 ≤ β)
    (hβ : β ^ 2 ≤ 4 * (12 / (5 * N)) * (7905 / 1000) * (32 / (5 * N ^ 2)) / (N - 9))
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ 32 / (5 * N ^ 2) / (N - 2)) (hden : 1 / (10 * N) - 16 / N ^ 3 ≤ den) :
    (α + β + γ) ^ 8 / den ^ 8 ≤ 1 / N ^ 4 := by
  have hN0 : 0 < N := by linarith
  set w := 1 / N with hw
  have hw0 : 0 < w := by positivity
  have hw1 : w ≤ 1 / 55000 := by rw [hw]; exact one_div_le_one_div_of_le (by norm_num) hN
  have hα' : α ≤ 18 / 10000 * w ^ 2 := by
    refine hα.trans ?_
    rw [hw, div_le_iff₀ (by linarith)]
    field_simp
    nlinarith
  have hγ' : γ ≤ 12 / 100000 * w ^ 2 := by
    refine hγ.trans ?_
    rw [hw, div_le_iff₀ (by linarith)]
    field_simp
    nlinarith
  have hβ' : β ^ 2 ≤ 4858 / 10 * w ^ 4 := by
    refine hβ.trans ?_
    rw [hw, div_le_iff₀ (by linarith)]
    field_simp
    nlinarith
  have hβ2 : β ≤ 2205 / 100 * w ^ 2 := by
    by_contra hcon
    have := not_le.mp hcon
    nlinarith
  have hden' : 998 / 10000 * w ≤ den := by
    refine le_trans ?_ hden
    rw [hw]
    rw [show 1 / (10 * N) - 16 / N ^ 3 = (N ^ 2 - 160) / (10 * N ^ 3) by field_simp; ring]
    rw [show 998 / 10000 * (1 / N) = 998 / (10000 * N) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hd0 : 0 < den := lt_of_lt_of_le (by positivity) hden'
  have hsum : α + β + γ ≤ 22064 / 1000 * w ^ 2 := by linarith
  have hs0 : 0 ≤ α + β + γ := by positivity
  have hsq : (α + β + γ) ^ 2 ≤ den ^ 2 * w := by
    have h1 : (α + β + γ) ^ 2 ≤ (22064 / 1000 * w ^ 2) ^ 2 := pow_le_pow_left₀ hs0 hsum 2
    have h2 : (998 / 10000 * w) ^ 2 ≤ den ^ 2 := pow_le_pow_left₀ (by positivity) hden' 2
    have h3 : (22064 / 1000 * w ^ 2) ^ 2 ≤ (998 / 10000 * w) ^ 2 * w := by
      have : w ^ 3 * (w * (22064 / 1000) ^ 2) ≤ w ^ 3 * ((998 / 10000) ^ 2) := by
        gcongr; nlinarith
      nlinarith
    nlinarith
  have h8 : (α + β + γ) ^ 8 ≤ den ^ 8 * w ^ 4 := by
    have := pow_le_pow_left₀ (by positivity) hsq 4
    calc (α + β + γ) ^ 8 = ((α + β + γ) ^ 2) ^ 4 := by ring
      _ ≤ (den ^ 2 * w) ^ 4 := this
      _ = den ^ 8 * w ^ 4 := by ring
  rw [div_le_iff₀ (by positivity)]
  calc (α + β + γ) ^ 8 ≤ den ^ 8 * w ^ 4 := h8
    _ = 1 / N ^ 4 * den ^ 8 := by rw [hw]; ring

section
variable (c : Ret n) (g : ℕ)
lemma nd_mu (hn : 55000 ≤ n) (hs : nodeS c g ^ 2 ≤ 1) (h1 : OpB (A1 c) (O1n n))
    (hσu : vsig2 c (nodeS c g) ≤ 12 / (5 * (n : ℝ))) :
    (∫ v, √(wT c g v) ∂stdGauss (Fin (n - 1))) ^ 2 ≤ 12 / (5 * (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have h := mo_sq_int_le (μ := stdGauss (Fin (n - 1))) (measurable_wT c g).sqrt
    (nd_S_bdd c g hn1 hs h1)
  have e : ∫ v, √(wT c g v) ^ 2 ∂stdGauss (Fin (n - 1)) = ∫ v, wT c g v ∂stdGauss (Fin (n - 1)) :=
    integral_congr_ae (ae_of_all _ fun v => Real.sq_sqrt (wT_nonneg c g v))
  rw [e, int_wT_eq hn1 c g hs (O1n_nonneg n) h1] at h
  linarith [DstN_nonneg c g]

/-- **`V2N ≤ 64/n⁴`** from the tangential statistics of `S` (paper `t7:p08:statistics`,
line 2). -/
theorem V2N_of_tan (hn : 55000 ≤ n) (hs : nodeS c g ^ 2 ≤ 1) (h1 : OpB (A1 c) (O1n n))
    (hσu : vsig2 c (nodeS c g) ≤ 12 / (5 * (n : ℝ))) (hDst : DstN c g ≤ DmN n)
    (hT1 : ∫ v, tanSq (SN c g) c (nodeS c g) v ∂stdGauss (Fin (n - 1)) ≤ K3N n)
    (hT2 : ∫ v, |√(tanSq (SN c g) c (nodeS c g) v)| ^ (2 * 2) ∂stdGauss (Fin (n - 1)) ≤
      K3N n ^ 2) :
    V2N c g ≤ VmN n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (55000 : ℝ) ≤ n := by exact_mod_cast hn
  have hK : 0 ≤ K3N n := by unfold K3N; positivity
  have h4 := nd_mom c g hn hs h1 (q := 2) (by norm_num) (by omega) hK hT2
  have h2 := nd_var c g hn hs h1 hT1
  have hμ := nd_mu c g hn hs h1 hσu
  set μ0 := ∫ v, √(wT c g v) ∂stdGauss (Fin (n - 1))
  set x := cLS 2 ^ 2 * K3N n * ((n : ℝ) - 5)⁻¹ with hx
  set y := √(K3N n / ((n : ℝ) - 2)) with hy
  have hn5 : (0 : ℝ) < (n : ℝ) - 5 := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have h4' : ∫ v, (√(wT c g v) - μ0) ^ 4 ∂stdGauss (Fin (n - 1)) ≤ x ^ 2 := by
    refine h4.trans (le_of_eq ?_)
    rw [hx]; push_cast; ring_nf
  have h2' : ∫ v, (√(wT c g v) - μ0) ^ 2 ∂stdGauss (Fin (n - 1)) ≤ y ^ 2 := by
    rw [hy, Real.sq_sqrt (by positivity)]; exact h2
  have HV := mo_var_sq (μ := stdGauss (Fin (n - 1))) (measurable_wT c g).sqrt
    (nd_S_bdd c g hn1 hs h1) hx0 (Real.sqrt_nonneg _) h4' h2'
  rw [V2N_eq hn1 c g hs (O1n_nonneg n) h1, nd_wT_S c g hn1 hs h1]
  refine (add_le_add HV le_rfl).trans ?_
  unfold VmN
  have hc2 : cLS 2 ^ 2 ≤ 42742 / 10000 := by
    have := cLS2_le; have h0 := (cLS_pos (q := 2) (by norm_num)).le; nlinarith
  refine nd_numV hnR hx0 ?_ (by positivity) ?_ (DstN_nonneg c g) hDst
  · rw [hx, ← div_eq_mul_inv]
    unfold K3N
    gcongr
  · rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), sq_abs]
    change 2 ^ 2 * μ0 ^ 2 * (K3N n / ((n : ℝ) - 2)) ≤ _
    unfold K3N
    have : (2 : ℝ) ^ 2 * μ0 ^ 2 ≤ 4 * (12 / (5 * n)) := by nlinarith
    calc 2 ^ 2 * μ0 ^ 2 * (32 / (5 * (n : ℝ) ^ 2) / ((n : ℝ) - 2)) ≤
        4 * (12 / (5 * n)) * (32 / (5 * (n : ℝ) ^ 2) / ((n : ℝ) - 2)) := by gcongr
      _ = _ := by ring

/-- **`piN ≤ 1/n⁴`** from the tangential statistics of `S` (paper `t7:p08:statistics`, line 3,
and Markov of order eight). -/
theorem piN_of_tan (hn : 55000 ≤ n) (hs : nodeS c g ^ 2 ≤ 1) (h1 : OpB (A1 c) (O1n n))
    (hσl : SminN n ≤ vsig2 c (nodeS c g)) (hσu : vsig2 c (nodeS c g) ≤ 12 / (5 * (n : ℝ)))
    (hDst : DstN c g ≤ DmN n)
    (hT1 : ∫ v, tanSq (SN c g) c (nodeS c g) v ∂stdGauss (Fin (n - 1)) ≤ K3N n)
    (hT4 : ∫ v, |√(tanSq (SN c g) c (nodeS c g) v)| ^ (2 * 4) ∂stdGauss (Fin (n - 1)) ≤
      K3N n ^ 4)
    (hT8 : ∫ v, |√(tanSq (SN c g) c (nodeS c g) v)| ^ (2 * 8) ∂stdGauss (Fin (n - 1)) ≤
      K3N n ^ 8) :
    piN c g ≤ PmN n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (55000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hK : 0 ≤ K3N n := by unfold K3N; positivity
  have hK0 : 0 < K3N n := by unfold K3N; positivity
  have hm8 := nd_mom c g hn hs h1 (q := 8) (by norm_num) (by omega) hK hT8
  have hm4 := nd_mom c g hn hs h1 (q := 4) (by norm_num) (by omega) hK hT4
  have h2 := nd_var c g hn hs h1 hT1
  have hμ := nd_mu c g hn hs h1 hσu
  set μ0 := ∫ v, √(wT c g v) ∂stdGauss (Fin (n - 1))
  have hDlt : DstN c g < vsig2 c (nodeS c g) / 2 := by
    have : DmN n < SminN n / 2 := by
      unfold DmN SminN
      rw [div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      have h3 : (160 : ℝ) * n < (n : ℝ) ^ 3 := by nlinarith [mul_pos hn0 hn0]
      nlinarith
    linarith
  have HP := piN_le hn1 c g hs (O1n_nonneg n) h1 hDlt
  rw [nd_wT_S c g hn1 hs h1] at HP
  have hn17 : (0 : ℝ) < (n : ℝ) - 17 := by linarith
  have hn9 : (0 : ℝ) < (n : ℝ) - 9 := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  set α := cLS 8 ^ 2 * K3N n * ((n : ℝ) - 17)⁻¹ with hα
  set β := 2 * √(12 / (5 * (n : ℝ))) * (cLS 4 * √(K3N n) * √(((n : ℝ) - 9)⁻¹)) with hβ
  set γ := K3N n / ((n : ℝ) - 2) with hγ
  have hc8 := (cLS_pos (q := 8) (by norm_num))
  have hc4 := (cLS_pos (q := 4) (by norm_num))
  have hα0 : 0 < α := by rw [hα]; positivity
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have hγ0 : 0 < γ := by rw [hγ]; positivity
  have h16 : ∫ v, (√(wT c g v) - μ0) ^ 16 ∂stdGauss (Fin (n - 1)) ≤ α ^ 8 := by
    refine hm8.trans (le_of_eq ?_)
    rw [hα]; push_cast; ring_nf
  have hμa : |μ0| ≤ √(12 / (5 * (n : ℝ))) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hμ
  have h8 : (2 * |μ0|) ^ 8 * ∫ v, (√(wT c g v) - μ0) ^ 8 ∂stdGauss (Fin (n - 1)) ≤ β ^ 8 := by
    have hm4' : ∫ v, (√(wT c g v) - μ0) ^ 8 ∂stdGauss (Fin (n - 1)) ≤
        cLS 4 ^ 8 * K3N n ^ 4 * (((n : ℝ) - 9)⁻¹) ^ 4 := by
      refine hm4.trans (le_of_eq ?_); push_cast; ring_nf
    have hI0 : 0 ≤ ∫ v, (√(wT c g v) - μ0) ^ 8 ∂stdGauss (Fin (n - 1)) :=
      integral_nonneg fun _ => by positivity
    calc (2 * |μ0|) ^ 8 * ∫ v, (√(wT c g v) - μ0) ^ 8 ∂stdGauss (Fin (n - 1)) ≤
        (2 * √(12 / (5 * (n : ℝ)))) ^ 8 * (cLS 4 ^ 8 * K3N n ^ 4 * (((n : ℝ) - 9)⁻¹) ^ 4) := by
          refine mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith [hμa]) 8) hm4' hI0
            (by positivity)
      _ = β ^ 8 := by
          rw [hβ]
          have e1 : √(K3N n) ^ 8 = K3N n ^ 4 := by
            rw [show √(K3N n) ^ 8 = (√(K3N n) ^ 2) ^ 4 by ring, Real.sq_sqrt hK]
          have e2 : √(((n : ℝ) - 9)⁻¹) ^ 8 = (((n : ℝ) - 9)⁻¹) ^ 4 := by
            rw [show √(((n : ℝ) - 9)⁻¹) ^ 8 = (√(((n : ℝ) - 9)⁻¹) ^ 2) ^ 4 by ring,
              Real.sq_sqrt (by positivity)]
          simp only [mul_pow, e1, e2]
  have HE := mo_eight_sq (μ := stdGauss (Fin (n - 1))) (measurable_wT c g).sqrt
    (nd_S_bdd c g hn1 hs h1) hα0 hβ0 hγ0 h16 h8 h2
  refine HP.trans ?_
  have hden : 1 / (10 * (n : ℝ)) - 16 / (n : ℝ) ^ 3 ≤ vsig2 c (nodeS c g) / 2 - DstN c g := by
    have e : SminN n / 2 = 1 / (10 * (n : ℝ)) := by unfold SminN; field_simp; ring
    have : DstN c g ≤ 16 / (n : ℝ) ^ 3 := hDst
    linarith
  have hd0 : 0 < vsig2 c (nodeS c g) / 2 - DstN c g := by linarith
  calc (∫ v, (√(wT c g v) ^ 2 - ∫ w, √(wT c g w) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 8
        ∂stdGauss (Fin (n - 1))) / (vsig2 c (nodeS c g) / 2 - DstN c g) ^ 8 ≤
      (α + β + γ) ^ 8 / (vsig2 c (nodeS c g) / 2 - DstN c g) ^ 8 := by gcongr
    _ ≤ 1 / (n : ℝ) ^ 4 := by
      refine nd_numP hnR hα0.le ?_ hβ0.le ?_ hγ0.le le_rfl hden
      · have hc8' : cLS 8 ^ 2 ≤ 1519 / 100 :=
          (pow_le_pow_left₀ hc8.le cLS8_le 2).trans (by norm_num)
        rw [hα, ← div_eq_mul_inv]; unfold K3N; gcongr
      · have hc4' : cLS 4 ^ 2 ≤ 7905 / 1000 :=
          (pow_le_pow_left₀ hc4.le cLS4_le 2).trans (by norm_num)
        rw [hβ, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
          Real.sq_sqrt hK, Real.sq_sqrt (by positivity)]
        unfold K3N
        rw [div_eq_mul_inv _ ((n : ℝ) - 9)]
        have : (0:ℝ) ≤ 32 / (5 * (n : ℝ) ^ 2) := by positivity
        calc 2 ^ 2 * (12 / (5 * ↑n)) * (cLS 4 ^ 2 * (32 / (5 * ↑n ^ 2)) * ((n : ℝ) - 9)⁻¹) ≤
            2 ^ 2 * (12 / (5 * ↑n)) * (7905 / 1000 * (32 / (5 * ↑n ^ 2)) * ((n : ℝ) - 9)⁻¹) := by
              gcongr
          _ = _ := by ring
    _ = PmN n := by unfold PmN; rfl

end
end SPart172Node

-- ===== from Part172Good.lean =====
section SPart172Good
open BstLean.Part172
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part134 (res)
open BstLean.Part161 (xLat uHat)
open BstLean.Part162 (dirW tanSq)
open BstLean.Part167 (latSq D1A1)
open BstLean.Part170 (tA hB mkR windowW node_bulk)
open BstLean.Part53 (unitF53)
variable {n : ℕ}
/-- **The four node statistics on the good set.** -/
theorem node_good (hn : 55000 ≤ n) {wr : WRet n} (hw : windowW wr)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (h1 : OpB A (O1n n)) {g : ℕ} (hg : g < Js n)
    (hσl : SminN n ≤ vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g))
    (hσu : vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) ≤ 12 / (5 * (n : ℝ)))
    (hk : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ i, (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)) i ≠ 0)
    (hb1 : ∫ v, |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (F1 wr) A v| ^ 64
      ∂stdGauss (Fin (n - 1)) ≤ K1N n ^ 64)
    (hb2 : ∫ v, |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (F2 wr g) A v| ^ 64
      ∂stdGauss (Fin (n - 1)) ≤ K1N n ^ 64)
    (hb3 : ∫ v, |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (F3 wr g) A v| ^ 64
      ∂stdGauss (Fin (n - 1)) ≤ K3N n ^ 64) :
    LowStat2 (mkR wr (A, 0)) g := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (55000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : (nodeS (mkR wr (0, 0)) g) ^ 2 ≤ 1 := node_bulk hn hw (A, 0) hg
  have hc : (mkR wr (0, 0)).1.2 ≠ 0 := sg_wr_ne hn1 hw
  have hc' : (mkR wr (A, 0)).1.2 ≠ 0 := hc
  have hO : 0 ≤ O1n n := O1n_nonneg n
  have hK1 : 0 < K1N n := by unfold K1N; positivity
  have hK3 : 0 < K3N n := by unfold K3N; positivity
  have hnz : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
    have h0 : stdGauss (Fin (n - 1)) {(0 : Fin (n - 1) → ℝ)} = 0 :=
      BstLean.Part168.stdGauss_zero (by omega)
    rw [ae_iff]; simpa using h0
  -- measurability and bounds of the three statistics in `v`
  have hmT : ∀ F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ,
      Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2) →
      Measurable (fun v => Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) F A v) := fun F hF =>
    gd_meas_left _ _ hF A
  have hF1m : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      F1 wr p.1 p.2) := (fr_meas_e1 wr).comp measurable_fst
  have hF2m : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      F2 wr g p.1 p.2) := (fr_meas_e2 wr g).comp measurable_fst
  have hF3m := gd_F3_meas wr g
  have hB1 : ∀ A' v, normSq (F1 wr A' v) ≤ tA n := fun A' v => e1v_normSq_le _
  have hB2 : ∀ A' v, normSq (F2 wr g A' v) ≤ tA n := fun A' v => e2v_normSq_le _ _
  have hB3 : ∀ A' v, normSq (F3 wr g A' v) ≤ tA n := gd_F3_le wr g
  have hCb : ∀ F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ,
      (∀ A' v, normSq (F A' v) ≤ tA n) → ∀ v, |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) F A v| ≤
        |1 - (nodeS (mkR wr (0, 0)) g) ^ 2| * (tA n * (∑ i, ∑ l, A i l ^ 2) * 3) :=
    fun F hF v => mk_bdd hn1 hc (nodeS (mkR wr (0, 0)) g) F hF A v
  obtain ⟨-, -, -, h11⟩ := gd_chain (hmT _ hF1m) (hCb _ hB1) hK1 hb1
  obtain ⟨-, -, -, h21⟩ := gd_chain (hmT _ hF2m) (hCb _ hB2) hK1 hb2
  obtain ⟨h38, h34, h32, h31⟩ := gd_chain (hmT _ hF3m) (hCb _ hB3) hK3 hb3
  have hi : ∀ F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ,
      Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2) →
      (∀ A' v, normSq (F A' v) ≤ tA n) → ∀ k : ℕ,
      Integrable (fun v => |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) F A v| ^ k) (stdGauss (Fin (n - 1))) := fun F hF hB k =>
    mo_bdd_pow (hmT F hF).abs (fun v => by rw [abs_abs]; exact hCb F hB v) k
  -- DstN
  have hT1i : ∀ F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ,
      Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2) →
      (∀ A' v, normSq (F A' v) ≤ tA n) →
      Integrable (fun v => Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) F A v) (stdGauss (Fin (n - 1))) := fun F hF hB =>
    mo_bdd_int (hmT F hF) (hCb F hB)
  have hDe : ∀ (e : Fin (mA n) → ℝ) (F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) →
      Fin (mA n) → ℝ), (∀ v, F A v = e) →
      Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2) →
      (∀ A' v, normSq (F A' v) ≤ tA n) →
      ∫ v, |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) F A v| ∂stdGauss (Fin (n - 1)) ≤ K1N n →
      ∫ v, tanSq (fun x => e ⬝ᵥ reluV ((A1 (mkR wr (A, 0))) *ᵥ x)) (mkR wr (A, 0))
        (nodeS (mkR wr (A, 0)) g) v ∂stdGauss (Fin (n - 1)) ≤ K1N n := by
    intro e F hFe hF hB hK
    have hcg : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
        tanSq (fun x => e ⬝ᵥ reluV ((A1 (mkR wr (A, 0))) *ᵥ x)) (mkR wr (A, 0))
          (nodeS (mkR wr (A, 0)) g) v = Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) F A v := by
      filter_upwards [hnz, hk] with v hv hkv
      have ht := tan_dot (s := nodeS (mkR wr (A, 0)) g) hn1 hc' hs hv (A1 (mkR wr (A, 0))) e hkv
      rw [ht]
      simp only [Tf, hFe]
      rfl
    rw [integral_congr_ae hcg]
    exact (integral_mono (hT1i F hF hB) (hT1i F hF hB).abs fun v => le_abs_self _).trans hK
  have hD1 := hDe (e1v (mkR wr (A, 0))) (F1 wr) (fun v => rfl) hF1m hB1 h11
  have hD2 := hDe (e2v (mkR wr (A, 0)) g) (F2 wr g) (fun v => rfl) hF2m hB2 h21
  have hDst : DstN (mkR wr (A, 0)) g ≤ DmN n := by
    have H := DstN_le_tan (by omega) (mkR wr (A, 0)) g hs hO h1
    have H2 : ((n : ℝ) - 2) * DstN (mkR wr (A, 0)) g ≤ 2 * K1N n := by
      have := add_le_add hD1 hD2
      linarith
    unfold DmN
    unfold K1N at H2
    have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    rw [le_div_iff₀ (by positivity)]
    have hD0 := DstN_nonneg (mkR wr (A, 0)) g
    have e : DstN (mkR wr (A, 0)) g ≤ 2 * (79 / (10 * (n : ℝ) ^ 2)) / ((n : ℝ) - 2) := by
      rw [le_div_iff₀ hn2]; linarith
    calc DstN (mkR wr (A, 0)) g * (n : ℝ) ^ 3 ≤ 2 * (79 / (10 * (n : ℝ) ^ 2)) / ((n : ℝ) - 2) * (n : ℝ) ^ 3 := by
          gcongr
      _ ≤ 16 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hn2]
          field_simp
          nlinarith
  -- the field `S`
  have hrh : ∑ j, res (hB (mkR wr (A, 0))) (a1Bar (mkR wr (A, 0)) (nodeS (mkR wr (0, 0)) g)) j * hB (mkR wr (A, 0)) j = 0 := by
    rw [← BstLean.Part170.perp_eq_res]; exact gr_perp_orth _ _
  have hSle : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      tanSq (SN (mkR wr (A, 0)) g) (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) v ≤ Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (F3 wr g) A v := by
    filter_upwards [hnz, hk] with v hv hkv
    exact tan_sqrtw hn1 hc' hs hv A (tA n) (hB (mkR wr (A, 0))) (res (hB (mkR wr (A, 0))) (a1Bar (mkR wr (A, 0)) (nodeS (mkR wr (0, 0)) g))) hrh hkv
  have hT1 : ∫ v, tanSq (SN (mkR wr (A, 0)) g) (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) v ∂stdGauss (Fin (n - 1)) ≤ K3N n :=
    (gd_int_le (hT1i _ hF3m hB3) hSle).trans h31
  have hTq : ∀ q : ℕ, 1 ≤ q → ∫ v, |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (F3 wr g) A v| ^ q ∂stdGauss (Fin (n - 1)) ≤ K3N n ^ q →
      ∫ v, |√(tanSq (SN (mkR wr (A, 0)) g) (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) v)| ^ (2 * q) ∂stdGauss (Fin (n - 1)) ≤ K3N n ^ q := by
    intro q _ hq
    refine le_trans (integral_mono_of_nonneg (ae_of_all _ fun v => by positivity)
      (hi _ hF3m hB3 q) ?_) hq
    filter_upwards [hSle] with v hv
    rw [abs_of_nonneg (Real.sqrt_nonneg _), pow_mul]
    rcases le_total 0 (tanSq (SN (mkR wr (A, 0)) g) (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) v) with ht | ht
    · rw [Real.sq_sqrt ht]
      exact pow_le_pow_left₀ ht (hv.trans (le_abs_self _)) q
    · rw [Real.sqrt_eq_zero'.mpr ht]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      rw [zero_pow (by omega)]; positivity
  have hT2 := hTq 2 (by norm_num) h32
  have hT4 := hTq 4 (by norm_num) h34
  have hT8 := hTq 8 (by norm_num) h38
  exact ⟨hσl, hDst, V2N_of_tan (mkR wr (A, 0)) g hn hs h1 hσu hDst hT1 hT2,
    piN_of_tan (mkR wr (A, 0)) g hn hs h1 hσl hσu hDst hT1 hT4 hT8⟩

end SPart172Good

-- ===== from Part172End.lean =====
section SPart172End
open BstLean.Part172
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part161 (xLat uHat)
open BstLean.Part170 (tA mkR windowW node_bulk)
open BstLean.Part153 (nuA)
open BstLean.Part53 (unitF53)
variable {n : ℕ}
/-- The Markov bound of one per-node event, in the window. -/
lemma en_bad (hn : 55000 ≤ n) {wr : WRet n} (hw : windowW wr) {g : ℕ} (hg : g < Js n)
    (F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ)
    (hF : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2))
    (hadm : ∀ v, fr_Adm (xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v))
      (uHat (mkR wr (0, 0))) (fun A => F A v))
    (hB : ∀ A v, normSq (F A v) ≤ tA n) {k r : ℝ} (hk : 0 < k) (hr : 5752 / 10000 * (425 / 100) / k ≤ r) :
    gaussMat (mA n) n (2 / (n : ℝ))
        {A | (k / (n : ℝ) ^ 2) ^ 64 < ∫ v, |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) F A v| ^ 64
          ∂stdGauss (Fin (n - 1))} ≤ ENNReal.ofReal (r ^ 64) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1 := node_bulk hn hw (0, 0) hg
  obtain ⟨-, hs2⟩ := sg_node_lat hn hw (0, 0) hg
  have hc : (mkR wr (0, 0)).1.2 ≠ 0 := sg_wr_ne hn1 hw
  have hK : 0 < k / (n : ℝ) ^ 2 := by positivity
  refine (mk_markov hn hc hs F hF hadm hB hK).trans ?_
  rw [← ENNReal.ofReal_div_of_pos (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set s := nodeS (mkR wr (0, 0)) g
  have e : ((1 - s ^ 2) * (425 / 100 / (n : ℝ) ^ 2)) ^ 64 / (k / (n : ℝ) ^ 2) ^ 64 =
      ((1 - s ^ 2) * (425 / 100) / k) ^ 64 := by
    rw [← div_pow]; congr 1; field_simp
  rw [e]
  refine pow_le_pow_left₀ (by
    have : 0 ≤ 1 - s ^ 2 := by linarith
    positivity) ?_ 64
  refine le_trans ?_ hr
  gcongr
  linarith

/-- **The charge of the statistics event** (the remaining hypothesis of Part 171). -/
theorem stat_charge (hn : 55000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) {wr : WRet n} (hw : windowW wr) :
    (nuA n).real {θ | (wr, θ.1) ∉ StatEvOp2 n} ≤ 1 / 10000 := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc : (mkR wr (0, 0)).1.2 ≠ 0 := sg_wr_ne hn1 hw
  set μA := gaussMat (mA n) n (2 / (n : ℝ))
  set c0 : Ret n := mkR wr (0, 0)
  -- the sets
  set Sig := {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < SminN n ∨
      12 / (5 * (n : ℝ)) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} with hSig
  set Bk := fun (g : ℕ) (k : ℝ) (F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) →
      Fin (mA n) → ℝ) => {A | (k / (n : ℝ) ^ 2) ^ 64 <
      ∫ v, |Tf c0 (nodeS c0 g) F A v| ^ 64 ∂stdGauss (Fin (n - 1))} with hBk
  set Nul := {A : Matrix (Fin (mA n)) (Fin n) ℝ | ¬ ∀ g < Js n, ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ i, (A *ᵥ xLat c0 (nodeS c0 g) (unitF53 v)) i ≠ 0} with hNul
  set Bad := {A : Matrix (Fin (mA n)) (Fin n) ℝ | (wr, A) ∉ StatEvOp2 n} with hBad
  -- inclusion
  have hsub : Bad ⊆ Sig ∪ (⋃ g ∈ Finset.range (Js n),
      (Bk g (79 / 10) (F1 wr) ∪ Bk g (79 / 10) (F2 wr g) ∪ Bk g (32 / 5) (F3 wr g))) ∪ Nul := by
    intro A hA
    simp only [hBad, mem_setOf_eq, StatEvOp2, not_forall] at hA
    obtain ⟨hop, g, hg, hlow⟩ := hA
    by_contra hcon
    simp only [mem_union, mem_iUnion, Finset.mem_range, not_or, not_exists] at hcon
    obtain ⟨⟨hS, hB⟩, hN0⟩ := hcon
    apply hlow
    have hS' : ¬ (vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) < SminN n ∨
        12 / (5 * (n : ℝ)) < vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g)) := fun h =>
      hS ⟨g, hg, h⟩
    push_neg at hS'
    have hN' : ∀ g < Js n, ∀ᵐ v ∂stdGauss (Fin (n - 1)),
        ∀ i, (A *ᵥ xLat c0 (nodeS c0 g) (unitF53 v)) i ≠ 0 := by
      by_contra h; exact hN0 h
    obtain ⟨⟨h1, h2⟩, h3⟩ := hB g hg
    have e1 : K1N n ^ 64 = (79 / 10 / (n : ℝ) ^ 2) ^ 64 := by unfold K1N; congr 1; ring
    have e3 : K3N n ^ 64 = (32 / 5 / (n : ℝ) ^ 2) ^ 64 := by unfold K3N; congr 1; ring
    refine node_good hn hw A hop hg hS'.1 hS'.2 (hN' g hg) ?_ ?_ ?_
    · rw [e1]; exact not_lt.mp h1
    · rw [e1]; exact not_lt.mp h2
    · rw [e3]; exact not_lt.mp h3
  -- the null set
  have hNul0 : μA Nul = 0 := by
    have hae : ∀ᵐ A ∂μA, ∀ g < Js n, ∀ᵐ v ∂stdGauss (Fin (n - 1)),
        ∀ i, (A *ᵥ xLat c0 (nodeS c0 g) (unitF53 v)) i ≠ 0 := by
      rw [ae_all_iff]
      intro g
      by_cases hg : g < Js n
      · have hs : nodeS c0 g ^ 2 ≤ 1 := node_bulk hn hw (0, 0) hg
        exact (kink_ae (by omega) c0 hs).mono fun A h _ => h
      · exact Eventually.of_forall fun A h => absurd h hg
    rw [ae_iff] at hae
    simpa [hNul] using hae
  -- the ς event
  have hSigm : μA Sig ≤ ENNReal.ofReal (15 / 10 ^ 7) := by
    have h := sig_charge hn hw
    rw [← ENNReal.ofReal_toReal (measure_ne_top μA Sig)]
    exact ENNReal.ofReal_le_ofReal h
  -- the Markov events
  have hadm1 : ∀ g, ∀ v, fr_Adm (xLat c0 (nodeS c0 g) (unitF53 v)) (uHat c0)
      (fun A => F1 wr A v) := fun g v => e1v_adm c0 _
  have hadm2 : ∀ g, ∀ v, fr_Adm (xLat c0 (nodeS c0 g) (unitF53 v)) (uHat c0)
      (fun A => F2 wr g A v) := fun g v => e2v_adm (by omega) c0 hc g _
  have hadm3 : ∀ g, ∀ v, fr_Adm (xLat c0 (nodeS c0 g) (unitF53 v)) (uHat c0)
      (fun A => F3 wr g A v) := by
    intro g v A A' hx hu hr
    have := cdir_adm (by omega) c0 hc (nodeS c0 g) (xLat c0 (nodeS c0 g) (unitF53 v)) A A' hx hu hr
    simp only [F3]
    exact congrArg (fun z => √(tA n) • z) this
  have hb : ∀ g < Js n, μA (Bk g (79 / 10) (F1 wr) ∪ Bk g (79 / 10) (F2 wr g) ∪
      Bk g (32 / 5) (F3 wr g)) ≤ ENNReal.ofReal (2 * (3095 / 10000) ^ 64 + (3820 / 10000) ^ 64) := by
    intro g hg
    have b1 := en_bad hn hw hg (F1 wr) ((fr_meas_e1 wr).comp measurable_fst) (hadm1 g)
      (fun A v => e1v_normSq_le _) (k := 79 / 10) (r := 3095 / 10000) (by norm_num) (by norm_num)
    have b2 := en_bad hn hw hg (F2 wr g) ((fr_meas_e2 wr g).comp measurable_fst) (hadm2 g)
      (fun A v => e2v_normSq_le _ _) (k := 79 / 10) (r := 3095 / 10000) (by norm_num) (by norm_num)
    have b3 := en_bad hn hw hg (F3 wr g) (gd_F3_meas wr g) (hadm3 g)
      (gd_F3_le wr g) (k := 32 / 5) (r := 3820 / 10000) (by norm_num) (by norm_num)
    calc μA (Bk g (79 / 10) (F1 wr) ∪ Bk g (79 / 10) (F2 wr g) ∪ Bk g (32 / 5) (F3 wr g))
        ≤ μA (Bk g (79 / 10) (F1 wr)) + μA (Bk g (79 / 10) (F2 wr g)) +
          μA (Bk g (32 / 5) (F3 wr g)) :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal ((3095 / 10000) ^ 64) + ENNReal.ofReal ((3095 / 10000) ^ 64) +
          ENNReal.ofReal ((3820 / 10000) ^ 64) := add_le_add (add_le_add b1 b2) b3
      _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  -- total
  have htot : μA Bad ≤ ENNReal.ofReal (1 / 10000) := by
    refine (measure_mono hsub).trans ?_
    refine (measure_union_le _ _).trans ?_
    rw [hNul0, add_zero]
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add hSigm (measure_biUnion_finset_le _ _)).trans ?_
    refine (add_le_add le_rfl (Finset.sum_le_sum fun g hg => hb g (Finset.mem_range.mp hg))).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have e : ((Js n : ℕ) : ℝ≥0∞) = ENNReal.ofReal (512 * (n : ℝ)) := by
      unfold Js; push_cast
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]; norm_num
    rw [e, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by norm_num) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (en_num55 hN hn0)
  -- back to `nuA`
  have hset : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      (wr, θ.1) ∉ StatEvOp2 n} = Bad ×ˢ univ := by
    ext θ; simp [hBad]
  rw [hset, measureReal_def, Measure.prod_prod, measure_univ, mul_one]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) htot

/-- **The classifier theorem with no remaining hypothesis, every `n` with `55 000 ≤ n ≤ 10²⁰`**
(the paper's program in Lean's exact-moment form; success probability `≥ 99/100` for the actual
random networks; every threshold `t`). Part 172's `classifier_paper_uncond` had `80 000 ≤ n`. -/
theorem classifier_paper_uncond55k (hn : 55000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_final55k hn t fun _ hw => stat_charge hn hN hw

end SPart172End

end BstLean.Part174.N55
