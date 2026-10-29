import BstLean.Part172SCheb
import BstLean.Part172SNode

/-!
# Part 172 (file `Sig`): the lower and upper `ς` event and its charge

No proof is left open; no `native_decide` or `axiom` is used.

* **`sig_charge`**: for `n ≥ 80 000` and a World datum in the window, the Gaussian probability
  over `A₁` that some node `g < J_s` has `ς² < 1/(5n)` or `ς² > 12/(5n)` is at most `10⁻⁶`.

Route: `sg_vsig2_lower`, `sg_vsig2_upper` reduce both events to the two row sums
`Σ_i φ₁(a_i)`, `Σ_i φ₂(a_i)` (no union over nodes: the nodes enter only through
`0.43 ≤ 1 − s² ≤ 0.571` and `s ≥ 0`); then Chebyshev (`sg_cheb`).
-/

namespace BstLean.Part172

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS nodeL nodeH nodeD bulk_of_window qB qB_pos)
open BstLean.Part170 (windowW mkR)
open BstLean.Part171 (SminN)

variable {n : ℕ}

lemma sg_wr_ne (hn : 1 ≤ n) {wr : WRet n} (hw : windowW wr) : wr.2 ≠ 0 := by
  obtain ⟨hτ, -, hθ1⟩ := hw
  intro h
  rw [h] at hθ1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have : BstLean.Part150.thetaC (0 : Fin n → ℝ) (BstLean.Part157.tau0p wr.1) = 1 := by
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    have h0 : normSq (0 : Fin n → ℝ) = 0 := by simp [normSq]
    rw [h0, zero_add, Real.sq_sqrt (by positivity)]
    have : 0 < (n : ℝ) * BstLean.Part157.tau0p wr.1 ^ 2 := by positivity
    field_simp
  linarith

lemma sg_node_q (hn : 80000 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
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

lemma sg_alg_low {M D q X m : ℝ} (hM : 0 < M) (hD : 0 < D) (hm : 0 < m) (hq : 43 / 100 ≤ q)
    (hX : 94 / 100 * M * D / m ≤ X) : 1 / (5 * m) ≤ 2 / M * (q / (4 * D)) * X := by
  have e : 2 / M * (q / (4 * D)) * X = q * X / (2 * M * D) := by field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [div_le_iff₀ hm] at hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ 94 / 100 * M * D := by positivity
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hq) (mul_nonneg hX0 hm.le)]

lemma sg_alg_up {M D q Y m : ℝ} (hM : 0 < M) (hD : 0 < D) (hm : 0 < m) (hq0 : 0 ≤ q)
    (hq : q ≤ 571 / 1000) (hY0 : 0 ≤ Y) (hY : Y ≤ 208 / 100 * M * D / m) :
    2 / M * (q / D) * Y ≤ 12 / (5 * m) := by
  have e : 2 / M * (q / D) * Y = 2 * q * Y / (M * D) := by field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [le_div_iff₀ hm] at hY
  nlinarith [mul_le_mul hq hY (by positivity) (by norm_num : (0 : ℝ) ≤ 571 / 1000),
    mul_nonneg hq0 (mul_nonneg hY0 hm.le)]

lemma sg_phi1_smul {u : Fin n → ℝ} {a : ℝ} (ha : 0 < a) (g : Fin n → ℝ) :
    sg_phi1 u (a • g) = a ^ 2 * sg_phi1 u g := by
  have hz : sg_z u (a • g) = a * sg_z u g := by
    unfold sg_z; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring
  have hN : normSq (a • g) = a ^ 2 * normSq g := by
    unfold normSq; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring
  unfold sg_phi1 sg_phi2
  rw [hz, hN]
  by_cases h : 0 ≤ sg_z u g
  · rw [if_pos (mul_nonneg ha.le h), if_pos h]; ring
  · have : ¬ 0 ≤ a * sg_z u g := by
      intro h'; apply h; exact nonneg_of_mul_nonneg_right (by linarith) ha
    rw [if_neg this, if_neg h]; ring

lemma sg_phi2_smul {u : Fin n → ℝ} (a : ℝ) (g : Fin n → ℝ) :
    sg_phi2 u (a • g) = a ^ 2 * sg_phi2 u g := by
  have hz : sg_z u (a • g) = a * sg_z u g := by
    unfold sg_z; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring
  have hN : normSq (a • g) = a ^ 2 * normSq g := by
    unfold normSq; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring
  unfold sg_phi2; rw [hz, hN]; ring

lemma sg_num {m M D B k : ℝ} (hm : 80000 ≤ m) (hM : M = m ^ 2) (hD : D = m - 1)
    (hB : B ≤ m ^ 2 + 2 * m) (hk : 3 / 100 ≤ k) : M * B / (k * M * D) ^ 2 ≤ 5 / 10 ^ 7 := by
  have hD0 : 79999 ≤ D := by rw [hD]; linarith
  have hM0 : 0 < M := by rw [hM]; positivity
  have hk0 : 0 < k := by linarith
  rw [div_le_iff₀ (by positivity)]
  have h1 : M * B ≤ 2 * M ^ 2 := by
    rw [hM]
    have : m ^ 2 * B ≤ m ^ 2 * (m ^ 2 + 2 * m) := mul_le_mul_of_nonneg_left hB (by positivity)
    nlinarith
  have hk2 : 9 / 10000 ≤ k ^ 2 := by nlinarith
  have hD2 : 79999 ^ 2 ≤ D ^ 2 := by nlinarith
  have h2 : 2 ≤ 5 / 10 ^ 7 * (k ^ 2 * D ^ 2) := by nlinarith [mul_le_mul hk2 hD2 (by norm_num) (by positivity)]
  calc M * B ≤ 2 * M ^ 2 := h1
    _ ≤ 5 / 10 ^ 7 * (k ^ 2 * D ^ 2) * M ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 5 / 10 ^ 7 * (k * M * D) ^ 2 := by ring

/-- **The `ς` event and its charge.** -/
theorem sig_charge (hn : 80000 ≤ n) {wr : WRet n} (hw : windowW wr) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real {A₁ | ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < SminN n ∨
      12 / (5 * (n : ℝ)) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} ≤ 1 / 10 ^ 6 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
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
      have := sg_alg_up (q := 1 - s ^ 2) hM hD hn0 (by linarith) (by linarith) hY0 hY
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
      ENNReal.ofReal (1 / 10 ^ 6) := by
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
theorem sig_charge_op (hn : 80000 ≤ n) {wr : WRet n} (hw : windowW wr) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real {A₁ | BstLean.Part169.OpB A₁ (BstLean.Part169.O1n n) ∧
      ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < SminN n ∨
      12 / (5 * (n : ℝ)) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} ≤ 1 / 10 ^ 6 :=
  (measureReal_mono fun _ h => h.2).trans (sig_charge hn hw)

end BstLean.Part172
