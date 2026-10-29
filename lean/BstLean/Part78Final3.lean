import BstLean.Part78Final2
import BstLean.Part78Poincare2
import BstLean.Part78Var4

/-!
# Part 78, first chaos separated: Theorem 4 at `(2,2)`, uniform `D`, from `n ≥ 6600`

The Poincaré inequality with the first chaos separated (`poincareMv2`) halves the main constant of
the conditional variance bound; the first-chaos term is `E_x Σ_i r_i(x)²`, `r_i = E_W[Q_x T_i]`
(`varBoundK2`), and it is small: `≤ 0.727 · Wf · V̄(u)`.

Results:
* `part78_varBoundW3`: `Var(V | u) ≤ c_V · Wf · V̄(u)/n ≤ c_V V̄(u)²/n`, `c_V < 21.96` (`n ≥ 1000`).
* `part78_gauss3`: the Gaussian-model theorem with this `c_V`.
* `part78_22_6600`: Theorem 4 at `(2,2)`, `ε = 1/2`, failure `≤ 1/100`, every `n ≥ 6600`.
* `part78_22_eps3`: every `ε > 0`, every `n ≥ 3950 + 930/ε²`.
-/

namespace BstLean.Part78

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU heavyCount)
open BstLean.Part59

variable {n : ℕ}

lemma int_kap_centered (n : ℕ) (hn1 : 1 ≤ n) :
    ∫ x, (kap x x - tG n) ^ 2 ∂uniformSphere n = kk2 n - tG n ^ 2 := by
  have := BstLean.Part29.uniformSphere_isProbability n hn1
  have ck : Continuous (fun x : Fin n → ℝ => kap x x) := kap_diag_cont
  have e : ∀ x : Fin n → ℝ, (kap x x - tG n) ^ 2 =
      kap x x ^ 2 - 2 * tG n * kap x x + tG n ^ 2 := fun x => by ring
  simp only [e]
  rw [integral_add (f := fun x : Fin n → ℝ => kap x x ^ 2 - 2 * tG n * kap x x)
      (g := fun _ => tG n ^ 2)
      ((sph_int hn1 (ck.pow 2)).sub ((sph_int hn1 ck).const_mul _)) (integrable_const _),
    integral_sub (f := fun x : Fin n → ℝ => kap x x ^ 2)
      (g := fun x : Fin n → ℝ => 2 * tG n * kap x x)
      (sph_int hn1 (ck.pow 2)) ((sph_int hn1 ck).const_mul _), integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  unfold kk2
  have : ∫ x, kap x x ∂uniformSphere n = tG n := rfl
  rw [this]; ring

set_option maxHeartbeats 1600000 in
/-- The first-chaos term: `E_x Σ_i r_i(x)² ≤ 0.727 · Wf · E_W V` (`n ≥ 1000`). -/
lemma rT_int_le (n : ℕ) (hn : 1000 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsSymm) :
    ∫ x, ∑ i, rT a H i x ^ 2 ∂uniformSphere n ≤
      727 / 1000 * Wf a H * ∫ W, VG a H W ∂stdGauss (WIdx n) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have := BstLean.Part29.uniformSphere_isProbability n hn1
  obtain ⟨htG, hm1, hk1, hk2, hs0, hs2, hk⟩ := part78_sphere n hn
  have hfl := floor_le hn (part78_sphere n hn) (by norm_num) (part78_meanIds n hn1) a H hH
  set m := ∫ W, VG a H W ∂stdGauss (WIdx n) with hm
  set A := nsq a with hA
  set v := frobH H with hv
  set T := trH H with hT
  have hA0 : 0 ≤ A := nsq_nonneg a
  have hv0 : 0 ≤ v := frobH_nonneg H
  have ck : Continuous (fun x : Fin n → ℝ => kap x x) := kap_diag_cont
  have cki := cont_kap_int (n := n) hn1
  -- `‖Ha‖² ≤ ‖H‖² ‖a‖²`
  have hHa : ∑ i, (∑ k, H i k * a k) ^ 2 ≤ v * A := by
    rw [hv, hA]; unfold frobH nsq
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hpt : ∀ᵐ x ∂uniformSphere n, ∑ i, rT a H i x ^ 2 ≤
      2 * A * (T ^ 2 * (kap x x - tG n) ^ 2) + 8 * (v * A) * kap x x ^ 2 := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    have hkx := kap_diag_sphere x hx
    have hq0 : 0 ≤ q4 x := Finset.sum_nonneg fun i _ => by positivity
    have hin := inner_kap hn1 x
    rw [hx] at hin
    have h1n : 0 ≤ 1 / (n : ℝ) := by positivity
    have h1n' : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnpos]; linarith
    have hY : (kap x x - 1 / (n : ℝ)) ^ 2 ≤ kap x x ^ 2 := by
      have h0 : 0 ≤ kap x x - 1 / (n : ℝ) := by rw [hkx]; linarith
      nlinarith
    have hterm : ∀ i, rT a H i x ^ 2 ≤ 2 * (a i ^ 2 * (T ^ 2 * (kap x x - tG n) ^ 2)) +
        8 * ((∑ k, H i k * a k) ^ 2 * (kap x x - 1 / (n : ℝ)) ^ 2) := by
      intro i
      unfold rT
      rw [hin]
      nlinarith [sq_nonneg (a i * (T * (kap x x - tG n)) -
        2 * (∑ k, H i k * a k) * (kap x x - 1 / (n : ℝ)))]
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul,
      ← Finset.sum_mul]
    have s1 : (∑ i, (∑ k, H i k * a k) ^ 2) * (kap x x - 1 / (n : ℝ)) ^ 2 ≤
        (v * A) * kap x x ^ 2 :=
      mul_le_mul hHa hY (sq_nonneg _) (mul_nonneg hv0 hA0)
    have e : ∑ i, a i ^ 2 = A := rfl
    rw [e]
    linarith
  have crT : Continuous (fun x : Fin n → ℝ => ∑ i, rT a H i x ^ 2) := by
    refine continuous_finsetSum _ fun i _ => ?_
    unfold rT
    exact ((continuous_const.mul (continuous_const.mul (ck.sub continuous_const))).add
      (continuous_const.mul (ck.sub cki))).pow 2
  have ik2 : Integrable (fun x : Fin n → ℝ => (kap x x - tG n) ^ 2) (uniformSphere n) :=
    sph_int hn1 ((ck.sub continuous_const).pow 2)
  have ikk : Integrable (fun x : Fin n → ℝ => kap x x ^ 2) (uniformSphere n) :=
    sph_int hn1 (ck.pow 2)
  have hI : ∫ x, ∑ i, rT a H i x ^ 2 ∂uniformSphere n ≤
      ∫ x, (2 * A * (T ^ 2 * (kap x x - tG n) ^ 2) + 8 * (v * A) * kap x x ^ 2)
        ∂uniformSphere n :=
    integral_mono_ae (sph_int hn1 crT)
      (((ik2.const_mul (T ^ 2)).const_mul (2 * A)).add (ikk.const_mul (8 * (v * A)))) hpt
  rw [integral_add (f := fun x : Fin n → ℝ => 2 * A * (T ^ 2 * (kap x x - tG n) ^ 2))
      (g := fun x : Fin n → ℝ => 8 * (v * A) * kap x x ^ 2)
      ((ik2.const_mul (T ^ 2)).const_mul (2 * A)) (ikk.const_mul (8 * (v * A))),
    integral_const_mul, integral_const_mul, integral_const_mul, int_kap_centered n hn1] at hI
  have hkk2 : ∫ x, kap x x ^ 2 ∂uniformSphere n = kk2 n := rfl
  rw [hkk2] at hI
  -- numbers
  have hq : 3 / (4 * ((n : ℝ) + 2)) ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hq0 : 0 ≤ 3 / (4 * ((n : ℝ) + 2)) := by positivity
  have hq' : 3 / (2 * ((n : ℝ) + 2)) = 2 * (3 / (4 * ((n : ℝ) + 2))) := by field_simp; ring
  have ht : tG n ≤ 1502 / 1000 := by rw [htG, hq']; linarith
  have ht0 : 3 / 2 ≤ tG n := by rw [htG, hq']; linarith
  have ht2 : tG n ^ 2 ≤ 2257 / 1000 := by nlinarith
  have hkk : kk2 n ≤ 2258 / 1000 := by linarith
  have hT2 : T ^ 2 * (kk2 n - tG n ^ 2) ≤ 3 / 4 * v := by
    have e2 := trH_sq_le H
    have hC0 : 0 ≤ kk2 n - tG n ^ 2 := by linarith
    have hC1 : kk2 n - tG n ^ 2 ≤ 3 / (4 * ((n : ℝ) + 2)) := by linarith
    have e3 : T ^ 2 * (kk2 n - tG n ^ 2) ≤ (n * v) * (3 / (4 * ((n : ℝ) + 2))) :=
      mul_le_mul e2 hC1 hC0 (mul_nonneg hnpos.le hv0)
    have hnq : (n : ℝ) * (3 / (4 * ((n : ℝ) + 2))) ≤ 3 / 4 := by
      have : (n : ℝ) * (3 / (4 * ((n : ℝ) + 2))) = 3 * n / (4 * ((n : ℝ) + 2)) := by ring
      rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have e4 : (n * v) * (3 / (4 * ((n : ℝ) + 2))) = ((n : ℝ) * (3 / (4 * ((n : ℝ) + 2)))) * v := by
      ring
    rw [e4] at e3
    exact e3.trans (mul_le_mul_of_nonneg_right hnq hv0)
  have hvA0 : 0 ≤ v * A := mul_nonneg hv0 hA0
  have b1 : 2 * A * (T ^ 2 * (kk2 n - tG n ^ 2)) ≤ 2 * A * (3 / 4 * v) :=
    mul_le_mul_of_nonneg_left hT2 (by linarith)
  have b2 : 8 * (v * A) * kk2 n ≤ 8 * (v * A) * (2258 / 1000) :=
    mul_le_mul_of_nonneg_left hkk (by linarith)
  have hW0 := Wf_nonneg a H
  have hWW : Wf a H * Wf a H ≤ Wf a H * m := mul_le_mul_of_nonneg_left hfl hW0
  have hAM : 2694 / 100 * (v * A) ≤ Wf a H * Wf a H := by
    unfold Wf
    nlinarith [sq_nonneg (3 / 2 * A - 449 / 100 * v)]
  refine hI.trans ?_
  nlinarith

/-- From the two kernel forms to the floor form. -/
theorem varBoundW_of_K2 (n : ℕ) (hn : 1000 ≤ n) {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hK : VarBoundK n c) (hK2 : VarBoundK2 n c c') (hQ : WQId n) :
    VarBoundW n (1 / 2 * (c * (1414 / 1000)) + 1 / 2 * (c' * (727 / 1000))) := by
  intro a H hH
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hwc, hwm, -⟩ := hK a H hH
  have h1 := kernel_int_le n hn hQ a H hH hwc hwm
  have h2 := rT_int_le n hn a H hH
  refine (hK2 a H hH).trans ?_
  have hcn : 0 ≤ c / (n : ℝ) := div_nonneg hc hnpos.le
  have hcn' : 0 ≤ c' / (n : ℝ) := div_nonneg hc' hnpos.le
  have g1 := mul_le_mul_of_nonneg_left h1 hcn
  have g2 := mul_le_mul_of_nonneg_left h2 hcn'
  have e : (1 / 2 * (c * (1414 / 1000)) + 1 / 2 * (c' * (727 / 1000))) / (n : ℝ) * Wf a H *
      ∫ W, VG a H W ∂stdGauss (WIdx n) =
      1 / 2 * (c / (n : ℝ) * (1414 / 1000 * Wf a H * ∫ W, VG a H W ∂stdGauss (WIdx n))) +
      1 / 2 * (c' / (n : ℝ) * (727 / 1000 * Wf a H * ∫ W, VG a H W ∂stdGauss (WIdx n))) := by
    ring
  rw [e]
  linarith

theorem part78_varBoundK2 (n : ℕ) (hn : 1 ≤ n) :
    VarBoundK2 n (4 * 1 * (1733 / 1000) * (4184 / 1000)) (4 * 1) :=
  varBoundK2 n hn 1 3 (1733 / 1000) (35 / 2) (4184 / 1000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) poincareMv2 (featOp1 n hn) affFourth3 deg2Fourth
    gaussLin wickTwoPoint

/-- **`Var(V | u) ≤ c_V · Wf · V̄(u)/n`** with
`c_V = (1/2)·4·1.733·4.184·1.414 + (1/2)·4·0.727 < 21.96`, `n ≥ 1000`. -/
theorem part78_varBoundW3 (n : ℕ) (hn : 1000 ≤ n) :
    VarBoundW n (1 / 2 * (4 * 1 * (1733 / 1000) * (4184 / 1000) * (1414 / 1000)) +
      1 / 2 * (4 * 1 * (727 / 1000))) :=
  varBoundW_of_K2 n hn (by norm_num) (by norm_num) (part78_varBoundK n (by omega))
    (part78_varBoundK2 n (by omega)) (wQId n (by omega) wickTwoPoint)

/-- **`Var(V | u) ≤ c_V V̄(u)²/n` with `c_V = 2196/100`**, `n ≥ 1000`. -/
theorem part78_cV3 (n : ℕ) (hn : 1000 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsSymm) :
    ∫ W, (VG a H W - ∫ W', VG a H W' ∂stdGauss (WIdx n)) ^ 2 ∂stdGauss (WIdx n) ≤
      (2196 / 100) / n * (∫ W, VG a H W ∂stdGauss (WIdx n)) ^ 2 := by
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hfl := floor_le hn (part78_sphere n hn) (by norm_num) (part78_meanIds n (by omega)) a H hH
  set m := ∫ W, VG a H W ∂stdGauss (WIdx n)
  have hm0 : 0 ≤ m := le_trans (Wf_nonneg a H) hfl
  refine (part78_varBoundW3 n hn a H hH).trans ?_
  have h1 : (1 / 2 * (4 * 1 * (1733 / 1000) * (4184 / 1000) * (1414 / 1000)) +
      1 / 2 * (4 * 1 * (727 / 1000)) : ℝ) / n ≤ (2196 / 100) / n :=
    div_le_div_of_nonneg_right (by norm_num) hnpos.le
  have h2 := mul_le_mul_of_nonneg_right
    (mul_le_mul h1 hfl (Wf_nonneg a H) (by positivity)) hm0
  refine h2.trans (le_of_eq ?_)
  ring

/-- **The Gaussian-model theorem, given the constant column** (`n ≥ 1000`):
failure `≤ c₁/(n ε² κ) + c_V/(n (1−κ)²)`, `c₁ = 19/20`, `c_V < 21.96`, `κ = 1 − θ`. -/
theorem part78_gauss3 (n : ℕ) (hn : 1000 ≤ n) (κ ε : ℝ) (hκ0 : 0 < κ) (hκ : κ < 1) (hε : 0 < ε)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hpos : 0 < frobH H) :
    stdGauss (WIdx n) {W | ε ^ 2 * VG a H W < errG a H W ^ 2} ≤
      ENNReal.ofReal (19 / 20 / (n * (ε ^ 2 * κ)) +
        (1 / 2 * (4 * 1 * (1733 / 1000) * (4184 / 1000) * (1414 / 1000)) +
          1 / 2 * (4 * 1 * (727 / 1000))) / (n * (1 - κ) ^ 2)) :=
  gauss_model hn (part78_sphere n hn) (by norm_num) (part78_meanIds n (by omega))
    (part78_varBoundW3 n hn) (by norm_num) (by norm_num) (by norm_num) hκ0 hκ hε a H hH hpos

/-- Failure `≤ 1/100` at `ε = 1/2` for every `n ≥ 6600`. -/
theorem fail78_6600 (n : ℕ) (hn : 6600 ≤ n) (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
      (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n 2 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal (1 / 100) := by
  have hn' : (6600 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx : 1 / (n : ℝ) ≤ 1 / 6600 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have hx' : (n : ℝ)⁻¹ ≤ 1 / 6600 := by rw [← one_div]; exact hx
  refine (fail78_core n (by omega)
    (cW := 1 / 2 * (4 * 1 * (1733 / 1000) * (4184 / 1000) * (1414 / 1000)) +
      1 / 2 * (4 * 1 * (727 / 1000)))
    (κ := 23 / 100) (ε := 1 / 2) (ε₁ := 2035 / 10000) (lam := 3 / 100) (t := 8)
    (part78_varBoundW3 n (by omega)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; linarith) c hc).trans (ENNReal.ofReal_le_ofReal ?_)
  norm_num
  linarith

/-- Failure `≤ 1/100` for every `ε > 0` and every `n ≥ 3950 + 930/ε²`. -/
theorem fail78_eps3 (ε : ℝ) (hε0 : 0 < ε) (n : ℕ)
    (hn : 3950 + 930 / ε ^ 2 ≤ (n : ℝ)) (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
      ε ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n 2 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal (1 / 100) := by
  have he2 : 0 < ε ^ 2 := by positivity
  have hd0 : 0 ≤ 930 / ε ^ 2 := by positivity
  have hnR : (3950 : ℝ) ≤ n := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hn1000 : 1000 ≤ n := by
    have : ((1000 : ℕ) : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx1 : 1 / (n : ℝ) ≤ 1 / 3950 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have hx2 : 1 / (n : ℝ) ≤ ε ^ 2 / 930 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]
    have : 930 / ε ^ 2 ≤ (n : ℝ) := by linarith
    rw [div_le_iff₀ he2] at this
    linarith
  refine (fail78_core n hn1000
    (cW := 1 / 2 * (4 * 1 * (1733 / 1000) * (4184 / 1000) * (1414 / 1000)) +
      1 / 2 * (4 * 1 * (727 / 1000)))
    (κ := 1 / 5) (ε := ε) (ε₁ := 8 / 25 * ε) (lam := 3 / 100) (t := 10)
    (part78_varBoundW3 n hn1000) (by norm_num)
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by norm_num) (by norm_num)
    ?_ c hc).trans (ENNReal.ofReal_le_ofReal ?_)
  · have h3 := mul_le_mul_of_nonneg_left hx1 he2.le
    nlinarith
  · have e : (19 / 20 : ℝ) / (8 / 25 * ε) ^ 2 = 11875 / 1280 / ε ^ 2 := by
      field_simp; ring
    rw [e]
    have hY : 11875 / 1280 / ε ^ 2 ≤ 930 / 100 / ε ^ 2 :=
      div_le_div_of_nonneg_right (by norm_num) he2.le
    have hsum : (4 + 11875 / 1280 / ε ^ 2 +
        (1 / 2 * (4 * 1 * (1733 / 1000) * (4184 / 1000) * (1414 / 1000)) +
          1 / 2 * (4 * 1 * (727 / 1000))) / (1 - 1 / 5) ^ 2 +
        567 / 50 / 10 + 1 / 100 : ℝ) ≤ (n : ℝ) / 100 := by
      have : (930 : ℝ) / 100 / ε ^ 2 = 930 / ε ^ 2 / 100 := by ring
      norm_num at this ⊢
      linarith
    have := mul_le_mul_of_nonneg_right hsum hx0.le
    refine this.trans (le_of_eq ?_)
    field_simp

/-- **Theorem 4 at `(d_M, d_f) = (2,2)`, uniform `D`, `ε = 1/2`, failure `≤ 1/100`, every
`n ≥ 6600`.** The statement of `Part59.part59_general` at `(2,2)` with `μ = uniformSphere n`. -/
theorem part78_22_6600 :
    ∀ n : ℕ, 6600 ≤ n → ∃ pg : Prog (In59 n 2 2) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n 2 2 → ℝ, pg.eval v () = g0Q n 2 2 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n 2 2 (1 / 2) ∧
      ∀ c : Mono n 2 → ℝ, TopNZ 2 c →
        stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
          (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
            (BP (uniformSphere n) 2 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  intro n hn
  have hn1 : 1 ≤ n := by omega
  obtain ⟨pg, h0, hread, hspec, hcost⟩ := prog59_exists n 2 2 hn1 (by norm_num) (by norm_num)
  refine ⟨pg, h0, hread, hspec, cost_lt_baselineF59 2 (1 / 2) pg.cost hcost
    ((costG59_lt_twoPp n 2 2 (by norm_num) (by omega)).trans_le (twoPp_le_baselineF n 2 2 (1 / 2))),
    ?_⟩
  intro c hc
  have heval : ∀ M : CoefIdxD n 2 → ℝ, pg.eval (inp59 c M) () = g0Q n 2 2 c M := by
    intro M
    rw [hspec, (cv59_inp 2 c M).1, (cv59_inp 2 c M).2]
  simp only [heval]
  exact fail78_6600 n hn c hc

/-- **Theorem 4 at `(2,2)`, uniform `D`, every `ε > 0`, failure `≤ 1/100`, every
`n ≥ 3950 + 930/ε²`.** -/
theorem part78_22_eps3 (ε : ℝ) (hε0 : 0 < ε) :
    ∀ n : ℕ, 3950 + 930 / ε ^ 2 ≤ (n : ℝ) → ∃ pg : Prog (In59 n 2 2) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n 2 2 → ℝ, pg.eval v () = g0Q n 2 2 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n 2 2 ε ∧
      ∀ c : Mono n 2 → ℝ, TopNZ 2 c →
        stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
          ε ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
            (BP (uniformSphere n) 2 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  intro n hn
  have hd0 : 0 ≤ 930 / ε ^ 2 := by positivity
  have hn38 : 38 ≤ n := by
    have : ((38 : ℕ) : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  have hn1 : 1 ≤ n := by omega
  obtain ⟨pg, h0, hread, hspec, hcost⟩ := prog59_exists n 2 2 hn1 (by norm_num) (by norm_num)
  refine ⟨pg, h0, hread, hspec, cost_lt_baselineF59 2 ε pg.cost hcost
    ((costG59_lt_twoPp n 2 2 (by norm_num) (by omega)).trans_le (twoPp_le_baselineF n 2 2 ε)),
    ?_⟩
  intro c hc
  have heval : ∀ M : CoefIdxD n 2 → ℝ, pg.eval (inp59 c M) () = g0Q n 2 2 c M := by
    intro M
    rw [hspec, (cv59_inp 2 c M).1, (cv59_inp 2 c M).2]
  simp only [heval]
  exact fail78_eps3 ε hε0 n hn c hc

end BstLean.Part78

#print axioms BstLean.Part78.part78_22_6600
#print axioms BstLean.Part78.part78_22_eps3
#print axioms BstLean.Part78.part78_gauss3
#print axioms BstLean.Part78.part78_cV3
#print axioms BstLean.Part78.part78_varBoundW3
