import BstLean.Part78Final
import BstLean.Part78Deg2
import BstLean.Part78Var3
import BstLean.Part78Mean3

/-!
# Part 78, sharper constants: Theorem 4 at `(2,2)`, uniform `D`, from `n ≥ 9500`, and general `ε`

Two improvements on `Part78Final`:
* the fourth moment at degree two with the constant `35/2` (`deg2Fourth`) in place of `5⁴`;
* the kernel form of the variance bound (`varBoundK`) with the pointwise identity for
  `w(x) = E_W Q_x²` (`wQId`), which replaces `κ(x,x) ≤ 2` by `κ(x,x) = 3/2 + q(x)/2`.

Results:
* `part78_varBoundW2`: `Var(V | u) ≤ c_V · Wf · V̄(u)/n ≤ c_V V̄(u)²/n`,
  `c_V = 4·(1733/1000)·(4184/1000)·(1414/1000) < 41.02` (`n ≥ 1000`).
* `part78_gauss2`: the Gaussian-model theorem with this `c_V`.
* `part78_22_sharp`: Theorem 4 at `(2,2)`, `ε = 1/2`, failure `≤ 1/100`, every `n ≥ 9500`.
* `part78_22_eps`: every `ε > 0`, every `n ≥ 6620 + 1060/ε²`.
-/

namespace BstLean.Part78

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU heavyCount)
open BstLean.Part59

variable {n : ℕ}

lemma wQ_nonneg (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : 0 ≤ wQ a H x := by
  unfold wQ; exact integral_nonneg fun _ => sq_nonneg _

set_option maxHeartbeats 3200000 in
/-- `E_x[(‖a‖² + 4‖H‖²κ(x,x)) w(x)] ≤ 1.414 · Wf · E_W V` (`n ≥ 1000`). -/
lemma kernel_int_le (n : ℕ) (hn : 1000 ≤ n) (hQ : WQId n) (a : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hwc : Continuous (wQ a H))
    (hwm : ∫ x, wQ a H x ∂uniformSphere n = ∫ W, VG a H W ∂stdGauss (WIdx n)) :
    ∫ x, (nsq a + 4 * frobH H * kap x x) * wQ a H x ∂uniformSphere n ≤
      1414 / 1000 * Wf a H * ∫ W, VG a H W ∂stdGauss (WIdx n) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have := BstLean.Part29.uniformSphere_isProbability n hn1
  obtain ⟨htG, hm1, hk1, hk2, hs0, hs2, hk⟩ := part78_sphere n hn
  have hM := part78_meanIds n hn1
  have hfl := floor_le hn (part78_sphere n hn) (by norm_num) hM a H hH
  set m := ∫ W, VG a H W ∂stdGauss (WIdx n) with hm
  set A := nsq a with hA
  set v := frobH H with hv
  set T := trH H with hT
  have hA0 : 0 ≤ A := nsq_nonneg a
  have hv0 : 0 ≤ v := frobH_nonneg H
  have hm0 : 0 ≤ m := le_trans (Wf_nonneg a H) hfl
  have ck : Continuous (fun x : Fin n → ℝ => kap x x) := kap_diag_cont
  have cq : Continuous (q4 (n := n)) := q4_cont
  -- pointwise bound on the sphere
  have hpt : ∀ᵐ x ∂uniformSphere n, (A + 4 * v * kap x x) * wQ a H x ≤
      (A + 6 * v) * wQ a H x +
        2 * v * (q4 x * (2 * A + 2 * v * (4 + ss2 n)) + T ^ 2 * (kap x x - tG n) ^ 2) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    have hkx := kap_diag_sphere x hx
    have hk2' := hk x hx
    have hq0 : 0 ≤ q4 x := Finset.sum_nonneg fun i _ => by positivity
    have hq1 : q4 x ≤ 1 := by linarith
    have hw0 := wQ_nonneg a H x
    have hin := inner_kap hn1 x
    rw [hx] at hin
    have hsq : 0 ≤ ∫ y, kap x y ^ 2 ∂uniformSphere n := integral_nonneg fun _ => sq_nonneg _
    have hwU : wQ a H x ≤ A * kap x x + T ^ 2 * (kap x x - tG n) ^ 2 +
        2 * v * (kap x x ^ 2 + ss2 n) := by
      rw [hQ a H hH x, hin, hm1]
      have h1 : A * (kap x x - 2 * (1 / (n : ℝ)) + 1 / (n : ℝ)) ≤ A * kap x x := by
        apply mul_le_mul_of_nonneg_left _ hA0
        have : 0 ≤ 1 / (n : ℝ) := by positivity
        linarith
      have h2 : 2 * v * (kap x x ^ 2 - 2 * ∫ y, kap x y ^ 2 ∂uniformSphere n + ss2 n) ≤
          2 * v * (kap x x ^ 2 + ss2 n) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    have hk0 : 0 ≤ kap x x := by rw [hkx]; linarith
    have hkk : kap x x ^ 2 ≤ 4 := by nlinarith
    have hT0 : 0 ≤ T ^ 2 * (kap x x - tG n) ^ 2 := by positivity
    -- q · U ≤ q (2A + 2v(4 + ss2)) + T²(κ − tG)²
    have hU1 : A * kap x x + 2 * v * (kap x x ^ 2 + ss2 n) ≤ 2 * A + 2 * v * (4 + ss2 n) := by
      have p1 := mul_nonneg hA0 (sub_nonneg.2 hk2')
      have p2 := mul_nonneg hv0 (sub_nonneg.2 hkk)
      linarith
    have hqU : q4 x * wQ a H x ≤
        q4 x * (2 * A + 2 * v * (4 + ss2 n)) + T ^ 2 * (kap x x - tG n) ^ 2 := by
      have s1 : q4 x * wQ a H x ≤ q4 x * (A * kap x x + T ^ 2 * (kap x x - tG n) ^ 2 +
          2 * v * (kap x x ^ 2 + ss2 n)) := mul_le_mul_of_nonneg_left hwU hq0
      have s2 : q4 x * (A * kap x x + 2 * v * (kap x x ^ 2 + ss2 n)) ≤
          q4 x * (2 * A + 2 * v * (4 + ss2 n)) := mul_le_mul_of_nonneg_left hU1 hq0
      have s3 : q4 x * (T ^ 2 * (kap x x - tG n) ^ 2) ≤ T ^ 2 * (kap x x - tG n) ^ 2 := by
        have := mul_nonneg hT0 (sub_nonneg.2 hq1)
        linarith
      linarith
    have e : (A + 4 * v * kap x x) * wQ a H x =
        (A + 6 * v) * wQ a H x + 2 * v * (q4 x * wQ a H x) := by rw [hkx]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hqU (by linarith : (0 : ℝ) ≤ 2 * v)
    linarith
  -- integrate
  have iw := sph_int hn1 hwc
  have iq := sph_int hn1 cq
  have ik2 : Integrable (fun x : Fin n → ℝ => (kap x x - tG n) ^ 2) (uniformSphere n) :=
    sph_int hn1 ((ck.sub continuous_const).pow 2)
  have hint2 : ∫ x, (kap x x - tG n) ^ 2 ∂uniformSphere n = kk2 n - tG n ^ 2 := by
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
  have hRHS : ∫ x, ((A + 6 * v) * wQ a H x +
      2 * v * (q4 x * (2 * A + 2 * v * (4 + ss2 n)) + T ^ 2 * (kap x x - tG n) ^ 2))
        ∂uniformSphere n =
      (A + 6 * v) * m + 2 * v * ((3 / ((n : ℝ) + 2)) * (2 * A + 2 * v * (4 + ss2 n)) +
        T ^ 2 * (kk2 n - tG n ^ 2)) := by
    rw [integral_add (f := fun x : Fin n → ℝ => (A + 6 * v) * wQ a H x)
        (g := fun x : Fin n → ℝ => 2 * v * (q4 x * (2 * A + 2 * v * (4 + ss2 n)) +
          T ^ 2 * (kap x x - tG n) ^ 2))
        (iw.const_mul _) (((iq.mul_const _).add (ik2.const_mul _)).const_mul _),
      integral_const_mul, integral_const_mul,
      integral_add (f := fun x : Fin n → ℝ => q4 x * (2 * A + 2 * v * (4 + ss2 n)))
        (g := fun x : Fin n → ℝ => T ^ 2 * (kap x x - tG n) ^ 2)
        (iq.mul_const _) (ik2.const_mul _), integral_mul_const, integral_const_mul,
      hwm, integral_q4 hn1, hint2]
  have hLHSi : Integrable (fun x : Fin n → ℝ => (A + 4 * v * kap x x) * wQ a H x)
      (uniformSphere n) :=
    sph_int hn1 ((continuous_const.add (continuous_const.mul ck)).mul hwc)
  have hRHSi : Integrable (fun x : Fin n → ℝ => (A + 6 * v) * wQ a H x +
      2 * v * (q4 x * (2 * A + 2 * v * (4 + ss2 n)) + T ^ 2 * (kap x x - tG n) ^ 2))
      (uniformSphere n) :=
    (iw.const_mul _).add (((iq.mul_const _).add (ik2.const_mul _)).const_mul _)
  have hI := integral_mono_ae hLHSi hRHSi hpt
  rw [hRHS] at hI
  -- numbers
  have hq3 : 3 / ((n : ℝ) + 2) ≤ 3 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hq30 : 0 ≤ 3 / ((n : ℝ) + 2) := by positivity
  have hss : ss2 n ≤ 1 / 100 := by
    refine hs2.trans ?_
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
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
  have hbr : (3 / ((n : ℝ) + 2)) * (2 * A + 2 * v * (4 + ss2 n)) + T ^ 2 * (kk2 n - tG n ^ 2) ≤
      6 / 1000 * A + 775 / 1000 * v := by
    have h1 : 2 * A + 2 * v * (4 + ss2 n) ≤ 2 * A + 802 / 100 * v := by nlinarith
    have h10 : 0 ≤ 2 * A + 2 * v * (4 + ss2 n) := by nlinarith
    have h2 : (3 / ((n : ℝ) + 2)) * (2 * A + 2 * v * (4 + ss2 n)) ≤
        3 / 1000 * (2 * A + 802 / 100 * v) :=
      mul_le_mul hq3 h1 h10 (by norm_num)
    linarith
  have hWm : Wf a H ≤ m := hfl
  have hvm : 449 / 100 * v ≤ m := by
    have : 449 / 100 * v ≤ Wf a H := by unfold Wf; nlinarith
    linarith
  have hfin : ∫ x, (A + 4 * v * kap x x) * wQ a H x ∂uniformSphere n ≤
      1414 / 1000 * Wf a H * m := by
    refine hI.trans ?_
    have b1 : 2 * v * ((3 / ((n : ℝ) + 2)) * (2 * A + 2 * v * (4 + ss2 n)) +
        T ^ 2 * (kk2 n - tG n ^ 2)) ≤ 2 * v * (6 / 1000 * A + 775 / 1000 * v) :=
      mul_le_mul_of_nonneg_left hbr (by linarith)
    -- 2v(0.006A + 0.775v) ≤ (0.0027A + 0.3453v) m
    have b2 : 2 * v * (6 / 1000 * A + 775 / 1000 * v) ≤ (27 / 10000 * A + 3453 / 10000 * v) * m := by
      have c1 : 0 ≤ 12 / 1000 * A + 1550 / 1000 * v := by positivity
      have := mul_le_mul_of_nonneg_left hvm c1
      nlinarith
    have b3 : (A + 6 * v) * m + (27 / 10000 * A + 3453 / 10000 * v) * m ≤
        1414 / 1000 * Wf a H * m := by
      have : A + 6 * v + (27 / 10000 * A + 3453 / 10000 * v) ≤ 1414 / 1000 * Wf a H := by
        unfold Wf; nlinarith
      nlinarith [mul_le_mul_of_nonneg_right this hm0]
    linarith
  exact hfin

/-- From the kernel form to the floor form. -/
theorem varBoundW_of_K (n : ℕ) (hn : 1000 ≤ n) {c : ℝ} (hc : 0 ≤ c) (hK : VarBoundK n c)
    (hQ : WQId n) : VarBoundW n (c * (1414 / 1000)) := by
  intro a H hH
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hwc, hwm, hvar⟩ := hK a H hH
  have hfin := kernel_int_le n hn hQ a H hH hwc hwm
  refine hvar.trans ?_
  have hcn : 0 ≤ c / (n : ℝ) := div_nonneg hc hnpos.le
  refine (mul_le_mul_of_nonneg_left hfin hcn).trans (le_of_eq ?_)
  ring

theorem part78_varBoundK (n : ℕ) (hn : 1 ≤ n) :
    VarBoundK n (4 * 1 * (1733 / 1000) * (4184 / 1000)) :=
  varBoundK n hn 1 3 (1733 / 1000) (35 / 2) (4184 / 1000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) poincareMv (featOp1 n hn) affFourth3 deg2Fourth
    gaussLin

/-- **`Var(V | u) ≤ c_V · Wf · V̄(u)/n`** with `c_V = 4·1.733·4.184·1.414 < 41.02`, `n ≥ 1000`. -/
theorem part78_varBoundW2 (n : ℕ) (hn : 1000 ≤ n) :
    VarBoundW n (4 * 1 * (1733 / 1000) * (4184 / 1000) * (1414 / 1000)) :=
  varBoundW_of_K n hn (by norm_num) (part78_varBoundK n (by omega))
    (wQId n (by omega) wickTwoPoint)

/-- **`Var(V | u) ≤ c_V V̄(u)²/n` with `c_V = 4102/100`**, `n ≥ 1000`. -/
theorem part78_cV2 (n : ℕ) (hn : 1000 ≤ n) (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsSymm) :
    ∫ W, (VG a H W - ∫ W', VG a H W' ∂stdGauss (WIdx n)) ^ 2 ∂stdGauss (WIdx n) ≤
      (4102 / 100) / n * (∫ W, VG a H W ∂stdGauss (WIdx n)) ^ 2 := by
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hfl := floor_le hn (part78_sphere n hn) (by norm_num) (part78_meanIds n (by omega)) a H hH
  set m := ∫ W, VG a H W ∂stdGauss (WIdx n)
  have hm0 : 0 ≤ m := le_trans (Wf_nonneg a H) hfl
  refine (part78_varBoundW2 n hn a H hH).trans ?_
  have h1 : (4 * 1 * (1733 / 1000) * (4184 / 1000) * (1414 / 1000) : ℝ) / n ≤ (4102 / 100) / n :=
    div_le_div_of_nonneg_right (by norm_num) hnpos.le
  have h2 : (4 * 1 * (1733 / 1000) * (4184 / 1000) * (1414 / 1000) : ℝ) / n * Wf a H * m ≤
      (4102 / 100) / n * m * m :=
    mul_le_mul_of_nonneg_right (mul_le_mul h1 hfl (Wf_nonneg a H) (by positivity)) hm0
  refine h2.trans (le_of_eq ?_)
  ring

/-- **The Gaussian-model theorem, given the constant column**, sharper constants (`n ≥ 1000`):
failure `≤ c₁/(n ε² κ) + c_V/(n (1−κ)²)`, `c₁ = 19/20`, `c_V < 41.02`, `κ = 1 − θ`. -/
theorem part78_gauss2 (n : ℕ) (hn : 1000 ≤ n) (κ ε : ℝ) (hκ0 : 0 < κ) (hκ : κ < 1) (hε : 0 < ε)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hpos : 0 < frobH H) :
    stdGauss (WIdx n) {W | ε ^ 2 * VG a H W < errG a H W ^ 2} ≤
      ENNReal.ofReal (19 / 20 / (n * (ε ^ 2 * κ)) +
        4 * 1 * (1733 / 1000) * (4184 / 1000) * (1414 / 1000) / (n * (1 - κ) ^ 2)) :=
  gauss_model hn (part78_sphere n hn) (by norm_num) (part78_meanIds n (by omega))
    (part78_varBoundW2 n hn) (by norm_num) (by norm_num) (by norm_num) hκ0 hκ hε a H hH hpos

/-- Failure `≤ 1/100` at `ε = 1/2` for every `n ≥ 9500`. -/
theorem fail78_sharp (n : ℕ) (hn : 9500 ≤ n) (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
      (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n 2 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal (1 / 100) := by
  have hn' : (9500 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx : 1 / (n : ℝ) ≤ 1 / 9500 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have hx' : (n : ℝ)⁻¹ ≤ 1 / 9500 := by rw [← one_div]; exact hx
  refine (fail78_core n (by omega) (cW := 4 * 1 * (1733 / 1000) * (4184 / 1000) * (1414 / 1000))
    (κ := 9 / 50) (ε := 1 / 2) (ε₁ := 1827 / 10000) (lam := 3 / 100) (t := 8)
    (part78_varBoundW2 n (by omega)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; linarith) c hc).trans (ENNReal.ofReal_le_ofReal ?_)
  norm_num
  linarith

/-- Failure `≤ 1/100` for every `ε > 0` and every `n ≥ 6620 + 1060/ε²`. -/
theorem fail78_eps (ε : ℝ) (hε0 : 0 < ε) (n : ℕ)
    (hn : 6620 + 1060 / ε ^ 2 ≤ (n : ℝ)) (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
      ε ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n 2 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal (1 / 100) := by
  have he2 : 0 < ε ^ 2 := by positivity
  have hd0 : 0 ≤ 1060 / ε ^ 2 := by positivity
  have hnR : (6620 : ℝ) ≤ n := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hn1000 : 1000 ≤ n := by
    have : ((1000 : ℕ) : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx1 : 1 / (n : ℝ) ≤ 1 / 6620 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have hx2 : 1 / (n : ℝ) ≤ ε ^ 2 / 1060 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]
    have : 1060 / ε ^ 2 ≤ (n : ℝ) := by linarith
    rw [div_le_iff₀ he2] at this
    linarith
  refine (fail78_core n hn1000 (cW := 4 * 1 * (1733 / 1000) * (4184 / 1000) * (1414 / 1000))
    (κ := 9 / 50) (ε := ε) (ε₁ := 3 / 10 * ε) (lam := 3 / 100) (t := 10)
    (part78_varBoundW2 n hn1000) (by norm_num)
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by norm_num) (by norm_num)
    ?_ c hc).trans (ENNReal.ofReal_le_ofReal ?_)
  · have h3 := mul_le_mul_of_nonneg_left hx1 he2.le
    nlinarith
  · have e : (19 / 20 : ℝ) / (3 / 10 * ε) ^ 2 = 95 / 9 / ε ^ 2 := by
      field_simp; ring
    rw [e]
    have hY : 95 / 9 / ε ^ 2 ≤ 1060 / 100 / ε ^ 2 :=
      div_le_div_of_nonneg_right (by norm_num) he2.le
    have hsum : (4 + 95 / 9 / ε ^ 2 +
        4 * 1 * (1733 / 1000) * (4184 / 1000) * (1414 / 1000) / (1 - 9 / 50) ^ 2 +
        567 / 50 / 10 + 1 / 100 : ℝ) ≤ (n : ℝ) / 100 := by
      have : (1060 : ℝ) / 100 / ε ^ 2 = 1060 / ε ^ 2 / 100 := by ring
      norm_num at this ⊢
      linarith
    have := mul_le_mul_of_nonneg_right hsum hx0.le
    refine this.trans (le_of_eq ?_)
    field_simp

/-- **Theorem 4 at `(d_M, d_f) = (2,2)`, uniform `D`, `ε = 1/2`, failure `≤ 1/100`, every
`n ≥ 9500`.** The statement of `Part59.part59_general` at `(2,2)` with `μ = uniformSphere n`. -/
theorem part78_22_sharp :
    ∀ n : ℕ, 9500 ≤ n → ∃ pg : Prog (In59 n 2 2) Unit,
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
  exact fail78_sharp n hn c hc

/-- **Theorem 4 at `(2,2)`, uniform `D`, every `ε > 0`, failure `≤ 1/100`, every
`n ≥ 6620 + 1060/ε²`.** -/
theorem part78_22_eps (ε : ℝ) (hε0 : 0 < ε) :
    ∀ n : ℕ, 6620 + 1060 / ε ^ 2 ≤ (n : ℝ) → ∃ pg : Prog (In59 n 2 2) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n 2 2 → ℝ, pg.eval v () = g0Q n 2 2 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n 2 2 ε ∧
      ∀ c : Mono n 2 → ℝ, TopNZ 2 c →
        stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
          ε ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
            (BP (uniformSphere n) 2 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  intro n hn
  have hd0 : 0 ≤ 1060 / ε ^ 2 := by positivity
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
  exact fail78_eps ε hε0 n hn c hc

end BstLean.Part78

#print axioms BstLean.Part78.part78_22_sharp
#print axioms BstLean.Part78.part78_22_eps
#print axioms BstLean.Part78.part78_gauss2
#print axioms BstLean.Part78.part78_cV2
#print axioms BstLean.Part78.part78_varBoundW2
