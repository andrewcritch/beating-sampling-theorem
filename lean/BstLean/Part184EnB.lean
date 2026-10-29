import BstLean.Part184Def
import BstLean.Part183EnJ
import BstLean.Part184Row
import BstLean.Part184Core
import BstLean.Part162Gm

/-!
# Part 184 (file `EnB`): the energy fluctuation bound of the row moment expansion, PROVED

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, Lemma `t7:p08:BE` (Bernstein energy fluctuation). Lean proves the
eighth-moment form: given `A₁` and the plane coordinates, the energy fluctuation is a sum of `m`
independent centred row terms; the moment expansion (file `Mom`) bounds its eighth moment by
`105·S₂⁴ + …`, the sharp Gaussian Poincaré inequality bounds `S₂` per row (file `Row`), and the
higher row moments only enter through terms of relative size `O(1/m)`.

* `Wr`, `WrS`: the row energies `E_v((M(a(v) − ā))_j)²` of the whole matrix and their power sums.
* `MplS`, `PlS`, `plane_tot`, `plane_tot3`, `dbl_comb2`: the plane split for matrix functionals.
* `WgR_Mpl`: the row energy of the core lemma is the row energy of the whole matrix.
* `num_t2`, `num_t3`, `num_sqrt`, **`enb_closure`**: the numeric closure (`n ≥ 16 000`, `q ≥ 1/10`):
  `107.59·1.001⁸ + 0.17 + 0.001 + 0.14 ≤ 1.81⁸`.
* **`exWn_mom_B_of`**, **`EnB_proved : EnB_stmt`**.
-/

namespace BstLean.Part184

open MeasureTheory ProbabilityTheory Real Matrix Filter Topology
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part170
open BstLean.Part134 (res lam projPerp)
open BstLean.Part162 (gmom gmom_nonneg)
open BstLean.Part183 (Qvar)

section numeric

lemma gmom8_eq : gmom 8 = 105 := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num, BstLean.Part162.gmom_even]
  simp [Finset.prod_range_succ]; norm_num

lemma gmom12_eq : gmom 12 = 10395 := by
  rw [show (12 : ℕ) = 2 * 6 by norm_num, BstLean.Part162.gmom_even]
  simp [Finset.prod_range_succ]; norm_num

lemma pi2_8 : (π / 2) ^ 8 ≤ 38 := by
  have h1 : π < 3.1416 := Real.pi_lt_d4
  have : π / 2 ≤ 1.5708 := by linarith
  calc (π / 2) ^ 8 ≤ 1.5708 ^ 8 := pow_le_pow_left₀ (by positivity) this 8
    _ ≤ 38 := by norm_num

lemma pi2_12 : (π / 2) ^ 12 ≤ 227 := by
  have h1 : π < 3.1416 := Real.pi_lt_d4
  have : π / 2 ≤ 1.5708 := by linarith
  calc (π / 2) ^ 12 ≤ 1.5708 ^ 12 := pow_le_pow_left₀ (by positivity) this 12
    _ ≤ 227 := by norm_num

lemma num_t2 {m t u T T' P x : ℝ} (hm : 1 ≤ m) (ht : 0 ≤ t) (hu : 0 ≤ u) (huT : u ≤ 10 * T)
    (hT0 : 0 ≤ T') (hT' : T' ≤ T) (hP : 0 ≤ P) (hx : 16000 ≤ x)
    (hmt : m * m * t ^ 4 = 16 / x ^ 4) :
    (24563 * m + 1) * ((π / 2) ^ 8 * 105) * P * (m * (105 * t ^ 4 * (4 * u) ^ 3 * T')) ≤
      17 / 100 * P * T ^ 4 := by
  have hT : 0 ≤ T := hT0.trans hT'
  have hk : 24563 * m + 1 ≤ 24564 * m := by linarith
  have hu3 : (4 * u) ^ 3 ≤ (40 * T) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hx4 : (16000 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) hx 4
  have hx0 : 0 < x ^ 4 := by positivity
  have hp := pi2_8
  calc (24563 * m + 1) * ((π / 2) ^ 8 * 105) * P * (m * (105 * t ^ 4 * (4 * u) ^ 3 * T'))
      ≤ 24564 * m * (38 * 105) * P * (m * (105 * t ^ 4 * (40 * T) ^ 3 * T)) := by
        gcongr
    _ = 24564 * (38 * 105) * 105 * 64000 * (P * T ^ 4) * (m * m * t ^ 4) := by ring
    _ = 24564 * (38 * 105) * 105 * 64000 * 16 * (P * T ^ 4) / x ^ 4 := by rw [hmt]; ring
    _ ≤ 17 / 100 * P * T ^ 4 := by
        rw [div_le_iff₀ hx0]
        have : 0 ≤ P * T ^ 4 := by positivity
        nlinarith

lemma num_t3 {m t u T T' P x : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (huT : u ≤ 10 * T)
    (hT0 : 0 ≤ T') (hT' : T' ≤ T) (hTp : 0 < T) (hP : 0 ≤ P) (hx : 16000 ≤ x) (hm0 : 0 ≤ m)
    (hmt : m * m * t ^ 6 = 64 / x ^ 8) :
    2800 * m * ((π / 2) ^ 12 * 10395) * (P / T ^ 2) * (m * (10395 * t ^ 6 * (4 * u) ^ 5 * T')) ≤
      1 / 1000 * P * T ^ 4 := by
  have hu5 : (4 * u) ^ 5 ≤ (40 * T) ^ 5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
  have hx8 : (16000 : ℝ) ^ 8 ≤ x ^ 8 := pow_le_pow_left₀ (by norm_num) hx 8
  have hx0 : 0 < x ^ 8 := by positivity
  have hp := pi2_12
  calc 2800 * m * ((π / 2) ^ 12 * 10395) * (P / T ^ 2) * (m * (10395 * t ^ 6 * (4 * u) ^ 5 * T'))
      ≤ 2800 * m * (227 * 10395) * (P / T ^ 2) * (m * (10395 * t ^ 6 * (40 * T) ^ 5 * T)) := by
        gcongr
    _ = 2800 * (227 * 10395) * 10395 * 40 ^ 5 * (P * T ^ 4) * (m * m * t ^ 6) := by
        field_simp
    _ = 2800 * (227 * 10395) * 10395 * 40 ^ 5 * 64 * (P * T ^ 4) / x ^ 8 := by rw [hmt]; ring
    _ ≤ 1 / 1000 * P * T ^ 4 := by
        rw [div_le_iff₀ hx0]
        have : 0 ≤ P * T ^ 4 := by positivity
        nlinarith

lemma num_sqrt {t u T : ℝ} (hT : 0 ≤ T) (h : t * u ≤ 1 / 10 ^ 7 * T) :
    π / 2 * (18 / 10) * √(t * u) ≤ 1 / 1000 * √T := by
  have h1 : π < 3.1416 := Real.pi_lt_d4
  have h2 : √(t * u) ≤ √(1 / 10 ^ 7 * T) := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 7)] at h2
  have h3 : √(1 / 10 ^ 7 : ℝ) ≤ 1 / 3162 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h4 : 0 ≤ √T := Real.sqrt_nonneg _
  have h5 : π / 2 * (18 / 10) ≤ 2828 / 1000 := by linarith
  have h6 : √(t * u) ≤ 1 / 3162 * √T := h2.trans (mul_le_mul_of_nonneg_right h3 h4)
  have h7 : 0 ≤ √(t * u) := Real.sqrt_nonneg _
  calc π / 2 * (18 / 10) * √(t * u) ≤ 2828 / 1000 * (1 / 3162 * √T) := by
        have : 0 ≤ π / 2 * (18 / 10) := by positivity
        exact mul_le_mul h5 h6 h7 (by norm_num)
    _ ≤ 1 / 1000 * √T := by nlinarith

/-- **The numeric closure of the row moment expansion** (`n ≥ 16 000`, `q ≥ 1/10`). -/
lemma enb_closure {n : ℕ} (hn : 16000 ≤ n) {O q : ℝ} (hO : 0 < O) (hq1 : 1 / 10 ≤ q) {T' : ℝ}
    (hT0 : 0 ≤ T') (hT : T' ≤ q * n * O ^ 2 / ((n : ℝ) - 2)) :
    10759 / 100 * (4 * (tA n * (q * O ^ 2 / ((n : ℝ) - 2)))) ^ 4 *
        (√((mA n : ℝ) * tA n * (q * n * O ^ 2 / ((n : ℝ) - 2)) / 2) +
          π / 2 * (18 / 10) * √(tA n * O ^ 2)) ^ 8 +
      (24563 * (mA n : ℝ) + 1) * ((π / 2) ^ 8 * gmom 8) *
          (4 * (tA n * (q * O ^ 2 / ((n : ℝ) - 2)))) ^ 4 *
        ((mA n : ℝ) * (gmom 8 * tA n ^ 4 * (4 * O ^ 2) ^ 3 * T')) +
      2800 * (mA n : ℝ) * ((π / 2) ^ 12 * gmom 12) *
          (4 * (tA n * (q * O ^ 2 / ((n : ℝ) - 2)))) ^ 6 /
          (4 * (tA n * (q * O ^ 2 / ((n : ℝ) - 2))) * (q * n * O ^ 2 / ((n : ℝ) - 2))) ^ 2 *
        ((mA n : ℝ) * (gmom 12 * tA n ^ 6 * (4 * O ^ 2) ^ 5 * T')) +
      14 / 100 * (4 * (tA n * (q * O ^ 2 / ((n : ℝ) - 2))) *
        (q * n * O ^ 2 / ((n : ℝ) - 2))) ^ 4 ≤ WflB n O q ^ 8 := by
  have hq0 : 0 < q := by linarith
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (16000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have htA : 0 < tA n := by
    unfold tA; have : 0 < mA n := by unfold mA; positivity
    positivity
  set Λ := q * O ^ 2 / ((n : ℝ) - 2) with hΛd
  set Tq := q * n * O ^ 2 / ((n : ℝ) - 2) with hTqd
  have hΛ0 : 0 < Λ := by positivity
  have hTq0 : 0 < Tq := by positivity
  set σ := 4 * (tA n * Λ) * Tq with hσd
  set K1 := 10759 / 100 * (4 * (tA n * Λ)) ^ 4 with hK1
  set K2 := (24563 * (mA n : ℝ) + 1) * ((π / 2) ^ 8 * gmom 8) * (4 * (tA n * Λ)) ^ 4 with hK2d
  set K3 := 2800 * (mA n : ℝ) * ((π / 2) ^ 12 * gmom 12) * (4 * (tA n * Λ)) ^ 6 / σ ^ 2 with hK3
  set K0 := 14 / 100 * σ ^ 4 with hK0
  set A := WflB n O q with hAd
  have hx : (16000 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have ht : tA n = 2 / (n : ℝ) ^ 2 := by unfold tA; rw [show ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 from hm]
  have hn0 : (0 : ℝ) < n := by linarith
  have hm1 : (1 : ℝ) ≤ mA n := by rw [hm]; nlinarith
  have hmt : (mA n : ℝ) * tA n = 2 := by rw [hm, ht]; field_simp
  have hmt4 : (mA n : ℝ) * (mA n : ℝ) * tA n ^ 4 = 16 / (n : ℝ) ^ 4 := by
    rw [hm, ht]; field_simp; ring
  have hmt6 : (mA n : ℝ) * (mA n : ℝ) * tA n ^ 6 = 64 / (n : ℝ) ^ 8 := by
    rw [hm, ht]; field_simp; ring
  have huT : O ^ 2 ≤ 10 * Tq := by
    have h1 : O ^ 2 * ((n : ℝ) - 2) ≤ 10 * (q * n * O ^ 2) := by
      have h3 := mul_le_mul_of_nonneg_right hq1 (by positivity : (0 : ℝ) ≤ (n : ℝ) * O ^ 2)
      have h4 : 0 ≤ O ^ 2 := sq_nonneg O
      nlinarith
    rw [hTqd, show 10 * (q * n * O ^ 2 / ((n : ℝ) - 2)) = 10 * (q * n * O ^ 2) / ((n : ℝ) - 2)
      by ring, le_div_iff₀ h2n]
    exact h1
  have hTT : T' ≤ Tq := hT
  set P := (4 * (tA n * Λ)) ^ 4 with hPd
  have hP0 : 0 ≤ P := by positivity
  -- term 1
  have hsT : √((mA n : ℝ) * tA n * Tq / 2) = √Tq := by rw [hmt]; congr 1; ring
  have htu : tA n * O ^ 2 ≤ 1 / 10 ^ 7 * Tq := by
    rw [ht]
    have h1 : 2 / (n : ℝ) ^ 2 * O ^ 2 ≤ 2 / 16000 ^ 2 * O ^ 2 := by
      gcongr
    have hc0 : (2 : ℝ) / 16000 ^ 2 ≤ 1 / 10 ^ 7 / 10 := by norm_num
    have h2 : 2 / (16000 : ℝ) ^ 2 * O ^ 2 ≤ 1 / 10 ^ 7 / 10 * O ^ 2 :=
      mul_le_mul_of_nonneg_right hc0 (sq_nonneg O)
    linarith
  have hc := num_sqrt hTq0.le htu
  have hY8 : (√((mA n : ℝ) * tA n * Tq / 2) + π / 2 * (18 / 10) * √(tA n * O ^ 2)) ^ 8 ≤
      (1001 / 1000) ^ 8 * Tq ^ 4 := by
    rw [hsT]
    have h0 : 0 ≤ π / 2 * (18 / 10) * √(tA n * O ^ 2) := by positivity
    have h1 : √Tq + π / 2 * (18 / 10) * √(tA n * O ^ 2) ≤ 1001 / 1000 * √Tq := by linarith
    calc (√Tq + π / 2 * (18 / 10) * √(tA n * O ^ 2)) ^ 8 ≤ (1001 / 1000 * √Tq) ^ 8 :=
          pow_le_pow_left₀ (by positivity) h1 8
      _ = (1001 / 1000) ^ 8 * (√Tq ^ 2) ^ 4 := by ring
      _ = (1001 / 1000) ^ 8 * Tq ^ 4 := by rw [Real.sq_sqrt hTq0.le]
  have e1 : K1 * (√((mA n : ℝ) * tA n * Tq / 2) + π / 2 * (18 / 10) * √(tA n * O ^ 2)) ^ 8 ≤
      10759 / 100 * (1001 / 1000) ^ 8 * (P * Tq ^ 4) := by
    have := mul_le_mul_of_nonneg_left hY8 (by positivity : (0 : ℝ) ≤ K1)
    rw [hK1] at this ⊢
    nlinarith
  -- term 2
  have e2 : K2 * ((mA n : ℝ) * (gmom 8 * tA n ^ 4 * (4 * O ^ 2) ^ 3 * T')) ≤
      17 / 100 * P * Tq ^ 4 := by
    rw [hK2d, gmom8_eq]
    exact num_t2 hm1 htA.le (sq_nonneg O) huT hT0 hTT hP0 hx hmt4
  -- term 3
  have e3 : K3 * ((mA n : ℝ) * (gmom 12 * tA n ^ 6 * (4 * O ^ 2) ^ 5 * T')) ≤
      1 / 1000 * P * Tq ^ 4 := by
    have eK : K3 = 2800 * (mA n : ℝ) * ((π / 2) ^ 12 * 10395) * (P / Tq ^ 2) := by
      rw [hK3, gmom12_eq, hσd, hPd]
      have : 4 * (tA n * Λ) ≠ 0 := (mul_pos (by norm_num) (mul_pos htA hΛ0)).ne'
      field_simp
    rw [eK, gmom12_eq]
    exact num_t3 htA.le (sq_nonneg O) huT hT0 hTT hTq0 hP0 hx (by positivity) hmt6
  -- term 4
  have e4 : K0 = 14 / 100 * (P * Tq ^ 4) := by rw [hK0, hσd, hPd]; ring
  -- the target
  have hA8 : A ^ 8 = (181 / 100) ^ 8 * (P * Tq ^ 4) := by
    rw [hAd]
    unfold WflB
    rw [← hΛd, ← hTqd, hsT]
    have e : (2 * (181 / 100 * √(tA n * Λ)) * √Tq) ^ 8 =
        (181 / 100) ^ 8 * (2 ^ 2 * √(tA n * Λ) ^ 2) ^ 4 * (√Tq ^ 2) ^ 4 := by ring
    rw [e, Real.sq_sqrt (by positivity), Real.sq_sqrt hTq0.le, hPd]
    ring
  have hfin : 10759 / 100 * (1001 / 1000 : ℝ) ^ 8 + 17 / 100 + 1 / 1000 + 14 / 100 ≤
      (181 / 100) ^ 8 := by norm_num
  have hPT : 0 ≤ P * Tq ^ 4 := by positivity
  rw [hA8, e4]
  have hfx := mul_le_mul_of_nonneg_right hfin hPT
  linarith [e1, e2, e3]

end numeric

section meas
variable {m : ℕ} {V : Type*} [MeasurableSpace V] {μ : Measure V} [SFinite μ]

/-- The row energy of the centred array: `Wr j M = E_v ((M(a(v) − ā))_j)²`. -/
noncomputable def Wr (μ : Measure V) (a : V → Fin m → ℝ) (j : Fin m)
    (M : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∫ v, ((M *ᵥ (a v - vmean μ a)) j) ^ 2 ∂μ

/-- `Σ_j Wr_j(M)^p`. -/
noncomputable def WrS (μ : Measure V) (a : V → Fin m → ℝ) (p : ℕ)
    (M : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∑ j, Wr μ a j M ^ p

lemma measurable_Wr {a : V → Fin m → ℝ} (ha : Measurable a) (j : Fin m) :
    Measurable (fun M : Matrix (Fin m) (Fin m) ℝ => Wr μ a j M) := by
  unfold Wr
  have c1 : Continuous (fun p : Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) => ((p.1 *ᵥ p.2) j) ^ 2) :=
    ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_fst continuous_snd)).pow 2
  have m1 : Measurable (fun p : Matrix (Fin m) (Fin m) ℝ × V =>
      ((p.1 *ᵥ (a p.2 - vmean μ a)) j) ^ 2) :=
    c1.measurable.comp (measurable_fst.prodMk ((ha.comp measurable_snd).sub_const _))
  exact (m1.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma measurable_WrS {a : V → Fin m → ℝ} (ha : Measurable a) (p : ℕ) :
    Measurable (fun M : Matrix (Fin m) (Fin m) ℝ => WrS μ a p M) := by
  unfold WrS
  exact Finset.measurable_sum _ fun j _ => (measurable_Wr (μ := μ) ha j).pow_const p

end meas



section net
open BstLean.Part157 BstLean.Part169
open BstLean.Part157 (cOf reb)
variable {n : ℕ}

/-- The plane split for a measurable matrix functional. -/
lemma plane_tot (c : Ret n) (s : ℝ) {G : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ N, G (reb (hB c) (cOf (tA n) (hB c) ξ₁) (reb (res (hB c) (a1Bar c s))
        (cOf (tA n) (res (hB c) (a1Bar c s)) ξ₂) N)) ∂gaussMat (mA n) (mA n) (tA n)
        ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) =
      ∫⁻ M, G M ∂gaussMat (mA n) (mA n) (tA n) := by
  have mFQ : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => G p.2.2) := hG.comp (measurable_snd.comp measurable_snd)
  exact (BstLean.Part167.plane_split (q := mA n) (tA n) (hB c) (a1Bar c s) mFQ).symm

lemma measurable_plane (c : Ret n) (s : ℝ) {G : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ≥0∞}
    (hG : Measurable G) :
    Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) => ∫⁻ N, G (reb (hB c)
      (cOf (tA n) (hB c) p.1) (reb (res (hB c) (a1Bar c s))
        (cOf (tA n) (res (hB c) (a1Bar c s)) p.2) N)) ∂gaussMat (mA n) (mA n) (tA n)) := by
  have : Measurable (fun p : ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => G (reb (hB c) (cOf (tA n) (hB c) p.1.1)
        (reb (res (hB c) (a1Bar c s)) (cOf (tA n) (res (hB c) (a1Bar c s)) p.1.2) p.2))) :=
    hG.comp (BstLean.Part157.measurable_reb_comp measurable_const
      (BstLean.Part157.measurable_cOf_comp (tA n) measurable_const
        (measurable_fst.comp measurable_fst))
      (BstLean.Part157.measurable_reb_comp measurable_const
        (BstLean.Part157.measurable_cOf_comp (tA n) measurable_const
          (measurable_snd.comp measurable_fst)) measurable_snd))
  exact this.lintegral_prod_right'

/-- The plane-split matrix. -/
noncomputable def MplS (c : Ret n) (s : ℝ) (ξ₁ ξ₂ : Fin (mA n) → ℝ)
    (N : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) : Matrix (Fin (mA n)) (Fin (mA n)) ℝ :=
  reb (hB c) (cOf (tA n) (hB c) ξ₁) (reb (res (hB c) (a1Bar c s))
    (cOf (tA n) (res (hB c) (a1Bar c s)) ξ₂) N)

/-- The inner integral of a matrix functional at fixed plane coordinates. -/
noncomputable def PlS (c : Ret n) (s : ℝ) (G : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ≥0∞)
    (ξ₁ ξ₂ : Fin (mA n) → ℝ) : ℝ≥0∞ :=
  ∫⁻ N, G (MplS c s ξ₁ ξ₂ N) ∂gaussMat (mA n) (mA n) (tA n)

lemma measurable_PlS (c : Ret n) (s : ℝ) {G : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ≥0∞}
    (hG : Measurable G) : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) =>
      PlS c s G p.1 p.2) :=
  measurable_plane c s hG

lemma PlS_tot (c : Ret n) (s : ℝ) {G : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, PlS c s G ξ₁ ξ₂ ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) =
      ∫⁻ M, G M ∂gaussMat (mA n) (mA n) (tA n) :=
  plane_tot c s hG

/-- A double integral of a combination of jointly measurable functions. -/
lemma dbl_comb {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    {f₁ f₂ f₃ : α × α → ℝ≥0∞} (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃)
    (k₁ k₂ k₃ k₀ : ℝ≥0∞) :
    ∫⁻ x, ∫⁻ y, (k₁ * f₁ (x, y) + k₂ * f₂ (x, y) + k₃ * f₃ (x, y) + k₀) ∂ν ∂ν =
      k₁ * ∫⁻ x, ∫⁻ y, f₁ (x, y) ∂ν ∂ν + k₂ * ∫⁻ x, ∫⁻ y, f₂ (x, y) ∂ν ∂ν +
        k₃ * ∫⁻ x, ∫⁻ y, f₃ (x, y) ∂ν ∂ν + k₀ := by
  have e : ∀ x, ∫⁻ y, (k₁ * f₁ (x, y) + k₂ * f₂ (x, y) + k₃ * f₃ (x, y) + k₀) ∂ν =
      k₁ * ∫⁻ y, f₁ (x, y) ∂ν + k₂ * ∫⁻ y, f₂ (x, y) ∂ν + k₃ * ∫⁻ y, f₃ (x, y) ∂ν + k₀ := by
    intro x
    have a₁ : Measurable (fun y => f₁ (x, y)) := h₁.comp (measurable_const.prodMk measurable_id)
    have a₂ : Measurable (fun y => f₂ (x, y)) := h₂.comp (measurable_const.prodMk measurable_id)
    have a₃ : Measurable (fun y => f₃ (x, y)) := h₃.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_add_right _ measurable_const, lintegral_add_right _ (a₃.const_mul k₃),
      lintegral_add_right _ (a₂.const_mul k₂), lintegral_const_mul _ a₁,
      lintegral_const_mul _ a₂, lintegral_const_mul _ a₃, lintegral_const, measure_univ, mul_one]
  simp_rw [e]
  have b₁ := h₁.lintegral_prod_right' (ν := ν)
  have b₂ := h₂.lintegral_prod_right' (ν := ν)
  have b₃ := h₃.lintegral_prod_right' (ν := ν)
  rw [lintegral_add_right _ measurable_const, lintegral_add_right _ (b₃.const_mul k₃),
    lintegral_add_right _ (b₂.const_mul k₂), lintegral_const_mul _ b₁,
    lintegral_const_mul _ b₂, lintegral_const_mul _ b₃, lintegral_const, measure_univ, mul_one]


/-- A double integral of `k₁ f + k₂ g` with `f` jointly measurable. -/
lemma dbl_comb2 {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    {f : α → α → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) (g : α → α → ℝ≥0∞)
    (k₁ k₂ : ℝ≥0∞) (hk₂ : k₂ ≠ ⊤) :
    ∫⁻ x, ∫⁻ y, (k₁ * f x y + k₂ * g x y) ∂ν ∂ν =
      k₁ * ∫⁻ x, ∫⁻ y, f x y ∂ν ∂ν + k₂ * ∫⁻ x, ∫⁻ y, g x y ∂ν ∂ν := by
  have hf1 : ∀ x, Measurable (f x) := fun x =>
    hf.comp (measurable_const.prodMk measurable_id)
  have e : ∀ x, ∫⁻ y, (k₁ * f x y + k₂ * g x y) ∂ν =
      k₁ * ∫⁻ y, f x y ∂ν + k₂ * ∫⁻ y, g x y ∂ν := by
    intro x
    rw [lintegral_add_left ((hf1 x).const_mul k₁), lintegral_const_mul _ (hf1 x),
      lintegral_const_mul' _ _ hk₂]
  simp_rw [e]
  have hm : Measurable (fun x => ∫⁻ y, f x y ∂ν) := hf.lintegral_prod_right'
  rw [lintegral_add_left (hm.const_mul k₁), lintegral_const_mul _ hm,
    lintegral_const_mul' _ _ hk₂]

/-- The outer integral of three plane-split functionals and a constant. -/
lemma plane_tot3 (c : Ret n) (s : ℝ) {G₁ G₂ G₃ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ≥0∞}
    (h₁ : Measurable G₁) (h₂ : Measurable G₂) (h₃ : Measurable G₃) (k₁ k₂ k₃ k₀ : ℝ≥0∞) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, (k₁ * PlS c s G₁ ξ₁ ξ₂ + k₂ * PlS c s G₂ ξ₁ ξ₂ + k₃ * PlS c s G₃ ξ₁ ξ₂ + k₀)
        ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) =
      k₁ * ∫⁻ M, G₁ M ∂gaussMat (mA n) (mA n) (tA n) +
        k₂ * ∫⁻ M, G₂ M ∂gaussMat (mA n) (mA n) (tA n) +
        k₃ * ∫⁻ M, G₃ M ∂gaussMat (mA n) (mA n) (tA n) + k₀ := by
  have h := dbl_comb (stdGauss (Fin (mA n))) (measurable_PlS c s h₁) (measurable_PlS c s h₂)
    (measurable_PlS c s h₃) k₁ k₂ k₃ k₀
  simp only at h
  rw [h, PlS_tot c s h₁, PlS_tot c s h₂, PlS_tot c s h₃]


/-- `E_v (M a(v))_j = (M ā)_j`. -/
lemma int_mulVec_j {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ] {m : ℕ}
    {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (M : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    ∫ v, (M *ᵥ a v) j ∂μ = (M *ᵥ vmean μ a) j := by
  simp only [Matrix.mulVec, dotProduct, vmean]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
  · intro k _
    exact (int_comp_bdd (μ := μ) ha hK (f := fun y => y k) (continuous_apply k)).const_mul _

/-- The row energy `WgR` at the plane split is the row energy `Wr` of the whole matrix. -/
lemma WgR_Mpl (c : Ret n) (s : ℝ) {O : ℝ} (hK : ∀ v, ‖aLat c s v‖ ≤ O) (ξ₁ ξ₂ : Fin (mA n) → ℝ)
    (j : Fin (mA n)) (ζ : Fin (mA n) × Fin (mA n) → ℝ) :
    WgR (stdGauss (Fin (n - 1))) (aLat c s) (hB c)
      (Mpl (hB c) (res (hB c) (a1Bar c s)) (cOf (tA n) (hB c) ξ₁)
        (cOf (tA n) (res (hB c) (a1Bar c s)) ξ₂) 0) (tA n) j ζ =
      Wr (stdGauss (Fin (n - 1))) (aLat c s) j (MplS c s ξ₁ ξ₂ (matOf (tA n) ζ)) := by
  unfold WgR Wr
  set M := MplS c s ξ₁ ξ₂ (matOf (tA n) ζ)
  have e1 : ∀ v, (Mpl (hB c) (res (hB c) (a1Bar c s)) (cOf (tA n) (hB c) ξ₁)
        (cOf (tA n) (res (hB c) (a1Bar c s)) ξ₂) 0 *ᵥ aLat c s v) j +
      (matOf (tA n) ζ *ᵥ BstLean.Part183.wT (stdGauss (Fin (n - 1))) (aLat c s) (hB c)
        (aLat c s v)) j = (M *ᵥ aLat c s v) j := by
    intro v
    simp only [M, MplS]
    rw [show reb (hB c) (cOf (tA n) (hB c) ξ₁) (reb (res (hB c) (a1Bar c s))
        (cOf (tA n) (res (hB c) (a1Bar c s)) ξ₂) (matOf (tA n) ζ)) =
        Mpl (hB c) (res (hB c) (a1Bar c s)) (cOf (tA n) (hB c) ξ₁)
          (cOf (tA n) (res (hB c) (a1Bar c s)) ξ₂) (matOf (tA n) ζ) from rfl,
      Mpl_mulVec _ _ _ _ (matOf (tA n) ζ)]
    rfl
  simp_rw [e1]
  have hn1 := int_mulVec_j (μ := stdGauss (Fin (n - 1))) (measurable_aLat c s) hK M j
  rw [hn1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Matrix.mulVec_sub, Pi.sub_apply]


/-- **The energy fluctuation at a node by the row moment expansion.** -/
theorem exWn_mom_B_of (hn : 16000 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 < O) (h1 : OpB (A1 c) O) {q : ℝ} (hq1 : 1 / 10 ≤ q) (hq : 1 - nodeS c g ^ 2 ≤ q)
    {B : ℝ} (hB0 : 0 < B)
    (hBias : ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
      ∂stdGauss (Fin (mA n)) ≤ ENNReal.ofReal (B ^ 8)) :
    ∫⁻ M, ENNReal.ofReal (exWn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal ((WflB n O q + B) ^ 8) := by
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  set s := nodeS c g with hsd
  set h := hB c
  set r := res h (a1Bar c s)
  set μv := stdGauss (Fin (n - 1))
  set Λ := q * O ^ 2 / ((n : ℝ) - 2) with hΛd
  set Tq := q * n * O ^ 2 / ((n : ℝ) - 2) with hTqd
  have hq0 : 0 < q := by linarith
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  have hΛ0 : 0 < Λ := by positivity
  have hTq0 : 0 < Tq := by positivity
  have htA : 0 < tA n := by
    unfold tA; have : 0 < mA n := by unfold mA; positivity
    positivity
  have hK := aLat_bdd hn1 c hs hO.le h1
  have hK2 : ∀ v, normSq (aLat c s v) ≤ O ^ 2 := aLat_normSq_le hn1 c hs h1
  have hΛ : ∀ e, ∫ v, (e ⬝ᵥ (aLat c s v - vmean μv (aLat c s))) ^ 2
      ∂μv ≤ Λ * normSq e := fun e =>
    (BstLean.Part173.cov_bound_lat hn3 c hs hO.le h1 e).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hq (sq_nonneg O)) h2n.le)
      (normSq_nonneg e))
  have hT : ∫ v, normSq (aLat c s v - vmean μv (aLat c s)) ∂μv ≤ Tq := by
    rw [vmean_aLat]
    refine (BstLean.Part183.trCov_lat hn3 c hs hO.le h1).trans ?_
    refine div_le_div_of_nonneg_right ?_ h2n.le
    have : (0 : ℝ) ≤ n * O ^ 2 := by positivity
    nlinarith
  have hT0 : 0 ≤ ∫ v, normSq (aLat c s v - vmean μv (aLat c s)) ∂μv :=
    integral_nonneg fun v => normSq_nonneg _
  set σ := 4 * (tA n * Λ) * Tq with hσd
  have hσ : 0 < σ := by positivity
  set K1 := 10759 / 100 * (4 * (tA n * Λ)) ^ 4 with hK1
  set K2 := (24563 * (mA n : ℝ) + 1) * ((π / 2) ^ 8 * gmom 8) * (4 * (tA n * Λ)) ^ 4 with hK2d
  set K3 := 2800 * (mA n : ℝ) * ((π / 2) ^ 12 * gmom 12) * (4 * (tA n * Λ)) ^ 6 / σ ^ 2 with hK3
  set K0 := 14 / 100 * σ ^ 4 with hK0
  set G₁ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ≥0∞ := fun M =>
    ENNReal.ofReal (Qvar μv (aLat c s) M ^ 4) with hG₁
  set G₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ≥0∞ := fun M =>
    ENNReal.ofReal (WrS μv (aLat c s) 4 M) with hG₂
  set G₃ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ≥0∞ := fun M =>
    ENNReal.ofReal (WrS μv (aLat c s) 6 M) with hG₃
  have mG₁ : Measurable G₁ :=
    ENNReal.measurable_ofReal.comp ((BstLean.Part183.measurable_Qvar (measurable_aLat c s)).pow_const 4)
  have mG₂ : Measurable G₂ :=
    ENNReal.measurable_ofReal.comp (measurable_WrS (μ := μv) (measurable_aLat c s) 4)
  have mG₃ : Measurable G₃ :=
    ENNReal.measurable_ofReal.comp (measurable_WrS (μ := μv) (measurable_aLat c s) 6)
  set A := WflB n O q with hAd
  have hA : 0 < A := by
    rw [hAd]; unfold WflB
    have h1' : 0 < √(tA n * (q * O ^ 2 / ((n : ℝ) - 2))) := Real.sqrt_pos.mpr (by positivity)
    have h2' : 0 < √((mA n : ℝ) * tA n * (q * n * O ^ 2 / ((n : ℝ) - 2)) / 2) :=
      Real.sqrt_pos.mpr (by have : (0 : ℝ) < mA n := by unfold mA; positivity
                            positivity)
    positivity
  set k₁ := (A + B) ^ 7 / A ^ 7
  set k₂ := (A + B) ^ 7 / B ^ 7
  have hk₁ : 0 ≤ k₁ := by positivity
  have hk₂ : 0 ≤ k₂ := by positivity
  -- the plane split
  have mF : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => ENNReal.ofReal (exWn (withA2 c p.2.2) g ^ 8)) :=
    ENNReal.measurable_ofReal.comp ((measurable_exWn_comp ((measurable_withA2 c).comp
      (measurable_snd.comp measurable_snd)) measurable_const).pow_const 8)
  have hps := BstLean.Part167.plane_split (q := mA n) (tA n) h (a1Bar c s) mF
  have e0 : ∫⁻ M, ENNReal.ofReal (exWn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) =
      ∫⁻ M, (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
        ENNReal.ofReal (exWn (withA2 c p.2.2) g ^ 8)) (M *ᵥ h, M *ᵥ a1Bar c s, M)
        ∂gaussMat (mA n) (mA n) (tA n) := rfl
  rw [e0, hps]
  simp only
  -- the inner bound at fixed plane coordinates
  have hin : ∀ ξ₁ ξ₂ : Fin (mA n) → ℝ, ∫⁻ N, ENNReal.ofReal (exWn (withA2 c
      (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
      ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal k₁ * (ENNReal.ofReal K1 * PlS c s G₁ ξ₁ ξ₂ +
        ENNReal.ofReal K2 * PlS c s G₂ ξ₁ ξ₂ + ENNReal.ofReal K3 * PlS c s G₃ ξ₁ ξ₂ +
        ENNReal.ofReal K0) +
        ENNReal.ofReal k₂ * ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) := by
    intro ξ₁ ξ₂
    set c₁ := cOf (tA n) h ξ₁
    set c₂ := cOf (tA n) r ξ₂
    set M₀ := Mpl h r c₁ c₂ 0
    set C₀' := ∑ j, G2 √(vsig2 c s) ((M₀ *ᵥ a1Bar c s) j)
    set E : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ := fun N =>
      exWn (withA2 c (reb h c₁ (reb r c₂ N))) g
    have mE : Measurable E :=
      measurable_exWn_comp ((measurable_withA2 c).comp (BstLean.Part157.measurable_reb_comp
        measurable_const measurable_const (BstLean.Part157.measurable_reb_comp measurable_const
          measurable_const measurable_id))) measurable_const
    have hE : ∀ N, E N = flQ μv (aLat c s) h M₀ N - C₀' := fun N =>
      exWn_Mpl hn1 c g hK c₁ c₂ N
    set F : (Fin (mA n) × Fin (mA n) → ℝ) → ℝ := fun ζ =>
      flQ μv (aLat c s) h M₀ (matOf (tA n) ζ)
    have hS := sqrtQ_euLip (measurable_aLat c s) hK hΛ0.le hΛ h M₀ htA.le
    have iF : Integrable F (stdGauss (Fin (mA n) × Fin (mA n))) := by
      have := euLip_sq_integrable (Real.sqrt_nonneg _) hS
      refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
      exact Real.sq_sqrt (flQ_nonneg _ _ _ _)
    set qb := ∫ ζ, F ζ ∂stdGauss (Fin (mA n) × Fin (mA n))
    have hmE : biasW c g ξ₁ ξ₂ = qb - C₀' := by
      have e0 : biasW c g ξ₁ ξ₂ = ∫ N, E N ∂gaussMat (mA n) (mA n) (tA n) := rfl
      rw [e0, gaussMat_eq, integral_map (measurable_matOf _).aemeasurable mE.aestronglyMeasurable]
      have : (fun ζ => E (matOf (tA n) ζ)) = fun ζ => F ζ - C₀' := funext fun ζ => hE _
      rw [this]
      rw [integral_sub iF (integrable_const _)]
      simp
      rfl
    have hfl := flQ_rows8 (measurable_aLat c s) hK hΛ0.le hΛ h M₀ htA.le hσ
    have hP : ∀ {G : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ≥0∞}, Measurable G →
        PlS c s G ξ₁ ξ₂ = ∫⁻ ζ, G (MplS c s ξ₁ ξ₂ (matOf (tA n) ζ))
          ∂stdGauss (Fin (mA n) × Fin (mA n)) := by
      intro G hG
      unfold PlS
      have hmN : Measurable (fun N : Matrix (Fin (mA n)) (Fin (mA n)) ℝ => G (MplS c s ξ₁ ξ₂ N)) :=
        hG.comp (BstLean.Part157.measurable_reb_comp measurable_const measurable_const
          (BstLean.Part157.measurable_reb_comp measurable_const measurable_const measurable_id))
      rw [gaussMat_eq, lintegral_map hmN (measurable_matOf _)]
    have hQ1 : ∫⁻ ζ, ENNReal.ofReal (BstLean.Part183.flQv μv (aLat c s) h M₀ (matOf (tA n) ζ) ^ 4)
        ∂stdGauss (Fin (mA n) × Fin (mA n)) = PlS c s G₁ ξ₁ ξ₂ := by
      rw [hP mG₁]
      refine lintegral_congr fun ζ => ?_
      simp only [G₁, M₀]
      rw [BstLean.Part183.flQv_Mpl]
      rfl
    have hQp : ∀ p : ℕ, ∫⁻ ζ, ENNReal.ofReal (∑ j, WgR μv (aLat c s) h M₀ (tA n) j ζ ^ p)
        ∂stdGauss (Fin (mA n) × Fin (mA n)) =
        ∫⁻ ζ, ENNReal.ofReal (WrS μv (aLat c s) p (MplS c s ξ₁ ξ₂ (matOf (tA n) ζ)))
          ∂stdGauss (Fin (mA n) × Fin (mA n)) := by
      intro p
      refine lintegral_congr fun ζ => ?_
      unfold WrS
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [WgR_Mpl c s hK ξ₁ ξ₂ j ζ]
    have hQ2 : ∫⁻ ζ, ENNReal.ofReal (∑ j, WgR μv (aLat c s) h M₀ (tA n) j ζ ^ 4)
        ∂stdGauss (Fin (mA n) × Fin (mA n)) = PlS c s G₂ ξ₁ ξ₂ := by
      rw [hQp 4, hP mG₂]
    have hQ3 : ∫⁻ ζ, ENNReal.ofReal (∑ j, WgR μv (aLat c s) h M₀ (tA n) j ζ ^ 6)
        ∂stdGauss (Fin (mA n) × Fin (mA n)) = PlS c s G₃ ξ₁ ξ₂ := by
      rw [hQp 6, hP mG₃]
    rw [hQ1, hQ2, hQ3] at hfl
    have hpt : ∀ ζ, ENNReal.ofReal (E (matOf (tA n) ζ) ^ 8) ≤ ENNReal.ofReal k₁ *
        ENNReal.ofReal (|F ζ - qb| ^ 8) + ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8) := by
      intro ζ
      rw [← ENNReal.ofReal_mul hk₁, ← ENNReal.ofReal_add (by positivity)
        (mul_nonneg hk₂ (by positivity))]
      refine ENNReal.ofReal_le_ofReal ?_
      have := pow8_split (F ζ - qb) (biasW c g ξ₁ ξ₂) hA hB0
      have e8 : |biasW c g ξ₁ ξ₂| ^ 8 = biasW c g ξ₁ ξ₂ ^ 8 := (by decide : Even 8).pow_abs _
      rw [e8] at this
      have e : E (matOf (tA n) ζ) = F ζ - qb + biasW c g ξ₁ ξ₂ := by rw [hE, hmE]; ring
      rw [e]; exact this
    have cF : Continuous F :=
      ((hS.continuous (Real.sqrt_nonneg _)).pow 2).congr fun ζ => Real.sq_sqrt (flQ_nonneg _ _ _ _)
    have mfl : Measurable (fun ζ => ENNReal.ofReal (|F ζ - qb| ^ 8)) :=
      ENNReal.measurable_ofReal.comp (((cF.measurable.sub_const _).abs).pow_const 8)
    rw [gaussMat_eq, lintegral_map (f := fun N => ENNReal.ofReal (E N ^ 8))
      (ENNReal.measurable_ofReal.comp (mE.pow_const 8)) (measurable_matOf _)]
    calc ∫⁻ ζ, ENNReal.ofReal (E (matOf (tA n) ζ) ^ 8) ∂stdGauss (Fin (mA n) × Fin (mA n))
        ≤ ∫⁻ ζ, (ENNReal.ofReal k₁ * ENNReal.ofReal (|F ζ - qb| ^ 8) +
          ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8)) ∂stdGauss (Fin (mA n) × Fin (mA n)) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal k₁ * ∫⁻ ζ, ENNReal.ofReal (|F ζ - qb| ^ 8)
            ∂stdGauss (Fin (mA n) × Fin (mA n)) + ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ mfl]
      _ ≤ ENNReal.ofReal k₁ * (ENNReal.ofReal K1 * PlS c s G₁ ξ₁ ξ₂ +
            ENNReal.ofReal K2 * PlS c s G₂ ξ₁ ξ₂ + ENNReal.ofReal K3 * PlS c s G₃ ξ₁ ξ₂ +
            ENNReal.ofReal K0) + ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8) := by
          gcongr
      _ = _ := by rw [ENNReal.ofReal_mul hk₂]
  -- the moment bounds of the whole matrix
  have hY : ∫⁻ M, G₁ M ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal ((√((mA n : ℝ) * tA n * Tq / 2) + π / 2 * (18 / 10) * √(tA n * O ^ 2)) ^ 8) :=
    BstLean.Part183.Qvar_mom4_gm (μ := μv) (measurable_aLat c s) hK hK2 (by positivity) htA hT
  have hWp : ∀ p : ℕ, 1 ≤ p → ∫⁻ M, ENNReal.ofReal (WrS μv (aLat c s) p M)
      ∂gaussMat (mA n) (mA n) (tA n) ≤ ENNReal.ofReal ((mA n : ℝ) * (gmom (2 * p) * tA n ^ p *
        (4 * O ^ 2) ^ (p - 1) * ∫ v, normSq (aLat c s v - vmean μv (aLat c s)) ∂μv)) := by
    intro p hp
    have hsum : ∀ M, ENNReal.ofReal (WrS μv (aLat c s) p M) =
        ∑ j, ENNReal.ofReal (Wr μv (aLat c s) j M ^ p) := by
      intro M
      unfold WrS
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro j _
      exact pow_nonneg (integral_nonneg fun v => sq_nonneg _) _
    simp_rw [hsum]
    rw [lintegral_finset_sum]
    swap
    · intro j _
      exact ENNReal.measurable_ofReal.comp
        ((measurable_Wr (μ := μv) (measurable_aLat c s) j).pow_const p)
    have hj : ∀ j, ∫⁻ M, ENNReal.ofReal (Wr μv (aLat c s) j M ^ p) ∂gaussMat (mA n) (mA n) (tA n) ≤
        ENNReal.ofReal (gmom (2 * p) * tA n ^ p * (4 * O ^ 2) ^ (p - 1) *
          ∫ v, normSq (aLat c s v - vmean μv (aLat c s)) ∂μv) := fun j =>
      row_var_mom (μ := μv) (measurable_aLat c s) hO.le hK2 htA.le j hp
    calc ∑ j, ∫⁻ M, ENNReal.ofReal (Wr μv (aLat c s) j M ^ p) ∂gaussMat (mA n) (mA n) (tA n)
        ≤ ∑ _j : Fin (mA n), ENNReal.ofReal (gmom (2 * p) * tA n ^ p * (4 * O ^ 2) ^ (p - 1) *
          ∫ v, normSq (aLat c s v - vmean μv (aLat c s)) ∂μv) := Finset.sum_le_sum fun j _ => hj j
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          simp
  have hW4 := hWp 4 (by norm_num)
  have hW6 := hWp 6 (by norm_num)
  simp only [show 2 * 4 = 8 from rfl, show 2 * 6 = 12 from rfl, show 4 - 1 = 3 from rfl,
    show 6 - 1 = 5 from rfl] at hW4 hW6
  -- the numeric closure
  set T' := ∫ v, normSq (aLat c s v - vmean μv (aLat c s)) ∂μv with hT'd
  have hnum : K1 * (√((mA n : ℝ) * tA n * Tq / 2) + π / 2 * (18 / 10) * √(tA n * O ^ 2)) ^ 8 +
      K2 * ((mA n : ℝ) * (gmom 8 * tA n ^ 4 * (4 * O ^ 2) ^ 3 * T')) +
      K3 * ((mA n : ℝ) * (gmom 12 * tA n ^ 6 * (4 * O ^ 2) ^ 5 * T')) + K0 ≤ A ^ 8 :=
    enb_closure hn hO hq1 hT0 hT
  have hK1p : 0 ≤ K1 := by positivity
  have hK2p : 0 ≤ K2 := by have := gmom_nonneg 8; positivity
  have hK3p : 0 ≤ K3 := by have := gmom_nonneg 12; positivity
  have hK0p : 0 ≤ K0 := by positivity
  -- the outer integrals
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ N, ENNReal.ofReal (exWn (withA2 c
        (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
        ∂gaussMat (mA n) (mA n) (tA n) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, (ENNReal.ofReal k₁ * (ENNReal.ofReal K1 * PlS c s G₁ ξ₁ ξ₂ +
          ENNReal.ofReal K2 * PlS c s G₂ ξ₁ ξ₂ + ENNReal.ofReal K3 * PlS c s G₃ ξ₁ ξ₂ +
          ENNReal.ofReal K0) + ENNReal.ofReal k₂ * ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8))
          ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) :=
        lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => hin ξ₁ ξ₂
    _ = ENNReal.ofReal k₁ * ∫⁻ ξ₁, ∫⁻ ξ₂, (ENNReal.ofReal K1 * PlS c s G₁ ξ₁ ξ₂ +
          ENNReal.ofReal K2 * PlS c s G₂ ξ₁ ξ₂ + ENNReal.ofReal K3 * PlS c s G₃ ξ₁ ξ₂ +
          ENNReal.ofReal K0) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) +
          ENNReal.ofReal k₂ * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8)
          ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) := by
        have mR : Measurable (Function.uncurry fun (ξ₁ ξ₂ : Fin (mA n) → ℝ) =>
            ENNReal.ofReal K1 * PlS c s G₁ ξ₁ ξ₂ + ENNReal.ofReal K2 * PlS c s G₂ ξ₁ ξ₂ +
              ENNReal.ofReal K3 * PlS c s G₃ ξ₁ ξ₂ + ENNReal.ofReal K0) :=
          ((((measurable_PlS c s mG₁).const_mul _).add ((measurable_PlS c s mG₂).const_mul _)).add
            ((measurable_PlS c s mG₃).const_mul _)).add measurable_const
        exact dbl_comb2 (stdGauss (Fin (mA n))) mR
          (fun ξ₁ ξ₂ => ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8)) _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal k₁ * ENNReal.ofReal (A ^ 8) + ENNReal.ofReal k₂ * ENNReal.ofReal (B ^ 8) := by
        rw [plane_tot3 c s mG₁ mG₂ mG₃]
        gcongr
        calc ENNReal.ofReal K1 * ∫⁻ M, G₁ M ∂gaussMat (mA n) (mA n) (tA n) +
              ENNReal.ofReal K2 * ∫⁻ M, G₂ M ∂gaussMat (mA n) (mA n) (tA n) +
              ENNReal.ofReal K3 * ∫⁻ M, G₃ M ∂gaussMat (mA n) (mA n) (tA n) + ENNReal.ofReal K0
            ≤ ENNReal.ofReal K1 * ENNReal.ofReal ((√((mA n : ℝ) * tA n * Tq / 2) +
                π / 2 * (18 / 10) * √(tA n * O ^ 2)) ^ 8) +
              ENNReal.ofReal K2 * ENNReal.ofReal ((mA n : ℝ) * (gmom 8 * tA n ^ 4 *
                (4 * O ^ 2) ^ 3 * T')) +
              ENNReal.ofReal K3 * ENNReal.ofReal ((mA n : ℝ) * (gmom 12 * tA n ^ 6 *
                (4 * O ^ 2) ^ 5 * T')) + ENNReal.ofReal K0 := by
              gcongr
          _ = ENNReal.ofReal (K1 * (√((mA n : ℝ) * tA n * Tq / 2) +
                π / 2 * (18 / 10) * √(tA n * O ^ 2)) ^ 8 +
              K2 * ((mA n : ℝ) * (gmom 8 * tA n ^ 4 * (4 * O ^ 2) ^ 3 * T')) +
              K3 * ((mA n : ℝ) * (gmom 12 * tA n ^ 6 * (4 * O ^ 2) ^ 5 * T')) + K0) := by
              have g8 := gmom_nonneg 8
              have g12 := gmom_nonneg 12
              rw [ENNReal.ofReal_add (by positivity) hK0p, ENNReal.ofReal_add (by positivity)
                (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
                ENNReal.ofReal_mul hK1p, ENNReal.ofReal_mul hK2p, ENNReal.ofReal_mul hK3p]
          _ ≤ ENNReal.ofReal (A ^ 8) := ENNReal.ofReal_le_ofReal hnum
    _ = ENNReal.ofReal ((A + B) ^ 8) := by
        rw [← ENNReal.ofReal_mul hk₁, ← ENNReal.ofReal_mul hk₂,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have hA7 : A ^ 7 ≠ 0 := by positivity
        have hB7 : B ^ 7 ≠ 0 := by positivity
        simp only [k₁, k₂]
        field_simp

/-- **The energy fluctuation bound of the row moment expansion** (`EnB_stmt`). -/
theorem EnB_proved : EnB_stmt := by
  intro n hn c g hs O hO h1 q hq1 hq B hB0 hBias
  exact exWn_mom_B_of hn c g hs hO h1 hq1 hq hB0 hBias

end net

end BstLean.Part184

#print axioms BstLean.Part184.enb_closure
#print axioms BstLean.Part184.exWn_mom_B_of
#print axioms BstLean.Part184.EnB_proved
