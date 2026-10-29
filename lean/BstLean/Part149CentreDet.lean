import BstLean.Part149CDefs
import BstLean.Part149Frame

/-!
# Part 149, item 5: the first hidden layer statistics of the mean-field centre (deterministic)

Do not use `sorry`, `native_decide` or `axiom`.

Fixed `c`, `τ`, `A₁`. Write `a = a1 c τ A₁`, `d = m/n`. Hypotheses: `|a|²` is within `d·εD` of `d`
in `L²` (`errD1 ≤ (d·εD)²`) and the Gram kernel of `a` is within `d·εQ` of `kq·|a||a'|` in `L²`
(`Qk kq ≤ (d·εQ)²`). Conclusion (`centre_det`): `N2 > 0`, `|b1|² ≤ (3/4)·N2`, and the quantity
`V1 + K·(Qu/(d·π₀) + 8·d·π₀·P(|a|² < d·π₀))` is at most a constant times `Qk kq/d` plus a constant
times `errD1/d`.

The proof is for every probability space `(U, μ)` and every map `a : U → ℝ^m` with bounded
measurable coordinates (`centre_det_gen`); the steps are Jensen, Fubini, Cauchy–Schwarz,
Minkowski in `L²` (`bm_minkowski`) and Chebyshev.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (BM bm_cauchy_schwarz)
open BstLean.Part130 BstLean.Part134
open BstLean.Part132 (nrm nrm_nonneg nrm_sq)
open BstLean.Part136 (hbar bm_fst bm_snd)

section generic

variable {m : ℕ} {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]

/-- The integrated squared error of the Gram kernel of `a` against `k·|a||a'|`. -/
noncomputable def QkG (a : U → Fin m → ℝ) (k : ℝ) : ℝ :=
  ∫ p, (dotp (a p.1) (a p.2) - k * (nrm (a p.1) * nrm (a p.2))) ^ 2 ∂(μ.prod μ)

lemma bm_normSq_of {a : U → Fin m → ℝ} (ha : ∀ j, BM (fun u => a u j)) :
    BM (fun u => normSq (a u)) :=
  BstLean.Part134.bm_sum Finset.univ fun j _ => (ha j).sq

lemma bm_nrm_of {a : U → Fin m → ℝ} (ha : ∀ j, BM (fun u => a u j)) :
    BM (fun u => nrm (a u)) := by
  obtain ⟨M, hM⟩ := (bm_normSq_of ha).bdd
  have hmeas : Measurable a := measurable_pi_iff.mpr fun j => (ha j).meas
  refine ⟨(measurable_normSq.comp hmeas).sqrt, √M, fun u => ?_⟩
  rw [abs_of_nonneg (nrm_nonneg _)]
  exact Real.sqrt_le_sqrt ((le_abs_self _).trans (hM u))

lemma bm_dotp_of {a : U → Fin m → ℝ} (ha : ∀ j, BM (fun u => a u j)) :
    BM (fun p : U × U => dotp (a p.1) (a p.2)) :=
  BstLean.Part134.bm_sum Finset.univ fun k _ => (bm_fst (ha k)).mul (bm_snd (ha k))

lemma bm_pn_of {a : U → Fin m → ℝ} (ha : ∀ j, BM (fun u => a u j)) :
    BM (fun p : U × U => nrm (a p.1) * nrm (a p.2)) :=
  (bm_fst (bm_nrm_of ha)).mul (bm_snd (bm_nrm_of ha))

/-- Jensen for a bounded measurable function on a probability space. -/
lemma bm_sq_int_le {V : Type*} [MeasurableSpace V] (ν : Measure V) [IsProbabilityMeasure ν]
    {f : V → ℝ} (hf : BM f) : (∫ x, f x ∂ν) ^ 2 ≤ ∫ x, f x ^ 2 ∂ν := by
  have := bm_cauchy_schwarz ν hf (BM.const 1)
  simpa using this

/-- (f1) `|E|a|² − d| ≤ δ`. -/
lemma abs_N2_sub_le {a : U → Fin m → ℝ} (ha : ∀ j, BM (fun u => a u j)) {d δ : ℝ} (hδ : 0 ≤ δ)
    (hE : ∫ u, (normSq (a u) - d) ^ 2 ∂μ ≤ δ ^ 2) : |∫ u, normSq (a u) ∂μ - d| ≤ δ := by
  have bN := bm_normSq_of ha
  have h1 := bm_sq_int_le μ (bN.sub (BM.const d))
  have h2 : |∫ u, (normSq (a u) - d) ∂μ| ≤ δ := abs_le_of_sq_le_sq (h1.trans hE) hδ
  rw [integral_sub (bN.integrable μ) (integrable_const d)] at h2
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h2

/-- (f2) the variance of `|a|` is nonnegative and at most `E(|a|² − d)²/d`. -/
lemma V_bounds {a : U → Fin m → ℝ} (ha : ∀ j, BM (fun u => a u j)) {d : ℝ} (hd : 0 < d) :
    (∫ u, nrm (a u) ∂μ) ^ 2 ≤ ∫ u, normSq (a u) ∂μ ∧
    ∫ u, normSq (a u) ∂μ - (∫ u, nrm (a u) ∂μ) ^ 2 ≤
      (∫ u, (normSq (a u) - d) ^ 2 ∂μ) / d := by
  have bN := bm_normSq_of ha
  have bR := bm_nrm_of ha
  have e2 : ∫ u, nrm (a u) ^ 2 ∂μ = ∫ u, normSq (a u) ∂μ := by simp_rw [nrm_sq]
  have h1 : (∫ u, nrm (a u) ∂μ) ^ 2 ≤ ∫ u, normSq (a u) ∂μ := by
    rw [← e2]; exact bm_sq_int_le μ bR
  refine ⟨h1, ?_⟩
  obtain ⟨s, hspos, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 = d :=
    ⟨√d, Real.sqrt_pos.mpr hd, Real.sq_sqrt hd.le⟩
  have pt : ∀ u, (nrm (a u) - s) ^ 2 ≤ d⁻¹ * (normSq (a u) - d) ^ 2 := by
    intro u
    have hx := nrm_nonneg (a u)
    have hS : normSq (a u) = nrm (a u) ^ 2 := (nrm_sq _).symm
    have e : (nrm (a u) ^ 2 - d) ^ 2 = (nrm (a u) - s) ^ 2 * (nrm (a u) + s) ^ 2 := by
      rw [← hs2]; ring
    have h3 : d ≤ (nrm (a u) + s) ^ 2 := by
      nlinarith [mul_nonneg hx hspos.le, sq_nonneg (nrm (a u))]
    rw [hS, inv_mul_eq_div, le_div_iff₀ hd, e]
    exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
  have bRs : BM (fun u => nrm (a u) - s) := bR.sub (BM.const s)
  have bNd : BM (fun u => normSq (a u) - d) := bN.sub (BM.const d)
  have h2 : ∫ u, (nrm (a u) - s) ^ 2 ∂μ ≤ d⁻¹ * ∫ u, (normSq (a u) - d) ^ 2 ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono (bRs.sq.integrable μ) ((bNd.sq.integrable μ).const_mul _) pt
  have h3 : ∫ u, (nrm (a u) - s) ^ 2 ∂μ =
      ∫ u, normSq (a u) ∂μ - 2 * s * ∫ u, nrm (a u) ∂μ + d := by
    have e : (fun u => (nrm (a u) - s) ^ 2) =
        fun u => (normSq (a u) - 2 * s * nrm (a u)) + d := by
      funext u
      linear_combination nrm_sq (a u) + hs2
    rw [e, integral_add (f := fun u => normSq (a u) - 2 * s * nrm (a u)) (g := fun _ => d)
        ((bN.integrable μ).sub ((bR.integrable μ).const_mul _)) (integrable_const _),
      integral_sub (f := fun u => normSq (a u)) (g := fun u => 2 * s * nrm (a u))
        (bN.integrable μ) ((bR.integrable μ).const_mul _), integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [div_eq_inv_mul]
  nlinarith [sq_nonneg (∫ u, nrm (a u) ∂μ - s)]

lemma int_dotp {a : U → Fin m → ℝ} (ha : ∀ j, BM (fun u => a u j)) :
    ∫ p, dotp (a p.1) (a p.2) ∂(μ.prod μ) = normSq (hbar μ a) := by
  unfold dotp normSq hbar
  rw [integral_finsetSum _ fun k _ => ((bm_fst (ha k)).mul (bm_snd (ha k))).integrable _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_prod_mul (fun u => a u k) (fun u => a u k), sq]

lemma int_pn (a : U → Fin m → ℝ) :
    ∫ p, nrm (a p.1) * nrm (a p.2) ∂(μ.prod μ) = (∫ u, nrm (a u) ∂μ) ^ 2 := by
  rw [integral_prod_mul (fun u => nrm (a u)) (fun u => nrm (a u)), sq]

/-- (f4) -/
lemma int_pn_sq (a : U → Fin m → ℝ) :
    ∫ p, (nrm (a p.1) * nrm (a p.2)) ^ 2 ∂(μ.prod μ) = (∫ u, normSq (a u) ∂μ) ^ 2 := by
  have e : (fun p : U × U => (nrm (a p.1) * nrm (a p.2)) ^ 2) =
      fun p => normSq (a p.1) * normSq (a p.2) := by
    funext p; rw [mul_pow, nrm_sq, nrm_sq]
  rw [e, integral_prod_mul (fun u => normSq (a u)) (fun u => normSq (a u)), sq]

omit [IsProbabilityMeasure μ] in
lemma QkG_nonneg (a : U → Fin m → ℝ) (k : ℝ) : 0 ≤ QkG μ a k :=
  integral_nonneg fun _ => sq_nonneg _

/-- (f3) -/
lemma sq_mean_le_QkG {a : U → Fin m → ℝ} (ha : ∀ j, BM (fun u => a u j)) (k : ℝ) :
    (normSq (hbar μ a) - k * (∫ u, nrm (a u) ∂μ) ^ 2) ^ 2 ≤ QkG μ a k := by
  have bkP : BM (fun p : U × U => k * (nrm (a p.1) * nrm (a p.2))) :=
    (BM.const k).mul (bm_pn_of ha)
  have bD : BM (fun p : U × U => dotp (a p.1) (a p.2) - k * (nrm (a p.1) * nrm (a p.2))) :=
    (bm_dotp_of ha).sub bkP
  have h := bm_sq_int_le (μ.prod μ) bD
  rw [integral_sub ((bm_dotp_of ha).integrable _) (bkP.integrable _), integral_const_mul,
    int_dotp μ ha, int_pn μ a] at h
  exact h

/-- (f5), the Minkowski step. -/
lemma QkG_shift {a : U → Fin m → ℝ} (ha : ∀ j, BM (fun u => a u j)) (k u : ℝ) {q w : ℝ}
    (hq : 0 ≤ q) (hw : 0 ≤ w) (h1 : QkG μ a k ≤ q ^ 2)
    (h2 : |(k - u) * ∫ x, normSq (a x) ∂μ| ≤ w) : QkG μ a u ≤ (q + w) ^ 2 := by
  have bf : BM (fun p : U × U => dotp (a p.1) (a p.2) - k * (nrm (a p.1) * nrm (a p.2))) :=
    (bm_dotp_of ha).sub ((BM.const k).mul (bm_pn_of ha))
  have bg : BM (fun p : U × U => (k - u) * (nrm (a p.1) * nrm (a p.2))) :=
    (BM.const (k - u)).mul (bm_pn_of ha)
  have n2 : ∫ p, ((k - u) * (nrm (a p.1) * nrm (a p.2))) ^ 2 ∂(μ.prod μ) ≤ w ^ 2 := by
    have e : (fun p : U × U => ((k - u) * (nrm (a p.1) * nrm (a p.2))) ^ 2) =
        fun p => (k - u) ^ 2 * (nrm (a p.1) * nrm (a p.2)) ^ 2 := by
      funext p; ring
    rw [e, integral_const_mul, int_pn_sq μ a, ← mul_pow]
    exact sq_le_sq' (by linarith [(abs_le.mp h2).1]) (abs_le.mp h2).2
  have h := bm_minkowski (μ.prod μ) bf bg hq hw h1 n2
  refine le_of_eq_of_le ?_ h
  unfold QkG
  congr 1
  funext p
  ring

/-- (f6) Chebyshev. -/
lemma cheb_low {a : U → Fin m → ℝ} (ha : ∀ j, BM (fun u => a u j)) {d t : ℝ} (ht : t < d) :
    μ.real {u | normSq (a u) < t} ≤ (∫ u, (normSq (a u) - d) ^ 2 ∂μ) / (d - t) ^ 2 := by
  have bN := bm_normSq_of ha
  have hs : MeasurableSet {u | normSq (a u) < t} := measurableSet_lt bN.meas measurable_const
  have hdt : 0 < d - t := by linarith
  have hpos : 0 < (d - t) ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  have pt : ∀ u, ({u | normSq (a u) < t}).indicator (fun _ => (d - t) ^ 2) u ≤
      (normSq (a u) - d) ^ 2 := by
    intro u
    rw [Set.indicator_apply]
    split_ifs with hu
    · have hu' : normSq (a u) < t := hu
      nlinarith [mul_nonneg (sub_nonneg.mpr hu'.le)
        (by linarith : (0 : ℝ) ≤ (d - t) + (d - normSq (a u)))]
    · positivity
  have h := integral_mono ((integrable_const ((d - t) ^ 2)).indicator hs)
    ((bN.sub (BM.const d)).sq.integrable μ) pt
  rw [integral_indicator_const _ hs, smul_eq_mul] at h
  exact h

/-- The arithmetic of (f5): from `Qu ≤ (q + (q + V))²`. -/
lemma arith_f5 {q V ζ εD E d Qu : ℝ} (hζ : 0 < ζ) (hd : 0 < d) (hV0 : 0 ≤ V)
    (hV1 : V ≤ E / d) (hV2 : V ≤ d * εD ^ 2) (hQu : Qu ≤ (q + (q + V)) ^ 2) :
    Qu ≤ (1 + ζ) * 4 * q ^ 2 + (1 + 1 / ζ) * (εD ^ 2 * E) := by
  have hVV : V ^ 2 ≤ εD ^ 2 * E := by
    have h := mul_le_mul hV2 hV1 hV0 (mul_nonneg hd.le (sq_nonneg εD))
    have e : d * εD ^ 2 * (E / d) = εD ^ 2 * E := by field_simp
    rw [e] at h
    nlinarith
  have hc : 4 * q * V ≤ ζ * (4 * q ^ 2) + V ^ 2 / ζ := by
    rw [← sub_nonneg]
    have e : ζ * (4 * q ^ 2) + V ^ 2 / ζ - 4 * q * V = (2 * q * ζ - V) ^ 2 / ζ := by
      field_simp; ring
    rw [e]
    positivity
  have h1 : 0 ≤ 1 + 1 / ζ := by positivity
  have h2 := mul_le_mul_of_nonneg_left hVV h1
  have e3 : (1 + 1 / ζ) * V ^ 2 = V ^ 2 + V ^ 2 / ζ := by ring
  nlinarith

/-- The arithmetic of (f3): `Y ≤ (3/4)·N`. -/
lemma arith_f3 {Y kq M2 q d εQ εD N : ℝ} (hkq0 : 0 ≤ kq) (hd : 0 < d) (hεD1 : εD < 1)
    (hεQ0 : 0 ≤ εQ) (hcond : kq * (1 - εD) + εQ ≤ 3 / 4 * (1 - εD))
    (hY : Y ≤ kq * M2 + q) (hq : q ≤ d * εQ) (hM : M2 ≤ N) (hN : d * (1 - εD) ≤ N) :
    Y ≤ 3 / 4 * N := by
  have h1 : kq * M2 ≤ kq * N := mul_le_mul_of_nonneg_left hM hkq0
  have hc : εQ ≤ (3 / 4 - kq) * (1 - εD) := by linarith
  have hc0 : 0 ≤ 3 / 4 - kq :=
    nonneg_of_mul_nonneg_left (hεQ0.trans hc) (by linarith)
  have h2 : d * εQ ≤ d * ((3 / 4 - kq) * (1 - εD)) := mul_le_mul_of_nonneg_left hc hd.le
  have h3 : (3 / 4 - kq) * (d * (1 - εD)) ≤ (3 / 4 - kq) * N :=
    mul_le_mul_of_nonneg_left hN hc0
  nlinarith

/-- The last sum. -/
lemma arith_sum {V E d K Qu P Q ζ εD π₀ : ℝ} (hd : 0 < d) (hζ : 0 < ζ) (hπ0 : 0 < π₀)
    (hπ1 : π₀ < 1) (hK : 0 ≤ K) (hV1 : V ≤ E / d)
    (hQu : Qu ≤ (1 + ζ) * 4 * Q + (1 + 1 / ζ) * (εD ^ 2 * E))
    (hP : P ≤ E / (d - d * π₀) ^ 2) :
    V + K * (Qu / (d * π₀) + 8 * (d * π₀) * P) ≤
      4 * K * (1 + ζ) / π₀ * (Q / d) +
        (1 + K * ((1 + 1 / ζ) * εD ^ 2 / π₀ + 8 * π₀ / (1 - π₀) ^ 2)) * (E / d) := by
  have hdπ : 0 < d * π₀ := mul_pos hd hπ0
  have h1π : 0 < 1 - π₀ := by linarith
  have t1 : Qu / (d * π₀) ≤ ((1 + ζ) * 4 * Q + (1 + 1 / ζ) * (εD ^ 2 * E)) / (d * π₀) :=
    div_le_div_of_nonneg_right hQu hdπ.le
  have t2 : 8 * (d * π₀) * P ≤ 8 * (d * π₀) * (E / (d - d * π₀) ^ 2) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have h := add_le_add hV1 (mul_le_mul_of_nonneg_left (add_le_add t1 t2) hK)
  refine h.trans (le_of_eq ?_)
  have e : d - d * π₀ = d * (1 - π₀) := by ring
  rw [e]
  have h1 : (1 - π₀) ≠ 0 := h1π.ne'
  field_simp
  ring

/-- **The first-layer statistics, for a map with bounded measurable coordinates.** -/
theorem centre_det_gen {a : U → Fin m → ℝ} (ha : ∀ j, BM (fun u => a u j))
    {d kq εD εQ π₀ ζ K : ℝ} (hd : 0 < d) (hkq0 : 0 ≤ kq) (hkq1 : kq ≤ 1)
    (hεD0 : 0 ≤ εD) (hεD1 : εD < 1) (hεQ0 : 0 ≤ εQ)
    (hcond : kq * (1 - εD) + εQ ≤ 3 / 4 * (1 - εD))
    (hπ0 : 0 < π₀) (hπ1 : π₀ < 1) (hζ : 0 < ζ) (hK : 0 ≤ K)
    (hD1 : ∫ u, (normSq (a u) - d) ^ 2 ∂μ ≤ (d * εD) ^ 2)
    (hQ : QkG μ a kq ≤ (d * εQ) ^ 2) :
    0 < ∫ u, normSq (a u) ∂μ ∧ normSq (hbar μ a) ≤ 3 / 4 * ∫ u, normSq (a u) ∂μ ∧
    (∫ u, normSq (a u) ∂μ - (∫ u, nrm (a u) ∂μ) ^ 2) +
        K * (QkG μ a (normSq (hbar μ a) / ∫ u, normSq (a u) ∂μ) / (d * π₀) + 8 * (d * π₀) *
          μ.real {u | normSq (a u) < d * π₀}) ≤
      4 * K * (1 + ζ) / π₀ * (QkG μ a kq / d) +
        (1 + K * ((1 + 1 / ζ) * εD ^ 2 / π₀ + 8 * π₀ / (1 - π₀) ^ 2)) *
          ((∫ u, (normSq (a u) - d) ^ 2 ∂μ) / d) := by
  have hN := abs_N2_sub_le μ ha (mul_nonneg hd.le hεD0) hD1
  obtain ⟨hM, hV1⟩ := V_bounds μ ha hd
  have hQ0 := QkG_nonneg μ a kq
  have hf3 := sq_mean_le_QkG μ ha kq
  have hP := cheb_low μ ha (d := d) (t := d * π₀) (by nlinarith)
  have hshift := fun (u q w : ℝ) => QkG_shift μ ha kq u (q := q) (w := w)
  generalize (∫ u, normSq (a u) ∂μ) = N at *
  generalize (∫ u, nrm (a u) ∂μ) = M at *
  generalize (∫ u, (normSq (a u) - d) ^ 2 ∂μ) = E at *
  generalize normSq (hbar μ a) = Y at *
  generalize μ.real {u | normSq (a u) < d * π₀} = P at *
  obtain ⟨q, hq0, hq2⟩ : ∃ q : ℝ, 0 ≤ q ∧ q ^ 2 = QkG μ a kq :=
    ⟨√(QkG μ a kq), Real.sqrt_nonneg _, Real.sq_sqrt hQ0⟩
  have hqle : q ≤ d * εQ :=
    (le_abs_self q).trans (abs_le_of_sq_le_sq (hq2.le.trans hQ) (mul_nonneg hd.le hεQ0))
  have hY : |Y - kq * M ^ 2| ≤ q := abs_le_of_sq_le_sq (hf3.trans hq2.ge) hq0
  have hNlow : d * (1 - εD) ≤ N := by linarith [(abs_le.mp hN).1]
  have hNpos : 0 < N := lt_of_lt_of_le (mul_pos hd (by linarith)) hNlow
  have hYN : Y ≤ 3 / 4 * N :=
    arith_f3 hkq0 hd hεD1 hεQ0 hcond (by linarith [(abs_le.mp hY).2]) hqle hM hNlow
  refine ⟨hNpos, hYN, ?_⟩
  have hV0 : 0 ≤ N - M ^ 2 := by linarith
  have hV2 : N - M ^ 2 ≤ d * εD ^ 2 := by
    refine hV1.trans ?_
    rw [div_le_iff₀ hd]
    nlinarith
  have hw : |(kq - Y / N) * N| ≤ q + (N - M ^ 2) := by
    have e : (kq - Y / N) * N = (kq * M ^ 2 - Y) + kq * (N - M ^ 2) := by
      field_simp; ring
    rw [e]
    have h1 : kq * (N - M ^ 2) ≤ N - M ^ 2 := by nlinarith
    have h2 : 0 ≤ kq * (N - M ^ 2) := mul_nonneg hkq0 hV0
    rw [abs_le]
    constructor <;> linarith [(abs_le.mp hY).1, (abs_le.mp hY).2]
  have hQu := hshift (Y / N) q (q + (N - M ^ 2)) hq0 (by linarith) hq2.ge hw
  have hQu2 := arith_f5 (εD := εD) hζ hd hV0 hV1 hV2 hQu
  rw [hq2] at hQu2
  exact arith_sum hd hζ hπ0 hπ1 hK hV1 hQu2 hP

end generic

variable {n m : ℕ}

lemma measurable_a1_det (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) :
    Measurable (a1 c τ A₁) :=
  (continuous_reluV.comp
    (Continuous.matrix_mulVec continuous_const continuous_id)).measurable.comp
    (measurable_sphPt.comp (measurable_const.add (measurable_id.const_smul τ)))

/-- The coordinates of the first hidden vector are bounded measurable: the inputs are unit
vectors. -/
lemma bm_a1 (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) (j : Fin m) :
    BM (fun γ => a1 c τ A₁ γ j) := by
  have hc : Continuous (fun x : Fin n → ℝ => reluV (A₁.mulVec x) j) :=
    (continuous_apply j).comp
      (continuous_reluV.comp (Continuous.matrix_mulVec continuous_const continuous_id))
  obtain ⟨C, hC⟩ := isCompact_unit.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨(measurable_pi_apply j).comp (measurable_a1_det c τ A₁), C, fun γ => ?_⟩
  have := hC (sphPt (c + τ • γ)) (normSq_sphPt hn _)
  rwa [Real.norm_eq_abs] at this

lemma bm_normSq_a1 (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) :
    BM (fun γ => normSq (a1 c τ A₁ γ)) := bm_normSq_of (bm_a1 hn c τ A₁)

lemma bm_nrm_a1 (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) :
    BM (fun γ => nrm (a1 c τ A₁ γ)) := bm_nrm_of (bm_a1 hn c τ A₁)

/-- **The first hidden layer statistics of the mean-field centre, from the two `L²` bounds
`errD1 ≤ (d·εD)²` and `Qk kq ≤ (d·εQ)²` (`d = m/n`).** -/
theorem centre_det {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) (τ : ℝ)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) {kq εD εQ π₀ ζ K : ℝ} (hkq0 : 0 ≤ kq) (hkq1 : kq ≤ 1)
    (hεD0 : 0 ≤ εD) (hεD1 : εD < 1) (hεQ0 : 0 ≤ εQ)
    (hcond : kq * (1 - εD) + εQ ≤ 3 / 4 * (1 - εD))
    (hπ0 : 0 < π₀) (hπ1 : π₀ < 1) (hζ : 0 < ζ) (hK : 0 ≤ K)
    (hD1 : errD1 c τ A₁ ≤ ((m : ℝ) / n * εD) ^ 2)
    (hQ : Qk kq c τ A₁ ≤ ((m : ℝ) / n * εQ) ^ 2) :
    0 < N2 c τ A₁ ∧ normSq (b1 c τ A₁) ≤ 3 / 4 * N2 c τ A₁ ∧
    V1 c τ A₁ + K * (Qu c τ A₁ / ((m : ℝ) / n * π₀) + 8 * ((m : ℝ) / n * π₀) *
        (stdGauss (Fin n)).real {γ | normSq (a1 c τ A₁ γ) < (m : ℝ) / n * π₀}) ≤
      4 * K * (1 + ζ) / π₀ * (Qk kq c τ A₁ / ((m : ℝ) / n)) +
        (1 + K * ((1 + 1 / ζ) * εD ^ 2 / π₀ + 8 * π₀ / (1 - π₀) ^ 2)) *
          (errD1 c τ A₁ / ((m : ℝ) / n)) := by
  have hd : (0 : ℝ) < (m : ℝ) / n :=
    div_pos (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hn)
  exact centre_det_gen (stdGauss (Fin n)) (bm_a1 hn c τ A₁) hd hkq0 hkq1 hεD0 hεD1 hεQ0 hcond
    hπ0 hπ1 hζ hK hD1 hQ

end BstLean.Part149

open BstLean.Part149 in
#print axioms centre_det
