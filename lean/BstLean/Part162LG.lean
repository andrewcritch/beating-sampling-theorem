import BstLean.Part162LSp
import BstLean.Part162Final

/-!
# Part 162, items 1 and 3: the latitude moments from the realized certificate `Ψ`

Role: `delegations/statements/p162-spec.md`, items 1, 3, 4. Do not use `sorry`, `native_decide`
or `axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Proposition `t7:p07:LG` (the
integration of Lemma LS: `(E_s Var(φ|s)²)^{1/2} ≤ V`, `‖φ − φ̄(s)‖_{2p} ≤ τ_{2p}` from the
realized certificate `‖Ψ_φ‖_{L^{12}(x)} ≤ C_lat/n`).

* `gmom_even_le`, `one_le_gmom_even`: `1 ≤ E g^{2k} ≤ (2k)^k`; `cLS_le`, `cLS_pos`,
  `cLS_lt_sqrt` (`n ≥ 61`, `q ≤ 12`).
* `tanSq`, `psiA`: the squared tangential gradient on the latitude sphere and the realized `Ψ`.
* `idx_var_psi`, `idx_mom_psi`: Lemma LS per latitude with `Ψ`.
* `int_var_psi`, `int_mom_psi`: the integrated bounds (`V = (C/n)/(n−2)`,
  `τ_{2q} = K_q √(C/n)`, `K_q = c_q/(√(n−1) − c_q)`).
* **`latMomOfPsi`**: the interface `LatMom` from the `Ψ`-moments.
* **`classifier_paper_psi`**: the classifier theorem with the Agent replacement reduced to the
  `Ψ`-moments, `V_S`, the mass below the floor, `|c_A|² ≤ C_A`, the root sum and `BIAS_hyp`.
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real

/-! ## Even Gaussian moments -/

lemma gexp_deriv : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
    (fun t => t) * (fun t => Real.exp (t ^ 2 / 2)) := by
  funext t
  have h : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
    convert (hasDerivAt_pow 2 t).div_const 2 using 1 <;> ring
  simpa [mul_comm] using h.exp.deriv

lemma gexp_deriv_rec (j : ℕ) :
    iteratedDeriv (j + 2) (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 =
      (j + 1 : ℝ) * iteratedDeriv j (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
  rw [iteratedDeriv_succ', gexp_deriv, iteratedDeriv_mul (by fun_prop) (by fun_prop)]
  simp [iteratedDeriv_fun_id_zero, Finset.mem_range, Nat.choose_one_right]

lemma gexp_iter_zero (k : ℕ) :
    iteratedDeriv (2 * k) (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 ≤ (2 * k : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, gexp_deriv_rec]
    have h0 : 0 ≤ iteratedDeriv (2 * k) (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
      clear ih
      induction k with
      | zero => simp
      | succ k ih2 =>
        rw [show 2 * (k + 1) = 2 * k + 2 by ring, gexp_deriv_rec]
        positivity
    have hk : (2 * k : ℝ) ^ k ≤ (2 * (k + 1 : ℕ) : ℝ) ^ k :=
      pow_le_pow_left₀ (by positivity) (by push_cast; linarith) k
    calc ((2 * k : ℕ) + 1 : ℝ) * iteratedDeriv (2 * k) (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0
        ≤ (2 * (k + 1 : ℕ) : ℝ) * (2 * (k + 1 : ℕ) : ℝ) ^ k := by
          apply mul_le_mul _ (ih.trans hk) h0 (by positivity)
          push_cast; linarith
      _ = (2 * (k + 1 : ℕ) : ℝ) ^ (k + 1) := by ring

/-- `E g^{2k} ≤ (2k)^k` (from the moment generating function `e^{t²/2}`). -/
lemma gmom_even_le (k : ℕ) : gmom (2 * k) ≤ (2 * k : ℝ) ^ k := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) (2 * k)
  rw [mgf_fun_id_gaussianReal] at h
  simp only [NNReal.coe_one, zero_mul, zero_add, one_mul] at h
  change iteratedDeriv (2 * k) (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 =
    ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1 at h
  unfold gmom
  have e : ∫ x : ℝ, |x| ^ (2 * k) ∂gaussianReal 0 1 = ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1 := by
    congr 1; funext x; exact pow_abs_two_mul x
  rw [e, ← h]
  exact gexp_iter_zero k

lemma gexp_iter_ge_one (k : ℕ) :
    1 ≤ iteratedDeriv (2 * k) (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, gexp_deriv_rec]
    have : (1 : ℝ) ≤ (2 * k : ℕ) + 1 := by push_cast; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    nlinarith

lemma one_le_gmom_even (k : ℕ) : 1 ≤ gmom (2 * k) := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) (2 * k)
  rw [mgf_fun_id_gaussianReal] at h
  simp only [NNReal.coe_one, zero_mul, zero_add, one_mul] at h
  change iteratedDeriv (2 * k) (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 =
    ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1 at h
  unfold gmom
  have e : ∫ x : ℝ, |x| ^ (2 * k) ∂gaussianReal 0 1 = ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1 := by
    congr 1; funext x; exact pow_abs_two_mul x
  rw [e, ← h]
  exact gexp_iter_ge_one k

lemma cLS_pos {q : ℕ} (hq : 1 ≤ q) : 0 < cLS q := by
  unfold cLS
  have := one_le_gmom_even q
  have : 0 < gmom (2 * q) ^ (((2 * q : ℕ) : ℝ)⁻¹) := Real.rpow_pos_of_pos (by linarith) _
  positivity

/-- `c_q ≤ (π/2)√(2q)`. -/
lemma cLS_le {q : ℕ} (hq : 1 ≤ q) : cLS q ≤ π / 2 * √(2 * q) := by
  unfold cLS
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h0 := gmom_nonneg (2 * q)
  have hq0 : ((2 * q : ℕ) : ℝ) ≠ 0 := by positivity
  calc gmom (2 * q) ^ (((2 * q : ℕ) : ℝ)⁻¹) ≤ ((2 * q : ℝ) ^ q) ^ (((2 * q : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow h0 (gmom_even_le q) (by positivity)
    _ = √(2 * q) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.sqrt_eq_rpow]
        congr 1
        push_cast
        field_simp

/-! ## The tangential gradient on the latitude spheres -/

open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157
open BstLean.Part161
open BstLean.Part151 (gradSq gradSq_le measurable_gradSq)
open BstLean.Part53 (unitF53 radF53 measurable_unitF measurable_radF)
open BstLean.Part148 (EuLip)

variable {n : ℕ}

lemma continuous_consV : Continuous (fun p : ℝ × (Fin (n - 1) → ℝ) => consV (n := n) p.1 p.2) := by
  refine continuous_pi fun i => ?_
  unfold consV
  split_ifs <;> fun_prop

lemma continuous_xLatH (c : Ret n) :
    Continuous (fun p : ℝ × (Fin (n - 1) → ℝ) => xLatH c p.1 p.2) := by
  unfold xLatH
  have h1 : Continuous (fun p : ℝ × (Fin (n - 1) → ℝ) => (p.1 * radF53 p.2, √(1 - p.1 ^ 2) • p.2)) := by
    unfold radF53; fun_prop
  exact (Continuous.matrix_mulVec continuous_const (continuous_consV.comp h1))

/-- **The squared tangential gradient** of a field `Φ` on the latitude sphere at `s`:
`T = |∇(Φ ∘ xLatH c s)|² − Φ(x)²` (the paper's `Ψ_φ = (1 − s²)|P_lat ∇φ|²`, see `ls_var`). -/
noncomputable def tanSq (Φ : (Fin n → ℝ) → ℝ) (c : Ret n) (s : ℝ) (v : Fin (n - 1) → ℝ) : ℝ :=
  gradSq (fun w => Φ (xLatH c s w)) v - Φ (xLat c s (unitF53 v)) ^ 2

/-- The realized `Ψ` at the pair `(a, v)` (the nonnegative part of `tanSq`). -/
noncomputable def psiA (Φ : (Fin n → ℝ) → ℝ) (D : Design n) (c : Ret n) (a : Ix n)
    (v : Fin (n - 1) → ℝ) : ℝ :=
  √(tanSq Φ c (latC D c a) v) ^ 2

lemma measurable_tanSq {Φ : (Fin n → ℝ) → ℝ} (hΦ : Continuous Φ) (c : Ret n) :
    Measurable (fun p : ℝ × (Fin (n - 1) → ℝ) => tanSq Φ c p.1 p.2) := by
  unfold tanSq gradSq
  have hf : Continuous (Function.uncurry fun (s : ℝ) (w : Fin (n - 1) → ℝ) => Φ (xLatH c s w)) :=
    hΦ.comp (continuous_xLatH c)
  have m1 : Measurable (fun p : ℝ × (Fin (n - 1) → ℝ) =>
      ∑ i, (fderiv ℝ (fun w => Φ (xLatH c p.1 w)) p.2 (Pi.single i 1)) ^ 2) :=
    Finset.measurable_sum _ fun i _ =>
      (measurable_fderiv_apply_const_with_param ℝ hf (Pi.single i 1)).pow_const 2
  exact m1.sub ((hΦ.measurable.comp (measurable_xLat_comp c measurable_fst
    (measurable_unitF.comp measurable_snd))).pow_const 2)

lemma measurable_tanSq_left {Φ : (Fin n → ℝ) → ℝ} (hΦ : Continuous Φ) (c : Ret n) (s : ℝ) :
    Measurable (tanSq Φ c s) := by
  unfold tanSq gradSq
  exact (Finset.measurable_sum _ fun i _ =>
    (measurable_fderiv_apply_const ℝ _ (Pi.single i 1)).pow_const 2).sub
    ((hΦ.measurable.comp (measurable_xLat_comp c measurable_const measurable_unitF)).pow_const 2)

lemma meas_Xv {Φ : (Fin n → ℝ) → ℝ} (hΦ : Continuous Φ) (c : Ret n) (s : ℝ) :
    Measurable (fun v : Fin (n - 1) → ℝ => Φ (xLat c s (unitF53 v))) :=
  hΦ.measurable.comp (measurable_xLat_comp c measurable_const measurable_unitF)

lemma meas_psi_v {Φ : (Fin n → ℝ) → ℝ} (hΦ : Continuous Φ) (D : Design n) (c : Ret n) (a : Ix n) :
    Measurable (psiA Φ D c a) := by
  unfold psiA; exact (measurable_tanSq_left hΦ c _).sqrt.pow_const 2

lemma measurable_psiA {Φ : (Fin n → ℝ) → ℝ} (hΦ : Continuous Φ) (D : Design n) (c : Ret n) :
    Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => psiA Φ D c p.1 p.2) := by
  unfold psiA
  exact (((measurable_tanSq hΦ c).comp
    (((measurable_latC D c).comp measurable_fst).prodMk measurable_snd)).sqrt).pow_const 2

section idxT

variable {Φ : (Fin n → ℝ) → ℝ} {L : ℝ}

lemma lift_euLip (hn : 2 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) (hL0 : 0 ≤ L)
    (hL : EuLip Φ L) : EuLip (fun w => Φ (xLatH c s w)) L := by
  intro v w
  refine (hL _ _).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hL0)
  exact xLatH_dist (by omega) c hs v w

lemma abs_tanSq_le (hn : 2 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) (hL0 : 0 ≤ L)
    (hL : EuLip Φ L) (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x)
    (v : Fin (n - 1) → ℝ) : |tanSq Φ c s v| ≤ 2 * L ^ 2 := by
  unfold tanSq
  have h1 := gradSq_le hL0 (lift_euLip hn c hs hL0 hL) v
  have h2 : |Φ (xLat c s (unitF53 v))| ≤ L := by
    refine (abs_hom_le hL hhom _).trans ?_
    calc L * √(normSq (xLat c s (unitF53 v))) ≤ L * √1 :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (normSq_xLat_le (by omega) c hs v)) hL0
      _ = L := by simp
  have h3 : Φ (xLat c s (unitF53 v)) ^ 2 ≤ L ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have h4 := BstLean.Part151.gradSq_nonneg (fun w => Φ (xLatH c s w)) v
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Φ (xLat c s (unitF53 v)))]

/-- **Lemma LS (`p = 1`) with the realized `Ψ`**: `Var(Φ | a) ≤ E(Ψ | a)/(n − 2)`. -/
lemma idx_var_psi (hn : 3 ≤ n) (D : Design n) (c : Ret n) (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) (a : Ix n) :
    ∫ v, (Φ (xLat c (latC D c a) (unitF53 v)) -
        ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2
          ∂stdGauss (Fin (n - 1)) ≤
      (∫ v, psiA Φ D c a v ∂stdGauss (Fin (n - 1))) / ((n : ℝ) - 2) := by
  have hs := latC_sq_le D c a
  have h := ls_lat (by omega) c hs hL0 hL hhom
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [le_div_iff₀ hn2]
  have h' : ((n : ℝ) - 2) * ∫ v, (Φ (xLat c (latC D c a) (unitF53 v)) -
        ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2
          ∂stdGauss (Fin (n - 1)) ≤ ∫ v, tanSq Φ c (latC D c a) v ∂stdGauss (Fin (n - 1)) := h
  refine (le_of_eq (mul_comm _ _)).trans (h'.trans ?_)
  have hc := hL.continuous hL0
  have mT : Measurable (tanSq Φ c (latC D c a)) := measurable_tanSq_left hc c (latC D c a)
  have bT := abs_tanSq_le (by omega) c hs hL0 hL hhom
  have mP : Measurable (fun v => psiA Φ D c a v) := by
    unfold psiA; exact mT.sqrt.pow_const 2
  have hle : ∀ v, tanSq Φ c (latC D c a) v ≤ psiA Φ D c a v := fun v => by
    unfold psiA
    by_cases h0 : 0 ≤ tanSq Φ c (latC D c a) v
    · rw [Real.sq_sqrt h0]
    · push_neg at h0; exact h0.le.trans (sq_nonneg _)
  have bP : ∀ v, |psiA Φ D c a v| ≤ 2 * L ^ 2 := fun v => by
    unfold psiA
    rw [abs_of_nonneg (sq_nonneg _)]
    by_cases h0 : 0 ≤ tanSq Φ c (latC D c a) v
    · rw [Real.sq_sqrt h0]; exact (le_abs_self _).trans (bT v)
    · push_neg at h0
      rw [Real.sqrt_eq_zero'.mpr h0.le]; simp; positivity
  exact integral_mono (intB mT bT) (intB mP bP) hle

/-- **Lemma LS (order `2q`) with the realized `Ψ`**:
`E(|Φ − E(Φ|a)|^{2q} | a) ≤ (c_q/(√(n−1) − c_q))^{2q}·E(Ψ^q | a)`. -/
lemma idx_mom_psi (hn : 2 ≤ n) (D : Design n) (c : Ret n) (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) {q : ℕ} (hq : 1 ≤ q)
    (hcq : cLS q < √((n : ℝ) - 1)) (a : Ix n) :
    ∫ v, |Φ (xLat c (latC D c a) (unitF53 v)) -
        ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))| ^ (2 * q)
          ∂stdGauss (Fin (n - 1)) ≤
      (cLS q / (√((n : ℝ) - 1) - cLS q)) ^ (2 * q) *
        ∫ v, psiA Φ D c a v ^ q ∂stdGauss (Fin (n - 1)) := by
  have hs := latC_sq_le D c a
  have h := ls_lat_mom hn c hs hL0 hL hhom hq
  set X := momN (stdGauss (Fin (n - 1))) (2 * q) (fun v => Φ (xLat c (latC D c a) (unitF53 v)) -
    ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1)))
  set Y := momN (stdGauss (Fin (n - 1))) (2 * q) (fun v =>
    √(gradSq (fun w => Φ (xLatH c (latC D c a) w)) v - Φ (xLat c (latC D c a) (unitF53 v)) ^ 2))
  have hd : 0 < √((n : ℝ) - 1) - cLS q := by linarith
  have hX0 : 0 ≤ X := momN_nonneg _ _ _
  have hY0 : 0 ≤ Y := momN_nonneg _ _ _
  have hXY : X ≤ cLS q / (√((n : ℝ) - 1) - cLS q) * Y := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]; linarith
  have hp : 2 * q ≠ 0 := by omega
  have hXp : X ^ (2 * q) = ∫ v, |Φ (xLat c (latC D c a) (unitF53 v)) -
      ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))| ^ (2 * q)
        ∂stdGauss (Fin (n - 1)) := momN_pow _ hp _
  have hYp : Y ^ (2 * q) = ∫ v, psiA Φ D c a v ^ q ∂stdGauss (Fin (n - 1)) := by
    rw [momN_pow _ hp]
    congr 1; funext v
    unfold psiA tanSq
    rw [abs_of_nonneg (Real.sqrt_nonneg _), pow_mul]
  rw [← hXp, ← hYp, ← mul_pow]
  exact pow_le_pow_left₀ hX0 hXY _

lemma psiA_bounds (hn : 2 ≤ n) (D : Design n) (c : Ret n) (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) (a : Ix n)
    (v : Fin (n - 1) → ℝ) : 0 ≤ psiA Φ D c a v ∧ psiA Φ D c a v ≤ 2 * L ^ 2 := by
  refine ⟨sq_nonneg _, ?_⟩
  unfold psiA
  have bT := abs_tanSq_le hn c (latC_sq_le D c a) hL0 hL hhom v
  by_cases h0 : 0 ≤ tanSq Φ c (latC D c a) v
  · rw [Real.sq_sqrt h0]; exact (le_abs_self _).trans bT
  · push_neg at h0
    rw [Real.sqrt_eq_zero'.mpr h0.le]; simp; positivity

/-- **The latitude variance from `Ψ`** (Prop. `t7:p07:LG`, `V`):
`∫ Var(Φ|a)² ≤ ((C/n)/(n − 2))²` if `∫∫ Ψ² ≤ (C/n)²`. -/
lemma int_var_psi (hn : 3 ≤ n) (D : Design n) (c : Ret n) (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) {C : ℝ} (hC : 0 ≤ C)
    (h2 : ∫ a, ∫ v, psiA Φ D c a v ^ 2 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (C / n) ^ 2) :
    ∫ a, (∫ v, (Φ (xLat c (latC D c a) (unitF53 v)) -
        ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2
          ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ (C / n / ((n : ℝ) - 2)) ^ 2 := by
  set ν := stdGauss (Fin (n - 1))
  have hc := hL.continuous hL0
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have mP := measurable_psiA hc D c
  have mInt : ∀ {F : Ix n × (Fin (n - 1) → ℝ) → ℝ}, Measurable F →
      Measurable (fun a => ∫ v, F (a, v) ∂ν) := fun hF =>
    (hF.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have mX : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) =>
      Φ (xLat c (latC D c p.1) (unitF53 p.2))) :=
    hc.measurable.comp (measurable_xA D c)
  have mE : Measurable (fun a => ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂ν) := mInt mX
  have mV : Measurable (fun a => ∫ v, (Φ (xLat c (latC D c a) (unitF53 v)) -
      ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂ν) ^ 2 ∂ν) :=
    mInt ((mX.sub (mE.comp measurable_fst)).pow_const 2)
  have bP := psiA_bounds (by omega) D c hL0 hL hhom
  have hbX : ∀ a v, |Φ (xLat c (latC D c a) (unitF53 v))| ≤ L := fun a v => by
    refine (abs_hom_le hL hhom _).trans ?_
    calc L * √(normSq (xLat c (latC D c a) (unitF53 v))) ≤ L * √1 :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
            (normSq_xLat_le (by omega) c (latC_sq_le D c a) v)) hL0
      _ = L := by simp
  have bE : ∀ a, |∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂ν| ≤ L := fun a => by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ w, |Φ (xLat c (latC D c a) (unitF53 w))| ∂ν ≤ ∫ _w, L ∂ν :=
          integral_mono (intB (meas_Xv hc c (latC D c a)).abs (M := L)
            fun w => by rw [abs_abs]; exact hbX a w) (integrable_const _) (hbX a)
      _ = L := by simp
  have bV : ∀ a, 0 ≤ ∫ v, (Φ (xLat c (latC D c a) (unitF53 v)) -
      ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂ν) ^ 2 ∂ν ∧
      ∫ v, (Φ (xLat c (latC D c a) (unitF53 v)) -
        ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂ν) ^ 2 ∂ν ≤ (2 * L) ^ 2 := fun a => by
    refine ⟨integral_nonneg fun v => sq_nonneg _, ?_⟩
    calc _ ≤ ∫ _v, (2 * L) ^ 2 ∂ν := integral_mono
          (intB (((meas_Xv hc c (latC D c a)).sub_const _).pow_const 2)
            (M := (2 * L) ^ 2) fun v => by
              rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans
                (by linarith [hbX a v, bE a])) 2) (integrable_const _) fun v => by
            show _ ≤ (2 * L) ^ 2
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans
              (by linarith [hbX a v, bE a])) 2
      _ = (2 * L) ^ 2 := by simp
  have mE1 : Measurable (fun a => ∫ v, psiA Φ D c a v ∂ν) := mInt mP
  have mE2 : Measurable (fun a => ∫ v, psiA Φ D c a v ^ 2 ∂ν) := mInt (mP.pow_const 2)
  have hpt : ∀ a, (∫ v, (Φ (xLat c (latC D c a) (unitF53 v)) -
      ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂ν) ^ 2 ∂ν) ^ 2 ≤
      (∫ v, psiA Φ D c a v ^ 2 ∂ν) / ((n : ℝ) - 2) ^ 2 := fun a => by
    have h1 := idx_var_psi hn D c hL0 hL hhom a
    have h2 := pow_le_pow_left₀ (bV a).1 h1 2
    have h3 : (∫ v, psiA Φ D c a v ∂ν) ^ 2 ≤ ∫ v, psiA Φ D c a v ^ 2 ∂ν :=
      mean_sq_le ((meas_psi_v hc D c a)) (M := 2 * L ^ 2) fun v => by
        rw [abs_of_nonneg (bP a v).1]; exact (bP a v).2
    rw [div_pow] at h2
    exact h2.trans (div_le_div_of_nonneg_right h3 (by positivity))
  have iL : Integrable (fun a => (∫ v, (Φ (xLat c (latC D c a) (unitF53 v)) -
      ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂ν) ^ 2 ∂ν) ^ 2) (muI n) :=
    intB (mV.pow_const 2) (M := ((2 * L) ^ 2) ^ 2) fun a => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (bV a).1 (bV a).2 2
  have iR : Integrable (fun a => (∫ v, psiA Φ D c a v ^ 2 ∂ν) / ((n : ℝ) - 2) ^ 2) (muI n) :=
    (intB mE2 (M := (2 * L ^ 2) ^ 2) fun a => by
      have h0 : 0 ≤ ∫ v, psiA Φ D c a v ^ 2 ∂ν :=
        integral_nonneg fun v => sq_nonneg _
      rw [abs_of_nonneg h0]
      calc ∫ v, psiA Φ D c a v ^ 2 ∂ν ≤ ∫ _v, (2 * L ^ 2) ^ 2 ∂ν :=
            integral_mono (intB ((meas_psi_v hc D c a).pow_const 2)
              (M := (2 * L ^ 2) ^ 2) fun v => by
                rw [abs_of_nonneg (sq_nonneg _)]
                exact pow_le_pow_left₀ (bP a v).1 (bP a v).2 2) (integrable_const _)
              fun v => pow_le_pow_left₀ (bP a v).1 (bP a v).2 2
        _ = _ := by simp).div_const _
  calc _ ≤ ∫ a, (∫ v, psiA Φ D c a v ^ 2 ∂ν) / ((n : ℝ) - 2) ^ 2 ∂muI n :=
        integral_mono iL iR hpt
    _ = (∫ a, ∫ v, psiA Φ D c a v ^ 2 ∂ν ∂muI n) / ((n : ℝ) - 2) ^ 2 := integral_div _ _
    _ ≤ (C / n) ^ 2 / ((n : ℝ) - 2) ^ 2 := div_le_div_of_nonneg_right h2 (by positivity)
    _ = _ := by rw [div_pow (C / n)]

/-- **The latitude moments of order `2q` from `Ψ`** (Prop. `t7:p07:LG`, `τ_{2q}`):
`∫∫ |Φ − E(Φ|a)|^{2q} ≤ (c_q/(√(n−1) − c_q)·√(C/n))^{2q}` if `∫∫ Ψ^q ≤ (C/n)^q`. -/
lemma int_mom_psi (hn : 2 ≤ n) (D : Design n) (c : Ret n) (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) {q : ℕ} (hq : 1 ≤ q)
    (hcq : cLS q < √((n : ℝ) - 1)) {C : ℝ} (hC : 0 ≤ C)
    (hΨ : ∫ a, ∫ v, psiA Φ D c a v ^ q ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (C / n) ^ q) :
    ∫ a, ∫ v, |Φ (xLat c (latC D c a) (unitF53 v)) -
        ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))| ^ (2 * q)
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      (cLS q / (√((n : ℝ) - 1) - cLS q) * √(C / n)) ^ (2 * q) := by
  set ν := stdGauss (Fin (n - 1))
  have hc := hL.continuous hL0
  have mP := measurable_psiA hc D c
  have mInt : ∀ {F : Ix n × (Fin (n - 1) → ℝ) → ℝ}, Measurable F →
      Measurable (fun a => ∫ v, F (a, v) ∂ν) := fun hF =>
    (hF.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have mX : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) =>
      Φ (xLat c (latC D c p.1) (unitF53 p.2))) :=
    hc.measurable.comp (measurable_xA D c)
  have mE : Measurable (fun a => ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂ν) := mInt mX
  have bP := psiA_bounds hn D c hL0 hL hhom
  have hbX : ∀ a v, |Φ (xLat c (latC D c a) (unitF53 v))| ≤ L := fun a v => by
    refine (abs_hom_le hL hhom _).trans ?_
    calc L * √(normSq (xLat c (latC D c a) (unitF53 v))) ≤ L * √1 :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
            (normSq_xLat_le (by omega) c (latC_sq_le D c a) v)) hL0
      _ = L := by simp
  have bE : ∀ a, |∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂ν| ≤ L := fun a => by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ w, |Φ (xLat c (latC D c a) (unitF53 w))| ∂ν ≤ ∫ _w, L ∂ν :=
          integral_mono (intB (meas_Xv hc c (latC D c a)).abs (M := L)
            fun w => by rw [abs_abs]; exact hbX a w) (integrable_const _) (hbX a)
      _ = L := by simp
  set K := cLS q / (√((n : ℝ) - 1) - cLS q)
  have hK : 0 ≤ K := div_nonneg (cLS_nonneg q) (by linarith)
  have iL : Integrable (fun a => ∫ v, |Φ (xLat c (latC D c a) (unitF53 v)) -
      ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂ν| ^ (2 * q) ∂ν) (muI n) := by
    refine intB (mInt ((mX.sub (mE.comp measurable_fst)).abs.pow_const _))
      (M := (2 * L) ^ (2 * q)) fun a => ?_
    have h0 : 0 ≤ ∫ v, |Φ (xLat c (latC D c a) (unitF53 v)) -
        ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂ν| ^ (2 * q) ∂ν :=
      integral_nonneg fun v => pow_nonneg (abs_nonneg _) _
    rw [abs_of_nonneg h0]
    calc _ ≤ ∫ _v, (2 * L) ^ (2 * q) ∂ν := integral_mono
          (intB (((meas_Xv hc c (latC D c a)).sub_const _).abs.pow_const _)
            (M := (2 * L) ^ (2 * q)) fun v => by
              rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
              exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans
                (by linarith [hbX a v, bE a])) _) (integrable_const _) fun v =>
            pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith [hbX a v, bE a])) _
      _ = _ := by simp
  have iR : Integrable (fun a => K ^ (2 * q) * ∫ v, psiA Φ D c a v ^ q ∂ν) (muI n) := by
    refine (intB (mInt (mP.pow_const q)) (M := (2 * L ^ 2) ^ q) fun a => ?_).const_mul _
    have h0 : 0 ≤ ∫ v, psiA Φ D c a v ^ q ∂ν := integral_nonneg fun v => pow_nonneg (bP a v).1 _
    rw [abs_of_nonneg h0]
    calc ∫ v, psiA Φ D c a v ^ q ∂ν ≤ ∫ _v, (2 * L ^ 2) ^ q ∂ν :=
          integral_mono (intB ((meas_psi_v hc D c a).pow_const q)
            (M := (2 * L ^ 2) ^ q) fun v => by
              rw [abs_of_nonneg (pow_nonneg (bP a v).1 _)]
              exact pow_le_pow_left₀ (bP a v).1 (bP a v).2 q) (integrable_const _)
            fun v => pow_le_pow_left₀ (bP a v).1 (bP a v).2 q
      _ = _ := by simp
  calc _ ≤ ∫ a, K ^ (2 * q) * ∫ v, psiA Φ D c a v ^ q ∂ν ∂muI n :=
        integral_mono iL iR fun a => idx_mom_psi hn D c hL0 hL hhom hq hcq a
    _ = K ^ (2 * q) * ∫ a, ∫ v, psiA Φ D c a v ^ q ∂ν ∂muI n := integral_const_mul _ _
    _ ≤ K ^ (2 * q) * (C / n) ^ q := mul_le_mul_of_nonneg_left hΨ (by positivity)
    _ = (K * √(C / n)) ^ (2 * q) := by
        rw [mul_pow, pow_mul (√(C / n)), Real.sq_sqrt (by positivity)]

end idxT

/-- `K_q = c_q/(√(n−1) − c_q)` (the factor of Lemma LS of order `2q`). -/
noncomputable def kLS (n q : ℕ) : ℝ := cLS q / (√((n : ℝ) - 1) - cLS q)

lemma cLS_lt_sqrt {n q : ℕ} (hn : 61 ≤ n) (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    cLS q < √((n : ℝ) - 1) := by
  refine (cLS_le hq).trans_lt ?_
  have hn' : (60 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (61 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hq' : (q : ℝ) ≤ 12 := by exact_mod_cast hq12
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  rw [show π / 2 * √(2 * q) = √((π / 2) ^ 2 * (2 * q)) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]]
  refine Real.sqrt_lt_sqrt (by positivity) ?_
  have h1 : (π / 2) ^ 2 < (315 / 200) ^ 2 := by
    apply pow_lt_pow_left₀ (by linarith) (by positivity); norm_num
  nlinarith

lemma kLS_pos {n q : ℕ} (hn : 61 ≤ n) (hq : 1 ≤ q) (hq12 : q ≤ 12) : 0 < kLS n q := by
  unfold kLS
  exact div_pos (cLS_pos hq) (by linarith [cLS_lt_sqrt hn hq hq12])

/-- **The latitude-moment interface from the realized certificate `Ψ`** (Prop. `t7:p07:LG`): the
moments `∫∫ Ψ_φ^j ≤ (C_φ/n)^j` (`j = 2, 4, 6, r`) for `φ = λ, σ` give `LatMom` with
`V = (C/n)/(n − 2)` and `τ_{2q} = K_q √(C/n)`. -/
noncomputable def latMomOfPsi (hn : 61 ≤ n) (D : Design n) (c : Ret n) {σl CL CS VS βlow : ℝ}
    {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ 12) (hCL : 0 < CL) (hCS : 0 < CS) (hVS0 : 0 ≤ VS)
    (hβ : 0 ≤ βlow)
    (hL2 : ∫ a, ∫ v, psiA (lamX D c) D c a v ^ 2 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 2)
    (hL4 : ∫ a, ∫ v, psiA (lamX D c) D c a v ^ 4 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 4)
    (hL6 : ∫ a, ∫ v, psiA (lamX D c) D c a v ^ 6 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 6)
    (hLr : ∫ a, ∫ v, psiA (lamX D c) D c a v ^ r ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ r)
    (hS2 : ∫ a, ∫ v, psiA (sigX D c) D c a v ^ 2 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 2)
    (hS4 : ∫ a, ∫ v, psiA (sigX D c) D c a v ^ 4 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 4)
    (hS6 : ∫ a, ∫ v, psiA (sigX D c) D c a v ^ 6 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 6)
    (hSr : ∫ a, ∫ v, psiA (sigX D c) D c a v ^ r ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ r)
    (hVS : ∫ a, (∫ v, (sA D c a v - ∫ w, sA D c a w ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ VS ^ 2)
    (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA D c a v < σl} ∂muI n ≤ βlow) :
    LatMom D c σl (2 * r) where
  Vs := CS / n / ((n : ℝ) - 2)
  Vl := CL / n / ((n : ℝ) - 2)
  VS := VS
  ts8 := kLS n 4 * √(CS / n)
  ts12 := kLS n 6 * √(CS / n)
  tl8 := kLS n 4 * √(CL / n)
  tl12 := kLS n 6 * √(CL / n)
  tlq := kLS n r * √(CL / n)
  tsq := kLS n r * √(CS / n)
  βlow := βlow
  hVs0 := by
    have : (0 : ℝ) < (n : ℝ) - 2 := by
      have : (61 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    positivity
  hVl0 := by
    have : (0 : ℝ) < (n : ℝ) - 2 := by
      have : (61 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    positivity
  hVS0 := hVS0
  hts8 := mul_pos (kLS_pos hn (by norm_num) (by norm_num))
    (Real.sqrt_pos.mpr (div_pos hCS (by have : (61 : ℝ) ≤ n := by exact_mod_cast hn
                                        linarith)))
  hts12 := mul_pos (kLS_pos hn (by norm_num) (by norm_num))
    (Real.sqrt_pos.mpr (div_pos hCS (by have : (61 : ℝ) ≤ n := by exact_mod_cast hn
                                        linarith)))
  htl8 := mul_pos (kLS_pos hn (by norm_num) (by norm_num))
    (Real.sqrt_pos.mpr (div_pos hCL (by have : (61 : ℝ) ≤ n := by exact_mod_cast hn
                                        linarith)))
  htl12 := mul_pos (kLS_pos hn (by norm_num) (by norm_num))
    (Real.sqrt_pos.mpr (div_pos hCL (by have : (61 : ℝ) ≤ n := by exact_mod_cast hn
                                        linarith)))
  htlq := (mul_pos (kLS_pos hn hr1 hr) (Real.sqrt_pos.mpr (div_pos hCL
    (by have : (61 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)))).le
  htsq := (mul_pos (kLS_pos hn hr1 hr) (Real.sqrt_pos.mpr (div_pos hCS
    (by have : (61 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)))).le
  hβl := hβ
  hVs := int_var_psi (by omega) D c (lipSig_nonneg D c) (sigX_euLip D c)
    (fun t x ht => sigX_hom D c t x ht) hCS.le hS2
  hVl := int_var_psi (by omega) D c (lipLam_nonneg D c) (lamX_euLip D c)
    (fun t x ht => lamX_hom D c t x ht) hCL.le hL2
  hVS := hVS
  hs8 := int_mom_psi (by omega) D c (lipSig_nonneg D c) (sigX_euLip D c)
    (fun t x ht => sigX_hom D c t x ht) (q := 4) (by norm_num)
    (cLS_lt_sqrt hn (by norm_num) (by norm_num)) hCS.le hS4
  hs12 := int_mom_psi (by omega) D c (lipSig_nonneg D c) (sigX_euLip D c)
    (fun t x ht => sigX_hom D c t x ht) (q := 6) (by norm_num)
    (cLS_lt_sqrt hn (by norm_num) (by norm_num)) hCS.le hS6
  hl8 := int_mom_psi (by omega) D c (lipLam_nonneg D c) (lamX_euLip D c)
    (fun t x ht => lamX_hom D c t x ht) (q := 4) (by norm_num)
    (cLS_lt_sqrt hn (by norm_num) (by norm_num)) hCL.le hL4
  hl12 := int_mom_psi (by omega) D c (lipLam_nonneg D c) (lamX_euLip D c)
    (fun t x ht => lamX_hom D c t x ht) (q := 6) (by norm_num)
    (cLS_lt_sqrt hn (by norm_num) (by norm_num)) hCL.le hL6
  hlq := int_mom_psi (by omega) D c (lipLam_nonneg D c) (lamX_euLip D c)
    (fun t x ht => lamX_hom D c t x ht) hr1 (cLS_lt_sqrt hn hr1 hr) hCL.le hLr
  hsq := int_mom_psi (by omega) D c (lipSig_nonneg D c) (sigX_euLip D c)
    (fun t x ht => sigX_hom D c t x ht) hr1 (cLS_lt_sqrt hn hr1 hr) hCS.le hSr
  hmass := hmass

open BstLean.Part130 BstLean.Part156 BstLean.Part159 BstLean.Part160 in
/-- **The classifier theorem for the paper's design (`n ≥ 23 000`) with the Agent replacement
reduced to the realized latitude certificate `Ψ`, the scale moment `V_S`, the mass below the
floor, the norm of `c_A`, the root sum and the bias.** For every retained value `c` of the good
set there are constants with: the `Ψ`-moments of `λ` and `σ` (orders `2, 4, 6, r`, `r ≤ 12`; the
paper's `‖Ψ_φ‖_{L^{12}(x)} ≤ C_lat/n`), `V_S`, `β_low`, `|c_A|² ≤ C_A`, `ε₀ < 1`,
`rootFL ≤ 0.002159` for the interface built by `latMomOfPsi`, and `BIAS_hyp` at `0.004295`. -/
theorem classifier_paper_psi (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    (hM : ∀ c ∈ goodSet (HP n) (Ethm (paperCentres n) ∩ Ethp (paperCentres n))
        (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (wl ws σl η CA CL CS VS βlow : ℝ) (r : ℕ) (h0 : 0 < η) (h1 : η < 1) (hr1 : 1 ≤ r)
        (hr : r ≤ 12) (hCL : 0 < CL) (hCS : 0 < CS) (hVS0 : 0 ≤ VS) (hβ : 0 ≤ βlow)
        (hL2 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ 2
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 2)
        (hL4 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ 4
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 4)
        (hL6 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ 6
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 6)
        (hLr : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ r
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ r)
        (hS2 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ 2
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 2)
        (hS4 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ 4
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 4)
        (hS6 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ 6
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 6)
        (hSr : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ r
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ r)
        (hVS : ∫ a, (∫ v, (sA (paperDesign n fT wT hf hw) c a v -
            ∫ w, sA (paperDesign n fT wT hf hw) c a w ∂stdGauss (Fin (n - 1))) ^ 2
          ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ VS ^ 2)
        (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA (paperDesign n fT wT hf hw) c a v < σl}
          ∂muI n ≤ βlow),
        0 < wl ∧ 0 < ws ∧ 0 < σl ∧ 0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ CA ∧
        eps0 ws σl < 1 ∧
        rootFL wl ws η CA (latMomOfPsi (by omega) (paperDesign n fT wT hf hw) c hr1 hr hCL hCS
          hVS0 hβ hL2 hL4 hL6 hLr hS2 hS4 hS6 hSr hVS hmass) ≤ 2159 / 10 ^ 6 ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_paper_mom hn fT wT hf hw t fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CA, CL, CS, VS, βlow, r, h0, h1, hr1, hr, hCL, hCS, hVS0, hβ, hL2, hL4,
    hL6, hLr, hS2, hS4, hS6, hSr, hVS, hmass, hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩ := hM c hc
  exact ⟨wl, ws, σl, η, CA, 2 * r, h0, h1, latMomOfPsi (by omega) _ c hr1 hr hCL hCS hVS0 hβ hL2
    hL4 hL6 hLr hS2 hS4 hS6 hSr hVS hmass, hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩

end BstLean.Part162

open BstLean.Part162 in
#print axioms int_mom_psi
open BstLean.Part162 in
#print axioms classifier_paper_psi
