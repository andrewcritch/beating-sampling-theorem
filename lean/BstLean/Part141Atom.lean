import BstLean.Part141Defs
import BstLean.Part137Smooth

/-!
# Part 141, item 1 (`atomSum141`): a finite ReLU sum with rational atoms and weights

Role: `delegations/statements/p141-spec.md`, item 1. Paper source: `onW8c-cx.md` §2 (the clipped,
rounded grid of atoms; Lemma R for the rational weights).

`ψ_s(x) = psiS s x = E_Z relu(x + sZ)`, `Z` a standard Gaussian number.

* `psiS_lip_x`, `psiS_lip_s`: `ψ_s(x)` is 1-Lipschitz in `x` and in `s`.
* `cell_integral`: for the cell index `quant q R`: `E f(quant Z) = Σ_ℓ pR ℓ·f(ℓ − Rq)`.
* `pR_sum`, `pQ_sum`, `pQ_nonneg`: the real and the rational weights are nonnegative, with sum 1.
* `atom_couple`: `|Σ_ℓ pR ℓ·relu(x + s z_ℓ) − ψ_s(x)| ≤ s(1/q + 4/2^R)` (the coupling
  `Z ↦ ⌊clip(Z)q⌋/q`; the clipping error is at most `exp(|Z| − R)`).
* `atom_round`: the change from `pR` to the rational `pQ` costs at most `s·4R²q/D`.
* **`atomSum141`**: `|Σ_ℓ pQ ℓ·relu(x + s z_ℓ) − ψ_s(x)| ≤ s(1/q + 4/2^R + 4R²q/D)`, every `x`,
  every `s ≥ 0`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part141

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part137

/-! ## Tools -/

lemma relu_lip (a b : ℝ) : |relu a - relu b| ≤ |a - b| := by
  unfold relu
  rw [max_comm 0 a, max_comm 0 b]
  exact abs_max_sub_max_le_abs a b 0

lemma abs_int_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g h : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    (H : ∀ z, |f z - g z| ≤ h z) : |∫ z, f z ∂μ - ∫ z, g z ∂μ| ≤ ∫ z, h z ∂μ := by
  rw [← integral_sub hf hg]
  exact abs_integral_le_integral_abs.trans (integral_mono (hf.sub hg).abs hh H)

lemma integrable_abs_gauss : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
  have h := (integrable_pow_gauss 1).abs
  simpa using h

lemma integral_abs_gauss_le : ∫ z : ℝ, |z| ∂gaussianReal 0 1 ≤ 1 := by
  have h2 : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    rw [BstLean.Part29.gaussMom_eq 2]
    norm_num [BstLean.Part29.gaussMom, Nat.doubleFactorial, Nat.even_iff]
  have hi : Integrable (fun z : ℝ => (1 + z ^ 2) / 2) (gaussianReal 0 1) :=
    ((integrable_const _).add (integrable_pow_gauss 2)).div_const 2
  calc ∫ z : ℝ, |z| ∂gaussianReal 0 1 ≤ ∫ z : ℝ, (1 + z ^ 2) / 2 ∂gaussianReal 0 1 :=
        integral_mono integrable_abs_gauss hi
          (fun z => by nlinarith [sq_nonneg (|z| - 1), sq_abs z])
    _ = 1 := by
        rw [integral_div, integral_add (integrable_const _) (integrable_pow_gauss 2), h2]
        simp

/-- `ψ_s(x)` is 1-Lipschitz in `x`. -/
theorem psiS_lip_x (s x x' : ℝ) : |psiS s x - psiS s x'| ≤ |x - x'| := by
  have h := abs_int_sub_le (μ := gaussianReal 0 1) (integrable_relu_shift x s)
    (integrable_relu_shift x' s) (integrable_const (|x - x'|)) (fun z => by
      refine (relu_lip _ _).trans (le_of_eq ?_)
      congr 1
      ring)
  simpa [psiS] using h

/-- `ψ_s(x)` is 1-Lipschitz in `s` (`E|Z| ≤ 1`). -/
theorem psiS_lip_s (s s' x : ℝ) : |psiS s x - psiS s' x| ≤ |s - s'| := by
  have h := abs_int_sub_le (μ := gaussianReal 0 1) (integrable_relu_shift x s)
    (integrable_relu_shift x s') (integrable_abs_gauss.const_mul (|s - s'|)) (fun z => by
      refine (relu_lip _ _).trans (le_of_eq ?_)
      rw [← abs_mul]
      congr 1
      ring)
  rw [integral_const_mul] at h
  have h1 := mul_le_mul_of_nonneg_left integral_abs_gauss_le (abs_nonneg (s - s'))
  unfold psiS
  linarith

/-! ## The cells -/

section cells

variable (q R : ℕ)

/-- The integer index of cell `ℓ`: `ℓ − Rq`. -/
def off (ℓ : Fin (2 * R * q + 1)) : ℤ := ((ℓ : ℕ) : ℤ) - ((R * q : ℕ) : ℤ)

lemma off_inj : Function.Injective (off q R) := by
  intro a b h
  unfold off at h
  ext
  omega

lemma quant_mem (z : ℝ) : ∃ ℓ : Fin (2 * R * q + 1), quant q R z = off q R ℓ := by
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : -(R : ℝ) ≤ max (-(R : ℝ)) (min (R : ℝ) z) := le_max_left _ _
  have h2 : max (-(R : ℝ)) (min (R : ℝ) z) ≤ R := max_le (by linarith) (min_le_left _ _)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = R * q := ⟨_, rfl⟩
  have h2K : 2 * R * q = 2 * K := by rw [hK]; ring
  have l1 : -((K : ℕ) : ℤ) ≤ quant q R z := by
    unfold quant
    rw [Int.le_floor, hK]
    push_cast
    nlinarith
  have l2 : quant q R z ≤ ((K : ℕ) : ℤ) := by
    have h3 : ((quant q R z : ℤ) : ℝ) ≤ ((K : ℕ) : ℝ) := by
      unfold quant
      refine (Int.floor_le _).trans ?_
      rw [hK]
      push_cast
      nlinarith
    exact_mod_cast h3
  have h0 : 0 ≤ quant q R z + (K : ℤ) := by omega
  refine ⟨⟨(quant q R z + (K : ℤ)).toNat, by omega⟩, ?_⟩
  unfold off
  rw [← hK]
  simp only
  omega

lemma measurable_quant : Measurable (quant q R) := by
  unfold quant
  exact Int.measurable_floor.comp
    ((measurable_const.max (measurable_const.min measurable_id)).mul_const _)

lemma measurableSet_cell (ℓ : Fin (2 * R * q + 1)) :
    MeasurableSet {z : ℝ | quant q R z = off q R ℓ} :=
  measurable_quant q R (measurableSet_singleton _)

/-- `E f(quant Z) = Σ_ℓ pR ℓ·f(ℓ − Rq)`. -/
lemma cell_integral (f : ℤ → ℝ) :
    Integrable (fun z => f (quant q R z)) (gaussianReal 0 1) ∧
      ∫ z, f (quant q R z) ∂gaussianReal 0 1 = ∑ ℓ, pR q R ℓ * f (off q R ℓ) := by
  have hpt : ∀ z, f (quant q R z) = ∑ ℓ, ({z : ℝ | quant q R z = off q R ℓ}).indicator
      (fun _ => f (off q R ℓ)) z := by
    intro z
    obtain ⟨ℓ0, h0⟩ := quant_mem q R z
    rw [Finset.sum_eq_single ℓ0]
    · rw [Set.indicator_of_mem (show z ∈ {z : ℝ | quant q R z = off q R ℓ0} from h0), h0]
    · intro b _ hb
      exact Set.indicator_of_notMem
        (fun h : quant q R z = off q R b => hb (off_inj q R (h.symm.trans h0))) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hint : ∀ ℓ, Integrable (({z : ℝ | quant q R z = off q R ℓ}).indicator
      (fun _ => f (off q R ℓ))) (gaussianReal 0 1) := fun ℓ =>
    (integrable_const _).indicator (measurableSet_cell q R ℓ)
  have e : (fun z => f (quant q R z)) = fun z => ∑ ℓ,
      ({z : ℝ | quant q R z = off q R ℓ}).indicator (fun _ => f (off q R ℓ)) z := funext hpt
  rw [e]
  refine ⟨integrable_finsetSum _ (fun ℓ _ => hint ℓ), ?_⟩
  rw [integral_finsetSum _ (fun ℓ _ => hint ℓ)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [integral_indicator_const _ (measurableSet_cell q R ℓ), smul_eq_mul]
  rfl

lemma pR_nonneg (ℓ : Fin (2 * R * q + 1)) : 0 ≤ pR q R ℓ := measureReal_nonneg

lemma pR_sum : ∑ ℓ, pR q R ℓ = 1 := by
  have h := (cell_integral q R (fun _ => (1 : ℝ))).2
  simpa using h.symm

end cells

/-! ## The rational weights -/

section weights

variable (q R D : ℕ)

lemma pQ_zero : pQ q R D 0 = 1 - ∑ ℓ' ∈ Finset.univ.erase (0 : Fin (2 * R * q + 1)),
    ((⌊(D : ℝ) * pR q R ℓ'⌋ : ℤ) : ℚ) / (D : ℚ) := by
  unfold pQ
  simp

lemma pQ_ne {ℓ : Fin (2 * R * q + 1)} (h : ℓ ≠ 0) :
    pQ q R D ℓ = ((⌊(D : ℝ) * pR q R ℓ⌋ : ℤ) : ℚ) / (D : ℚ) := by
  unfold pQ
  simp [h]

/-- The rational weights have sum `1`. -/
theorem pQ_sum : ∑ ℓ, pQ q R D ℓ = 1 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (2 * R * q + 1))),
    Finset.sum_congr rfl (fun ℓ hℓ => pQ_ne q R D (Finset.ne_of_mem_erase hℓ)), pQ_zero]
  ring

theorem pQ_sum_real : ∑ ℓ, ((pQ q R D ℓ : ℚ) : ℝ) = 1 := by
  have h := congrArg (fun r : ℚ => (r : ℝ)) (pQ_sum q R D)
  push_cast at h
  exact h

lemma pQ_zero_real : ((pQ q R D 0 : ℚ) : ℝ) =
    1 - ∑ ℓ' ∈ Finset.univ.erase (0 : Fin (2 * R * q + 1)),
      ((⌊(D : ℝ) * pR q R ℓ'⌋ : ℤ) : ℝ) / (D : ℝ) := by
  rw [pQ_zero]
  push_cast
  rfl

lemma pQ_ne_real {ℓ : Fin (2 * R * q + 1)} (h : ℓ ≠ 0) :
    ((pQ q R D ℓ : ℚ) : ℝ) = ((⌊(D : ℝ) * pR q R ℓ⌋ : ℤ) : ℝ) / (D : ℝ) := by
  rw [pQ_ne q R D h]
  push_cast
  rfl

variable {q R D}

lemma fl_le (hD : 1 ≤ D) (p : ℝ) : ((⌊(D : ℝ) * p⌋ : ℤ) : ℝ) / (D : ℝ) ≤ p := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [div_le_iff₀ hD']
  linarith [Int.floor_le ((D : ℝ) * p)]

lemma fl_ge (hD : 1 ≤ D) (p : ℝ) : p - 1 / (D : ℝ) ≤ ((⌊(D : ℝ) * p⌋ : ℤ) : ℝ) / (D : ℝ) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [le_div_iff₀ hD', sub_mul, one_div, inv_mul_cancel₀ hD'.ne']
  linarith [Int.sub_one_lt_floor ((D : ℝ) * p)]

lemma fl_nonneg {p : ℝ} (hp : 0 ≤ p) : 0 ≤ ((⌊(D : ℝ) * p⌋ : ℤ) : ℝ) / (D : ℝ) :=
  div_nonneg (Int.cast_nonneg (Int.floor_nonneg.2 (mul_nonneg (Nat.cast_nonneg D) hp)))
    (Nat.cast_nonneg D)

theorem pQ_nonneg_real (hD : 1 ≤ D) (ℓ : Fin (2 * R * q + 1)) :
    0 ≤ ((pQ q R D ℓ : ℚ) : ℝ) := by
  by_cases h : ℓ = 0
  · subst h
    rw [pQ_zero_real]
    have h1 : ∑ ℓ' ∈ Finset.univ.erase (0 : Fin (2 * R * q + 1)),
        ((⌊(D : ℝ) * pR q R ℓ'⌋ : ℤ) : ℝ) / (D : ℝ) ≤
        ∑ ℓ' ∈ Finset.univ.erase (0 : Fin (2 * R * q + 1)), pR q R ℓ' :=
      Finset.sum_le_sum fun ℓ' _ => fl_le hD _
    have h2 := Finset.add_sum_erase Finset.univ (pR q R)
      (Finset.mem_univ (0 : Fin (2 * R * q + 1)))
    rw [pR_sum] at h2
    linarith [pR_nonneg q R 0]
  · rw [pQ_ne_real q R D h]
    exact fl_nonneg (pR_nonneg q R ℓ)

/-- The rational weights are nonnegative. -/
theorem pQ_nonneg (hD : 1 ≤ D) (ℓ : Fin (2 * R * q + 1)) : 0 ≤ pQ q R D ℓ :=
  (Rat.cast_nonneg (K := ℝ)).1 (pQ_nonneg_real hD ℓ)

end weights

/-! ## The atom sum against `ψ_s` -/

lemma zQ_cast (q R : ℕ) (ℓ : Fin (2 * R * q + 1)) :
    ((zQ q R ℓ : ℚ) : ℝ) = (((ℓ : ℕ) : ℝ) - (R : ℝ) * q) / (q : ℝ) := by
  unfold zQ
  push_cast
  rfl

lemma clip_err (R : ℕ) (z : ℝ) : |max (-(R : ℝ)) (min (R : ℝ) z) - z| ≤ rexp (|z| - R) := by
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have he := Real.add_one_le_exp (|z| - R)
  have hp := Real.exp_pos (|z| - R)
  rcases le_total z (-(R : ℝ)) with h1 | h1
  · rw [min_eq_right (by linarith), max_eq_left h1, abs_of_nonneg (by linarith)]
    have : |z| = -z := abs_of_nonpos (by linarith)
    linarith
  · rcases le_total z R with h2 | h2
    · rw [min_eq_right h2, max_eq_right h1, sub_self, abs_zero]
      exact hp.le
    · rw [min_eq_left h2, max_eq_right (by linarith), abs_of_nonpos (by linarith)]
      have : |z| = z := abs_of_nonneg (by linarith)
      linarith

lemma quant_err {q : ℕ} (hq : 1 ≤ q) (R : ℕ) (z : ℝ) :
    |((quant q R z : ℤ) : ℝ) / (q : ℝ) - z| ≤
      1 / (q : ℝ) + (rexp (1 * z) + rexp (-1 * z)) * rexp (-(R : ℝ)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set c : ℝ := max (-(R : ℝ)) (min (R : ℝ) z) with hc
  have h1 : ((quant q R z : ℤ) : ℝ) ≤ c * q := Int.floor_le _
  have h2 : c * q - 1 < ((quant q R z : ℤ) : ℝ) := Int.sub_one_lt_floor _
  have h3 : |((quant q R z : ℤ) : ℝ) / (q : ℝ) - c| ≤ 1 / (q : ℝ) := by
    rw [abs_le]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hq', add_mul, neg_mul, one_div, inv_mul_cancel₀ hq'.ne']
      linarith
    · rw [sub_le_iff_le_add, div_le_iff₀ hq', add_mul, one_div, inv_mul_cancel₀ hq'.ne']
      linarith
  have h4 : |c - z| ≤ rexp (|z| - R) := clip_err R z
  have h5 : rexp (|z| - R) ≤ (rexp (1 * z) + rexp (-1 * z)) * rexp (-(R : ℝ)) := by
    rw [sub_eq_add_neg, Real.exp_add]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rcases le_total 0 z with h | h
    · rw [abs_of_nonneg h, one_mul]
      linarith [Real.exp_pos (-1 * z)]
    · rw [abs_of_nonpos h, neg_one_mul]
      linarith [Real.exp_pos (1 * z)]
  calc |((quant q R z : ℤ) : ℝ) / (q : ℝ) - z|
      = |(((quant q R z : ℤ) : ℝ) / (q : ℝ) - c) + (c - z)| := by congr 1; ring
    _ ≤ |((quant q R z : ℤ) : ℝ) / (q : ℝ) - c| + |c - z| := abs_add_le _ _
    _ ≤ _ := by linarith

lemma mgf_gauss (t : ℝ) : ∫ z : ℝ, rexp (t * z) ∂gaussianReal 0 1 = rexp (t ^ 2 / 2) := by
  have h := congrFun (mgf_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))) t
  simp only [mgf, id] at h
  rw [h]
  congr 1
  simp

lemma exp_half_le : rexp (1 / 2) ≤ 2 := by
  have h : rexp (1 / 2) ^ 2 = rexp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h1 := Real.exp_one_lt_d9
  nlinarith [Real.exp_pos (1 / 2 : ℝ)]

lemma exp_neg_nat_le (R : ℕ) : rexp (-(R : ℝ)) ≤ 1 / (2 : ℝ) ^ R := by
  have h2 : (2 : ℝ) ≤ rexp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h3 : (2 : ℝ) ^ R ≤ rexp R := by
    refine (pow_le_pow_left₀ (by norm_num) h2 R).trans_eq ?_
    rw [← Real.exp_nat_mul, mul_one]
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by positivity) h3

/-- **The coupling.** `|Σ_ℓ pR ℓ·relu(x + s z_ℓ) − ψ_s(x)| ≤ s(1/q + 4/2^R)`. -/
theorem atom_couple {q : ℕ} (hq : 1 ≤ q) (R : ℕ) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    |atomSum (pR q R) (fun ℓ => ((zQ q R ℓ : ℚ) : ℝ)) s x - psiS s x| ≤
      s * (1 / (q : ℝ) + 4 / (2 : ℝ) ^ R) := by
  obtain ⟨hi, hv⟩ := cell_integral q R (fun k : ℤ => relu (x + s * ((k : ℝ) / (q : ℝ))))
  have ev : atomSum (pR q R) (fun ℓ => ((zQ q R ℓ : ℚ) : ℝ)) s x =
      ∫ z, relu (x + s * (((quant q R z : ℤ) : ℝ) / (q : ℝ))) ∂gaussianReal 0 1 := by
    rw [hv]
    unfold atomSum
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    beta_reduce
    rw [zQ_cast]
    unfold off
    push_cast
    rfl
  have ie : ∀ t : ℝ, Integrable (fun z : ℝ => rexp (t * z)) (gaussianReal 0 1) := fun t =>
    integrable_exp_mul_gaussianReal t
  have i2 : Integrable (fun a : ℝ => rexp (1 * a) + rexp (-1 * a)) (gaussianReal 0 1) :=
    (ie 1).add (ie (-1))
  have hh : Integrable (fun z : ℝ =>
      s * (1 / (q : ℝ) + (rexp (1 * z) + rexp (-1 * z)) * rexp (-(R : ℝ)))) (gaussianReal 0 1) :=
    ((integrable_const _).add (i2.mul_const _)).const_mul s
  have hI : ∫ a : ℝ, (1 / (q : ℝ) + (rexp (1 * a) + rexp (-1 * a)) * rexp (-(R : ℝ)))
      ∂gaussianReal 0 1 = 1 / (q : ℝ) + (rexp (1 / 2) + rexp (1 / 2)) * rexp (-(R : ℝ)) := by
    rw [integral_add (integrable_const _) (i2.mul_const _), integral_mul_const,
      integral_add (ie 1) (ie (-1)), mgf_gauss, mgf_gauss, integral_const, probReal_univ,
      one_smul]
    norm_num
  have h := abs_int_sub_le (μ := gaussianReal 0 1) hi (integrable_relu_shift x s) hh (fun z => by
    refine (relu_lip _ _).trans ?_
    have e : x + s * (((quant q R z : ℤ) : ℝ) / (q : ℝ)) - (x + s * z) =
        s * (((quant q R z : ℤ) : ℝ) / (q : ℝ) - z) := by ring
    rw [e, abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left (quant_err hq R z) hs)
  rw [integral_const_mul, hI] at h
  rw [ev]
  unfold psiS
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hs)
  have h1 := exp_half_le
  have h2 := exp_neg_nat_le R
  have h3 : (0 : ℝ) ≤ rexp (-(R : ℝ)) := (Real.exp_pos _).le
  have h4 : (rexp (1 / 2) + rexp (1 / 2)) * rexp (-(R : ℝ)) ≤ 4 * (1 / (2 : ℝ) ^ R) :=
    mul_le_mul (by linarith) h2 h3 (by norm_num)
  have e3 : (4 : ℝ) / (2 : ℝ) ^ R = 4 * (1 / (2 : ℝ) ^ R) := by ring
  rw [e3]
  linarith

/-- **Lemma R.** The change from the cell probabilities to the rational weights costs at most
`s·4R²q/D`. -/
theorem atom_round {q R D : ℕ} (hq : 1 ≤ q) (hD : 1 ≤ D) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    |atomSum (fun ℓ => ((pQ q R D ℓ : ℚ) : ℝ)) (fun ℓ => ((zQ q R ℓ : ℚ) : ℝ)) s x -
        atomSum (pR q R) (fun ℓ => ((zQ q R ℓ : ℚ) : ℝ)) s x| ≤
      s * (4 * (R : ℝ) ^ 2 * (q : ℝ) / (D : ℝ)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  set g : Fin (2 * R * q + 1) → ℝ := fun ℓ => relu (x + s * ((zQ q R ℓ : ℚ) : ℝ)) with hg
  set fl : Fin (2 * R * q + 1) → ℝ := fun ℓ => ((⌊(D : ℝ) * pR q R ℓ⌋ : ℤ) : ℝ) / (D : ℝ)
    with hfl
  set E := Finset.univ.erase (0 : Fin (2 * R * q + 1)) with hE
  have hp0 := Finset.add_sum_erase Finset.univ (pR q R)
    (Finset.mem_univ (0 : Fin (2 * R * q + 1)))
  rw [pR_sum, ← hE] at hp0
  have key : atomSum (fun ℓ => ((pQ q R D ℓ : ℚ) : ℝ)) (fun ℓ => ((zQ q R ℓ : ℚ) : ℝ)) s x -
        atomSum (pR q R) (fun ℓ => ((zQ q R ℓ : ℚ) : ℝ)) s x =
      ∑ ℓ ∈ E, (pR q R ℓ - fl ℓ) * (g 0 - g ℓ) := by
    unfold atomSum
    beta_reduce
    rw [← Finset.sum_sub_distrib,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (2 * R * q + 1))), ← hE]
    have hne : ∀ ℓ ∈ E, ((pQ q R D ℓ : ℚ) : ℝ) * relu (x + s * ((zQ q R ℓ : ℚ) : ℝ)) -
        pR q R ℓ * relu (x + s * ((zQ q R ℓ : ℚ) : ℝ)) = -((pR q R ℓ - fl ℓ) * g ℓ) := by
      intro ℓ hℓ
      rw [pQ_ne_real q R D (Finset.ne_of_mem_erase hℓ)]
      simp only [hg, hfl]
      ring
    rw [Finset.sum_congr rfl hne, pQ_zero_real, Finset.sum_neg_distrib]
    have e1 : ∑ ℓ ∈ E, (pR q R ℓ - fl ℓ) * (g 0 - g ℓ) =
        (∑ ℓ ∈ E, pR q R ℓ - ∑ ℓ ∈ E, fl ℓ) * g 0 - ∑ ℓ ∈ E, (pR q R ℓ - fl ℓ) * g ℓ := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1]
    have e2 : pR q R 0 = 1 - ∑ ℓ ∈ E, pR q R ℓ := by linarith
    rw [e2]
    change (1 - ∑ ℓ ∈ E, fl ℓ) * g 0 - (1 - ∑ ℓ ∈ E, pR q R ℓ) * g 0 +
      -∑ ℓ ∈ E, (pR q R ℓ - fl ℓ) * g ℓ = _
    ring
  rw [key]
  have hterm : ∀ ℓ ∈ E, |(pR q R ℓ - fl ℓ) * (g 0 - g ℓ)| ≤ 1 / (D : ℝ) * (s * (2 * (R : ℝ))) := by
    intro ℓ _
    have a1 : 0 ≤ pR q R ℓ - fl ℓ := sub_nonneg.2 (fl_le hD _)
    have a2 : pR q R ℓ - fl ℓ ≤ 1 / (D : ℝ) := by linarith [fl_ge hD (pR q R ℓ)]
    have a3 : |g 0 - g ℓ| ≤ s * (2 * (R : ℝ)) := by
      refine (relu_lip _ _).trans ?_
      have e : x + s * ((zQ q R 0 : ℚ) : ℝ) - (x + s * ((zQ q R ℓ : ℚ) : ℝ)) =
          s * (-(((ℓ : ℕ) : ℝ) / (q : ℝ))) := by
        rw [zQ_cast, zQ_cast]
        simp only [Fin.val_zero, Nat.cast_zero]
        ring
      rw [e, abs_mul, abs_of_nonneg hs, abs_neg, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ hs
      rw [div_le_iff₀ hq']
      have : (ℓ : ℕ) ≤ 2 * R * q := Nat.lt_succ_iff.mp ℓ.isLt
      have h' : ((ℓ : ℕ) : ℝ) ≤ ((2 * R * q : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      linarith
    rw [abs_mul, abs_of_nonneg a1]
    exact mul_le_mul a2 a3 (abs_nonneg _) (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans (le_of_eq ?_))
  rw [Finset.sum_const, nsmul_eq_mul, hE, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- **Item 1 (`atomSum141`).** The finite ReLU sum with the rational atoms `zQ q R` (the grid of
mesh `1/q` on `[−R, R]`) and the rational weights `pQ q R D` is uniformly close to the Gaussian
smoothing `ψ_s` of ReLU: for every `x` and every `s ≥ 0`,
`|Σ_ℓ pQ ℓ·relu(x + s z_ℓ) − ψ_s(x)| ≤ s·(1/q + 4/2^R + 4R²q/D)`. -/
theorem atomSum141 {q R D : ℕ} (hq : 1 ≤ q) (hD : 1 ≤ D) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    |atomSum (fun ℓ => ((pQ q R D ℓ : ℚ) : ℝ)) (fun ℓ => ((zQ q R ℓ : ℚ) : ℝ)) s x - psiS s x| ≤
      s * (1 / (q : ℝ) + 4 / (2 : ℝ) ^ R + 4 * (R : ℝ) ^ 2 * (q : ℝ) / (D : ℝ)) := by
  have h1 := atom_round (R := R) hq hD hs x
  have h2 := atom_couple hq R hs x
  have h3 := abs_sub_le
    (atomSum (fun ℓ => ((pQ q R D ℓ : ℚ) : ℝ)) (fun ℓ => ((zQ q R ℓ : ℚ) : ℝ)) s x)
    (atomSum (pR q R) (fun ℓ => ((zQ q R ℓ : ℚ) : ℝ)) s x) (psiS s x)
  have e : s * (1 / (q : ℝ) + 4 / (2 : ℝ) ^ R + 4 * (R : ℝ) ^ 2 * (q : ℝ) / (D : ℝ)) =
      s * (4 * (R : ℝ) ^ 2 * (q : ℝ) / (D : ℝ)) + s * (1 / (q : ℝ) + 4 / (2 : ℝ) ^ R) := by ring
  rw [e]
  linarith

end BstLean.Part141

open BstLean.Part141 in
#print axioms psiS_lip_x
open BstLean.Part141 in
#print axioms psiS_lip_s
open BstLean.Part141 in
#print axioms pQ_nonneg
open BstLean.Part141 in
#print axioms pQ_nonneg_real
open BstLean.Part141 in
#print axioms pQ_sum
open BstLean.Part141 in
#print axioms pQ_sum_real
open BstLean.Part141 in
#print axioms atom_couple
open BstLean.Part141 in
#print axioms atom_round
open BstLean.Part141 in
#print axioms atomSum141
