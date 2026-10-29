import BstLean.Part86Defs
import BstLean.Part84Tail

/-!
# Part 86, scale tail and counting lemmas

`tail86`: `P(|λ₀² − 1| > 1/n) ≤ 100/n` for `2 ≤ d ≤ n`, `n ≥ 100`.
No `sorry`, no `native_decide`, no `axiom`.
-/

namespace BstLean.Part86

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD)
open BstLean.Part41 (Mono)
open BstLean.Part53 (radF53)
open BstLean.Part78 (Good good_coord markov_gt)

/-! ## Counting -/

theorem card_mono86 (n d : ℕ) : Fintype.card (Mono n d) = (n + d).choose d := by
  classical
  simp only [Mono, Fintype.card_sigma, Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range, Nat.sum_range_multichoose,
    ← Nat.choose_symm_add (a := d) (b := n)]
  simp [Nat.add_comm]

theorem card_JR (n d : ℕ) : Fintype.card (JR n d) = (n + d).choose d - (d + 1) := by
  rw [Fintype.card_fin, card_mono86]

theorem choose2_86 (n : ℕ) : 2 * (n + 2).choose 2 = (n + 2) * (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h : (n + 1 + 2).choose 2 = (n + 2).choose 1 + (n + 2).choose 2 :=
      Nat.choose_succ_succ' (n + 2) 1
    rw [h, Nat.choose_one_right, Nat.mul_add, ih]
    ring

theorem choose3_86 (n : ℕ) : 6 * (n + 3).choose 3 = (n + 3) * (n + 2) * (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h : (n + 1 + 3).choose 3 = (n + 3).choose 2 + (n + 3).choose 3 :=
      Nat.choose_succ_succ' (n + 3) 2
    have h2 := choose2_86 (n + 1)
    rw [h, Nat.mul_add, ih]
    have : 6 * (n + 3).choose 2 = 3 * ((n + 1 + 2) * (n + 1 + 1)) := by
      rw [← h2]; ring
    rw [this]; ring

/-- `C(n+d, d) ≥ C(n+j, j)` for `j ≤ d`. -/
theorem choose_mono86 (n d j : ℕ) (hj : j ≤ d) : (n + j).choose j ≤ (n + d).choose d := by
  have hc := Nat.choose_le_choose n (show n + j ≤ n + d by omega)
  rwa [Nat.choose_symm_add (a := n) (b := j), Nat.choose_symm_add (a := n) (b := d)] at hc

/-- `C(n+d, d) ≥ C(j+d, d)` for `j ≤ n`. -/
theorem choose_mono86' (n d j : ℕ) (hj : j ≤ n) : (j + d).choose d ≤ (n + d).choose d :=
  Nat.choose_le_choose d (by omega)

theorem card_mono_ge (n d : ℕ) (hn : 1 ≤ n) : d + 1 ≤ Fintype.card (Mono n d) := by
  rw [card_mono86]
  have h := choose_mono86' n d 1 hn
  rw [Nat.add_comm 1 d, Nat.choose_succ_self_right] at h
  exact h

theorem card_JR_pos (n d : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) : 0 < Fintype.card (JR n d) := by
  rw [card_JR]
  have h := choose_mono86' n d 2 hn
  have h1 : (2 + d).choose d = (d + 2).choose 2 := by
    rw [Nat.add_comm 2 d]; exact Nat.choose_symm_add (a := d) (b := 2)
  have h2 := choose2_86 d
  rw [h1] at h
  have : 2 * (d + 2) ≤ (d + 2) * (d + 1) := by nlinarith
  omega

/-- The main count: `card (JR n d) ≥ 2 n (d+1)`. -/
theorem card_JR_ge (n d : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (hn : 100 ≤ n) :
    2 * n * (d + 1) ≤ Fintype.card (JR n d) := by
  rw [card_JR]
  suffices h : (2 * n + 1) * (d + 1) ≤ (n + d).choose d by
    have : (2 * n + 1) * (d + 1) = 2 * n * (d + 1) + (d + 1) := by ring
    omega
  by_cases h2 : d = 2
  · subst h2
    have := choose2_86 n
    nlinarith
  · have h3 := choose_mono86 n d 3 (by omega)
    have h6 := choose3_86 n
    have hA : 6 * ((2 * n + 1) * (d + 1)) ≤ (n + 3) * (n + 2) * (n + 1) := by
      have h1 : 6 * ((2 * n + 1) * (d + 1)) ≤ 6 * ((2 * n + 1) * (n + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      have h2' : 6 * (2 * n + 1) ≤ (n + 3) * (n + 2) := by nlinarith
      calc 6 * ((2 * n + 1) * (d + 1)) ≤ 6 * ((2 * n + 1) * (n + 1)) := h1
        _ = 6 * (2 * n + 1) * (n + 1) := by ring
        _ ≤ (n + 3) * (n + 2) * (n + 1) := Nat.mul_le_mul_right _ h2'
    omega

theorem card_W_ge (n d : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (hn : 100 ≤ n) :
    1000 ≤ Fintype.card (JR n d × Fin n) := by
  rw [Fintype.card_prod, Fintype.card_fin n]
  have h := card_JR_ge n d hd hdn hn
  have h1 : 2 * n * 3 ≤ Fintype.card (JR n d) :=
    le_trans (Nat.mul_le_mul_left _ (by omega)) h
  nlinarith

theorem DWr_eq (n d : ℕ) (hn : 1 ≤ n) : DWr n (JR n d) = DD n d - n * ((d : ℝ) + 1) := by
  have h := card_mono_ge n d hn
  unfold DWr DD
  rw [BstLean.Part36.card_coefIdxD, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    ← card_mono86]
  push_cast [Nat.cast_sub h]
  ring

theorem DD_ge_sq (n d : ℕ) (hd : 1 ≤ d) : (n : ℝ) ^ 2 ≤ DD n d := by
  rw [BstLean.Part36.DD_eq]
  have hc := choose_mono86 n d 1 hd
  rw [Nat.choose_one_right] at hc
  have hc' : (n : ℝ) + 1 ≤ ((n + d).choose d : ℝ) := by exact_mod_cast hc
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hc' hn0]

/-! ## Chebyshev -/

/-- Chebyshev for the squared radius, general threshold. -/
theorem chi_tail_gen (ι : Type) [Fintype ι] (c : ℝ) (hc : 0 < c) :
    stdGauss ι {Z : ι → ℝ | c < |(∑ i, Z i ^ 2) - (Fintype.card ι : ℝ)|} ≤
      ENNReal.ofReal (2 * (Fintype.card ι : ℝ) / c ^ 2) := by
  have hq : Good (stdGauss ι) (fun Z : ι → ℝ => ∑ i, Z i ^ 2) :=
    Good.sum _ fun α _ => (good_coord α).pow 2
  have hg : Good (stdGauss ι)
      (fun Z : ι → ℝ => ((∑ i, Z i ^ 2) - (Fintype.card ι : ℝ)) ^ 2) :=
    (hq.sub (Good.const _)).pow 2
  have hm := markov_gt (μ := stdGauss ι) (fun Z => sq_nonneg _) hg.integrable
    (t := c ^ 2) (by positivity) (BstLean.Part84.chi_sq_var ι).le
  refine le_trans (measure_mono ?_) hm
  intro Z hZ
  simp only [Set.mem_ofPred_eq] at hZ ⊢
  exact sq_lt_sq.mpr (by rwa [abs_of_pos hc])

/-! ## The pointwise bound -/

theorem lam0_good86 (n : ℕ) (hn : 1 ≤ n) (N E Jc a b : ℝ) (hE : E = n * Jc) (hN2 : N ≤ 2 * Jc)
    (hN0 : 0 ≤ N) (hJ : 0 < Jc) (ha0 : 0 ≤ a)
    (ha : |a - N| ≤ Jc / 4) (hb : |b - E| ≤ E / 4) :
    |(E + N) * b / ((a + b) * E) - 1| ≤ 1 / (n : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hEpos : 0 < E := by rw [hE]; positivity
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have hab : 0 < a + b := by linarith
  have hx : (E + N) * b / ((a + b) * E) - 1 = (N * (b - E) - E * (a - N)) / ((a + b) * E) := by
    field_simp; ring
  rw [hx, abs_div, abs_of_pos (mul_pos hab hEpos), div_le_div_iff₀ (mul_pos hab hEpos) hn0]
  have hnum : |N * (b - E) - E * (a - N)| ≤ N * (E / 4) + E * (Jc / 4) := by
    rw [abs_le]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hb1 hN0, mul_le_mul_of_nonneg_left ha2 hEpos.le]
    · nlinarith [mul_le_mul_of_nonneg_left hb2 hN0, mul_le_mul_of_nonneg_left ha1 hEpos.le]
  have h3 : (N * (E / 4) + E * (Jc / 4)) * n ≤ 1 * ((a + b) * E) := by
    have h4 : (N / 4 + Jc / 4) * n ≤ a + b := by
      have : (N / 4 + Jc / 4) * n ≤ 3 / 4 * E := by rw [hE]; nlinarith
      linarith
    nlinarith [mul_le_mul_of_nonneg_right h4 hEpos.le]
  exact le_trans (mul_le_mul_of_nonneg_right hnum hn0.le) h3

/-! ## The tail -/

/-- **Scale tail**: `P(|λ₀² − 1| > 1/n) ≤ 100/n`. -/
theorem tail86 (n d : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (hn : 100 ≤ n) : TailIface86 n d 100 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set Jc : ℝ := (Fintype.card (JR n d) : ℝ) with hJc
  set N : ℝ := (Fintype.card (Fin (d + 1) × Fin n) : ℝ) with hNdef
  set E : ℝ := DWr n (JR n d) with hEdef
  have hNeq : N = n * ((d : ℝ) + 1) := by
    simp only [hNdef, Fintype.card_prod, Fintype.card_fin]; push_cast; ring
  have hEeq : E = n * Jc := by
    simp only [hEdef, DWr, hJc, Fintype.card_prod, Fintype.card_fin]; push_cast; ring
  have hJge : 2 * N ≤ Jc := by
    have h := card_JR_ge n d hd hdn hn
    have h'' : ((2 * n * (d + 1) : ℕ) : ℝ) ≤ (Fintype.card (JR n d) : ℝ) := Nat.cast_le.mpr h
    have h' : (2 : ℝ) * n * ((d : ℝ) + 1) ≤ Jc := by push_cast at h''; exact h''
    rw [hNeq]; linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hN0 : 0 < N := by rw [hNeq]; positivity
  have hNn : (n : ℝ) ≤ N := by rw [hNeq]; nlinarith
  have hJ0 : 0 < Jc := by linarith
  have hE0 : 0 < E := by rw [hEeq]; positivity
  have hDD : DD n d = E + N := by
    rw [hEdef, DWr_eq n d hn1, hNeq]; ring
  set A : Set (Fin (d + 1) × Fin n → ℝ) := {U | Jc / 4 < |(∑ a, U a ^ 2) - N|} with hA
  set B : Set (JR n d × Fin n → ℝ) := {W | E / 4 < |(∑ β, W β ^ 2) - E|} with hB
  have hAm : MeasurableSet A := measurableSet_lt measurable_const (by fun_prop)
  have hBm : MeasurableSet B := measurableSet_lt measurable_const (by fun_prop)
  have hPA : stdGauss (Fin (d + 1) × Fin n) A ≤ ENNReal.ofReal (2 * N / (Jc / 4) ^ 2) :=
    chi_tail_gen (Fin (d + 1) × Fin n) (Jc / 4) (by positivity)
  have hPB : stdGauss (JR n d × Fin n) B ≤ ENNReal.ofReal (2 * E / (E / 4) ^ 2) :=
    chi_tail_gen (JR n d × Fin n) (E / 4) (by positivity)
  have hpt : ∀ (U : Fin (d + 1) × Fin n → ℝ) (W' : JR n d × Fin n → ℝ),
      Set.indicator {p : (Fin (d + 1) × Fin n → ℝ) × (JR n d × Fin n → ℝ) |
        1 / (n : ℝ) < |lam0 (DD n d) (DWr n (JR n d)) p.1 (radF53 p.2) ^ 2 - 1|}
        (fun _ => (1 : ℝ≥0∞)) (U, W') ≤
      A.indicator (fun _ => (1 : ℝ≥0∞)) U + B.indicator (fun _ => (1 : ℝ≥0∞)) W' := by
    intro U W'
    by_cases hu : U ∈ A
    · rw [Set.indicator_of_mem hu]
      exact le_trans (Set.indicator_le_self' (fun _ _ => zero_le) _) le_self_add
    by_cases hW : W' ∈ B
    · rw [Set.indicator_of_mem hW]
      exact le_trans (Set.indicator_le_self' (fun _ _ => zero_le) _) le_add_self
    · have ha : |(∑ a, U a ^ 2) - N| ≤ Jc / 4 := not_lt.mp hu
      have hb : |(∑ β, W' β ^ 2) - E| ≤ E / 4 := not_lt.mp hW
      have ha0 : 0 ≤ ∑ a, U a ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hb0 : 0 ≤ ∑ β, W' β ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hab : 0 < (∑ a, U a ^ 2) + ∑ β, W' β ^ 2 := by
        have := (abs_le.mp hb).1; linarith
      have hρ : radF53 W' ^ 2 = ∑ β, W' β ^ 2 := by
        unfold radF53; rw [Real.sq_sqrt hb0]
      have hl : lam0 (DD n d) (DWr n (JR n d)) U (radF53 W') ^ 2 =
          (E + N) * (∑ β, W' β ^ 2) / (((∑ a, U a ^ 2) + ∑ β, W' β ^ 2) * E) := by
        unfold lam0
        rw [div_pow, mul_pow, mul_pow, hρ, Real.sq_sqrt (by rw [hDD]; positivity),
          Real.sq_sqrt hab.le, Real.sq_sqrt hE0.le, hDD]
      have hg := lam0_good86 n hn1 N E Jc _ _ hEeq (by linarith) hN0.le hJ0 ha0 ha hb
      rw [← hl] at hg
      rw [Set.indicator_of_notMem (by simpa using hg)]
      exact zero_le
  unfold TailIface86
  calc ∫⁻ U : Fin (d + 1) × Fin n → ℝ, ∫⁻ W' : JR n d × Fin n → ℝ,
          Set.indicator {p : (Fin (d + 1) × Fin n → ℝ) × (JR n d × Fin n → ℝ) |
            1 / (n : ℝ) < |lam0 (DD n d) (DWr n (JR n d)) p.1 (radF53 p.2) ^ 2 - 1|}
            (fun _ => (1 : ℝ≥0∞)) (U, W')
          ∂stdGauss (JR n d × Fin n) ∂stdGauss (Fin (d + 1) × Fin n)
      ≤ ∫⁻ U : Fin (d + 1) × Fin n → ℝ, ∫⁻ W' : JR n d × Fin n → ℝ,
          (A.indicator (fun _ => (1 : ℝ≥0∞)) U + B.indicator (fun _ => (1 : ℝ≥0∞)) W')
          ∂stdGauss (JR n d × Fin n) ∂stdGauss (Fin (d + 1) × Fin n) :=
        lintegral_mono fun U => lintegral_mono fun W' => hpt U W'
    _ = stdGauss (Fin (d + 1) × Fin n) A + stdGauss (JR n d × Fin n) B := by
        have h1 : ∀ U : Fin (d + 1) × Fin n → ℝ, ∫⁻ W' : JR n d × Fin n → ℝ,
            (A.indicator (fun _ => (1 : ℝ≥0∞)) U + B.indicator (fun _ => (1 : ℝ≥0∞)) W')
            ∂stdGauss (JR n d × Fin n) =
            A.indicator (fun _ => (1 : ℝ≥0∞)) U + stdGauss (JR n d × Fin n) B := by
          intro U
          rw [lintegral_add_left measurable_const, lintegral_indicator hBm]
          simp
        simp only [h1]
        rw [lintegral_add_right _ measurable_const, lintegral_indicator hAm]
        simp
    _ ≤ ENNReal.ofReal (2 * N / (Jc / 4) ^ 2) + ENNReal.ofReal (2 * E / (E / 4) ^ 2) :=
        add_le_add hPA hPB
    _ = ENNReal.ofReal (2 * N / (Jc / 4) ^ 2 + 2 * E / (E / 4) ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (100 / (n : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : 2 * N / (Jc / 4) ^ 2 ≤ 8 / (n : ℝ) := by
          rw [div_le_div_iff₀ (by positivity) hn0]
          have hJJ : 2 * N * (2 * N) ≤ Jc * Jc := mul_le_mul hJge hJge (by positivity) hJ0.le
          have : N * n ≤ N * N := mul_le_mul_of_nonneg_left hNn hN0.le
          nlinarith
        have h2 : 2 * E / (E / 4) ^ 2 ≤ 32 / (n : ℝ) := by
          rw [div_le_div_iff₀ (by positivity) hn0]
          have hEn : (n : ℝ) ≤ E := by rw [hEeq]; nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hEn hE0.le]
        have h3 : (100 : ℝ) / n = 8 / n + 32 / n + 60 / n := by ring
        have : (0 : ℝ) ≤ 60 / n := by positivity
        linarith

end BstLean.Part86

#print axioms BstLean.Part86.tail86
#print axioms BstLean.Part86.card_W_ge
#print axioms BstLean.Part86.DWr_eq
#print axioms BstLean.Part86.DD_ge_sq
#print axioms BstLean.Part86.card_JR_pos
