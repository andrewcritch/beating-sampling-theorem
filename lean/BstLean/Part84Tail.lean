import BstLean.Part84Defs

/-!
# Part 84, scale tail: `D_W = 𝒟 − n ≥ n²`, and `P(|λ₀² − 1| > 1/n) ≤ 33/n`

No `sorry`, no `native_decide`, no `axiom`.
-/

namespace BstLean.Part84

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD rhoD)
open BstLean.Part53 (radF53)
open BstLean.Part78 (Good good_coord markov_gt)
open BstLean.Part81 (JJ WIdx)

/-- `D_W = 𝒟 − n`. -/
theorem DW_eq (n d : ℕ) : DW n d = DD n d - n := by
  have h : Fintype.card (CoefIdxD n d) = n + Fintype.card (WIdx n d) := by
    rw [← Fintype.card_congr (BstLean.Part81.Br.splitEquiv n d), Fintype.card_sum,
      Fintype.card_fin]
  unfold DW DD
  rw [h]; push_cast; ring

/-- `D_W ≥ n²` for `d ≥ 1`. -/
theorem DW_ge (n d : ℕ) (hd : 1 ≤ d) : (n : ℝ) ^ 2 ≤ DW n d := by
  rw [DW_eq, BstLean.Part36.DD_eq]
  have hc := Nat.choose_le_choose n (show n + 1 ≤ n + d by omega)
  rw [Nat.choose_symm_add (a := n) (b := 1), Nat.choose_one_right,
    Nat.choose_symm_add (a := n) (b := d)] at hc
  have hc' : (n : ℝ) + 1 ≤ ((n + d).choose d : ℝ) := by exact_mod_cast hc
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hc' hn0]

theorem card_WIdx_ge (n d : ℕ) (hd : 1 ≤ d) (hn : 32 ≤ n) : 1000 ≤ Fintype.card (WIdx n d) := by
  have h := DW_ge n d hd
  unfold DW at h
  have h' : n ^ 2 ≤ Fintype.card (WIdx n d) := by exact_mod_cast h
  nlinarith

/-- The chi-square second moment on a general index type. -/
theorem chi_sq_var (ι : Type) [Fintype ι] :
    ∫ Z : ι → ℝ, ((∑ i, Z i ^ 2) - (Fintype.card ι : ℝ)) ^ 2 ∂stdGauss ι =
      2 * (Fintype.card ι : ℝ) := by
  have hq : Good (stdGauss ι) (fun Z : ι → ℝ => ∑ i, Z i ^ 2) :=
    Good.sum _ fun α _ => (good_coord α).pow 2
  have h1 := BstLean.Part41.p1_gauss_norm_moment (ι := ι) 1
  have h2 := BstLean.Part41.p1_gauss_norm_moment (ι := ι) 2
  have e1 : ∀ Z : ι → ℝ, Real.sqrt (∑ i, Z i ^ 2) ^ (2 * 1) = ∑ i, Z i ^ 2 := fun Z => by
    rw [mul_one, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have e2 : ∀ Z : ι → ℝ, Real.sqrt (∑ i, Z i ^ 2) ^ (2 * 2) = (∑ i, Z i ^ 2) ^ 2 := fun Z => by
    rw [pow_mul, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [e1, e2] at h1 h2
  simp only [rhoD, Finset.prod_range_succ, Finset.prod_range_zero] at h1 h2
  have e3 : ∀ Z : ι → ℝ, ((∑ i, Z i ^ 2) - (Fintype.card ι : ℝ)) ^ 2 =
      (∑ i, Z i ^ 2) ^ 2 - 2 * (Fintype.card ι : ℝ) * (∑ i, Z i ^ 2)
        + (Fintype.card ι : ℝ) ^ 2 := fun Z => by ring
  simp only [e3]
  have hi2 : Integrable (fun Z : ι → ℝ => (∑ i, Z i ^ 2) ^ 2) (stdGauss ι) := (hq.pow 2).integrable
  have hi1 : Integrable (fun Z : ι → ℝ => 2 * (Fintype.card ι : ℝ) * ∑ i, Z i ^ 2) (stdGauss ι) :=
    hq.integrable.const_mul _
  rw [integral_add (f := fun Z : ι → ℝ => (∑ i, Z i ^ 2) ^ 2 -
      2 * (Fintype.card ι : ℝ) * ∑ i, Z i ^ 2) (g := fun _ => (Fintype.card ι : ℝ) ^ 2)
      (hi2.sub hi1) (integrable_const _),
    integral_sub (f := fun Z : ι → ℝ => (∑ i, Z i ^ 2) ^ 2)
      (g := fun Z : ι → ℝ => 2 * (Fintype.card ι : ℝ) * ∑ i, Z i ^ 2) hi2 hi1,
    integral_const_mul, h1, h2]
  simp
  ring

/-- Chebyshev for the squared radius. -/
theorem chi_tail (ι : Type) [Fintype ι] (hN : 0 < Fintype.card ι) :
    stdGauss ι {Z : ι → ℝ | (Fintype.card ι : ℝ) / 4 < |(∑ i, Z i ^ 2) - (Fintype.card ι : ℝ)|} ≤
      ENNReal.ofReal (32 / (Fintype.card ι : ℝ)) := by
  have hN' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  have hq : Good (stdGauss ι) (fun Z : ι → ℝ => ∑ i, Z i ^ 2) :=
    Good.sum _ fun α _ => (good_coord α).pow 2
  have hg : Good (stdGauss ι)
      (fun Z : ι → ℝ => ((∑ i, Z i ^ 2) - (Fintype.card ι : ℝ)) ^ 2) :=
    (hq.sub (Good.const _)).pow 2
  have hm := markov_gt (μ := stdGauss ι) (fun Z => sq_nonneg _) hg.integrable
    (t := ((Fintype.card ι : ℝ) / 4) ^ 2) (by positivity) (chi_sq_var ι).le
  have he : 2 * (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) / 4) ^ 2 =
      32 / (Fintype.card ι : ℝ) := by field_simp; ring
  rw [he] at hm
  refine le_trans (measure_mono ?_) hm
  intro Z hZ
  simp only [Set.mem_ofPred_eq] at hZ ⊢
  have := sq_lt_sq.mpr (by rwa [abs_of_pos (by positivity : (0 : ℝ) < (Fintype.card ι : ℝ) / 4)] :
    |(Fintype.card ι : ℝ) / 4| < |(∑ i, Z i ^ 2) - (Fintype.card ι : ℝ)|)
  exact this

/-- The pointwise bound on the good event. -/
theorem lam0_good (n d : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (u : Fin n → ℝ) (W : WIdx n d → ℝ)
    (ha : |(∑ i, u i ^ 2) - (n : ℝ)| ≤ (n : ℝ) / 4)
    (hb : |(∑ β, W β ^ 2) - DW n d| ≤ DW n d / 4) :
    |lam0 n d u (radF53 W) ^ 2 - 1| ≤ 1 / (n : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hDW := DW_ge n d hd
  have hDD : DD n d = DW n d + n := by rw [DW_eq]; ring
  set a := ∑ i, u i ^ 2 with ha_def
  set b := ∑ β, W β ^ 2 with hb_def
  set E := DW n d with hE
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun i _ => sq_nonneg _
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hEpos : 0 < E := by nlinarith
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have hab : 0 < a + b := by nlinarith
  have hρ : radF53 W ^ 2 = b := by
    unfold radF53; rw [Real.sq_sqrt hb0]
  have hl : lam0 n d u (radF53 W) ^ 2 = (E + n) * b / ((a + b) * E) := by
    unfold lam0
    rw [div_pow, mul_pow, mul_pow, hρ, Real.sq_sqrt (by rw [hDD]; positivity),
      Real.sq_sqrt hab.le, Real.sq_sqrt hEpos.le, hDD]
  have hx : lam0 n d u (radF53 W) ^ 2 - 1 = (n * (b - E) - E * (a - n)) / ((a + b) * E) := by
    rw [hl]; field_simp; ring
  rw [hx, abs_div, abs_of_pos (mul_pos hab hEpos), div_le_div_iff₀ (mul_pos hab hEpos)
    (by linarith)]
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hnum : |(n : ℝ) * (b - E) - E * (a - n)| ≤ n * E / 2 := by
    rw [abs_le]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hb1 hn0, mul_le_mul_of_nonneg_left ha2 hEpos.le]
    · nlinarith [mul_le_mul_of_nonneg_left hb2 hn0, mul_le_mul_of_nonneg_left ha1 hEpos.le]
  have h3 : (n : ℝ) * E / 2 * n ≤ 1 * ((a + b) * E) := by
    have : (n : ℝ) ^ 2 / 2 ≤ a + b := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hEpos.le]
  exact le_trans (mul_le_mul_of_nonneg_right hnum hn0) h3

/-- **Scale tail**: `P(|λ₀² − 1| > 1/n) ≤ 33/n`. -/
theorem tailIface (n d : ℕ) (hd : 1 ≤ d) (hn : 32 ≤ n) : TailIface n d 33 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hcard := card_WIdx_ge n d hd hn
  have hDW := DW_ge n d hd
  set A : Set (Fin n → ℝ) := {u | (n : ℝ) / 4 < |(∑ i, u i ^ 2) - (n : ℝ)|} with hA
  set B : Set (WIdx n d → ℝ) := {W | DW n d / 4 < |(∑ β, W β ^ 2) - DW n d|} with hB
  have hAm : MeasurableSet A :=
    measurableSet_lt measurable_const (by fun_prop)
  have hBm : MeasurableSet B :=
    measurableSet_lt measurable_const (by fun_prop)
  have hPA : stdGauss (Fin n) A ≤ ENNReal.ofReal (32 / (n : ℝ)) := by
    have := chi_tail (Fin n) (by simpa using (show 0 < n by omega))
    simpa [hA] using this
  have hPB : stdGauss (WIdx n d) B ≤ ENNReal.ofReal (32 / DW n d) :=
    chi_tail (WIdx n d) (by omega)
  have hpt : ∀ (u : Fin n → ℝ) (W' : WIdx n d → ℝ),
      Set.indicator {p : (Fin n → ℝ) × (WIdx n d → ℝ) |
        1 / (n : ℝ) < |lam0 n d p.1 (radF53 p.2) ^ 2 - 1|} (fun _ => (1 : ℝ≥0∞)) (u, W') ≤
      A.indicator (fun _ => (1 : ℝ≥0∞)) u + B.indicator (fun _ => (1 : ℝ≥0∞)) W' := by
    intro u W'
    by_cases hu : u ∈ A
    · rw [Set.indicator_of_mem hu]
      exact le_trans (Set.indicator_le_self' (fun _ _ => zero_le) _) le_self_add
    by_cases hW : W' ∈ B
    · rw [Set.indicator_of_mem hW]
      exact le_trans (Set.indicator_le_self' (fun _ _ => zero_le) _) le_add_self
    · have hg := lam0_good n d hd hn1 u W' (not_lt.mp hu) (not_lt.mp hW)
      rw [Set.indicator_of_notMem (by simpa using hg)]
      exact zero_le
  unfold TailIface
  calc ∫⁻ u : Fin n → ℝ, ∫⁻ W' : WIdx n d → ℝ,
          Set.indicator {p : (Fin n → ℝ) × (WIdx n d → ℝ) |
            1 / (n : ℝ) < |lam0 n d p.1 (radF53 p.2) ^ 2 - 1|} (fun _ => (1 : ℝ≥0∞)) (u, W')
          ∂stdGauss (WIdx n d) ∂stdGauss (Fin n)
      ≤ ∫⁻ u : Fin n → ℝ, ∫⁻ W' : WIdx n d → ℝ,
          (A.indicator (fun _ => (1 : ℝ≥0∞)) u + B.indicator (fun _ => (1 : ℝ≥0∞)) W')
          ∂stdGauss (WIdx n d) ∂stdGauss (Fin n) :=
        lintegral_mono fun u => lintegral_mono fun W' => hpt u W'
    _ = stdGauss (Fin n) A + stdGauss (WIdx n d) B := by
        have h1 : ∀ u : Fin n → ℝ, ∫⁻ W' : WIdx n d → ℝ,
            (A.indicator (fun _ => (1 : ℝ≥0∞)) u + B.indicator (fun _ => (1 : ℝ≥0∞)) W')
            ∂stdGauss (WIdx n d) =
            A.indicator (fun _ => (1 : ℝ≥0∞)) u + stdGauss (WIdx n d) B := by
          intro u
          rw [lintegral_add_left measurable_const, lintegral_indicator hBm]
          simp
        simp only [h1]
        rw [lintegral_add_right _ measurable_const, lintegral_indicator hAm]
        simp
    _ ≤ ENNReal.ofReal (32 / (n : ℝ)) + ENNReal.ofReal (32 / DW n d) := add_le_add hPA hPB
    _ = ENNReal.ofReal (32 / (n : ℝ) + 32 / DW n d) := by
        rw [ENNReal.ofReal_add (by positivity) (by
          have : (0 : ℝ) < DW n d := by nlinarith
          positivity)]
    _ ≤ ENNReal.ofReal (33 / (n : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        have hn0 : (0 : ℝ) < n := by linarith
        have hE : (0 : ℝ) < DW n d := by nlinarith
        have h1 : 32 / DW n d ≤ 1 / (n : ℝ) := by
          rw [div_le_div_iff₀ hE hn0]; nlinarith
        have h2 : (33 : ℝ) / n = 32 / n + 1 / n := by ring
        linarith

end BstLean.Part84
