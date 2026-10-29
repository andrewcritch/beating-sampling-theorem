import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Part 152 (file `BM`): the Prékopa–Leindler inequality on the real line

Role: `delegations/statements/p152-spec.md`. This file has no Gaussian object. It proves, for the
Lebesgue measure on `ℝ` and a weight `0 < s < 1`:

* `bm_add`: the Brunn–Minkowski inequality on the line: for nonempty measurable `A`, `B` and a set
  `C` that contains `A + B`: `|A| + |B| ≤ |C|`.
* `bm_convex`: the same with weights: `s·|A| + (1 − s)·|B| ≤ |C|` if `sA + (1 − s)B ⊆ C`.
* **`pl_one`**: the Prékopa–Leindler inequality: for measurable `u, v : ℝ → [0, ∞]` and a
  measurable `h : ℝ → [0, ∞)` with `u(x)^s · v(y)^{1−s} ≤ h(s·x + (1 − s)·y)` for all `x`, `y`:
  `(∫u)^s · (∫v)^{1−s} ≤ ∫h`.

The proof is the classical one: the level sets, the layer-cake formula, and the weighted inequality
of the arithmetic and the geometric mean.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part152

open MeasureTheory Set
open scoped ENNReal NNReal

/-- Brunn–Minkowski on the line, `A` bounded above and `B` bounded below. -/
lemma bm_add_bdd {A B C : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAn : A.Nonempty) (hBn : B.Nonempty) (hAb : BddAbove A) (hBb : BddBelow B)
    (h : ∀ a ∈ A, ∀ b ∈ B, a + b ∈ C) : volume A + volume B ≤ volume C := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : (0 : ℝ) < (ε : ℝ) / 2 := by
    have : (0 : ℝ) < ε := by exact_mod_cast hε
    positivity
  obtain ⟨a, haA, ha⟩ := exists_lt_of_lt_csSup hAn (sub_lt_self (sSup A) hε2)
  obtain ⟨b, hbB, hb⟩ := exists_lt_of_csInf_lt hBn (lt_add_of_pos_right (sInf B) hε2)
  have m1 : MeasurableSet ((fun z : ℝ => z + (-b)) ⁻¹' A) := (measurable_id.add_const _) hA
  have m2 : MeasurableSet ((fun z : ℝ => z + (-a)) ⁻¹' B ∩ Ioi (sSup A + b)) :=
    ((measurable_id.add_const _) hB).inter measurableSet_Ioi
  have v1 : volume ((fun z : ℝ => z + (-b)) ⁻¹' A) = volume A :=
    measure_preimage_add_right volume (-b) A
  have v2 : volume B ≤ volume ((fun z : ℝ => z + (-a)) ⁻¹' B ∩ Ioi (sSup A + b)) + ε := by
    have e : volume ((fun z : ℝ => z + (-a)) ⁻¹' B) = volume B :=
      measure_preimage_add_right volume (-a) B
    have sub : (fun z : ℝ => z + (-a)) ⁻¹' B ⊆
        ((fun z : ℝ => z + (-a)) ⁻¹' B ∩ Ioi (sSup A + b)) ∪ Icc (a + sInf B) (sSup A + b) := by
      intro z hz
      by_cases hzz : sSup A + b < z
      · exact Or.inl ⟨hz, hzz⟩
      · refine Or.inr ⟨?_, not_lt.mp hzz⟩
        have : sInf B ≤ z + -a := csInf_le hBb hz
        linarith
    calc volume B = volume ((fun z : ℝ => z + (-a)) ⁻¹' B) := e.symm
      _ ≤ volume (((fun z : ℝ => z + (-a)) ⁻¹' B ∩ Ioi (sSup A + b)) ∪
            Icc (a + sInf B) (sSup A + b)) := measure_mono sub
      _ ≤ volume ((fun z : ℝ => z + (-a)) ⁻¹' B ∩ Ioi (sSup A + b)) +
            volume (Icc (a + sInf B) (sSup A + b)) := measure_union_le _ _
      _ ≤ volume ((fun z : ℝ => z + (-a)) ⁻¹' B ∩ Ioi (sSup A + b)) + ε := by
          gcongr
          rw [Real.volume_Icc]
          calc ENNReal.ofReal (sSup A + b - (a + sInf B)) ≤ ENNReal.ofReal (ε : ℝ) :=
                ENNReal.ofReal_le_ofReal (by linarith)
            _ = ε := ENNReal.ofReal_coe_nnreal
  have d : Disjoint ((fun z : ℝ => z + (-b)) ⁻¹' A)
      ((fun z : ℝ => z + (-a)) ⁻¹' B ∩ Ioi (sSup A + b)) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have h1 : z + -b ≤ sSup A := le_csSup hAb hz1
    have h2 : sSup A + b < z := hz2.2
    linarith
  have sub : ((fun z : ℝ => z + (-b)) ⁻¹' A) ∪
      ((fun z : ℝ => z + (-a)) ⁻¹' B ∩ Ioi (sSup A + b)) ⊆ C := by
    rintro z (hz | hz)
    · have := h _ hz b hbB
      have e : z + -b + b = z := by ring
      rwa [e] at this
    · have := h a haA _ hz.1
      have e : a + (z + -a) = z := by ring
      rwa [e] at this
  calc volume A + volume B
      ≤ volume ((fun z : ℝ => z + (-b)) ⁻¹' A) +
          (volume ((fun z : ℝ => z + (-a)) ⁻¹' B ∩ Ioi (sSup A + b)) + ε) := by
        rw [v1]; gcongr
    _ = volume (((fun z : ℝ => z + (-b)) ⁻¹' A) ∪
          ((fun z : ℝ => z + (-a)) ⁻¹' B ∩ Ioi (sSup A + b))) + ε := by
        rw [measure_union d m2, add_assoc]
    _ ≤ volume C + ε := by gcongr

/-- **Brunn–Minkowski on the line.** -/
lemma bm_add {A B C : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (h : ∀ a ∈ A, ∀ b ∈ B, a + b ∈ C) : volume A + volume B ≤ volume C := by
  obtain ⟨a0, ha0⟩ := hAn
  obtain ⟨b0, hb0⟩ := hBn
  have trunc : ∀ (D : Set ℝ) (d0 : ℝ),
      Monotone (fun n : ℕ => D ∩ Icc (d0 - n) (d0 + n)) ∧
      volume D = ⨆ n : ℕ, volume (D ∩ Icc (d0 - n) (d0 + n)) := by
    intro D d0
    have mono : Monotone (fun n : ℕ => D ∩ Icc (d0 - n) (d0 + n)) := by
      intro m n hmn x hx
      have hc : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
      exact ⟨hx.1, by linarith [hx.2.1], by linarith [hx.2.2]⟩
    refine ⟨mono, ?_⟩
    rw [← mono.measure_iUnion]
    congr 1
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_Icc]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge |x - d0|
      have := abs_le.mp hn
      exact ⟨n, hx, by linarith [this.1], by linarith [this.2]⟩
    · rintro ⟨n, hx, -⟩
      exact hx
  obtain ⟨monoA, vA⟩ := trunc A a0
  obtain ⟨monoB, vB⟩ := trunc B b0
  rw [vA, vB, ENNReal.iSup_add_iSup_of_monotone (fun m n hmn => measure_mono (monoA hmn))
    (fun m n hmn => measure_mono (monoB hmn))]
  refine iSup_le fun n => ?_
  exact bm_add_bdd (hA.inter measurableSet_Icc) (hB.inter measurableSet_Icc)
    ⟨a0, ha0, by simp⟩ ⟨b0, hb0, by simp⟩ ⟨a0 + n, fun x hx => hx.2.2⟩ ⟨b0 - n, fun x hx => hx.2.1⟩
    (fun a ha b hb => h a ha.1 b hb.1)

/-- **Brunn–Minkowski on the line, with weights.** -/
lemma bm_convex {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {A B C : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (h : ∀ a ∈ A, ∀ b ∈ B, s * a + (1 - s) * b ∈ C) :
    ENNReal.ofReal s * volume A + ENNReal.ofReal (1 - s) * volume B ≤ volume C := by
  have h1 : 0 < 1 - s := by linarith
  have e1 := Real.volume_preimage_mul_left (inv_ne_zero hs0.ne') A
  have e2 := Real.volume_preimage_mul_left (inv_ne_zero h1.ne') B
  rw [inv_inv, abs_of_pos hs0] at e1
  rw [inv_inv, abs_of_pos h1] at e2
  rw [← e1, ← e2]
  refine bm_add (measurable_const_mul _ hA) (measurable_const_mul _ hB) ?_ ?_ ?_
  · obtain ⟨a, ha⟩ := hAn
    refine ⟨s * a, ?_⟩
    simp only [mem_preimage]
    rwa [inv_mul_cancel_left₀ hs0.ne']
  · obtain ⟨b, hb⟩ := hBn
    refine ⟨(1 - s) * b, ?_⟩
    simp only [mem_preimage]
    rwa [inv_mul_cancel_left₀ h1.ne']
  · intro z hz w hw
    have := h _ hz _ hw
    rwa [mul_inv_cancel_left₀ hs0.ne', mul_inv_cancel_left₀ h1.ne'] at this

/-- The weighted inequality of the arithmetic and the geometric mean in `[0, ∞]`. -/
lemma enn_amgm {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (P Q : ℝ≥0∞) :
    P ^ s * Q ^ (1 - s) ≤ ENNReal.ofReal s * P + ENNReal.ofReal (1 - s) * Q := by
  have h1 : 0 < 1 - s := by linarith
  by_cases hP : P = ⊤
  · rw [hP, ENNReal.mul_top (by simpa using hs0)]
    simp
  by_cases hQ : Q = ⊤
  · rw [hQ, ENNReal.mul_top (by simpa using h1)]
    simp
  have h := Real.geom_mean_le_arith_mean2_weighted hs0.le h1.le (ENNReal.toReal_nonneg (a := P))
    (ENNReal.toReal_nonneg (a := Q)) (by ring)
  have eP : P = ENNReal.ofReal P.toReal := (ENNReal.ofReal_toReal hP).symm
  have eQ : Q = ENNReal.ofReal Q.toReal := (ENNReal.ofReal_toReal hQ).symm
  rw [eP, eQ, ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs0.le,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg h1.le,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hs0.le,
    ← ENNReal.ofReal_mul h1.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

/-- Prékopa–Leindler on the line, for functions with supremum `1`. -/
lemma pl_norm {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {u v h : ℝ → ℝ}
    (hu : Measurable u) (hv : Measurable v) (hh : Measurable h)
    (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x) (hh0 : ∀ x, 0 ≤ h x)
    (hu1 : ∀ x, u x ≤ 1) (hv1 : ∀ x, v x ≤ 1)
    (hus : ∀ t < 1, ∃ x, t < u x) (hvs : ∀ t < 1, ∃ x, t < v x)
    (H : ∀ x y t, 0 < t → t < u x → t < v y → t < h (s * x + (1 - s) * y)) :
    ENNReal.ofReal s * (∫⁻ x, ENNReal.ofReal (u x)) +
      ENNReal.ofReal (1 - s) * (∫⁻ x, ENNReal.ofReal (v x)) ≤ ∫⁻ x, ENNReal.ofReal (h x) := by
  have Eu := lintegral_eq_lintegral_meas_lt (volume : Measure ℝ) (f := u) (ae_of_all _ hu0)
    hu.aemeasurable
  have Ev := lintegral_eq_lintegral_meas_lt (volume : Measure ℝ) (f := v) (ae_of_all _ hv0)
    hv.aemeasurable
  have Eh := lintegral_eq_lintegral_meas_lt (volume : Measure ℝ) (f := h) (ae_of_all _ hh0)
    hh.aemeasurable
  rw [Eu, Ev, Eh]
  have mu : Measurable fun t => volume {a | t < u a} :=
    Antitone.measurable fun t t' htt => measure_mono fun a ha => lt_of_le_of_lt htt ha
  have mv : Measurable fun t => volume {a | t < v a} :=
    Antitone.measurable fun t t' htt => measure_mono fun a ha => lt_of_le_of_lt htt ha
  rw [← lintegral_const_mul _ mu, ← lintegral_const_mul _ mv,
    ← lintegral_add_left (mu.const_mul _)]
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  by_cases ht1 : t < 1
  · exact bm_convex hs0 hs1 (measurableSet_lt measurable_const hu)
      (measurableSet_lt measurable_const hv) (hus t ht1) (hvs t ht1)
      (fun a ha b hb => H a b t ht ha hb)
  · have e1 : {a | t < u a} = ∅ := by
      ext a
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      linarith [hu1 a]
    have e2 : {a | t < v a} = ∅ := by
      ext a
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      linarith [hv1 a]
    simp [e1, e2]

/-- Prékopa–Leindler on the line, for bounded real functions. -/
lemma pl_bdd {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {u v h : ℝ → ℝ}
    (hu : Measurable u) (hv : Measurable v) (hh : Measurable h)
    (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x) (hh0 : ∀ x, 0 ≤ h x)
    {M : ℝ} (huM : ∀ x, u x ≤ M) (hvM : ∀ x, v x ≤ M)
    (H : ∀ x y, u x ^ s * v y ^ (1 - s) ≤ h (s * x + (1 - s) * y)) :
    (∫⁻ x, ENNReal.ofReal (u x)) ^ s * (∫⁻ x, ENNReal.ofReal (v x)) ^ (1 - s) ≤
      ∫⁻ x, ENNReal.ofReal (h x) := by
  have h1 : 0 < 1 - s := by linarith
  have bddu : BddAbove (range u) := ⟨M, by rintro _ ⟨x, rfl⟩; exact huM x⟩
  have bddv : BddAbove (range v) := ⟨M, by rintro _ ⟨x, rfl⟩; exact hvM x⟩
  have hua : ∀ x, u x ≤ ⨆ x, u x := le_ciSup bddu
  have hvb : ∀ x, v x ≤ ⨆ x, v x := le_ciSup bddv
  by_cases ha : (⨆ x, u x) ≤ 0
  · have : ∀ x, ENNReal.ofReal (u x) = 0 := fun x =>
      ENNReal.ofReal_eq_zero.mpr ((hua x).trans ha)
    simp [this, ENNReal.zero_rpow_of_pos hs0]
  by_cases hb : (⨆ x, v x) ≤ 0
  · have : ∀ x, ENNReal.ofReal (v x) = 0 := fun x =>
      ENNReal.ofReal_eq_zero.mpr ((hvb x).trans hb)
    simp [this, ENNReal.zero_rpow_of_pos h1]
  push Not at ha hb
  set a : ℝ := ⨆ x, u x with haa
  set b : ℝ := ⨆ x, v x with hbb
  set c : ℝ := a ^ s * b ^ (1 - s) with hc
  have hc0 : 0 < c := mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)
  have R := pl_norm hs0 hs1 (u := fun x => u x / a) (v := fun x => v x / b)
    (h := fun x => h x / c) (hu.div_const _) (hv.div_const _) (hh.div_const _)
    (fun x => div_nonneg (hu0 x) ha.le) (fun x => div_nonneg (hv0 x) hb.le)
    (fun x => div_nonneg (hh0 x) hc0.le)
    (fun x => (div_le_one ha).mpr (hua x)) (fun x => (div_le_one hb).mpr (hvb x))
    (fun t ht => by
      have : t * a < a := by nlinarith
      obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup this
      exact ⟨x, (lt_div_iff₀ ha).mpr hx⟩)
    (fun t ht => by
      have : t * b < b := by nlinarith
      obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup this
      exact ⟨x, (lt_div_iff₀ hb).mpr hx⟩)
    (fun x y t ht htu htv => by
      rw [lt_div_iff₀ ha] at htu
      rw [lt_div_iff₀ hb] at htv
      rw [lt_div_iff₀ hc0]
      have ta : 0 ≤ t * a := by positivity
      have tb : 0 ≤ t * b := by positivity
      have l1 : (t * a) ^ s < u x ^ s := Real.rpow_lt_rpow ta htu hs0
      have l2 : (t * b) ^ (1 - s) < v y ^ (1 - s) := Real.rpow_lt_rpow tb htv h1
      have l3 : (t * a) ^ s * (t * b) ^ (1 - s) < u x ^ s * v y ^ (1 - s) :=
        mul_lt_mul'' l1 l2 (Real.rpow_nonneg ta _) (Real.rpow_nonneg tb _)
      have e : (t * a) ^ s * (t * b) ^ (1 - s) = t * c := by
        rw [Real.mul_rpow ht.le ha.le, Real.mul_rpow ht.le hb.le, hc]
        have : t ^ s * t ^ (1 - s) = t := by
          rw [← Real.rpow_add ht]
          simp
        calc t ^ s * a ^ s * (t ^ (1 - s) * b ^ (1 - s))
            = (t ^ s * t ^ (1 - s)) * (a ^ s * b ^ (1 - s)) := by ring
          _ = t * (a ^ s * b ^ (1 - s)) := by rw [this]
      rw [← e]
      exact l3.trans_le (H x y))
  have eu : ∀ x, ENNReal.ofReal (u x / a) = ENNReal.ofReal a⁻¹ * ENNReal.ofReal (u x) := fun x => by
    rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)]
  have ev : ∀ x, ENNReal.ofReal (v x / b) = ENNReal.ofReal b⁻¹ * ENNReal.ofReal (v x) := fun x => by
    rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr hb.le)]
  have eh : ∀ x, ENNReal.ofReal (h x / c) = ENNReal.ofReal c⁻¹ * ENNReal.ofReal (h x) := fun x => by
    rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr hc0.le)]
  simp only [eu, ev, eh] at R
  rw [lintegral_const_mul _ hu.ennreal_ofReal, lintegral_const_mul _ hv.ennreal_ofReal,
    lintegral_const_mul _ hh.ennreal_ofReal] at R
  have G := (enn_amgm hs0 hs1 (ENNReal.ofReal a⁻¹ * ∫⁻ x, ENNReal.ofReal (u x))
    (ENNReal.ofReal b⁻¹ * ∫⁻ x, ENNReal.ofReal (v x))).trans R
  rw [ENNReal.mul_rpow_of_nonneg _ _ hs0.le, ENNReal.mul_rpow_of_nonneg _ _ h1.le,
    ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr ha.le) hs0.le,
    ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hb.le) h1.le] at G
  have ec : ENNReal.ofReal c⁻¹ = ENNReal.ofReal (a⁻¹ ^ s) * ENNReal.ofReal (b⁻¹ ^ (1 - s)) := by
    rw [← ENNReal.ofReal_mul (by positivity), hc, mul_inv, Real.inv_rpow ha.le,
      Real.inv_rpow hb.le]
  have G' : ENNReal.ofReal c⁻¹ * ((∫⁻ x, ENNReal.ofReal (u x)) ^ s *
      (∫⁻ x, ENNReal.ofReal (v x)) ^ (1 - s)) ≤ ENNReal.ofReal c⁻¹ * ∫⁻ x, ENNReal.ofReal (h x) := by
    refine le_trans (le_of_eq ?_) G
    rw [ec]
    ring
  exact (ENNReal.mul_le_mul_iff_right (by simpa using hc0) ENNReal.ofReal_ne_top).mp G'

/-- **The Prékopa–Leindler inequality on the line.** -/
theorem pl_one {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {u v : ℝ → ℝ≥0∞} {h : ℝ → ℝ}
    (hu : Measurable u) (hv : Measurable v) (hh : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (H : ∀ x y, u x ^ s * v y ^ (1 - s) ≤ ENNReal.ofReal (h (s * x + (1 - s) * y))) :
    (∫⁻ x, u x) ^ s * (∫⁻ x, v x) ^ (1 - s) ≤ ∫⁻ x, ENNReal.ofReal (h x) := by
  have h1 : 0 < 1 - s := by linarith
  have tr : ∀ (w : ℝ → ℝ≥0∞), Measurable w →
      ∫⁻ x, w x = ⨆ n : ℕ, ∫⁻ x, min (w x) (n : ℝ≥0∞) := by
    intro w hw
    rw [← lintegral_iSup (fun n => hw.min measurable_const)
      (fun m n hmn x => min_le_min le_rfl (by exact_mod_cast hmn))]
    refine lintegral_congr fun x => ?_
    show w x = ⨆ n : ℕ, w x ⊓ (n : ℝ≥0∞)
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have key : ∀ m n : ℕ, (∫⁻ x, min (u x) (m : ℝ≥0∞)) ^ s * (∫⁻ x, min (v x) (n : ℝ≥0∞)) ^ (1 - s) ≤
      ∫⁻ x, ENNReal.ofReal (h x) := by
    intro m n
    set N : ℕ := max m n with hN
    have fin : ∀ (w : ℝ≥0∞), min w (N : ℝ≥0∞) ≠ ⊤ := fun w =>
      ne_of_lt (min_lt_iff.mpr (Or.inr (ENNReal.natCast_lt_top N)))
    have B := pl_bdd hs0 hs1 (u := fun x => (min (u x) (N : ℝ≥0∞)).toReal)
      (v := fun x => (min (v x) (N : ℝ≥0∞)).toReal) (h := h) (M := N)
      (ENNReal.measurable_toReal.comp (hu.min measurable_const))
      (ENNReal.measurable_toReal.comp (hv.min measurable_const)) hh
      (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg) hh0
      (fun x => by
        have := ENNReal.toReal_mono (ENNReal.natCast_ne_top N) (min_le_right (u x) (N : ℝ≥0∞))
        rwa [ENNReal.toReal_natCast] at this)
      (fun x => by
        have := ENNReal.toReal_mono (ENNReal.natCast_ne_top N) (min_le_right (v x) (N : ℝ≥0∞))
        rwa [ENNReal.toReal_natCast] at this)
      (fun x y => by
        rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
        have l : min (u x) (N : ℝ≥0∞) ^ s * min (v y) (N : ℝ≥0∞) ^ (1 - s) ≤
            ENNReal.ofReal (h (s * x + (1 - s) * y)) :=
          (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) hs0.le)
            (ENNReal.rpow_le_rpow (min_le_left _ _) h1.le)).trans (H x y)
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top l
        rwa [ENNReal.toReal_ofReal (hh0 _)] at this)
    simp only [ENNReal.ofReal_toReal (fin _)] at B
    refine le_trans (mul_le_mul' (ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) hs0.le)
      (ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) h1.le)) B
    · exact min_le_min le_rfl (by exact_mod_cast le_max_left m n)
    · exact min_le_min le_rfl (by exact_mod_cast le_max_right m n)
  rw [tr u hu, tr v hv]
  have r1 : (⨆ m : ℕ, ∫⁻ x, min (u x) (m : ℝ≥0∞)) ^ s =
      ⨆ m : ℕ, (∫⁻ x, min (u x) (m : ℝ≥0∞)) ^ s := by
    have := (ENNReal.orderIsoRpow s hs0).map_iSup fun m : ℕ => ∫⁻ x, min (u x) (m : ℝ≥0∞)
    simpa only [ENNReal.orderIsoRpow_apply] using this
  have r2 : (⨆ n : ℕ, ∫⁻ x, min (v x) (n : ℝ≥0∞)) ^ (1 - s) =
      ⨆ n : ℕ, (∫⁻ x, min (v x) (n : ℝ≥0∞)) ^ (1 - s) := by
    have := (ENNReal.orderIsoRpow (1 - s) h1).map_iSup fun n : ℕ => ∫⁻ x, min (v x) (n : ℝ≥0∞)
    simpa only [ENNReal.orderIsoRpow_apply] using this
  rw [r1, r2, ENNReal.iSup_mul]
  refine iSup_le fun m => ?_
  rw [ENNReal.mul_iSup]
  exact iSup_le fun n => key m n

end BstLean.Part152

open BstLean.Part152 in
#print axioms pl_one
