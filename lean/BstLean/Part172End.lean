import BstLean.Part172Good

/-!
# Part 172 (file `End`): the charge of the statistics event, and the classifier theorem with
no remaining hypothesis

No proof is left open; no `native_decide` or `axiom` is used.

* `en_bad`: one per-node Markov event has `ν_A`-measure at most `r⁶⁴`
  (`r = 0.3072` for `K = 7.9/n²`, `r = 0.3792` for `K = 6.4/n²`).
* **`stat_charge`**: for `80 000 ≤ n ≤ 10²⁰` and World data in the window,
  `ν_A{θ : (wr, A₁) ∉ StatEvOp2 n} ≤ 0.0006` (the remaining hypothesis of Part 171's
  `classifier_paper_final80k`).
* **`classifier_paper_uncond`**: the classifier theorem (the paper's program, Lean's
  exact-moment form) for every `n` with `80 000 ≤ n ≤ 10²⁰`, success `≥ 99/100`, with no
  hypothesis.
-/

namespace BstLean.Part172

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part161 (xLat uHat)
open BstLean.Part170 (tA mkR windowW node_bulk)
open BstLean.Part153 (nuA)
open BstLean.Part53 (unitF53)

variable {n : ℕ}

/-- The Markov bound of one per-node event, in the window. -/
lemma en_bad (hn : 80000 ≤ n) {wr : WRet n} (hw : windowW wr) {g : ℕ} (hg : g < Js n)
    (F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ)
    (hF : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2))
    (hadm : ∀ v, fr_Adm (xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v))
      (uHat (mkR wr (0, 0))) (fun A => F A v))
    (hB : ∀ A v, normSq (F A v) ≤ tA n) {k r : ℝ} (hk : 0 < k) (hr : 571 / 1000 * (425 / 100) / k ≤ r) :
    gaussMat (mA n) n (2 / (n : ℝ))
        {A | (k / (n : ℝ) ^ 2) ^ 64 < ∫ v, |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) F A v| ^ 64
          ∂stdGauss (Fin (n - 1))} ≤ ENNReal.ofReal (r ^ 64) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1 := node_bulk hn hw (0, 0) hg
  obtain ⟨-, hs2⟩ := sg_node_lat hn hw (0, 0) hg
  have hc : (mkR wr (0, 0)).1.2 ≠ 0 := sg_wr_ne hn1 hw
  have hK : 0 < k / (n : ℝ) ^ 2 := by positivity
  refine (mk_markov hn hc hs F hF hadm hB hK).trans ?_
  rw [← ENNReal.ofReal_div_of_pos (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set s := nodeS (mkR wr (0, 0)) g
  have e : ((1 - s ^ 2) * (425 / 100 / (n : ℝ) ^ 2)) ^ 64 / (k / (n : ℝ) ^ 2) ^ 64 =
      ((1 - s ^ 2) * (425 / 100) / k) ^ 64 := by
    rw [← div_pow]; congr 1; field_simp
  rw [e]
  refine pow_le_pow_left₀ (by
    have : 0 ≤ 1 - s ^ 2 := by linarith
    positivity) ?_ 64
  refine le_trans ?_ hr
  gcongr
  linarith

lemma en_num {N : ℝ} (hN : N ≤ 10 ^ 20) (hN0 : 0 ≤ N) :
    1 / 10 ^ 6 + 512 * N * (2 * (3072 / 10000 : ℝ) ^ 64 + (3792 / 10000) ^ 64) ≤ 6 / 10000 := by
  have h : 512 * N * (2 * (3072 / 10000 : ℝ) ^ 64 + (3792 / 10000) ^ 64) ≤
      512 * 10 ^ 20 * (2 * (3072 / 10000 : ℝ) ^ 64 + (3792 / 10000) ^ 64) := by gcongr
  have h2 : 512 * 10 ^ 20 * (2 * (3072 / 10000 : ℝ) ^ 64 + (3792 / 10000) ^ 64) ≤ 1 / 10000 := by
    norm_num
  linarith

/-- **The charge of the statistics event** (the remaining hypothesis of Part 171). -/
theorem stat_charge (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) {wr : WRet n} (hw : windowW wr) :
    (nuA n).real {θ | (wr, θ.1) ∉ StatEvOp2 n} ≤ 6 / 10000 := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc : (mkR wr (0, 0)).1.2 ≠ 0 := sg_wr_ne hn1 hw
  set μA := gaussMat (mA n) n (2 / (n : ℝ))
  set c0 : Ret n := mkR wr (0, 0)
  -- the sets
  set Sig := {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < SminN n ∨
      12 / (5 * (n : ℝ)) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} with hSig
  set Bk := fun (g : ℕ) (k : ℝ) (F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) →
      Fin (mA n) → ℝ) => {A | (k / (n : ℝ) ^ 2) ^ 64 <
      ∫ v, |Tf c0 (nodeS c0 g) F A v| ^ 64 ∂stdGauss (Fin (n - 1))} with hBk
  set Nul := {A : Matrix (Fin (mA n)) (Fin n) ℝ | ¬ ∀ g < Js n, ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ i, (A *ᵥ xLat c0 (nodeS c0 g) (unitF53 v)) i ≠ 0} with hNul
  set Bad := {A : Matrix (Fin (mA n)) (Fin n) ℝ | (wr, A) ∉ StatEvOp2 n} with hBad
  -- inclusion
  have hsub : Bad ⊆ Sig ∪ (⋃ g ∈ Finset.range (Js n),
      (Bk g (79 / 10) (F1 wr) ∪ Bk g (79 / 10) (F2 wr g) ∪ Bk g (32 / 5) (F3 wr g))) ∪ Nul := by
    intro A hA
    simp only [hBad, mem_setOf_eq, StatEvOp2, not_forall] at hA
    obtain ⟨hop, g, hg, hlow⟩ := hA
    by_contra hcon
    simp only [mem_union, mem_iUnion, Finset.mem_range, not_or, not_exists] at hcon
    obtain ⟨⟨hS, hB⟩, hN0⟩ := hcon
    apply hlow
    have hS' : ¬ (vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) < SminN n ∨
        12 / (5 * (n : ℝ)) < vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g)) := fun h =>
      hS ⟨g, hg, h⟩
    push_neg at hS'
    have hN' : ∀ g < Js n, ∀ᵐ v ∂stdGauss (Fin (n - 1)),
        ∀ i, (A *ᵥ xLat c0 (nodeS c0 g) (unitF53 v)) i ≠ 0 := by
      by_contra h; exact hN0 h
    obtain ⟨⟨h1, h2⟩, h3⟩ := hB g hg
    have e1 : K1N n ^ 64 = (79 / 10 / (n : ℝ) ^ 2) ^ 64 := by unfold K1N; congr 1; ring
    have e3 : K3N n ^ 64 = (32 / 5 / (n : ℝ) ^ 2) ^ 64 := by unfold K3N; congr 1; ring
    refine node_good hn hw A hop hg hS'.1 hS'.2 (hN' g hg) ?_ ?_ ?_
    · rw [e1]; exact not_lt.mp h1
    · rw [e1]; exact not_lt.mp h2
    · rw [e3]; exact not_lt.mp h3
  -- the null set
  have hNul0 : μA Nul = 0 := by
    have hae : ∀ᵐ A ∂μA, ∀ g < Js n, ∀ᵐ v ∂stdGauss (Fin (n - 1)),
        ∀ i, (A *ᵥ xLat c0 (nodeS c0 g) (unitF53 v)) i ≠ 0 := by
      rw [ae_all_iff]
      intro g
      by_cases hg : g < Js n
      · have hs : nodeS c0 g ^ 2 ≤ 1 := node_bulk hn hw (0, 0) hg
        exact (kink_ae (by omega) c0 hs).mono fun A h _ => h
      · exact Eventually.of_forall fun A h => absurd h hg
    rw [ae_iff] at hae
    simpa [hNul] using hae
  -- the ς event
  have hSigm : μA Sig ≤ ENNReal.ofReal (1 / 10 ^ 6) := by
    have h := sig_charge hn hw
    rw [← ENNReal.ofReal_toReal (measure_ne_top μA Sig)]
    exact ENNReal.ofReal_le_ofReal h
  -- the Markov events
  have hadm1 : ∀ g, ∀ v, fr_Adm (xLat c0 (nodeS c0 g) (unitF53 v)) (uHat c0)
      (fun A => F1 wr A v) := fun g v => e1v_adm c0 _
  have hadm2 : ∀ g, ∀ v, fr_Adm (xLat c0 (nodeS c0 g) (unitF53 v)) (uHat c0)
      (fun A => F2 wr g A v) := fun g v => e2v_adm (by omega) c0 hc g _
  have hadm3 : ∀ g, ∀ v, fr_Adm (xLat c0 (nodeS c0 g) (unitF53 v)) (uHat c0)
      (fun A => F3 wr g A v) := by
    intro g v A A' hx hu hr
    have := cdir_adm (by omega) c0 hc (nodeS c0 g) (xLat c0 (nodeS c0 g) (unitF53 v)) A A' hx hu hr
    simp only [F3]
    exact congrArg (fun z => √(tA n) • z) this
  have hb : ∀ g < Js n, μA (Bk g (79 / 10) (F1 wr) ∪ Bk g (79 / 10) (F2 wr g) ∪
      Bk g (32 / 5) (F3 wr g)) ≤ ENNReal.ofReal (2 * (3072 / 10000) ^ 64 + (3792 / 10000) ^ 64) := by
    intro g hg
    have b1 := en_bad hn hw hg (F1 wr) ((fr_meas_e1 wr).comp measurable_fst) (hadm1 g)
      (fun A v => e1v_normSq_le _) (k := 79 / 10) (r := 3072 / 10000) (by norm_num) (by norm_num)
    have b2 := en_bad hn hw hg (F2 wr g) ((fr_meas_e2 wr g).comp measurable_fst) (hadm2 g)
      (fun A v => e2v_normSq_le _ _) (k := 79 / 10) (r := 3072 / 10000) (by norm_num) (by norm_num)
    have b3 := en_bad hn hw hg (F3 wr g) (gd_F3_meas wr g) (hadm3 g)
      (gd_F3_le wr g) (k := 32 / 5) (r := 3792 / 10000) (by norm_num) (by norm_num)
    calc μA (Bk g (79 / 10) (F1 wr) ∪ Bk g (79 / 10) (F2 wr g) ∪ Bk g (32 / 5) (F3 wr g))
        ≤ μA (Bk g (79 / 10) (F1 wr)) + μA (Bk g (79 / 10) (F2 wr g)) +
          μA (Bk g (32 / 5) (F3 wr g)) :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal ((3072 / 10000) ^ 64) + ENNReal.ofReal ((3072 / 10000) ^ 64) +
          ENNReal.ofReal ((3792 / 10000) ^ 64) := add_le_add (add_le_add b1 b2) b3
      _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  -- total
  have htot : μA Bad ≤ ENNReal.ofReal (6 / 10000) := by
    refine (measure_mono hsub).trans ?_
    refine (measure_union_le _ _).trans ?_
    rw [hNul0, add_zero]
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add hSigm (measure_biUnion_finset_le _ _)).trans ?_
    refine (add_le_add le_rfl (Finset.sum_le_sum fun g hg => hb g (Finset.mem_range.mp hg))).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have e : ((Js n : ℕ) : ℝ≥0∞) = ENNReal.ofReal (512 * (n : ℝ)) := by
      unfold Js; push_cast
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]; norm_num
    rw [e, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by norm_num) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (en_num hN hn0)
  -- back to `nuA`
  have hset : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      (wr, θ.1) ∉ StatEvOp2 n} = Bad ×ˢ univ := by
    ext θ; simp [hBad]
  rw [hset, measureReal_def, Measure.prod_prod, measure_univ, mul_one]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) htot

/-- **The classifier theorem with no remaining hypothesis** (the paper's program in Lean's
exact-moment form; every `n` with `80 000 ≤ n ≤ 10²⁰`; success probability `≥ 99/100` for the
actual random networks). -/
theorem classifier_paper_uncond (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_final80k hn t fun _ hw => stat_charge hn hN hw

end BstLean.Part172
