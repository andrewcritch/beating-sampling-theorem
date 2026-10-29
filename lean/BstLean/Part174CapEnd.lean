import BstLean.Part174CapGood

/-!
# Part 174 (file `CapEnd`): the statistics charge with growing Markov thresholds, and the
classifier theorem with no upper bound on `n`

No proof is left open; no `native_decide` or `axiom` is used.

Part 172's cap `n ≤ 10²⁰` comes only from the union over the `512n` nodes of per-node Markov
bounds of order 64 with fixed thresholds. Here the thresholds grow: `K_k = κ·(7.9 or 6.4)/n²` with
`κ = n^{1/64}`, so the union costs `512n·κ⁻⁶⁴·(…) = 512·(…)`, independent of `n`.

* `en_numK`, **`stat_chargeK`**: the charge `≤ 0.0006` of Part 171's free-threshold statistics event
  `StatEvOpG n (1/(5n)) (κ·16/n³) (κ²·64/n⁴) (1/n⁴)`, for any `κ ≥ 1` with `48 900κ² ≤ n ≤ κ⁶⁴`.
* `kap`, `kap_facts`: `κ = n^{1/64}` satisfies these and `67 568κ² ≤ n` for `n ≥ 10¹⁹`.
* `AF0_le` … `AW2_le`: the row-bound coefficients at the scaled thresholds are `≤ κ²` times the old.
* **`classifier_paper_uncond_large`**: the classifier theorem for every `n ≥ 10¹⁹` (no upper end),
  through Part 171's `classifier_paper_gen80k`.
* **`classifier_paper_uncond_nocap`**: the classifier theorem for every `n ≥ 55 000`, no upper end
  (with Part 174's `classifier_paper_uncond_55000` for `n ≤ 10²⁰`); `uncond_nocap_eq_172` (`rfl`).
-/

namespace BstLean.Part174.Cap

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part172
open BstLean.Part161 (xLat uHat)
open BstLean.Part170 (tA mkR windowW node_bulk)
open BstLean.Part153 (nuA phiG phiG_pos)
open BstLean.Part53 (unitF53)

variable {n : ℕ}

/-- The total with growing thresholds: `n·κ⁻⁶⁴ ≤ 1`. -/
lemma en_numK {N κ : ℝ} (hκ0 : 0 < κ) (hκ : N ≤ κ ^ 64) (hN0 : 0 ≤ N) :
    1 / 10 ^ 6 + 512 * N * (2 * (3072 / 10000 / κ) ^ 64 + (3792 / 10000 / κ) ^ 64) ≤ 6 / 10000 := by
  have e : 512 * N * (2 * (3072 / 10000 / κ) ^ 64 + (3792 / 10000 / κ) ^ 64) =
      (N / κ ^ 64) * (512 * (2 * (3072 / 10000 : ℝ) ^ 64 + (3792 / 10000) ^ 64)) := by
    rw [div_pow, div_pow]; field_simp
  have h1 : N / κ ^ 64 ≤ 1 := by rw [div_le_one (by positivity)]; exact hκ
  have h2 : (512 * (2 * (3072 / 10000 : ℝ) ^ 64 + (3792 / 10000) ^ 64)) ≤ 1 / 10000 := by norm_num
  have h0 : 0 ≤ N / κ ^ 64 := by positivity
  rw [e]
  nlinarith

/-- **The charge of the statistics event** (the remaining hypothesis of Part 171). -/
theorem stat_chargeK (hn : 80000 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ) (hκN : 48900 * κ ^ 2 ≤ (n : ℝ))
    (hκ64 : (n : ℝ) ≤ κ ^ 64) {wr : WRet n} (hw : windowW wr) :
    (nuA n).real {θ | (wr, θ.1) ∉ StatEvOpG n (SminN n) (κ * DmN n) (κ ^ 2 * VmN n) (PmN n)} ≤
      6 / 10000 := by
  have hκ0 : 0 < κ := by linarith
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
  set Bad := {A : Matrix (Fin (mA n)) (Fin n) ℝ | (wr, A) ∉ StatEvOpG n (SminN n) (κ * DmN n) (κ ^ 2 * VmN n) (PmN n)} with hBad
  -- inclusion
  have hsub : Bad ⊆ Sig ∪ (⋃ g ∈ Finset.range (Js n),
      (Bk g (79 / 10 * κ) (F1 wr) ∪ Bk g (79 / 10 * κ) (F2 wr g) ∪ Bk g (32 / 5 * κ) (F3 wr g))) ∪ Nul := by
    intro A hA
    simp only [hBad, mem_setOf_eq, StatEvOpG, not_forall] at hA
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
    have e1 : (κ * K1N n) ^ 64 = (79 / 10 * κ / (n : ℝ) ^ 2) ^ 64 := by unfold K1N; congr 1; ring
    have e3 : (κ * K3N n) ^ 64 = (32 / 5 * κ / (n : ℝ) ^ 2) ^ 64 := by unfold K3N; congr 1; ring
    refine node_goodK hn hκ hκN hw A hop hg hS'.1 hS'.2 (hN' g hg) ?_ ?_ ?_
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
  have hb : ∀ g < Js n, μA (Bk g (79 / 10 * κ) (F1 wr) ∪ Bk g (79 / 10 * κ) (F2 wr g) ∪
      Bk g (32 / 5 * κ) (F3 wr g)) ≤
        ENNReal.ofReal (2 * (3072 / 10000 / κ) ^ 64 + (3792 / 10000 / κ) ^ 64) := by
    intro g hg
    have b1 := en_bad hn hw hg (F1 wr) ((fr_meas_e1 wr).comp measurable_fst) (hadm1 g)
      (fun A v => e1v_normSq_le _) (k := 79 / 10 * κ) (r := 3072 / 10000 / κ) (by positivity) (by rw [div_le_div_iff₀ (by positivity) hκ0]; nlinarith)
    have b2 := en_bad hn hw hg (F2 wr g) ((fr_meas_e2 wr g).comp measurable_fst) (hadm2 g)
      (fun A v => e2v_normSq_le _ _) (k := 79 / 10 * κ) (r := 3072 / 10000 / κ) (by positivity) (by rw [div_le_div_iff₀ (by positivity) hκ0]; nlinarith)
    have b3 := en_bad hn hw hg (F3 wr g) (gd_F3_meas wr g) (hadm3 g)
      (gd_F3_le wr g) (k := 32 / 5 * κ) (r := 3792 / 10000 / κ) (by positivity) (by rw [div_le_div_iff₀ (by positivity) hκ0]; nlinarith)
    calc μA (Bk g (79 / 10 * κ) (F1 wr) ∪ Bk g (79 / 10 * κ) (F2 wr g) ∪ Bk g (32 / 5 * κ) (F3 wr g))
        ≤ μA (Bk g (79 / 10 * κ) (F1 wr)) + μA (Bk g (79 / 10 * κ) (F2 wr g)) +
          μA (Bk g (32 / 5 * κ) (F3 wr g)) :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal ((3072 / 10000 / κ) ^ 64) + ENNReal.ofReal ((3072 / 10000 / κ) ^ 64) +
          ENNReal.ofReal ((3792 / 10000 / κ) ^ 64) := add_le_add (add_le_add b1 b2) b3
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
    exact ENNReal.ofReal_le_ofReal (en_numK hκ0 hκ64 hn0)
  -- back to `nuA`
  have hset : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      (wr, θ.1) ∉ StatEvOpG n (SminN n) (κ * DmN n) (κ ^ 2 * VmN n) (PmN n)} = Bad ×ˢ univ := by
    ext θ; simp [hBad]
  rw [hset, measureReal_def, Measure.prod_prod, measure_univ, mul_one]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) htot

/-! ## The growing factor `κ = n^{1/64}` -/

/-- `κ = n^{1/64}`. -/
noncomputable def kap (n : ℕ) : ℝ := (n : ℝ) ^ ((1 : ℝ) / 64)

lemma kap_pow (n : ℕ) : kap n ^ 64 = n := by
  unfold kap
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

/-- For `n ≥ 10¹⁹`: `κ ≥ 6/5`, `1 ≤ κ`, `67 568κ² ≤ n`, `48 900κ² ≤ n`, `n ≤ κ⁶⁴`. -/
lemma kap_facts (hn : (10 : ℝ) ^ 19 ≤ n) :
    1 ≤ kap n ∧ 67568 * kap n ^ 2 ≤ (n : ℝ) ∧ 48900 * kap n ^ 2 ≤ (n : ℝ) ∧
      (n : ℝ) ≤ kap n ^ 64 := by
  have hp := kap_pow n
  have h0 : 0 ≤ kap n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h12 : 6 / 5 ≤ kap n := by
    by_contra hc
    have hc' : kap n < 6 / 5 := not_le.mp hc
    have : kap n ^ 64 < (6 / 5) ^ 64 := pow_lt_pow_left₀ hc' h0 (by norm_num)
    have : (6 / 5 : ℝ) ^ 64 < 10 ^ 19 := by norm_num
    linarith
  have h62 : (6 / 5 : ℝ) ^ 62 ≤ kap n ^ 62 := pow_le_pow_left₀ (by norm_num) h12 62
  have hk2 : 0 ≤ kap n ^ 2 := sq_nonneg _
  have e : (n : ℝ) = kap n ^ 2 * kap n ^ 62 := by rw [← pow_add]; exact hp.symm
  have h1 : 67568 * kap n ^ 2 ≤ (n : ℝ) := by
    rw [e]
    have : (67568 : ℝ) ≤ (6 / 5) ^ 62 := by norm_num
    nlinarith
  refine ⟨by linarith, h1, by nlinarith, le_of_eq hp.symm⟩

/-! ## The row-bound coefficients at the scaled thresholds -/

lemma sc_sqrt {κ D V : ℝ} (hκ : 1 ≤ κ) (hD : 0 ≤ D) (hV : 0 ≤ V) :
    √(κ * D) * √(κ ^ 2 * V) ≤ κ ^ 2 * (√D * √V) := by
  have hκ0 : 0 ≤ κ := by linarith
  rw [Real.sqrt_mul hκ0, Real.sqrt_mul (sq_nonneg κ), Real.sqrt_sq hκ0]
  have hs : √κ ≤ κ := by
    rw [Real.sqrt_le_left hκ0]; nlinarith
  have h0 : 0 ≤ √D * √V := by positivity
  calc √κ * √D * (κ * √V) = (√κ * κ) * (√D * √V) := by ring
    _ ≤ (κ * κ) * (√D * √V) := by gcongr
    _ = κ ^ 2 * (√D * √V) := by ring

lemma AF0_le {sm Γ D V P κ : ℝ} (hκ : 1 ≤ κ) (hsm : 0 < sm) (hΓ : 0 ≤ Γ) (hD : 0 ≤ D)
    (hV : 0 ≤ V) (hP : 0 ≤ P) :
    AF0 sm Γ (κ * D) (κ ^ 2 * V) P ≤ κ ^ 2 * AF0 sm Γ D V P := by
  unfold AF0
  have hp := phiG_pos 0
  have a : 0 ≤ phiG 0 / (2 * sm) * D := by positivity
  have b : 0 ≤ 1 / 2 * (phiG 0 / (√2 * sm ^ 3) * V) := by positivity
  have c : 0 ≤ P * (3 / 2 * phiG 0 / sm * Γ) := by positivity
  have hk : κ ≤ κ ^ 2 := by nlinarith
  have hk1 : 1 ≤ κ ^ 2 := by nlinarith
  calc phiG 0 / (2 * sm) * (κ * D) + 1 / 2 * (phiG 0 / (√2 * sm ^ 3) * (κ ^ 2 * V)) +
        P * (3 / 2 * phiG 0 / sm * Γ)
      = κ * (phiG 0 / (2 * sm) * D) + κ ^ 2 * (1 / 2 * (phiG 0 / (√2 * sm ^ 3) * V)) +
        P * (3 / 2 * phiG 0 / sm * Γ) := by ring
    _ ≤ κ ^ 2 * (phiG 0 / (2 * sm) * D) + κ ^ 2 * (1 / 2 * (phiG 0 / (√2 * sm ^ 3) * V)) +
        κ ^ 2 * (P * (3 / 2 * phiG 0 / sm * Γ)) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_right hk a) le_rfl)
            (le_mul_of_one_le_left c hk1)
    _ = _ := by ring

lemma AF1_le {sm D V P C κ : ℝ} (hκ : 1 ≤ κ) (hsm : 0 < sm) (hD : 0 ≤ D) (hV : 0 ≤ V)
    (hP : 0 ≤ P) (hC : 0 ≤ C) :
    AF1 sm (κ * D) (κ ^ 2 * V) P C ≤ κ ^ 2 * AF1 sm D V P C := by
  unfold AF1
  have hp := phiG_pos 1
  have hs := sc_sqrt hκ hD hV
  have hk1 : 1 ≤ κ ^ 2 := by nlinarith
  have c : 0 ≤ P * (2 * (2 * √2 * C)) := by positivity
  have hco : 0 ≤ 1 / 2 * (2 * phiG 1 / sm ^ 2) := by positivity
  calc 1 / 2 * (2 * phiG 1 / sm ^ 2 * (√(κ * D) * √(κ ^ 2 * V))) + P * (2 * (2 * √2 * C))
      = 1 / 2 * (2 * phiG 1 / sm ^ 2) * (√(κ * D) * √(κ ^ 2 * V)) + P * (2 * (2 * √2 * C)) := by
        ring
    _ ≤ 1 / 2 * (2 * phiG 1 / sm ^ 2) * (κ ^ 2 * (√D * √V)) + κ ^ 2 * (P * (2 * (2 * √2 * C))) :=
        add_le_add (mul_le_mul_of_nonneg_left hs hco) (le_mul_of_one_le_left c hk1)
    _ = _ := by ring

lemma AF2_le {sm D κ : ℝ} (hκ : 1 ≤ κ) (hsm : 0 < sm) (hD : 0 ≤ D) :
    AF2 sm (κ * D) ≤ κ ^ 2 * AF2 sm D := by
  unfold AF2
  have hp := phiG_pos 0
  have a : 0 ≤ 1 / 2 * (√2 * phiG 0 / sm * D) := by positivity
  have hk : κ ≤ κ ^ 2 := by nlinarith
  calc 1 / 2 * (√2 * phiG 0 / sm * (κ * D)) = κ * (1 / 2 * (√2 * phiG 0 / sm * D)) := by ring
    _ ≤ κ ^ 2 * (1 / 2 * (√2 * phiG 0 / sm * D)) := by gcongr

lemma AW0_le {sm Γ D V P κ : ℝ} (hκ : 1 ≤ κ) (hsm : 0 < sm) (hΓ : 0 ≤ Γ) (hD : 0 ≤ D)
    (hV : 0 ≤ V) (hP : 0 ≤ P) :
    AW0 sm Γ (κ * D) (κ ^ 2 * V) P ≤ κ ^ 2 * AW0 sm Γ D V P := by
  unfold AW0
  have hp := phiG_pos 1
  have b : 0 ≤ phiG 1 / (2 * sm ^ 2) * V := by positivity
  have c : 0 ≤ P * (4 * Γ) := by positivity
  have hk : κ ≤ κ ^ 2 := by nlinarith
  have hk1 : 1 ≤ κ ^ 2 := by nlinarith
  calc κ * D + phiG 1 / (2 * sm ^ 2) * (κ ^ 2 * V) + P * (4 * Γ)
      = κ * D + κ ^ 2 * (phiG 1 / (2 * sm ^ 2) * V) + P * (4 * Γ) := by ring
    _ ≤ κ ^ 2 * D + κ ^ 2 * (phiG 1 / (2 * sm ^ 2) * V) + κ ^ 2 * (P * (4 * Γ)) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_right hk hD) le_rfl)
          (le_mul_of_one_le_left c hk1)
    _ = _ := by ring

lemma AW1_le {sm sp D V P C κ : ℝ} (hκ : 1 ≤ κ) (hsm : 0 < sm) (hsp : 0 ≤ sp) (hD : 0 ≤ D)
    (hV : 0 ≤ V) (hP : 0 ≤ P) (hC : 0 ≤ C) :
    AW1 sm sp (κ * D) (κ ^ 2 * V) P C ≤ κ ^ 2 * AW1 sm sp D V P C := by
  unfold AW1
  have hp := phiG_pos 0
  have hs := sc_sqrt hκ hD hV
  have hk1 : 1 ≤ κ ^ 2 := by nlinarith
  have c : 0 ≤ P * (4 * √2 * C * sp) := by positivity
  have hco : 0 ≤ √2 * phiG 0 / sm := by positivity
  calc √2 * phiG 0 / sm * (√(κ * D) * √(κ ^ 2 * V)) + P * (4 * √2 * C * sp)
      ≤ √2 * phiG 0 / sm * (κ ^ 2 * (√D * √V)) + κ ^ 2 * (P * (4 * √2 * C * sp)) :=
        add_le_add (mul_le_mul_of_nonneg_left hs hco) (le_mul_of_one_le_left c hk1)
    _ = _ := by ring

lemma AW2_le {D P C κ : ℝ} (hκ : 1 ≤ κ) (hD : 0 ≤ D) (hP : 0 ≤ P) :
    AW2 (κ * D) P C ≤ κ ^ 2 * AW2 D P C := by
  unfold AW2
  have c : 0 ≤ P * (28 * C ^ 2) := by positivity
  have hk : κ ≤ κ ^ 2 := by nlinarith
  have hk1 : 1 ≤ κ ^ 2 := by nlinarith
  nlinarith

/-! ## The end theorems -/

/-- **The classifier theorem with no upper end, for every `n ≥ 10¹⁹`.** -/
theorem classifier_paper_uncond_large (hn : (10 : ℝ) ^ 19 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn8 : 80000 ≤ n := by
    have : (80000 : ℝ) ≤ n := le_trans (by norm_num) hn
    exact_mod_cast this
  obtain ⟨κ, hκd⟩ : ∃ κ, κ = kap n := ⟨_, rfl⟩
  obtain ⟨hκ, hκ67, hκN, hκ64⟩ := hκd ▸ kap_facts hn
  obtain ⟨hF0, hF1, hF2, hF⟩ := numF' hn8
  obtain ⟨hW0, hW1, hW2, hW⟩ := numW' hn8
  have hn0 : (0 : ℝ) < n := by linarith [show (0:ℝ) < 10 ^ 19 by norm_num]
  have hsm : 0 < √(SminN n) := Real.sqrt_pos.mpr (by unfold SminN; positivity)
  have hsp : 0 ≤ √(SmaxN n) := Real.sqrt_nonneg _
  have hΓ : 0 ≤ tA n * O1n n ^ 2 + SmaxN n := by
    have := BstLean.Part171.tA_nonneg n; unfold SmaxN; positivity
  have hD : 0 ≤ DmN n := by unfold DmN; positivity
  have hV : 0 ≤ VmN n := by unfold VmN; positivity
  have hP : 0 ≤ PmN n := by unfold PmN; positivity
  have hC : 0 ≤ √(tA n) * O1n n := mul_nonneg (Real.sqrt_nonneg _) (O1n_nonneg n)
  have hk1 : 1 ≤ κ ^ 2 := by nlinarith
  have hp0 := phiG_pos 0
  have hp1 := phiG_pos 1
  -- the location condition
  obtain ⟨X, hXd⟩ : ∃ X, X = AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (PmN n) +
    AF1 √(SminN n) (DmN n) (VmN n) (PmN n) (√(tA n) * O1n n) * (211 / 100) +
    AF2 √(SminN n) (DmN n) * (754 / 100) := ⟨_, rfl⟩
  rw [← hXd] at hF
  have hX0 : 0 ≤ X := by rw [hXd]; unfold AF0 AF1 AF2; positivity
  have hXn : AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (κ * DmN n) (κ ^ 2 * VmN n) (PmN n) +
      AF1 √(SminN n) (κ * DmN n) (κ ^ 2 * VmN n) (PmN n) (√(tA n) * O1n n) * (211 / 100) +
      AF2 √(SminN n) (κ * DmN n) * (754 / 100) ≤ κ ^ 2 * X := by
    have a := AF0_le hκ hsm hΓ hD hV hP
    have b := AF1_le hκ hsm hD hV hP hC
    have c := AF2_le hκ hsm hD
    have := add_le_add (add_le_add a (mul_le_mul_of_nonneg_right b (by norm_num : (0:ℝ) ≤ 211 / 100)))
      (mul_le_mul_of_nonneg_right c (by norm_num : (0:ℝ) ≤ 754 / 100))
    refine this.trans (le_of_eq ?_); rw [hXd]; ring
  -- the energy condition
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (PmN n) +
    AW1 √(SminN n) √(SmaxN n) (DmN n) (VmN n) (PmN n) (√(tA n) * O1n n) * (211 / 100) +
    AW2 (DmN n) (PmN n) (√(tA n) * O1n n) * (754 / 100) := ⟨_, rfl⟩
  rw [← hYd] at hW
  have hY0 : 0 ≤ Y := by rw [hYd]; unfold AW0 AW1 AW2; positivity
  have hYn : AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (κ * DmN n) (κ ^ 2 * VmN n) (PmN n) +
      AW1 √(SminN n) √(SmaxN n) (κ * DmN n) (κ ^ 2 * VmN n) (PmN n) (√(tA n) * O1n n) * (211 / 100) +
      AW2 (κ * DmN n) (PmN n) (√(tA n) * O1n n) * (754 / 100) ≤ κ ^ 2 * Y := by
    have a := AW0_le hκ hsm hΓ hD hV hP
    have b := AW1_le hκ hsm hsp hD hV hP hC
    have c := AW2_le (C := √(tA n) * O1n n) hκ hD hP
    have := add_le_add (add_le_add a (mul_le_mul_of_nonneg_right b (by norm_num : (0:ℝ) ≤ 211 / 100)))
      (mul_le_mul_of_nonneg_right c (by norm_num : (0:ℝ) ≤ 754 / 100))
    refine this.trans (le_of_eq ?_); rw [hYd]; ring
  have hnm0 : 0 ≤ ((n : ℝ) * ((mA n : ℕ) : ℝ)) ^ 4 := by positivity
  have hκ0 : 0 < κ := by linarith
  have hDp : 0 < DmN n := by unfold DmN; positivity
  have hVp : 0 < VmN n := by unfold VmN; positivity
  have hPp : 0 < PmN n := by unfold PmN; positivity
  have hΓp : 0 < tA n * O1n n ^ 2 + SmaxN n := by
    have := BstLean.Part171.tA_nonneg n
    have : 0 < SmaxN n := by unfold SmaxN; positivity
    positivity
  have hspp : 0 < √(SmaxN n) := Real.sqrt_pos.mpr (by unfold SmaxN; positivity)
  have hCp : 0 < √(tA n) * O1n n := by
    have h1 : 0 < tA n := by unfold tA mA; positivity
    have h2 : 0 < O1n n := by unfold O1n; positivity
    positivity
  have hm0 : 0 ≤ ((mA n : ℕ) : ℝ) ^ 8 := by positivity
  refine classifier_paper_gen80k hn8 t (Sm := SminN n) (Dm := κ * DmN n) (Vm := κ ^ 2 * VmN n)
    (Pm := PmN n) (z₁ := 211 / 100) (z₂ := 754 / 100) (by unfold SminN; positivity)
    (by norm_num) (by norm_num) z1_pow z2_pow ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · unfold AF0; positivity
  · unfold AF1; positivity
  · unfold AF2; positivity
  · -- (nm)⁴(new)⁸ ≤ κ¹⁶(nm)⁴X⁸ ≤ (κ²·270/n)⁸ ≤ 0.004⁸
    have hnew0 : 0 ≤ AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (κ * DmN n) (κ ^ 2 * VmN n) (PmN n) +
      AF1 √(SminN n) (κ * DmN n) (κ ^ 2 * VmN n) (PmN n) (√(tA n) * O1n n) * (211 / 100) +
      AF2 √(SminN n) (κ * DmN n) * (754 / 100) := by
      unfold AF0 AF1 AF2; positivity
    calc _ ≤ ((n : ℝ) * ((mA n : ℕ) : ℝ)) ^ 4 * (κ ^ 2 * X) ^ 8 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnew0 hXn 8) hnm0
      _ = (κ ^ 2) ^ 8 * (((n : ℝ) * ((mA n : ℕ) : ℝ)) ^ 4 * X ^ 8) := by ring
      _ ≤ (κ ^ 2) ^ 8 * (270 / (n : ℝ)) ^ 8 := mul_le_mul_of_nonneg_left hF (by positivity)
      _ = (κ ^ 2 * (270 / (n : ℝ))) ^ 8 := by ring
      _ ≤ (4 / 1000) ^ 8 := by
          refine pow_le_pow_left₀ (by positivity) ?_ 8
          rw [show κ ^ 2 * (270 / (n : ℝ)) = 270 * κ ^ 2 / n by ring, div_le_iff₀ hn0]
          linarith
  · unfold AW0; positivity
  · unfold AW1; positivity
  · unfold AW2; positivity
  · have hnew0 : 0 ≤ AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (κ * DmN n) (κ ^ 2 * VmN n) (PmN n) +
      AW1 √(SminN n) √(SmaxN n) (κ * DmN n) (κ ^ 2 * VmN n) (PmN n) (√(tA n) * O1n n) * (211 / 100) +
      AW2 (κ * DmN n) (PmN n) (√(tA n) * O1n n) * (754 / 100) := by
      unfold AW0 AW1 AW2; positivity
    calc _ ≤ ((mA n : ℕ) : ℝ) ^ 8 * (κ ^ 2 * Y) ^ 8 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnew0 hYn 8) hm0
      _ = (κ ^ 2) ^ 8 * (((mA n : ℕ) : ℝ) ^ 8 * Y ^ 8) := by ring
      _ ≤ (κ ^ 2) ^ 8 * (280 / (n : ℝ)) ^ 8 := mul_le_mul_of_nonneg_left hW (by positivity)
      _ = (κ ^ 2 * (280 / (n : ℝ))) ^ 8 := by ring
      _ ≤ (2 / 100) ^ 8 := by
          refine pow_le_pow_left₀ (by positivity) ?_ 8
          rw [show κ ^ 2 * (280 / (n : ℝ)) = 280 * κ ^ 2 / n by ring, div_le_iff₀ hn0]
          linarith
  · exact fun wr hw => stat_chargeK hn8 hκ hκN hκ64 hw

/-- **The classifier theorem with no hypothesis and no upper end: every `n ≥ 55 000`, every
threshold `t`** (the paper's program in Lean's exact-moment form; success `≥ 99/100` for the actual
random networks). -/
theorem classifier_paper_uncond_nocap {n : ℕ} (hn : 55000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  rcases le_total (n : ℝ) (10 ^ 20) with h | h
  · exact BstLean.Part174.classifier_paper_uncond_55000 hn h t
  · exact classifier_paper_uncond_large (le_trans (by norm_num) h) t

/-- The conclusion is Part 172's: on `80 000 ≤ n ≤ 10²⁰` the two proofs are equal by `rfl`. -/
theorem uncond_nocap_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_nocap (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

end BstLean.Part174.Cap
