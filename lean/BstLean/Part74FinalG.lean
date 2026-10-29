import BstLean.Part74Final33
import BstLean.Part69Final

/-!
# Part 74: Theorem 1 at a general degree pair `2 ≤ d_f = k ≤ d = d_M`, at strict cost, from a
moment program of cost `B (n + K + 1)`

`part74_single_gen_of`: the statement of `Part69.part69_single` with `(2, 2) ↦ (k, d)`, with the
moment program abstracted as a hypothesis (`MomSpecUsed74`, cost `≤ B (n + K + 1)`).
Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part74

open MeasureTheory BstLean.Cost
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (frob Tens TSymm baseline heavyCount Pn NN)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part56

theorem choose_ge74 (n d : ℕ) (hd : 1 ≤ d) : n + 1 ≤ (n + d).choose d := by
  induction d, hd using Nat.le_induction with
  | base => simp
  | succ d _ ih =>
    rw [← Nat.add_assoc, Nat.choose_succ_succ]
    omega

/-- `P = n C(n+d, d) ≥ n²` for `d ≥ 1`. -/
theorem Pn_ge74 (n d : ℕ) (hd : 1 ≤ d) : (n : ℝ) * n ≤ Pn n d := by
  unfold Pn
  rw [BstLean.Part36.DD_eq]
  have h : ((n : ℝ)) + 1 ≤ ((n + d).choose d : ℝ) := by exact_mod_cast choose_ge74 n d hd
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- For every `α, β`, the cost `B (n + (α n + β) + 1)` is below `c · P` for large `n`. -/
theorem cost_small74 (d : ℕ) (hd : 1 ≤ d) (B α β c : ℝ) (hB : 0 ≤ B) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hc : 0 < c) :
    ∃ n1 : ℕ, ∀ n : ℕ, n1 ≤ n → B * ((n : ℝ) + (α * n + β) + 1) ≤ c * Pn n d := by
  set X := B * (1 + α + β + 1)
  refine ⟨⌈X / c⌉₊ + 1, fun n hn => ?_⟩
  have hn1 : (⌈X / c⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hX : X / c ≤ n := (Nat.le_ceil _).trans (by linarith)
  have hX' : X ≤ c * n := by rw [div_le_iff₀ hc] at hX; linarith
  have h1 : (1 : ℝ) ≤ n := le_trans (by linarith [Nat.cast_nonneg (α := ℝ) ⌈X / c⌉₊]) hn1
  have hP := Pn_ge74 n d hd
  have hXn : B * ((n : ℝ) + (α * n + β) + 1) ≤ X * n := by
    have : (n : ℝ) + (α * n + β) + 1 ≤ (1 + α + β + 1) * n := by nlinarith
    calc B * ((n : ℝ) + (α * n + β) + 1) ≤ B * ((1 + α + β + 1) * n) :=
          mul_le_mul_of_nonneg_left this hB
      _ = X * n := by simp only [X]; ring
  have : X * n ≤ c * ((n : ℝ) * n) := by
    nlinarith [mul_le_mul_of_nonneg_right hX' (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  have : c * ((n : ℝ) * n) ≤ c * Pn n d := mul_le_mul_of_nonneg_left hP hc.le
  linarith

/-- **Theorem 1 at a general degree pair `2 ≤ k ≤ d` at strict cost**, given a moment program
that meets `MomSpecUsed74` at cost `≤ B (n + K + 1)`. -/
theorem part74_single_gen_of (k d : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (B : ℕ)
    (hprog : ∀ n K : ℕ, 2 ≤ n → ∃ pm : Prog (InM56 n) (KeyRK k d), heavyCount pm = 0 ∧
      MomSpecUsed74 pm K ∧ pm.cost ≤ B * (n + K + 1))
    (C εlo εhi : ℝ) (hlo : 0 < εlo) (hlh : εlo ≤ εhi) (hhi : εhi ^ 2 < 91 / 200) :
    ∃ (η : ℝ) (n0 : ℕ), 0 < η ∧ 100 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      ∃ (pm : Prog (InM56 n) (KeyRK k d)) (pg : Prog (In56 n d k) Unit),
        heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpecUsed74 pm (KRK C n η) ∧ GSpec56 pg ∧
        (pm.cost : ℝ) ≤ B * ((n : ℝ) + (KRK C n η : ℝ) + 1) ∧
        ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
        ∀ ε : ℝ, εlo ≤ ε → ε ≤ εhi →
        ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varFQ (lawRK n t v) k f0 T (unitOfD Z) <
              (BofQ (lawRK n t v) k f0 T (unitOfD Z) -
                pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) ∧
          (pm.cost : ℝ) + pg.cost < baseline n d ε := by
  have hfail := BstLean.Part64.part64_fail k d hk hkd C εlo εhi hlo
  set η := eRK k (BstLean.Part64.s64 k) εlo
  have hεhi : 0 < εhi := lt_of_lt_of_le hlo hlh
  obtain ⟨nc, hc⟩ := costLine56_lt d k (by omega) hkd εhi hεhi hhi
  have hν := nuRK_pos εhi hhi
  set L := BstLean.Part43.Leta η
  obtain ⟨n1, h1⟩ := cost_small74 d (by omega) B ((1 + 2 * |L|) * |C|) (|L| / 3 + L ^ 2 / 9 + 2)
    (nuRK εhi * (91 / 100) / εhi ^ 2) (by positivity) (by positivity) (by positivity)
    (by positivity)
  have hη0 : 0 < η := by
    simp only [η]; unfold eRK etaRK BstLean.Part43.xi43
    have := BstLean.Part64.tsb64_pos k
    unfold BstLean.Part64.s64; positivity
  refine ⟨η, max (max (BstLean.Part64.NF56 d k C εlo) nc) (max n1 100), hη0, le_max_of_le_right
    (le_max_right _ _), fun n hn => ?_⟩
  have hnf : BstLean.Part64.NF56 d k C εlo ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnc : nc ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : n1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn100 : 100 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨pg, hpg0, hpgs, hpgc⟩ := lineProg56_exists n d k (by omega)
  obtain ⟨pm, hpm0, hpms, hpmc⟩ := hprog n (KRK C n η) (by omega)
  have hpmc' : (pm.cost : ℝ) ≤ B * ((n : ℝ) + (KRK C n η : ℝ) + 1) := by exact_mod_cast hpmc
  refine ⟨pm, pg, hpm0, hpg0, hpms, hpgs, hpmc', fun v hv t ht0 ht ε hε1 hε2 f0 T hT hTk => ⟨?_, ?_⟩⟩
  · have heval : ∀ M : CoefIdxD n d → ℝ,
        pg.eval (inp56 f0 T M v (pm.eval (inRK t v))) () =
          gLineW (surrRK n (KRK C n η) t v) k f0 T v M :=
      fun M => eval74 pm pg _ hpms hpgs t v ht0 hv f0 T hT M
    simp only [heval]
    exact hfail n hnf v hv t ht0 ht ε hε1 hε2 f0 T hT hTk
  · have hK : (KRK C n η : ℝ) ≤ (1 + 2 * |L|) * |C| * n + (|L| / 3 + L ^ 2 / 9 + 2) := by
      have := BstLean.Part69.K_le69 (C * n) η
      rw [abs_mul, Nat.abs_cast] at this
      unfold KRK; linarith
    have hm := h1 n hn1
    have hP : 0 < Pn n d := by
      have := Pn_ge74 n d (by omega)
      have h100 : (100 : ℝ) ≤ n := by exact_mod_cast hn100
      nlinarith
    have hε : 0 < ε := lt_of_lt_of_le hlo hε1
    have hbase : 91 / 100 * Pn n d / εhi ^ 2 ≤ baseline n d ε := by
      unfold baseline
      refine le_trans ?_ (le_max_right _ _)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ hε.le hε2 2
    have hcl := hc n hnc
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    have : (pm.cost : ℝ) ≤ nuRK εhi * (91 / 100) / εhi ^ 2 * Pn n d := by
      calc (pm.cost : ℝ) ≤ B * ((n : ℝ) + (KRK C n η : ℝ) + 1) := hpmc'
        _ ≤ B * ((n : ℝ) + ((1 + 2 * |L|) * |C| * n + (|L| / 3 + L ^ 2 / 9 + 2)) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hB0
        _ ≤ _ := hm
    have e : nuRK εhi * (91 / 100) / εhi ^ 2 * Pn n d + (1 - nuRK εhi) * (91 / 100) * Pn n d /
        εhi ^ 2 = 91 / 100 * Pn n d / εhi ^ 2 := by field_simp; ring
    have hpg' := lt_of_le_of_lt hpgc hcl
    linarith

end BstLean.Part74

#print axioms BstLean.Part74.part74_single_gen_of
