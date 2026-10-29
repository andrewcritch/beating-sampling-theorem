import BstLean.Part41Tensor
import BstLean.Part41Keep
import BstLean.Part41Error
import BstLean.Part41Prog
import BstLean.Part41Consts
import BstLean.Part41Norm
import BstLean.Part41Upper
import BstLean.Part41Floor1
import BstLean.Part41Contam
import BstLean.Part41Ball
import BstLean.Part41Budget

/-!
# Part 41, wave 2: the failure bound and the costed program of Theorem TC-LF

Paper: the proof of Theorem TC-LF in `proofs/option-m/41-arbitrary-degree.tex`. Specification:
`delegations/answers/p41-spec-opus.md`. Proved here from the wave-1 statements.

* `floor_event` is Lemma `LF-ball`: `LF_i`, `EP_lower`, `cascade` (with `nu_bounds`), `contam`, `pball`
  and Markov.
* `fail_bound`: on `E₁ ∩ E₂ ∩ E₃` (`radius_event`, `floor_event`, `upper_event`), `norm_det` and
  `radius_det` give `sd_x f(Mφ) ≥ γ √𝒩(f)`; Markov on the error (`errE`, `errT`, `kept_exists`) closes.
* `cost_main`: `gProgL_eval`, `gProgL_cost`, `gProgL_heights`, `inline_consts`, `alloc_le`, `budget_le`.

Do not use `native_decide` anywhere.
-/

namespace BstLean.Part41

open MeasureTheory ProbabilityTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD rhoD)

variable {n d : ℕ}

/-- Markov's inequality in the form used here. -/
theorem markov_lt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Integrable f P) (h0 : ∀ ω, 0 ≤ f ω) (c : ℝ) (hc : 0 < c) :
    P {ω | c < f ω} ≤ ENNReal.ofReal ((∫ ω, f ω ∂P) / c) := by
  have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall h0) hf c
  have hsub : {ω | c < f ω} ⊆ {ω | c ≤ f ω} := Set.ofPred_subset_ofPred.mpr fun ω h => h.le
  calc P {ω | c < f ω} ≤ P {ω | c ≤ f ω} := measure_mono hsub
    _ = ENNReal.ofReal ((P {ω | c ≤ f ω}).toReal) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := by
      have h' : c * (P {ω | c ≤ f ω}).toReal ≤ ∫ ω, f ω ∂P := h
      exact ENNReal.ofReal_le_ofReal (by rw [le_div_iff₀ hc]; linarith)

theorem varU_nonneg (μ : Measure (Fin n → ℝ)) (h : (Fin n → ℝ) → ℝ) : 0 ≤ varU μ h :=
  integral_nonneg fun _ => sq_nonneg _

theorem frob_nonneg' {ι : Type*} [Fintype ι] {j : ℕ} (A : (Fin j → ι) → ℝ) : 0 ≤ frob A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem piN_nonneg (k : ℕ) (th : ℝ) : 0 ≤ piN n d k th := by
  unfold piN qN
  have h9 : (0 : ℝ) ≤ 9 ^ k - 1 := by have := one_le_pow₀ (M₀ := ℝ) (a := 9) (by norm_num) (n := k); linarith
  have hq : (0 : ℝ) ≤ ∑ i ∈ Finset.Icc d (k * d), ((k * d).choose i : ℝ) * ((n - k * d).choose (k * d - i) : ℝ) /
      (n.choose (k * d) : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  exact div_nonneg (mul_nonneg h9 hq) (add_nonneg (mul_nonneg h9 hq) (sq_nonneg _))

/-- **Lemma `LF-ball`**: `Pr{Var_x 𝒫 < (√ϑ − √(h_n/β_H))² (μ_n/K_c) 𝒩(f)} ≤ π_n(ϑ) + β_H`. -/
theorem floor_event (hn : 1 ≤ n) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hkd : k * d ≤ n) (T : Tens n)
    (hT : TSymm k T) (q : Params) (hbH : 0 < q.betaH) (hth0 : 0 < q.th) (hth1 : q.th < 1)
    (heta : 0 < q.eta) (hθ : (1 + 1 / q.eta) * thetaT n d k < 1) (hmu : 0 < muN n d k)
    (hKc : 0 < Kc n d k q.eta) (hh : 0 < hN n d k q.eta)
    (hsq : Real.sqrt (hN n d k q.eta / q.betaH) < Real.sqrt q.th) :
    stdGauss (CoefIdxD n d) {Z | varU (uniformSphere n) (Pcal k T Z) <
      (Real.sqrt q.th - Real.sqrt (hN n d k q.eta / q.betaH)) ^ 2 * (muN n d k / Kc n d k q.eta) * Nn n d k T} ≤
      ENNReal.ofReal (piN n d k q.th + q.betaH) := by
  obtain ⟨E, hEdef⟩ : ∃ E, E = ∫ Z, Palpha k T Z ∂stdGauss (CoefIdxD n d) := ⟨_, rfl⟩
  set Sb := ∑ s ∈ Finset.Icc 1 k, (s.factorial : ℝ) * s * frob (bEff n d k T s) / (n : ℝ) ^ (k - s)
  set den := 1 - (1 + 1 / q.eta) * thetaT n d k with hden
  set c := Real.sqrt q.th - Real.sqrt (hN n d k q.eta / q.betaH) with hc
  have hden0 : 0 < den := by rw [hden]; linarith
  have hc0 : 0 < c := by rw [hc]; linarith
  obtain ⟨hPint, hEP⟩ := EP_lower hn hd k hk hkd T hT
  rw [← hEdef] at hEP
  obtain ⟨hHint, hEH⟩ := contam hn hd k hk hkd T hT
  have hsd : ∀ s ∈ Finset.Icc 1 k, s * d ≤ n := fun s hs =>
    le_trans (Nat.mul_le_mul_right d (Finset.mem_Icc.mp hs).2) hkd
  obtain ⟨hct, hcN⟩ := cascade hn k T q.eta heta hθ (fun s hs => (nu_bounds hn s 0 (hsd s hs)).1)
    (fun s hs l _ _ => (nu_bounds hn s l (hsd s hs)).2)
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun s _ => by
    have := frob_nonneg' (bEff n d k T s); positivity
  have hSbE : Sb ≤ E / muN n d k := by rw [le_div_iff₀ hmu]; linarith
  have hNnSb : muN n d k / Kc n d k q.eta * Nn n d k T ≤ E := by
    have h1 : Nn n d k T / Kc n d k q.eta ≤ Sb := by rw [div_le_iff₀ hKc]; linarith
    calc muN n d k / Kc n d k q.eta * Nn n d k T = muN n d k * (Nn n d k T / Kc n d k q.eta) := by ring
      _ ≤ muN n d k * Sb := mul_le_mul_of_nonneg_left h1 hmu.le
      _ ≤ E := by linarith
  have hXi : 0 ≤ XiC n d k := by
    have : 0 < hN n d k q.eta := hh
    unfold hN at this
    have hpos : 0 < (n : ℝ) * muN n d k * den := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    have := (div_pos_iff.mp this)
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · nlinarith
    · rw [← hden] at h2; linarith
  have htj : ∑ j ∈ Finset.Icc 1 k, tj n d k T j ≤ (1 + q.eta) / den * (E / muN n d k) :=
    hct.trans (mul_le_mul_of_nonneg_left hSbE (div_nonneg (by linarith) hden0.le))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hEHle : ∫ Z, Halpha k T Z ∂stdGauss (CoefIdxD n d) ≤ hN n d k q.eta * E := by
    calc ∫ Z, Halpha k T Z ∂stdGauss (CoefIdxD n d) ≤ XiC n d k / n * ∑ j ∈ Finset.Icc 1 k, tj n d k T j := hEH
      _ ≤ XiC n d k / n * ((1 + q.eta) / den * (E / muN n d k)) :=
          mul_le_mul_of_nonneg_left htj (div_nonneg hXi hnpos.le)
      _ = hN n d k q.eta * E := by unfold hN; rw [← hden]; field_simp
  by_cases hE : E ≤ 0
  · -- the bound is `≤ 0`, so the event is empty
    have hb : c ^ 2 * (muN n d k / Kc n d k q.eta) * Nn n d k T ≤ 0 := by
      have := mul_le_mul_of_nonneg_left (hNnSb.trans hE) (sq_nonneg c)
      nlinarith
    have hempty : {Z : CoefIdxD n d → ℝ | varU (uniformSphere n) (Pcal k T Z) < c ^ 2 * (muN n d k / Kc n d k q.eta) * Nn n d k T} = ∅ := by
      ext Z; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hb.trans (varU_nonneg _ _)
    rw [hempty, measure_empty]; exact bot_le
  · push Not at hE
    obtain ⟨c', hc'⟩ : ∃ c', c' = hN n d k q.eta * E / q.betaH := ⟨_, rfl⟩
    have hc'0 : 0 < c' := by rw [hc']; positivity
    have hsub : {Z : CoefIdxD n d → ℝ | varU (uniformSphere n) (Pcal k T Z) < c ^ 2 * (muN n d k / Kc n d k q.eta) * Nn n d k T} ⊆
        {Z : CoefIdxD n d → ℝ | Palpha k T Z < q.th * E} ∪ {Z | c' < Halpha k T Z} := by
      intro Z hZ
      simp only [Set.mem_ofPred_eq] at hZ
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon
      obtain ⟨h1, h2⟩ := hcon
      have hs1 : Real.sqrt q.th * Real.sqrt E ≤ Real.sqrt (Palpha k T Z) := by
        rw [← Real.sqrt_mul hth0.le]; exact Real.sqrt_le_sqrt h1
      have hs2 : Real.sqrt (Halpha k T Z) ≤ Real.sqrt (hN n d k q.eta / q.betaH) * Real.sqrt E := by
        rw [← Real.sqrt_mul (div_nonneg hh.le hbH.le)]
        apply Real.sqrt_le_sqrt; rw [div_mul_eq_mul_div]; rw [hc'] at h2; exact h2
      have hge : c * Real.sqrt E ≤ max (Real.sqrt (Palpha k T Z) - Real.sqrt (Halpha k T Z)) 0 := by
        rw [hc]; refine le_max_of_le_left ?_; nlinarith
      have hsqE : 0 ≤ Real.sqrt E := Real.sqrt_nonneg _
      have hcE : c ^ 2 * E ≤ max (Real.sqrt (Palpha k T Z) - Real.sqrt (Halpha k T Z)) 0 ^ 2 := by
        have h3 : (c * Real.sqrt E) ^ 2 = c ^ 2 * E := by rw [mul_pow, Real.sq_sqrt hE.le]
        rw [← h3]; exact pow_le_pow_left₀ (mul_nonneg hc0.le hsqE) hge 2
      have := LF_i hn hd k T Z
      have h4 : c ^ 2 * (muN n d k / Kc n d k q.eta * Nn n d k T) ≤ c ^ 2 * E :=
        mul_le_mul_of_nonneg_left hNnSb (sq_nonneg c)
      nlinarith
    calc stdGauss (CoefIdxD n d) _ ≤ stdGauss (CoefIdxD n d) ({Z | Palpha k T Z < q.th * E} ∪ {Z | c' < Halpha k T Z}) := measure_mono hsub
      _ ≤ stdGauss (CoefIdxD n d) {Z | Palpha k T Z < q.th * E} + stdGauss (CoefIdxD n d) {Z | c' < Halpha k T Z} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (piN n d k q.th) + ENNReal.ofReal q.betaH := by
          gcongr
          · have := pball hn hd k hk hkd T hT q.th hth0 hth1; rw [← hEdef] at this; exact this
          · refine (markov_lt (stdGauss (CoefIdxD n d)) (Halpha k T) hHint (fun Z => ?_) c' hc'0).trans
              (ENNReal.ofReal_le_ofReal ?_)
            · unfold Halpha; exact Finset.sum_nonneg fun s _ => div_nonneg
                (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
            · have hb' : q.betaH * c' = hN n d k q.eta * E := by
                rw [hc', mul_comm, div_mul_cancel₀ _ hbH.ne']
              exact (div_le_iff₀ hc'0).mpr (by rw [hb']; exact hEHle)
      _ = ENNReal.ofReal (piN n d k q.th + q.betaH) := (ENNReal.ofReal_add (piN_nonneg k _) hbH.le).symm

/-- The kept sets of the program satisfy `KeepOK` at every level. -/
theorem keepSet_ok (hn : 1 ≤ n) (hd : 1 ≤ d) (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hτ : 0 < tauF n d k) :
    ∀ jl ∈ levels k, KeepOK n d k ε jl.1 jl.2 (keepSet n d k ε jl.1 jl.2) := fun jl hjl =>
  Classical.epsilon_spec (kept_exists hn hd k ε hε hτ jl.1 jl.2 hjl)

/-- **The failure bound** of Theorem TC-LF: `Pr{fail} ≤ Φ_LF(n)` under `BudgetOK`. -/
theorem fail_bound (k : ℕ) (hk : 2 ≤ k) (q : Params) (hB : BudgetOK n d k q) (f0 : ℝ) (T : Tens n)
    (hT : TSymm k T) (hTk : 0 < frob (T k)) (ε : ℝ) (hε : 0 < ε) :
    stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧ ε ^ 2 * varF k f0 T (unitOfD Z) <
      (Bof k f0 T (unitOfD Z) - gOf41 k ε f0 T (unitOfD Z)) ^ 2} ≤ ENNReal.ofReal (PhiLF n d k q) := by
  obtain ⟨hn2, hd, hkd, hτ, hx, hβ, hbH, hth0, hth1, heta, hθ, hηr, hmu, hKc, hh, hsq, hγ, _, _, hΦ⟩ := hB
  have hn : 1 ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  have hNn : 0 < Nn n d k T := Nn_pos hn k hk1 T hTk
  set γ := gam41 n d k q with hγdef
  set cc := Real.sqrt q.th - Real.sqrt (hN n d k q.eta / q.betaH) with hcc
  -- the four events
  set E1 := {Z : CoefIdxD n d → ℝ | etaR n d q.x < |r2 Z / DD n d - 1|}
  set E2 := {Z : CoefIdxD n d → ℝ | varU (uniformSphere n) (Pcal k T Z) <
      cc ^ 2 * (muN n d k / Kc n d k q.eta) * Nn n d k T}
  set E3 := {Z : CoefIdxD n d → ℝ | Real.sqrt (GamP n d k * Nn n d k T / q.beta) < upperSum k T Z}
  set t := ε ^ 2 * γ ^ 2 * Nn n d k T with ht
  have ht0 : 0 < t := by positivity
  set E4 := {Z : CoefIdxD n d → ℝ | t < (Bof k f0 T (unitOfD Z) - gOf41 k ε f0 T (unitOfD Z)) ^ 2}
  have hsub : {Z : CoefIdxD n d → ℝ | Z ≠ 0 ∧ ε ^ 2 * varF k f0 T (unitOfD Z) <
      (Bof k f0 T (unitOfD Z) - gOf41 k ε f0 T (unitOfD Z)) ^ 2} ⊆ E1 ∪ E2 ∪ E3 ∪ E4 := by
    intro Z ⟨hZ0, hZf⟩
    by_contra hcon
    simp only [E1, E2, E3, E4, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcon
    -- `sd_x f(Mφ) ≥ γ √𝒩`
    have hnd := norm_det (d := d) hn k f0 T Z hZ0
    have hrad : ∀ j ∈ Finset.Icc 1 k, |rhoZ Z ^ j - 1| ≤ etaK n d k q.x := fun j hj =>
      radius_det hn k q.x hx hηr Z h1 j (Finset.mem_Icc.mp hj).2
    have hek : 0 ≤ etaK n d k q.x := by
      have := radius_det hn k q.x hx hηr Z h1 0 (Nat.zero_le _); simpa using this
    have hsum : ∑ j ∈ Finset.Icc 1 k, |rhoZ Z ^ j - 1| *
        (sdU (uniformSphere n) (uJ T j Z) / Real.sqrt (DD n d) ^ j) ≤ etaK n d k q.x * upperSum k T Z := by
      unfold upperSum; rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hrad j hj)
        (div_nonneg (Real.sqrt_nonneg _) (by positivity))
    have hsdP : cc * Real.sqrt (muN n d k / Kc n d k q.eta) * Real.sqrt (Nn n d k T) ≤
        sdU (uniformSphere n) (Pcal k T Z) := by
      unfold sdU
      have hcc0 : 0 ≤ cc := by rw [hcc]; linarith
      calc cc * Real.sqrt (muN n d k / Kc n d k q.eta) * Real.sqrt (Nn n d k T) =
          Real.sqrt (cc ^ 2 * (muN n d k / Kc n d k q.eta) * Nn n d k T) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hcc0]
        _ ≤ _ := Real.sqrt_le_sqrt h2
    have hup : etaK n d k q.x * upperSum k T Z ≤
        etaK n d k q.x * (Real.sqrt (GamP n d k / q.beta) * Real.sqrt (Nn n d k T)) := by
      apply mul_le_mul_of_nonneg_left _ hek
      have heq : Real.sqrt (GamP n d k * Nn n d k T / q.beta) =
          Real.sqrt (GamP n d k / q.beta) * Real.sqrt (Nn n d k T) := by
        rw [← Real.sqrt_mul' _ hNn.le]; congr 1; ring
      rw [← heq]; exact h3
    have hsdf : γ * Real.sqrt (Nn n d k T) ≤ Real.sqrt (varF k f0 T (unitOfD Z)) := by
      rw [hγdef]; unfold gam41; rw [← hcc]; nlinarith
    have hvar : γ ^ 2 * Nn n d k T ≤ varF k f0 T (unitOfD Z) := by
      have h0 : 0 ≤ γ * Real.sqrt (Nn n d k T) := mul_nonneg hγ.le (Real.sqrt_nonneg _)
      have := pow_le_pow_left₀ h0 hsdf 2
      rwa [mul_pow, Real.sq_sqrt hNn.le, Real.sq_sqrt (by unfold varF; exact varU_nonneg _ _)] at this
    have : t ≤ ε ^ 2 * varF k f0 T (unitOfD Z) := by
      rw [ht, mul_assoc]; exact mul_le_mul_of_nonneg_left hvar (sq_nonneg ε)
    linarith
  -- the error term
  have hKOK := keepSet_ok hn hd k ε hε hτ
  obtain ⟨hEint, hEle⟩ := errE hn hd k (keepSet n d k ε) f0 T hT
  have hT2 := errT hn k (keepSet n d k ε) T ε hτ.le (fun jl hjl => (hKOK jl hjl).2.2)
  have herr : stdGauss (CoefIdxD n d) E4 ≤ ENNReal.ofReal (Lk k * tauF n d k / γ ^ 2) := by
    refine (markov_lt _ _ hEint (fun Z => sq_nonneg _) t ht0).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_div_iff₀ ht0 (by positivity)]
    have hes : epsS ε ≤ ε ^ 2 := min_le_left _ _
    have h1 : (∫ Z, (Bof k f0 T (unitOfD Z) - gOf41 k ε f0 T (unitOfD Z)) ^ 2 ∂stdGauss (CoefIdxD n d)) ≤
        Lk k * tauF n d k * epsS ε * Nn n d k T := hEle.trans hT2
    have hL : (0 : ℝ) ≤ Lk k * tauF n d k := by positivity
    have h2 : Lk k * tauF n d k * epsS ε * Nn n d k T ≤ Lk k * tauF n d k * ε ^ 2 * Nn n d k T := by
      have := mul_le_mul_of_nonneg_left hes hL
      exact mul_le_mul_of_nonneg_right this hNn.le
    have h3 : (∫ Z, (Bof k f0 T (unitOfD Z) - gOf41 k ε f0 T (unitOfD Z)) ^ 2 ∂stdGauss (CoefIdxD n d)) * γ ^ 2 ≤
        Lk k * tauF n d k * ε ^ 2 * Nn n d k T * γ ^ 2 :=
      mul_le_mul_of_nonneg_right (h1.trans h2) (sq_nonneg _)
    calc _ ≤ Lk k * tauF n d k * ε ^ 2 * Nn n d k T * γ ^ 2 := h3
      _ = Lk k * tauF n d k * t := by rw [ht]; ring
  have hm1 : stdGauss (CoefIdxD n d) E1 ≤ ENNReal.ofReal (2 * Real.exp (-q.x)) := radius_event hn q.x hx
  have hm2 : stdGauss (CoefIdxD n d) E2 ≤ ENNReal.ofReal (piN n d k q.th + q.betaH) :=
    floor_event hn hd k hk1 hkd T hT q hbH hth0 hth1 heta hθ hmu hKc hh hsq
  have hm3 : stdGauss (CoefIdxD n d) E3 ≤ ENNReal.ofReal q.beta := upper_event hn hd k T hT q.beta hβ
  calc stdGauss (CoefIdxD n d) _ ≤ stdGauss (CoefIdxD n d) (E1 ∪ E2 ∪ E3 ∪ E4) := measure_mono hsub
    _ ≤ stdGauss (CoefIdxD n d) E1 + stdGauss (CoefIdxD n d) E2 + stdGauss (CoefIdxD n d) E3 +
        stdGauss (CoefIdxD n d) E4 := by
      refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
      refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
      exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * Real.exp (-q.x)) + ENNReal.ofReal (piN n d k q.th + q.betaH) +
        ENNReal.ofReal q.beta + ENNReal.ofReal (Lk k * tauF n d k / γ ^ 2) := by gcongr
    _ = ENNReal.ofReal (PhiLF n d k q) := by
      have hp := piN_nonneg (n := n) (d := d) k q.th
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) hβ.le,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      unfold PhiLF; congr 1; rw [← hγdef]; ring

theorem Corb_nonneg (hn : 2 ≤ n) (a : ℕ) : 0 ≤ Corb n a := by
  unfold Corb
  split_ifs
  · exact le_rfl
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ a := one_le_pow₀ (by linarith)
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)

theorem cS_nonneg (hn : 2 ≤ n) (s : ℕ) : 0 ≤ cS n s := by
  unfold cS
  have h2 : (0 : ℝ) ≤ n := by positivity
  exact add_nonneg h2 (Finset.sum_nonneg fun i _ =>
    mul_nonneg (by positivity) (by linarith [Corb_nonneg hn (s - 2 * i)]))

/-- **The costed program** of Theorem TC-LF: it uses only the constants `0` and `1`, computes the
branch for every symmetric input, and costs less than `max(2P, 0.91 P/ε²)`. -/
theorem cost_main (k : ℕ) (hk : 2 ≤ k) (q : Params) (hB : BudgetOK n d k q) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Prog (In41 n d k) Unit, heavyCount p = 0 ∧
      (∀ v, TSymm k (Tv v) → p.eval v () = gOf41 k ε (f0v v) (Tv v) (Mv v)) ∧
      (p.cost : ℝ) < baseline n d ε := by
  obtain ⟨hn2, hd, hkd, hτ, -, -, -, -, -, -, -, -, -, -, -, -, -, hP, hbQ, -⟩ := hB
  have hn : 1 ≤ n := by omega
  have hKOK := keepSet_ok hn hd k ε hε hτ
  have hK : ∀ jl ∈ levels k, ∀ o ∈ keepSet n d k ε jl.1 jl.2, Multiset.card o = jl.1 - 2 * jl.2 :=
    fun jl hjl => (hKOK jl hjl).2.1
  obtain ⟨p', hp'0, hp'e, hp'c⟩ := inline_consts (gProg n d k ε) (bQ n d k)
    (gProgL_heights hn hd k (by omega) (keepSet n d k ε) hK)
  refine ⟨p', hp'0, fun v hv => ?_, ?_⟩
  · rw [hp'e]; exact gProgL_eval hn k (keepSet n d k ε) hK v hv
  · have hc1 : (p'.cost : ℝ) ≤ chargedCost n (gProg n d k ε) := by
      have : p'.cost ≤ chargedCost n (gProg n d k ε) := by
        unfold chargedCost
        calc p'.cost ≤ (gProg n d k ε).cost + 4 * bQ n d k * heavyCount (gProg n d k ε) := hp'c
          _ ≤ _ := by gcongr
      exact_mod_cast this
    have hc2 := gProgL_cost hn2 k (keepSet n d k ε) hK
    have hc3 : ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) * ((keepSet n d k ε jl.1 jl.2).card : ℝ) ≤
        ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) * (Ocnt n d k ε jl.1 jl.2 : ℝ) :=
      Finset.sum_le_sum fun jl hjl => mul_le_mul_of_nonneg_left (by exact_mod_cast (hKOK jl hjl).1)
        (cS_nonneg hn2 _)
    have hc4 := alloc_le hn2 k ε hε hτ
    have hc5 := budget_le (n := n) (d := d) k ε hε hP
    have hk3 : (0 : ℝ) ≤ (k : ℝ) ^ 3 * (n + 5) := by positivity
    have hB' : Bfix n k = 1 + ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) +
        ∑ j ∈ Finset.Icc 1 k, ∑ m ∈ Finset.Icc 1 (j / 2), (n : ℝ) ^ (j - 2 * m) * ((n : ℝ) ^ m - 1) +
        (k : ℝ) ^ 3 * (n + 5) + k * (n + 3) := rfl
    have hgp : gProg n d k ε = gProgL n d k (keepSet n d k ε) := rfl
    rw [hgp] at hc1
    linarith

end BstLean.Part41
