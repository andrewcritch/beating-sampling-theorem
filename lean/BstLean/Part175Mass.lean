import BstLean.Part174All

/-!
# Part 175 (file `Mass`): the World window `θ_in ≤ 0.528` and the floor mass at `n ≥ 50 000`

No proof is left open; no `native_decide` or `axiom` is used.

The Lean chain of Parts 160–174 uses the window `0.46 ≤ θ_in ≤ 0.55` (`winC`, `WINDOW_hyp`).
Part 159 proves the sharper window `0.465 ≤ θ_in ≤ 0.528` on `HP n ∩ E_{θ−} ∩ E_{θ+}`
(`theta_window_paper'`), and these events are part of every good set (`goodA`).

* **`win528_goodA`**: on `goodA`, `τ₀ > 0` and `0.465 ≤ θ_in ≤ 0.528`.
* `goodA_mono`, `goodC_mono`: the good sets are monotone in the caller event.
* **`W20_le_528`**: `W₂₀ ≤ (1.0615·θ/n)²⁰` for `n ≥ 50 000` and `0.46 ≤ θ ≤ 0.528`
  (Part 165's `W20_le_theta`: `1.109`, at `ε = 0.05`; here `ε = 0.029`).
* `SXM n`: the event `X₂₀ ≤ (1.125·n)²⁰·W₂₀` (Part 160's `SXqN n 20` has `1.157`);
  `jS_200_le_50000` (`jS ≤ 1.0323`); **`SXM_charge`**, `SXM_ret_charge`: charge `≤ 5·10⁻⁵`.
* **`tX20_le_W`**: on `SXM` and in the window `θ ≤ 0.528`, `t_A²⁰·X₂₀ ≤ (0.6306·γ_A/n)²⁰`
  (Part 165's `tX20_le`: `0.706 = 1.157·1.109·0.55`).
* `s0W = 0.5096`, `s0W_cond` (`n ≥ 45 000`), `betaMW n sd = (π/2)⁴⁰·E|g|⁴⁰·(0.6306/(n(s0W − sd)²))²⁰`.
* **`mass_order40W`**, **`mass_of_goodCW`**: Part 174's `mass_order40P`, `mass_of_goodCP` with
  the new constants.
* **`classifier_paper_free23_massW`**: Part 174's `classifier_paper_free23_mass40P` with
  `betaMW`; the caller event is intersected with `agentEv D (SXM n)` (charge `5·10⁻⁵`, so the room
  is `roomC − 5·10⁻⁵`).
-/

namespace BstLean.Part175

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part165
open BstLean.Part161 (muI sigX lamX BIAS_hyp)
open BstLean.Part162 (sgA gmom gmom_nonneg psiA rootFL latMomOfPsi12e eps0 dPaper)
open BstLean.Part153 (XiS Xi4 N2 hid2Mean_cr nuA jS)
open BstLean.Part134 (res sig)
open BstLean.Part164 (goodA window_goodA goodC16_of_goodA hE8_of_good CAn E0 E0_nonneg roomB roomB_ge)

variable {n : ℕ}

/-! ## The window `θ_in ≤ 0.528` on the good set -/

/-- **The window of Part 159 on the good set `goodA`**: `τ₀ > 0` and `0.465 ≤ θ_in ≤ 0.528`. -/
theorem win528_goodA (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    (EA : Set (Ret n)) {c : Ret n} (hc : c ∈ goodA n (paperDesign n fT wT hf hw) EA) :
    0 < (paperDesign n fT wT hf hw).tau0 c ∧
      465 / 1000 ≤ thetaC c.1.2 ((paperDesign n fT wT hf hw).tau0 c) ∧
      thetaC c.1.2 ((paperDesign n fT wT hf hw).tau0 c) ≤ 528 / 1000 := by
  obtain ⟨hτ, -, -, -, h1, h2⟩ := BstLean.Part159.theta_window_paper' hn
    (paperDesign n fT wT hf hw) rfl (fun _ => rfl) hc.1.1
  have e := BstLean.Part160.thetaIn_eq (paperDesign n fT wT hf hw) c
  refine ⟨hτ, ?_, ?_⟩
  · have := h1 hc.2.1.1.1; rw [e] at this; exact this
  · have := h2 hc.2.1.1.2; rw [e] at this; exact this

lemma goodA_mono {D : Design n} {EA EA' : Set (Ret n)} (h : EA ⊆ EA') :
    goodA n D EA ⊆ goodA n D EA' := fun _ hc =>
  ⟨hc.1, ⟨⟨hc.2.1.1, ⟨⟨h hc.2.1.2.1.1, hc.2.1.2.1.2⟩, hc.2.1.2.2⟩⟩, hc.2.2⟩⟩

lemma goodC_mono {D : Design n} {EA EA' : Set (Ret n)} (h : EA ⊆ EA') :
    goodC n D EA ⊆ goodC n D EA' :=
  goodA_mono (Set.inter_subset_inter_left _ h)

/-! ## The radius moment `W₂₀` in the window `θ ≤ 0.528` -/

/-- **`E[(τ²/|y|²)²⁰] ≤ (1.0615·θ/n)²⁰`** for `n ≥ 50 000`, `0.46 ≤ θ ≤ 0.528`. -/
theorem W20_le_528 (hn : 50000 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000) :
    WqN 20 c τ ≤ (10615 / 10000 * (thetaC c τ / n)) ^ 20 := by
  have hnR : (50000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := WqN_le (q := 20) (by omega) c hτ (ε := 29 / 1000) (by norm_num) (by norm_num)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = τ ^ 2 := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = normSq c + (n : ℝ) * τ ^ 2 := ⟨_, rfl⟩
  have hR0 : 0 < R := by
    have := normSq_nonneg c
    rw [hR]; nlinarith [sq_pos_of_pos hτ]
  have hθ : thetaC c τ = (n : ℝ) * T / R := by
    unfold thetaC rhoC
    rw [Real.sq_sqrt (by rw [← hR]; exact hR0.le), ← hR, ← hT]
  rw [hθ] at hθ0 hθ1 ⊢
  rw [le_div_iff₀ hR0] at hθ0
  rw [div_le_iff₀ hR0] at hθ1
  rw [← hT, show normSq c + (n : ℝ) * T - T = R - T by rw [hR, hT]] at h
  have hT23 : 50000 * T ≤ 528 / 1000 * R := by nlinarith
  have hQ0 : 0 < R - T := by nlinarith
  have e : (n : ℝ) * T / R / n = T / R := by field_simp
  rw [e]
  have hTR0 : 0 ≤ T / R := by positivity
  -- the first term
  have h1 : T / ((1 - 29 / 1000) ^ 2 * (R - T)) ≤ 10607 / 10000 * (T / R) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hR0]
    have : R ≤ 10607 / 10000 * ((1 - 29 / 1000) ^ 2 * (R - T)) := by nlinarith
    calc T * R ≤ T * (10607 / 10000 * ((1 - 29 / 1000) ^ 2 * (R - T))) :=
          mul_le_mul_of_nonneg_left this hT0.le
      _ = 10607 / 10000 * T * ((1 - 29 / 1000) ^ 2 * (R - T)) := by ring
  have h1' := pow_le_pow_left₀ (by positivity) h1 20
  -- the second term
  have hexp : exp (-((29 / 1000 : ℝ) ^ 2 * (R - T)) / (2 * T)) ≤ exp (-13) ^ 3 := by
    rw [← Real.exp_nat_mul]
    apply exp_le_exp.mpr
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  have hE4 : exp (-13) ^ 3 ≤ ((1504 / 10 ^ 6 : ℝ) ^ 3) ^ 2 := by
    have := pow_le_pow_left₀ (exp_pos _).le exp_neg_13_le 3
    calc exp (-13) ^ 3 ≤ ((1504 / 10 ^ 6 : ℝ) ^ 2) ^ 3 := this
      _ = ((1504 / 10 ^ 6 : ℝ) ^ 3) ^ 2 := by ring
  have hsq : √(exp (-((29 / 1000 : ℝ) ^ 2 * (R - T)) / (2 * T))) ≤ (1504 / 10 ^ 6 : ℝ) ^ 3 := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ (1504 / 10 ^ 6) ^ 3 by norm_num)]
    exact Real.sqrt_le_sqrt (hexp.trans hE4)
  have hd0 : (0 : ℝ) < (n : ℝ) - 1 - 4 * (20 : ℕ) := by push_cast; linarith
  have hTR : 46 / 100 / (n : ℝ) ≤ T / R := by
    rw [div_le_div_iff₀ hn0 hR0]
    linarith
  have hinv : ((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹ ≤ 219 / 100 * (T / R) := by
    have h4 : ((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹ ≤ 219 / 100 * (46 / 100 / (n : ℝ)) := by
      rw [inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hd0 hn0]
      push_cast
      nlinarith
    exact h4.trans (mul_le_mul_of_nonneg_left hTR (by norm_num))
  have h2' := pow_le_pow_left₀ (inv_nonneg.mpr hd0.le) hinv 20
  have h2 : √(exp (-((29 / 1000 : ℝ) ^ 2 * (R - T)) / (2 * T))) *
      (((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹) ^ 20 ≤
      (1504 / 10 ^ 6 : ℝ) ^ 3 * (219 / 100 * (T / R)) ^ 20 :=
    mul_le_mul hsq h2' (by positivity) (by norm_num)
  have hfin : (10607 / 10000 * (T / R)) ^ 20 + (1504 / 10 ^ 6 : ℝ) ^ 3 * (219 / 100 * (T / R)) ^ 20 ≤
      (10615 / 10000 * (T / R)) ^ 20 := by
    have e2 : (10615 / 10000 * (T / R)) ^ 20 - ((10607 / 10000 * (T / R)) ^ 20 +
        (1504 / 10 ^ 6 : ℝ) ^ 3 * (219 / 100 * (T / R)) ^ 20) =
        ((10615 / 10000 : ℝ) ^ 20 - (10607 / 10000) ^ 20 - (1504 / 10 ^ 6) ^ 3 * (219 / 100) ^ 20) *
          (T / R) ^ 20 := by ring
    have : 0 ≤ ((10615 / 10000 : ℝ) ^ 20 - (10607 / 10000) ^ 20 - (1504 / 10 ^ 6) ^ 3 *
          (219 / 100) ^ 20) * (T / R) ^ 20 := mul_nonneg (by norm_num) (by positivity)
    linarith
  push_cast at h h2
  linarith

/-! ## The event `SXM` with the sharper Lemma PP constant -/

/-- **The event of the gradient moment of order 40 with `M = 1.125`**: `X₂₀ ≤ (1.125·n)²⁰·W₂₀`. -/
def SXM (n : ℕ) : Set (AgFam n) :=
  {x | XqN 20 x.2.1 x.2.2 x.1.1 x.1.2 ≤ (1125 / 1000 * (n : ℝ)) ^ 20 * WqN 20 x.1.1 x.1.2}

theorem measurableSet_SXM (n : ℕ) : MeasurableSet (SXM n) :=
  measurableSet_le (measurable_XqN_fam 20) ((measurable_WqN_fam 20).const_mul _)

/-- `jS n 200 (6/1000) ≤ 1.0323` for `n ≥ 50 000`. -/
lemma jS_200_le_50000 (hn : 50000 ≤ n) : jS n 200 (6 / 1000) ≤ 10323 / 10000 := by
  have hnr : (50000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : (2236 / 10 : ℝ) ≤ √(n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hg0 := BstLean.Part152.gaussMomConst_nonneg 200
  have hg := BstLean.Part153.gaussMomConst_200_le
  have hu : 1 / √(n : ℝ) ≤ 1 / (2236 / 10) := one_div_le_one_div_of_le (by norm_num) hs
  have hw : BstLean.Part152.gaussMomConst 200 / (n : ℝ) ≤ (25 / 2) / 50000 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith
  have hgu : BstLean.Part152.gaussMomConst 200 / √(n : ℝ) ≤ (25 / 2) / (2236 / 10) := by
    rw [div_le_div_iff₀ hs0 (by norm_num)]
    nlinarith
  refine (BstLean.Part153.jS_le_atoms n 200 (6 / 1000) BstLean.Part153.sqrt_two_le
    BstLean.Part153.sqrt_eta_le hu hw hgu (BstLean.Part153.epsS_200_le (by omega))).trans ?_
  norm_num

/-- **The charge of `SXM n`**: at most `5·10⁻⁵` (`n ≥ 50 000`, `τ > 0`; Markov over the weights
at order `400`, as in Part 165's `SX20_charge`). -/
theorem SXM_charge (hn : 50000 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXM n} ≤ 5 / 100000 := by
  have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ((c, τ), θ) ∉ SXM n} =
      {θ | (1125 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ < XqN 20 θ.1 θ.2 c τ} := by
    ext θ
    change ¬ (XqN 20 θ.1 θ.2 c τ ≤ (1125 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ) ↔ _
    exact not_le
  rw [e]
  have h := markov_XqN (n := n) (q := 20) (P' := 10) (by norm_num) (by omega) c hτ
    (BstLean.Part153.jS_nonneg n 200 (6 / 1000))
    (fun _ hx => by
      exact BstLean.Part153.lemmaPP_i_sharp (by omega) (by norm_num)
        (by norm_num : (0 : ℝ) ≤ 6 / 1000) hx) (M := 1125 / 1000) (by norm_num)
  refine h.trans ?_
  have hj0 := BstLean.Part153.jS_nonneg n 200 (6 / 1000)
  have hj := jS_200_le_50000 hn
  have hj2 : jS n 200 (6 / 1000) ^ 2 ≤ (10323 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hratio : jS n 200 (6 / 1000) ^ 2 / (1125 / 1000) ≤ 951 / 1000 := by
    rw [div_le_iff₀ (by norm_num)]
    refine hj2.trans (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) hratio 200).trans BstLean.Part153.pow_951_le

theorem SXM_ret_charge (hn : 50000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (SXM n))ᶜ ≤
      5 / 100000 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_SXM n) (by norm_num) (fun c τ hτ => SXM_charge hn c τ hτ)

/-- **The gradient moment of order 40 on `SXM` in the window `θ ≤ 0.528`**:
`t_A²⁰·X₂₀ ≤ (0.6306·γ_A/n)²⁰` (`1.125·1.0615·0.528 ≤ 0.6306`), for `n ≥ 50 000`. -/
theorem tX20_le_W (hn : 50000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM n) :
    (2 / (mA n : ℝ)) ^ 20 * XqN 20 A₁ A₂ c τ ≤ (6306 / 10000 * (2 / (n : ℝ)) / n) ^ 20 := by
  have hnR : (50000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have h1 : XqN 20 A₁ A₂ c τ ≤ (1125 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ := h
  have h2 := W20_le_528 hn c hτ hθ0 hθ1
  have hθn : (0 : ℝ) ≤ thetaC c τ := by linarith
  have h3 : XqN 20 A₁ A₂ c τ ≤ (1125 / 1000 * (10615 / 10000) * thetaC c τ) ^ 20 := by
    refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
    rw [← mul_pow]; congr 1; field_simp
  have hB : 1125 / 1000 * (10615 / 10000) * thetaC c τ ≤ 6306 / 10000 := by nlinarith
  have h4 := pow_le_pow_left₀ (by positivity) hB 20
  rw [hmA]
  calc (2 / (n : ℝ) ^ 2) ^ 20 * XqN 20 A₁ A₂ c τ ≤ (2 / (n : ℝ) ^ 2) ^ 20 * (6306 / 10000) ^ 20 :=
        mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
    _ = (6306 / 10000 * (2 / (n : ℝ)) / n) ^ 20 := by rw [← mul_pow]; congr 1; field_simp

/-! ## The floor mass -/

/-- The lower bound of `E σ/√γ_A` used for the floor: `s0W = 0.5096`. -/
noncomputable def s0W : ℝ := 5096 / 10000

/-- **The mass bound of order 40**: `β(n, sd) = (π/2)⁴⁰·E|g|⁴⁰·(0.6306/(n(s0W − sd)²))²⁰`. -/
noncomputable def betaMW (n : ℕ) (sd : ℝ) : ℝ :=
  (π / 2) ^ 40 * gmom 40 * (6306 / 10000 / ((n : ℝ) * (s0W - sd) ^ 2)) ^ 20

lemma betaMW_nonneg (n : ℕ) (sd : ℝ) : 0 ≤ betaMW n sd := by
  unfold betaMW
  have := gmom_nonneg 40
  have h : 0 ≤ (6306 / 10000 / ((n : ℝ) * (s0W - sd) ^ 2)) ^ 20 := by
    rw [show (20 : ℕ) = 2 * 10 by norm_num, pow_mul]; positivity
  positivity

/-- The numeric condition on `s0W` (`n ≥ 45 000`). -/
lemma s0W_cond (hn : 45000 ≤ n) :
    s0W ^ 2 ≤ 1 - 18334 / 1000 / (n : ℝ) * (2 + 18334 / 1000 / (n : ℝ)) -
      (8553 / 10000 + 46 / 10000) ^ 2 - 2 * (11911 / 10000) / n := by
  have hnR : (45000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 1 / (n : ℝ) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x ≤ 1 / 45000 := by rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hnR
  have e1 : 18334 / 1000 / (n : ℝ) = 18334 / 1000 * x := by rw [hx]; ring
  have e2 : 2 * (11911 / 10000) / (n : ℝ) = 2 * (11911 / 10000) * x := by rw [hx]; ring
  rw [e1, e2]
  unfold s0W
  nlinarith

/-- **The mass below the floor from the moment of order 40 of `σ`**, for one retained value:
with the quantities of the frame events and the event `SXM n`, in the window `θ ≤ 0.528`,
`∫_a ν{σ < √γ_A·sd} ≤ betaMW n sd` for `0 ≤ sd < s0W`, `n ≥ 23 000`. -/
theorem mass_order40W (hn : 50000 ≤ n) (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c)
    (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c)) (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100)
    (hθ2 : thetaC c.1.2 (D.tau0 c) ≤ 528 / 1000)
    (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hXi : XiS c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ 11911 / 10000 * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) ≤ 2 / (n : ℝ) * (7315 / 10000))
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) -
      D.bA c.1 c.2.1.1) ≤ 485 / 1000 * (2 / (n : ℝ)) / n)
    (hN22 : N2 2 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ 18334 / 1000 / (n : ℝ))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM n)
    {sd : ℝ} (hsd0 : 0 ≤ sd) (hsd : sd < s0W) :
    ∫ a', (stdGauss (Fin (n - 1))).real {v | sgA D c a' v < √(2 / (n : ℝ)) * sd} ∂muI n ≤
      betaMW n sd := by
  have hnR : (50000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hc : c.1.2 ≠ 0 := c_ne_of_theta (by omega) hτ hθ1
  rw [BstLean.Part162.mass_eq_stand (by omega) D c hc hτ]
  -- the tail bound of order 40
  set A₁ := c.2.1.1.1
  set A₂ := c.2.1.1.2
  set b := D.bA c.1 c.2.1.1
  set τ := D.tau0 c
  have hX := tX20_le_W hn hτ hθ0 hθ2 hS
  set K : ℝ := (π / 2) ^ 40 * (gmom 40 * (6306 / 10000 * (2 / (n : ℝ)) / n) ^ 20) with hK
  have hT : ∀ g : ℝ, 0 < g → (stdGauss (Fin n)).real
      {ξ | g ≤ |sigD A₁ A₂ c.1.2 τ b ξ - ∫ ζ, sigD A₁ A₂ c.1.2 τ b ζ ∂stdGauss (Fin n)|} ≤
        K / g ^ 40 := by
    intro g hg
    have h := sigD_tail (q := 20) (by norm_num) (by omega) A₁ A₂ c.1.2 hτ hb hg
    refine h.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    rw [hK]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX (gmom_nonneg _)) (by positivity)
  have hXi' : XiS A₁ A₂ c.1.2 τ ≤ 11911 / 10000 * (2 / (n : ℝ)) / n := hXi
  have hm := mass_bound_gen (by omega) A₁ A₂ c.1.2 hτ hb hXi' heb hxi hN22
    (e1 := 8553 / 10000) (e2 := 46 / 10000) (by norm_num) (by norm_num) (by norm_num)
    (by rw [div_le_iff₀ hn0]; nlinarith) hsd0 hsd (by
      have := s0W_cond (by omega : 45000 ≤ n)
      unfold s0W at this ⊢
      linarith) hT
  have hset : {ξ : Fin n → ℝ | sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) < √(2 / (n : ℝ)) * sd} =
      {ξ | 2 / (mA n : ℝ) * normSq (res (D.bA c.1 c.2.1.1)
        (hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)))) < 2 / (n : ℝ) * sd ^ 2} := by
    ext ξ
    simp only [Set.mem_ofPred_eq]
    set R := normSq (res (D.bA c.1 c.2.1.1) (hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ))))
    have hR : 0 ≤ R := normSq_nonneg _
    have hsig : sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) = √(2 / (mA n : ℝ)) * √R := rfl
    rw [hsig, ← Real.sqrt_mul (by positivity)]
    have e : √(2 / (n : ℝ)) * sd = √(2 / (n : ℝ) * sd ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hsd0]
    rw [e]
    exact Real.sqrt_lt_sqrt_iff (by positivity)
  rw [hset]
  refine hm.trans (le_of_eq ?_)
  -- the value of `K / (√γ_A (s0W − sd))⁴⁰`
  have hd : 0 < s0W - sd := by linarith
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hs40 : (√(2 / (n : ℝ)) * (s0W - sd)) ^ 40 = (2 / (n : ℝ)) ^ 20 * ((s0W - sd) ^ 2) ^ 20 := by
    rw [mul_pow, show (40 : ℕ) = 2 * 20 by norm_num, pow_mul, pow_mul, Real.sq_sqrt hγ.le]
  unfold s0W at hs40 hd ⊢
  rw [hs40, hK]
  unfold betaMW s0W
  field_simp

/-- **The mass below the floor on the good set**: `∫_a ν{σ < √γ_A·sd} ≤ betaMW n sd`. -/
theorem mass_of_goodCW (hn : 50000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodC n (paperDesign n fT wT hf hw) (EA ∩ agentEv (paperDesign n fT wT hf hw) (SXM n)))
    {sd : ℝ} (hsd0 : 0 ≤ sd) (hsd : sd < s0W) :
    ∫ a, (stdGauss (Fin (n - 1))).real
        {v | sgA (paperDesign n fT wT hf hw) c a v < √(2 / (n : ℝ)) * sd} ∂muI n ≤
      betaMW n sd := by
  set D := paperDesign n fT wT hf hw
  have hn16 : 16384 ≤ n := by omega
  obtain ⟨hτ, hθ0, hθ1⟩ := window_goodA hn16 fT wT hf hw _ c hc
  have hG := goodC16_of_goodA hn16 fT wT hf hw hc
  have hSc : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n := hc.2.2.1.1.2 hτ
  have hS20 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM n := hc.2.1.2.1.1.1.2 hτ
  have hθ2 := (win528_goodA hn16 fT wT hf hw _ hc).2.2
  obtain ⟨hxi, -, -, hpos, hX4, hN22, -⟩ := centre16 hn16 hτ hθ0 hθ1 hG
  have heb := eb16_sharp hn16 hτ hθ0 hθ1 hG hSc
  have hb : D.bA c.1 c.2.1.1 =
      (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) :=
    paperDesign_agentCentre fT wT hf hw c
  rw [← hb] at hxi hpos heb
  have hXi := (BstLean.Part153.XiS_le_Xi4 (by omega) c.2.1.1.1 c.2.1.1.2 c.1.2 hτ).trans hX4
  exact mass_order40W hn D c hτ hθ0 hθ1 hθ2 hpos hXi heb hxi hN22 hS20 hsd0 hsd

/-- **The free-event classifier theorem with the sharper floor mass (every `n ≥ 50 000`).**
Part 174's `classifier_paper_free23_mass40P` with `s0W`, `betaMW` and `mass_of_goodCW`. The caller
event `E_A` is intersected with `agentEv D (SXM n)`, whose charge `5·10⁻⁵` is paid here: the room
for `E_A` is `roomC − 5·10⁻⁵`. -/
theorem classifier_paper_free23_massW (hn : 50000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomC - 5 / 100000)
    (hM : ∀ (c : Ret n) (hc : c ∈ goodC n (paperDesign n fT wT hf hw)
        (EA ∩ agentEv (paperDesign n fT wT hf hw) (SXM n))),
      ∃ (wl ws sd η CL CS : ℝ) (h0 : 0 < η) (h1 : η < 1) (hCL : 0 < CL)
        (hCS : 0 < CS) (hsd0 : 0 < sd) (hsd : sd < s0W)
        (hL12 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 12)
        (hS12 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 12),
        0 < wl ∧ 0 < ws ∧ eps0 ws (√(2 / (n : ℝ)) * sd) < 1 ∧
        rootFL wl ws η (CAn n) (latMomOfPsi12e (by omega) (paperDesign n fT wT hf hw) c hCL hCS
          (E0_nonneg n) (betaMW_nonneg n sd) hL12 hS12 (hE8_of_good (by omega) fT wT hf hw hc)
          (mass_of_goodCW hn fT wT hf hw hc hsd0.le hsd)) ≤ 2159 / 10 ^ 6 ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws (√(2 / (n : ℝ)) * sd) η h0 h1)
          (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  set D := paperDesign n fT wT hf hw
  set S := BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
    BstLean.Part159.Ethp (paperCentres n)
  set E1 := EA ∩ agentEv D (SXM n) with hE1
  have hE1m : MeasurableSet E1 := hEA.inter (measurableSet_agentEv D (measurableSet_SXM n))
  have hEA' : MeasurableSet (E1 ∩ agentEv D (SXqN n 20)) :=
    hE1m.inter (measurableSet_agentEv D (measurableSet_SXqN n 20))
  have hA' : (retDist (paperCentres n)).real (S ∩ (E1 ∩ agentEv D (SXqN n 20))ᶜ) ≤
      δA + 5 / 100000 + 5 / 100000 := by
    have hsub : S ∩ (E1 ∩ agentEv D (SXqN n 20))ᶜ ⊆
        ((S ∩ EAᶜ) ∪ (agentEv D (SXM n))ᶜ) ∪ (agentEv D (SXqN n 20))ᶜ := by
      intro c hc
      by_cases h1 : c ∈ EA
      · by_cases h2 : c ∈ agentEv D (SXM n)
        · exact Or.inr fun h3 => hc.2 ⟨⟨h1, h2⟩, h3⟩
        · exact Or.inl (Or.inr h2)
      · exact Or.inl (Or.inl ⟨hc.1, h1⟩)
    refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
    have c1 := SX20_ret_charge (by omega) fT wT hf hw
    have c2 := SXM_ret_charge hn fT wT hf hw
    have c3 := (measureReal_union_le (μ := retDist (paperCentres n)) (S ∩ EAᶜ)
      (agentEv D (SXM n))ᶜ)
    linarith
  have hroom' : δA + 5 / 100000 + 5 / 100000 ≤ roomB := by unfold roomC at hroom; linarith
  refine BstLean.Part164.classifier_paper_free23_cA8 (by omega) fT wT hf hw t hEA' hA' hroom'
    fun c hc => ?_
  obtain ⟨wl, ws, sd, η, CL, CS, h0, h1, hCL, hCS, hsd0, hsd, hL12, hS12, hwl, hws, hε, hroot,
    hbias⟩ := hM c hc
  have hσl : 0 < √(2 / (n : ℝ)) * sd := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  exact ⟨wl, ws, √(2 / (n : ℝ)) * sd, η, CL, CS, betaMW n sd, h0, h1, hCL, hCS, betaMW_nonneg n sd,
    hL12, hS12, mass_of_goodCW hn fT wT hf hw hc hsd0.le hsd, hwl, hws, hσl, hε, hroot, hbias⟩

end BstLean.Part175
