import BstLean.Part140Frame

/-!
# Part 140: the scalar of the stand-in with the computed centre is nearly constant

Role: `delegations/statements/p140-spec.md` (item 3, the scalar `τ̂₀`). Paper sources:
`onW17c-cx.md` §5 (the one-pass scalar; `ℓ₀`, `w₀`, `G_ζ`, `ω₁`, `β₁`), `onW16c-cx.md` §4.

`N` inputs, hidden width `m`, `t = 2/m`, `γ = 2/N`, `θ = (M₁, M₂)`, `b̂ = bhat θ`,
`T̂(u) = t⟨h(u), b̂⟩`, `κ₁ = kap1 N = κ(q₁)` (a constant that depends on `N` only),
`D(u) = t|h(u)|²/γ`.

* `lamH = T̂/(γκ₁)` (the paper's `ℓ/ℓ₀`); `B0 = γκ₁²/(t|b̂|²)` (the paper's `ℓ₀²`);
  `wH = D/(B0·lamH²) − 1` (the paper's `w = D/ℓ² − 1`); `w0H = 1/B0 − 1 = t|b̂|²/(γκ₁²) − 1`
  (the paper's `w₀`: a function of `|b̂|²` and of constants that depend on `N` only).
* **`tauHat N m θ = √(t|b̂|²·max(0, t|b̂|²/(γκ₁²) − 1))`**: the scalar `τ̂₀` of the cheap stand-in
  with the computed centre. It needs `|b̂|²` and the constant `κ₁` only (no exact `h̄`).
* `tauH_sq`: `σ̂(u)²/λ̂(u)² = t|b̂|²·wH(u)` for the centre `b̂` (the `σ`, `λ` of Part 134).
* `lamH_L2`, `tauFluctH_gen`, `tauBadH_gen`: the restricted second moment of `wH − w0H` on a
  hidden event and the good set of inputs `G_ζ = {|D − 1| ≤ ζ, |lamH − 1| ≤ ζ}`, and the
  measure of the bad inputs (from H2(a) and H2(b) of Part 137).
* `B0_window`, `w0H_window`, `tauHat_sq`, `tauHat_pos`: the facts on `goodHat n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part140

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105 (BM sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137

variable {N m : ℕ}

/-! ## Definitions -/

/-- `T̂(u)/(γκ₁)`: the paper's `ℓ(u)/ℓ₀`. -/
noncomputable def lamH (N m : ℕ) (u : Fin N → ℝ) (θ : HidParam N m) : ℝ :=
  That N m u θ / (2 / (N : ℝ) * kap1 N)

/-- `γκ₁²/(t|b̂|²)`: the paper's `ℓ₀²`. -/
noncomputable def B0 (N m : ℕ) (θ : HidParam N m) : ℝ := 2 / (N : ℝ) * kap1 N ^ 2 / Bh N m θ

/-- `ŵ(u) = D(u)/ℓ̂(u)² − 1`, with `ℓ̂(u)² = B0·lamH(u)²`. -/
noncomputable def wH (N m : ℕ) (u : Fin N → ℝ) (θ : HidParam N m) : ℝ :=
  Dn N m u θ / (B0 N m θ * lamH N m u θ ^ 2) - 1

/-- `ŵ₀ = 1/ℓ₀² − 1`. -/
noncomputable def w0H (N m : ℕ) (θ : HidParam N m) : ℝ := 1 / B0 N m θ - 1

/-- The good set of inputs for the computed centre: `|D − 1| ≤ ζ` and `|lamH − 1| ≤ ζ`. -/
def goodUH (N m : ℕ) (ζ : ℝ) : Set ((Fin N → ℝ) × HidParam N m) :=
  {p | |Dn N m p.1 p.2 - 1| ≤ ζ ∧ |lamH N m p.1 p.2 - 1| ≤ ζ}

/-- A hidden event `E` and the good set of inputs together. -/
def goodSH (E : Set (HidParam N m)) (ζ : ℝ) : Set ((Fin N → ℝ) × HidParam N m) :=
  {p | p.2 ∈ E ∧ p ∈ goodUH N m ζ}

/-- **The scalar `τ̂₀` of the cheap stand-in with the computed centre**:
`τ̂₀² = t|b̂|²·max(0, t|b̂|²/(γκ₁²) − 1)`. A function of `|b̂|²` and of `N` only. -/
noncomputable def tauHat (N m : ℕ) (θ : HidParam N m) : ℝ :=
  √(Bh N m θ * max 0 (Bh N m θ / (2 / (N : ℝ) * kap1 N ^ 2) - 1))

lemma w0H_eq (θ : HidParam N m) : w0H N m θ = Bh N m θ / (2 / (N : ℝ) * kap1 N ^ 2) - 1 := by
  unfold w0H B0
  rw [one_div_div]

/-! ## Measurability -/

lemma measurable_lamH (hN : 1 ≤ N) : Measurable (Function.uncurry (lamH N m)) :=
  ((measurable_That hN).div_const _ :)

lemma measurable_B0 (hN : 1 ≤ N) : Measurable (B0 N m) := (measurable_Bh hN).const_div _

lemma measurable_wH (hN : 1 ≤ N) : Measurable (Function.uncurry (wH N m)) := by
  have h1 : Measurable (fun z : (Fin N → ℝ) × HidParam N m => B0 N m z.2) :=
    (measurable_B0 hN).comp measurable_snd
  exact ((continuous_Dn.measurable).div (h1.mul ((measurable_lamH hN).pow_const 2))).sub_const 1

lemma measurable_w0H (hN : 1 ≤ N) : Measurable (w0H N m) :=
  ((measurable_B0 hN).const_div 1).sub_const 1

lemma goodUH_meas (hN : 1 ≤ N) (ζ : ℝ) : MeasurableSet (goodUH N m ζ) := by
  have h1 : Measurable (fun p : (Fin N → ℝ) × HidParam N m => |Dn N m p.1 p.2 - 1|) :=
    (continuous_Dn.measurable.sub_const 1).abs
  have h2 : Measurable (fun p : (Fin N → ℝ) × HidParam N m => |lamH N m p.1 p.2 - 1|) :=
    ((measurable_lamH hN).sub_const 1).abs
  exact (measurableSet_le h1 measurable_const).inter (measurableSet_le h2 measurable_const)

lemma goodSH_meas (hN : 1 ≤ N) {E : Set (HidParam N m)} (hE : MeasurableSet E) (ζ : ℝ) :
    MeasurableSet (goodSH E ζ) :=
  (measurable_snd hE).inter (goodUH_meas hN ζ)

lemma measurable_tauHat (hN : 1 ≤ N) : Measurable (tauHat N m) := by
  unfold tauHat
  exact ((measurable_Bh hN).mul
    (measurable_const.max (((measurable_Bh hN).div_const _).sub_const 1))).sqrt

/-! ## The algebra -/

/-- **The ratio of the two scalars of the stand-in with the centre `b̂`**:
`σ̂(u)²/λ̂(u)² = t|b̂|²·ŵ(u)`. -/
theorem tauH_sq (hN : 1 ≤ N) (hm : 1 ≤ m) (u : Fin N → ℝ) {θ : HidParam N m}
    (hb : normSq (bhat θ) ≠ 0) (hk : kap1 N ≠ 0) (hT : That N m u θ ≠ 0) :
    sig (2 / (m : ℝ)) (bhat θ) (hid2 θ.1 θ.2 u) ^ 2 / lam (bhat θ) (hid2 θ.1 θ.2 u) ^ 2 =
      Bh N m θ * wH N m u θ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have eT : That N m u θ = 2 / (m : ℝ) * dotp (hid2 θ.1 θ.2 u) (bhat θ) := rfl
  have hX : dotp (hid2 θ.1 θ.2 u) (bhat θ) ≠ 0 := by
    intro h0
    apply hT
    rw [eT, h0, mul_zero]
  have hs : sig (2 / (m : ℝ)) (bhat θ) (hid2 θ.1 θ.2 u) ^ 2 =
      2 / (m : ℝ) * (normSq (hid2 θ.1 θ.2 u) -
        dotp (hid2 θ.1 θ.2 u) (bhat θ) ^ 2 / normSq (bhat θ)) := by
    unfold sig
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (normSq_nonneg _), normSq_res hb]
    rfl
  have hl : lam (bhat θ) (hid2 θ.1 θ.2 u) =
      dotp (hid2 θ.1 θ.2 u) (bhat θ) / normSq (bhat θ) := rfl
  rw [hs, hl]
  unfold wH B0 lamH Bh
  rw [Dn_eq, eT]
  field_simp

/-! ## The second moments over the input and `θ` -/

/-- `‖lamH − 1‖_{L²(u, θ)} ≤ cHat2 N m/κ₁`. -/
theorem lamH_L2 (hN : 1 ≤ N) (hm : 1 ≤ m) (hk : 0 < kap1 N) :
    L2le ((uniformSphere N).prod (hidGauss N m))
      (fun p => |lamH N m p.1 p.2 - 1|) (cHat2 N m / kap1 N) := by
  have := uniformSphere_isProbability N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hg : 0 < 2 / (N : ℝ) * kap1 N := by positivity
  have hk1 : kappa (q1 (e0 N)) = kap1 N := rfl
  obtain ⟨h1, h2⟩ := hatFluct2_joint (m := m) hN hm
  rw [hk1] at h1 h2
  have hj : L2le ((uniformSphere N).prod (hidGauss N m))
      (fun p : (Fin N → ℝ) × HidParam N m => That N m p.1 p.2 - 2 / (N : ℝ) * kap1 N)
      (2 / (N : ℝ) * cHat2 N m) :=
    ⟨(((measurable_That hN).sub_const _ :)).aestronglyMeasurable, h1, h2⟩
  have hc := hj.const_mul (1 / (2 / (N : ℝ) * kap1 N))
  rw [abs_of_pos (by positivity)] at hc
  have hmeas : Measurable (fun p : (Fin N → ℝ) × HidParam N m => |lamH N m p.1 p.2 - 1|) :=
    ((measurable_lamH hN).sub_const 1).abs
  refine (L2le.of_abs_le hmeas.aestronglyMeasurable hc fun p => ?_).congr_bound ?_
  · rw [abs_abs]
    refine le_of_eq ?_
    congr 1
    unfold lamH
    field_simp
  · field_simp

/-- **The restricted second moment of `ŵ − ŵ₀`, general form** (`onW17c-cx.md` §5): if
`ℓ₀² ≥ L > 0` on a measurable hidden event `E`, then on `E` and the good set of inputs:
`‖ŵ − ŵ₀‖_{L²(u, θ)} ≤ (√(10/m + 25/m²) + (2 + ζ)·cHat2/κ₁)/(L(1 − ζ)²)`. -/
theorem tauFluctH_gen (hN : 1 ≤ N) (hm : 1 ≤ m) (hk : 0 < kap1 N) {E : Set (HidParam N m)}
    (hE : MeasurableSet E) {L ζ : ℝ} (hL : 0 < L) (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1)
    (hB : ∀ θ ∈ E, L ≤ B0 N m θ) :
    L2le ((uniformSphere N).prod (hidGauss N m))
      ((goodSH E ζ).indicator fun p => wH N m p.1 p.2 - w0H N m p.2)
      (1 / (L * (1 - ζ) ^ 2) *
        (√(10 / (m : ℝ) + 25 / (m : ℝ) ^ 2) + (2 + ζ) * (cHat2 N m / kap1 N))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1ζ : 0 < 1 - ζ := by linarith
  have hc0 : 0 ≤ cHat2 N m / kap1 N := div_nonneg (cHat2_nonneg N m) hk.le
  have hsum := (Dn_L2 (m := m) hN hm).add'
    ((lamH_L2 (m := m) hN hm hk).const_mul_nonneg (by linarith : (0 : ℝ) ≤ 2 + ζ))
    (Real.sqrt_nonneg _) (mul_nonneg (by linarith) hc0)
  have hall := hsum.const_mul_nonneg (c := 1 / (L * (1 - ζ) ^ 2)) (by positivity)
  have hFm : Measurable ((goodSH E ζ).indicator fun p : (Fin N → ℝ) × HidParam N m =>
      wH N m p.1 p.2 - w0H N m p.2) :=
    ((measurable_wH hN).sub ((measurable_w0H hN).comp measurable_snd)).indicator
      (goodSH_meas hN hE ζ)
  refine L2le.of_abs_le hFm.aestronglyMeasurable hall fun p => ?_
  by_cases hp : p ∈ goodSH E ζ
  · obtain ⟨hpE, hpD, hpl⟩ := hp
    have hw := w_diff hL (hB p.2 hpE) hζ1 hpD hpl
    rw [Set.indicator_of_mem (show p ∈ goodSH E ζ from ⟨hpE, hpD, hpl⟩)]
    refine le_trans ?_ (le_abs_self _)
    exact hw
  · rw [Set.indicator_of_notMem hp, abs_zero]
    exact abs_nonneg _

/-- The same as a second moment. -/
theorem tauFluctH_gen_int (hN : 1 ≤ N) (hm : 1 ≤ m) (hk : 0 < kap1 N) {E : Set (HidParam N m)}
    (hE : MeasurableSet E) {L ζ : ℝ} (hL : 0 < L) (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1)
    (hB : ∀ θ ∈ E, L ≤ B0 N m θ) :
    Integrable ((goodSH E ζ).indicator (fun p => (wH N m p.1 p.2 - w0H N m p.2) ^ 2))
        ((uniformSphere N).prod (hidGauss N m)) ∧
    ∫ p, (goodSH E ζ).indicator (fun p => (wH N m p.1 p.2 - w0H N m p.2) ^ 2) p
        ∂((uniformSphere N).prod (hidGauss N m)) ≤
      (1 / (L * (1 - ζ) ^ 2) *
        (√(10 / (m : ℝ) + 25 / (m : ℝ) ^ 2) + (2 + ζ) * (cHat2 N m / kap1 N))) ^ 2 := by
  have h := tauFluctH_gen hN hm hk hE hL hζ0 hζ1 hB
  have e : (goodSH E ζ).indicator (fun p : (Fin N → ℝ) × HidParam N m =>
      (wH N m p.1 p.2 - w0H N m p.2) ^ 2) =
      fun p => ((goodSH E ζ).indicator (fun p : (Fin N → ℝ) × HidParam N m =>
        wH N m p.1 p.2 - w0H N m p.2) p) ^ 2 := by
    funext p
    by_cases hp : p ∈ goodSH E ζ
    · simp [Set.indicator_of_mem hp]
    · simp [Set.indicator_of_notMem hp]
  rw [e]
  exact ⟨h.int_sq, h.le⟩

/-- **The bad inputs** (Chebyshev): `Pr(u ∉ G_ζ) ≤ (10/m + 25/m² + (cHat2/κ₁)²)/ζ²`, over the
input and `θ`. -/
theorem tauBadH_gen (hN : 1 ≤ N) (hm : 1 ≤ m) (hk : 0 < kap1 N) {ζ : ℝ} (hζ : 0 < ζ) :
    ((uniformSphere N).prod (hidGauss N m)).real {p | p ∉ goodUH N m ζ} ≤
      (10 / (m : ℝ) + 25 / (m : ℝ) ^ 2 + (cHat2 N m / kap1 N) ^ 2) / ζ ^ 2 := by
  have := uniformSphere_isProbability N hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := Dn_L2 (m := m) hN hm
  have h2 := lamH_L2 (m := m) hN hm hk
  set g : (Fin N → ℝ) × HidParam N m → ℝ := fun p =>
    |Dn N m p.1 p.2 - 1| ^ 2 + |lamH N m p.1 p.2 - 1| ^ 2 with hg
  have hgi : Integrable g ((uniformSphere N).prod (hidGauss N m)) := h1.int_sq.add h2.int_sq
  have hg0 : 0 ≤ᵐ[(uniformSphere N).prod (hidGauss N m)] g :=
    Filter.Eventually.of_forall fun p => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmk := mul_meas_ge_le_integral_of_nonneg hg0 hgi (ζ ^ 2)
  have hsub : {p : (Fin N → ℝ) × HidParam N m | p ∉ goodUH N m ζ} ⊆ {p | ζ ^ 2 ≤ g p} := by
    intro p hpb
    change ζ ^ 2 ≤ g p
    simp only [hg]
    by_contra hlt
    push Not at hlt
    apply hpb
    have a1 : |Dn N m p.1 p.2 - 1| ^ 2 < ζ ^ 2 := by
      nlinarith [sq_nonneg (|lamH N m p.1 p.2 - 1|)]
    have a2 : |lamH N m p.1 p.2 - 1| ^ 2 < ζ ^ 2 := by
      nlinarith [sq_nonneg (|Dn N m p.1 p.2 - 1|)]
    exact ⟨(abs_lt_of_sq_lt_sq a1 hζ.le |>.le.trans' (by rw [abs_abs])),
      (abs_lt_of_sq_lt_sq a2 hζ.le |>.le.trans' (by rw [abs_abs]))⟩
  have hint : ∫ p, g p ∂((uniformSphere N).prod (hidGauss N m)) ≤
      10 / (m : ℝ) + 25 / (m : ℝ) ^ 2 + (cHat2 N m / kap1 N) ^ 2 := by
    rw [hg, integral_add h1.int_sq h2.int_sq]
    have := h1.le
    rw [Real.sq_sqrt (by positivity)] at this
    exact add_le_add this h2.le
  have hmono := measureReal_mono (μ := (uniformSphere N).prod (hidGauss N m)) hsub
    (measure_ne_top _ _)
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact (mul_le_mul_of_nonneg_left hmono (sq_nonneg _)).trans (hmk.trans hint)

/-! ## The facts on the good hidden event -/

/-- The lower bound of `ŵ₀` on `goodHat n`. -/
noncomputable def wLowH : ℝ := 1 / (508 / 1000) - 1

lemma wLowH_pos : 0 < wLowH := by unfold wLowH; norm_num

section good

variable {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ goodHat n)

include hn hθ

/-- On `goodHat n`: `0.4798 ≤ ℓ₀² ≤ 0.508`. -/
theorem B0_window : 4798 / 10000 ≤ B0 (2 * n) (mW n) θ ∧ B0 (2 * n) (mW n) θ ≤ 508 / 1000 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  obtain ⟨hk1, hk2⟩ := kap1_window hn
  obtain ⟨hB1, hB2⟩ := Bh_hat hn hθ
  have hBpos := Bh_pos hn hθ
  have hksq1 : (49372 / 100000 : ℝ) ^ 2 ≤ kap1 (2 * n) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hk1 2
  have hksq2 : kap1 (2 * n) ^ 2 ≤ (4938 / 10000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hk2 2
  unfold B0
  constructor
  · rw [le_div_iff₀ hBpos]
    have h1 : 4798 / 10000 * Bh (2 * n) (mW n) θ ≤
        4798 / 10000 * (2 / ((2 * n : ℕ) : ℝ) * (508 / 1000)) :=
      mul_le_mul_of_nonneg_left hB2 (by norm_num)
    have h2 : 2 / ((2 * n : ℕ) : ℝ) * (49372 / 100000 : ℝ) ^ 2 ≤
        2 / ((2 * n : ℕ) : ℝ) * kap1 (2 * n) ^ 2 := mul_le_mul_of_nonneg_left hksq1 hγ.le
    have h3 : 4798 / 10000 * (2 / ((2 * n : ℕ) : ℝ) * (508 / 1000)) ≤
        2 / ((2 * n : ℕ) : ℝ) * (49372 / 100000 : ℝ) ^ 2 := by
      have e : 4798 / 10000 * (2 / ((2 * n : ℕ) : ℝ) * (508 / 1000)) =
          2 / ((2 * n : ℕ) : ℝ) * (4798 / 10000 * (508 / 1000)) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by norm_num) hγ.le
    linarith
  · rw [div_le_iff₀ hBpos]
    have h1 : 508 / 1000 * (2 / ((2 * n : ℕ) : ℝ) * (48 / 100)) ≤
        508 / 1000 * Bh (2 * n) (mW n) θ := mul_le_mul_of_nonneg_left hB1 (by norm_num)
    have h2 : 2 / ((2 * n : ℕ) : ℝ) * kap1 (2 * n) ^ 2 ≤
        2 / ((2 * n : ℕ) : ℝ) * (4938 / 10000 : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hksq2 hγ.le
    have h3 : 2 / ((2 * n : ℕ) : ℝ) * (4938 / 10000 : ℝ) ^ 2 ≤
        508 / 1000 * (2 / ((2 * n : ℕ) : ℝ) * (48 / 100)) := by
      have e : 508 / 1000 * (2 / ((2 * n : ℕ) : ℝ) * (48 / 100)) =
          2 / ((2 * n : ℕ) : ℝ) * (508 / 1000 * (48 / 100)) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by norm_num) hγ.le
    linarith

/-- On `goodHat n`: `wLowH ≤ ŵ₀ ≤ 1/0.4798 − 1`. -/
theorem w0H_window : wLowH ≤ w0H (2 * n) (mW n) θ ∧
    w0H (2 * n) (mW n) θ ≤ 1 / (4798 / 10000) - 1 := by
  obtain ⟨hB1, hB2⟩ := B0_window hn hθ
  have hB0 : 0 < B0 (2 * n) (mW n) θ := by linarith
  unfold w0H wLowH
  have h1 := one_div_le_one_div_of_le hB0 hB2
  have h2 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4798 / 10000) hB1
  constructor <;> linarith

theorem tauHat_sq : tauHat (2 * n) (mW n) θ ^ 2 =
    Bh (2 * n) (mW n) θ * w0H (2 * n) (mW n) θ := by
  have h1 := (w0H_window hn hθ).1
  have h2 := wLowH_pos
  have hB := Bh_pos hn hθ
  unfold tauHat
  rw [← w0H_eq, max_eq_right (by linarith)]
  exact Real.sq_sqrt (mul_nonneg hB.le (by linarith))

theorem tauHat_pos : 0 < tauHat (2 * n) (mW n) θ := by
  have h1 := (w0H_window hn hθ).1
  have h2 := wLowH_pos
  have hB := Bh_pos hn hθ
  unfold tauHat
  rw [← w0H_eq, max_eq_right (by linarith)]
  exact Real.sqrt_pos.mpr (mul_pos hB (by linarith))

end good

end BstLean.Part140

open BstLean.Part140 in
#print axioms tauH_sq
open BstLean.Part140 in
#print axioms lamH_L2
open BstLean.Part140 in
#print axioms tauFluctH_gen
open BstLean.Part140 in
#print axioms tauBadH_gen
open BstLean.Part140 in
#print axioms B0_window
open BstLean.Part140 in
#print axioms tauHat_sq
