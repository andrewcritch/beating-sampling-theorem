import BstLean.Part161Split
import BstLean.Part161Gauss
import BstLean.Part161Lat
import BstLean.Part161Tail

/-!
# Part 161, item 2: the reduction of `REPLA_mix_hyp` to named scalar hypotheses

Role: `delegations/statements/p161-spec.md`, item 2. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Lemma `t7:p07:latitude`,
Lemma `t7:p07:split`, Proposition `t7:p07:FL`, Lemma `t7:p07:tails`;
`theorem7-08-bias.tex` (the bias root); `theorem7-09-assembly.tex` (the sum
`0.002159 + 0.004295 + 0.000129 ≤ h_A`).

* `gP B m S = N(m, S·I)(B)` (with `√S` as the scale; `S < 0` gives the point mass at `m`).
* `QStand_eq`: `Q = E_a E_v pLat(a, v)`: the index `a = (Z, G)` gives the latitude
  `s = latitude |ĉ| τ₀ a`, the direction is `V = G'/|G'|` (independent), and `pLat` is the
  probability of the classifier event under `N(λ(x) c_A, S(x) I)`, `x = xLat c s V`.
* `qTilde_eq_lat`: `q̃ = E_a qtLat(a)`, `qtLat a = N(λ̃(s) c_A, S̃(s) I)(B)`.
* `SplitData`: a good set, the level `η`, and the two reference pairs `(λ₀, S₀)` (good-set
  means; the paper's `Q_s`) and `(λ̄, S̄)` (conditional means; the paper's `Q̄_s`).
* `FLUCT_hyp`, `BIAS_hyp`, `TAIL_hyp`: the named hypotheses.
* **`repla_root_of_split`**: `|√Q − √q̃| ≤ h_fl + h_bias + √(2 m_tail)`.
* **`repla_of_hyps`**: `REPLA_mix_hyp D t h_A E` from `FLUCT_hyp` (`0.002159`) and `BIAS_hyp`
  (`0.004295`) on `E` and the World window on `E`; the tail is PROVED (`latitude_tail`).
-/

namespace BstLean.Part161

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part157
open BstLean.Part53 (unitF53 radF53 measurable_unitF)

variable {n : ℕ}

/-- The classifier event `{y | F(y) > t}` of the retained `F`. -/
def clsSet (c : Ret n) (t : ℝ) : Set (Fin n → ℝ) := {y | classifier c.2.2 t y}

lemma measurableSet_clsSet (c : Ret n) (t : ℝ) : MeasurableSet (clsSet c t) :=
  measurableSet_lt measurable_const ((measurable_pi_apply 0).comp (continuous_mlpEval c.2.2).measurable)

/-- **The probability of the event `B` under `N(m, S·I)`** (the scale is `√S`). -/
noncomputable def gP (B : Set (Fin n → ℝ)) (m : Fin n → ℝ) (S : ℝ) : ℝ :=
  (stdGauss (Fin n)).real {η | m + √S • η ∈ B}

lemma gP_nonneg (B : Set (Fin n → ℝ)) (m : Fin n → ℝ) (S : ℝ) : 0 ≤ gP B m S := measureReal_nonneg

lemma gP_le_one (B : Set (Fin n → ℝ)) (m : Fin n → ℝ) (S : ℝ) : gP B m S ≤ 1 := measureReal_le_one

lemma measurable_gP_comp {β : Type*} [MeasurableSpace β] {B : Set (Fin n → ℝ)}
    (hB : MeasurableSet B) {m : β → Fin n → ℝ} {S : β → ℝ} (hm : Measurable m)
    (hS : Measurable S) : Measurable (fun x => gP B (m x) (S x)) := by
  have hT : MeasurableSet {q : β × (Fin n → ℝ) | m q.1 + √(S q.1) • q.2 ∈ B} :=
    ((hm.comp measurable_fst).add (((hS.comp measurable_fst).sqrt).smul measurable_snd)) hB
  exact (measurable_measure_prodMk_left (ν := stdGauss (Fin n)) hT).ennreal_toReal

/-- `|λ₁ c − λ₂ c|² = (λ₁ − λ₂)²·|c|²`. -/
lemma normSq_smul_sub (l₁ l₂ : ℝ) (c : Fin n → ℝ) :
    normSq (l₁ • c - l₂ • c) = (l₁ - l₂) ^ 2 * normSq c := by
  rw [← sub_smul, normSq_smul]

/-- `gauss_root` for two location factors along the same vector `c`. -/
lemma gP_root (B : Set (Fin n → ℝ)) (hB : MeasurableSet B) (c : Fin n → ℝ) (l₁ S₁ l₂ S₂ : ℝ) :
    (√(gP B (l₁ • c) S₁) - √(gP B (l₂ • c) S₂)) ^ 2 ≤
      hellG2 n ((l₁ - l₂) ^ 2 * normSq c) S₁ S₂ := by
  have h := gauss_root (l₁ • c) (l₂ • c) S₁ S₂ hB
  rwa [normSq_smul_sub] at h

/-! ## The index space, the components and the program's components -/

/-- The index `a = (Z, G)`: `Z` standard Gaussian, `G` standard Gaussian in `ℝ^{n−1}`. -/
abbrev Ix (n : ℕ) : Type := ℝ × (Fin (n - 1) → ℝ)

/-- The distribution of the index. -/
noncomputable def muI (n : ℕ) : Measure (Ix n) := (gaussianReal 0 1).prod (stdGauss (Fin (n - 1)))

instance : IsProbabilityMeasure (muI n) := by unfold muI; infer_instance

/-- The latitude of the index `a` for the retained data `c`. -/
noncomputable def latC (D : Design n) (c : Ret n) (a : Ix n) : ℝ :=
  latitude (√(normSq c.1.2)) (D.tau0 c) a

lemma measurable_latC (D : Design n) (c : Ret n) : Measurable (latC D c) :=
  measurable_latitude_comp measurable_const measurable_const measurable_id

/-- The probability of the classifier event under `N(λ(x) c_A, σ(x)²·I)` at the input `x`. -/
noncomputable def pAt (D : Design n) (t : ℝ) (c : Ret n) (x : Fin n → ℝ) : ℝ :=
  gP (clsSet c t) (lamX D c x • c.2.1.2) (sigX D c x ^ 2)

lemma measurable_pAt (D : Design n) (t : ℝ) (c : Ret n) : Measurable (pAt D t c) :=
  measurable_gP_comp (measurableSet_clsSet c t) ((measurable_lamX D c).smul_const _)
    ((measurable_sigX D c).pow_const 2)

/-- **The component of the pair (index, direction)**: `pLat (a, v) = pAt (xLat c s (v/|v|))`,
`s = latC D c a`. -/
noncomputable def pLat (D : Design n) (t : ℝ) (c : Ret n) (q : Ix n × (Fin (n - 1) → ℝ)) : ℝ :=
  pAt D t c (xLat c (latC D c q.1) (unitF53 q.2))

lemma measurable_pLat (D : Design n) (t : ℝ) (c : Ret n) : Measurable (pLat D t c) :=
  (measurable_pAt D t c).comp (measurable_xLat_comp c ((measurable_latC D c).comp measurable_fst)
    (measurable_unitF.comp measurable_snd))

/-- **The program's component at the index `a`**: `N(λ̃(s) c_A, S̃(s)·I)(B)`. -/
noncomputable def qtLat (D : Design n) (t : ℝ) (c : Ret n) (a : Ix n) : ℝ :=
  gP (clsSet c t) ((D.mix c (latC D c a)).1 • c.2.1.2) (D.mix c (latC D c a)).2

lemma measurable_mix_c (D : Design n) (c : Ret n) : Measurable (D.mix c) :=
  D.mmix.comp measurable_prodMk_left

lemma measurable_qtLat (D : Design n) (t : ℝ) (c : Ret n) : Measurable (qtLat D t c) :=
  measurable_gP_comp (measurableSet_clsSet c t)
    ((measurable_fst.comp ((measurable_mix_c D c).comp (measurable_latC D c))).smul_const _)
    (measurable_snd.comp ((measurable_mix_c D c).comp (measurable_latC D c)))

/-! ## `Q` and `q̃` as integrals over the index -/

/-- `Q` as an integral over the stand-in Gaussian vector `ξ`. -/
lemma QStand_eq_xi (D : Design n) (t : ℝ) (c : Ret n) :
    QStand D t c = ∫ ξ, pAt D t c (sphPt (c.1.2 + D.tau0 c • ξ)) ∂stdGauss (Fin n) := by
  set T : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {p | classifier c.2.2 t (lam (D.bA c.1 c.2.1.1) (hStand D c p.1) • c.2.1.2 +
      sig (2 / (mA n : ℝ)) (D.bA c.1 c.2.1.1) (hStand D c p.1) • p.2)} with hT
  have mh : Measurable (hStand D c) := measurable_hStand D c
  have mT : MeasurableSet T := by
    have h1 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        lam (D.bA c.1 c.2.1.1) (hStand D c p.1) • c.2.1.2 +
          sig (2 / (mA n : ℝ)) (D.bA c.1 c.2.1.1) (hStand D c p.1) • p.2) :=
      ((((measurable_lam _).comp mh).comp measurable_fst).smul_const _).add
        ((((measurable_sig _ _).comp mh).comp measurable_fst).smul measurable_snd)
    exact h1 (measurableSet_clsSet c t)
  unfold QStand
  rw [← hT, ← integral_indicator_one mT,
    integral_prod (f := T.indicator (1 : (Fin n → ℝ) × (Fin n → ℝ) → ℝ))
      ((integrable_const (1 : ℝ)).indicator mT)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have hs : MeasurableSet (Prod.mk ξ ⁻¹' T) := mT.preimage measurable_prodMk_left
  change ∫ η, T.indicator 1 (ξ, η) ∂stdGauss (Fin n) = _
  have e : (fun η => T.indicator (1 : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (ξ, η)) =
      (Prod.mk ξ ⁻¹' T).indicator 1 := by
    funext η
    by_cases h : (ξ, η) ∈ T
    · have h' : η ∈ Prod.mk ξ ⁻¹' T := h
      simp [h, h']
    · have h' : η ∉ Prod.mk ξ ⁻¹' T := h
      simp [h, h']
  rw [e, integral_indicator_one hs]
  unfold pAt gP
  congr 1
  ext η
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hT, clsSet]
  rw [Real.sqrt_sq (sigX_nonneg D c _)]
  rfl

/-- **`Q` as an integral over the index and the direction** (Lemma `t7:p07:latitude`). -/
theorem QStand_eq (hn : 2 ≤ n) (D : Design n) (t : ℝ) (c : Ret n) (hc : c.1.2 ≠ 0)
    (hτ : 0 < D.tau0 c) :
    QStand D t c = ∫ a, ∫ v, pLat D t c (a, v) ∂stdGauss (Fin (n - 1)) ∂muI n := by
  have mp := measurable_pAt D t c
  have hb : ∀ x, ‖pAt D t c x‖ ≤ 1 := fun x => by
    have h0 : 0 ≤ pAt D t c x := gP_nonneg _ _ _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact gP_le_one _ _ _
  have mf : Measurable (fun ξ : Fin n → ℝ => sphPt (c.1.2 + D.tau0 c • ξ)) :=
    measurable_sphPt.comp (measurable_const.add (measurable_const_smul (D.tau0 c)))
  rw [QStand_eq_xi, ← integral_map mf.aemeasurable mp.aestronglyMeasurable]
  change ∫ x, pAt D t c x ∂nuStand D c = _
  rw [nuStand_latitude hn D c hc hτ]
  have mg : Measurable (fun p : (ℝ × (Fin (n - 1) → ℝ)) × (Fin (n - 1) → ℝ) =>
      xLat c (latitude (n := n) (√(normSq c.1.2)) (D.tau0 c) p.1) (unitF53 p.2)) :=
    measurable_xLat_comp c ((measurable_latC D c).comp measurable_fst)
      (measurable_unitF.comp measurable_snd)
  rw [integral_map mg.aemeasurable mp.aestronglyMeasurable]
  unfold muI
  rw [integral_prod (f := fun p : (ℝ × (Fin (n - 1) → ℝ)) × (Fin (n - 1) → ℝ) =>
      pAt D t c (xLat c (latitude (n := n) (√(normSq c.1.2)) (D.tau0 c) p.1) (unitF53 p.2)))
    (Integrable.of_bound (mp.comp mg).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun p => hb _))]
  rfl

/-- **`q̃` as an integral over the index.** -/
theorem qTilde_eq_lat (D : Design n) (t : ℝ) (c : Ret n) :
    qTilde D t c = ∫ a, qtLat D t c a ∂muI n := by
  have mH := measurable_hitFn D t
  unfold qTilde drawMeas
  rw [integral_prod (f := fun d : DrawSp n => hitFn D t (c, d))
    (Integrable.of_bound (mH.comp measurable_prodMk_left).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun d => by
      rcases hitFn_01 D t (c, d) with h | h <;> simp [h]))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  set S : Set (Fin n → ℝ) := {η | classifier c.2.2 t (drawY D c (a, η))} with hS
  have mS : MeasurableSet S :=
    (measurableSet_hitEv D t).preimage (measurable_prodMk_left.comp measurable_prodMk_left)
  have e : (fun η => hitFn D t (c, (a, η))) = S.indicator 1 := by
    funext η
    unfold hitFn
    by_cases h : (c, (a, η)) ∈ hitEv D t
    · have h' : η ∈ S := h
      simp [h, h']
    · have h' : η ∉ S := h
      simp [h, h']
  change ∫ η, hitFn D t (c, (a, η)) ∂stdGauss (Fin n) = _
  rw [e, integral_indicator_one mS]
  rfl

/-! ## The named hypotheses -/

/-- **The data of the split**: a measurable good set of pairs (index, direction), the level `η`
of the removed mass, the good-set reference `(λ₀, S₀)` and the conditional reference `(λ̄, S̄)`,
measurable functions of the index. (The paper takes `λ₀ = E(λ | s, 𝒳_s)`, `S₀ = E(S | s, 𝒳_s)`,
`λ̄ = E(λ | s)`, `S̄ = E(S | s)`, `𝒳_s` the good set of Proposition `t7:p07:FL`, `η = 10⁻⁴`.) -/
structure SplitData (n : ℕ) where
  good : Set (Ix n × (Fin (n - 1) → ℝ))
  mgood : MeasurableSet good
  eta : ℝ
  eta_pos : 0 < eta
  eta_lt : eta < 1
  lam0 : Ix n → ℝ
  S0 : Ix n → ℝ
  lamb : Ix n → ℝ
  Sb : Ix n → ℝ
  mlam0 : Measurable lam0
  mS0 : Measurable S0
  mlamb : Measurable lamb
  mSb : Measurable Sb

/-- The bulk interval of the program, `[s_c − 6τ₀/ρ, s_c + 6τ₀/ρ]`, `s_c = |ĉ|/ρ`,
`ρ = √(|ĉ|² + n τ₀²)` (the clipping interval of `gridMix`). -/
noncomputable def bulkI (D : Design n) (c : Ret n) : Set ℝ :=
  Set.Icc (√(normSq c.1.2) / √(normSq c.1.2 + n * D.tau0 c ^ 2) -
      6 * D.tau0 c / √(normSq c.1.2 + n * D.tau0 c ^ 2))
    (√(normSq c.1.2) / √(normSq c.1.2 + n * D.tau0 c ^ 2) +
      6 * D.tau0 c / √(normSq c.1.2 + n * D.tau0 c ^ 2))

/-- The indices with latitude in the bulk interval. -/
def bulkIx (D : Design n) (c : Ret n) : Set (Ix n) := latC D c ⁻¹' bulkI D c

lemma measurableSet_bulkIx (D : Design n) (c : Ret n) : MeasurableSet (bulkIx D c) :=
  measurableSet_Icc.preimage (measurable_latC D c)

/-- The kept indices: latitude in the bulk interval and removed mass at most `η`. -/
def keptIx (D : Design n) (c : Ret n) (d : SplitData n) : Set (Ix n) :=
  keptSet (stdGauss (Fin (n - 1))) d.good (bulkIx D c) d.eta

/-- The probability of the event under the good-set reference `N(λ₀ c_A, S₀ I)`. -/
noncomputable def q0Lat (t : ℝ) (c : Ret n) (d : SplitData n) (a : Ix n) : ℝ :=
  gP (clsSet c t) (d.lam0 a • c.2.1.2) (d.S0 a)

/-- The probability of the event under the conditional reference `N(λ̄ c_A, S̄ I)`. -/
noncomputable def qbLat (t : ℝ) (c : Ret n) (d : SplitData n) (a : Ix n) : ℝ :=
  gP (clsSet c t) (d.lamb a • c.2.1.2) (d.Sb a)

/-- **(FLUCT) the fluctuation part: removed mass, good-set mixture against one Gaussian per
latitude, displacement of the good-set means.** There are `B`, `C`, `Dd` with
`E β ≤ B` (`β(a)` the removed mass), `E_kept (√P_a^g(C) − √Q_a(C))² ≤ C`,
`E_kept H²(Q_a, Q̄_a) ≤ Dd` and `√(2(1 + 1/η)B) + √C + √Dd ≤ h_fl`.

Paper statement that proves it: `theorem7-07-mixture-fluctuation.tex`, Proposition `t7:p07:FL`
(formula `t7:p07:hfl`; `h_fl < 0.002159` at `n = 16 384`; Proposition `t7:p09:upward` for larger
`n`), on the event `E_base ∩ E_lat ∩ E_{c_A}`. The middle term is bounded there by the chi-square
`E_s χ²(P_s^g ‖ Q_s)` (Lemma `t7:p07:chi-identity`, Corollary `t7:p07:chi-bounds`). -/
def FLUCT_hyp (D : Design n) (t : ℝ) (c : Ret n) (d : SplitData n) (hfl : ℝ) : Prop :=
  ∃ B C Dd : ℝ,
    ∫ a, removed (stdGauss (Fin (n - 1))) d.good a ∂muI n ≤ B ∧
    ∫ a in keptIx D c d, (√(goodMean (stdGauss (Fin (n - 1))) d.good (pLat D t c) a) -
      √(q0Lat t c d a)) ^ 2 ∂muI n ≤ C ∧
    ∫ a in keptIx D c d, hellG2 n ((d.lam0 a - d.lamb a) ^ 2 * normSq c.2.1.2) (d.S0 a) (d.Sb a)
      ∂muI n ≤ Dd ∧
    √(2 * (1 + d.eta⁻¹) * B) + √C + √Dd ≤ hfl

/-- **(BIAS) the bias of the program's tables.** `√(E_kept H²(Q̄_a, Q̃_a)) ≤ h_b`, with
`Q̄_a = N(λ̄ c_A, S̄ I)` and `Q̃_a = N(λ̃(s) c_A, S̃(s) I)` the program's component.

Paper statement that proves it: `theorem7-08-bias.tex` (the bias of the conditional passes, the
fourth root of formula `t7:p07:R`; `0.004295` in the assembly `theorem7-09-assembly.tex`). -/
def BIAS_hyp (D : Design n) (c : Ret n) (d : SplitData n) (hb : ℝ) : Prop :=
  √(∫ a in keptIx D c d, hellG2 n ((d.lamb a - (D.mix c (latC D c a)).1) ^ 2 * normSq c.2.1.2)
    (d.Sb a) (D.mix c (latC D c a)).2 ∂muI n) ≤ hb

/-- **(TAIL) the latitude tail**: the latitude is outside the bulk interval with probability at
most `m_tail`. Paper: Lemma `t7:p07:tails`. PROVED in the World window (`tail_of_window`). -/
def TAIL_hyp (D : Design n) (c : Ret n) (mt : ℝ) : Prop := (muI n).real (bulkIx D c)ᶜ ≤ mt

/-- **The World window** on the retained data: `ĉ ≠ 0`, `τ₀ > 0` and
`0.46 ≤ θ_in ≤ 0.54`, `θ_in = n τ₀²/(|ĉ|² + n τ₀²)` (paper: the window of Part 07, supplied by
the World part). -/
def WINDOW (D : Design n) (c : Ret n) : Prop :=
  c.1.2 ≠ 0 ∧ 0 < D.tau0 c ∧
    46 / 100 * (normSq c.1.2 + n * D.tau0 c ^ 2) ≤ n * D.tau0 c ^ 2 ∧
    n * D.tau0 c ^ 2 ≤ 54 / 100 * (normSq c.1.2 + n * D.tau0 c ^ 2)

/-- **The tail hypothesis holds in the World window** (`n ≥ 16 384`), with `m_tail = 4e^{−20}`. -/
theorem tail_of_window (hn : 16384 ≤ n) (D : Design n) (c : Ret n) (hw : WINDOW D c) :
    TAIL_hyp D c (4 * exp (-20)) := by
  obtain ⟨hc, hτ, h1, h2⟩ := hw
  have ha : 0 < √(normSq c.1.2) := by
    refine Real.sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg _) (Ne.symm ?_))
    intro h0
    exact hc (BstLean.Part130.normSq_eq_zero h0)
  have hsq : √(normSq c.1.2) ^ 2 = normSq c.1.2 := Real.sq_sqrt (normSq_nonneg _)
  have h := latitude_tail hn ha hτ (by rw [hsq]; exact h1) (by rw [hsq]; exact h2)
  unfold TAIL_hyp bulkIx bulkI muI
  rw [hsq] at h
  convert h using 2
  ext p
  rfl

/-! ## The reduction -/

/-- **The root of the Agent replacement from the three named parts.** For `n ≥ 2`, `ĉ ≠ 0`,
`τ₀ > 0` and every split data `d`: IF `FLUCT_hyp D t c d h_fl`, `BIAS_hyp D c d h_b` and
`TAIL_hyp D c m_t`, THEN `|√Q − √q̃| ≤ h_fl + h_b + √(2 m_t)`. -/
theorem repla_root_of_split (hn : 2 ≤ n) (D : Design n) (t : ℝ) (c : Ret n) (hc : c.1.2 ≠ 0)
    (hτ : 0 < D.tau0 c) (d : SplitData n) {hfl hb mt : ℝ} (hF : FLUCT_hyp D t c d hfl)
    (hB : BIAS_hyp D c d hb) (hT : TAIL_hyp D c mt) :
    |√(QStand D t c) - √(qTilde D t c)| ≤ hfl + hb + √(2 * mt) := by
  obtain ⟨Bm, C, Dd, hBm, hC, hDd, hsum⟩ := hF
  set ν := stdGauss (Fin (n - 1))
  set K := keptIx D c d
  have mK : MeasurableSet K :=
    measurableSet_keptSet ν d.mgood (measurableSet_bulkIx D c) d.eta
  set B := clsSet c t
  have mB := measurableSet_clsSet c t
  have mq0 : Measurable (q0Lat t c d) :=
    measurable_gP_comp mB (d.mlam0.smul_const _) d.mS0
  have mqb : Measurable (qbLat t c d) :=
    measurable_gP_comp mB (d.mlamb.smul_const _) d.mSb
  have mpl := measurable_pLat D t c
  have mqt := measurable_qtLat D t c
  -- the three kernels
  set Kχ : Ix n → ℝ := fun a => (√(goodMean ν d.good (pLat D t c) a) - √(q0Lat t c d a)) ^ 2
  set KD : Ix n → ℝ := fun a =>
    hellG2 n ((d.lam0 a - d.lamb a) ^ 2 * normSq c.2.1.2) (d.S0 a) (d.Sb a)
  set KB : Ix n → ℝ := fun a =>
    hellG2 n ((d.lamb a - (D.mix c (latC D c a)).1) ^ 2 * normSq c.2.1.2)
      (d.Sb a) (D.mix c (latC D c a)).2
  have mhell : ∀ {d2 S₁ S₂ : Ix n → ℝ}, Measurable d2 → Measurable S₁ → Measurable S₂ →
      Measurable (fun a => hellG2 n (d2 a) (S₁ a) (S₂ a)) := fun h1 h2 h3 =>
    (measurable_hellG2 n).comp (h1.prodMk (h2.prodMk h3))
  have mmix := (measurable_mix_c D c).comp (measurable_latC D c)
  have mKD : Measurable KD :=
    mhell (((d.mlam0.sub d.mlamb).pow_const 2).mul_const _) d.mS0 d.mSb
  have mKB : Measurable KB :=
    mhell (((d.mlamb.sub (measurable_fst.comp mmix)).pow_const 2).mul_const _) d.mSb
      (measurable_snd.comp mmix)
  have mKχ : Measurable Kχ :=
    (((measurable_goodMean ν d.mgood mpl).sqrt).sub mq0.sqrt).pow_const 2
  have bnd : ∀ {f : Ix n → ℝ}, Measurable f → (∀ a, 0 ≤ f a) → (∀ a, f a ≤ 2) →
      IntegrableOn f K (muI n) := fun {f} hf h0 h2 =>
    (Integrable.of_bound hf.aestronglyMeasurable 2 (Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 a)]; exact h2 a)).integrableOn
  have hpl0 : ∀ q, 0 ≤ pLat D t c q := fun q => gP_nonneg _ _ _
  have hpl1 : ∀ q, pLat D t c q ≤ 1 := fun q => gP_le_one _ _ _
  have iχ : IntegrableOn Kχ K (muI n) := by
    refine (Integrable.of_bound mKχ.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun a => ?_)).integrableOn
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases ha : removed ν d.good a < 1
    · obtain ⟨h0, h1, _⟩ := goodMean_bounds ν d.mgood mpl hpl0 hpl1 a ha
      exact sqrt_sub_sq_le_one h0 h1 (gP_nonneg _ _ _) (gP_le_one _ _ _)
    · have h1 : removed ν d.good a = 1 :=
        le_antisymm (removed_le_one ν d.good a) (not_lt.mp ha)
      have e : goodMean ν d.good (pLat D t c) a = 0 := by
        unfold goodMean; rw [h1]; simp
      change (√(goodMean ν d.good (pLat D t c) a) - √(q0Lat t c d a)) ^ 2 ≤ 1
      rw [e]
      exact sqrt_sub_sq_le_one le_rfl zero_le_one (gP_nonneg _ _ _) (gP_le_one _ _ _)
  have iD := bnd mKD (fun a => hellG2_nonneg n (mul_nonneg (sq_nonneg _) (normSq_nonneg _)) _ _) (fun a => hellG2_le_two n _ _ _)
  have iB := bnd mKB (fun a => hellG2_nonneg n (mul_nonneg (sq_nonneg _) (normSq_nonneg _)) _ _) (fun a => hellG2_le_two n _ _ _)
  have h := root_split (muI n) ν mpl hpl0 hpl1 d.mgood (measurableSet_bulkIx D c) d.eta_pos
    d.eta_lt mq0 mqb mqt (fun a => ⟨gP_nonneg _ _ _, gP_le_one _ _ _⟩)
    (fun a => ⟨gP_nonneg _ _ _, gP_le_one _ _ _⟩) (fun a => ⟨gP_nonneg _ _ _, gP_le_one _ _ _⟩)
    iχ iD iB hBm hT (fun a _ => le_rfl) (fun a _ => gP_root B mB _ _ _ _ _)
    (fun a _ => gP_root B mB _ _ _ _ _)
  rw [QStand_eq hn D t c hc hτ, qTilde_eq_lat D t c]
  refine h.trans ?_
  have hC' : √(∫ a in keptSet ν d.good (bulkIx D c) d.eta, Kχ a ∂muI n) ≤ √C :=
    Real.sqrt_le_sqrt hC
  have hD' : √(∫ a in keptSet ν d.good (bulkIx D c) d.eta, KD a ∂muI n) ≤ √Dd :=
    Real.sqrt_le_sqrt hDd
  have hB' : √(∫ a in keptSet ν d.good (bulkIx D c) d.eta, KB a ∂muI n) ≤ hb := hB
  linarith

/-- **The arithmetic of the assembly**: `0.002159 + 0.004295 + √(8e^{−20}) ≤ h_A`
(`h_A = 0.006583 + 10⁻²⁰`, `hAL` of Part 156). -/
theorem repla_arith : 2159 / 10 ^ 6 + 4295 / 10 ^ 6 + √(2 * (4 * exp (-20))) ≤
    BstLean.Part156.hAL := by
  have h := tail_root_num
  unfold BstLean.Part156.hAL
  linarith

/-- **`REPLA_mix_hyp` from the named hypotheses (item 2).** For `n ≥ 16 384` and a set `E` of
retained data: IF on `E` the World window holds and there is split data `d` with
`FLUCT_hyp D t c d 0.002159` and `BIAS_hyp D c d 0.004295`, THEN
`REPLA_mix_hyp D t h_A E` with `h_A = 0.006583 + 10⁻²⁰`. The tail is proved
(`tail_of_window`). -/
theorem repla_of_hyps (hn : 16384 ≤ n) (D : Design n) (t : ℝ) {E : Set (Ret n)}
    (hw : ∀ c ∈ E, WINDOW D c)
    (hd : ∀ c ∈ E, ∃ d : SplitData n,
      FLUCT_hyp D t c d (2159 / 10 ^ 6) ∧ BIAS_hyp D c d (4295 / 10 ^ 6)) :
    REPLA_mix_hyp D t BstLean.Part156.hAL E := by
  intro c hc
  obtain ⟨d, hF, hB⟩ := hd c hc
  have hwc := hw c hc
  have h := repla_root_of_split (by omega) D t c hwc.1 hwc.2.1 d hF hB
    (tail_of_window hn D c hwc)
  exact h.trans repla_arith

end BstLean.Part161

open BstLean.Part161 in
#print axioms QStand_eq
open BstLean.Part161 in
#print axioms qTilde_eq_lat
open BstLean.Part161 in
#print axioms repla_root_of_split
open BstLean.Part161 in
#print axioms repla_of_hyps
