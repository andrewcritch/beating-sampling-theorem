import BstLean.Part163Sane
import BstLean.Part162All

/-!
# Part 163 (file `Vac`): the hypothesis of `classifier_paper_comb23` is false

Do not use `sorry`, `native_decide` or `axiom`.

* `gauss_tail_half`: `Pr(Z > 1/2) ≥ 3/32` for a standard Gaussian `Z` (from `E Z² = 1`,
  `E Z⁴ = 3` and the symmetry of `Z`).
* `Fsel hn s`: the test network `F(y) = s·relu(y₀)` (two hidden layers, one non-zero weight each).
* `degen c F`: the retained value with the World data and `A₁` of `c`, `A₂ = 0`, `c_A = 0`, and `F`.
* `QStand_degen`: at `degen c F`, `Q = 1` if `t < 0` and `Q = 0` if `t ≥ 0` (the last hidden Agent
  vector is `0`, so `F` sees the input `0` and `F(0) = 0`).
* `qTilde_ge`, `qTilde_le`: `q̃ ≥ 3/32` or `q̃ ≤ 29/32` when the draws with `η₀ > 1/2` all hit or
  all miss (the scale `S̃ ≥ (2/n)/5` of the paper's table `gridMix`).
* `goodSet_compl_le`: `Pr(goodSetᶜ) ≤ δ_hid + v_W/h_W² + δ_extra` from `EVENTS_hyp`;
  `oldSet_nonempty`: the World-only good set of `classifier_paper_comb23` is not empty.
* **`comb23_hyp_false`**: for every `n ≥ 16 384` and every `t`, `REPLA_mix_hyp` on
  `goodSet (HP n) (E_{θ−} ∩ E_{θ+}) (HbarW D) hWL` is FALSE. So `classifier_paper_comb23` and
  `classifier_paper_comb` of Part 160 are vacuous (their only hypothesis never holds).
* `comb23_fluct_false`: the same for Part 161's named hypotheses on that set (the form that
  Part 162's `classifier_paper_mom` and `classifier_paper_psi` reduce to).
-/

namespace BstLean.Part163

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160

variable {n : ℕ}

lemma int_abs_pow (k : ℕ) : Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 1) := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp
  have h1 : MemLp (id : ℝ → ℝ) ((k : NNReal) : ENNReal) (gaussianReal 0 1) := memLp_id_gaussianReal _
  have h2 : MemLp (id : ℝ → ℝ) (k : ENNReal) (gaussianReal 0 1) := by simpa using h1
  have := h2.integrable_norm_pow (by omega)
  simpa [Real.norm_eq_abs] using this

lemma gauss_abs_half : (3 : ℝ) / 16 ≤ (gaussianReal 0 1).real {x : ℝ | 1 / 2 < |x|} := by
  set μ := gaussianReal 0 1
  set A := {x : ℝ | 1 / 2 < |x|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const continuous_abs.measurable
  have hpt : ∀ x : ℝ, |x| ^ 2 ≤ 1 / 4 + 2 * A.indicator 1 x + |x| ^ 4 / 8 := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      simp only [Pi.one_apply]
      nlinarith [sq_nonneg (|x| ^ 2 - 4), abs_nonneg x]
    · rw [Set.indicator_of_notMem hx]
      have : |x| ≤ 1 / 2 := not_lt.1 hx
      nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 4]
  have i2 := int_abs_pow 2
  have i4 := int_abs_pow 4
  have iA : Integrable (A.indicator (1 : ℝ → ℝ)) μ := (integrable_const (1 : ℝ)).indicator hA
  have iR : Integrable (fun x : ℝ => 1 / 4 + 2 * A.indicator 1 x + |x| ^ 4 / 8) μ :=
    ((integrable_const _).add (iA.const_mul 2)).add (i4.div_const 8)
  have hmono : ∫ x, |x| ^ 2 ∂μ ≤ ∫ x, (1 / 4 + 2 * A.indicator 1 x + |x| ^ 4 / 8) ∂μ :=
    integral_mono i2 iR hpt
  have hR : ∫ x, (1 / 4 + 2 * A.indicator 1 x + |x| ^ 4 / 8) ∂μ =
      1 / 4 + 2 * μ.real A + (∫ x, |x| ^ 4 ∂μ) / 8 := by
    have i0 : Integrable (fun x : ℝ => (2 : ℝ) * A.indicator (1 : ℝ → ℝ) x) μ := iA.const_mul 2
    have i1 : Integrable (fun x : ℝ => (1 / 4 : ℝ) + 2 * A.indicator (1 : ℝ → ℝ) x) μ :=
      (integrable_const _).add i0
    have i5 : Integrable (fun x : ℝ => |x| ^ 4 / 8) μ := i4.div_const 8
    rw [integral_add i1 i5, integral_add (integrable_const _) i0, integral_const, integral_const_mul,
      integral_div, integral_indicator_one hA]
    simp
  rw [hR] at hmono
  have g2 : ∫ x, |x| ^ 2 ∂μ = 1 := by
    have := BstLean.Part162.gmom_even 1
    simpa [BstLean.Part162.gmom] using this
  have g4 : ∫ x, |x| ^ 4 ∂μ = 3 := by
    have := BstLean.Part162.gmom_even 2
    norm_num [BstLean.Part162.gmom, Finset.prod_range_succ] at this
    exact this
  rw [g2, g4] at hmono
  linarith

lemma gauss_tail_half : (3 : ℝ) / 32 ≤ (gaussianReal 0 1).real {x : ℝ | 1 / 2 < x} := by
  have h := gauss_abs_half
  set μ := gaussianReal 0 1
  have hsym : μ.real {x : ℝ | 1 / 2 < -x} = μ.real {x : ℝ | 1 / 2 < x} := by
    have hm : μ.map (fun x => -x) = μ := by
      rw [gaussianReal_map_neg]; simp [μ]
    have hs : MeasurableSet {x : ℝ | 1 / 2 < x} := measurableSet_lt measurable_const measurable_id
    conv_rhs => rw [← hm]
    rw [map_measureReal_apply measurable_neg hs]
    rfl
  have hsub : {x : ℝ | 1 / 2 < |x|} ⊆ {x : ℝ | 1 / 2 < x} ∪ {x : ℝ | 1 / 2 < -x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
    rcases le_or_gt 0 x with h0 | h0
    · left; rwa [abs_of_nonneg h0] at hx
    · right; rwa [abs_of_neg h0] at hx
  have h2 := (measureReal_mono hsub).trans (measureReal_union_le (μ := μ) _ _)
  linarith


/-- The test network `F(y) = s·relu(relu(y_{j₀}))`. -/
noncomputable def Fsel (hn : 1 ≤ n) (s : ℝ) : FPar n :=
  (Matrix.single (⟨0, BstLean.Part151.mF_pos hn⟩ : Fin (mF n)) (⟨0, hn⟩ : Fin n) 1,
   Matrix.single (⟨0, BstLean.Part151.mF_pos hn⟩ : Fin (mF n)) (⟨0, BstLean.Part151.mF_pos hn⟩ : Fin (mF n)) 1,
   Matrix.single (0 : Fin 1) (⟨0, BstLean.Part151.mF_pos hn⟩ : Fin (mF n)) s)

lemma single_mulVec {m k : ℕ} (i : Fin m) (j : Fin k) (a : ℝ) (v : Fin k → ℝ) (l : Fin m) :
    (Matrix.single i j a).mulVec v l = if l = i then a * v j else 0 := by
  by_cases h : l = i
  · subst h; simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · have h' : ¬ i = l := fun e => h e.symm
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply, h, h']

lemma Fsel_eval (hn : 1 ≤ n) (s : ℝ) (y : Fin n → ℝ) :
    mlpEval (Fsel hn s) y 0 = s * relu (y ⟨0, hn⟩) := by
  simp only [mlpEval, mlp2, Fsel, single_mulVec, reluV, ite_true]
  simp [relu]

lemma Fsel_zero (hn : 1 ≤ n) (s : ℝ) : mlpEval (Fsel hn s) 0 0 = 0 := by
  rw [Fsel_eval]; simp [relu]


/-- The retained value with the World data and `A₁` of `c`, `A₂ = 0`, `c_A = 0`, and the network `F`. -/
def degen (c : Ret n) (F : FPar n) : Ret n := (c.1, ((c.2.1.1.1, 0), 0), F)

lemma hStand_degen (D : Design n) (c : Ret n) (F : FPar n) (ξ : Fin n → ℝ) :
    hStand D (degen c F) ξ = 0 := by
  funext j; simp [hStand, degen, hid2, reluV, relu]

lemma QStand_degen (hn : 1 ≤ n) (D : Design n) (t : ℝ) (c : Ret n) (s : ℝ) :
    QStand D t (degen c (Fsel hn s)) = if t < 0 then 1 else 0 := by
  unfold QStand
  have e : {p : (Fin n → ℝ) × (Fin n → ℝ) | classifier (degen c (Fsel hn s)).2.2 t
      (lam (D.bA (degen c (Fsel hn s)).1 (degen c (Fsel hn s)).2.1.1)
        (hStand D (degen c (Fsel hn s)) p.1) • (degen c (Fsel hn s)).2.1.2 +
      sig (2 / (mA n : ℝ)) (D.bA (degen c (Fsel hn s)).1 (degen c (Fsel hn s)).2.1.1)
        (hStand D (degen c (Fsel hn s)) p.1) • p.2)} = {p | t < 0} := by
    ext p
    simp only [hStand_degen, Set.mem_ofPred_eq]
    have h1 : lam (D.bA (degen c (Fsel hn s)).1 (degen c (Fsel hn s)).2.1.1) 0 = 0 := by
      simp [lam]
    have h2 : sig (2 / (mA n : ℝ)) (D.bA (degen c (Fsel hn s)).1 (degen c (Fsel hn s)).2.1.1) 0
        = 0 := by
      simp [sig, res, h1, normSq]
    rw [h1, h2, zero_smul, zero_smul, add_zero]
    show t < mlpEval (Fsel hn s) 0 0 ↔ t < 0
    rw [Fsel_zero]
  rw [e]
  split_ifs with ht
  · simp [ht]
  · simp [ht]

lemma mixS_lower (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    (c : Ret n) (σ : ℝ) : 2 / (n : ℝ) * (1 / 5) ≤ ((paperDesign n fT wT hf hw).mix c σ).2 := by
  show 2 / (n : ℝ) * (1 / 5) ≤ (gridMix (paperCentres n) (fun c => tau0p c.1.1) fT wT c σ).2
  unfold gridMix
  exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

lemma drawY_degen (hn : 1 ≤ n) (D : Design n) (c : Ret n) (F : FPar n) (d : DrawSp n) :
    drawY D (degen c F) d ⟨0, hn⟩ =
      √((D.mix (degen c F) (latitude (√(normSq (degen c F).1.2)) (D.tau0 (degen c F)) d.1)).2) *
        d.2 ⟨0, hn⟩ := by
  simp [drawY, degen]

/-- The scale of the test network. -/
noncomputable def Kt (n : ℕ) (t : ℝ) : ℝ := 2 * (|t| + 1) / √(2 / (n : ℝ) * (1 / 5))

/-- The sign of the test network. -/
noncomputable def sgn (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

lemma key_hit (hn : 1 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    (t : ℝ) (c : Ret n) (d : DrawSp n) (hd : 1 / 2 < d.2 ⟨0, hn⟩) :
    |t| + 1 ≤ Kt n t * relu (drawY (paperDesign n fT wT hf hw)
      (degen c (Fsel hn (sgn t * Kt n t))) d ⟨0, hn⟩) := by
  rw [drawY_degen]
  set S := ((paperDesign n fT wT hf hw).mix (degen c (Fsel hn (sgn t * Kt n t)))
    (latitude (√(normSq (degen c (Fsel hn (sgn t * Kt n t))).1.2))
      ((paperDesign n fT wT hf hw).tau0 (degen c (Fsel hn (sgn t * Kt n t)))) d.1)).2
  have hS := mixS_lower fT wT hf hw (degen c (Fsel hn (sgn t * Kt n t)))
    (latitude (√(normSq (degen c (Fsel hn (sgn t * Kt n t))).1.2))
      ((paperDesign n fT wT hf hw).tau0 (degen c (Fsel hn (sgn t * Kt n t)))) d.1)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set r := √(2 / (n : ℝ) * (1 / 5)) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hrS : r ≤ √S := Real.sqrt_le_sqrt hS
  have hpos : 0 ≤ √S * d.2 ⟨0, hn⟩ := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  rw [show relu (√S * d.2 ⟨0, hn⟩) = √S * d.2 ⟨0, hn⟩ from max_eq_right hpos]
  have hK : Kt n t * r = 2 * (|t| + 1) := by
    unfold Kt; rw [← hr]; field_simp
  have hK0 : 0 ≤ Kt n t := by unfold Kt; positivity
  have h1 : r / 2 ≤ √S * d.2 ⟨0, hn⟩ := by
    have : r * (1 / 2) ≤ √S * d.2 ⟨0, hn⟩ :=
      mul_le_mul hrS hd.le (by norm_num) (Real.sqrt_nonneg _)
    linarith
  have h2 : Kt n t * (r / 2) ≤ Kt n t * (√S * d.2 ⟨0, hn⟩) := mul_le_mul_of_nonneg_left h1 hK0
  nlinarith

lemma drawMeas_coord (hn : 1 ≤ n) :
    (drawMeas n).real {d : DrawSp n | 1 / 2 < d.2 ⟨0, hn⟩} =
      (gaussianReal 0 1).real {x : ℝ | 1 / 2 < x} := by
  have hT : MeasurableSet {x : ℝ | 1 / 2 < x} := measurableSet_lt measurable_const measurable_id
  have hT' : MeasurableSet {η : Fin n → ℝ | 1 / 2 < η ⟨0, hn⟩} :=
    measurableSet_lt measurable_const (measurable_pi_apply _)
  have e1 : {d : DrawSp n | 1 / 2 < d.2 ⟨0, hn⟩} =
      Prod.snd ⁻¹' {η : Fin n → ℝ | 1 / 2 < η ⟨0, hn⟩} := rfl
  have e2 : {η : Fin n → ℝ | 1 / 2 < η ⟨0, hn⟩} =
      Function.eval (⟨0, hn⟩ : Fin n) ⁻¹' {x : ℝ | 1 / 2 < x} := rfl
  rw [e1, ← map_measureReal_apply measurable_snd hT']
  unfold drawMeas
  rw [Measure.map_snd_prod, measure_univ, one_smul, e2]
  unfold stdGauss
  simp only [Measure.real]
  rw [(measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) (⟨0, hn⟩ : Fin n)).measure_preimage
    hT.nullMeasurableSet]

lemma qTilde_ge (hn : 1 ≤ n) (D : Design n) (t : ℝ) (c : Ret n)
    (h : ∀ d : DrawSp n, 1 / 2 < d.2 ⟨0, hn⟩ → (c, d) ∈ hitEv D t) :
    3 / 32 ≤ qTilde D t c := by
  have hS : MeasurableSet {d : DrawSp n | 1 / 2 < d.2 ⟨0, hn⟩} :=
    measurableSet_lt measurable_const ((measurable_pi_apply _).comp measurable_snd)
  have hm : Measurable (fun d : DrawSp n => hitFn D t (c, d)) :=
    (measurable_hitFn D t).comp measurable_prodMk_left
  have hint : Integrable (fun d : DrawSp n => hitFn D t (c, d)) (drawMeas n) := by
    refine Integrable.of_bound (C := 1) hm.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro d
    unfold hitFn
    by_cases hx : (c, d) ∈ hitEv D t
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hle : ∀ d : DrawSp n, {d : DrawSp n | 1 / 2 < d.2 ⟨0, hn⟩}.indicator (1 : DrawSp n → ℝ) d ≤
      hitFn D t (c, d) := by
    intro d
    by_cases hd : 1 / 2 < d.2 ⟨0, hn⟩
    · rw [Set.indicator_of_mem (show d ∈ {d : DrawSp n | 1 / 2 < d.2 ⟨0, hn⟩} from hd)]
      unfold hitFn; rw [Set.indicator_of_mem (h d hd)]; simp
    · rw [Set.indicator_of_notMem (show d ∉ {d : DrawSp n | 1 / 2 < d.2 ⟨0, hn⟩} from hd)]
      unfold hitFn; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have iS : Integrable ({d : DrawSp n | 1 / 2 < d.2 ⟨0, hn⟩}.indicator (1 : DrawSp n → ℝ))
      (drawMeas n) := (integrable_const (1 : ℝ)).indicator hS
  have h1 := integral_mono iS hint hle
  rw [integral_indicator_one hS, drawMeas_coord hn] at h1
  unfold qTilde
  exact (gauss_tail_half).trans h1

lemma qTilde_le (hn : 1 ≤ n) (D : Design n) (t : ℝ) (c : Ret n)
    (h : ∀ d : DrawSp n, 1 / 2 < d.2 ⟨0, hn⟩ → (c, d) ∉ hitEv D t) :
    qTilde D t c ≤ 29 / 32 := by
  have hS : MeasurableSet {d : DrawSp n | 1 / 2 < d.2 ⟨0, hn⟩} :=
    measurableSet_lt measurable_const ((measurable_pi_apply _).comp measurable_snd)
  have hm : Measurable (fun d : DrawSp n => hitFn D t (c, d)) :=
    (measurable_hitFn D t).comp measurable_prodMk_left
  have hint : Integrable (fun d : DrawSp n => hitFn D t (c, d)) (drawMeas n) := by
    refine Integrable.of_bound (C := 1) hm.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro d
    unfold hitFn
    by_cases hx : (c, d) ∈ hitEv D t
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have iS : Integrable ({d : DrawSp n | 1 / 2 < d.2 ⟨0, hn⟩}.indicator (1 : DrawSp n → ℝ))
      (drawMeas n) := (integrable_const (1 : ℝ)).indicator hS
  have hle : ∀ d : DrawSp n, hitFn D t (c, d) ≤
      1 - {d : DrawSp n | 1 / 2 < d.2 ⟨0, hn⟩}.indicator (1 : DrawSp n → ℝ) d := by
    intro d
    by_cases hd : 1 / 2 < d.2 ⟨0, hn⟩
    · rw [Set.indicator_of_mem (show d ∈ {d : DrawSp n | 1 / 2 < d.2 ⟨0, hn⟩} from hd)]
      unfold hitFn; rw [Set.indicator_of_notMem (h d hd)]; simp
    · rw [Set.indicator_of_notMem (show d ∉ {d : DrawSp n | 1 / 2 < d.2 ⟨0, hn⟩} from hd)]
      unfold hitFn
      by_cases hx : (c, d) ∈ hitEv D t
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
  have iD : Integrable (fun d : DrawSp n =>
      1 - {d : DrawSp n | 1 / 2 < d.2 ⟨0, hn⟩}.indicator (1 : DrawSp n → ℝ) d) (drawMeas n) :=
    (integrable_const (1 : ℝ)).sub iS
  have h1 := integral_mono hint iD hle
  rw [integral_sub (integrable_const _) iS, integral_const, integral_indicator_one hS,
    drawMeas_coord hn] at h1
  rw [probReal_univ, smul_eq_mul, one_mul] at h1
  unfold qTilde
  linarith [gauss_tail_half]

/-- **The charge of the good set** from `EVENTS_hyp` (Markov on `H`). -/
theorem goodSet_compl_le (D : Centres n) {H E₁ : Set (Ret n)} {Hbar : Ret n → ℝ}
    {δhid vW δextra hW : ℝ} (hhW : 0 < hW) (hEv : EVENTS_hyp D H E₁ Hbar δhid vW δextra) :
    (retDist D).real (goodSet H E₁ Hbar hW)ᶜ ≤ δhid + vW / hW ^ 2 + δextra := by
  obtain ⟨hH, hE₁, hHm, hhid, hHint, hvW, hextra⟩ := hEv
  set μC := retDist D
  have hmarkov : μC.real (H ∩ {c | hW < Hbar c}) ≤ vW / hW ^ 2 := by
    have h1 := mul_meas_ge_le_integral_of_nonneg (μ := μC.restrict H)
      (f := fun c => Hbar c ^ 2) (Filter.Eventually.of_forall (fun c => sq_nonneg _)) hHint
      (hW ^ 2)
    have h2 : μC.real (H ∩ {c | hW < Hbar c}) ≤
        (μC.restrict H).real {c | hW ^ 2 ≤ Hbar c ^ 2} := by
      have h3 : (μC.restrict H).real {c | hW ^ 2 ≤ Hbar c ^ 2} =
          μC.real ({c | hW ^ 2 ≤ Hbar c ^ 2} ∩ H) := by
        simp only [Measure.real]
        rw [Measure.restrict_apply]
        exact measurableSet_le measurable_const (hHm.pow_const 2)
      rw [h3]
      refine measureReal_mono (fun c hc => ⟨?_, hc.1⟩)
      exact pow_le_pow_left₀ hhW.le (le_of_lt hc.2) 2
    rw [le_div_iff₀ (by positivity)]
    calc μC.real (H ∩ {c | hW < Hbar c}) * hW ^ 2
        ≤ (μC.restrict H).real {c | hW ^ 2 ≤ Hbar c ^ 2} * hW ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = hW ^ 2 * (μC.restrict H).real {c | hW ^ 2 ≤ Hbar c ^ 2} := mul_comm _ _
      _ ≤ ∫ c in H, Hbar c ^ 2 ∂μC := h1
      _ ≤ vW := hvW
  have hsub : (goodSet H E₁ Hbar hW)ᶜ ⊆ Hᶜ ∪ (H ∩ {c | hW < Hbar c}) ∪ (H ∩ E₁ᶜ) := by
    intro c hc
    by_cases h1 : c ∈ H
    · by_cases h2 : Hbar c ≤ hW
      · right
        exact ⟨h1, fun h3 => hc ⟨⟨h1, h2⟩, h3⟩⟩
      · left; right
        exact ⟨h1, not_le.1 h2⟩
    · left; left
      exact h1
  calc μC.real (goodSet H E₁ Hbar hW)ᶜ
      ≤ μC.real (Hᶜ ∪ (H ∩ {c | hW < Hbar c}) ∪ (H ∩ E₁ᶜ)) := measureReal_mono hsub
    _ ≤ μC.real Hᶜ + μC.real (H ∩ {c | hW < Hbar c}) + μC.real (H ∩ E₁ᶜ) :=
        (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
    _ ≤ δhid + vW / hW ^ 2 + δextra := by linarith

/-- **The old good set is not empty** (`n ≥ 16 384`): its charge is `≤ 0.0029 < 1`. -/
theorem oldSet_nonempty (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    ∃ c, c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
      BstLean.Part159.Ethp (paperCentres n)) (HbarW (paperDesign n fT wT hf hw)) hWL := by
  set D := paperDesign n fT wT hf hw
  set E₁ := BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n)
  have hE₁ : MeasurableSet E₁ :=
    (BstLean.Part159.measurableSet_Ethm _).inter (BstLean.Part159.measurableSet_Ethp _)
  obtain ⟨hW1, -⟩ := BstLean.Part159.paper_world hn D rfl (fun _ => rfl)
  have hang : (retDist D.toCentres).real (BstLean.Part159.HP n ∩ E₁ᶜ) ≤
      BstLean.Part159.δAng := by
    have h := BstLean.Part159.extra_angle hn (paperCentres n) (BstLean.Part159.HP n) Set.univ
    have e1 : BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩
        Set.univ = E₁ := by rw [Set.inter_univ]
    rw [e1, Set.compl_univ, Set.inter_empty, measureReal_empty, add_zero] at h
    exact h
  have hEv := hW1 hE₁ hang
  have h := goodSet_compl_le D.toCentres (hW := hWL) (by unfold hWL; norm_num) hEv
  have hnum : BstLean.Part159.δPap + BstLean.Part159.vPap / hWL ^ 2 + BstLean.Part159.δAng < 1 := by
    unfold BstLean.Part159.δPap BstLean.Part159.vPap BstLean.Part159.δAng hWL; norm_num
  by_contra hne
  simp only [not_exists] at hne
  have hem : (goodSet (BstLean.Part159.HP n) E₁ (HbarW D) hWL)ᶜ = Set.univ := by
    ext c; simp only [Set.mem_compl_iff, Set.mem_univ, iff_true]; exact hne c
  rw [hem, probReal_univ] at h
  linarith

/-- **The hypothesis of Part 160's `classifier_paper_comb23` is FALSE** for every threshold `t`
and every `n ≥ 16 384`: `REPLA_mix_hyp` on the World-only good set fails at a retained value with
the World data of a good value, `A₂ = 0`, `c_A = 0` and the network `F(y) = ±K·relu(y₀)`. -/
theorem comb23_hyp_false (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) :
    ¬ REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n)) (HbarW (paperDesign n fT wT hf hw)) hWL) := by
  intro hRA
  have hn1 : 1 ≤ n := by omega
  obtain ⟨c, hc⟩ := oldSet_nonempty hn fT wT hf hw
  set F := Fsel hn1 (sgn t * Kt n t)
  have hc' := worldGood_agent_free fT wT hf hw hc (((c.2.1.1.1, 0), 0), F)
  have h := hRA _ hc'
  have hQ := QStand_degen hn1 (paperDesign n fT wT hf hw) t c (sgn t * Kt n t)
  have hK := fun d hd => key_hit hn1 fT wT hf hw t c d hd
  change |√(QStand (paperDesign n fT wT hf hw) t (degen c F)) -
    √(qTilde (paperDesign n fT wT hf hw) t (degen c F))| ≤ hAL at h
  rw [hQ] at h
  by_cases ht : 0 ≤ t
  · have hq := qTilde_ge hn1 (paperDesign n fT wT hf hw) t (degen c F) (fun d hd => by
      show t < mlpEval F (drawY (paperDesign n fT wT hf hw) (degen c F) d) 0
      rw [Fsel_eval]
      have := hK d hd
      simp only [sgn, if_pos ht, one_mul]
      have : t ≤ |t| := le_abs_self t
      linarith)
    rw [if_neg (not_lt.2 ht), Real.sqrt_zero, zero_sub, abs_neg,
      abs_of_nonneg (Real.sqrt_nonneg _)] at h
    have h0 : 0 ≤ qTilde (paperDesign n fT wT hf hw) t (degen c F) := by linarith
    have h2 : qTilde (paperDesign n fT wT hf hw) t (degen c F) ≤ hAL ^ 2 := by
      rw [← Real.sq_sqrt h0]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    have : hAL ^ 2 < 3 / 32 := by unfold hAL; norm_num
    linarith
  · rw [not_le] at ht
    have hq := qTilde_le hn1 (paperDesign n fT wT hf hw) t (degen c F) (fun d hd => by
      show ¬ t < mlpEval F (drawY (paperDesign n fT wT hf hw) (degen c F) d) 0
      rw [Fsel_eval]
      have := hK d hd
      simp only [sgn, if_neg (not_le.2 ht)]
      rw [abs_of_neg ht] at this
      rw [not_lt]
      linarith)
    rw [if_pos ht, Real.sqrt_one] at h
    have h1 : 1 - hAL ≤ √(qTilde (paperDesign n fT wT hf hw) t (degen c F)) := by
      have := le_abs_self (1 - √(qTilde (paperDesign n fT wT hf hw) t (degen c F)))
      linarith
    have hA0 : 0 ≤ 1 - hAL := by unfold hAL; norm_num
    have h0 : 0 ≤ qTilde (paperDesign n fT wT hf hw) t (degen c F) := by
      unfold qTilde
      exact integral_nonneg fun d => Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have h2 : (1 - hAL) ^ 2 ≤ qTilde (paperDesign n fT wT hf hw) t (degen c F) := by
      rw [← Real.sq_sqrt h0]
      exact pow_le_pow_left₀ hA0 h1 2
    have : (29 : ℝ) / 32 < (1 - hAL) ^ 2 := by unfold hAL; norm_num
    linarith

/-- **Part 161's named hypotheses on the World-only good set are false** (every `n ≥ 16 384`,
every `t`). Part 162's `classifier_paper_mom` and `classifier_paper_psi` derive exactly this
statement from their hypothesis `hM` (through `fluct_of_latMom`), so their `hM` is false too. -/
theorem comb23_fluct_false (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) :
    ¬ (∀ c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n)) (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (d : BstLean.Part161.SplitData n) (ε₀ δ₀ slow : ℝ),
        BstLean.Part161.FLUCT_chi_hyp (paperDesign n fT wT hf hw) c d ε₀ δ₀ slow (2159 / 10 ^ 6) ∧
        BstLean.Part161.BIAS_hyp (paperDesign n fT wT hf hw) c d (4295 / 10 ^ 6)) := by
  intro hFl
  refine comb23_hyp_false hn fT wT hf hw t ?_
  refine BstLean.Part161.repla_of_hyps_chi hn _ t (fun c hc => ?_) hFl
  exact BstLean.Part161.window_paper (by omega) fT wT hf hw hc.1.1 hc.2.1 hc.2.2

end BstLean.Part163

open BstLean.Part163 in
#print axioms gauss_tail_half
open BstLean.Part163 in
#print axioms QStand_degen
open BstLean.Part163 in
#print axioms qTilde_ge
open BstLean.Part163 in
#print axioms qTilde_le
open BstLean.Part163 in
#print axioms goodSet_compl_le
open BstLean.Part163 in
#print axioms oldSet_nonempty
open BstLean.Part163 in
#print axioms comb23_hyp_false
open BstLean.Part163 in
#print axioms comb23_fluct_false
