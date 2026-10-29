import BstLean.Part171Meas

/-!
# Part 171 (file `Op`): the statistics event conditional on the operator event

No proof is left open; no `native_decide` or `axiom` is used.

`BiasMomF` and `BiasMomW` only ask for bounds at `A₁` with `‖A₁‖_op ≤ O₁` (the operator event,
already charged in Lean's good set). So the statistics event only needs to hold on the operator
event, and the upper bound `ς² ≤ 5/n` follows from the operator bound (Part 169's `vsig2_le`).

* `LowStat c g`: `1/(5n) ≤ ς²`, `DstN ≤ 16/n³`, `hUN ≤ 16/n³`, `V2N ≤ 64/n⁴`, `piN ≤ 1/n⁴`.
* `StatEvOp n = {(wr, A₁) | ‖A₁‖_op ≤ O₁ → ∀ g < J_s, LowStat}`; `measurableSet_StatEvOp`.
* `vsig2_upper`: on the operator event, at a node with `s² ≤ 1`, `ς² ≤ 5/n`.
* **`classifier_paper_statOp80k`**: the classifier theorem for every `n ≥ 80 000`; the only
  remaining hypothesis is `ν_A{‖A₁‖_op ≤ O₁ and some node fails LowStat} ≤ 0.0006` at every World
  datum in the window.
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (tA BiasMomF BiasMomW windowW mkR node_bulk opSet measurableSet_opSet
  biasF biasW measurable_mkR)
open BstLean.Part153 (nuA)

variable {n : ℕ}

/-- The node statistics without the upper bound of `ς²`. -/
def LowStat (c : Ret n) (g : ℕ) : Prop :=
  SminN n ≤ vsig2 c (nodeS c g) ∧ DstN c g ≤ DmN n ∧ hUN c g ≤ DmN n ∧ V2N c g ≤ VmN n ∧
    piN c g ≤ PmN n

/-- **The statistics event on the operator event.** -/
def StatEvOp (n : ℕ) : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {p | OpB p.2 (O1n n) → ∀ g < Js n, LowStat (mkR p.1 (p.2, 0)) g}

lemma opN_le_of_OpB {k m : ℕ} {A : Matrix (Fin m) (Fin k) ℝ} {O : ℝ} (hO : 0 ≤ O) (h : OpB A O) :
    BstLean.Part152.opN A ≤ O := by
  refine BstLean.Part153.opN_le_of_forall A hO fun v => ?_
  unfold BstLean.Part153.nrm
  rw [← Real.sqrt_sq hO, ← Real.sqrt_mul (sq_nonneg O)]
  exact Real.sqrt_le_sqrt (h v)

/-- **On the operator event, `ς² ≤ 5/n`.** -/
lemma vsig2_upper (hn : 80000 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1)
    (h1 : OpB (A1 c) (O1n n)) : vsig2 c s ≤ SmaxN n := by
  have hle := vsig2_le (by omega) c hs
  have hop := opN_le_of_OpB (O1n_nonneg n) h1
  have hn0 : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hop2 : BstLean.Part152.opN (A1 c) ^ 2 ≤ O1n n ^ 2 :=
    pow_le_pow_left₀ (BstLean.Part152.opN_nonneg _) hop 2
  have hO2 : O1n n ^ 2 ≤ 2 * (n : ℝ) * (1 + 2 / 100) := by
    obtain ⟨hr, hr2, -, -, -, -, hO, -, -⟩ := r_facts hn
    rw [hO, mul_pow, Real.sq_sqrt (by norm_num)]
    set r := √(n : ℝ)
    rw [← hr2]
    nlinarith
  have hs0 : 0 ≤ 1 - s ^ 2 := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h1' : (1 - s ^ 2) * ((n : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      (n : ℝ) * (2 * (n : ℝ) * (1 + 2 / 100)) := by
    have a1 : 1 - s ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
    have a2 : (n : ℝ) * BstLean.Part152.opN (A1 c) ^ 2 ≤ (n : ℝ) * (2 * (n : ℝ) * (1 + 2 / 100)) :=
      mul_le_mul_of_nonneg_left (hop2.trans hO2) (by positivity)
    have a3 : 0 ≤ (n : ℝ) * BstLean.Part152.opN (A1 c) ^ 2 := by positivity
    nlinarith
  refine hle.trans ?_
  rw [hmA]
  unfold SmaxN
  calc 2 / (n : ℝ) ^ 2 * ((1 - s ^ 2) * ((n : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) / ((n : ℝ) - 1))
      ≤ 2 / (n : ℝ) ^ 2 * ((n : ℝ) * (2 * (n : ℝ) * (1 + 2 / 100)) / ((n : ℝ) - 1)) := by
        gcongr
    _ = (408 / 100) / ((n : ℝ) - 1) := by field_simp; ring
    _ ≤ 5 / (n : ℝ) := by
        rw [div_le_div_iff₀ hn1 (by positivity)]
        nlinarith

/-- **The location bias moments on `StatEvOp`.** -/
theorem biasMomF_statOp (hn : 80000 ≤ n) : BiasMomF (O1n n) (StatEvOp n) (4 / 1000) := by
  obtain ⟨h0, h1, h2, h3⟩ := numF hn
  have hS : StatEvOp n ∩ {p | p.2 ∈ opSet n (O1n n) ∧ windowW p.1} ⊆ StatEvN n := by
    rintro ⟨wr, A₁⟩ ⟨hG, hA, hw⟩ g hg
    obtain ⟨a, b, d, e, f⟩ := hG hA g hg
    exact ⟨a, vsig2_upper hn _ (node_bulk hn hw (A₁, 0) hg) hA, b, d, e, f⟩
  have H := biasMomF_of_stat hn (O1n_nonneg n) (SminN_pos (by omega)) hS (by norm_num)
    (by norm_num) z1_pow z2_pow h0 h1 h2 h3
  intro wr hw g hg A₁ hA hG
  exact H wr hw g hg A₁ hA ⟨hG, hA, hw⟩

/-- **The energy bias moments on `StatEvOp`.** -/
theorem biasMomW_statOp (hn : 80000 ≤ n) : BiasMomW (O1n n) (StatEvOp n) (2 / 100) := by
  obtain ⟨h0, h1, h2, h3⟩ := numW hn
  have hS : StatEvOp n ∩ {p | p.2 ∈ opSet n (O1n n) ∧ windowW p.1} ⊆ StatEvN n := by
    rintro ⟨wr, A₁⟩ ⟨hG, hA, hw⟩ g hg
    obtain ⟨a, b, d, e, f⟩ := hG hA g hg
    exact ⟨a, vsig2_upper hn _ (node_bulk hn hw (A₁, 0) hg) hA, b, d, e, f⟩
  have H := biasMomW_of_stat hn (O1n_nonneg n) (SminN_pos (by omega)) hS (by norm_num)
    (by norm_num) z1_pow z2_pow h0 h1 h2 h3
  intro wr hw g hg A₁ hA hG
  exact H wr hw g hg A₁ hA ⟨hG, hA, hw⟩

lemma measurableSet_LowStat (g : ℕ) : MeasurableSet {c : Ret n | LowStat c g} := by
  unfold LowStat
  exact ((((measurableSet_le measurable_const (measurable_vsig2_node g)).inter
    (measurableSet_le (measurable_DstN g) measurable_const)).inter
    (measurableSet_le (measurable_hUN g) measurable_const)).inter
    (measurableSet_le (measurable_V2N g) measurable_const)).inter
    (measurableSet_le (measurable_piN g) measurable_const) |>.congr (by
      ext c; simp only [mem_inter_iff, mem_ofPred_eq]; tauto)

/-- **`StatEvOp n` is measurable.** -/
theorem measurableSet_StatEvOp (n : ℕ) : MeasurableSet (StatEvOp n) := by
  have hC : Measurable (fun p : WRet n × Matrix (Fin (mA n)) (Fin n) ℝ => mkR p.1 (p.2, 0)) :=
    measurable_mkR.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have e : StatEvOp n = (Prod.snd ⁻¹' opSet n (O1n n))ᶜ ∪ ⋂ g ∈ Finset.range (Js n),
      (fun p : WRet n × Matrix (Fin (mA n)) (Fin n) ℝ => mkR p.1 (p.2, 0)) ⁻¹'
        {c | LowStat c g} := by
    ext p
    simp only [StatEvOp, mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage, mem_iInter,
      Finset.mem_range]
    constructor
    · intro h
      by_cases hA : OpB p.2 (O1n n)
      · exact Or.inr (h hA)
      · exact Or.inl hA
    · rintro (h | h) hA
      · exact absurd hA h
      · exact h
  rw [e]
  exact (measurable_snd (measurableSet_opSet (O1n n))).compl.union
    (Finset.measurableSet_biInter _ fun g _ => hC (measurableSet_LowStat g))

/-- **The classifier theorem with the bias moments proved** (every `n ≥ 80 000`). The only
remaining hypothesis: at every World datum in the window, the Agent probability that
`‖A₁‖_op ≤ O₁` and some node `g < J_s` fails `LowStat` is at most `0.0006`. -/
theorem classifier_paper_statOp80k (hn : 80000 ≤ n) (t : ℝ)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ StatEvOp n} ≤ 6 / 10000) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  BstLean.Part170.classifier_paper_bias_num80k hn t (measurableSet_StatEvOp n) hδG
    (biasMomF_statOp hn) (biasMomW_statOp hn)

end BstLean.Part171
