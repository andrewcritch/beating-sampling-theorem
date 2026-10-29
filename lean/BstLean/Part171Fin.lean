import BstLean.Part171Red

/-!
# Part 171 (file `Fin`): the end theorem with four node statistics

No proof is left open; no `native_decide` or `axiom` is used.

By `hUN_eq_DstN` the condition on `hUN` is implied by the condition on `DstN`. So the
statistics event needs only four conditions per node.

* `LowStat2 c g`: `1/(5n) ≤ ς²`, `DstN ≤ 16/n³`, `V2N ≤ 64/n⁴`, `piN ≤ 1/n⁴`.
* `StatEvOp2 n = {(wr, A₁) | ‖A₁‖_op ≤ O₁ → ∀ g < J_s, LowStat2}`; it is measurable.
* **`classifier_paper_final80k`**: the classifier theorem for every `n ≥ 80 000`; the only
  remaining hypothesis is the charge of `StatEvOp2 n` (`≤ 0.0006`) in the window.
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (tA BiasMomF BiasMomW windowW mkR node_bulk opSet measurableSet_opSet
  measurable_mkR)
open BstLean.Part153 (nuA)

variable {n : ℕ}

/-- The four node statistics. -/
def LowStat2 (c : Ret n) (g : ℕ) : Prop :=
  SminN n ≤ vsig2 c (nodeS c g) ∧ DstN c g ≤ DmN n ∧ V2N c g ≤ VmN n ∧ piN c g ≤ PmN n

/-- **The statistics event with four conditions, on the operator event.** -/
def StatEvOp2 (n : ℕ) : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {p | OpB p.2 (O1n n) → ∀ g < Js n, LowStat2 (mkR p.1 (p.2, 0)) g}

lemma statOp2_sub (hn : 80000 ≤ n) :
    StatEvOp2 n ∩ {p | p.2 ∈ opSet n (O1n n) ∧ windowW p.1} ⊆ StatEvN n := by
  rintro ⟨wr, A₁⟩ ⟨hG, hA, hw⟩ g hg
  obtain ⟨a, b, d, f⟩ := hG hA g hg
  have hs := node_bulk hn hw (A₁, 0) hg
  have hU := hUN_eq_DstN (by omega) (mkR wr (A₁, 0)) g hs (O1n_nonneg n) hA
  exact ⟨a, vsig2_upper hn _ hs hA, b, hU ▸ b, d, f⟩

theorem biasMomF_statOp2 (hn : 80000 ≤ n) : BiasMomF (O1n n) (StatEvOp2 n) (4 / 1000) := by
  obtain ⟨h0, h1, h2, h3⟩ := numF hn
  have H := biasMomF_of_stat hn (O1n_nonneg n) (SminN_pos (by omega)) (statOp2_sub hn)
    (by norm_num) (by norm_num) z1_pow z2_pow h0 h1 h2 h3
  intro wr hw g hg A₁ hA hG
  exact H wr hw g hg A₁ hA ⟨hG, hA, hw⟩

theorem biasMomW_statOp2 (hn : 80000 ≤ n) : BiasMomW (O1n n) (StatEvOp2 n) (2 / 100) := by
  obtain ⟨h0, h1, h2, h3⟩ := numW hn
  have H := biasMomW_of_stat hn (O1n_nonneg n) (SminN_pos (by omega)) (statOp2_sub hn)
    (by norm_num) (by norm_num) z1_pow z2_pow h0 h1 h2 h3
  intro wr hw g hg A₁ hA hG
  exact H wr hw g hg A₁ hA ⟨hG, hA, hw⟩

lemma measurableSet_LowStat2 (g : ℕ) : MeasurableSet {c : Ret n | LowStat2 c g} := by
  unfold LowStat2
  exact (((measurableSet_le measurable_const (measurable_vsig2_node g)).inter
    (measurableSet_le (measurable_DstN g) measurable_const)).inter
    (measurableSet_le (measurable_V2N g) measurable_const)).inter
    (measurableSet_le (measurable_piN g) measurable_const) |>.congr (by
      ext c; simp only [mem_inter_iff, mem_ofPred_eq]; tauto)

theorem measurableSet_StatEvOp2 (n : ℕ) : MeasurableSet (StatEvOp2 n) := by
  have hC : Measurable (fun p : WRet n × Matrix (Fin (mA n)) (Fin n) ℝ => mkR p.1 (p.2, 0)) :=
    measurable_mkR.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have e : StatEvOp2 n = (Prod.snd ⁻¹' opSet n (O1n n))ᶜ ∪ ⋂ g ∈ Finset.range (Js n),
      (fun p : WRet n × Matrix (Fin (mA n)) (Fin n) ℝ => mkR p.1 (p.2, 0)) ⁻¹'
        {c | LowStat2 c g} := by
    ext p
    simp only [StatEvOp2, mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage, mem_iInter,
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
    (Finset.measurableSet_biInter _ fun g _ => hC (measurableSet_LowStat2 g))

/-- **The classifier theorem with the bias moments proved** (every `n ≥ 80 000`). The only
remaining hypothesis: at every World datum in the window, the Agent probability that
`‖A₁‖_op ≤ O₁` and some node `g < J_s` fails one of `1/(5n) ≤ ς²`, `DstN ≤ 16/n³`,
`V2N ≤ 64/n⁴`, `piN ≤ 1/n⁴` is at most `0.0006`. -/
theorem classifier_paper_final80k (hn : 80000 ≤ n) (t : ℝ)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ StatEvOp2 n} ≤ 6 / 10000) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  BstLean.Part170.classifier_paper_bias_num80k hn t (measurableSet_StatEvOp2 n) hδG
    (biasMomF_statOp2 hn) (biasMomW_statOp2 hn)

end BstLean.Part171
