import BstLean.Part171Fin

/-!
# Part 171 (file `Gen`): the end theorem with free thresholds

No proof is left open; no `native_decide` or `axiom` is used.

For the next part (the charge of the statistics event) the thresholds can be chosen freely,
subject to the two numerical conditions of `biasMomF_of_stat` and `biasMomW_of_stat`. The upper
bound of `ς²` stays `5/n` (it follows from the operator event).

* `LowStatG c g Sm Dm Vm Pm`, `StatEvOpG n Sm Dm Vm Pm`; `measurableSet_StatEvOpG`.
* **`classifier_paper_gen80k`**: the classifier theorem for every `n ≥ 80 000`, every
  `Sm > 0`, `D_m`, `V_m`, `P_m` and `z₁, z₂ > 0` with `z₁⁸ ≥ 384`, `z₂⁸ ≥ 10 321 920` and the two
  numerical conditions; remaining hypothesis: the charge of `StatEvOpG` (`≤ 0.0006`).
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (tA BiasMomF BiasMomW windowW mkR node_bulk opSet measurableSet_opSet
  measurable_mkR)
open BstLean.Part153 (nuA)

variable {n : ℕ}

/-- The four node statistics with free thresholds. -/
def LowStatG (c : Ret n) (g : ℕ) (Sm Dm Vm Pm : ℝ) : Prop :=
  Sm ≤ vsig2 c (nodeS c g) ∧ DstN c g ≤ Dm ∧ V2N c g ≤ Vm ∧ piN c g ≤ Pm

/-- The statistics event with free thresholds, on the operator event. -/
def StatEvOpG (n : ℕ) (Sm Dm Vm Pm : ℝ) : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {p | OpB p.2 (O1n n) → ∀ g < Js n, LowStatG (mkR p.1 (p.2, 0)) g Sm Dm Vm Pm}

lemma statOpG_sub (hn : 80000 ≤ n) (Sm Dm Vm Pm : ℝ) :
    StatEvOpG n Sm Dm Vm Pm ∩ {p | p.2 ∈ opSet n (O1n n) ∧ windowW p.1} ⊆
      StatEv n Sm (SmaxN n) Dm Dm Vm Pm := by
  rintro ⟨wr, A₁⟩ ⟨hG, hA, hw⟩ g hg
  obtain ⟨a, b, d, f⟩ := hG hA g hg
  have hs := node_bulk hn hw (A₁, 0) hg
  have hU := hUN_eq_DstN (by omega) (mkR wr (A₁, 0)) g hs (O1n_nonneg n) hA
  exact ⟨a, vsig2_upper hn _ hs hA, b, hU ▸ b, d, f⟩

lemma measurableSet_StatEvOpG (n : ℕ) (Sm Dm Vm Pm : ℝ) :
    MeasurableSet (StatEvOpG n Sm Dm Vm Pm) := by
  have hC : Measurable (fun p : WRet n × Matrix (Fin (mA n)) (Fin n) ℝ => mkR p.1 (p.2, 0)) :=
    measurable_mkR.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hL : ∀ g, MeasurableSet {c : Ret n | LowStatG c g Sm Dm Vm Pm} := fun g => by
    unfold LowStatG
    exact (((measurableSet_le measurable_const (measurable_vsig2_node g)).inter
      (measurableSet_le (measurable_DstN g) measurable_const)).inter
      (measurableSet_le (measurable_V2N g) measurable_const)).inter
      (measurableSet_le (measurable_piN g) measurable_const) |>.congr (by
        ext c; simp only [mem_inter_iff, mem_ofPred_eq]; tauto)
  have e : StatEvOpG n Sm Dm Vm Pm = (Prod.snd ⁻¹' opSet n (O1n n))ᶜ ∪ ⋂ g ∈ Finset.range (Js n),
      (fun p : WRet n × Matrix (Fin (mA n)) (Fin n) ℝ => mkR p.1 (p.2, 0)) ⁻¹'
        {c | LowStatG c g Sm Dm Vm Pm} := by
    ext p
    simp only [StatEvOpG, mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage, mem_iInter,
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
    (Finset.measurableSet_biInter _ fun g _ => hC (hL g))

/-- **The classifier theorem with free thresholds** (every `n ≥ 80 000`). -/
theorem classifier_paper_gen80k (hn : 80000 ≤ n) (t : ℝ) {Sm Dm Vm Pm z₁ z₂ : ℝ} (hSm : 0 < Sm)
    (hz1 : 0 < z₁) (hz2 : 0 < z₂) (hz1' : 384 ≤ z₁ ^ 8) (hz2' : 10321920 ≤ z₂ ^ 8)
    (hF0 : 0 < AF0 √Sm (tA n * O1n n ^ 2 + SmaxN n) Dm Vm Pm)
    (hF1 : 0 < AF1 √Sm Dm Vm Pm (√(tA n) * O1n n)) (hF2 : 0 < AF2 √Sm Dm)
    (hF : ((n : ℝ) * ((mA n : ℕ) : ℝ)) ^ 4 * (AF0 √Sm (tA n * O1n n ^ 2 + SmaxN n) Dm Vm Pm +
      AF1 √Sm Dm Vm Pm (√(tA n) * O1n n) * z₁ + AF2 √Sm Dm * z₂) ^ 8 ≤ (4 / 1000) ^ 8)
    (hW0 : 0 < AW0 √Sm (tA n * O1n n ^ 2 + SmaxN n) Dm Vm Pm)
    (hW1 : 0 < AW1 √Sm √(SmaxN n) Dm Vm Pm (√(tA n) * O1n n))
    (hW2 : 0 < AW2 Dm Pm (√(tA n) * O1n n))
    (hW : ((mA n : ℕ) : ℝ) ^ 8 * (AW0 √Sm (tA n * O1n n ^ 2 + SmaxN n) Dm Vm Pm +
      AW1 √Sm √(SmaxN n) Dm Vm Pm (√(tA n) * O1n n) * z₁ +
      AW2 Dm Pm (√(tA n) * O1n n) * z₂) ^ 8 ≤ (2 / 100) ^ 8)
    (hδG : ∀ wr : WRet n, windowW wr →
      (nuA n).real {θ | (wr, θ.1) ∉ StatEvOpG n Sm Dm Vm Pm} ≤ 6 / 10000) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have HF := biasMomF_of_stat hn (O1n_nonneg n) hSm (statOpG_sub hn Sm Dm Vm Pm) hz1 hz2
    hz1' hz2' hF0 hF1 hF2 hF
  have HW := biasMomW_of_stat hn (O1n_nonneg n) hSm (statOpG_sub hn Sm Dm Vm Pm) hz1 hz2
    hz1' hz2' hW0 hW1 hW2 hW
  refine BstLean.Part170.classifier_paper_bias_num80k hn t (measurableSet_StatEvOpG n Sm Dm Vm Pm)
    hδG ?_ ?_
  · intro wr hw g hg A₁ hA hG
    exact HF wr hw g hg A₁ hA ⟨hG, hA, hw⟩
  · intro wr hw g hg A₁ hA hG
    exact HW wr hw g hg A₁ hA ⟨hG, hA, hw⟩

end BstLean.Part171
