import BstLean.Part171End

/-!
# Part 171 (file `Meas`): the statistics event is measurable

No proof is left open; no `native_decide` or `axiom` is used.

* `measurable_DstN`, `measurable_hUN`, `measurable_V2N`, `measurable_piN`: the node statistics
  are measurable functions of the retained value.
* **`measurableSet_StatEv`**, **`measurableSet_StatEvN`**: the statistics event is a measurable
  set of pairs (World data, `A₁`).
* **`classifier_paper_statN80k`**: the end theorem with `Gb = StatEvN n`; the only remaining
  hypothesis is the charge of `StatEvN n` in the World window.
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part134 (res lam)
open BstLean.Part167 (perp)
open BstLean.Part170 (hB tA aLat windowW mkR measurable_mkR)
open BstLean.Part153 (nuA)

variable {n : ℕ}

lemma measurable_perp_joint {m : ℕ} :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => perp p.1 p.2) := by
  unfold perp
  have h1 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => (normSq p.1)⁻¹) :=
    (BstLean.Part130.continuous_normSq.measurable.comp measurable_fst).inv
  have h2 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => ∑ j, p.2 j * p.1 j) := by fun_prop
  exact measurable_snd.sub ((h1.mul h2).smul measurable_fst)

lemma measurable_res_joint {m : ℕ} :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => res p.1 p.2) := by
  unfold res lam
  have h1 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => normSq p.1) :=
    BstLean.Part130.continuous_normSq.measurable.comp measurable_fst
  have h2 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => ∑ j, p.2 j * p.1 j) := by fun_prop
  exact measurable_snd.sub ((h2.div h1).smul measurable_fst)

lemma measurable_hB : Measurable (fun c : Ret n => hB c) := by
  have hx : Measurable (fun c : Ret n =>
      (((c.1.2, tau0p c.1.1), c.2.1.1) : ((Fin n → ℝ) × ℝ) × BstLean.Part136.HidParam n (mA n))) :=
    (((measurable_snd.comp measurable_fst).prodMk
      (measurable_tau0p.comp (measurable_fst.comp measurable_fst))).prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd)))
  have h := (BstLean.Part150.measurable_hT (n := n) (m := mA n) n).comp hx
  unfold hB
  exact h

lemma measurable_aLat_joint (g : ℕ) :
    Measurable (fun p : Ret n × (Fin (n - 1) → ℝ) => aLat p.1 (nodeS p.1 g) p.2) :=
  measurable_pi_iff.mpr fun i => measurable_relu_row measurable_fst
    ((measurable_nodeS g).comp measurable_fst) measurable_snd i

lemma measurable_a1Bar_node (g : ℕ) : Measurable (fun c : Ret n => a1Bar c (nodeS c g)) :=
  measurable_pi_iff.mpr fun i => measurable_a1Bar_comp measurable_id (measurable_nodeS g) i

lemma measurable_vsig2_node (g : ℕ) : Measurable (fun c : Ret n => vsig2 c (nodeS c g)) :=
  measurable_vsig2_comp measurable_id (measurable_nodeS g)

lemma measurable_wT_joint (g : ℕ) :
    Measurable (fun p : Ret n × (Fin (n - 1) → ℝ) => wT p.1 g p.2) := by
  unfold wT
  have hh : Measurable (fun p : Ret n × (Fin (n - 1) → ℝ) => hB p.1) := measurable_hB.comp measurable_fst
  have hr : Measurable (fun p : Ret n × (Fin (n - 1) → ℝ) => res (hB p.1) (a1Bar p.1 (nodeS p.1 g))) :=
    measurable_res_joint.comp (hh.prodMk ((measurable_a1Bar_node g).comp measurable_fst))
  have hp1 : Measurable (fun p : Ret n × (Fin (n - 1) → ℝ) => perp (hB p.1) (aLat p.1 (nodeS p.1 g) p.2)) :=
    measurable_perp_joint.comp (hh.prodMk (measurable_aLat_joint g))
  exact measurable_const.mul (BstLean.Part130.continuous_normSq.measurable.comp
    (measurable_perp_joint.comp (hr.prodMk hp1)))

lemma measurable_q1_joint : Measurable (fun p : Ret n × (Fin (mA n) → ℝ) => q1 p.1 p.2) := by
  unfold q1
  have hh : Measurable (fun p : Ret n × (Fin (mA n) → ℝ) => hB p.1) := measurable_hB.comp measurable_fst
  have hN : Measurable (fun p : Ret n × (Fin (mA n) → ℝ) => normSq (hB p.1)) :=
    BstLean.Part130.continuous_normSq.measurable.comp hh
  have hd : Measurable (fun p : Ret n × (Fin (mA n) → ℝ) => hB p.1 ⬝ᵥ p.2) :=
    ((continuous_fst.dotProduct continuous_snd).measurable).comp (hh.prodMk measurable_snd)
  exact (hN.inv.mul hd).mul (measurable_const.mul hN.sqrt)

lemma measurable_q2_joint (g : ℕ) :
    Measurable (fun p : Ret n × (Fin (mA n) → ℝ) => q2 p.1 g p.2) := by
  unfold q2
  have hh : Measurable (fun p : Ret n × (Fin (mA n) → ℝ) => hB p.1) := measurable_hB.comp measurable_fst
  have hr : Measurable (fun p : Ret n × (Fin (mA n) → ℝ) => res (hB p.1) (a1Bar p.1 (nodeS p.1 g))) :=
    measurable_res_joint.comp (hh.prodMk ((measurable_a1Bar_node g).comp measurable_fst))
  have hN : Measurable (fun p : Ret n × (Fin (mA n) → ℝ) =>
      normSq (res (hB p.1) (a1Bar p.1 (nodeS p.1 g)))) :=
    BstLean.Part130.continuous_normSq.measurable.comp hr
  have hy : Measurable (fun p : Ret n × (Fin (mA n) → ℝ) => res (hB p.1) p.2) :=
    measurable_res_joint.comp (hh.prodMk measurable_snd)
  have hd : Measurable (fun p : Ret n × (Fin (mA n) → ℝ) =>
      res (hB p.1) (a1Bar p.1 (nodeS p.1 g)) ⬝ᵥ res (hB p.1) p.2) :=
    ((continuous_fst.dotProduct continuous_snd).measurable).comp (hr.prodMk hy)
  exact (hN.inv.mul hd).mul (measurable_const.mul hN.sqrt)

lemma measurable_DstN (g : ℕ) : Measurable (fun c : Ret n => DstN c g) := by
  unfold DstN
  have hy : Measurable (fun p : Ret n × (Fin (n - 1) → ℝ) =>
      aLat p.1 (nodeS p.1 g) p.2 - a1Bar p.1 (nodeS p.1 g)) :=
    (measurable_aLat_joint g).sub ((measurable_a1Bar_node g).comp measurable_fst)
  have h1 := (measurable_q1_joint (n := n)).comp (measurable_fst.prodMk hy)
  have h2 := (measurable_q2_joint (n := n) g).comp (measurable_fst.prodMk hy)
  exact measurable_int_dir ((h1.pow_const 2).add (h2.pow_const 2))

lemma measurable_hUN (g : ℕ) : Measurable (fun c : Ret n => hUN c g) := by
  unfold hUN
  exact (measurable_int_dir ((measurable_wT_joint g).sub
    ((measurable_vsig2_node g).comp measurable_fst))).abs

lemma measurable_V2N (g : ℕ) : Measurable (fun c : Ret n => V2N c g) := by
  unfold V2N
  exact measurable_int_dir (((measurable_wT_joint g).sub
    ((measurable_vsig2_node g).comp measurable_fst)).pow_const 2)

lemma measurable_piN (g : ℕ) : Measurable (fun c : Ret n => piN c g) := by
  unfold piN
  have hS : MeasurableSet {p : Ret n × (Fin (n - 1) → ℝ) | wT p.1 g p.2 < vsig2 p.1 (nodeS p.1 g) / 2} :=
    measurableSet_lt (measurable_wT_joint g) (((measurable_vsig2_node g).comp measurable_fst).div_const 2)
  have h := measurable_measure_prodMk_left (ν := stdGauss (Fin (n - 1))) hS
  simp only [Measure.real]
  exact h.ennreal_toReal

lemma measurableSet_NodeStat (g : ℕ) (Smin Smax Dm Hm Vm Pm : ℝ) :
    MeasurableSet {c : Ret n | NodeStat c g Smin Smax Dm Hm Vm Pm} := by
  have e : {c : Ret n | NodeStat c g Smin Smax Dm Hm Vm Pm} =
      {c | Smin ≤ vsig2 c (nodeS c g)} ∩ {c | vsig2 c (nodeS c g) ≤ Smax} ∩
        {c | DstN c g ≤ Dm} ∩ {c | hUN c g ≤ Hm} ∩ {c | V2N c g ≤ Vm} ∩ {c | piN c g ≤ Pm} := by
    ext c
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · intro H; exact ⟨⟨⟨⟨⟨H.hS1, H.hS2⟩, H.hD⟩, H.hH⟩, H.hV⟩, H.hP⟩
    · rintro ⟨⟨⟨⟨⟨a, b⟩, d⟩, h⟩, v⟩, p⟩; exact ⟨a, b, d, h, v, p⟩
  rw [e]
  exact (((((measurableSet_le measurable_const (measurable_vsig2_node g)).inter
    (measurableSet_le (measurable_vsig2_node g) measurable_const)).inter
    (measurableSet_le (measurable_DstN g) measurable_const)).inter
    (measurableSet_le (measurable_hUN g) measurable_const)).inter
    (measurableSet_le (measurable_V2N g) measurable_const)).inter
    (measurableSet_le (measurable_piN g) measurable_const)

/-- **The statistics event is measurable.** -/
theorem measurableSet_StatEv (Smin Smax Dm Hm Vm Pm : ℝ) :
    MeasurableSet (StatEv n Smin Smax Dm Hm Vm Pm) := by
  have hC : Measurable (fun p : WRet n × Matrix (Fin (mA n)) (Fin n) ℝ => mkR p.1 (p.2, 0)) :=
    measurable_mkR.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have e : StatEv n Smin Smax Dm Hm Vm Pm = ⋂ g ∈ Finset.range (Js n),
      (fun p : WRet n × Matrix (Fin (mA n)) (Fin n) ℝ => mkR p.1 (p.2, 0)) ⁻¹'
        {c | NodeStat c g Smin Smax Dm Hm Vm Pm} := by
    ext p
    simp only [StatEv, mem_ofPred_eq, mem_iInter, mem_preimage, Finset.mem_range]
  rw [e]
  exact Finset.measurableSet_biInter _ fun g _ => hC (measurableSet_NodeStat g _ _ _ _ _ _)

theorem measurableSet_StatEvN (n : ℕ) : MeasurableSet (StatEvN n) := measurableSet_StatEv _ _ _ _ _ _

/-- **The classifier theorem with the bias moments proved and `Gb = StatEvN n`** (every
`n ≥ 80 000`). The only remaining hypothesis is the charge of the statistics event `StatEvN n`
(`≤ 0.0006`) at every World datum in the window. -/
theorem classifier_paper_statN80k (hn : 80000 ≤ n) (t : ℝ)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ StatEvN n} ≤ 6 / 10000) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_stat80k hn t (measurableSet_StatEvN n) subset_rfl hδG

end BstLean.Part171
