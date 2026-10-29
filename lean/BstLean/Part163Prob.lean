import BstLean.Part163Comb

/-!
# Part 163 (file `Prob`): the free-event theorem in probability form

Do not use `sorry`, `native_decide` or `axiom`.

* `measurable_QStand`, `measurable_qTilde`: `Q` and `q̃` are measurable functions of the retained
  data.
* `replaSet D t h_A = {c | |√Q(c) − √q̃(c)| ≤ h_A}` (measurable).
* **`classifier_paper_free23_prob`**: for `paperDesign` and every `n ≥ 23 000`: IF the Agent
  replacement root fails with probability at most `roomA` (`≥ 0.003059`) on
  `HP n ∩ E_{θ−} ∩ E_{θ+} ∩ Eframe D`, THEN success `≥ 99/100`. The hypothesis is one number: the
  probability of a measurable set. It holds as soon as `REPLA_mix_hyp` holds outside a set of that
  probability, so it is not vacuous in the way of Part 160's `classifier_paper_comb23`.
-/

namespace BstLean.Part163

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160

variable {n : ℕ}

lemma measurable_hStand_joint (D : Design n) :
    Measurable (fun p : Ret n × (Fin n → ℝ) => hStand D p.1 p.2) := by
  have hx : Measurable (fun p : Ret n × (Fin n → ℝ) => sphPt (p.1.1.2 + D.tau0 p.1 • p.2)) :=
    measurable_sphPt.comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).add
      ((D.mtau0.comp measurable_fst).smul measurable_snd))
  have hA : Measurable (fun p : Ret n × (Fin n → ℝ) => p.1.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_fst))
  exact (BstLean.Part136.continuous_hid2_joint (N := n) (m := mA n)).measurable.comp (hA.prodMk hx)

/-- `Q` is a measurable function of the retained data. -/
theorem measurable_QStand (D : Design n) (t : ℝ) : Measurable (fun c => QStand D t c) := by
  set E : Set (Ret n × ((Fin n → ℝ) × (Fin n → ℝ))) :=
    {x | classifier x.1.2.2 t (lam (D.bA x.1.1 x.1.2.1.1) (hStand D x.1 x.2.1) • x.1.2.1.2 +
      sig (2 / (mA n : ℝ)) (D.bA x.1.1 x.1.2.1.1) (hStand D x.1 x.2.1) • x.2.2)} with hEd
  have hb : Measurable (fun x : Ret n × ((Fin n → ℝ) × (Fin n → ℝ)) => D.bA x.1.1 x.1.2.1.1) :=
    D.mbA.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_fst))))
  have hh : Measurable (fun x : Ret n × ((Fin n → ℝ) × (Fin n → ℝ)) => hStand D x.1 x.2.1) :=
    (measurable_hStand_joint D).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hl := measurable_lam_joint.comp (hb.prodMk hh)
  have hs := (measurable_sig_joint (2 / (mA n : ℝ))).comp (hb.prodMk hh)
  have hcA : Measurable (fun x : Ret n × ((Fin n → ℝ) × (Fin n → ℝ)) => x.1.2.1.2) :=
    measurable_snd.comp (measurable_fst.comp (measurable_snd.comp measurable_fst))
  have hy : Measurable (fun x : Ret n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      lam (D.bA x.1.1 x.1.2.1.1) (hStand D x.1 x.2.1) • x.1.2.1.2 +
        sig (2 / (mA n : ℝ)) (D.bA x.1.1 x.1.2.1.1) (hStand D x.1 x.2.1) • x.2.2) :=
    (hl.smul hcA).add (hs.smul (measurable_snd.comp measurable_snd))
  have hF : Measurable (fun x : Ret n × ((Fin n → ℝ) × (Fin n → ℝ)) => x.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hE : MeasurableSet E :=
    measurableSet_lt measurable_const
      ((measurable_pi_apply 0).comp (continuous_mlpEval_joint.measurable.comp (hF.prodMk hy)))
  have h := measurable_measure_prodMk_left (ν := (stdGauss (Fin n)).prod (stdGauss (Fin n))) hE
  exact ENNReal.measurable_toReal.comp h

/-- `q̃` is a measurable function of the retained data. -/
theorem measurable_qTilde (D : Design n) (t : ℝ) : Measurable (fun c => qTilde D t c) :=
  ((measurable_hitFn D t).stronglyMeasurable.integral_prod_right' (ν := drawMeas n)).measurable

/-- The set of retained values where the Agent replacement root `h_A` holds. -/
def replaSet (D : Design n) (t hA : ℝ) : Set (Ret n) :=
  {c | |√(QStand D t c) - √(qTilde D t c)| ≤ hA}

theorem measurableSet_replaSet (D : Design n) (t hA : ℝ) : MeasurableSet (replaSet D t hA) :=
  measurableSet_le ((((measurable_QStand D t).sqrt).sub ((measurable_qTilde D t).sqrt)).abs)
    measurable_const

/-- **The free-event classifier theorem in probability form (every `n ≥ 23 000`).** IF the Agent
replacement root `h_A` fails with probability at most `δ_A ≤ roomA` (`roomA ≥ 0.003059`) on the
event `HP n ∩ E_{θ−} ∩ E_{θ+} ∩ Eframe D`, THEN the program succeeds with probability at least
`99/100`. -/
theorem classifier_paper_free23_prob (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩
      Eframe (paperDesign n fT wT hf hw) ∩ (replaSet (paperDesign n fT wT hf hw) t hAL)ᶜ) ≤ δA)
    (hroom : δA ≤ roomA) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  set D := paperDesign n fT wT hf hw
  set EA := replaSet D t hAL ∪ (Eframe D)ᶜ with hEAd
  have hEA : MeasurableSet EA :=
    (measurableSet_replaSet D t hAL).union (measurableSet_Eframe (by omega) D).compl
  have hset : BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
      BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ = BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩
      Eframe D ∩ (replaSet D t hAL)ᶜ := by
    ext c
    simp only [hEAd, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_union, not_or, not_not]
    tauto
  refine classifier_paper_free23 hn fT wT hf hw t hEA (δA := δA) (by rw [hset]; exact hA) hroom ?_
  intro c hc
  have h1 : c ∈ EA := hc.2.1.2
  have h2 : c ∈ Eframe D := hc.2.2
  rcases h1 with h | h
  · exact h
  · exact absurd h2 h

end BstLean.Part163

open BstLean.Part163 in
#print axioms measurable_QStand
open BstLean.Part163 in
#print axioms measurable_qTilde
open BstLean.Part163 in
#print axioms classifier_paper_free23_prob
