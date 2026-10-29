import BstLean.Part184LTop
import BstLean.Part179TopJN
import BstLean.Part177En
import BstLean.Part177EnMom

/-!
# Part 184 (file `LTopJ`): the top with the energy event and the certificate charge `4.5·10⁻⁵`.

No proof is left open; no `native_decide` or `axiom` is used.

A copy of the Part 184 `K` chain (floor 18 000) for every `n ≥ 17 750` (statistics cap `n ≤ 18 000`),
namespaces `….J1775` / `BstLean.Part184.L`. The constants above are those of the Lean statements; the
docstrings of copied lemmas can carry older numbers, and the Lean statements are authoritative.
-/

namespace BstLean.Part179.N30.N27.N26.N24.N23.N22.J1775.M

variable {n : ℕ}

section SJ
open BstLean.Part167
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part150 BstLean.Part156 BstLean.Part157
  BstLean.Part160
open BstLean.Part161 (muI Ix BIAS_hyp lamX sigX)
open BstLean.Part162 (dPaper psiA)
open BstLean.Part153 (nuA)
open BstLean.Part166 (psiK psiK_nonneg fK sK winC certI Cf Scert measurableSet_Scert
  markov12 measurable_psiK_f measurable_psiK_s goodD measurable_certI measurable_thetaC_key pow64_le
  integral_le_of_lintegral psiA_lam_eq psiA_sig_eq)
open BstLean.Part165 (goodC roomC roomC_ge)
open BstLean.Part164 (goodA window_goodA goodC16_of_goodA)
open BstLean.Part175.N50 (winC528 Scert528 measurableSet_Scert528 scert_of_good528 roomF roomF_ge)
variable {n : ℕ}


theorem classifier_paper_JM21H (hHQ : BstLean.Part184.L.HQG n) (hn : 17750 ≤ n) (hJM : JM_hyp n 5)
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ BstLean.Part179.N30.N27.N26.N25.roomK + BstLean.Part181.roomX + BstLean.Part184.L.roomL)
    (hB : ∀ c ∈ goodD n (paperDesign n fT wT hf hw) EA,
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (452 / 1000))
          (1 / 50) (by norm_num) (by norm_num)) (4288 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  set D := paperDesign n fT wT hf hw
  have hn16 : 16384 ≤ n := by omega
  have hLJ : LJae_hyp n 5 := LJae_of_JM (by omega) hJM
  set Een := agentEv D (BstLean.Part177.SEn n) with hEen
  have hEm : MeasurableSet Een := measurableSet_agentEv D (BstLean.Part177.measurableSet_SEn n)
  have hEc : (retDist (paperCentres n)).real Eenᶜ ≤ 1 / 10 ^ 6 := BstLean.Part177.SEn_ret_charge hn16 (BstLean.Part179.N30.N27.N26.N25.hmomN hn16) fT wT hf hw
  set EA₁ := EA ∩ Een with hEA₁
  have hEA₁m : MeasurableSet EA₁ := hEA.inter hEm
  have hA₁ : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EA₁ᶜ) ≤
      δA + 1 / 10 ^ 6 := by
    rw [hEA₁, Set.compl_inter, Set.inter_union_distrib_left]
    refine (measureReal_union_le _ _).trans (add_le_add hA ?_)
    exact (measureReal_mono Set.inter_subset_right).trans hEc
  have hS : MeasurableSet (agentEv D (Scert528 n)) :=
    measurableSet_agentEv D (measurableSet_Scert528 n)
  have hC := BstLean.Part179.N30.N27.N26.N24.N23.N22.J1775.M.cert_ret_charge528 hn hLJ fT wT hf hw
  refine classifier_paper_root22k hHQ hn fT wT hf hw t (hEA₁m.inter hS)
    (δA := δA + 1 / 10 ^ 6 + 45 / 10 ^ 6) ?_ ?_ (fun c hc => ?_) (fun c hc => ?_)
  · rw [Set.compl_inter, Set.inter_union_distrib_left]
    refine (measureReal_union_le _ _).trans (add_le_add hA₁ ?_)
    exact (measureReal_mono Set.inter_subset_right).trans hC
  · unfold BstLean.Part179.N30.N27.N26.N25.roomK at hroom; linarith
  · -- the eighth moment of `σ` from the energy event
    have hE : c ∈ Een := hc.2.1.2.1.1.1.1.1.2
    obtain ⟨hτ, -, -⟩ := window_goodA hn16 fT wT hf hw _ c hc
    exact BstLean.Part177.sg8_of_SEn (by omega) D hE hτ
  · -- `hc : c ∈ goodC n D ((EA₁ ∩ agentEv D (Scert528 n)) ∩ agentEv D (SXM40 n))`
    have hS0 : c ∈ agentEv D (Scert528 n) := hc.2.1.2.1.1.1.1.2
    have hcert := BstLean.Part179.N30.N27.N26.N24.N23.N22.J1775.M.certs_of_good528 hn fT wT hf hw hc hS0
    refine ⟨hcert.1, hcert.2, hB c ?_⟩
    have hSc : c ∈ agentEv D (Scert n) := scert_of_good528 hn16 fT wT hf hw hc hS0
    have hc1 : c ∈ goodD n D EA₁ :=
      ⟨hc.1, ⟨⟨hc.2.1.1, ⟨⟨⟨⟨hc.2.1.2.1.1.1.1.1, hSc⟩, hc.2.1.2.1.1.2⟩, hc.2.1.2.1.2⟩,
        hc.2.1.2.2⟩⟩, hc.2.2⟩⟩
    exact BstLean.Part175.goodC_mono (Set.inter_subset_inter_left _ Set.inter_subset_left) hc1

end SJ

end BstLean.Part179.N30.N27.N26.N24.N23.N22.J1775.M

open BstLean.Part179.N30.N27.N26.N24.N23.N22.J1775.M in
#print axioms classifier_paper_JM21H
