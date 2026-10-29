import BstLean.Part78Transfer

/-!
# Part 78: the probability bound in the split coordinates `(u, W)`

`uw_fail`: on the event `|√𝒟/r − 1| ≤ δ`, the set of `(u, W)` where the sphere program fails has
probability at most the sum of the four conditional tails (floor, error, and the two tails of the
homogeneous part), integrated over `u`.
-/

namespace BstLean.Part78

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (varU)

variable {n : ℕ}

lemma VG_nonneg (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n → ℝ) : 0 ≤ VG a H W := by
  unfold VG varU; exact integral_nonneg fun _ => sq_nonneg _

lemma cont_aU (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun p : (Fin n → ℝ) × (WIdx n → ℝ) => (aU ℓ H p.1, p.2)) := by
  refine Continuous.prodMk ?_ continuous_snd
  refine continuous_pi fun i => ?_
  unfold aU
  exact continuous_const.add (continuous_const.mul (continuous_finsetSum _ fun j _ =>
    continuous_const.mul ((continuous_apply j).comp continuous_fst)))

lemma cont_Wf (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun p : (Fin n → ℝ) × (WIdx n → ℝ) => Wf (aU ℓ H p.1) H) := by
  unfold Wf nsq
  refine (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)).add continuous_const
  exact (((continuous_apply i).comp (continuous_fst.comp (cont_aU ℓ H)))).pow 2

lemma aU0_sq (H : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (i : Fin n) :
    (aU 0 H u i) ^ 2 = (∑ j, (2 * H i j) * u j) * (∑ j, (2 * H i j) * u j) := by
  unfold aU
  simp only [Pi.zero_apply, zero_add]
  have : 2 * ∑ j, H i j * u j = ∑ j, (2 * H i j) * u j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]; ring

lemma nsq_aU0_int (hG : GaussLin) (H : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun u : Fin n → ℝ => nsq (aU 0 H u)) (stdGauss (Fin n)) ∧
    ∫ u, nsq (aU 0 H u) ∂stdGauss (Fin n) = 4 * frobH H := by
  unfold nsq
  simp only [aU0_sq]
  refine ⟨integrable_finsetSum _ fun i _ => (hG (Fin n) _ _).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => (hG (Fin n) _ _).1]
  unfold frobH
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hG (Fin n) _ _).2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `1/r` in the split coordinates. -/
noncomputable def sOf (p : (Fin n → ℝ) × (WIdx n → ℝ)) : ℝ :=
  1 / Real.sqrt (∑ i, p.1 i ^ 2 + ∑ β, p.2 β ^ 2)

set_option maxHeartbeats 1600000 in
/-- **The failure probability in the split coordinates, on the good radius event.** -/
theorem uw_fail (hn : 1000 ≤ n) {S2 cW c1 κ ε ε₁ lam TQ T2 δ : ℝ}
    (hS : SphereConsts n S2) (hS2 : S2 ≤ 5) (hS20 : 0 ≤ S2)
    (hM : MeanIds n) (hV : VarBoundW n cW) (hR : RegIface n) (hG : GaussLin) (hcW : 0 ≤ cW)
    (hc1 : 2 / 3 ≤ c1) (hc1' : 2 * S2 + 9 / 4 ≤ 449 / 100 * c1)
    (hκ0 : 0 < κ) (hκ : κ < 1) (hε₁ : 0 < ε₁) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hTQ : 0 < TQ) (hT2 : 0 < T2) (hδ : δ ≤ 1 / 100)
    (hnum : 11 / 10 * ε₁ ^ 2 + (22 * δ ^ 2 * T2 + 207 * δ ^ 2 * (n : ℝ) + ε ^ 2 * δ ^ 2 * TQ / lam)
      * (100 / 449) ≤ ε ^ 2 * (1 - lam) * κ)
    (f0 : ℝ) (ℓ₀ ℓ : Fin n → ℝ) (H₀ H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (hv : 0 < frobH H) (sD D : ℝ) (hsD : sD ^ 2 = D) (hD : D ≠ 0)
    (hℓ : ∀ i, ℓ₀ i = sD * ℓ i) (hHs : ∀ i j, H₀ i j = D * H i j) :
    ((stdGauss (Fin n)).prod (stdGauss (WIdx n))) {p | |sD * sOf p - 1| ≤ δ ∧
      ε ^ 2 * varU (uniformSphere n)
          (fun x => qfun f0 ℓ₀ H₀ (fun i => sOf p * (p.1 i + zv p.2 (pf x) i))) <
        ((∫ x, qfun f0 ℓ₀ H₀ (fun i => sOf p * (p.1 i + zv p.2 (pf x) i)) ∂uniformSphere n) -
          (qfun f0 ℓ₀ H₀ (fun i => sOf p * p.1 i) + 3 / 2 / D * trH H₀)) ^ 2} ≤
      ENNReal.ofReal (c1 / (n * ε₁ ^ 2) + cW / (n * (1 - κ) ^ 2) +
        (151 / 100 * 4 + 53 / 10) / TQ + (4 + (2 * S2 + 9 / 4)) / (n * T2)) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set v := frobH H with hvdef
  -- the bad set
  set E : Set ((Fin n → ℝ) × (WIdx n → ℝ)) :=
    (({p | VG (aU ℓ H p.1) H p.2 < κ * Wf (aU ℓ H p.1) H} ∪
      {p | ε₁ ^ 2 * Wf (aU ℓ H p.1) H < errG (aU ℓ H p.1) H p.2 ^ 2}) ∪
      {p | TQ * v < VG (aU 0 H p.1) H p.2}) ∪
      {p | T2 * v < errG (aU 0 H p.1) H p.2 ^ 2} with hE
  have cV1 : Continuous (fun p : (Fin n → ℝ) × (WIdx n → ℝ) => VG (aU ℓ H p.1) H p.2) :=
    (hR H).1.comp (cont_aU ℓ H)
  have cE1 : Continuous (fun p : (Fin n → ℝ) × (WIdx n → ℝ) => errG (aU ℓ H p.1) H p.2) :=
    (hR H).2.comp (cont_aU ℓ H)
  have cV2 : Continuous (fun p : (Fin n → ℝ) × (WIdx n → ℝ) => VG (aU 0 H p.1) H p.2) :=
    (hR H).1.comp (cont_aU 0 H)
  have cE2 : Continuous (fun p : (Fin n → ℝ) × (WIdx n → ℝ) => errG (aU 0 H p.1) H p.2) :=
    (hR H).2.comp (cont_aU 0 H)
  have cWf := cont_Wf (n := n) ℓ H
  have hEm : MeasurableSet E := by
    refine (((measurableSet_lt cV1.measurable (continuous_const.mul cWf).measurable).union
      (measurableSet_lt (continuous_const.mul cWf).measurable (cE1.pow 2).measurable)).union
      (measurableSet_lt measurable_const cV2.measurable)).union
      (measurableSet_lt measurable_const (cE2.pow 2).measurable)
  -- the failure set is inside `E`
  have hsub : {p : (Fin n → ℝ) × (WIdx n → ℝ) | |sD * sOf p - 1| ≤ δ ∧
      ε ^ 2 * varU (uniformSphere n)
          (fun x => qfun f0 ℓ₀ H₀ (fun i => sOf p * (p.1 i + zv p.2 (pf x) i))) <
        ((∫ x, qfun f0 ℓ₀ H₀ (fun i => sOf p * (p.1 i + zv p.2 (pf x) i)) ∂uniformSphere n) -
          (qfun f0 ℓ₀ H₀ (fun i => sOf p * p.1 i) + 3 / 2 / D * trH H₀)) ^ 2} ⊆ E := by
    intro p hp
    obtain ⟨hτ, hfail⟩ := hp
    by_contra hnot
    simp only [hE, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hnot
    obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := hnot
    obtain ⟨hVS, heS⟩ := pw_core hn1 f0 ℓ₀ ℓ H₀ H hH sD D (sOf p) hsD hD hℓ hHs p.1 p.2 lam hlam0
    have h6 : v ≤ 100 / 449 * Wf (aU ℓ H p.1) H := by
      unfold Wf; nlinarith [nsq_nonneg (aU ℓ H p.1)]
    have := det_core (ε := ε) (κ := κ) (ε₁ := ε₁) (TQ := TQ) (T2 := T2) hτ hδ hlam0 hlam1
      (VG_nonneg _ _ _) hv.le hTQ.le hT2.le hnpos.le hVS heS g1 g3 g4 g2 (trH_sq_le H) h6 hnum
    exact absurd hfail (not_lt.mpr this)
  refine (measure_mono hsub).trans ?_
  have : IsProbabilityMeasure (stdGauss (Fin n)) := inferInstance
  rw [Measure.prod_apply hEm]
  -- the conditional bound
  set e := 2 * S2 + 9 / 4 with he
  set g : (Fin n → ℝ) → ℝ := fun u =>
    c1 / (n * ε₁ ^ 2) + cW / (n * (1 - κ) ^ 2) +
      (151 / 100 * nsq (aU 0 H u) + 53 / 10 * v) / (TQ * v) +
      ((nsq (aU 0 H u) + e * v) / n) / (T2 * v) with hg
  have hc10 : 0 ≤ c1 := by linarith
  have he0 : 0 ≤ e := by rw [he]; linarith
  have hcond : ∀ u : Fin n → ℝ, stdGauss (WIdx n) (Prod.mk u ⁻¹' E) ≤ ENNReal.ofReal (g u) := by
    intro u
    have hWpos : 0 < Wf (aU ℓ H u) H := by unfold Wf; nlinarith [nsq_nonneg (aU ℓ H u)]
    have b1 := cheb_floor hn hS hS2 hM hV hcW hκ0.le hκ (aU ℓ H u) H hH hWpos
    have b2 := markov_err hn (T := ε₁ ^ 2) hS hM hc1 hc1' (by positivity) (aU ℓ H u) H hH hWpos
    obtain ⟨hi1, -, hi3, -, -⟩ := hM (aU 0 H u) H hH
    have b3 := markov_gt (μ := stdGauss (WIdx n)) (fun W => VG_nonneg (aU 0 H u) H W) hi1
      (mul_pos hTQ hv) (mean_upper hn hS hM (aU 0 H u) H hH)
    have b4 := markov_gt (μ := stdGauss (WIdx n)) (fun W => sq_nonneg (errG (aU 0 H u) H W)) hi3
      (mul_pos hT2 hv) (err_le hn hS hM (aU 0 H u) H hH)
    have hpre : Prod.mk u ⁻¹' E =
        (({W | VG (aU ℓ H u) H W < κ * Wf (aU ℓ H u) H} ∪
          {W | ε₁ ^ 2 * Wf (aU ℓ H u) H < errG (aU ℓ H u) H W ^ 2}) ∪
          {W | TQ * v < VG (aU 0 H u) H W}) ∪
          {W | T2 * v < errG (aU 0 H u) H W ^ 2} := rfl
    rw [hpre]
    have ha := nsq_nonneg (aU 0 H u)
    have p1 : 0 ≤ c1 / (n * ε₁ ^ 2) := by positivity
    have p2 : 0 ≤ cW / (n * (1 - κ) ^ 2) := by positivity
    have p3 : 0 ≤ (151 / 100 * nsq (aU 0 H u) + 53 / 10 * v) / (TQ * v) := by positivity
    have p4 : 0 ≤ ((nsq (aU 0 H u) + e * v) / n) / (T2 * v) := by positivity
    rw [hg]
    simp only
    rw [ENNReal.ofReal_add (by positivity) p4, ENNReal.ofReal_add (by positivity) p3,
      ENNReal.ofReal_add p1 p2]
    refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
      (add_le_add ((measure_union_le _ _).trans ?_) b3)) b4)
    rw [add_comm]
    exact add_le_add b2 b1
  obtain ⟨hni, hnv⟩ := nsq_aU0_int hG H
  have hgi : Integrable g (stdGauss (Fin n)) := by
    rw [hg]
    exact ((integrable_const _).add (((hni.const_mul _).add (integrable_const _)).div_const _)).add
      (((hni.add (integrable_const _)).div_const _).div_const _)
  have hg0 : ∀ u, 0 ≤ g u := by
    intro u
    have ha := nsq_nonneg (aU 0 H u)
    rw [hg]; simp only
    have p1 : 0 ≤ c1 / (n * ε₁ ^ 2) := by positivity
    have p2 : 0 ≤ cW / (n * (1 - κ) ^ 2) := by positivity
    have p3 : 0 ≤ (151 / 100 * nsq (aU 0 H u) + 53 / 10 * v) / (TQ * v) := by positivity
    have p4 : 0 ≤ ((nsq (aU 0 H u) + e * v) / n) / (T2 * v) := by positivity
    linarith
  refine (lintegral_mono hcond).trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  have hgeq : ∀ u, g u = (c1 / (n * ε₁ ^ 2) + cW / (n * (1 - κ) ^ 2) +
      (53 / 10 * v) / (TQ * v) + (e * v / n) / (T2 * v)) +
      (151 / 100 / (TQ * v) + 1 / n / (T2 * v)) * nsq (aU 0 H u) := by
    intro u; rw [hg]; ring
  have hint : ∫ u, g u ∂stdGauss (Fin n) =
      (c1 / (n * ε₁ ^ 2) + cW / (n * (1 - κ) ^ 2) +
      (53 / 10 * v) / (TQ * v) + (e * v / n) / (T2 * v)) +
      (151 / 100 / (TQ * v) + 1 / n / (T2 * v)) * (4 * v) := by
    simp only [hgeq]
    rw [integral_add (integrable_const _) (hni.const_mul _), integral_const_mul, hnv]
    simp
    exact Or.inl hvdef.symm
  rw [hint]
  have hvne : v ≠ 0 := hv.ne'
  field_simp
  ring

end BstLean.Part78

#print axioms BstLean.Part78.uw_fail
