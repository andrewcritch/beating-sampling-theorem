import BstLean.Part81D1A
import BstLean.Part81CoreW

/-!
# Part 81, map degree 1: the failure probability with the exact cancellation

At `d = 1` the sphere error is `τ² · R` with `R = E(W) − tr H · (ρ − 1)` a centred quadratic form
in the full Gaussian vector, `∫ R² ≤ 2‖H‖²/n`. This replaces the three separately bounded terms of
`fail81_coreW` by one.

* `D1.det1`: the deterministic step.
* `uw_fail1`: the failure probability in the split coordinates, on the good radius event.
* `fail81_core1`: the failure probability of `g₀` on the coefficient sphere, map degree 1.
-/

namespace BstLean.Part81.D1

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (DD)
open BstLean.Part78 (nsq frobH trH aU)
open BstLean.Part81

variable {n : ℕ}

/-- (iv) The deterministic step at map degree 1. -/
lemma det1 {τ VS VG1 VQ eS R Wfv v δ ε κ lam TQ θ β : ℝ}
    (hτ : |τ - 1| ≤ δ) (hδ : δ ≤ 1 / 100) (hβ : 0 < β)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hVQ0 : 0 ≤ VQ) (hv : 0 ≤ v) (hTQ : 0 ≤ TQ)
    (hθ : 0 ≤ θ)
    (hVS : τ ^ 2 * ((1 - lam) * VG1 - (1 / lam) * (τ - 1) ^ 2 * VQ) ≤ VS)
    (heS : eS = τ ^ 2 * R)
    (h1 : κ * Wfv ≤ VG1) (h2 : VQ ≤ TQ * v) (h3 : R ^ 2 ≤ θ * β * v) (h6 : β * v ≤ Wfv)
    (hnum : (1 + δ) ^ 2 * θ + ε ^ 2 * δ ^ 2 * TQ / (lam * β) ≤ ε ^ 2 * (1 - lam) * κ) :
    eS ^ 2 ≤ ε ^ 2 * VS := by
  obtain ⟨hτl, hτu⟩ := abs_le.mp hτ
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hτ
  have hτlo : 99 / 100 ≤ τ := by linarith
  have hd2 : (τ - 1) ^ 2 ≤ δ ^ 2 := by nlinarith
  have hτ2 : 0 ≤ τ ^ 2 := sq_nonneg _
  have hτ2u : τ ^ 2 ≤ (1 + δ) ^ 2 := by nlinarith
  have hW0 : 0 ≤ Wfv := le_trans (mul_nonneg hβ.le hv) h6
  have hR : R ^ 2 ≤ θ * Wfv := by
    have := mul_le_mul_of_nonneg_left h6 hθ
    nlinarith
  have hA : eS ^ 2 ≤ τ ^ 2 * ((1 + δ) ^ 2 * θ * Wfv) := by
    have e : eS ^ 2 = τ ^ 2 * (τ ^ 2 * R ^ 2) := by rw [heS]; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hτ2
    calc τ ^ 2 * R ^ 2 ≤ (1 + δ) ^ 2 * (θ * Wfv) :=
          mul_le_mul hτ2u hR (sq_nonneg _) (sq_nonneg _)
      _ = (1 + δ) ^ 2 * θ * Wfv := by ring
  have h6' : v ≤ Wfv / β := by rw [le_div_iff₀ hβ]; linarith
  have hlamVQ : (1 / lam) * (τ - 1) ^ 2 * VQ ≤ δ ^ 2 * TQ / (lam * β) * Wfv := by
    have a1 : (τ - 1) ^ 2 * VQ ≤ δ ^ 2 * (TQ * v) := mul_le_mul hd2 h2 hVQ0 (sq_nonneg _)
    have a2 : δ ^ 2 * (TQ * v) ≤ δ ^ 2 * (TQ * (Wfv / β)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h6' hTQ) (sq_nonneg _)
    have a3 := mul_le_mul_of_nonneg_left (a1.trans a2) (by positivity : (0 : ℝ) ≤ 1 / lam)
    have e : (1 / lam) * (τ - 1) ^ 2 * VQ = (1 / lam) * ((τ - 1) ^ 2 * VQ) := by ring
    have e' : δ ^ 2 * TQ / (lam * β) * Wfv = (1 / lam) * (δ ^ 2 * (TQ * (Wfv / β))) := by
      field_simp
    rw [e, e']; exact a3
  have hVS' : τ ^ 2 * ((1 - lam) * (κ * Wfv) - δ ^ 2 * TQ / (lam * β) * Wfv) ≤ VS := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hτ2) hVS
    have : (1 - lam) * (κ * Wfv) ≤ (1 - lam) * VG1 :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    linarith
  have hsc : (1 + δ) ^ 2 * θ * Wfv ≤
      ε ^ 2 * ((1 - lam) * (κ * Wfv) - δ ^ 2 * TQ / (lam * β) * Wfv) := by
    have a1 := mul_le_mul_of_nonneg_right hnum hW0
    have e : ε ^ 2 * δ ^ 2 * TQ / (lam * β) = ε ^ 2 * (δ ^ 2 * TQ / (lam * β)) := by ring
    rw [e] at a1
    nlinarith
  calc eS ^ 2 ≤ τ ^ 2 * ((1 + δ) ^ 2 * θ * Wfv) := hA
    _ ≤ τ ^ 2 * (ε ^ 2 * ((1 - lam) * (κ * Wfv) - δ ^ 2 * TQ / (lam * β) * Wfv)) :=
        mul_le_mul_of_nonneg_left hsc hτ2
    _ = ε ^ 2 * (τ ^ 2 * ((1 - lam) * (κ * Wfv) - δ ^ 2 * TQ / (lam * β) * Wfv)) := by ring
    _ ≤ ε ^ 2 * VS := mul_le_mul_of_nonneg_left hVS' (sq_nonneg _)

/-- (ii) The sphere error is `τ² · R` on the event `|τ − 1| ≤ δ ≤ 1/100`. -/
lemma err_exact (hn : 1 ≤ n) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (sD δ : ℝ)
    (hsD : sD ^ 2 = DD n 1) (hδ : δ ≤ 1 / 100) (p : (Fin n → ℝ) × (WIdx n 1 → ℝ))
    (hτ : |sD * Core.sOf p - 1| ≤ δ) :
    (sD * Core.sOf p) * errG (aU ℓ H p.1) H p.2 +
        (sD * Core.sOf p) * (sD * Core.sOf p - 1) * errG (aU 0 H p.1) H p.2 +
        eD 1 * trH H * ((sD * Core.sOf p) ^ 2 - 1) = (sD * Core.sOf p) ^ 2 * Rf H p := by
  have hD : 0 < DD n 1 := BstLean.Part36.DD_pos hn
  obtain ⟨hτl, hτu⟩ := abs_le.mp hτ
  set q := ∑ i, p.1 i ^ 2 + ∑ β, p.2 β ^ 2 with hq
  have hq0 : 0 ≤ q :=
    add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hs : Core.sOf p = 1 / Real.sqrt q := rfl
  have hqpos : 0 < q := by
    rcases hq0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [hs, ← h] at hτl
      simp at hτl
      linarith
  have hs2 : Core.sOf p ^ 2 = 1 / q := by
    rw [hs, div_pow, one_pow, Real.sq_sqrt hq0]
  have hτq : (sD * Core.sOf p) ^ 2 * q = DD n 1 := by
    rw [mul_pow, hsD, hs2]; field_simp
  rw [errG1 hn, errG1 hn, eD_one]
  unfold Rf
  rw [← hq]
  have e : (sD * Core.sOf p) ^ 2 * (QW H p.2 / n - trH H / DD n 1 * q) =
      (sD * Core.sOf p) ^ 2 * (QW H p.2 / n) - trH H / DD n 1 * ((sD * Core.sOf p) ^ 2 * q) := by
    ring
  rw [e, hτq]
  field_simp
  ring

end BstLean.Part81.D1

namespace BstLean.Part81

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU)
open BstLean.Part59 (polyEval TopNZ g0Q BP varP)
open BstLean.Part78 (nsq frobH trH qfun aU zv Phi markov_gt meas_le_ofReal nsq_nonneg
  frobH_nonneg trH_sq_le nsq_aU0_int GaussLin tau_close)

set_option maxHeartbeats 1600000 in
/-- **The failure probability in the split coordinates, on the good radius event**, map degree 1,
with the exact cancellation. -/
theorem uw_fail1 (n : ℕ) (hn : 1 ≤ n) {α β E2 UA Uv cW κ ε θ lam TQ δ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 < β) (hUA : 0 ≤ UA) (hUv : 0 ≤ Uv)
    (hM : MB n 1 α β 0 E2 UA Uv) (hV : VarBoundW n 1 α β cW) (hR : RegIface n 1)
    (hG : BstLean.Part78.GaussLin) (hcW : 0 ≤ cW)
    (hκ0 : 0 < κ) (hκ : κ < 1) (hθ : 0 < θ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hTQ : 0 < TQ) (hδ : δ ≤ 1 / 100)
    (hnum : (1 + δ) ^ 2 * θ + ε ^ 2 * δ ^ 2 * TQ / (lam * β) ≤ ε ^ 2 * (1 - lam) * κ)
    (f0 : ℝ) (ℓ₀ ℓ : Fin n → ℝ) (H₀ H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (hv : 0 < frobH H) (sD : ℝ) (hsD : sD ^ 2 = DD n 1)
    (hℓ : ∀ i, ℓ₀ i = sD * ℓ i) (hHs : ∀ i j, H₀ i j = DD n 1 * H i j) :
    ((stdGauss (Fin n)).prod (stdGauss (WIdx n 1))) {p | |sD * Core.sOf p - 1| ≤ δ ∧
      ε ^ 2 * varU (uniformSphere n)
          (fun x => qfun f0 ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i))) <
        ((∫ x, qfun f0 ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i)) ∂uniformSphere n) -
          (qfun f0 ℓ₀ H₀ (fun i => Core.sOf p * p.1 i) + eD 1 / DD n 1 * trH H₀)) ^ 2} ≤
      ENNReal.ofReal (2 / (n * β * θ) + cW / (n * (1 - κ) ^ 2) + (4 * UA + Uv) / TQ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hD : 0 < DD n 1 := BstLean.Part36.DD_pos hn
  set v := frobH H with hvdef
  set E12 : Set ((Fin n → ℝ) × (WIdx n 1 → ℝ)) :=
    {p | VG (aU ℓ H p.1) H p.2 < κ * Wf α β (aU ℓ H p.1) H} ∪
      {p | TQ * v < VG (aU 0 H p.1) H p.2} with hE12
  set E3 : Set ((Fin n → ℝ) × (WIdx n 1 → ℝ)) := {p | θ * β * v < D1.Rf H p ^ 2} with hE3
  have cV1 : Continuous (fun p : (Fin n → ℝ) × (WIdx n 1 → ℝ) => VG (aU ℓ H p.1) H p.2) :=
    (hR H).1.comp (Core.cont_aU ℓ H)
  have cV2 : Continuous (fun p : (Fin n → ℝ) × (WIdx n 1 → ℝ) => VG (aU 0 H p.1) H p.2) :=
    (hR H).1.comp (Core.cont_aU 0 H)
  have cWf := Core.cont_Wf (n := n) (d := 1) α β ℓ H
  have hEm : MeasurableSet E12 :=
    (measurableSet_lt cV1.measurable (continuous_const.mul cWf).measurable).union
      (measurableSet_lt measurable_const cV2.measurable)
  have hsub : {p : (Fin n → ℝ) × (WIdx n 1 → ℝ) | |sD * Core.sOf p - 1| ≤ δ ∧
      ε ^ 2 * varU (uniformSphere n)
          (fun x => qfun f0 ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i))) <
        ((∫ x, qfun f0 ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i)) ∂uniformSphere n) -
          (qfun f0 ℓ₀ H₀ (fun i => Core.sOf p * p.1 i) + eD 1 / DD n 1 * trH H₀)) ^ 2} ⊆
      E12 ∪ E3 := by
    intro p hp
    obtain ⟨hτ, hfail⟩ := hp
    by_contra hnot
    simp only [hE12, hE3, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hnot
    obtain ⟨⟨g1, g3⟩, gR⟩ := hnot
    obtain ⟨hVS, heS⟩ := Core.pw_core hn f0 ℓ₀ ℓ H₀ H hH sD (DD n 1) (Core.sOf p) hsD hD.ne' hℓ hHs
      p.1 p.2 lam hlam0
    rw [D1.err_exact hn ℓ H sD δ hsD hδ p hτ] at heS
    have h6 : β * v ≤ Wf α β (aU ℓ H p.1) H := by
      unfold Wf
      have := mul_nonneg hα (nsq_nonneg (aU ℓ H p.1))
      linarith
    have := D1.det1 (ε := ε) (κ := κ) (TQ := TQ) (θ := θ) hτ hδ hβ hlam0 hlam1
      (Core.VG_nonneg _ _ _) hv.le hTQ.le hθ.le hVS heS g1 g3 gR h6 hnum
    exact absurd hfail (not_lt.mpr this)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  -- the event on `R`
  obtain ⟨hRi, hRb⟩ := D1.secmom hn H hH
  have b3 : ((stdGauss (Fin n)).prod (stdGauss (WIdx n 1))) E3 ≤
      ENNReal.ofReal (2 * v / n / (θ * β * v)) :=
    markov_gt (μ := (stdGauss (Fin n)).prod (stdGauss (WIdx n 1)))
      (fun p => sq_nonneg (D1.Rf H p)) hRi (by positivity) hRb
  -- the two events on `V`
  have b12 : ((stdGauss (Fin n)).prod (stdGauss (WIdx n 1))) E12 ≤
      ENNReal.ofReal (cW / (n * (1 - κ) ^ 2) + (4 * UA + Uv) / TQ) := by
    rw [Measure.prod_apply hEm]
    set g : (Fin n → ℝ) → ℝ := fun u =>
      cW / (n * (1 - κ) ^ 2) + (UA * nsq (aU 0 H u) + Uv * v) / (TQ * v) with hg
    have hcond : ∀ u : Fin n → ℝ,
        stdGauss (WIdx n 1) (Prod.mk u ⁻¹' E12) ≤ ENNReal.ofReal (g u) := by
      intro u
      have hWpos : 0 < Wf α β (aU ℓ H u) H := by
        unfold Wf
        have := mul_nonneg hα (nsq_nonneg (aU ℓ H u))
        have := mul_pos hβ hv
        linarith
      have b1 := Core.cheb_floor hn hM hV hcW hκ0.le hκ (aU ℓ H u) H hH hWpos
      obtain ⟨hi1, -, -, -, -, hup⟩ := hM (aU 0 H u) H hH
      have b3 := markov_gt (μ := stdGauss (WIdx n 1)) (fun W => Core.VG_nonneg (aU 0 H u) H W) hi1
        (mul_pos hTQ hv) hup
      have hpre : Prod.mk u ⁻¹' E12 =
          {W | VG (aU ℓ H u) H W < κ * Wf α β (aU ℓ H u) H} ∪
            {W | TQ * v < VG (aU 0 H u) H W} := rfl
      rw [hpre]
      have ha := nsq_nonneg (aU 0 H u)
      have p2 : 0 ≤ cW / (n * (1 - κ) ^ 2) := by positivity
      have p3 : 0 ≤ (UA * nsq (aU 0 H u) + Uv * v) / (TQ * v) := by positivity
      rw [hg]
      simp only
      rw [ENNReal.ofReal_add p2 p3]
      exact (measure_union_le _ _).trans (add_le_add b1 b3)
    obtain ⟨hni, hnv⟩ := nsq_aU0_int hG H
    have hgi : Integrable g (stdGauss (Fin n)) := by
      rw [hg]
      exact (integrable_const _).add (((hni.const_mul _).add (integrable_const _)).div_const _)
    have hg0 : ∀ u, 0 ≤ g u := by
      intro u
      have ha := nsq_nonneg (aU 0 H u)
      rw [hg]; simp only
      have p2 : 0 ≤ cW / (n * (1 - κ) ^ 2) := by positivity
      have p3 : 0 ≤ (UA * nsq (aU 0 H u) + Uv * v) / (TQ * v) := by positivity
      linarith
    refine (lintegral_mono hcond).trans ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)]
    apply ENNReal.ofReal_le_ofReal
    apply le_of_eq
    have hgeq : ∀ u, g u = (cW / (n * (1 - κ) ^ 2) + (Uv * v) / (TQ * v)) +
        (UA / (TQ * v)) * nsq (aU 0 H u) := by
      intro u; rw [hg]; ring
    have hint : ∫ u, g u ∂stdGauss (Fin n) =
        (cW / (n * (1 - κ) ^ 2) + (Uv * v) / (TQ * v)) + (UA / (TQ * v)) * (4 * v) := by
      simp only [hgeq]
      rw [integral_add (integrable_const _) (hni.const_mul _), integral_const_mul, hnv]
      simp
      exact Or.inl hvdef.symm
    rw [hint]
    have hvne : v ≠ 0 := hv.ne'
    field_simp
    ring
  refine (add_le_add b12 b3).trans ?_
  have h1κ : 0 < 1 - κ := by linarith
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  have hvne : v ≠ 0 := hv.ne'
  field_simp
  ring

set_option maxHeartbeats 800000 in
/-- **Failure probability of `g₀` on the coefficient sphere**, map degree 1, with the exact
cancellation of the radial term. -/
theorem fail81_core1 (n : ℕ) (hn : 1 ≤ n) {α β E2 UA Uv cW κ ε θ lam TQ δ Rad : ℝ}
    (hα : 0 ≤ α) (hβ : 0 < β) (hE2 : 0 ≤ E2) (hUA : 0 ≤ UA) (hUv : 0 ≤ Uv)
    (hM : MB n 1 α β 0 E2 UA Uv) (hV : VarBoundW n 1 α β cW) (hcW : 0 ≤ cW)
    (hκ0 : 0 < κ) (hκ : κ < 1) (hθ : 0 < θ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hTQ : 0 < TQ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 100) (hRad0 : 0 ≤ Rad)
    (hRad : stdGauss (CoefIdxD n 1) {Z | δ ^ 2 < ((∑ α, Z α ^ 2) / DD n 1 - 1) ^ 2} ≤
      ENNReal.ofReal Rad)
    (hnum : (1 + δ) ^ 2 * θ + ε ^ 2 * δ ^ 2 * TQ / (lam * β) ≤ ε ^ 2 * (1 - lam) * κ)
    (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n 1) {Z | Z ≠ 0 ∧
      ε ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n 1 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal (Rad + (2 / (n * β * θ) + cW / (n * (1 - κ) ^ 2) + (4 * UA + Uv) / TQ)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨ℓ₀, H₀, hH₀, hpoly, htop, hg0⟩ := coefBridge n 1 c
  have hD : 0 < DD n 1 := BstLean.Part36.DD_pos hn
  set D := DD n 1 with hDdef
  set sD := Real.sqrt D with hsDdef
  have hsD0 : 0 < sD := Real.sqrt_pos.mpr hD
  have hsD : sD ^ 2 = D := Real.sq_sqrt hD.le
  set ℓ : Fin n → ℝ := fun i => ℓ₀ i / sD with hℓdef
  set H : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => H₀ i j / D with hHdef
  have hH : H.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [hHdef, Matrix.of_apply]
    rw [hH₀.apply j i]
  have hℓ : ∀ i, ℓ₀ i = sD * ℓ i := fun i => by simp only [hℓdef]; field_simp
  have hHs : ∀ i j, H₀ i j = D * H i j := fun i j => by
    simp only [hHdef, Matrix.of_apply]; field_simp
  have hv : 0 < frobH H := by
    have h0 := htop hc
    have : frobH H = frobH H₀ / D ^ 2 := by
      unfold frobH
      simp only [hHdef, Matrix.of_apply, div_pow]
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_div]
    rw [this]; positivity
  set UW : Set ((Fin n → ℝ) × (WIdx n 1 → ℝ)) := {p | |sD * Core.sOf p - 1| ≤ δ ∧
      ε ^ 2 * varU (uniformSphere n)
          (fun x => qfun (c default) ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i))) <
        ((∫ x, qfun (c default) ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i))
            ∂uniformSphere n) -
          (qfun (c default) ℓ₀ H₀ (fun i => Core.sOf p * p.1 i) + eD 1 / D * trH H₀)) ^ 2}
    with hUW
  have hsub : {Z : CoefIdxD n 1 → ℝ | Z ≠ 0 ∧
      ε ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n 1 2 c (unitOfD Z)) ^ 2} ⊆
      {Z | δ ^ 2 < ((∑ α, Z α ^ 2) / D - 1) ^ 2} ∪ (Br.combEquiv n 1).symm ⁻¹' UW := by
    intro Z hZ
    obtain ⟨hZ0, hfail⟩ := hZ
    by_cases hr : δ ^ 2 < ((∑ α, Z α ^ 2) / D - 1) ^ 2
    · exact Or.inl hr
    right
    simp only [Set.mem_preimage]
    set p := (Br.combEquiv n 1).symm Z with hp
    have hZp : Br.combEquiv n 1 (p.1, p.2) = Z := by
      show Br.combEquiv n 1 p = Z
      rw [hp]; exact (Br.combEquiv n 1).apply_symm_apply Z
    obtain ⟨f1, f2, f3⟩ := Br.comb_facts (n := n) (d := 1) p.1 p.2
    rw [hZp] at f1 f2 f3
    have hq : 0 < ∑ α, Z α ^ 2 := by
      by_contra hc0
      apply hZ0
      have h0 : ∑ α, Z α ^ 2 = 0 :=
        le_antisymm (not_lt.mp hc0) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      funext α
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h0 α
        (Finset.mem_univ α)
      simpa using this
    have hs : Core.sOf p = 1 / Real.sqrt (∑ α, Z α ^ 2) := by unfold Core.sOf; rw [f3]
    have hunit : unitOfD Z = Core.sOf p • Z := by unfold unitOfD; rw [hs]
    have hτ : |sD * Core.sOf p - 1| ≤ δ := by
      rw [hs]
      exact tau_close hq hD hδ0.le (by linarith) (not_lt.mp hr)
    have hmap : ∀ x : Fin n → ℝ, polyEval 2 c (mapMD (Core.sOf p • Z) x) =
        qfun (c default) ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i)) := by
      intro x
      rw [hpoly]
      congr 1
      funext i
      rw [BstLean.Part52.mapMD_smul, f2]
    have hcol : colM (Core.sOf p • Z) default = fun i => Core.sOf p * p.1 i := by
      funext i
      have := congrFun f1 i
      simp only [colM, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [this]
    refine ⟨hτ, ?_⟩
    have e1 : varP (uniformSphere n) 2 c (unitOfD Z) = varU (uniformSphere n)
        (fun x => qfun (c default) ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i))) := by
      unfold varP; rw [hunit]; simp only [hmap]
    have e2 : BP (uniformSphere n) 2 c (unitOfD Z) =
        ∫ x, qfun (c default) ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i))
          ∂uniformSphere n := by
      unfold BP; rw [hunit]; simp only [hmap]
    have e3 : g0Q n 1 2 c (unitOfD Z) =
        qfun (c default) ℓ₀ H₀ (fun i => Core.sOf p * p.1 i) + eD 1 / D * trH H₀ := by
      rw [hunit, hg0, hcol]
    rw [e1, e2, e3] at hfail
    exact hfail
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hpre : stdGauss (CoefIdxD n 1) ((Br.combEquiv n 1).symm ⁻¹' UW) =
      ((stdGauss (Fin n)).prod (stdGauss (WIdx n 1))) UW := by
    rw [← (Br.combEquiv_preserving (n := n) (d := 1)).measure_preimage_equiv,
      ← Set.preimage_comp]
    simp
  have huw := uw_fail1 n hn (cW := cW) (κ := κ) (ε := ε) (θ := θ) (lam := lam) (TQ := TQ) (δ := δ)
    hα hβ hUA hUv hM hV (regIface n 1 hn) BstLean.Part78.gaussLin hcW
    hκ0 hκ hθ hlam0 hlam1 hTQ hδ hnum
    (c default) ℓ₀ ℓ H₀ H hH hv sD hsD hℓ hHs
  rw [hpre]
  refine (add_le_add hRad huw).trans ?_
  have h1κ : 0 < 1 - κ := by linarith
  rw [← ENNReal.ofReal_add hRad0 (by positivity)]

end BstLean.Part81

#print axioms BstLean.Part81.D1.errG_indep
#print axioms BstLean.Part81.D1.err_exact
#print axioms BstLean.Part81.D1.secmom
#print axioms BstLean.Part81.D1.det1
#print axioms BstLean.Part81.uw_fail1
#print axioms BstLean.Part81.fail81_core1
