import BstLean.Part162BD
import BstLean.Part160Comb
import BstLean.Part161Final

/-!
# Part 162: the classifier theorem with the latitude-moment interface

Role: `delegations/statements/p162-spec.md`, items 3 and 4. Do not use `sorry`, `native_decide`
or `axiom`.

* `LatMom D c σ_l q`: the latitude-moment interface (the conclusions of Proposition
  `t7:p07:LG` and of the mass bound `t7:p07:mass-low` for `λ`, `σ`, `S`), as a structure.
* `rootFL`: the Lean form of `h_fl = √(2β_tot) + √𝒞 + √𝒟`.
* **`fluct_of_latMom`**: `FLUCT_chi_hyp` for `dPaper` from `LatMom`, `|c_A|² ≤ C_A`, `ε₀ < 1`,
  `rootFL ≤ h_fl`.
* **`classifier_paper_mom`**: Part 160's `classifier_paper_comb23` with `REPLA_mix_hyp` replaced
  by: on the good set, `LatMom`, the norm bound, `rootFL ≤ 0.002159` and `BIAS_hyp` (for `dPaper`)
  at `0.004295`.
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157
open BstLean.Part161

variable {n : ℕ}

/-- **The latitude-moment interface** (the conclusions of Proposition `t7:p07:LG` and of the mass
bound `t7:p07:mass-low`, written for `λ`, `σ`, `S = σ²` on the latitude spheres): the constants
and the inequalities used by `fluct_paper_mom`. -/
structure LatMom (D : Design n) (c : Ret n) (σl : ℝ) (q : ℕ) where
  Vs : ℝ
  Vl : ℝ
  VS : ℝ
  ts8 : ℝ
  ts12 : ℝ
  tl8 : ℝ
  tl12 : ℝ
  tlq : ℝ
  tsq : ℝ
  βlow : ℝ
  hVs0 : 0 ≤ Vs
  hVl0 : 0 ≤ Vl
  hVS0 : 0 ≤ VS
  hts8 : 0 < ts8
  hts12 : 0 < ts12
  htl8 : 0 < tl8
  htl12 : 0 < tl12
  htlq : 0 ≤ tlq
  htsq : 0 ≤ tsq
  hβl : 0 ≤ βlow
  hVs : ∫ a, (∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ Vs ^ 2
  hVl : ∫ a, (∫ v, (lA D c a v - lbar D c a) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ Vl ^ 2
  hVS : ∫ a, (∫ v, (sA D c a v - ∫ w, sA D c a w ∂stdGauss (Fin (n - 1))) ^ 2
    ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ VS ^ 2
  hs8 : ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ ts8 ^ 8
  hs12 : ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ ts12 ^ 12
  hl8 : ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tl8 ^ 8
  hl12 : ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tl12 ^ 12
  hlq : ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ q ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tlq ^ q
  hsq : ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ q ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tsq ^ q
  hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA D c a v < σl} ∂muI n ≤ βlow

/-- **The fluctuation root `h_fl` in Lean form**: `√(2(1 + 1/η)B) + √𝒞 + √𝒟`. -/
noncomputable def rootFL {D : Design n} {c : Ret n} {σl : ℝ} {q : ℕ} (wl ws η CA : ℝ)
    (P : LatMom D c σl q) : ℝ :=
  √(2 * (1 + η⁻¹) * Bpap wl ws P.tlq P.tsq P.βlow q) +
    √(priceC (1 - eps0 ws σl ^ 2)⁻¹ n (√CA * (2 * wl) / σl)
      (eps0 ws σl) (exp ((1 - eps0 ws σl ^ 2)⁻¹ * (n * eps0 ws σl ^ 2 / 2 +
        (√CA * (2 * wl) / σl) ^ 2 * (1 + eps0 ws σl))))
      (cVw ws σl * ((1 - η)⁻¹ * P.Vs)) (CA / σl ^ 2 * ((1 - η)⁻¹ * P.Vl))
      (cEw ws σl * ((iotaP η 8 + c2η η + c3η η ws σl) * P.ts8))
      (√CA / σl * ((iotaP η 8 + c2η η) * P.tl8))
      (cEw ws σl * ((iotaP η 12 + c2η η + c3η η ws σl) * P.ts12))
      (√CA / σl * ((iotaP η 12 + c2η η) * P.tl12))) +
    √(Dpap n (Bpap wl ws P.tlq P.tsq P.βlow q) CA P.Vl P.VS η σl)

/-- `FLUCT_chi_hyp` from the latitude-moment interface. -/
theorem fluct_of_latMom (hn : 1 ≤ n) (D : Design n) (c : Ret n) {wl ws σl η : ℝ} (hwl : 0 < wl)
    (hws : 0 < ws) (hσl : 0 < σl) (h0 : 0 < η) (h1 : η < 1) (hcA : 0 < normSq c.2.1.2)
    {CA : ℝ} (hCA : normSq c.2.1.2 ≤ CA) (hε : eps0 ws σl < 1) {q : ℕ} (P : LatMom D c σl q)
    {hfl : ℝ} (hsum : rootFL wl ws η CA P ≤ hfl) :
    FLUCT_chi_hyp D c (dPaper D c wl ws σl η h0 h1) (eps0 ws σl) (2 * wl) (σl ^ 2) hfl :=
  fluct_paper_mom hn D c hwl hws hσl h0 h1 hcA hCA hε q P.hVs0 P.hVl0 P.hVS0 P.hts8 P.hts12
    P.htl8 P.htl12 P.htlq P.htsq P.hβl P.hVs P.hVl P.hVS P.hs8 P.hs12 P.hl8 P.hl12 P.hlq P.hsq
    P.hmass hsum

open BstLean.Part130 BstLean.Part156 BstLean.Part159 BstLean.Part160 in
/-- **The classifier theorem for the paper's design, every `n ≥ 23 000`, with the Agent
replacement reduced to the latitude-moment interface and the bias hypothesis.** On the good set
of `classifier_paper_comb23`, for every retained value `c` there are a width, a floor, `η`, a norm
bound `|c_A|² ≤ C_A`, the latitude moments `P` with `rootFL ≤ 0.002159`, and `BIAS_hyp` for the
paper's split data at `0.004295`. -/
theorem classifier_paper_mom (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    (hM : ∀ c ∈ goodSet (HP n) (Ethm (paperCentres n) ∩ Ethp (paperCentres n))
        (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (wl ws σl η CA : ℝ) (q : ℕ) (h0 : 0 < η) (h1 : η < 1)
        (P : LatMom (paperDesign n fT wT hf hw) c σl q),
        0 < wl ∧ 0 < ws ∧ 0 < σl ∧ 0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ CA ∧
        eps0 ws σl < 1 ∧ rootFL wl ws η CA P ≤ 2159 / 10 ^ 6 ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_paper_comb23 hn fT wT hf hw t ?_
  refine repla_of_hyps_chi (by omega) _ t (fun c hc => ?_) (fun c hc => ?_)
  · exact window_paper (by omega) fT wT hf hw hc.1.1 hc.2.1 hc.2.2
  · obtain ⟨wl, ws, σl, η, CA, q, h0, h1, P, hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩ := hM c hc
    exact ⟨dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1, eps0 ws σl, 2 * wl, σl ^ 2,
      fluct_of_latMom (by omega) _ c hwl hws hσl h0 h1 hcA hCA hε P hroot, hbias⟩

end BstLean.Part162

open BstLean.Part162 in
#print axioms fluct_of_latMom
open BstLean.Part162 in
#print axioms classifier_paper_mom
