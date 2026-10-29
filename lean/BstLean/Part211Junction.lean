import BstLean.Part211Parallel
import BstLean.Part211TL

/-! One source event supplies the full, parallel, energy and retained-noise bounds. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC bT)
open BstLean.Part153 (nrm hid2Mean_cr)
open BstLean.Part154 (csC bN eMP plow)
open BstLean.Part206 (energyRatio energyUpper meanLowerRoot)

noncomputable def hiddenCentre {n J : ℕ}
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : Fin (mA n) → ℝ := (rhoC c τ)⁻¹ • bT J J A M c τ

noncomputable def fullError {n J : ℕ}
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  (2 / (mA n : ℝ)) * normSq (hid2Mean_cr A M c τ - hiddenCentre (J := J) A M c τ) /
    (2 / (n : ℝ) / n)

noncomputable def parallelError {n J : ℕ}
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  |(√(2 / (mA n : ℝ)) • (hid2Mean_cr A M c τ - hiddenCentre (J := J) A M c τ)) ⬝ᵥ
    ((nrm (hiddenCentre (J := J) A M c τ))⁻¹ • hiddenCentre (J := J) A M c τ)| ^ 2 /
    (2 / (n : ℝ) / n)

noncomputable def hiddenEnergy {n J : ℕ}
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  (2 / (mA n : ℝ)) * normSq (bT J J A M c τ) / (2 / n * rhoC c τ ^ 2)

/-- The complete certificate contains only scalar formulas and interval guards. -/
structure CentreCertificate (n J : ℕ) (δe k k3 θlo Θ S MP qWorld : ℝ) (v : ℝ → ℝ) : Prop
    extends MomentCertificate n δe k k3 θlo Θ S v where
  delta_upper : δe ≤ 11 / 1000
  signal_domain : qWorld ∈ Icc (-1) 1
  energy_domain : energyRatio n (gMinus n) qWorld ≤ 1
  energy_root : 2 * √12 / (n : ℝ) < √(1 - 2 / (n : ℝ) ^ 2)
  energy_lower : 1 - δe ≤ gMinus n
  energy_upper : gPlus n ≤ 1 + δe
  relative_gap : eMP n δe (momentAllowance n csC δe k k3 Θ S) (bN n csC Θ) ≤ 1 / 10
  finite_guard : finiteEnergy n J δe / √(n : ℝ) < plow n (11 / 1000)
  lower_root : ∀ θ ∈ Icc θlo Θ, 0 ≤ meanLowerRoot n θ
  lower_bracket : ∀ θ ∈ Icc θlo Θ,
    0 ≤ kappa (meanLowerRoot n θ ^ 2 / gPlus n) - 2 / (n : ℝ) ^ 2
  lower_guard : ∀ θ ∈ Icc θlo Θ,
    0 ≤ √(gMinus n * (kappa (meanLowerRoot n θ ^ 2 / gPlus n) - 2 / (n : ℝ) ^ 2)) -
      2 * √(12 * gPlus n) / n - finiteEnergy n J δe / √(n : ℝ)
  upper_clip : energyUpper n (gMinus n) (gPlus n) (finiteEnergy n J δe) qWorld ≤ 1

/-- The complete S12 analytic junction, conditional on its scalar certificate. -/
theorem centre_formula_junction {n J : ℕ} (hn : 4096 ≤ n) (hn1 : n ≤ 16384) (hJ : 1 ≤ J)
    (c : Fin n → ℝ) (hc : 0 < normSq c) {τ δe k k3 θlo Θ S MP qWorld : ℝ}
    (hτ : 0 < τ) (hMP : 0 ≤ MP) (v : ℝ → ℝ)
    (C : CentreCertificate n J δe k k3 θlo Θ S MP qWorld v)
    (hθ : thetaC c τ ∈ Icc θlo Θ) (hWorld : 1 - thetaC c τ ≤ qWorld)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ} {M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hSource : (A, M) ∈ CentreSource n J c τ MP) :
    fullError (J := J) A M c τ ≤ fullFormula n J δe k k3 θlo Θ S MP ∧
    parallelError (J := J) A M c τ ≤ parallelFormula n J δe (momentAllowance n csC δe k k3 Θ S)
      (bN n csC Θ) (√(momentAllowance n csC δe k k3 Θ S) + sharpDeviation n csC δe θlo Θ) Θ MP ∧
    energyLower n (gMinus n) (gPlus n) (finiteEnergy n J δe) (thetaC c τ) ≤
      hiddenEnergy (J := J) A M c τ ∧
    hiddenEnergy (J := J) A M c τ ≤
      energyUpper n (gMinus n) (gPlus n) (finiteEnergy n J δe) qWorld ∧
    (2 / n) * (1 - energyUpper n (gMinus n) (gPlus n) (finiteEnergy n J δe) qWorld) ≤
      BstLean.Part150.sigT J J A M c τ ^ 2 ∧ hiddenCentre (J := J) A M c τ ≠ 0 := by
  have hn0 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpos : 0 < 2 / (n : ℝ) / n := by positivity
  have hf := full_error_on_source hn hn1 hJ c hc hτ hMP v C.toMomentCertificate hθ.1 hθ.2
    C.energy_root.le C.energy_lower C.energy_upper hSource.1
  have hp := parallel_error_on_source hn hn1 hJ c hc hτ hMP v C.toMomentCertificate C.delta_upper
    hθ.1 hθ.2 C.relative_gap C.finite_guard C.energy_root.le C.energy_lower C.energy_upper hSource
  have he := computed_energy_on_source (by omega : 2 ≤ n) hJ c hτ C.delta_nonneg C.signal_domain
    hWorld C.energy_root C.energy_upper C.energy_domain (C.lower_root _ hθ) (C.lower_bracket _ hθ)
    (C.lower_guard _ hθ) hSource.1.1
  have hs := retained_noise_energy hn0 A M c hτ C.upper_clip he.2
  refine ⟨?_, ?_, he.1, he.2, hs.2, hp.2.2⟩
  · exact (div_le_iff₀ hpos).mpr (by simpa only [hiddenCentre, mul_comm] using hf)
  · exact (div_le_iff₀ hpos).mpr (by simpa only [hiddenCentre, mul_comm] using hp.1)

/-- The six computed-centre conclusions share one probability payment. -/
theorem centre_formula_failure_charge {n J P : ℕ}
    (hn : 4096 ≤ n) (hn1 : n ≤ 16384) (hJ : 1 ≤ J) (hP : 1 ≤ P) (hnP : 2 * P + 1 < n)
    (c : Fin n → ℝ) (hc : 0 < normSq c) {τ δe k k3 θlo Θ S MP qWorld η : ℝ}
    (hτ : 0 < τ) (hMP : 0 < MP) (hη : 0 ≤ η) (v : ℝ → ℝ)
    (C : CentreCertificate n J δe k k3 θlo Θ S MP qWorld v)
    (hθ : thetaC c τ ∈ Icc θlo Θ) (hWorld : 1 - thetaC c τ ≤ qWorld) :
    (BstLean.Part153.nuA n).real
      {p : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
        fullError (J := J) p.1 p.2 c τ ≤ fullFormula n J δe k k3 θlo Θ S MP ∧
        parallelError (J := J) p.1 p.2 c τ ≤
          parallelFormula n J δe (momentAllowance n csC δe k k3 Θ S)
            (bN n csC Θ) (√(momentAllowance n csC δe k k3 Θ S) + sharpDeviation n csC δe θlo Θ) Θ MP ∧
        energyLower n (gMinus n) (gPlus n) (finiteEnergy n J δe) (thetaC c τ) ≤
          hiddenEnergy (J := J) p.1 p.2 c τ ∧
        hiddenEnergy (J := J) p.1 p.2 c τ ≤
          energyUpper n (gMinus n) (gPlus n) (finiteEnergy n J δe) qWorld ∧
        (2 / n) * (1 - energyUpper n (gMinus n) (gPlus n) (finiteEnergy n J δe) qWorld) ≤
          BstLean.Part150.sigT J J p.1 p.2 c τ ^ 2 ∧ hiddenCentre (J := J) p.1 p.2 c τ ≠ 0}ᶜ ≤
      exp (-(n : ℝ) / 2) + 3445 / (n : ℝ) ^ 2 + 13 * exp (-12) +
        (BstLean.Part153.jS n P η ^ 2 * n / (((n : ℝ) - 1 - 2 * P) * MP)) ^ P := by
  refine (measureReal_mono (μ := BstLean.Part153.nuA n) ?_).trans
    (centre_source_charge (J := J) hn hP hnP c hτ hMP hη C.ratio)
  intro p hp hSource
  exact hp (centre_formula_junction hn hn1 hJ c hc hτ hMP.le v C hθ hWorld hSource)

#print axioms centre_formula_junction
#print axioms centre_formula_failure_charge
end BstLean.Part211
