import BstLean.Part228Chernoff
import BstLean.Part162Final

/-! The removal, mixture, displacement, bias and tail roots retain their parameters. -/
namespace BstLean.Part228
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 (normSq)
open BstLean.Part157
open BstLean.Part161
open BstLean.Part162

noncomputable def bulkLower {n : ℕ} (D : Design n) (c : Ret n) : ℝ :=
  √(normSq c.1.2) / √(normSq c.1.2 + n * D.tau0 c ^ 2) -
    6 * D.tau0 c / √(normSq c.1.2 + n * D.tau0 c ^ 2)

noncomputable def bulkUpper {n : ℕ} (D : Design n) (c : Ret n) : ℝ :=
  √(normSq c.1.2) / √(normSq c.1.2 + n * D.tau0 c ^ 2) +
    6 * D.tau0 c / √(normSq c.1.2 + n * D.tau0 c ^ 2)

noncomputable def bulkTailMass {n : ℕ} (D : Design n) (c : Ret n) (tl tu : ℝ) : ℝ :=
  latitudeTailMass n (√(normSq c.1.2)) (D.tau0 c) (bulkLower D c) (bulkUpper D c) tl tu

noncomputable def bulkTailRoot {n : ℕ} (D : Design n) (c : Ret n) (tl tu : ℝ) : ℝ :=
  √(2 * bulkTailMass D c tl tu)

/-- These are analytic domains, not additional network events. -/
structure BulkChernoffDomain {n : ℕ} (D : Design n) (c : Ret n) (tl tu : ℝ) : Prop where
  tau_pos : 0 < D.tau0 c
  lower_pos : 0 < bulkLower D c
  lower_lt_one : bulkLower D c < 1
  upper_pos : 0 < bulkUpper D c
  upper_lt_one : bulkUpper D c < 1
  lower_tilt : tl ≤ 0
  upper_tilt : 0 ≤ tu
  lower_axial : 0 < 1 - 2 * tl * D.tau0 c ^ 2
  lower_transverse : 0 < 1 + 2 * tl * endpointRatio (bulkLower D c) * D.tau0 c ^ 2
  upper_axial : 0 < 1 - 2 * tu * D.tau0 c ^ 2
  upper_transverse : 0 < 1 + 2 * tu * endpointRatio (bulkUpper D c) * D.tau0 c ^ 2

theorem tail_hyp_chernoff {n : ℕ} (D : Design n) (c : Ret n) {tl tu : ℝ}
    (h : BulkChernoffDomain D c tl tu) : TAIL_hyp D c (bulkTailMass D c tl tu) := by
  have ht := latitude_interval_tail n (sqrt_nonneg (normSq c.1.2)) h.tau_pos h.lower_pos
    h.lower_lt_one h.upper_pos h.upper_lt_one h.lower_tilt h.upper_tilt
    h.lower_axial h.lower_transverse h.upper_axial h.upper_transverse
  exact ht

/-- The latitude-moment interface supplies the variable fluctuation root.
The tail root is its Chernoff value, with no fixed cap. -/
theorem replacement_root_latMom {n : ℕ} (hn : 2 ≤ n) (D : Design n) (t : ℝ) (c : Ret n)
    (hc : c.1.2 ≠ 0) {wl ws σl η CA tl tu hb : ℝ} {q : ℕ}
    (hwl : 0 < wl) (hws : 0 < ws) (hσl : 0 < σl) (hη0 : 0 < η) (hη1 : η < 1)
    (hcA : 0 < normSq c.2.1.2) (hCA : normSq c.2.1.2 ≤ CA)
    (hε : eps0 ws σl < 1) (P : LatMom D c σl q)
    (hB : BIAS_hyp D c (dPaper D c wl ws σl η hη0 hη1) hb)
    (hT : BulkChernoffDomain D c tl tu) :
    |√(QStand D t c) - √(qTilde D t c)| ≤
      rootFL wl ws η CA P + hb + bulkTailRoot D c tl tu := by
  have hF := fluct_of_latMom (by omega) D c hwl hws hσl hη0 hη1 hcA hCA hε P le_rfl
  exact repla_root_of_split hn D t c hc hT.tau_pos _ (fluct_of_chi D t c _ hF) hB
    (tail_hyp_chernoff D c hT)

/-- Scalar prices also give a root without the latitude-moment interface. -/
theorem replacement_root_prices {n : ℕ} (hn : 2 ≤ n) (D : Design n) (t : ℝ) (c : Ret n)
    (hc : c.1.2 ≠ 0) (d : SplitData n) {ε δ slow B C Dd hb tl tu : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hδ : 0 ≤ δ) (hslow : 0 < slow)
    (hwin : ∀ a ∈ keptIx D c d, slow ≤ d.S0 a ∧ ∀ v ∈ slice d a,
      |sA D c a v / d.S0 a - 1| ≤ ε ∧ |lA D c a v - d.lam0 a| ≤ δ)
    (hB : ∫ a, removed (BstLean.Part29.stdGauss (Fin (n - 1))) d.good a ∂muI n ≤ B)
    (hC : ∫ a in keptIx D c d, chiK D c d a ∂muI n ≤ C)
    (hD : ∫ a in keptIx D c d,
      hellG2 n ((d.lam0 a - d.lamb a) ^ 2 * normSq c.2.1.2) (d.S0 a) (d.Sb a)
        ∂muI n ≤ Dd)
    (hBias : BIAS_hyp D c d hb) (hT : BulkChernoffDomain D c tl tu) :
    |√(QStand D t c) - √(qTilde D t c)| ≤
      √(2 * (1 + d.eta⁻¹) * B) + √C + √Dd + hb + bulkTailRoot D c tl tu := by
  have hF : FLUCT_chi_hyp D c d ε δ slow
      (√(2 * (1 + d.eta⁻¹) * B) + √C + √Dd) :=
    ⟨hε0, hε1, hδ, hslow, hwin, B, C, Dd, hB, hC, hD, le_rfl⟩
  exact repla_root_of_split hn D t c hc hT.tau_pos d (fluct_of_chi D t c d hF) hBias
    (tail_hyp_chernoff D c hT)

theorem replacement_on_event {n : ℕ} (hn : 2 ≤ n) (D : Design n) (t H : ℝ)
    {E : Set (Ret n)}
    (h : ∀ c ∈ E, ∃ (d : SplitData n) (ε δ slow hfl hb tl tu : ℝ),
      c.1.2 ≠ 0 ∧ FLUCT_chi_hyp D c d ε δ slow hfl ∧ BIAS_hyp D c d hb ∧
        BulkChernoffDomain D c tl tu ∧ hfl + hb + bulkTailRoot D c tl tu ≤ H) :
    REPLA_mix_hyp D t H E := by
  intro c hc
  obtain ⟨d, ε, δ, slow, hfl, hb, tl, tu, hcentre, hF, hB, hT, hsum⟩ := h c hc
  exact (repla_root_of_split hn D t c hcentre hT.tau_pos d
    (fluct_of_chi D t c d hF) hB (tail_hyp_chernoff D c hT)).trans hsum

end BstLean.Part228
