import BstLean.Part291FrameScalar
import BstLean.Part252MomentNum

namespace BstLean.BlueprintLow
open Real Set BstLean.Part215 BstLean.Part255 BstLean.Part188 BstLean.Part222

/-- Rational enclosures for a continuum rectangle. Every field is checked by Lean. -/
structure FrameEnvelopeWitness (nlo nhi : ℕ) (Θ full E : ℝ) (p : Parameters)
    (pair outside bad cp2 cp4 cp12 : ℝ) where
  eRoot : ℝ
  xiRoot : ℝ
  s : ℝ
  mu : ℝ
  Y : ℝ
  r1 : ℝ
  r2 : ℝ
  D2 : ℝ
  D4 : ℝ
  delta : ℝ
  W2 : ℝ
  shell : ℝ
  cov : ℝ
  schur : ℝ
  G1 : ℝ
  G2 : ℝ
  G3 : ℝ
  cap : ℝ
  V : ℝ
  gap : ℝ
  mass : ℝ
  rootN : ℝ
  rootB : ℝ
  rootU : ℝ
  rootV : ℝ
  nonneg : 0 ≤ eRoot ∧ 0 ≤ xiRoot ∧ 0 ≤ s ∧ 0 ≤ mu ∧ 0 ≤ r1 ∧ 0 ≤ r2 ∧
    0 ≤ D2 ∧ 0 ≤ D4 ∧ 0 ≤ delta ∧ 0 ≤ W2 ∧ 0 ≤ shell ∧ 0 ≤ cov ∧ 0 ≤ schur ∧
    0 ≤ G1 ∧ 0 ≤ G2 ∧ 0 ≤ G3 ∧ 0 ≤ cap ∧ 0 ≤ V ∧
    0 ≤ rootN ∧ 0 ≤ rootB ∧ 0 ≤ rootU ∧ 0 ≤ rootV
  e_sq : E ≤ eRoot ^ 2
  xi_sq : agentParallelCap / nlo ≤ xiRoot ^ 2
  s_sq : agentDirectionCap / nlo ≤ s ^ 2
  mu_cap : eRoot + xiRoot ≤ mu
  Y_pos : 0.216 < Y
  Y_cap : Y ≤ (1 - 0.0045) ^ 2 - mu ^ 2
  r_den : 0 < 1 - 6 * Θ / nlo
  r1_cap : Θ / (1 - 4 * Θ / nlo) ≤ r1
  r2_cap : Θ / (1 - 6 * Θ / nlo) ≤ r2
  D2_cap : 2 * mu * s + (cp2 * s) ^ 2 ≤ D2
  D4_cap : 2 * mu * (cp2 * s) + (cp4 * s) ^ 2 ≤ D4
  delta_cap : D2 / Y ^ 2 + D4 ^ 2 / (0.216 * Y ^ 2) ≤ delta
  W2_cap : 1 / Y + (2 * mu * s + s ^ 2) / Y ^ 2 + D2 ^ 2 / (0.216 * Y ^ 2) ≤ W2
  shell_cap : Θ * p.wLam / (1 - p.cRadius) * pair +
    Θ * p.wLam / (1 - p.wRadius) * outside ≤ shell
  cov_cap : r1 * p.cLam + shell + bad ≤ cov
  schur_cap : p.cLam * (r1 / Y + delta * r2) + (shell + bad) / 0.216 ≤ schur
  G1_cap : ((cov + full) / (0.216 * nlo)) ^ 41 ≤ G1 ^ 45
  G2_cap : (1 / (0.216 : ℝ)) ^ 4 ≤ G2 ^ 45
  G3_cap : (1 + agentEnergyMomentCap / nlo) ^ 8 ≤ G3 ^ 45
  cap_cap : G1 * G2 * G3 * (((1 - 0.0045) ^ 2 - 0.216) / 0.216 ^ 2) * agentDirectionCap ≤ cap
  V_cap : (((1 - 0.0045) ^ 2 - 0.216) / 0.216 ^ 3) * (agentDirectionCap / nlo) * cov ≤ V
  gap_pos : 0 < gap
  gap_sq : (gap + mu) ^ 2 ≤ (1 - 0.0045) ^ 2 - 0.216
  mass_cap : (nhi : ℝ) * ((agentEnergyMomentCap / nlo / 0.0045) ^ 32 +
    (cp12 ^ 24 * (agentDirectionCap / nlo) ^ 12) / gap ^ 24) ≤ mass
  rootN_sq : schur ≤ rootN ^ 2
  rootB_sq : cap ≤ rootB ^ 2
  rootU_sq : W2 * full ≤ rootU ^ 2
  rootV_sq : V ≤ rootV ^ 2
  total : (rootN + rootB) ^ 2 + (rootU + rootV) ^ 2 + mass < weightedFrameCap

end BstLean.BlueprintLow
