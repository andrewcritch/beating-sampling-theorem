import BstLean.Part213PaperRA
import BstLean.Part220Events

/-! The two RA16 supplies integrate the actual node biases and their row formulas. -/
namespace BstLean.Part220
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part170 (biasF biasW tA)
open BstLean.Part213
open BstLean.Part186.RA (ρ2)

structure RAData where
  Smin : ℝ
  Smax : ℝ
  D : ℝ
  H : ℝ
  V : ℝ
  P : ℝ
  topF : ℝ
  topW : ℝ

noncomputable def RAData.f0 (d : RAData) (n : ℕ) (O : ℝ) :=
  AF0 (sqrt d.Smin) (tA n * O ^ 2 + d.Smax) d.H d.V d.P
noncomputable def RAData.f1 (d : RAData) (n : ℕ) (O : ℝ) :=
  AF1 (sqrt d.Smin) d.D d.V d.P (sqrt (tA n) * O)
noncomputable def RAData.f2 (d : RAData) := AF2 (sqrt d.Smin) d.D
noncomputable def RAData.w0 (d : RAData) (n : ℕ) (O : ℝ) :=
  AW0 (sqrt d.Smin) (tA n * O ^ 2 + d.Smax) d.H d.V d.P
noncomputable def RAData.w1 (d : RAData) (n : ℕ) (O : ℝ) :=
  AW1 (sqrt d.Smin) (sqrt d.Smax) d.D d.V d.P (sqrt (tA n) * O)
noncomputable def RAData.w2 (d : RAData) (n : ℕ) (O : ℝ) :=
  AW2 d.D d.P (sqrt (tA n) * O)

/-- These inputs are scalar statistics and complete plane-row moments.
They contain no premise about an actual node-bias moment. -/
structure NodeRASupply {n : ℕ} (c : Ret n) (g : ℕ) (O : ℝ) (d : RAData) : Prop where
  min_pos : 0 < d.Smin
  statistics : NodeStat c g d.Smin d.Smax d.D d.H d.V d.P
  f0_nonneg : 0 ≤ d.f0 n O
  f1_nonneg : 0 ≤ d.f1 n O
  f2_nonneg : 0 ≤ d.f2
  w0_nonneg : 0 ≤ d.w0 n O
  w1_nonneg : 0 ≤ d.w1 n O
  w2_nonneg : 0 ≤ d.w2 n O
  topF_nonneg : 0 ≤ d.topF
  topW_nonneg : 0 ≤ d.topW
  rowF : ∫ p, radiusPolynomial (d.f0 n O) (d.f1 n O) d.f2 p ^ 16 ∂ρ2 ≤ d.topF ^ 16
  rowW : ∫ p, radiusPolynomial (d.w0 n O) (d.w1 n O) (d.w2 n O) p ^ 16 ∂ρ2 ≤ d.topW ^ 16

noncomputable def RAData.locationBound (d : RAData) (n : ℕ) (O : ℝ) : ℝ :=
  (n : ℝ) ^ 8 * (mA n : ℝ) ^ 8 *
    (collectedSecond (d.f0 n O) (d.f1 n O) d.f2 + locationR16 n * d.topF ^ 2) ^ 8

noncomputable def RAData.energyBound (d : RAData) (n : ℕ) (O : ℝ) : ℝ :=
  (mA n : ℝ) ^ 16 *
    (d.w0 n O + d.w1 n O * sqrt (π / 2) + 2 * d.w2 n O + energyR16 n * d.topW) ^ 16

/-- The complete plane-row product supplies both actual RA16 node moments. -/
theorem node_RA16_supply {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (g : ℕ)
    (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB (A1 c) O)
    (d : RAData) (h : NodeRASupply c g O d) :
    (∫⁻ y, ENNReal.ofReal (|biasF c g (fun j => (y j).1) (fun j => (y j).2)| ^ 16)
      ∂(Measure.pi fun _ : Fin (mA n) => ρ2)) ≤ ENNReal.ofReal (d.locationBound n O) ∧
    (∫⁻ y, ENNReal.ofReal (|biasW c g (fun j => (y j).1) (fun j => (y j).2)| ^ 16)
      ∂(Measure.pi fun _ : Fin (mA n) => ρ2)) ≤ ENNReal.ofReal (d.energyBound n O) := by
  simp_rw [Even.pow_abs (by decide : Even 16)]
  exact ⟨conditional_location_RA16_paper hn c g hs hO hOp h.min_pos h.statistics
    h.f0_nonneg h.f1_nonneg h.f2_nonneg h.topF_nonneg h.rowF,
    conditional_energy_RA16_paper hn c g hs hO hOp h.min_pos h.statistics
    h.w0_nonneg h.w2_nonneg h.w1_nonneg h.topW_nonneg h.rowW⟩

/-- The weighted supplies keep the scalar node statistics inside their own integrals. -/
theorem weighted_RA16_supply {n : ℕ} (hn : 1 ≤ n) (c : Ret n)
    {G : Type*} [MeasurableSpace G] (ν : Measure G) (node : G → ℕ)
    (hs : ∀ g, nodeS c (node g) ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB (A1 c) O)
    (d : G → RAData) (h : ∀ g, NodeRASupply c (node g) O (d g))
    {BF BW : ℝ}
    (hF : ∫⁻ g, ENNReal.ofReal ((d g).locationBound n O) ∂ν ≤ ENNReal.ofReal (BF ^ 16))
    (hW : ∫⁻ g, ENNReal.ofReal ((d g).energyBound n O) ∂ν ≤ ENNReal.ofReal (BW ^ 16)) :
    (∫⁻ g, ∫⁻ y, ENNReal.ofReal (|biasF c (node g) (fun j => (y j).1) (fun j => (y j).2)| ^ 16)
      ∂(Measure.pi fun _ : Fin (mA n) => ρ2) ∂ν) ≤ ENNReal.ofReal (BF ^ 16) ∧
    (∫⁻ g, ∫⁻ y, ENNReal.ofReal (|biasW c (node g) (fun j => (y j).1) (fun j => (y j).2)| ^ 16)
      ∂(Measure.pi fun _ : Fin (mA n) => ρ2) ∂ν) ≤ ENNReal.ofReal (BW ^ 16) := by
  exact ⟨(lintegral_mono fun g => (node_RA16_supply hn c (node g) (hs g) hO hOp (d g) (h g)).1).trans hF,
    (lintegral_mono fun g => (node_RA16_supply hn c (node g) (hs g) hO hOp (d g) (h g)).2).trans hW⟩

#print axioms node_RA16_supply
#print axioms weighted_RA16_supply
end BstLean.Part220
