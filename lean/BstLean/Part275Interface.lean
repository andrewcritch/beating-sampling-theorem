import BstLean.Part275Analytic

/-! Part 275 (plan part L1), steps 1, 5 and 6.
* Step 5: the low-mass reduction with `M, H, xi, E, u, d, B` and the gap `g` as parameters
  (`LowMassNumerics`, `low_mass_of_interfacesP`), and a monotone base form in `n`.
* Step 1: `RootCaps` and `ActualRootCertificateP n root caps`, with the floor `8000 ≤ n`.
* Step 6: the Part262 certificate is the special case `part262Caps`. -/
namespace BstLean.Part275
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part188 BstLean.Part195 BstLean.Part222

/-! ### Step 5: the low-mass reduction with parameters -/

/-- The low residual mass at cutoff `d` and budget `B`. -/
def LowResidualMassP {n : ℕ} (d B : ℝ) (c : Ret n) : Prop :=
  ∫ a, (stdGauss (Fin (n - 1))).real
    {v | BstLean.Part162.sgA (paperDesignP n) c a v < √(2 / (n : ℝ) * d)} ∂muI n ≤ B

theorem lowResidualMassP_part262 {n : ℕ} (c : Ret n) :
    LowResidualMassP BstLean.Part252.mixtureFloor BstLean.Part252.lowMassBudget c ↔
      BstLean.Part262.LowResidualMass c := Iff.rfl

/-- The scalar low-mass price, with `rotationConstant 12 ≤ 4.8`. -/
noncomputable def lowMassPrice (n : ℕ) (M H u g : ℝ) : ℝ :=
  (H / u) ^ 32 + ((48 / 10 : ℝ) ^ 24 * (M / n) ^ 12) / g ^ 24

/-- The scalar guards of the low-mass reduction. `g` is a lower bound for the gap. -/
structure LowMassNumerics (n : ℕ) (M H xi E u d B g : ℝ) : Prop where
  u_pos : 0 < u
  u_lt : u < 1
  d_nonneg : 0 ≤ d
  d_lt : d < (1 - u) ^ 2
  gap_pos : 0 < g
  gap : g ≤ √((1 - u) ^ 2 - d) - (√E + √(xi / n))
  price : lowMassPrice n M H u g ≤ B

theorem low_mass_priceP {n : ℕ} {M H xi E u d B g : ℝ}
    (N : LowMassNumerics n M H xi E u d B g) :
    massBound n M H xi E u d ≤ n * B := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr := BstLean.Part252.rotation_twelve
  have hr0 := rotationConstant_nonneg 12
  have hg0 : 0 < √((1 - u) ^ 2 - d) - (√E + √(xi / n)) := lt_of_lt_of_le N.gap_pos N.gap
  unfold massBound
  apply mul_le_mul_of_nonneg_left _ hn0
  have hM12 : 0 ≤ (M / n) ^ 12 := Even.pow_nonneg (by decide) _
  calc
    _ ≤ (H / u) ^ 32 + ((48 / 10 : ℝ) ^ 24 * (M / n) ^ 12) / g ^ 24 := by
      have hd := pow_le_pow_left₀ N.gap_pos.le N.gap 24
      have hm := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr0 hr 24) hM12
      exact add_le_add_right (div_le_div₀ (mul_nonneg (by norm_num) hM12) hm (pow_pos N.gap_pos 24) hd) ((H / u) ^ 32)
    _ ≤ B := N.price

theorem low_mass_of_interfacesP {n : ℕ} (hn : 50 ≤ n) {c : Ret n} {M H xi E u d B g : ℝ}
    (N : LowMassNumerics n M H xi E u d B g)
    (hw : WINDOW (paperDesignP n) c) (he : 0 < eR c)
    (I : WFInterfaces (paperDesignP n) c M H xi)
    (hE : centreEnergy (paperDesignP n) c ≤ E) : LowResidualMassP d B c := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb : 0 < normSq ((paperDesignP n).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by linarith)
  have hg0 : 0 < √((1 - u) ^ 2 - d) - (√E + √(xi / n)) := lt_of_lt_of_le N.gap_pos N.gap
  have hm := sharp_residual_mass (d := d) (by omega) (paperDesignP n) c hw.2.1 hb
    (BstLean.Part262.paper_centre_nonneg c) I hE N.u_pos N.u_lt N.d_lt hg0
  have hl := BstLean.Part252.latitude_mass_of_MASS (by omega) (paperDesignP n) c
    hw.1 hw.2.1 N.d_nonneg hm
  exact hl.trans ((div_le_div_of_nonneg_right (low_mass_priceP N) hnR.le).trans
    (by rw [mul_div_cancel_left₀ _ hnR.ne']))

/-- The base form: guards at `n0` with `H = Hc / n0` give the guards at every `n ≥ n0`. -/
theorem lowMassNumerics_base {n0 n : ℕ} (h0 : 1 ≤ n0) (hn : n0 ≤ n)
    {M Hc xi E u d B g : ℝ} (hM : 0 ≤ M) (hHc : 0 ≤ Hc) (hxi : 0 ≤ xi)
    (N : LowMassNumerics n0 M (Hc / n0) xi E u d B g) :
    LowMassNumerics n M (Hc / n) xi E u d B g := by
  have h0R : (1 : ℝ) ≤ n0 := by exact_mod_cast h0
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n0 := by linarith
  have hnp : (0 : ℝ) < n := by linarith
  have hu := N.u_pos
  refine ⟨N.u_pos, N.u_lt, N.d_nonneg, N.d_lt, N.gap_pos, ?_, ?_⟩
  · have hs : √(xi / n) ≤ √(xi / n0) :=
      sqrt_le_sqrt (div_le_div_of_nonneg_left hxi hn0 hnR)
    linarith [N.gap]
  · refine le_trans ?_ N.price
    unfold lowMassPrice
    have hH : Hc / n / u ≤ Hc / n0 / u :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_left hHc hn0 hnR) hu.le
    have hM' : M / n ≤ M / n0 := div_le_div_of_nonneg_left hM hn0 hnR
    have g0 : 0 < g ^ 24 := pow_pos N.gap_pos 24
    gcongr

/-! ### Step 1: the caps and the parameterized certificate -/

/-- Every dimension-sensitive constant of the Part262 actual root interface. -/
structure RootCaps where
  Mcap : ℝ
  Hcap : ℕ → ℝ
  xiCap : ℝ
  Ecap : ℝ
  u : ℝ
  tableF : ℝ
  tableW : ℝ
  sourceCharge : ℝ
  tableCharge : ℝ
  lowMassBudget : ℝ

/-- The low-mass guards for the caps, at a cutoff `d` and a gap bound `g`. -/
def RootCaps.LowMass (caps : RootCaps) (n : ℕ) (d g : ℝ) : Prop :=
  LowMassNumerics n caps.Mcap (caps.Hcap n) caps.xiCap caps.Ecap caps.u d caps.lowMassBudget g

/-- The successor of `Part262.ActualRootCertificate`. The only floor is `8000 ≤ n`. -/
structure ActualRootCertificateP (n : ℕ) (root : ℝ) (caps : RootCaps) where
  dimension : 8000 ≤ n
  source_charge : sourceChargeFn n ≤ caps.sourceCharge
  table_payment : (retDist (paperCentres n)).real
    (tableEventP n caps.tableF caps.tableW)ᶜ ≤ caps.tableCharge
  inputs : ∀ (t : ℝ) (c : Ret n), WINDOW (paperDesignP n) c →
    c ∈ sourceBaseP n caps.tableF caps.tableW →
    WFInterfaces (paperDesignP n) c caps.Mcap (caps.Hcap n) caps.xiCap →
    centreEnergy (paperDesignP n) c ≤ caps.Ecap →
    BstLean.Part243.RootInputs n t c root

structure LocalRootSupplyP (n : ℕ) (caps : RootCaps) (H : Set (Ret n)) : Prop where
  window : ∀ c ∈ H, c ∈ sourceBaseP n caps.tableF caps.tableW → WINDOW (paperDesignP n) c
  interfaces : ∀ c ∈ H, c ∈ sourceBaseP n caps.tableF caps.tableW →
    WFInterfaces (paperDesignP n) c caps.Mcap (caps.Hcap n) caps.xiCap
  energy_cap : ∀ c ∈ H, c ∈ sourceBaseP n caps.tableF caps.tableW →
    centreEnergy (paperDesignP n) c ≤ caps.Ecap

theorem payment_of_certificateP {n : ℕ} {root : ℝ} {caps : RootCaps}
    (C : ActualRootCertificateP n root caps) (H : Set (Ret n)) :
    (retDist (paperCentres n)).real (H ∩ (sourceBaseP n caps.tableF caps.tableW)ᶜ) ≤
      caps.sourceCharge + caps.tableCharge :=
  (sourceBaseP_charge C.dimension C.table_payment H).trans
    (by linarith [C.source_charge])

noncomputable def actualBaseRootSupplyP {n : ℕ} {root : ℝ} {caps : RootCaps}
    (C : ActualRootCertificateP n root caps) (H : Set (Ret n))
    (L : LocalRootSupplyP n caps H) :
    BstLean.Part262.BaseRootSupply n H root (caps.sourceCharge + caps.tableCharge) where
  event := sourceBaseP n caps.tableF caps.tableW
  measurable := sourceBaseP_measurable (by have := C.dimension; omega) _ _
  payment := payment_of_certificateP C H
  inputs := fun t c hw hc => C.inputs t c (L.window c hw hc) hc
    (L.interfaces c hw hc) (L.energy_cap c hw hc)

def commonEventP (n : ℕ) (caps : RootCaps)
    (covarianceEvent : Set (BstLean.Part160.AgFam n)) : Set (Ret n) :=
  sourceBaseP n caps.tableF caps.tableW ∩ BstLean.Part259.covarianceGood covarianceEvent

theorem actual_common_paymentP {n : ℕ} {root : ℝ} {caps : RootCaps}
    (C : ActualRootCertificateP n root caps) {event : Set (BstLean.Part160.AgFam n)}
    (hCovariance : (retDist (paperCentres n)).real
      (BstLean.Part160.agentEv (paperDesignP n) event)ᶜ ≤ (1 / 4000 : ℝ))
    (H : Set (Ret n)) :
    (retDist (paperCentres n)).real (H ∩ (commonEventP n caps event)ᶜ) ≤
      caps.sourceCharge + caps.tableCharge + 3 / 10000 := by
  have hs : H ∩ (commonEventP n caps event)ᶜ ⊆
      (H ∩ (sourceBaseP n caps.tableF caps.tableW)ᶜ) ∪
        (BstLean.Part259.covarianceGood event)ᶜ := by
    intro c hc
    by_cases hb : c ∈ sourceBaseP n caps.tableF caps.tableW
    · exact Or.inr (fun hg => hc.2 ⟨hb, hg⟩)
    · exact Or.inl ⟨hc.1, hb⟩
  have hp := BstLean.Part273.covarianceGood_charge_8000 C.dimension hCovariance
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (payment_of_certificateP C H) hp))

/-- The local frame inputs of RowInputs v2 give the remaining local interfaces. -/
noncomputable def rootInputs_from_frameK {n k : ℕ} {root t cf : ℝ} {caps : RootCaps}
    {event : Set (BstLean.Part160.AgFam n)} {needed : Fin k → Prop}
    {cell : Fin k → Set ℝ} {capTable : Fin k → ℝ}
    {c : Ret n} (C : ActualRootCertificateP n root caps)
    (F : BstLean.Part273.LocalFrameInputsK n k event needed cell capTable c cf)
    (hc : c ∈ sourceBaseP n caps.tableF caps.tableW)
    (hcell : cell F.index ⊆ Icc (46 / 100 : ℝ) (54 / 100))
    (hM : F.M ≤ caps.Mcap) (hH : F.H ≤ caps.Hcap n)
    (hxi : F.xiP ≤ caps.xiCap) (hE : F.E ≤ caps.Ecap) :
    BstLean.Part243.RootInputs n t c root := by
  have hn : 1 ≤ n := by have := C.dimension; omega
  have hw := BstLean.Part252.window_of_theta hn (paperDesignP n) c
    F.scale_pos (hcell F.member)
  have I : WFInterfaces (paperDesignP n) c caps.Mcap (caps.Hcap n) caps.xiCap := by
    refine ⟨BstLean.Part219.directionMoment_mono F.interfaces.direction hM, ?_, ?_⟩
    · exact ⟨F.interfaces.energy.1.trans hH, F.interfaces.energy.2.1,
        F.interfaces.energy.2.2.trans (pow_le_pow_left₀ F.interfaces.energy.1 hH 32)⟩
    · refine ⟨F.interfaces.parallel.1.trans hxi, F.interfaces.parallel.2.trans ?_⟩
      apply sqrt_le_sqrt
      exact div_le_div_of_nonneg_right hxi (Nat.cast_nonneg n)
  exact C.inputs t c hw hc I (F.centre_energy.trans hE)

/-! ### Step 6: the Part262 instance -/

/-- The Part262 caps: `(.091, 21.01/n, .04, .702, .0042)`, thresholds `(.0649, .2173)`,
charges `(.000599145, .0009)` and low-mass budget `5e-12`. -/
noncomputable def part262Caps : RootCaps where
  Mcap := 91 / 1000
  Hcap := fun n => (2101 / 100) / n
  xiCap := 4 / 100
  Ecap := 702 / 1000
  u := 42 / 10000
  tableF := 649 / 10000
  tableW := 2173 / 10000
  sourceCharge := 599145 / 10 ^ 9
  tableCharge := 9 / 10000
  lowMassBudget := 5 / 10 ^ 12

/-- Every Part262 actual certificate is an `ActualRootCertificateP` at `part262Caps`. -/
noncomputable def ofPart262 {n : ℕ} {root : ℝ}
    (C : BstLean.Part262.ActualRootCertificate n root) :
    ActualRootCertificateP n root part262Caps where
  dimension := by have := C.dimension; omega
  source_charge := sourceChargeFn_le_part262 (by have := C.dimension; omega)
  table_payment := C.table_payment
  inputs := fun t c hw hc I hE => C.inputs t c hw hc I hE

/-- The Part262 payment is the same number: `.000599145 + .0009 = .001499145`. -/
theorem part262Caps_charge :
    part262Caps.sourceCharge + part262Caps.tableCharge = 1499145 / 10 ^ 9 := by
  norm_num [part262Caps]

/-- The Part262 low-mass guards at base 12225 (`d` = the Part252 mixture floor, `g = .04`). -/
theorem part262_lowMass_12225 :
    LowMassNumerics 12225 (91 / 1000) ((2101 / 100) / (12225 : ℕ)) (4 / 100) (702 / 1000)
      (42 / 10000) BstLean.Part252.mixtureFloor (5 / 10 ^ 12) (4 / 100) := by
  refine ⟨by norm_num, by norm_num, by norm_num [BstLean.Part252.mixtureFloor],
    by norm_num [BstLean.Part252.mixtureFloor], by norm_num, ?_, ?_⟩
  · have h1 : (880019 / 10 ^ 6 : ℝ) ≤ √((1 - 42 / 10000) ^ 2 - BstLean.Part252.mixtureFloor) :=
      le_sqrt_of_sq_le (by norm_num [BstLean.Part252.mixtureFloor])
    have h2 : √(702 / 1000 : ℝ) ≤ 837855 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
    have h3 : √((4 / 100 : ℝ) / (12225 : ℕ)) ≤ 181 / 10 ^ 5 :=
      sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    linarith
  · unfold lowMassPrice
    norm_num

/-- The Part262 low-mass reduction is the special case of `low_mass_of_interfacesP`. -/
theorem part262_low_mass {n : ℕ} (hn : 12225 ≤ n) {c : Ret n}
    (hw : WINDOW (paperDesignP n) c) (he : 0 < eR c)
    (I : WFInterfaces (paperDesignP n) c (91 / 1000) ((2101 / 100) / n) (4 / 100))
    (hE : centreEnergy (paperDesignP n) c ≤ 702 / 1000) :
    BstLean.Part262.LowResidualMass c :=
  low_mass_of_interfacesP (by omega)
    (lowMassNumerics_base (n0 := 12225) (by norm_num) hn (by norm_num) (by norm_num)
      (by norm_num) part262_lowMass_12225) hw he I hE

/-! ### The low-mass guards from 8000 -/

/-- From 8000, with the record direction cap `M ≤ .11` and the M7 cutoff `d = .2009040784`,
the guards hold with `u = .006`, gap `g = .047` and budget `B = 1e-10`.
The Part262 pair `u = .0042`, `B = 5e-12` fails at 8000 (its first term is about `3e-7`). -/
theorem lowMass_8000 :
    LowMassNumerics 8000 (11 / 100) ((2101 / 100) / (8000 : ℕ)) (4 / 100) (702 / 1000)
      (6 / 1000) (2009040784 / 10 ^ 10) (1 / 10 ^ 10) (47 / 1000) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · have h1 : (8872 / 10 ^ 4 : ℝ) ≤ √((1 - 6 / 1000) ^ 2 - 2009040784 / 10 ^ 10) :=
      le_sqrt_of_sq_le (by norm_num)
    have h2 : √(702 / 1000 : ℝ) ≤ 837855 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
    have h3 : √((4 / 100 : ℝ) / (8000 : ℕ)) ≤ 2237 / 10 ^ 6 :=
      sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    linarith
  · unfold lowMassPrice
    norm_num

theorem lowMass_from_8000 {n : ℕ} (hn : 8000 ≤ n) :
    LowMassNumerics n (11 / 100) ((2101 / 100) / n) (4 / 100) (702 / 1000)
      (6 / 1000) (2009040784 / 10 ^ 10) (1 / 10 ^ 10) (47 / 1000) :=
  lowMassNumerics_base (n0 := 8000) (by norm_num) hn (by norm_num) (by norm_num)
    (by norm_num) lowMass_8000

/-- The Part262 pair fails at 8000: the energy term alone exceeds `5e-12`. -/
theorem part262_lowMass_fails_8000 :
    (5 / 10 ^ 12 : ℝ) < lowMassPrice 8000 (91 / 1000) ((2101 / 100) / (8000 : ℕ))
      (42 / 10000) (4 / 100) := by
  unfold lowMassPrice
  norm_num

end BstLean.Part275
