import BstLean.Part159Hid
import BstLean.Part143All

/-!
# Part 159 (file `Hat`): the World hypotheses for the computed centre `b̂ = ψ_s(W₂ h̄₁)`

Role: `delegations/statements/p159-spec.md`, items 1 and 2. Do not use `sorry`, `native_decide` or
`axiom`.

The centre is `bhat` of Part 137 (`b̂_i = ψ_s((W₂ h̄₁)_i)`, `h̄₁ = c_N·|row(W₁)|`,
`ψ_s(x) = E_Z ReLU(x + sZ)`): a function of `(W₁, W₂)` that one pass computes, up to the function
`ψ_s` and the constant `c_N` (NOT arithmetic: Part 141 has the arithmetic version). The scalar is
`tauHat` of Part 140. This is NOT the binomial centre of the paper (`bWp` of Part 157).

The hidden event is `goodHat n` of Part 140. For every `n ≥ 16 384`:

* `hat_charge`: `Pr((goodHat n)ᶜ) ≤ 0.00163194 ≤ 0.001900001` (from Part 143).
* `hat_frame`: the frame bound `1.37/n ≤ 1.377/n` (from Part 143).
* `hu2_le_hat`, `hellHid_le_hat`: `E_u H_u² ≤ HbarH + (mass of the bad inputs)` on `goodHat n`,
  with the value `2` of the paper at the bad inputs (Part 140 has the value `1`).
* `hat_moment`: `E[1_{goodHat}·E_u H_u²] ≤ EHH n ζ + BetaH n ζ`; `hat_moment_num`:
  `≤ 7.31·10⁻⁹ ≤ v_W = 1.1869648·10⁻⁸` at `ζ = 1/20`.
* `HW n`, `events_hat`, `frame_w_hat`: `EVENTS_hyp` (World parts) and `FRAME_W_hyp` with the
  constants of the ledger of Part 156, for every design with this World centre and scalar.
-/

namespace BstLean.Part159

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss mW_ge_million)
open BstLean.Part137 (bhat measurable_bhat)
open BstLean.Part138 (hellG)
open BstLean.Part140
open BstLean.Part143 (frameHat143 L143 goodHat_compl143s P143 cExtra143s nsq_div_mW_le128)
open BstLean.Part156 BstLean.Part157

variable {n : ℕ}

/-- The mass of the bad inputs `u` (outside `goodUH`) for the hidden matrices `θ`. -/
noncomputable def badH (n : ℕ) (ζ : ℝ) (θ : WHid n) : ℝ :=
  ∫ u, (goodUH (2 * n) (mW n) ζ)ᶜ.indicator (fun _ => (1 : ℝ)) (u, θ) ∂uniformSphere (2 * n)

lemma hellG_zero {k : ℕ} (hk : k ≠ 0) (τ₀ : ℝ) : hellG k 0 τ₀ = 2 := by
  unfold hellG
  simp [zero_pow hk]

/-- **The Hellinger term of one input for the computed centre**, with the value `2` of the paper
at the bad inputs. -/
theorem hu2_le_hat (hn : 4096 ≤ n) {θ : WHid n} (hθ : θ ∈ goodHat n) {ζ : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ1 : ζ < 1) (u : Fin (2 * n) → ℝ) :
    hu2 n (lam (bhat θ) (hid2 θ.1 θ.2 u)) (sig (2 / (mW n : ℝ)) (bhat θ) (hid2 θ.1 θ.2 u))
        (tauHat (2 * n) (mW n) θ) ≤
      KfunH n ζ (u, θ) + (goodUH (2 * n) (mW n) ζ)ᶜ.indicator (fun _ => (1 : ℝ)) (u, θ) := by
  by_cases hp : (u, θ) ∈ goodUH (2 * n) (mW n) ζ
  · rw [KfunH_of_mem hp, Set.indicator_of_notMem (by simpa using hp), add_zero]
    obtain ⟨hl, hH⟩ := good_ptH hn hθ hζ0 hζ1 hp
    have hτ := tauHat_pos hn hθ
    unfold hu2
    split_ifs with hc
    · exact hH
    · have hs0 : 0 ≤ sig (2 / (mW n : ℝ)) (bhat θ) (hid2 θ.1 θ.2 u) := by
        unfold sig; positivity
      have hs : sig (2 / (mW n : ℝ)) (bhat θ) (hid2 θ.1 θ.2 u) = 0 := by
        by_contra h
        exact hc ⟨hl, lt_of_le_of_ne hs0 (Ne.symm h), hτ⟩
      rw [hs, zero_div, hellG_zero (by omega)] at hH
      exact hH
  · rw [KfunH_of_notMem hp, Set.indicator_of_mem (by simpa using hp)]
    have := hu2_le_two n (lam (bhat θ) (hid2 θ.1 θ.2 u))
      (sig (2 / (mW n : ℝ)) (bhat θ) (hid2 θ.1 θ.2 u)) (tauHat (2 * n) (mW n) θ)
    linarith

lemma integrable_badInd (hn : 1 ≤ n) (ζ : ℝ) (θ : WHid n) :
    Integrable (fun u : Fin (2 * n) → ℝ =>
      (goodUH (2 * n) (mW n) ζ)ᶜ.indicator (fun _ => (1 : ℝ)) (u, θ)) (uniformSphere (2 * n)) := by
  have := uniformSphere_isProbability (2 * n) (by omega)
  have hm : MeasurableSet ((fun u : Fin (2 * n) → ℝ => (u, θ)) ⁻¹' (goodUH (2 * n) (mW n) ζ)ᶜ) :=
    measurable_prodMk_right (goodUH_meas (by omega) ζ).compl
  exact (integrable_const (1 : ℝ)).indicator hm

/-- **`E_u H_u² ≤ HbarH + badH`** for the computed centre and the scalar `tauHat`, on `goodHat`. -/
theorem hellHid_le_hat (hn : 4096 ≤ n) {θ : WHid n} (hθ : θ ∈ goodHat n) {ζ : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ1 : ζ < 1) :
    hellHid bhat (tauHat (2 * n) (mW n)) θ ≤ HbarH n ζ θ + badH n ζ θ := by
  have hK := KfunH_integrable hn hθ hζ1
  have hB := integrable_badInd (by omega : 1 ≤ n) ζ θ
  unfold hellHid HbarH badH
  rw [← integral_add hK hB]
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => hu2_nonneg _ _ _ _)
    (hK.add hB) (Filter.Eventually.of_forall fun u => hu2_le_hat hn hθ hζ0 hζ1 u)

/-- **The restricted mean of the majorant**: `E_θ[1_{goodHat}·(HbarH + badH)] ≤ EHH + BetaH`. -/
theorem hat_moment (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    Integrable ((goodHat n).indicator (fun θ => HbarH n ζ θ + badH n ζ θ))
        (hidGauss (2 * n) (mW n)) ∧
      ∫ θ, (goodHat n).indicator (fun θ => HbarH n ζ θ + badH n ζ θ) θ
        ∂hidGauss (2 * n) (mW n) ≤ EHH n ζ + BetaH n ζ := by
  have hN : 1 ≤ 2 * n := by omega
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have := uniformSphere_isProbability (2 * n) hN
  have mE := goodHat_meas (n := n) (by omega)
  obtain ⟨hk1, -⟩ := kap1_window hn
  have hkpos : 0 < kap1 (2 * n) := by linarith
  obtain ⟨i1, h1⟩ := HbarH_mean hn hζ0 hζ1
  set μP := (uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n)) with hμP
  set Bd : Set ((Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) :=
    {p | p.2 ∈ goodHat n ∧ p ∉ goodUH (2 * n) (mW n) ζ} with hBd
  have mBd : MeasurableSet Bd := (measurable_snd mE).inter (goodUH_meas hN ζ).compl
  set F2 : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) → ℝ :=
    Bd.indicator (fun _ => (1 : ℝ)) with hF2
  have iF2 : Integrable F2 μP := (integrable_const (1 : ℝ)).indicator mBd
  have hfun : (goodHat n).indicator (badH n ζ) =
      fun θ => ∫ u, F2 (u, θ) ∂uniformSphere (2 * n) := by
    funext θ
    by_cases hθ : θ ∈ goodHat n
    · rw [Set.indicator_of_mem hθ]
      unfold badH
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      by_cases hp : (u, θ) ∈ goodUH (2 * n) (mW n) ζ
      · have h2 : (u, θ) ∉ Bd := fun h => h.2 hp
        simp only [hF2]
        rw [Set.indicator_of_notMem (by simpa using hp), Set.indicator_of_notMem h2]
      · have h2 : (u, θ) ∈ Bd := ⟨hθ, hp⟩
        simp only [hF2]
        rw [Set.indicator_of_mem (by simpa using hp), Set.indicator_of_mem h2]
    · rw [Set.indicator_of_notMem hθ]
      have h0 : ∀ u : Fin (2 * n) → ℝ, F2 (u, θ) = 0 := fun u => by
        have h2 : (u, θ) ∉ Bd := fun h => hθ h.1
        simp only [hF2]
        rw [Set.indicator_of_notMem h2]
      simp [h0]
  have i2 : Integrable ((goodHat n).indicator (badH n ζ)) (hidGauss (2 * n) (mW n)) := by
    rw [hfun]; exact iF2.integral_prod_right
  have h2 : ∫ θ, (goodHat n).indicator (badH n ζ) θ ∂hidGauss (2 * n) (mW n) ≤ BetaH n ζ := by
    rw [hfun, ← integral_prod_symm _ iF2]
    have e : ∫ p, F2 p ∂μP = μP.real Bd := by
      rw [hF2, integral_indicator mBd, setIntegral_const, smul_eq_mul, mul_one]
    rw [e]
    have hsub : Bd ⊆ {p | p ∉ goodUH (2 * n) (mW n) ζ} := fun p hp => hp.2
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans
      (tauBadH_gen (N := 2 * n) (m := mW n) hN hm hkpos hζ0)
  have esum : (goodHat n).indicator (fun θ => HbarH n ζ θ + badH n ζ θ) =
      fun θ => (goodHat n).indicator (HbarH n ζ) θ + (goodHat n).indicator (badH n ζ) θ := by
    funext θ
    by_cases hθ : θ ∈ goodHat n
    · simp [Set.indicator_of_mem hθ]
    · simp [Set.indicator_of_notMem hθ]
  rw [esum]
  refine ⟨i1.add i2, ?_⟩
  rw [integral_add i1 i2]
  linarith

/-- `n/m_W ≤ 1/(128 n²)` and `1/m_W ≤ 1/(128 n³)` for `n ≥ 16 384`. -/
lemma inv_mW_le {n : ℕ} (hn : 16384 ≤ n) :
    (n : ℝ) / (mW n : ℝ) ≤ 1 / (128 * (n : ℝ) ^ 2) ∧ 1 / (mW n : ℝ) ≤ 1 / (128 * (n : ℝ) ^ 3) := by
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hm : (0 : ℝ) < mW n := by
    have := mW_ge_million (n := n) (by omega)
    exact_mod_cast (by omega : 0 < mW n)
  have h := nsq_div_mW_le128 hn
  have e1 : (n : ℝ) / (mW n : ℝ) = (n : ℝ) ^ 2 / (mW n : ℝ) / (n : ℝ) := by field_simp
  have e2 : 1 / (mW n : ℝ) = (n : ℝ) ^ 2 / (mW n : ℝ) / (n : ℝ) ^ 2 := by field_simp
  constructor
  · rw [e1]
    refine (div_le_div_of_nonneg_right h hnpos.le).trans (le_of_eq ?_)
    field_simp
  · rw [e2]
    refine (div_le_div_of_nonneg_right h (by positivity)).trans (le_of_eq ?_)
    field_simp

/-- The bound of the Hellinger moment of the computed centre for `n ≥ 16 384`:
`7.31·10⁻⁹` (the ledger of Part 156 has `v_W = 1.1869648·10⁻⁸`). -/
noncomputable def vHat : ℝ := 731 / 10 ^ 11

lemma vHat_le : vHat ≤ vWL := by unfold vHat vWL; norm_num

/-- **The Hellinger moment of the computed centre, numbers** (`ζ = 1/20`, `n ≥ 16 384`):
`EHH + BetaH ≤ 250·n/m_W + 17200/m_W ≤ 7.31·10⁻⁹`. -/
theorem hat_moment_num {n : ℕ} (hn : 16384 ≤ n) : EHH n (1 / 20) + BetaH n (1 / 20) ≤ vHat := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h1 := EHH_le hn4
  have h2 := BetaH_le hn4
  obtain ⟨a1, a2⟩ := inv_mW_le hn
  have b1 : 1 / (128 * (n : ℝ) ^ 2) ≤ 1 / (128 * (16384 : ℝ) ^ 2) :=
    one_div_le_one_div_of_le (by norm_num) (by gcongr)
  have b2 : 1 / (128 * (n : ℝ) ^ 3) ≤ 1 / (128 * (16384 : ℝ) ^ 3) :=
    one_div_le_one_div_of_le (by norm_num) (by gcongr)
  have e1 : 250 * (n : ℝ) / (mW n : ℝ) = 250 * ((n : ℝ) / (mW n : ℝ)) := by ring
  have e2 : 17200 / (mW n : ℝ) = 17200 * (1 / (mW n : ℝ)) := by ring
  rw [e1] at h1
  rw [e2] at h2
  have c1 : 250 * ((n : ℝ) / (mW n : ℝ)) ≤ 250 * (1 / (128 * (16384 : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left (a1.trans b1) (by norm_num)
  have c2 : 17200 * (1 / (mW n : ℝ)) ≤ 17200 * (1 / (128 * (16384 : ℝ) ^ 3)) :=
    mul_le_mul_of_nonneg_left (a2.trans b2) (by norm_num)
  have c3 : 250 * (1 / (128 * (16384 : ℝ) ^ 2)) + 17200 * (1 / (128 * (16384 : ℝ) ^ 3)) ≤
      731 / 10 ^ 11 := by norm_num
  unfold vHat
  linarith

/-- The bound of the hidden charge of the computed centre for `n ≥ 16 384`: `0.00163194`
(the ledger of Part 156 has `0.001900001`). -/
noncomputable def δHat : ℝ := 163194 / 10 ^ 8

lemma δHat_le : δHat ≤ δhidL := by unfold δHat δhidL; norm_num

/-- **The hidden charge of the computed centre** (from Part 143): `Pr((goodHat n)ᶜ) ≤ 0.00163194`
for every `n ≥ 16 384`. -/
theorem hat_charge {n : ℕ} (hn : 16384 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ δHat := by
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have h := goodHat_compl143s hn
  have h2 : cExtra143s / (n : ℝ) ≤ cExtra143s / 16384 :=
    div_le_div_of_nonneg_left (by unfold cExtra143s; norm_num) (by norm_num) hn'
  have h3 : P143 + cExtra143s / 16384 ≤ δHat := by
    unfold P143 cExtra143s δHat; norm_num
  linarith

/-- **The frame bound of the computed centre** (from Part 143): `1.37/n`, every `n ≥ 16 384`. -/
theorem hat_frame {n : ℕ} (hn : 16384 ≤ n) {θ : WHid n} (hθ : θ ∈ goodHat n)
    (w : Fin (mW n) → ℝ) :
    ∫ u, (∑ j, eDir (bhat θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
      137 / 100 / (n : ℝ) * ∑ j, w j ^ 2 := frameHat143 hn hθ w

/-! ## The World hypotheses of Part 157 -/

/-- **The hidden World event of this part**: the retained data whose hidden World matrices are in
`goodHat n` (Part 140). -/
def HW (n : ℕ) : Set (Ret n) := Hof (goodHat n)

lemma measurableSet_HW (hn : 1 ≤ n) : MeasurableSet (HW n) :=
  measurableSet_Hof (goodHat_meas hn)

/-- **`FRAME_W_hyp` is PROVED for the computed centre**, with the constant `1.377/n` of the
ledger (Lean has `1.37/n`), on every set of retained data inside `HW n`, every `n ≥ 16 384`. -/
theorem frame_w_hat (hn : 16384 ≤ n) (D : Centres n) (hD : D.bW = bhat) {E : Set (Ret n)}
    (hE : E ⊆ HW n) : FRAME_W_hyp D (cWL / n) E := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  refine frame_of_hid D (G := goodHat n) (fun θ hθ w => ?_) hE
  rw [hD]
  have hc : (137 / 100 / (n : ℝ)) ≤ cWL / (n : ℝ) :=
    div_le_div_of_nonneg_right (by unfold cWL; norm_num) hnpos.le
  exact (hat_frame hn hθ w).trans
    (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun j _ => sq_nonneg _))

/-- The majorant of `H̄_W²` on `HW n` for a design with the computed centre and `tauHat`. -/
theorem HbarW2_le_hat (hn : 4096 ≤ n) (D : Design n) (hD : D.bW = bhat)
    (hτ : ∀ c : Ret n, D.tau0 c = tauHat (2 * n) (mW n) c.1.1) {ζ : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ1 : ζ < 1) (c : Ret n) (hc : c.1.1 ∈ goodHat n) :
    HbarW2 D c ≤ HbarH n ζ c.1.1 + badH n ζ c.1.1 := by
  rw [HbarW2_eq_hellHid D c (hτ c), hD]
  exact hellHid_le_hat hn hc hζ0 hζ1

/-- **`EVENTS_hyp` with the World parts PROVED** for a design with the computed centre `bhat` and
the scalar `tauHat`, every `n ≥ 16 384`: the hidden charge is `δHat = 0.00163194`, the restricted
Hellinger moment is `vHat = 7.31·10⁻⁹`. The charge `δ_extra` of the other events is a
hypothesis. -/
theorem events_hat (hn : 16384 ≤ n) (D : Design n) (hD : D.bW = bhat)
    (hτ : ∀ c : Ret n, D.tau0 c = tauHat (2 * n) (mW n) c.1.1)
    {E₁ : Set (Ret n)} (hE₁ : MeasurableSet E₁) {δextra : ℝ}
    (h3 : (retDist D.toCentres).real (HW n ∩ E₁ᶜ) ≤ δextra) :
    EVENTS_hyp D.toCentres (HW n) E₁ (HbarW D) δHat vHat δextra := by
  have hn4 : 4096 ≤ n := by omega
  obtain ⟨iK, hK⟩ := hat_moment hn4 (ζ := 1 / 20) (by norm_num) (by norm_num)
  exact events_of_hid (by omega) D (goodHat_meas (by omega)) iK
    (fun c hc => HbarW2_le_hat hn4 D hD hτ (by norm_num) (by norm_num) c hc) hE₁
    (hat_charge hn) (hK.trans (hat_moment_num hn)) h3

/-- `EVENTS_hyp` is monotone in the three charges. -/
theorem events_mono {D : Centres n} {H E₁ : Set (Ret n)} {Hbar : Ret n → ℝ}
    {δhid vW δextra δhid' vW' δextra' : ℝ}
    (h : EVENTS_hyp D H E₁ Hbar δhid vW δextra) (h1 : δhid ≤ δhid') (h2 : vW ≤ vW')
    (h3 : δextra ≤ δextra') : EVENTS_hyp D H E₁ Hbar δhid' vW' δextra' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.trans h1, h.2.2.2.2.1, h.2.2.2.2.2.1.trans h2,
    h.2.2.2.2.2.2.trans h3⟩

end BstLean.Part159

open BstLean.Part159 in
#print axioms hu2_le_hat
open BstLean.Part159 in
#print axioms hat_moment
open BstLean.Part159 in
#print axioms hat_moment_num
open BstLean.Part159 in
#print axioms hat_charge
open BstLean.Part159 in
#print axioms frame_w_hat
open BstLean.Part159 in
#print axioms events_hat
