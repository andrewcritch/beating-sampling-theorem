import BstLean.Part186RA5
import BstLean.Part186Def

/-!
# Part 186 (file `RA`): the row-averaged bias moments (paper Lemma `t7:p08:RA`), proved

No proof is left open; no `native_decide` or `axiom` is used.

* `node_bulk16`: the nodes of the World window have `s² ≤ 1` for every `n ≥ 16 384`;
* **`BiasRA_gen`**: for every `n ≥ 16 384` and every `0 ≤ P_m ≤ 80/n⁴`, on the statistics event,
  `BiasMomF (O₁) Gb (194/n)` and `BiasMomW (O₁) Gb (148/n)`;
* **`BiasRA80_proved`** (threshold `P_m = 80/n⁴`) and **`BiasRA_proved : BiasRA_stmt`**
  (`P_m = 68/n⁴`).

Constants (location, `ε = 1/20`, `t = 10²⁶y³²`): `μ̄ ≈ 34 827`, `√μ̄ ≈ 186.6`, total `0.849·194⁸`;
(energy, `ε = 1/50`): `μ̄ ≈ 143.86`, total `0.915·148⁸`.
-/

namespace BstLean.Part186

open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part170 (tA windowW mkR BiasMomF BiasMomW)
open BstLean.Part186.RA

variable {n : ℕ}

lemma qB_nonneg16 (hn : 16384 ≤ n) : 0 ≤ qB n := by
  unfold qB
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : √(54 / 100 : ℝ) ≤ 734847 / 1000000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 : √(55 / 100 / (n : ℝ)) ≤ 5795 / 1000000 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by linarith)]; nlinarith
  have h3 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) := by positivity
  have h4 : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) ≤ 77 / 100 := by linarith
  nlinarith

/-- In the World window every node `s_g`, `g < J_s`, has `s_g² ≤ 1` (every `n ≥ 16 384`). -/
lemma node_bulk16 (hn : 16384 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
    (hg : g < Js n) : nodeS (mkR wr θ) g ^ 2 ≤ 1 := by
  obtain ⟨hτ, hθ0, hθ1⟩ := hw
  obtain ⟨hLH, hb, -⟩ := bulk_of_window (by omega) (mkR wr θ) hτ hθ0 hθ1
  have hq := qB_nonneg16 hn
  have hJ : (0 : ℝ) < Js n := by exact_mod_cast (show 0 < Js n by unfold Js; omega)
  have hD : 0 ≤ nodeD (mkR wr θ) := div_nonneg (by linarith) hJ.le
  have hg' : (g : ℝ) + 1 / 2 ≤ Js n := by
    have : (g : ℝ) + 1 ≤ Js n := by exact_mod_cast hg
    linarith
  have h1 : nodeL (mkR wr θ) ≤ nodeS (mkR wr θ) g := by
    unfold nodeS; have : 0 ≤ ((g : ℝ) + 1 / 2) * nodeD (mkR wr θ) := by positivity
    linarith
  have h2 : nodeS (mkR wr θ) g ≤ nodeH (mkR wr θ) := by
    unfold nodeS
    have e : nodeH (mkR wr θ) = nodeL (mkR wr θ) + (Js n : ℝ) * nodeD (mkR wr θ) := by
      unfold nodeD; field_simp; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hg' hD
    linarith
  have := hb _ h1 h2
  linarith

lemma cF_le {A0 A1 A2 a0 a1 a2 y : ℝ} (hy : 0 < y) (h0 : 0 ≤ A0) (h1 : 0 ≤ A1) (h2 : 0 ≤ A2)
    (k0 : A0 ≤ a0 * y ^ 5) (k1 : A1 ≤ a1 * y ^ 5) (k2 : A2 ≤ a2 * y ^ 5) :
    cF0 A0 A1 A2 + cF1 A0 A1 A2 + cF2 A0 A1 A2 ≤
      (cF0 a0 a1 a2 + cF1 a0 a1 a2 + cF2 a0 a1 a2) * y ^ 10 ∧
    cF0 A0 A1 A2 + 2 * cF1 A0 A1 A2 + 8 * cF2 A0 A1 A2 ≤
      (cF0 a0 a1 a2 + 2 * cF1 a0 a1 a2 + 8 * cF2 a0 a1 a2) * y ^ 10 := by
  have hy5 : 0 < y ^ 5 := by positivity
  have g0 : 0 ≤ a0 * y ^ 5 := h0.trans k0
  have g1 : 0 ≤ a1 * y ^ 5 := h1.trans k1
  have g2 : 0 ≤ a2 * y ^ 5 := h2.trans k2
  have ha : (0 : ℝ) < aa := by unfold aa; norm_num
  have c0 : cF0 A0 A1 A2 ≤ cF0 (a0 * y ^ 5) (a1 * y ^ 5) (a2 * y ^ 5) := by
    unfold cF0; gcongr
  have c1 : cF1 A0 A1 A2 ≤ cF1 (a0 * y ^ 5) (a1 * y ^ 5) (a2 * y ^ 5) := by
    unfold cF1; gcongr
  have c2 : cF2 A0 A1 A2 ≤ cF2 (a0 * y ^ 5) (a1 * y ^ 5) (a2 * y ^ 5) := by
    unfold cF2; gcongr
  have e0 : cF0 (a0 * y ^ 5) (a1 * y ^ 5) (a2 * y ^ 5) = cF0 a0 a1 a2 * y ^ 10 := by
    unfold cF0; ring
  have e1 : cF1 (a0 * y ^ 5) (a1 * y ^ 5) (a2 * y ^ 5) = cF1 a0 a1 a2 * y ^ 10 := by
    unfold cF1; field_simp
  have e2 : cF2 (a0 * y ^ 5) (a1 * y ^ 5) (a2 * y ^ 5) = cF2 a0 a1 a2 * y ^ 10 := by
    unfold cF2; ring
  constructor <;> nlinarith

lemma cW_le {A0 A1 A2 a0 a1 a2 y : ℝ} (_hy : 0 < y) (_h1 : 0 ≤ A1)
    (k0 : A0 ≤ a0 * y ^ 6) (k1 : A1 ≤ a1 * y ^ 6) (k2 : A2 ≤ a2 * y ^ 6) :
    cW0 A0 A1 A2 + cW1 A0 A1 A2 + 0 ≤ (cW0 a0 a1 a2 + cW1 a0 a1 a2) * y ^ 6 ∧
    cW0 A0 A1 A2 + 2 * cW1 A0 A1 A2 + 8 * 0 ≤ (cW0 a0 a1 a2 + 2 * cW1 a0 a1 a2) * y ^ 6 := by
  have ha : (0 : ℝ) < aa := by unfold aa; norm_num
  have c0 : cW0 A0 A1 A2 ≤ cW0 a0 a1 a2 * y ^ 6 := by
    unfold cW0
    have : A1 * aa / 2 ≤ a1 * y ^ 6 * aa / 2 := by gcongr
    nlinarith
  have c1 : cW1 A0 A1 A2 ≤ cW1 a0 a1 a2 * y ^ 6 := by
    unfold cW1
    have : A1 / (2 * aa) ≤ a1 * y ^ 6 / (2 * aa) := by gcongr
    have e : (a1 / (2 * aa) + a2) * y ^ 6 = a1 * y ^ 6 / (2 * aa) + a2 * y ^ 6 := by ring
    nlinarith
  constructor <;> nlinarith

/-- **The row-averaged bias moments, any `0 ≤ P_m ≤ 80/n⁴`.** -/
theorem BiasRA_gen (hn : 16384 ≤ n) {Pm : ℝ} (hP0 : 0 ≤ Pm) (hP : Pm ≤ 80 * PmN n)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    (hGb : Gb ⊆ StatEv n (SminN n) (SmaxN n) (DmN n) (DmN n) (VmN n) Pm) :
    BiasMomF (O1n n) Gb (194 / n) ∧ BiasMomW (O1n n) Gb (148 / n) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hbulk : ∀ wr : WRet n, windowW wr → ∀ (θ : AHid n) (g : ℕ), g < Js n →
      nodeS (mkR wr θ) g ^ 2 ≤ 1 := fun wr hw θ g hg => node_bulk16 hn hw θ hg
  have hSm : 0 < SminN n := by unfold SminN; positivity
  have hO : 0 ≤ O1n n := O1n_nonneg n
  obtain ⟨hr, hr2, -⟩ := r_facts16 hn
  set r := √(n : ℝ) with hrd
  have hr0 : 0 < r := by linarith
  set y := 1 / r with hyd
  have hy0 : 0 < y := by positivity
  have hy : y ≤ 1 / 128 := by rw [hyd]; gcongr
  have hNy : (n : ℝ) * y ^ 2 = 1 := by rw [hyd, ← hr2]; field_simp
  have hmy : ((mA n : ℕ) : ℝ) * y ^ 4 = 1 := by
    have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
    rw [hmA, hyd, ← hr2]; field_simp
  have hy5 : ∀ a : ℝ, a / r ^ 5 = a * y ^ 5 := fun a => by rw [hyd]; field_simp
  have hy6 : ∀ a : ℝ, a / r ^ 6 = a * y ^ 6 := fun a => by rw [hyd]; field_simp
  obtain ⟨f0, f0', f1, f1', f2, f2'⟩ := coefF hn hP0 hP
  obtain ⟨w0, w0', w1, w1', w2, w2'⟩ := coefW hn hP0 hP
  rw [hy5] at f0' f1' f2'
  rw [hy6] at w0' w1' w2'
  constructor
  · obtain ⟨hK, hμ⟩ := cF_le hy0 f0 f1 f2 f0' f1' f2'
    refine biasMomF_RA_of_stat hn1 hbulk hO hSm hGb f0 f1 f2 rfl rfl rfl
      (ε := 1 / 20) (t := 10 ^ 26 * y ^ 32) (by norm_num) (by positivity) ?_
    refine finalF hy0 hy hNy hmy (by unfold cF0 cF1 cF2 aa; positivity) hK
      (by unfold cF0 cF1 cF2 aa; positivity) hμ (by norm_num) (by norm_num) (by norm_num) ?_
    unfold sk cF0 cF1 cF2 aa
    norm_num
  · obtain ⟨hK, hμ⟩ := cW_le hy0 w1 w0' w1' w2'
    refine biasMomW_RA_of_stat hn1 hbulk hO hSm hGb w0 w1 w2 rfl rfl (ε := 1 / 50)
      (by norm_num) ?_
    refine finalW hy0 hy hNy hmy (by unfold cW0 cW1 aa; positivity) hK
      (by unfold cW0 cW1 aa; positivity) hμ (by norm_num) (by norm_num) ?_
    unfold sk cW0 cW1 aa
    norm_num

/-- **The row-averaged bias moments with the threshold `P_m = 80/n⁴`.** -/
theorem BiasRA80_proved : ∀ {n : ℕ}, 16384 ≤ n → ∀ {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)},
    Gb ⊆ StatEv n (SminN n) (SmaxN n) (DmN n) (DmN n) (VmN n) (80 * PmN n) →
    BiasMomF (O1n n) Gb (194 / n) ∧ BiasMomW (O1n n) Gb (148 / n) :=
  fun hn _ hGb => BiasRA_gen hn (by unfold PmN; positivity) le_rfl hGb

/-- **The row-averaged bias moments** (`P_m = 68/n⁴`): `BiasRA_stmt`. -/
theorem BiasRA_proved : BiasRA_stmt := by
  intro n hn Gb hGb
  refine BiasRA_gen hn (by unfold PmN; positivity) ?_ hGb
  have : 0 ≤ PmN n := by unfold PmN; positivity
  linarith

end BstLean.Part186

#print axioms BstLean.Part186.BiasRA_gen
#print axioms BstLean.Part186.BiasRA80_proved
#print axioms BstLean.Part186.BiasRA_proved
