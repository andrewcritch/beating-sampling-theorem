import BstLean.Part179TopJM
import BstLean.Part167All

/-!
# Part 179 (file `T167M`): the T167 link of the chain at `n ≥ 26 000`
(namespace `BstLean.Part179.N30.N27.N26`)

No proof is left open; no `native_decide` or `axiom` is used.

A copy of file `Part179TT167L` (the chain at `n ≥ 27 000`) with `27 000 ↦ 26 000`, in the
sub-namespace `N26` (its names shadow those of `N27` and `N30`; the split data `N30.dP`, `N30.KR`,
`N30.dStar` of file `Part179Q`, floor `sd = 0.452`, `η = 1/50`, are used unchanged). The top is
`N30.N27.N26.classifier_paper_JM49m` (file `Part179TopJM`): `K² ≤ 4.9`, bias root `0.00482`,
room `roomJ`.
No numeric change beyond the range.
The docstrings of the copied lemmas can carry older numbers; the Lean statements are authoritative.
-/

namespace BstLean.Part179.N30.N27.N26

-- ===== from Part166End.lean =====
section SPart166End
open BstLean.Part166
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part150 BstLean.Part156 BstLean.Part157
  BstLean.Part160
open BstLean.Part161 (xLat hhMat uHat consV muI latC lamX sigX Ix BIAS_hyp)
open BstLean.Part162 (xLatH tanSq psiA dPaper)
open BstLean.Part153 (nuA)
open BstLean.Part164 (goodA window_goodA goodC16_of_goodA)
open BstLean.Part165 (goodC roomC roomC_ge classifier_paper_root80k)
variable {n : ℕ}
/-- **Part 165's two certificates on the good set.** -/
theorem certsD (hn : 26000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {EA : Set (Ret n)} {c : Ret n} (hc : c ∈ goodD n (paperDesign n fT wT hf hw) EA) :
    (∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
        ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12) ∧
    (∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
        ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (326 / 100 * (2 / n) / n) ^ 12) := by
  set D := paperDesign n fT wT hf hw with hDd
  have hn16 : 16384 ≤ n := by omega
  have hnR : (26000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hD := paperDesign_agentCentre fT wT hf hw
  obtain ⟨hτ, hθ0, hθ1⟩ := window_goodA hn16 fT wT hf hw _ c hc
  have hS : agKey D c ∈ Scert n := hc.2.1.2.1.1.1.2 hτ
  obtain ⟨hcf, hcs⟩ := hS ⟨hτ, hθ0, hθ1⟩
  set k := agKey D c with hk
  have hmk : ∀ {Φ : AgFam n → (Fin n → ℝ) → ℝ},
      Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) => psiK Φ z.1 z.2.1 z.2.2) →
      Measurable (fun z : Ix n × (Fin (n - 1) → ℝ) => psiK Φ k z.1 z.2 ^ 12) := by
    intro Φ hΦ
    have hm : Measurable (fun z : Ix n × (Fin (n - 1) → ℝ) =>
        ((k, z.1, z.2) : AgFam n × Ix n × (Fin (n - 1) → ℝ))) :=
      measurable_const.prodMk (measurable_fst.prodMk measurable_snd)
    have h2 := hΦ.comp hm
    rw [Function.comp_def] at h2
    exact h2.pow_const 12
  -- σ
  have hsig : ∫ a, ∫ v, psiK sK k a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      (326 / 100 * (2 / n) / n) ^ 12 :=
    integral_le_of_lintegral (muI n) (stdGauss (Fin (n - 1))) (fun a v => psiK sK k a v ^ 12)
      (hmk measurable_psiK_s) (fun _ _ => pow_nonneg (psiK_nonneg _ _ _ _) _) (by positivity) hcs
  have hfK : ∫ a, ∫ v, psiK BstLean.Part166.fK k a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (Cf / n) ^ 12 :=
    integral_le_of_lintegral (muI n) (stdGauss (Fin (n - 1))) (fun a v => psiK BstLean.Part166.fK k a v ^ 12)
      (hmk measurable_psiK_f) (fun _ _ => pow_nonneg (psiK_nonneg _ _ _ _) _)
      (by unfold Cf; positivity) hcf
  refine ⟨?_, ?_⟩
  · -- the energy lower bound `e_b ≥ 0.6425`
    have hG := goodC16_of_goodA hn16 fT wT hf hw hc
    have hU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n := hc.2.2.1.2 hτ
    have hlo := eb16_lower hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hU
    have hb : D.bA c.1 c.2.1.1 =
        (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) := hD c
    rw [← hb] at hlo
    have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
    rw [hmA] at hlo
    set e := normSq (D.bA c.1 c.2.1.1) / n with he
    have he0 : 257 / 400 ≤ e := by
      rw [he, le_div_iff₀ hn0]
      have h2 : 2 / (n : ℝ) * (257 / 400) * (n ^ 2 / 2) ≤
          2 / (n : ℝ) ^ 2 * normSq (D.bA c.1 c.2.1.1) * (n ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hlo (by positivity)
      have l : 2 / (n : ℝ) * (257 / 400) * (n ^ 2 / 2) = 257 / 400 * n := by field_simp
      have r : 2 / (n : ℝ) ^ 2 * normSq (D.bA c.1 c.2.1.1) * (n ^ 2 / 2) =
          normSq (D.bA c.1 c.2.1.1) := by field_simp
      linarith
    have hepos : 0 < e := lt_of_lt_of_le (by norm_num) he0
    have hpt : ∀ a v, psiA (lamX D c) D c a v ^ 12 = (e⁻¹) ^ 12 * psiK BstLean.Part166.fK k a v ^ 12 := by
      intro a v
      have h := psiA_lam_eq (by omega) D hD c a v
      rw [← he] at h
      rw [← h, mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hepos.ne', one_pow, one_mul]
    simp_rw [hpt, integral_const_mul]
    calc (e⁻¹) ^ 12 * ∫ a, ∫ v, psiK BstLean.Part166.fK k a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n
        ≤ (e⁻¹) ^ 12 * (Cf / n) ^ 12 := mul_le_mul_of_nonneg_left hfK (by positivity)
      _ = (Cf / e / n) ^ 12 := by rw [← mul_pow]; congr 1; field_simp
      _ ≤ (51 / 10 / n) ^ 12 := by
          apply pow_le_pow_left₀ (by unfold Cf; positivity)
          apply div_le_div_of_nonneg_right _ hn0.le
          rw [div_le_iff₀ hepos]
          unfold Cf
          linarith
  · simp_rw [psiA_sig_eq D hD c]
    exact hsig

end SPart166End

-- ===== from Part167Fin.lean (rest) =====
section SPart167Fin
open BstLean.Part167
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part150 BstLean.Part156 BstLean.Part157
  BstLean.Part160
open BstLean.Part161 (muI Ix BIAS_hyp)
open BstLean.Part162 (dPaper)
open BstLean.Part153 (nuA)
open BstLean.Part166 (goodD)
variable {n : ℕ}
/-- **The classifier theorem with Lemma LJ reduced to the moments `X` and `Y`.** -/
theorem classifier_paper_XY26k (hn : 26000 ≤ n) {X2 Y2 : ℝ} (hX2 : 0 < X2) (hY2 : 0 < Y2)
    (hXY : XY_hyp n X2 Y2) (hK : K2XY n X2 Y2 ≤ 49 / 10)
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomJ)
    (hB : ∀ c ∈ goodD n (paperDesign n fT wT hf hw) EA,
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (452 / 1000))
          (1 / 50) (by norm_num) (by norm_num)) (482 / 10 ^ 5)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  BstLean.Part179.N30.N27.N26.classifier_paper_JM49m (by omega) (JM_mono (by unfold K2XY; positivity) hK (JM_of_XY (by omega) hX2 hY2 hXY))
    fT wT hf hw t hEA hA hroom hB

end SPart167Fin

-- ===== from Part167Y.lean =====
section SPart167Y
open BstLean.Part167
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part151 (mask mask_nonneg mask_sq measurable_mask)
variable {n m : ℕ}
open BstLean.Part161 (Ix uHat xLat)
open BstLean.Part162 (dirW)
open BstLean.Part166 (winC)
open BstLean.Part157 (latitude)
open BstLean.Part53 (unitF53)
/-- **The masked Frobenius moment is proved**: `Ymom ≤ Y2n^{64}` for every `n ≥ 45 000`. -/
theorem Y_bound (hn : 26000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hw : winC c τ) (a : Ix n)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) :
    Ymom c τ a v ≤ ENNReal.ofReal (Y2n n ^ 64) := by
  have hn1 : 1 ≤ n := by omega
  have hc := window_c_ne hn1 hw
  obtain ⟨hu, hw1, huw⟩ := frame_orth hn1 hc hv
  set s := latitude (n := n) (√(normSq c)) τ a with hsdef
  have hs : s ^ 2 ≤ 1 := BstLean.Part162.latitude_sq_le _ _ _
  set cc := √(1 - s ^ 2)
  have hsc : s ^ 2 + cc ^ 2 = 1 := by rw [Real.sq_sqrt (by linarith)]; ring
  have hc' : (rc c).1.2 ≠ 0 := hc
  have hx : xLat (rc c) s (unitF53 v) = s • uHat (rc c) + cc • dirW (rc c) (unitF53 v) :=
    BstLean.Part161.xLat_eq hn1 hc' s (unitF53 v)
  have hx1 : normSq (s • uHat (rc c) + cc • dirW (rc c) (unitF53 v)) = 1 := by
    rw [normSq_two, hu, hw1, huw]; linarith
  unfold Ymom
  rw [← hsdef, hx]
  have hpt : ∀ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ,
      ENNReal.ofReal (frobSq (Pmat (uHat (rc c)) (dirW (rc c) (unitF53 v)) *
        (D1A1 A₁ (s • uHat (rc c) + cc • dirW (rc c) (unitF53 v)))ᵀ) ^ 64) ≤
      ENNReal.ofReal (Qf A₁ (s • uHat (rc c) + cc • dirW (rc c) (unitF53 v)) ^ 64) := fun A₁ =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (frobSq_nonneg _)
      (frob_le_Q hu hw1 huw hsc A₁) 64)
  refine (lintegral_mono hpt).trans ?_
  have hnR : (26000 : ℝ) ≤ n := by exact_mod_cast hn
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hM := Y2n_pos (n := n) (by omega)
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hd : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1]; simp
  have hτ : 64 / Y2n n * (2 / (n : ℝ)) =
      64 / (1001 / 1000 * (((mA n : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) / 2)) := by
    unfold Y2n; field_simp
  refine Q_mom hn1 hx1 hγ hM ?_ ?_
  · rw [hτ, hmA, hd, div_lt_iff₀ (by nlinarith)]
    nlinarith
  · rw [hτ]
    exact Y_num (d := n - 1) (m := mA n) (by omega) (by unfold mA; nlinarith)

theorem XY_of_X (hn : 26000 ≤ n) {X2 : ℝ} (h : X_hyp n X2) : XY_hyp n X2 (Y2n n) :=
  fun c τ hw a v hv => ⟨(h c τ hw a v hv).1, (h c τ hw a v hv).2, Y_bound hn hw a hv⟩

open BstLean.Part134 BstLean.Part150 BstLean.Part156 BstLean.Part157 BstLean.Part160 in
open BstLean.Part161 (BIAS_hyp) in
open BstLean.Part162 (dPaper) in
open BstLean.Part166 (goodD) in
/-- **The classifier theorem with Lemma LJ reduced to the plane moment `X` alone** (`Y` and `Z`
are proved; every `n ≥ 45 000`, floor `d_low = 0.22005`, room `roomE ≥ 0.001792`). -/
theorem classifier_paper_X26k (hn : 26000 ≤ n) {X2 : ℝ} (hX2 : 0 < X2) (hX : X_hyp n X2)
    (hK : K2XY n X2 (Y2n n) ≤ 49 / 10)
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomJ)
    (hB : ∀ c ∈ goodD n (paperDesign n fT wT hf hw) EA,
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (452 / 1000))
          (1 / 50) (by norm_num) (by norm_num)) (482 / 10 ^ 5)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_XY26k hn hX2 (Y2n_pos (by omega)) (XY_of_X hn hX) hK fT wT hf hw t hEA hA
    hroom hB

end SPart167Y

end BstLean.Part179.N30.N27.N26
