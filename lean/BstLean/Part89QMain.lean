import BstLean.Part89MainS
import BstLean.Part89QDefs2
import BstLean.Part89QSlice
import BstLean.Part89QVar
import BstLean.Part89QInst
import BstLean.Part89QPt
import BstLean.Part89QCore2
import BstLean.Part88Semi

/-!
# Part 89, `d_f = 2`: the failure bound from the numeric conditions `NumQ`

The sphere step at `k = 2` with the anchor-averaged variance bound (`quadVar`) in place of the
slice reverse Hölder inequality, then `failQ_core2`.

No `sorry`, no `native_decide`, no `axiom`.
-/

namespace BstLean.Part89

open scoped ENNReal
open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD)
open BstLean.Part41 (Mono Tens TSymm)
open BstLean.Part53 (radF53)
open BstLean.Part56
open BstLean.Part80 (e80)
open BstLean.Part86 BstLean.Part86.XGauss

/-- The coefficient of `cV` in `semiBound89`. -/
noncomputable def KSq (n k : ℕ) (N efl b β ξ : ℝ) : ℝ :=
  BstLean.Part88.SE (2 * k) β ξ / ((1 - b) ^ 2 * (1 - efl) ^ 2 * n) /
    ((1 - ξ ^ 2) * (1 - 2 / (N * (99 / 100 * ξ * β) ^ 2)))

lemma semiBound_aff (n k : ℕ) (N c1 cV efl a b β ξ : ℝ) :
    semiBound89 n k N c1 cV efl a b β ξ =
      5 / 2 * ((k : ℝ) + 1) ^ 2 * c1 / (a * n) + KSq n k N efl b β ξ * cV := by
  unfold semiBound89 KSq; ring

lemma SE_nonneg89 (D : ℕ) (β ξ : ℝ) : 0 ≤ BstLean.Part88.SE D β ξ := by
  unfold BstLean.Part88.SE
  exact le_trans (le_trans zero_le_one (BstLean.Part88.SS_ge_one _ ξ)) (le_max_left _ _)

lemma KSq_nonneg (n k : ℕ) (N efl b β ξ : ℝ) (hξ2 : ξ ^ 2 ≤ 1)
    (hν : 2 / (N * (99 / 100 * ξ * β) ^ 2) < 1) : 0 ≤ KSq n k N efl b β ξ := by
  unfold KSq
  have h1 := SE_nonneg89 (2 * k) β ξ
  have h2 : 0 ≤ 1 - ξ ^ 2 := by linarith
  have h3 : 0 ≤ 1 - 2 / (N * (99 / 100 * ξ * β) ^ 2) := by linarith
  have h4 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  positivity

/-- The coefficient of `y` in `cV0Q`. -/
noncomputable def KcQ (d : ℕ) (L η η' ω β : ℝ) : ℝ :=
  2 * L / (1 - L) * ((1 + 1 / ω) * ((2 + η) * (1 + 1 / η') * kapQ d β) / (2 * (49 / 100)))

lemma cV0Q_aff (d : ℕ) (L η η' ω β y : ℝ) :
    cV0Q d L η η' ω β y = cV0Q d L η η' ω β 0 + KcQ d L η η' ω β * y := by
  unfold cV0Q XQ KcQ; ring

lemma cVW_aff (k : ℕ) (t L cV0 ϑ : ℝ) :
    cVW k t L cV0 ϑ = cVW k t L 0 ϑ + (1 + ϑ) * (1 + e1S k t) ^ 2 * cV0 := by
  unfold cVW; ring

/-- The coefficient of `y` in `gQ`. -/
noncomputable def KgQ (m d : ℕ) (η η' ω ϑ b β ξ : ℝ) : ℝ :=
  KSq (m + 1) 2 (DWr (m + 1) (JR (m + 1) d)) (CLs d / (m : ℝ)) b β ξ *
    (((m + 1 : ℕ) : ℝ) * ((1 + ϑ) * (1 + e1S 2 (tS (m + 1) β)) ^ 2 *
      KcQ d (CLs d / (m : ℝ)) η η' ω β))

lemma gQ_aff0 (m d : ℕ) (η η' ω ϑ a b β ξ y : ℝ) :
    gQ m d η η' ω ϑ a b β ξ y =
      gQ m d η η' ω ϑ a b β ξ 0 + KgQ m d η η' ω ϑ b β ξ * y := by
  unfold gQ KgQ
  rw [semiBound_aff, semiBound_aff, cVW_aff 2 _ _ (cV0Q _ _ _ _ _ _ y),
    cVW_aff 2 _ _ (cV0Q _ _ _ _ _ _ 0), cV0Q_aff d _ _ _ _ _ y]
  ring

lemma gQ_aff (m d : ℕ) (η η' ω ϑ a b β ξ y : ℝ) :
    gQ m d η η' ω ϑ a b β ξ y =
      gQ m d η η' ω ϑ a b β ξ 0 +
        (gQ m d η η' ω ϑ a b β ξ 1 - gQ m d η η' ω ϑ a b β ξ 0) * y := by
  rw [gQ_aff0 m d η η' ω ϑ a b β ξ y, gQ_aff0 m d η η' ω ϑ a b β ξ 1]
  ring

lemma kapQ_nonneg (d : ℕ) (β : ℝ) (hβ : β < 1) : 0 ≤ kapQ d β := by
  unfold kapQ
  have : 0 < 1 - β := by linarith
  positivity

lemma cV0Q_nonneg (d : ℕ) (L η η' ω β y : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1) (hη : 0 < η)
    (hη' : 0 < η') (hω : 0 < ω) (hβ : β < 1) (hy : 0 ≤ y) : 0 ≤ cV0Q d L η η' ω β y := by
  unfold cV0Q XQ
  have h1 : 0 < 1 - L := by linarith
  have h2 := kapQ_nonneg d β hβ
  have h3 := c0q_nonneg η hη
  have h4 : 0 ≤ kapQ d β * y := mul_nonneg h2 hy
  have h5 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  positivity

lemma CLs_div_nonneg (m d : ℕ) : (0 : ℝ) ≤ CLs d / (m : ℝ) := by unfold CLs; positivity

lemma NumQ.xi_sq {m d : ℕ} {η η' ω ϑ a b β ξ : ℝ} (hN : NumQ m d η η' ω ϑ a b β ξ) :
    ξ ^ 2 ≤ 1 := by
  have h1 := hN.hξ; have h2 := hN.hξ2
  nlinarith

lemma gQ_zero_nonneg (m d : ℕ) (η η' ω ϑ a b β ξ : ℝ) (hN : NumQ m d η η' ω ϑ a b β ξ) :
    0 ≤ gQ m d η η' ω ϑ a b β ξ 0 := by
  have hL0 := CLs_div_nonneg m d
  have hK := KSq_nonneg (m + 1) 2 (DWr (m + 1) (JR (m + 1) d)) (CLs d / (m : ℝ)) b β ξ
    hN.xi_sq hN.hν
  have hc := cV0Q_nonneg d (CLs d / (m : ℝ)) η η' ω β 0 hL0 (by linarith [hN.hL10]) hN.hη
    hN.hη' hN.hω (by linarith [hN.hβ4]) le_rfl
  have hW := cVW_nonneg 2 (tS (m + 1) β) (CLs d / (m : ℝ)) _ ϑ hc hN.hϑ
  have hn0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ha := hN.ha
  unfold gQ
  rw [semiBound_aff]
  have h1 : 0 ≤ ((m + 1 : ℕ) : ℝ) * (CLs d / (m : ℝ)) + 2 := by
    have := mul_nonneg hn0 hL0; linarith
  have h2 : 0 ≤ ((m + 1 : ℕ) : ℝ) * cVW 2 (tS (m + 1) β) (CLs d / (m : ℝ))
      (cV0Q d (CLs d / (m : ℝ)) η η' ω β 0) ϑ := mul_nonneg hn0 hW
  have h3 : 0 ≤ 5 / 2 * (((2 : ℕ) : ℝ) + 1) ^ 2 *
      (((m + 1 : ℕ) : ℝ) * (CLs d / (m : ℝ)) + 2) / (a * ((m + 1 : ℕ) : ℝ)) := by positivity
  exact add_nonneg h3 (mul_nonneg hK h2)

lemma KgQ_nonneg (m d : ℕ) (η η' ω ϑ a b β ξ : ℝ) (hN : NumQ m d η η' ω ϑ a b β ξ) :
    0 ≤ KgQ m d η η' ω ϑ b β ξ := by
  have hL0 := CLs_div_nonneg m d
  have hK := KSq_nonneg (m + 1) 2 (DWr (m + 1) (JR (m + 1) d)) (CLs d / (m : ℝ)) b β ξ
    hN.xi_sq hN.hν
  have hk := kapQ_nonneg d β (by linarith [hN.hβ4])
  have h1 : 0 < 1 - CLs d / (m : ℝ) := by linarith [hN.hL10]
  have hη := hN.hη; have hη' := hN.hη'; have hω := hN.hω; have hϑ := hN.hϑ
  have hc : 0 ≤ KcQ d (CLs d / (m : ℝ)) η η' ω β := by
    unfold KcQ; positivity
  unfold KgQ
  have hn0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  positivity

/-- The pointwise sphere step at `d_f = 2`. -/
theorem ptQ (m d : ℕ) (hd : 2 ≤ d) (η η' ω ϑ a b β ξ : ℝ)
    (hN : NumQ m d η η' ω ϑ a b β ξ)
    (v : Fin (m + 1) → ℝ) (hv : UnitV v) (t : ℝ) (ht0 : 0 ≤ t) (htn : t ≤ ((m + 1 : ℕ) : ℝ))
    (E : JR (m + 1) d → Mono (m + 1) d → ℝ) (hE : RotE v E)
    (f0 : ℝ) (T : Tens (m + 1)) (ℓ : Fin (m + 1) → ℝ)
    (H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hHs : H.IsSymm)
    (hrep : ∀ (U : Fin (d + 1) × Fin (m + 1) → ℝ) (r sc : ℝ),
      QuadRep (modRK m d t v E) (PU 2 f0 T U r sc) f0 ℓ H (fun j i => U (j, i) / r) sc)
    (U : Fin (d + 1) × Fin (m + 1) → ℝ) (W' : JR (m + 1) d × Fin (m + 1) → ℝ)
    (hlam : |lam0 (DD (m + 1) d) (DWr (m + 1) (JR (m + 1) d)) U (radF53 W') ^ 2 - 1| ≤
      1 / (((m + 1 : ℕ) : ℝ)))
    (hρ : 100 / 101 * DWr (m + 1) (JR (m + 1) d) ≤ radF53 W' ^ 2) :
    stdGauss (JR (m + 1) d × Fin (m + 1))
        (badSet86 (modRK m d t v E) (gqRK m d (KRK 1 (m + 1) e80) t v E)
          (PU 2 f0 T U (Real.sqrt (∑ a, U a ^ 2 + radF53 W' ^ 2))
            (1 / Real.sqrt (DD (m + 1) d)))
          (lam0 (DD (m + 1) d) (DWr (m + 1) (JR (m + 1) d)) U (radF53 W'))) ≤
      ENNReal.ofReal (gQ m d η η' ω ϑ a b β ξ (Ytil H U)) := by
  have hNN := hN
  obtain ⟨h100, h5000, hdn, hL10, hη, hη', hω, hϑ, ha, hb0, hb1, hab, hβ, hβ4, hξ, hξ2, hξβ,
    hν⟩ := hN
  have hL0 : (0 : ℝ) ≤ CLs d / (m : ℝ) := CLs_div_nonneg m d
  have hR := XInst.regRK m d t v hv E
  have hPF := polyFacts (modRK m d t v E) hR
  have hRF := rotFacts86 (m + 1) d
  have hT2 := XRotB.rot_twoPt v hv E hE
  have hS := XInst.sliceOp_modRK m d t v hv E hE hRF (CLs d)
    (XSliceOp.sliceOpRK_fact m d (by omega) h5000)
  have hD := decor86 (modRK m d t v E) d _ hR hT2 hS hL0
  have hSc := scale86 (modRK m d t v E) 2 (by omega) hT2 h100 (by omega)
  have hSE := scaleE89 (modRK m d t v E) 2 (by omega) hT2 (by omega)
  have hSu := XInst.surrHyp_modRK m d (by omega) t v hv E ht0 htn
  have hn0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
  have hOp := instSliceOpF m d t v E (by omega) h5000 hv hE
  have hQS := quadSlice (modRK m d t v E) d (CLs d / (m : ℝ)) (d : ℝ)
    (fun p => axialR p.1 (radF53 p.2) ^ 2) hR (instSph m d t v E (by omega) hv) hOp
    (instKmax m d t v E hv hE) (instBbd m d t v E) hL0 (by linarith) hd0
  have hQV : QuadVar (modRK m d t v E) (CLs d / (m : ℝ)) (d : ℝ) (49 / 100) :=
    quadVar (modRK m d t v E) d (CLs d / (m : ℝ)) (d : ℝ) (49 / 100)
      (fun p => axialR p.1 (radF53 p.2) ^ 2) hR hPF hOp hQS hL0 (by linarith) hd0
      (fun p => (instTauLe m p).trans hd1) (by norm_num) (instTmin m t v h100 hv ht0 htn)
  have hDD : 0 < DD (m + 1) d := BstLean.Part89.DD_pos (m + 1) d (by omega)
  have hDW : 0 < DWr (m + 1) (JR (m + 1) d) := DWr_pos (m + 1) d hd hdn h100
  set P := PU 2 f0 T U (Real.sqrt (∑ a, U a ^ 2 + radF53 W' ^ 2))
    (1 / Real.sqrt (DD (m + 1) d)) with hPdef
  set lam := lam0 (DD (m + 1) d) (DWr (m + 1) (JR (m + 1) d)) U (radF53 W') with hlamdef
  have hQ : QuadRep (modRK m d t v E) P f0 ℓ H
      (fun j i => U (j, i) / Real.sqrt (∑ a, U a ^ 2 + radF53 W' ^ 2))
      (1 / Real.sqrt (DD (m + 1) d)) := hrep U _ _
  have hP : P.totalDegree ≤ 2 := PU_degree 2 f0 T U _ _
  have hdq := dq_bound H U (radF53 W') (DD (m + 1) d) (DWr (m + 1) (JR (m + 1) d)) hDD hDW hρ
  rw [Fintype.card_fin] at hdq
  push_cast at hdq
  rw [← hlamdef] at hdq
  have hY0 := Ytil_nonneg H U
  have hF0 := frobH_nonneg H
  have h1β : 0 < 1 - β := by linarith
  have hkap := kapQ_nonneg d β (by linarith)
  have hcV0 : 0 ≤ cV0Q d (CLs d / (m : ℝ)) η η' ω β (Ytil H U) :=
    cV0Q_nonneg d _ η η' ω β _ hL0 (by linarith) hη hη' hω (by linarith) hY0
  have hG := gmw_of (modRK m d t v E) d 2 (CLs d / (m : ℝ))
    (cV0Q d (CLs d / (m : ℝ)) η η' ω β (Ytil H U)) β ϑ (by omega) hR hPF hD hSc hSE hL0
    (by linarith) hcV0 hβ (by linarith) hϑ P hP lam hlam
    (by
      intro u hu1 hu2
      have hu0 : 0 ≤ u := by linarith
      have hl2 : (|lam| * Real.sqrt u) ^ 2 = lam ^ 2 * u := by
        rw [mul_pow, sq_abs, Real.sq_sqrt hu0]
      have hbase : 0 ≤ 16 * ((d : ℝ) + 1) * (101 / 100) * Ytil H U *
          (lam ^ 2 * (1 / Real.sqrt (DD (m + 1) d)) ^ 2 * BstLean.Part78.frobH H) := by
        positivity
      have hratio : 1 ≤ u / (1 - β) := by rw [le_div_iff₀ h1β]; linarith
      have hDq : Dq H (fun j i => U (j, i) / Real.sqrt (∑ a, U a ^ 2 + radF53 W' ^ 2)) ≤
          kapQ d β * Ytil H U * ((|lam| * Real.sqrt u) ^ 2 *
            (1 / Real.sqrt (DD (m + 1) d)) ^ 2 * BstLean.Part78.frobH H) := by
        refine hdq.trans ?_
        rw [hl2]
        have e : kapQ d β * Ytil H U * (lam ^ 2 * u *
            (1 / Real.sqrt (DD (m + 1) d)) ^ 2 * BstLean.Part78.frobH H) =
            16 * ((d : ℝ) + 1) * (101 / 100) * Ytil H U *
              (lam ^ 2 * (1 / Real.sqrt (DD (m + 1) d)) ^ 2 * BstLean.Part78.frobH H) *
              (u / (1 - β)) := by
          unfold kapQ; ring
        rw [e]
        exact le_mul_of_one_le_right hbase hratio
      have hv1 := hQV P f0 ℓ H _ _ hHs hQ (|lam| * Real.sqrt u) η η' ω (kapQ d β * Ytil H U)
        hη hη' hω (mul_nonneg hkap hY0) hDq
      have hnn := intYbar_nonneg (modRK m d t v E) P (|lam| * Real.sqrt u)
      have hle := intYbar_le_q (modRK m d t v E) d hR hPF P (|lam| * Real.sqrt u)
      have hsq : (∫ p, Ybar (modRK m d t v E) P (|lam| * Real.sqrt u) p
            ∂(modRK m d t v E).pi) ^ 2 ≤
          (∫ p, qsl (modRK m d t v E) P (|lam| * Real.sqrt u) p ∂(modRK m d t v E).pi) ^ 2 :=
        pow_le_pow_left₀ hnn hle 2
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hsq hcV0)
      exact hv1)
  have hc1 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (CLs d / (m : ℝ)) + 2 := by
    have := mul_nonneg hn0 hL0; linarith
  have hcV : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) *
      cVW 2 (tS (m + 1) β) (CLs d / (m : ℝ))
        (cV0Q d (CLs d / (m : ℝ)) η η' ω β (Ytil H U)) ϑ :=
    mul_nonneg hn0 (cVW_nonneg _ _ _ _ _ hcV0 hϑ)
  have h40 : (0 : ℝ) ≤ 1 / 40 := by norm_num
  exact remezSemiP (modRK m d t v E) d 2 _ _ _ (1 / 40) a b β ξ _ (by omega) (by omega) hR hPF
    P hP lam hG hSu h40 le_rfl hL0 (by linarith) ha hb0 hb1 hab hβ hβ4 hξ hξ2 hξβ hν hc1 hcV
    (card_W_ge (m + 1) d hd hdn h100)

/-- **The failure bound on the coefficient sphere at `d_f = 2`** from the numeric conditions. -/
theorem failQ_of (m d : ℕ) (hd : 2 ≤ d) (η η' ω ϑ a b β ξ : ℝ)
    (hN : NumQ m d η η' ω ϑ a b β ξ)
    (hb : gQ m d η η' ω ϑ a b β ξ ((d : ℝ) + 1) + 100 / ((m + 1 : ℕ) : ℝ) +
        20808 / DWr (m + 1) (JR (m + 1) d) ≤ 1 / 100)
    (v : Fin (m + 1) → ℝ) (hv : UnitV v) (t : ℝ) (ht0 : 0 ≤ t) (htn : t ≤ ((m + 1 : ℕ) : ℝ))
    (f0 : ℝ) (T : Tens (m + 1)) (hT : TSymm 2 T) :
    stdGauss (CoefIdxD (m + 1) d) (SphereFail86 (m + 1) d 2 (KRK 1 (m + 1) e80) t v f0 T) ≤
      ENNReal.ofReal (1 / 100) := by
  obtain ⟨E, hE⟩ := rotExists (m + 1) d v hv
  have hRF := rotFacts86 (m + 1) d
  have hPol := XPolar.polarRed86 m d 2 (KRK 1 (m + 1) e80) (by omega)
    (card_JR_pos (m + 1) d (by omega) (by have := hN.h100; omega)) hRF
    (XIdent.ident86 m d 2 (KRK 1 (m + 1) e80) (by omega) hRF)
  have hTail := tail86 (m + 1) d hd hN.hdn hN.h100
  obtain ⟨ℓ, H, hHs, -, hrep⟩ := instQuadRep m d t v E f0 T hT
  have hDW : 0 < DWr (m + 1) (JR (m + 1) d) := DWr_pos (m + 1) d hd hN.hdn hN.h100
  have hA0 := gQ_zero_nonneg m d η η' ω ϑ a b β ξ hN
  have hA1 : 0 ≤ gQ m d η η' ω ϑ a b β ξ 1 - gQ m d η η' ω ϑ a b β ξ 0 := by
    have h := gQ_aff0 m d η η' ω ϑ a b β ξ 1
    have h2 := KgQ_nonneg m d η η' ω ϑ a b β ξ hN
    linarith
  have hcore := failQ_core2 m d (KRK 1 (m + 1) e80) 100 (gQ m d η η' ω ϑ a b β ξ 0)
    (gQ m d η η' ω ϑ a b β ξ 1 - gQ m d η η' ω ϑ a b β ξ 0) t v ht0 hv E hE hPol hTail f0 T hT
    H hA0 hA1 hDW
    (by
      intro U W' h1 h2
      rw [← gQ_aff]
      exact ptQ m d hd η η' ω ϑ a b β ξ hN v hv t ht0 htn E hE f0 T ℓ H hHs hrep U W' h1 h2)
  rw [← gQ_aff] at hcore
  refine hcore.trans ?_
  have hg : 0 ≤ gQ m d η η' ω ϑ a b β ξ ((d : ℝ) + 1) := by
    rw [gQ_aff]
    have : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
    exact add_nonneg hA0 (mul_nonneg hA1 this)
  have hn0 : (0 : ℝ) ≤ 100 / ((m + 1 : ℕ) : ℝ) := by positivity
  rw [← ENNReal.ofReal_add hg hn0, ← ENNReal.ofReal_add (add_nonneg hg hn0) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hb

end BstLean.Part89

#print axioms BstLean.Part89.failQ_of
