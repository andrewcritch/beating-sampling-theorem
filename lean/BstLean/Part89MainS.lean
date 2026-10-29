import BstLean.Part89Main
import BstLean.Part89Scale
import BstLean.Part89GaussW
import BstLean.Part89Semi
import BstLean.Part89Aux

/-!
# Part 89, every degree pair, second pass: the semicircle sphere step

The sphere step for the variance uses the semicircle transfer of Part 88 (`remezSemiP`) in place
of Lemma R+. `FailS d k N` : the failure bound for `n ≥ N` from numeric conditions.
-/

namespace BstLean.Part89

open scoped ENNReal
open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part41 (Mono Tens TSymm)
open BstLean.Part56
open BstLean.Part80 (e80)
open BstLean.Part86

/-- The variance constant on the window for the route of Part 86: `Λ = L`. -/
noncomputable def cVS (n d k : ℕ) (L β ϑ : ℝ) : ℝ :=
  n * cVW k (tS n β) L (104 / 100 * (L * 9 ^ (d * k))) ϑ

/-- The bound of the sphere step. -/
noncomputable def boundS (n d k : ℕ) (L a b β ξ ϑ : ℝ) : ℝ :=
  semiBound89 n k (DWr n (JR n d)) (n * L + 2) (cVS n d k L β ϑ) L a b β ξ

/-- The numeric conditions of the assembly, at `L = CLs d / m`, `n = m + 1`. -/
structure NumS (m d k : ℕ) (a b β ξ ϑ : ℝ) : Prop where
  h100 : 100 ≤ m + 1
  h5000 : 5000 ≤ m
  h4k : 4 * k ^ 4 ≤ m + 1
  hdn : d ≤ m + 1
  hLC : CLs d / (m : ℝ) * 9 ^ (d * k) ≤ 1 / 100
  hK : 10000 * ((9 : ℝ) ^ k * (CLs d / (m : ℝ))) ≤ 9 ^ (d * k)
  hL10 : CLs d / (m : ℝ) ≤ 1 / 10
  ha : 0 < a
  hb0 : 0 ≤ b
  hb1 : b < 1
  hab : 9 / 4 * a + 1 / 400 ≤ b * (1 - CLs d / (m : ℝ)) / 4
  hβ : 0 < β
  hβ4 : β ≤ 1 / 4
  hξ : 0 < ξ
  hξ2 : ξ ≤ 1 / 2
  hξβ : ξ * β ≤ 1 / 100
  hϑ : 0 < ϑ
  hν : 2 / (DWr (m + 1) (JR (m + 1) d) * (99 / 100 * ξ * β) ^ 2) < 1

theorem cVW_nonneg (k : ℕ) (t L cV0 ϑ : ℝ) (hcV0 : 0 ≤ cV0) (hϑ : 0 < ϑ) :
    0 ≤ cVW k t L cV0 ϑ := by
  unfold cVW
  have : 0 ≤ 1 / ϑ := by positivity
  positivity

/-- The sphere step for the model of `D_{t,v}`, semicircle form. -/
theorem remezS_modRK (m d k : ℕ) (hk : 2 ≤ k) (hd : 2 ≤ d) (a b β ξ ϑ : ℝ)
    (hN : NumS m d k a b β ξ ϑ)
    (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v) (E : JR (m + 1) d → Mono (m + 1) d → ℝ)
    (hE : RotE v E) (ht0 : 0 ≤ t) (htn : t ≤ ((m + 1 : ℕ) : ℝ)) :
    RemezStep86 (modRK m d t v E) k (gqRK m d (KRK 1 (m + 1) e80) t v E)
      (boundS (m + 1) d k (CLs d / (m : ℝ)) a b β ξ ϑ) := by
  obtain ⟨h100, h5000, h4k, hdn, hLC, hK, hL10, ha, hb0, hb1, hab, hβ, hβ4, hξ, hξ2, hξβ, hϑ,
    hν⟩ := hN
  have hL0 : (0 : ℝ) ≤ CLs d / (m : ℝ) := by unfold CLs; positivity
  have hR := XInst.regRK m d t v hv E
  have hPF := polyFacts (modRK m d t v E) hR
  have hRF := rotFacts86 (m + 1) d
  have hT := XRotB.rot_twoPt v hv E hE
  have hS := XInst.sliceOp_modRK m d t v hv E hE hRF (CLs d)
    (XSliceOp.sliceOpRK_fact m d (by omega) h5000)
  have hD := decor86 (modRK m d t v E) d _ hR hT hS hL0
  have hSc := scale86 (modRK m d t v E) k (by omega) hT h100 h4k
  have hSE := scaleE89 (modRK m d t v E) k (by omega) hT (by omega)
  have hRH := sliceRH_modRK9 m d t v hv E (d * k) (sliceRHRK9 m (d * k) (by omega))
  have hSu := XInst.surrHyp_modRK m d (by omega) t v hv E ht0 htn
  have hn0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcV0 : (0 : ℝ) ≤ 104 / 100 * (CLs d / (m : ℝ) * 9 ^ (d * k)) := by positivity
  intro P hP lam hlam
  have hG := gmw_of (modRK m d t v E) d k (CLs d / (m : ℝ))
    (104 / 100 * (CLs d / (m : ℝ) * 9 ^ (d * k))) β ϑ (by omega) hR hPF hD hSc hSE hL0
    (by linarith) hcV0 hβ (by linarith) hϑ P hP lam hlam
    (fun u _ _ => varAll89 (modRK m d t v E) d k (CLs d / (m : ℝ)) (9 ^ (d * k)) ((9 : ℝ) ^ k)
      (by omega) hR hPF hD hRH (BstLean.Part84.fourth84_nine k) hL0 hLC hK (by positivity)
      (by positivity) P hP _)
  have hc1 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (CLs d / (m : ℝ)) + 2 := by
    have := mul_nonneg hn0 hL0; linarith
  have hcV : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) *
      cVW k (tS (m + 1) β) (CLs d / (m : ℝ)) (104 / 100 * (CLs d / (m : ℝ) * 9 ^ (d * k))) ϑ :=
    mul_nonneg hn0 (cVW_nonneg _ _ _ _ _ hcV0 hϑ)
  have h40 : (0 : ℝ) ≤ 1 / 40 := by norm_num
  exact remezSemiP (modRK m d t v E) d k _ _ _ (1 / 40) a b β ξ _ (by omega) (by omega) hR hPF
    P hP lam hG hSu h40 le_rfl hL0 (by linarith) ha hb0 hb1 hab hβ hβ4 hξ hξ2 hξβ hν hc1 hcV
    (card_W_ge (m + 1) d hd hdn h100)

/-- **The failure bound on the coefficient sphere** from the numeric conditions. -/
theorem failS_of (m d k : ℕ) (hk : 2 ≤ k) (hd : 2 ≤ d) (a b β ξ ϑ : ℝ)
    (hN : NumS m d k a b β ξ ϑ)
    (hb : boundS (m + 1) d k (CLs d / (m : ℝ)) a b β ξ ϑ + 100 / ((m + 1 : ℕ) : ℝ) ≤ 1 / 100)
    (hb0 : 0 ≤ boundS (m + 1) d k (CLs d / (m : ℝ)) a b β ξ ϑ)
    (v : Fin (m + 1) → ℝ) (hv : UnitV v) (t : ℝ) (ht0 : 0 ≤ t) (htn : t ≤ ((m + 1 : ℕ) : ℝ))
    (f0 : ℝ) (T : Tens (m + 1)) (hT : TSymm k T) :
    stdGauss (CoefIdxD (m + 1) d) (SphereFail86 (m + 1) d k (KRK 1 (m + 1) e80) t v f0 T) ≤
      ENNReal.ofReal (1 / 100) := by
  obtain ⟨E, hE⟩ := rotExists (m + 1) d v hv
  have hRF := rotFacts86 (m + 1) d
  have hPol := XPolar.polarRed86 m d k (KRK 1 (m + 1) e80) (by omega)
    (card_JR_pos (m + 1) d (by omega) (by have := hN.h100; omega)) hRF
    (XIdent.ident86 m d k (KRK 1 (m + 1) e80) (by omega) hRF)
  have hRem := remezS_modRK m d k hk hd a b β ξ ϑ hN t v hv E hE ht0 htn
  have hTail := tail86 (m + 1) d hd hN.hdn hN.h100
  refine (fail86_core m d k _ _ 100 t v ht0 hv E hE hPol hRem hTail f0 T hT).trans ?_
  rw [← ENNReal.ofReal_add hb0 (by positivity)]
  exact ENNReal.ofReal_le_ofReal hb

end BstLean.Part89

#print axioms BstLean.Part89.failS_of
