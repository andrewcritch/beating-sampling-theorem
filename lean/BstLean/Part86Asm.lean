import BstLean.Part86Core
import BstLean.Part86Line
import BstLean.Part86Arith
import BstLean.Part86RotA
import BstLean.Part86RotB
import BstLean.Part86SliceOp
import BstLean.Part86SliceRH
import BstLean.Part86Poly
import BstLean.Part86Decor
import BstLean.Part86Scale
import BstLean.Part86Gauss
import BstLean.Part86Remez
import BstLean.Part86Ident
import BstLean.Part86Polar
import BstLean.Part86Tail
import BstLean.Part86Inst
import BstLean.Part84Bonami

/-!
# Part 86, assembly: the failure bound on the coefficient sphere for every `n ≥ N86 d k`
-/

namespace BstLean.Part86

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part41 (Mono Tens TSymm)
open BstLean.Part56 (UnitV KRK)
open BstLean.Part80 (e80)

theorem rotFacts86 (n d : ℕ) : RotFacts n d := fun v hv E hE =>
  ⟨XRotB.rot_mp v hv E hE, rot_sumsq v hv E hE, rot_mapMD v hv E hE, rot_KR v hv E hE,
    rot_resid v E hE, XRotB.rot_twoPt v hv E hE⟩

theorem N86_ge (d k : ℕ) (hd : 1 ≤ d) : 70000 ≤ N86 d k := by
  unfold N86
  have h1 : 1 ≤ (2 * k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 := CLn_pos d hd
  have h3 : 1 ≤ 9 ^ (d * k) := Nat.one_le_pow _ _ (by omega)
  calc 70000 = 70000 * 1 * 1 * 1 := by norm_num
    _ ≤ 70000 * (2 * k + 1) ^ 2 * CLn d * 9 ^ (d * k) := by gcongr

/-- The sphere step for the model of `D_{t,v}`. -/
theorem remez_modRK (m d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (hN : N86 d k ≤ m + 1)
    (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v) (E : JR (m + 1) d → Mono (m + 1) d → ℝ)
    (hE : RotE v E) (ht0 : 0 ≤ t) (htn : t ≤ ((m + 1 : ℕ) : ℝ)) :
    RemezStep86 (modRK m d t v E) k (gqRK m d (KRK 1 (m + 1) e80) t v E)
      (remezBound (m + 1) k (((m + 1 : ℕ) : ℝ) * (CL86 d / (m : ℝ)) + 2)
        (6 * ((m + 1 : ℕ) : ℝ) * (CL86 d / (m : ℝ)) * (8 * 9 ^ (d * k)))) := by
  have h7 := N86_ge d k (by omega)
  have e : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
  obtain ⟨h100, h4k, hdn, hL0, hLC, hK, hL10, -⟩ := arith86 d k (m + 1) hk hkd hN
  rw [e] at hL0 hLC hK hL10
  have hR := XInst.regRK m d t v hv E
  have hPF := polyFacts (modRK m d t v E) hR
  have hRF := rotFacts86 (m + 1) d
  have hT := XRotB.rot_twoPt v hv E hE
  have hS := XInst.sliceOp_modRK m d t v hv E hE hRF (CL86 d) (XSliceOp.sliceOpRK m d (by omega) (by omega))
  have hD := decor86 (modRK m d t v E) d _ hR hT hS hL0
  have hSc := scale86 (modRK m d t v E) k (by omega) hT h100 h4k
  have hRH := XInst.sliceRH_modRK m d t v hv E (d * k) (sliceRHRK m (d * k) (by omega))
  have hG := XGauss.gaussModel86 (modRK m d t v E) d k (CL86 d / (m : ℝ)) (8 * 9 ^ (d * k))
    ((9 : ℝ) ^ k) (by omega) hR hPF hD hSc hRH (BstLean.Part84.fourth84_nine k) hL0 hLC
    (by simpa [mul_comm] using hK) (by positivity) (by positivity)
  have hSu := XInst.surrHyp_modRK m d (by omega) t v hv E ht0 htn
  have hn0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  exact XRemez.remez86 (modRK m d t v E) d k _ _ _ (1 / 40) _ (by omega) (by omega) hR hPF hG hSu
    (by norm_num) le_rfl hL10 (by positivity)
    (by have := mul_nonneg hn0 hL0; positivity)
    (card_W_ge (m + 1) d (by omega) hdn h100)

/-- **The failure bound on the coefficient sphere**, for every `2 ≤ k ≤ d` and `n ≥ N86 d k`. -/
theorem failHyp86 (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) : FailHyp d k := by
  intro n hn v hv t ht0 htn f0 T hT
  have h7 := N86_ge d k (by omega)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨E, hE⟩ := rotExists (m + 1) d v hv
  have e : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
  obtain ⟨h100, -, hdn, -, -, -, -, hb⟩ := arith86 d k (m + 1) hk hkd hn
  rw [e] at hb
  have hRF := rotFacts86 (m + 1) d
  have hPol := XPolar.polarRed86 m d k (KRK 1 (m + 1) e80) (by omega)
    (card_JR_pos (m + 1) d (by omega) (by omega)) hRF
    (XIdent.ident86 m d k (KRK 1 (m + 1) e80) (by omega) hRF)
  have hRem := remez_modRK m d k hk hkd hn t v hv E hE ht0 htn
  have hTail := tail86 (m + 1) d (by omega) hdn h100
  refine (fail86_core m d k _ _ 100 t v ht0 hv E hE hPol hRem hTail f0 T hT).trans ?_
  have hn0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [← ENNReal.ofReal_add ?_ (by positivity)]
  · exact ENNReal.ofReal_le_ofReal hb
  · have hL0 : (0 : ℝ) ≤ CL86 d / (m : ℝ) := by unfold CL86; positivity
    unfold remezBound
    positivity

end BstLean.Part86

#print axioms BstLean.Part86.failHyp86
