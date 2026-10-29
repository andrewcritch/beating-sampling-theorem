import BstLean.Part86Main
import BstLean.Part86ArithS

/-!
# Part 86, second pass: the same theorems with the sharper slice operator constant
`1.01 (d+1)!` (`sliceOpRK_fact`), threshold `N86s d k = 71000 (2k+1)² (d+1)! 9^{dk}`.
-/

namespace BstLean.Part86
open scoped ENNReal
open BstLean.Part41 (Mono)


open MeasureTheory BstLean.Cost
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (frob Tens TSymm baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part56
open BstLean.Part74 (MomSpecUsed74 eval74)
open BstLean.Part80 (e80)

/-- The failure bound on the coefficient sphere, for every `n ≥ N86s d k`. -/
def FailHypS (d k : ℕ) : Prop :=
  ∀ n : ℕ, N86s d k ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ n →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      stdGauss (CoefIdxD n d) (SphereFail86 n d k (KRK 1 n e80) t v f0 T) ≤
        ENNReal.ofReal (1 / 100)

/-- The cost comparison, for every `n ≥ N86s d k` with `40 B ≤ n`. -/
def CostHypS (d k B : ℕ) : Prop :=
  ∀ n : ℕ, N86s d k ≤ n → 40 * B ≤ n → ∀ pmc pgc : ℕ,
    (pmc : ℝ) ≤ (B : ℝ) * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1) →
    (pgc : ℝ) ≤ costLine56 n d k → (pmc : ℝ) + pgc < baseline n d (1 / 2)

/-- **Theorem 1 at `(d, k)` from the failure bound**, `C = 1`, `ε = 1/2`, failure `≤ 1/100`, strict
cost: for every `n ≥ N86s d k` with `40 B ≤ n`, `B` the constant of the moment program. -/
theorem part86_lineS_of (d k : ℕ) (B : ℕ)
    (hprog : ∀ n K : ℕ, 2 ≤ n → ∃ pm : Prog (InM56 n) (KeyRK k d), heavyCount pm = 0 ∧
      MomSpecUsed74 pm K ∧ pm.cost ≤ B * (n + K + 1))
    (hF : FailHypS d k) (hC : CostHypS d k B) :
    ∀ n : ℕ, N86s d k ≤ n → 40 * B ≤ n → 2 ≤ n →
    ∃ (pm : Prog (InM56 n) (KeyRK k d)) (pg : Prog (In56 n d k) Unit),
      heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpecUsed74 pm (KRK 1 n e80) ∧ GSpec56 pg ∧
      (pm.cost : ℝ) ≤ B * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1) ∧
      ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
      ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
      ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ (lawRK n t v) k f0 T (unitOfD Z) <
            (BofQ (lawRK n t v) k f0 T (unitOfD Z) -
              pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) ∧
        (pm.cost : ℝ) + pg.cost < baseline n d ε := by
  intro n hn hB hn2
  obtain ⟨pg, hpg0, hpgs, hpgc⟩ := lineProg56_exists n d k (by omega)
  obtain ⟨pm, hpm0, hpms, hpmc⟩ := hprog n (KRK 1 n e80) hn2
  have hpmc' : (pm.cost : ℝ) ≤ B * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1) := by exact_mod_cast hpmc
  refine ⟨pm, pg, hpm0, hpg0, hpms, hpgs, hpmc', fun v hv t ht0 ht ε hε1 hε2 f0 T hT _ => ?_⟩
  have hε : ε = 1 / 2 := le_antisymm hε2 hε1
  subst hε
  refine ⟨?_, hC n hn hB pm.cost pg.cost hpmc' hpgc⟩
  have heval : ∀ M : CoefIdxD n d → ℝ,
      pg.eval (inp56 f0 T M v (pm.eval (inRK t v))) () =
        gLineW (surrRK n (KRK 1 n e80) t v) k f0 T v M :=
    fun M => eval74 pm pg _ hpms hpgs t v ht0 hv f0 T hT M
  simp only [heval]
  exact hF n hn v hv t ht0 (by simpa using ht) f0 T hT

/-- The sphere step for the model of `D_{t,v}`. -/
theorem remez_modRKs (m d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (hN : N86s d k ≤ m + 1)
    (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v) (E : JR (m + 1) d → Mono (m + 1) d → ℝ)
    (hE : RotE v E) (ht0 : 0 ≤ t) (htn : t ≤ ((m + 1 : ℕ) : ℝ)) :
    RemezStep86 (modRK m d t v E) k (gqRK m d (KRK 1 (m + 1) e80) t v E)
      (remezBound (m + 1) k (((m + 1 : ℕ) : ℝ) * (CLs d / (m : ℝ)) + 2)
        (6 * ((m + 1 : ℕ) : ℝ) * (CLs d / (m : ℝ)) * (8 * 9 ^ (d * k)))) := by
  have h7 := N86s_ge d k
  have e : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
  obtain ⟨h100, h4k, hdn, hL0, hLC, hK, hL10, -⟩ := arith86s d k (m + 1) hk hkd hN
  rw [e] at hL0 hLC hK hL10
  have hR := XInst.regRK m d t v hv E
  have hPF := polyFacts (modRK m d t v E) hR
  have hRF := rotFacts86 (m + 1) d
  have hT := XRotB.rot_twoPt v hv E hE
  have hS := XInst.sliceOp_modRK m d t v hv E hE hRF (CLs d) (XSliceOp.sliceOpRK_fact m d (by omega) (by omega))
  have hD := decor86 (modRK m d t v E) d _ hR hT hS hL0
  have hSc := scale86 (modRK m d t v E) k (by omega) hT h100 h4k
  have hRH := XInst.sliceRH_modRK m d t v hv E (d * k) (sliceRHRK m (d * k) (by omega))
  have hG := XGauss.gaussModel86 (modRK m d t v E) d k (CLs d / (m : ℝ)) (8 * 9 ^ (d * k))
    ((9 : ℝ) ^ k) (by omega) hR hPF hD hSc hRH (BstLean.Part84.fourth84_nine k) hL0 hLC
    (by simpa [mul_comm] using hK) (by positivity) (by positivity)
  have hSu := XInst.surrHyp_modRK m d (by omega) t v hv E ht0 htn
  have hn0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  exact XRemez.remez86 (modRK m d t v E) d k _ _ _ (1 / 40) _ (by omega) (by omega) hR hPF hG hSu
    (by norm_num) le_rfl hL10 (by positivity)
    (by have := mul_nonneg hn0 hL0; positivity)
    (card_W_ge (m + 1) d (by omega) hdn h100)

/-- **The failure bound on the coefficient sphere**, for every `2 ≤ k ≤ d` and `n ≥ N86s d k`. -/
theorem failHyp86s (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) : FailHypS d k := by
  intro n hn v hv t ht0 htn f0 T hT
  have h7 := N86s_ge d k
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨E, hE⟩ := rotExists (m + 1) d v hv
  have e : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
  obtain ⟨h100, -, hdn, -, -, -, -, hb⟩ := arith86s d k (m + 1) hk hkd hn
  rw [e] at hb
  have hRF := rotFacts86 (m + 1) d
  have hPol := XPolar.polarRed86 m d k (KRK 1 (m + 1) e80) (by omega)
    (card_JR_pos (m + 1) d (by omega) (by omega)) hRF
    (XIdent.ident86 m d k (KRK 1 (m + 1) e80) (by omega) hRF)
  have hRem := remez_modRKs m d k hk hkd hn t v hv E hE ht0 htn
  have hTail := tail86 (m + 1) d (by omega) hdn h100
  refine (fail86_core m d k _ _ 100 t v ht0 hv E hE hPol hRem hTail f0 T hT).trans ?_
  have hn0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [← ENNReal.ofReal_add ?_ (by positivity)]
  · exact ENNReal.ofReal_le_ofReal hb
  · have hL0 : (0 : ℝ) ≤ CLs d / (m : ℝ) := by unfold CLs; positivity
    unfold remezBound
    positivity




/-- **Theorem 1 at every degree pair `2 ≤ k = d_f ≤ d = d_M`**, `C = 1`, `ε = 1/2`, failure
`≤ 1/100`, strict cost, for every `n ≥ N86s d k` with `n ≥ 40 B`. -/
theorem part86_lineS_gen (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) :
    ∃ B : ℕ, ∀ n : ℕ, N86s d k ≤ n → 40 * B ≤ n →
    ∃ (pm : Prog (InM56 n) (KeyRK k d)) (pg : Prog (In56 n d k) Unit),
      heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpecUsed74 pm (KRK 1 n e80) ∧ GSpec56 pg ∧
      (pm.cost : ℝ) ≤ B * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1) ∧
      ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
      ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
      ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ (lawRK n t v) k f0 T (unitOfD Z) <
            (BofQ (lawRK n t v) k f0 T (unitOfD Z) -
              pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) ∧
        (pm.cost : ℝ) + pg.cost < baseline n d ε := by
  obtain ⟨B, hB⟩ := BstLean.Part74.momProgGen74 k d
  refine ⟨B, fun n hn hnB => ?_⟩
  have h7 := N86s_ge d k
  exact part86_lineS_of d k B hB (failHyp86s d k hk hkd)
    (fun n hn hB pmc pgc hpm hpg => cost86s d k n B hk hkd hn hB pmc pgc hpm hpg) n hn hnB
    (by omega)

/-- **Theorem 1 at `(d_M, d_f) = (3, 3)`**, `C = 1`, `ε = 1/2`, failure `≤ 1/100`, strict cost, for
every `n ≥ N86s 3 3 = 70000 · 49 · 306 · 9⁹`. -/
theorem part86_lineS_33 : ∀ n : ℕ, N86s 3 3 ≤ n →
    ∃ (pm : Prog (InM56 n) (KeyRK 3 3)) (pg : Prog (In56 n 3 3) Unit),
      heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpecUsed74 pm (KRK 1 n e80) ∧ GSpec56 pg ∧
      (pm.cost : ℝ) ≤ (1200035 : ℕ) * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1) ∧
      ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
      ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
      ∀ (f0 : ℝ) (T : Tens n), TSymm 3 T → 0 < frob (T 3) →
        stdGauss (CoefIdxD n 3) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ (lawRK n t v) 3 f0 T (unitOfD Z) <
            (BofQ (lawRK n t v) 3 f0 T (unitOfD Z) -
              pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) ∧
        (pm.cost : ℝ) + pg.cost < baseline n 3 ε := by
  intro n hn
  have h7 := N86s_ge 3 3
  exact part86_lineS_of 3 3 1200035 BstLean.Part74.progHyp33
    (failHyp86s 3 3 (by norm_num) le_rfl)
    (fun n hn hB pmc pgc hpm hpg =>
      cost86s 3 3 n 1200035 (by norm_num) le_rfl hn hB pmc pgc hpm hpg) n hn
    (le_trans N86s_33_ge hn) (by omega)

/-- **Theorem 1 at `(3, 3)` for every `n ≥ 5 · 10¹⁷`.** -/
theorem part86_lineS_33_num : ∀ n : ℕ, 33 * 10 ^ 15 ≤ n →
    ∃ (pm : Prog (InM56 n) (KeyRK 3 3)) (pg : Prog (In56 n 3 3) Unit),
      heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpecUsed74 pm (KRK 1 n e80) ∧ GSpec56 pg ∧
      (pm.cost : ℝ) ≤ (1200035 : ℕ) * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1) ∧
      ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
      ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
      ∀ (f0 : ℝ) (T : Tens n), TSymm 3 T → 0 < frob (T 3) →
        stdGauss (CoefIdxD n 3) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ (lawRK n t v) 3 f0 T (unitOfD Z) <
            (BofQ (lawRK n t v) 3 f0 T (unitOfD Z) -
              pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) ∧
        (pm.cost : ℝ) + pg.cost < baseline n 3 ε :=
  fun n hn => part86_lineS_33 n (le_trans N86s_33_le hn)

end BstLean.Part86

#print axioms BstLean.Part86.part86_lineS_gen
#print axioms BstLean.Part86.part86_lineS_33
#print axioms BstLean.Part86.part86_lineS_33_num
