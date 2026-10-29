import BstLean.Part90Core
import BstLean.Part90Pt
import BstLean.Part90Inst
import BstLean.Part90InstK
import BstLean.Part90Kernel
import BstLean.Part90Wick
import BstLean.Part90Var
import BstLean.Part90Slice
import BstLean.Part90VarM
import BstLean.Part89QMain

/-!
# Part 90: the failure bound on the coefficient sphere at `(3, 3)` from the numeric conditions

`fail3_of`: from `Num3`, the interface `GradL4`, the slice oscillation bound at the level `R_p²`
(`OscR`), and the numeric inequality `g3 + (400/n + 2/Mk) + 100/n + 20808/D_W ≤ 1/100`.

No `sorry`, no `native_decide`, no `axiom`.
-/

namespace BstLean.Part90

open scoped ENNReal
open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD)
open BstLean.Part41 (Mono Tens TSymm)
open BstLean.Part53 (radF53)
open BstLean.Part56 (UnitV KRK axialR)
open BstLean.Part78 (nsq frobH)
open BstLean.Part80 (e80)
open BstLean.Part82 (T3 SymT frobT)
open BstLean.Part86 BstLean.Part86.XGauss
open BstLean.Part89

/-- **The slice oscillation bound at the level `R_p²`** for the instance `modRK m 3 t v E`, for
anchors with the two norm bounds and the two bounds of `‖T[A_j]‖_F`. -/
def OscR (m : ℕ) (Mk e1 e2 e4 e3 : ℝ) : Prop :=
  ∀ (t : ℝ) (v : Fin (m + 1) → ℝ), UnitV v → ∀ E : JR (m + 1) 3 → Mono (m + 1) 3 → ℝ, RotE v E →
  ∀ (ℓ : Fin (m + 1) → ℝ) (H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ), H.IsSymm →
  ∀ T : T3 (m + 1), SymT T → ∀ (A : Fin (3 + 1) → Fin (m + 1) → ℝ) (c : ℝ),
    nsq (A 2) ≤ 9 / 8 * ((m : ℝ) + 1) * c ^ 2 → nsq (A 3) ≤ 9 / 8 * ((m : ℝ) + 1) * c ^ 2 →
    frobH (TA T (A 2)) ≤ 103 / 100 * Mk * c ^ 2 * frobT T →
    frobH (TA T (A 3)) ≤ 103 / 100 * Mk * c ^ 2 * frobT T →
    SliceOscM (modRK m 3 t v E) ℓ H T A c (fun p => axialR p.1 (radF53 p.2) ^ 2)
      (fun p => axialR p.1 (radF53 p.2)) e1 e2 e4 (e3 ^ 2 * (c ^ 2) ^ 3 * frobT T)

lemma osc_mono {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S]
    [MeasurableSpace G] (M : Mod n I J S G) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (T : T3 n) (A : I → Fin n → ℝ) (c : ℝ) (tau rho : S → ℝ) (e1 e2 e4 e0 e0' : ℝ)
    (h : SliceOscM M ℓ H T A c tau rho e1 e2 e4 e0) (he : e0 ≤ e0') :
    SliceOscM M ℓ H T A c tau rho e1 e2 e4 e0' := by
  unfold SliceOscM at h ⊢
  filter_upwards [h] with p hp
  obtain ⟨Abar, Hbar, z, hz, h0, hA, hH⟩ := hp
  exact ⟨Abar, Hbar, z, hz, h0.trans he, hA, hH⟩

lemma g3_nonneg (m : ℕ) (L X ϑ a b β ξ : ℝ) (hN : Num3 m L ϑ a b β ξ) :
    0 ≤ g3 m L X ϑ a b β ξ := by
  obtain ⟨h5000, hL0, hL10, hϑ, ha, hb0, hb1, hab, hβ, hβ4, hξ, hξ2, hξβ, hν⟩ := hN
  have hξsq : ξ ^ 2 ≤ 1 := by nlinarith
  have hK := KSq_nonneg (m + 1) 3 (DWr (m + 1) (JR (m + 1) 3)) L b β ξ hξsq hν
  have hW := cVW_nonneg 3 (tS (m + 1) β) L (X ^ 2) ϑ (sq_nonneg X) hϑ
  have hn0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold g3
  rw [semiBound_aff]
  have h1 : 0 ≤ ((m + 1 : ℕ) : ℝ) * L + 2 := by
    have := mul_nonneg hn0 hL0; linarith
  have h2 : 0 ≤ ((m + 1 : ℕ) : ℝ) * cVW 3 (tS (m + 1) β) L (X ^ 2) ϑ := mul_nonneg hn0 hW
  have h3 : 0 ≤ 5 / 2 * (((3 : ℕ) : ℝ) + 1) ^ 2 *
      (((m + 1 : ℕ) : ℝ) * L + 2) / (a * ((m + 1 : ℕ) : ℝ)) := by positivity
  exact add_nonneg h3 (mul_nonneg hK h2)

/-- **The failure bound on the coefficient sphere at `(3, 3)`** from the numeric conditions. -/
theorem fail3_of (m : ℕ) (ϑ a b β ξ cH cT e1 e2 e4 e3r e3 η ω ζ Mk : ℝ)
    (hN : Num3 m (2 / 3 * (CLs 3 / (m : ℝ))) ϑ a b β ξ) (hm4 : 10000 ≤ m)
    (hcH : 0 ≤ cH) (hcT : 0 ≤ cT)
    (hcH4 : 48 * (3 : ℝ) ^ 2 ≤ cH ^ 4) (hcT4 : 5670 * (3 : ℝ) ^ 4 ≤ cT ^ 4)
    (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he4 : 0 ≤ e4) (he3 : 0 ≤ e3)
    (hη : 0 < η) (hω : 0 < ω) (hζ : 0 < ζ) (hMk : 0 < Mk)
    (hGrad : GradL4) (hOscR : OscR m Mk e1 e2 e4 e3r) (he33 : 2 * e3r ^ 2 ≤ e3 ^ 2)
    (hb : g3 m (2 / 3 * (CLs 3 / (m : ℝ)))
          (Xc (2 / 3 * (CLs 3 / (m : ℝ))) 27 ((87 / 100) ^ 3) cH cT e1 e2 e4 e3 η ω ζ) ϑ a b β ξ +
        (400 / ((m + 1 : ℕ) : ℝ) + 2 / Mk) + 100 / ((m + 1 : ℕ) : ℝ) +
        20808 / DWr (m + 1) (JR (m + 1) 3) ≤ 1 / 100)
    (v : Fin (m + 1) → ℝ) (hv : UnitV v) (t : ℝ) (ht0 : 0 ≤ t) (htn : t ≤ ((m + 1 : ℕ) : ℝ))
    (f0 : ℝ) (T : Tens (m + 1)) (hT : TSymm 3 T) :
    stdGauss (CoefIdxD (m + 1) 3) (SphereFail86 (m + 1) 3 3 (KRK 1 (m + 1) e80) t v f0 T) ≤
      ENNReal.ofReal (1 / 100) := by
  have h5000 : 5000 ≤ m := hN.h5000
  have hL0 := hN.hL0
  have hL10 := hN.hL10
  obtain ⟨E, hE⟩ := rotExists (m + 1) 3 v hv
  have hRF := rotFacts86 (m + 1) 3
  have hPol := XPolar.polarRed86 m 3 3 (KRK 1 (m + 1) e80) (by omega)
    (card_JR_pos (m + 1) 3 (by omega) (by omega)) hRF
    (XIdent.ident86 m 3 3 (KRK 1 (m + 1) e80) (by omega) hRF)
  have hTail := tail86 (m + 1) 3 (by norm_num) (by omega) (by omega)
  obtain ⟨ℓ, H, T', hHs, hT's, hrep⟩ := instCubRep m t v E f0 T hT
  have hDW : 0 < DWr (m + 1) (JR (m + 1) 3) :=
    DWr_pos (m + 1) 3 (by norm_num) (by omega) (by omega)
  set L : ℝ := 2 / 3 * (CLs 3 / (m : ℝ)) with hLdef
  set X : ℝ := Xc L 27 ((87 / 100) ^ 3) cH cT e1 e2 e4 e3 η ω ζ with hXdef
  have hA0 := g3_nonneg m L X ϑ a b β ξ hN
  -- the instance facts
  have hR := XInst.regRK m 3 t v hv E
  have hPF := polyFacts (modRK m 3 t v E) hR
  have hSph := BstLean.Part89.instSph m 3 t v E (by omega) hv
  have hD := instK_decor m h5000 t v hv E hE (kernelLow3 (m + 1))
  have hOp := instK_opF m h5000 t v hv E hE (kernelLow3 (m + 1))
  have hK := instK_up m h5000 t v hv E hE (kernelUp3' (m + 1))
  have h4 := instK_feat4 m h5000 t v hv E hE (instFeat4 m h5000 t v hv E hE)
  have htau2 : Measurable (tauK (m := m)) ∧ (∀ p : ℝ × (Fin m → ℝ), 0 ≤ tauK p) ∧
      ∀ᵐ p ∂(modRK m 3 t v E).pi, ∀ᵐ g ∂(modRK m 3 t v E).ga,
        tauK p ≤ kapm (modRK m 3 t v E) ((modRK m 3 t v E).X (p, g))
          ((modRK m 3 t v E).X (p, g)) :=
    ⟨measurable_tauK, tauK_nonneg, Filter.Eventually.of_forall fun p => (hOp.2 p).2.1⟩
  have hc3' : ((87 / 100 : ℝ)) ^ 3 ≤ ∫ p, tauK p ^ 3 ∂(modRK m 3 t v E).pi :=
    instK_tau3 m h5000 t v hv E hE hm4 ht0 htn
  have hVarM : CubVarM (modRK m 3 t v E) L 27 3 tauK rhoK ((87 / 100) ^ 3) :=
    cubVarM (modRK m 3 t v E) 3 L 27 3 tauK rhoK tauK ((87 / 100) ^ 3) hR hPF hSph hD hOp
      instK_rho hK h4 htau2 (by positivity) hc3' hL0 (by linarith) (by norm_num) (by norm_num)
      (cubSliceA regC varBoundC hGrad) varWC
  have hOsc : ∀ (A : Fin (3 + 1) → Fin (m + 1) → ℝ) (c : ℝ),
      nsq (A 2) ≤ 9 / 8 * ((m : ℝ) + 1) * c ^ 2 → nsq (A 3) ≤ 9 / 8 * ((m : ℝ) + 1) * c ^ 2 →
      frobH (TA T' (A 2)) ≤ 103 / 100 * Mk * c ^ 2 * frobT T' →
      frobH (TA T' (A 3)) ≤ 103 / 100 * Mk * c ^ 2 * frobT T' →
      SliceOscM (modRK m 3 t v E) ℓ H T' A c tauK rhoK e1 e2 e4
        (e3 ^ 2 * (c ^ 2) ^ 3 * frobT T') := by
    intro A c h2 h3 h5 h6
    have h := instK_osc m h5000 t v hv E hE ℓ H T' A c e1 e2 e4 _ he1 he2 he4
      (hOscR t v hv E hE ℓ H hHs T' hT's A c h2 h3 h5 h6)
    refine osc_mono _ _ _ _ _ _ _ _ _ _ _ _ _ h ?_
    have hF : 0 ≤ (c ^ 2) ^ 3 * frobT T' :=
      mul_nonneg (by positivity) (VarM.frobT_nonneg T')
    nlinarith [mul_le_mul_of_nonneg_right he33 hF]
  -- the good set of the anchors
  set n : ℝ := ((m + 1 : ℕ) : ℝ) with hndef
  have hn0 : (0 : ℝ) < n := by rw [hndef]; positivity
  set GU : Set (Fin (3 + 1) × Fin (m + 1) → ℝ) :=
    {U | (∑ i, U (2, i) ^ 2 ≤ 11 / 10 * n ∧ ∑ i, U (3, i) ^ 2 ≤ 11 / 10 * n) ∧
      (frobH (TA T' (fun i => U (2, i))) ≤ Mk * frobT T' ∧
        frobH (TA T' (fun i => U (3, i))) ≤ Mk * frobT T')} with hGUdef
  have hmN : ∀ j : Fin (3 + 1), Measurable fun U : Fin (3 + 1) × Fin (m + 1) → ℝ =>
      ∑ i, U (j, i) ^ 2 := fun j =>
    Finset.measurable_sum _ fun i _ => (measurable_pi_apply (j, i)).pow_const 2
  have hmT : ∀ j : Fin (3 + 1), Measurable fun U : Fin (3 + 1) × Fin (m + 1) → ℝ =>
      frobH (TA T' (fun i => U (j, i))) := by
    intro j
    unfold BstLean.Part78.frobH TA
    simp only [Matrix.of_apply]
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun l _ => ?_
    exact (Finset.measurable_sum _ fun k _ =>
      measurable_const.mul (measurable_pi_apply (j, k))).pow_const 2
  have hGU : MeasurableSet GU :=
    ((measurableSet_le (hmN 2) measurable_const).inter
      (measurableSet_le (hmN 3) measurable_const)).inter
    ((measurableSet_le (hmT 2) measurable_const).inter
      (measurableSet_le (hmT 3) measurable_const))
  have hsub : GUᶜ ⊆
      ({U | 11 / 10 * n < ∑ i, U (2, i) ^ 2} ∪ {U | 11 / 10 * n < ∑ i, U (3, i) ^ 2}) ∪
      ({U | Mk * frobT T' < frobH (TA T' (fun i => U (2, i)))} ∪
        {U | Mk * frobT T' < frobH (TA T' (fun i => U (3, i)))}) := by
    intro U hU
    simp only [hGUdef, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_le] at hU
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    tauto
  have hGUp : stdGauss (Fin (3 + 1) × Fin (m + 1)) GUᶜ ≤
      ENNReal.ofReal (400 / n + 2 / Mk) := by
    refine (measure_mono hsub).trans ?_
    refine (measure_union_le _ _).trans ?_
    have hN2 := anchorNorm (m + 1) (by omega) 2
    have hN3 := anchorNorm (m + 1) (by omega) 3
    have hT2 := anchorTA (m + 1) T' 2 Mk hMk
    have hT3 := anchorTA (m + 1) T' 3 Mk hMk
    have hA := (measure_union_le _ _).trans (add_le_add hN2 hN3)
    have hB := (measure_union_le _ _).trans (add_le_add hT2 hT3)
    refine (add_le_add hA hB).trans ?_
    have p1 : (0 : ℝ) ≤ 200 / n := by positivity
    have p2 : (0 : ℝ) ≤ 1 / Mk := by positivity
    rw [← ENNReal.ofReal_add p1 p1, ← ENNReal.ofReal_add p2 p2,
      ← ENNReal.ofReal_add (add_nonneg p1 p1) (add_nonneg p2 p2)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    ring
  have hpU : (0 : ℝ) ≤ 400 / n + 2 / Mk := by positivity
  have hcore := core3 m (KRK 1 (m + 1) e80) 100 (g3 m L X ϑ a b β ξ) (400 / n + 2 / Mk) t v ht0
    hv E hE hPol hTail f0 T hT GU hGU hGUp hA0 hpU hDW
    (by
      intro U W' hU h1 h2
      obtain ⟨⟨hU2, hU3⟩, hTU2, hTU3⟩ := hU
      exact pt3 m L 27 3 ((87 / 100) ^ 3) ϑ a b β ξ hN tauK rhoK v hv t ht0 htn E hE f0 T ℓ H
        hHs T' hT's hrep cH cT e1 e2 e4 e3 η ω ζ Mk hcH hcT hcH4 hcT4 he1 he2 he4 he3 hη hω hζ
        hMk.le hD hVarM hOsc U W' h1 h2 hU2 hU3 hTU2 hTU3)
  refine hcore.trans ?_
  have q1 : (0 : ℝ) ≤ 100 / n := by positivity
  have q2 : (0 : ℝ) ≤ 20808 / DWr (m + 1) (JR (m + 1) 3) := by positivity
  rw [← ENNReal.ofReal_add hA0 hpU, ← ENNReal.ofReal_add (add_nonneg hA0 hpU) q1,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg hA0 hpU) q1) q2]
  exact ENNReal.ofReal_le_ofReal hb

end BstLean.Part90

#print axioms BstLean.Part90.fail3_of
