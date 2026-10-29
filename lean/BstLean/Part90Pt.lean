import BstLean.Part90Defs

/-!
# Part 90: the pointwise sphere step at `(3, 3)`

For anchors `U` in the good set (two norm bounds and two Markov bounds for the anchors `2`, `3`)
and a good radius, the failure probability over the direction of `W` is at most `g3`. The variance
bound of the within-slice variance (`CubVarM`) and the slice oscillation bound (`instOsc`) enter as
hypotheses; `gmw_of` and `remezSemiP` of Part 89 do the rest.

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

/-- The constant of the variance bound: `X = kY + kE ε₃²/(6 c₃ (1 − L))`. -/
noncomputable def Xc (L g4 c3 cH cT e1 e2 e4 e3 η ω ζ : ℝ) : ℝ :=
  kYc L g4 η ω ζ cH cT e1 e2 e4 + kEc L g4 η ω ζ * (e3 ^ 2 / (6 * c3 * (1 - L)))

/-- The bound of the sphere step at `(3, 3)` with the variance constant `X²`. -/
noncomputable def g3 (m : ℕ) (L X ϑ a b β ξ : ℝ) : ℝ :=
  semiBound89 (m + 1) 3 (DWr (m + 1) (JR (m + 1) 3))
    (((m + 1 : ℕ) : ℝ) * L + 2)
    (((m + 1 : ℕ) : ℝ) * cVW 3 (tS (m + 1) β) L (X ^ 2) ϑ)
    L a b β ξ

/-- The numeric conditions of the sphere step. -/
structure Num3 (m : ℕ) (L ϑ a b β ξ : ℝ) : Prop where
  h5000 : 5000 ≤ m
  hL0 : 0 ≤ L
  hL10 : L ≤ 1 / 10
  hϑ : 0 < ϑ
  ha : 0 < a
  hb0 : 0 ≤ b
  hb1 : b < 1
  hab : 9 / 4 * a + 1 / 400 ≤ b * (1 - L) / 4
  hβ : 0 < β
  hβ4 : β ≤ 1 / 100
  hξ : 0 < ξ
  hξ2 : ξ ≤ 1 / 2
  hξβ : ξ * β ≤ 1 / 100
  hν : 2 / (DWr (m + 1) (JR (m + 1) 3) * (99 / 100 * ξ * β) ^ 2) < 1

lemma TA_div {n : ℕ} (T : T3 n) (a : Fin n → ℝ) (r : ℝ) :
    frobH (TA T (fun i => a i / r)) = frobH (TA T a) / r ^ 2 := by
  unfold frobH TA
  simp only [Matrix.of_apply]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : ∑ k, T i l k * (a k / r) = (∑ k, T i l k * a k) / r := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this, div_pow]

lemma nsq_div {n : ℕ} (a : Fin n → ℝ) (r : ℝ) :
    nsq (fun i => a i / r) = nsq a / r ^ 2 := by
  unfold nsq
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by rw [div_pow]

set_option maxHeartbeats 1600000 in
/-- The pointwise sphere step at `(3, 3)`. -/
theorem pt3 (m : ℕ) (L g4 K c3 ϑ a b β ξ : ℝ) (hN : Num3 m L ϑ a b β ξ)
    (tau rho : ℝ × (Fin m → ℝ) → ℝ)
    (v : Fin (m + 1) → ℝ) (hv : UnitV v) (t : ℝ) (ht0 : 0 ≤ t) (htn : t ≤ ((m + 1 : ℕ) : ℝ))
    (E : JR (m + 1) 3 → Mono (m + 1) 3 → ℝ) (hE : RotE v E)
    (f0 : ℝ) (T : Tens (m + 1)) (ℓ : Fin (m + 1) → ℝ)
    (H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hHs : H.IsSymm) (T' : T3 (m + 1))
    (hT's : SymT T')
    (hrep : ∀ (U : Fin (3 + 1) × Fin (m + 1) → ℝ) (r sc : ℝ),
      CubRep (modRK m 3 t v E) (PU 3 f0 T U r sc) f0 ℓ H T' (fun j i => U (j, i) / r) sc)
    (cH cT e1 e2 e4 e3 η ω ζ Mk : ℝ) (hcH : 0 ≤ cH) (hcT : 0 ≤ cT)
    (hcH4 : 48 * K ^ 2 ≤ cH ^ 4) (hcT4 : 5670 * K ^ 4 ≤ cT ^ 4)
    (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he4 : 0 ≤ e4) (he3 : 0 ≤ e3)
    (hη : 0 < η) (hω : 0 < ω) (hζ : 0 < ζ) (hMk : 0 ≤ Mk)
    (hD : Decor86 (modRK m 3 t v E) L)
    (hVarM : CubVarM (modRK m 3 t v E) L g4 K tau rho c3)
    (hOsc : ∀ (A : Fin (3 + 1) → Fin (m + 1) → ℝ) (c : ℝ),
      nsq (A 2) ≤ 9 / 8 * ((m : ℝ) + 1) * c ^ 2 → nsq (A 3) ≤ 9 / 8 * ((m : ℝ) + 1) * c ^ 2 →
      frobH (TA T' (A 2)) ≤ 103 / 100 * Mk * c ^ 2 * frobT T' →
      frobH (TA T' (A 3)) ≤ 103 / 100 * Mk * c ^ 2 * frobT T' →
      SliceOscM (modRK m 3 t v E) ℓ H T' A c tau rho e1 e2 e4 (e3 ^ 2 * (c ^ 2) ^ 3 * frobT T'))
    (U : Fin (3 + 1) × Fin (m + 1) → ℝ) (W' : JR (m + 1) 3 × Fin (m + 1) → ℝ)
    (hlam : |lam0 (DD (m + 1) 3) (DWr (m + 1) (JR (m + 1) 3)) U (radF53 W') ^ 2 - 1| ≤
      1 / (((m + 1 : ℕ) : ℝ)))
    (hρ : 100 / 101 * DWr (m + 1) (JR (m + 1) 3) ≤ radF53 W' ^ 2)
    (hU2 : ∑ i, U (2, i) ^ 2 ≤ 11 / 10 * ((m + 1 : ℕ) : ℝ))
    (hU3 : ∑ i, U (3, i) ^ 2 ≤ 11 / 10 * ((m + 1 : ℕ) : ℝ))
    (hTU2 : frobH (TA T' (fun i => U (2, i))) ≤ Mk * frobT T')
    (hTU3 : frobH (TA T' (fun i => U (3, i))) ≤ Mk * frobT T') :
    stdGauss (JR (m + 1) 3 × Fin (m + 1))
        (badSet86 (modRK m 3 t v E) (gqRK m 3 (KRK 1 (m + 1) e80) t v E)
          (PU 3 f0 T U (Real.sqrt (∑ a, U a ^ 2 + radF53 W' ^ 2))
            (1 / Real.sqrt (DD (m + 1) 3)))
          (lam0 (DD (m + 1) 3) (DWr (m + 1) (JR (m + 1) 3)) U (radF53 W'))) ≤
      ENNReal.ofReal (g3 m L (Xc L g4 c3 cH cT e1 e2 e4 e3 η ω ζ) ϑ a b β ξ) := by
  obtain ⟨h5000, hL0, hL10, hϑ, ha, hb0, hb1, hab, hβ, hβ4, hξ, hξ2, hξβ, hν⟩ := hN
  have h100 : 100 ≤ m + 1 := by omega
  have hdn : 3 ≤ m + 1 := by omega
  have hR := XInst.regRK m 3 t v hv E
  have hPF := polyFacts (modRK m 3 t v E) hR
  have hRF := rotFacts86 (m + 1) 3
  have hT2 := XRotB.rot_twoPt v hv E hE
  have hSc := scale86 (modRK m 3 t v E) 3 (by omega) hT2 h100 (by omega)
  have hSE := scaleE89 (modRK m 3 t v E) 3 (by omega) hT2 (by omega)
  have hSu := XInst.surrHyp_modRK m 3 (by omega) t v hv E ht0 htn
  have hn0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hDD : 0 < DD (m + 1) 3 := BstLean.Part89.DD_pos (m + 1) 3 (by omega)
  have hDW : 0 < DWr (m + 1) (JR (m + 1) 3) := DWr_pos (m + 1) 3 (by omega) hdn h100
  set P := PU 3 f0 T U (Real.sqrt (∑ a, U a ^ 2 + radF53 W' ^ 2))
    (1 / Real.sqrt (DD (m + 1) 3)) with hPdef
  set lam := lam0 (DD (m + 1) 3) (DWr (m + 1) (JR (m + 1) 3)) U (radF53 W') with hlamdef
  have hQ := hrep U (Real.sqrt (∑ a, U a ^ 2 + radF53 W' ^ 2)) (1 / Real.sqrt (DD (m + 1) 3))
  have hP : P.totalDegree ≤ 3 := PU_degree 3 f0 T U _ _
  -- radius algebra
  have hρ2 : 0 < radF53 W' ^ 2 := lt_of_lt_of_le (by positivity) hρ
  have hSU : 0 ≤ ∑ a, U a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  set R : ℝ := ∑ a, U a ^ 2 + radF53 W' ^ 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hr2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hRpos.le
  have hsD : 0 < Real.sqrt (DD (m + 1) 3) := Real.sqrt_pos.mpr hDD
  have hsW : 0 < Real.sqrt (DWr (m + 1) (JR (m + 1) 3)) := Real.sqrt_pos.mpr hDW
  have hlamsc : lam ^ 2 * (1 / Real.sqrt (DD (m + 1) 3)) ^ 2 =
      radF53 W' ^ 2 / (R * DWr (m + 1) (JR (m + 1) 3)) := by
    rw [hlamdef]
    unfold lam0
    rw [← hRdef, div_pow, mul_pow, mul_pow, hr2, Real.sq_sqrt hDW.le, div_pow, one_pow,
      Real.sq_sqrt hDD.le]
    field_simp
  have hX0 : 0 ≤ Xc L g4 c3 cH cT e1 e2 e4 e3 η ω ζ ^ 2 := sq_nonneg _
  have hmR : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hG := gmw_of (modRK m 3 t v E) 3 3 L
    (Xc L g4 c3 cH cT e1 e2 e4 e3 η ω ζ ^ 2) β ϑ (by omega) hR hPF hD hSc hSE hL0
    (by linarith) hX0 hβ (by linarith) hϑ P hP lam hlam
    (by
      intro u hu1 hu2
      have hu0 : 0 ≤ u := by linarith
      have hu99 : 99 / 100 ≤ u := by linarith
      have hl2 : (|lam| * Real.sqrt u) ^ 2 = lam ^ 2 * u := by
        rw [mul_pow, sq_abs, Real.sq_sqrt hu0]
      -- `c² = u ρ² / (R D_W)`
      have hc2 : (|lam| * Real.sqrt u * (1 / Real.sqrt (DD (m + 1) 3))) ^ 2 =
          u * (radF53 W' ^ 2 / (R * DWr (m + 1) (JR (m + 1) 3))) := by
        rw [mul_pow, hl2, mul_assoc, mul_comm u, ← mul_assoc, hlamsc, mul_comm]
      -- `1/R ≤ (101/99) c²`
      have hinvR : 1 / R ≤ 101 / 99 *
          (|lam| * Real.sqrt u * (1 / Real.sqrt (DD (m + 1) 3))) ^ 2 := by
        rw [hc2, div_le_iff₀ hRpos]
        have e : 101 / 99 * (u * (radF53 W' ^ 2 / (R * DWr (m + 1) (JR (m + 1) 3)))) * R =
            101 / 99 * u * (radF53 W' ^ 2 / DWr (m + 1) (JR (m + 1) 3)) := by
          field_simp
        rw [e]
        have h1 : 100 / 101 ≤ radF53 W' ^ 2 / DWr (m + 1) (JR (m + 1) 3) := by
          rw [le_div_iff₀ hDW]; linarith
        have h2 : 99 / 100 * (100 / 101) ≤
            u * (radF53 W' ^ 2 / DWr (m + 1) (JR (m + 1) 3)) :=
          mul_le_mul hu99 h1 (by norm_num) hu0
        linarith
      have hc20 : 0 ≤ (|lam| * Real.sqrt u * (1 / Real.sqrt (DD (m + 1) 3))) ^ 2 := sq_nonneg _
      have hFT : 0 ≤ frobT T' := by
        unfold BstLean.Part82.frobT
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          Finset.sum_nonneg fun k _ => sq_nonneg _
      have hnsq : ∀ j : Fin (3 + 1), ∑ i, U (j, i) ^ 2 ≤ 11 / 10 * ((m + 1 : ℕ) : ℝ) →
          nsq (fun i => U (j, i) / Real.sqrt R) ≤ 9 / 8 * ((m : ℝ) + 1) *
            (|lam| * Real.sqrt u * (1 / Real.sqrt (DD (m + 1) 3))) ^ 2 := by
        intro j hj
        rw [nsq_div, hr2]
        have h1 : nsq (fun i => U (j, i)) / R = nsq (fun i => U (j, i)) * (1 / R) := by ring
        rw [h1]
        have h2 : nsq (fun i => U (j, i)) ≤ 11 / 10 * ((m : ℝ) + 1) := by
          rw [← hmR]; exact hj
        have h3 : 0 ≤ nsq (fun i => U (j, i)) := Finset.sum_nonneg fun i _ => sq_nonneg _
        have h4 : (0 : ℝ) ≤ 1 / R := by positivity
        have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
        calc nsq (fun i => U (j, i)) * (1 / R)
            ≤ 11 / 10 * ((m : ℝ) + 1) * (101 / 99 *
                (|lam| * Real.sqrt u * (1 / Real.sqrt (DD (m + 1) 3))) ^ 2) :=
              mul_le_mul h2 hinvR h4 (by positivity)
          _ ≤ _ := by
              have := mul_nonneg hm1 hc20
              linarith
      have hta : ∀ j : Fin (3 + 1), frobH (TA T' (fun i => U (j, i))) ≤ Mk * frobT T' →
          frobH (TA T' (fun i => U (j, i) / Real.sqrt R)) ≤ 103 / 100 * Mk *
            (|lam| * Real.sqrt u * (1 / Real.sqrt (DD (m + 1) 3))) ^ 2 * frobT T' := by
        intro j hj
        rw [TA_div, hr2]
        have h1 : frobH (TA T' (fun i => U (j, i))) / R =
            frobH (TA T' (fun i => U (j, i))) * (1 / R) := by ring
        rw [h1]
        have h3 : 0 ≤ frobH (TA T' (fun i => U (j, i))) :=
          Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ => sq_nonneg _
        have h4 : (0 : ℝ) ≤ 1 / R := by positivity
        have h5 : 0 ≤ Mk * frobT T' := mul_nonneg hMk hFT
        calc frobH (TA T' (fun i => U (j, i))) * (1 / R)
            ≤ Mk * frobT T' * (101 / 99 *
                (|lam| * Real.sqrt u * (1 / Real.sqrt (DD (m + 1) 3))) ^ 2) :=
              mul_le_mul hj hinvR h4 h5
          _ ≤ _ := by
              have := mul_nonneg h5 hc20
              linarith
      have hosc := hOsc (fun j i => U (j, i) / Real.sqrt R)
        (|lam| * Real.sqrt u * (1 / Real.sqrt (DD (m + 1) 3)))
        (hnsq 2 hU2) (hnsq 3 hU3) (hta 2 hTU2) (hta 3 hTU3)
      have hv1 := hVarM P f0 ℓ H T' _ _ hHs hT's hQ (|lam| * Real.sqrt u) cH cT e1 e2 e4 e3
        η ω ζ hcH hcT hcH4 hcT4 he1 he2 he4 he3 hη hω hζ hosc
      have hnn := intYbar_nonneg (modRK m 3 t v E) P (|lam| * Real.sqrt u)
      have hle := intYbar_le_q (modRK m 3 t v E) 3 hR hPF P (|lam| * Real.sqrt u)
      have hsq : (∫ p, Ybar (modRK m 3 t v E) P (|lam| * Real.sqrt u) p
            ∂(modRK m 3 t v E).pi) ^ 2 ≤
          (∫ p, qsl (modRK m 3 t v E) P (|lam| * Real.sqrt u) p ∂(modRK m 3 t v E).pi) ^ 2 :=
        pow_le_pow_left₀ hnn hle 2
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hsq hX0)
      exact hv1)
  have hc1 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * L + 2 := by
    have := mul_nonneg hn0 hL0; linarith
  have hcV : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) *
      cVW 3 (tS (m + 1) β) L
        (Xc L g4 c3 cH cT e1 e2 e4 e3 η ω ζ ^ 2) ϑ :=
    mul_nonneg hn0 (cVW_nonneg _ _ _ _ _ hX0 hϑ)
  have h40 : (0 : ℝ) ≤ 1 / 40 := by norm_num
  exact remezSemiP (modRK m 3 t v E) 3 3 _ _ _ (1 / 40) a b β ξ _ (by omega) (by omega) hR hPF
    P hP lam hG hSu h40 le_rfl hL0 (by linarith) ha hb0 hb1 hab hβ (by linarith) hξ hξ2 hξβ hν
    hc1 hcV (card_W_ge (m + 1) 3 (by omega) hdn h100)

end BstLean.Part90

#print axioms BstLean.Part90.pt3
