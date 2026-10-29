import BstLean.Part89QDefs
import BstLean.Part86Gauss

/-!
# Part 89, `d_f = 2`: the variance bound averaged over the slices (`quadVar`)

From the variance bound in one slice (`QuadSlice`) to the variance bound for the within-slice
variance `Vdn = E_p Y_p` (`QuadVar`): pairs of slices, Cauchy–Schwarz twice, and the floor
`Ȳ_p ≥ 2 (1 − Λ) ‖H‖_F² t_p²`.
-/

namespace BstLean.Part89

open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open BstLean.Part29 (stdGauss)
open BstLean.Part78 (nsq frobH qfun zv)
open BstLean.Part84 (sq_integral_le)
open BstLean.Part86 BstLean.Part86.XGauss

namespace QVar

/-! ## Tame helpers -/

section tame

variable {ι : Type} [Fintype ι] {T : Type} [MeasurableSpace T]

lemma tame_of_bdd {c : T → ℝ} (hm : Measurable c) (B : ℝ) (hB : ∀ t, |c t| ≤ B) :
    Tame (ι := ι) (fun _ t => c t) := by
  refine ⟨hm.comp measurable_snd, |B|, 0, abs_nonneg _, fun W t => ?_⟩
  have : Dom 0 W = 1 := by simp [Dom]
  rw [this, mul_one]
  exact (hB t).trans (le_abs_self _)

lemma sqrt_le_one_add_abs (x : ℝ) : Real.sqrt x ≤ 1 + |x| := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [abs_nonneg x, le_abs_self x]

lemma tame_sqrt {h : (ι → ℝ) → T → ℝ} (H : Tame h) :
    Tame (fun W t => Real.sqrt (h W t)) := by
  obtain ⟨m, A, N, a, b⟩ := H
  refine ⟨m.sqrt, 1 + A, N, by linarith, fun W t => ?_⟩
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 := sqrt_le_one_add_abs (h W t)
  have h2 := b W t
  have h3 := one_le_Dom N W
  nlinarith

end tame

/-! ## Arithmetic -/

lemma young (ω u w : ℝ) (hω : 0 < ω) : (u + w) ^ 2 ≤ (1 + ω) * u ^ 2 + (1 + 1 / ω) * w ^ 2 := by
  have e : (1 + ω) * u ^ 2 + (1 + 1 / ω) * w ^ 2 - (u + w) ^ 2 = (ω * u - w) ^ 2 / ω := by
    field_simp; ring
  have h0 : 0 ≤ (ω * u - w) ^ 2 / ω := div_nonneg (sq_nonneg _) hω.le
  linarith

/-- The arithmetic of Steps 2–4. -/
lemma final_arith (Lam η η' ω Yn kmax tmin Yb C F L T D c0 a b : ℝ)
    (hL0 : 0 ≤ Lam) (hL1 : Lam ≤ 1 / 2) (hη : 0 < η) (hη' : 0 < η') (hω : 0 < ω)
    (hYn : 0 ≤ Yn) (hkm : 0 < kmax) (htm0 : 0 < tmin) (hc0 : 0 ≤ c0) (hF : 0 ≤ F)
    (hLn : 0 ≤ L) (hT : 0 ≤ T) (htm : tmin ≤ T) (hYb : 0 ≤ Yb)
    (hC : C ^ 2 ≤ L * T * Yb)
    (hfl : 2 * (1 - Lam) * F * L ^ 2 * T ^ 2 ≤ Yb)
    (hD : D ≤ Yn * (L * F))
    (ha : a ^ 2 = 2 * Lam * (2 + η) * (1 + η') / (1 - Lam))
    (hb : b ^ 2 = 2 * Lam * ((2 + η) * (1 + 1 / η') * D + c0 * (L * kmax / 2) * F)) :
    (a * Yb + b * C) ^ 2 ≤
      2 * Lam / (1 - Lam) *
        ((1 + ω) * (2 + η) * (1 + η') +
          (1 + 1 / ω) * ((2 + η) * (1 + 1 / η') * Yn + c0 * kmax / 2) / (2 * tmin)) * Yb ^ 2 := by
  have h1L : 0 < 1 - Lam := by linarith
  have hc1 : 0 ≤ (2 + η) * (1 + 1 / η') := by positivity
  have hω1 : 0 ≤ 1 + 1 / ω := by positivity
  set K := (2 + η) * (1 + 1 / η') * Yn + c0 * kmax / 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set Z := F * L ^ 2 * T with hZ
  have hZ0 : 0 ≤ Z := by positivity
  -- Step 3
  have hZle : Z ≤ Yb / (2 * (1 - Lam) * tmin) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : F * L ^ 2 * T * tmin ≤ F * L ^ 2 * T * T :=
      mul_le_mul_of_nonneg_left htm (by positivity)
    have h2 : Z * (2 * (1 - Lam) * tmin) = 2 * (1 - Lam) * (F * L ^ 2 * T * tmin) := by
      rw [hZ]; ring
    have h3 : 2 * (1 - Lam) * (F * L ^ 2 * T * tmin) ≤ 2 * (1 - Lam) * (F * L ^ 2 * T * T) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h4 : 2 * (1 - Lam) * (F * L ^ 2 * T * T) = 2 * (1 - Lam) * F * L ^ 2 * T ^ 2 := by ring
    linarith
  have hE : ((2 + η) * (1 + 1 / η') * D + c0 * (L * kmax / 2) * F) * (L * T) ≤ K * Z := by
    have h1 : (2 + η) * (1 + 1 / η') * D ≤ (2 + η) * (1 + 1 / η') * (Yn * (L * F)) :=
      mul_le_mul_of_nonneg_left hD hc1
    have h2 : ((2 + η) * (1 + 1 / η') * D + c0 * (L * kmax / 2) * F) * (L * T) ≤
        ((2 + η) * (1 + 1 / η') * (Yn * (L * F)) + c0 * (L * kmax / 2) * F) * (L * T) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    refine h2.trans (le_of_eq ?_)
    rw [hK, hZ]; ring
  -- Step 4
  have hy := young ω (a * Yb) (b * C) hω
  have hb0 : 0 ≤ b ^ 2 := sq_nonneg _
  have hw : (b * C) ^ 2 ≤ 2 * Lam * (K * Z) * Yb := by
    have e1 : (b * C) ^ 2 = b ^ 2 * C ^ 2 := by ring
    have e2 : b ^ 2 * C ^ 2 ≤ b ^ 2 * (L * T * Yb) := mul_le_mul_of_nonneg_left hC hb0
    have e3 : b ^ 2 * (L * T * Yb) =
        2 * Lam * (((2 + η) * (1 + 1 / η') * D + c0 * (L * kmax / 2) * F) * (L * T)) * Yb := by
      rw [hb]; ring
    have e4 : 2 * Lam * (((2 + η) * (1 + 1 / η') * D + c0 * (L * kmax / 2) * F) * (L * T)) * Yb ≤
        2 * Lam * (K * Z) * Yb :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by linarith)) hYb
    linarith
  have hw2 : 2 * Lam * (K * Z) * Yb ≤ 2 * Lam * (K * (Yb / (2 * (1 - Lam) * tmin))) * Yb :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZle hK0) (by linarith)) hYb
  have hfin : (1 + ω) * (a * Yb) ^ 2 +
      (1 + 1 / ω) * (2 * Lam * (K * (Yb / (2 * (1 - Lam) * tmin))) * Yb) =
      2 * Lam / (1 - Lam) *
        ((1 + ω) * (2 + η) * (1 + η') + (1 + 1 / ω) * K / (2 * tmin)) * Yb ^ 2 := by
    rw [mul_pow, ha]
    field_simp
  have h5 : (1 + 1 / ω) * (b * C) ^ 2 ≤
      (1 + 1 / ω) * (2 * Lam * (K * (Yb / (2 * (1 - Lam) * tmin))) * Yb) :=
    mul_le_mul_of_nonneg_left (hw.trans hw2) hω1
  linarith

end QVar

open QVar

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]

lemma Yb_nonneg (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ) (p : S) :
    0 ≤ Yb M P lam p :=
  integral_nonneg fun W => integral_nonneg fun g => sq_nonneg _

lemma Dq_nonneg (H : Matrix (Fin n) (Fin n) ℝ) (A : I → Fin n → ℝ) : 0 ≤ Dq H A := by
  unfold Dq
  have : 0 ≤ ∑ j, nsq (fun i => ∑ l, H i l * A j l) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  positivity

lemma c0q_nonneg (η : ℝ) (hη : 0 < η) : 0 ≤ c0q η := by
  unfold c0q; positivity

/-- **The variance bound for the within-slice variance**, from the variance bound in one slice. -/
theorem quadVar (M : Mod n I J S G) (d : ℕ) (Lam kmax tmin : ℝ) (tau : S → ℝ)
    (hR : Reg M d) (hPF : PolyFacts M d) (hOp : SliceOpF M Lam tau)
    (hQS : QuadSlice M Lam tau kmax)
    (hL0 : 0 ≤ Lam) (hL1 : Lam ≤ 1 / 2) (hkm : 0 < kmax) (htk : ∀ p, tau p ≤ kmax)
    (htm0 : 0 < tmin) (htm : tmin ≤ ∫ p, tau p ∂M.pi) :
    QuadVar M Lam kmax tmin := by
  intro P f0 ℓ H A sc hH hQR lam η η' ω Yn hη hη' hω hYn hDq
  have := hR.1
  have := hR.2.1
  have hT := fun P lam => tameFs M d hR hPF P lam
  have h1L : 0 < 1 - Lam := by linarith
  have hF0 : 0 ≤ frobH H := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD0 := Dq_nonneg H A
  have hc0 := c0q_nonneg η hη
  have htau0 : ∀ p, 0 ≤ tau p := fun p => (hOp.2 p).1
  set L := lam ^ 2 * sc ^ 2 with hLdef
  have hLn : 0 ≤ L := by positivity
  set E0 := (2 + η) * (1 + 1 / η') * Dq H A + c0q η * (L * kmax / 2) * frobH H with hE0
  have hE00 : 0 ≤ E0 := by positivity
  set al := 2 * Lam * (2 + η) * (1 + η') / (1 - Lam) with hal
  have hal0 : 0 ≤ al := by positivity
  set a := Real.sqrt al with ha
  set b := Real.sqrt (2 * Lam * E0) with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = al := Real.sq_sqrt hal0
  have hb2 : b ^ 2 = 2 * Lam * E0 := Real.sq_sqrt (by positivity)
  -- tame functions
  have tY := t_Y M P lam hT
  have tYb : Tame (ι := J × Fin n) (fun _ (p : S) => Yb M P lam p) := tY.intW
  have ttau : Tame (ι := J × Fin n) (fun _ (p : S) => tau p) :=
    tame_of_bdd hOp.1 kmax (fun p => by rw [abs_of_nonneg (htau0 p)]; exact htk p)
  have tLt : Tame (ι := J × Fin n) (fun _ (p : S) => L * tau p) := (Tame.const L).mul ttau
  have tr1 : Tame (ι := J × Fin n) (fun _ (p : S) => Real.sqrt (L * tau p)) := tame_sqrt tLt
  have tr2 : Tame (ι := J × Fin n) (fun _ (p : S) => Real.sqrt (Yb M P lam p)) := tame_sqrt tYb
  set s : S → ℝ := fun p =>
    a * Yb M P lam p + b * (Real.sqrt (L * tau p) * Real.sqrt (Yb M P lam p)) with hs
  have ts : Tame (ι := J × Fin n) (fun _ (p : S) => s p) :=
    ((Tame.const a).mul tYb).add ((Tame.const b).mul (tr1.mul tr2))
  have hs0 : ∀ p, 0 ≤ s p := fun p => by
    have := Yb_nonneg M P lam p
    have := Real.sqrt_nonneg (L * tau p)
    have := Real.sqrt_nonneg (Yb M P lam p)
    show 0 ≤ a * Yb M P lam p + b * (Real.sqrt (L * tau p) * Real.sqrt (Yb M P lam p))
    positivity
  have iYb : Integrable (fun p => Yb M P lam p) M.pi := tYb.int_par M.pi
  have itau : Integrable tau M.pi := ttau.int_par M.pi
  have ir : Integrable (fun p => Real.sqrt (L * tau p) * Real.sqrt (Yb M P lam p)) M.pi :=
    (tr1.mul tr2).int_par M.pi
  -- the slice bound
  have hgood := hQS P f0 ℓ H A sc hH hQR lam η η' hη hη'
  have hVs : ∀ᵐ p ∂M.pi,
      ∫ W, (Ysl M P lam W p - Yb M P lam p) ^ 2 ∂stdGauss (J × Fin n) ≤ s p ^ 2 := by
    filter_upwards [hgood] with p hp
    have hp2 : ∫ W, (Ysl M P lam W p - Yb M P lam p) ^ 2 ∂stdGauss (J × Fin n) ≤
        al * Yb M P lam p ^ 2 + 2 * Lam * (L * tau p) * E0 * Yb M P lam p := hp.2
    refine hp2.trans ?_
    have hy := Yb_nonneg M P lam p
    have ht : 0 ≤ L * tau p := mul_nonneg hLn (htau0 p)
    have e1 : Real.sqrt (L * tau p) ^ 2 = L * tau p := Real.sq_sqrt ht
    have e2 : Real.sqrt (Yb M P lam p) ^ 2 = Yb M P lam p := Real.sq_sqrt hy
    have hr1 := Real.sqrt_nonneg (L * tau p)
    have hr2 := Real.sqrt_nonneg (Yb M P lam p)
    have e : s p ^ 2 = al * Yb M P lam p ^ 2 + 2 * Lam * (L * tau p) * E0 * Yb M P lam p +
        2 * (a * Yb M P lam p) * (b * (Real.sqrt (L * tau p) * Real.sqrt (Yb M P lam p))) := by
      show (a * Yb M P lam p + b * (Real.sqrt (L * tau p) * Real.sqrt (Yb M P lam p))) ^ 2 = _
      calc (a * Yb M P lam p + b * (Real.sqrt (L * tau p) * Real.sqrt (Yb M P lam p))) ^ 2
          = a ^ 2 * Yb M P lam p ^ 2 +
              b ^ 2 * (Real.sqrt (L * tau p) ^ 2 * Real.sqrt (Yb M P lam p) ^ 2) +
              2 * (a * Yb M P lam p) *
                (b * (Real.sqrt (L * tau p) * Real.sqrt (Yb M P lam p))) := by ring
        _ = _ := by rw [ha2, hb2, e1, e2]; ring
    have hcross : 0 ≤ 2 * (a * Yb M P lam p) *
        (b * (Real.sqrt (L * tau p) * Real.sqrt (Yb M P lam p))) := by positivity
    rw [e]
    linarith
  -- Step 1: pairs of slices
  set Ybb := ∫ p, Yb M P lam p ∂M.pi with hYbb
  have th : Tame (fun (W : J × Fin n → ℝ) (p : S) => Ysl M P lam W p - Yb M P lam p) :=
    tY.sub tYb
  have tH : Tame (fun (W : J × Fin n → ℝ) (z : S × S) =>
      (Ysl M P lam W z.1 - Yb M P lam z.1) * (Ysl M P lam W z.2 - Yb M P lam z.2)) :=
    (th.comp_right measurable_fst).mul (th.comp_right measurable_snd)
  have e1 : ∀ W, (Vdn M P lam W - Ybb) ^ 2 =
      ∫ z, (Ysl M P lam W z.1 - Yb M P lam z.1) * (Ysl M P lam W z.2 - Yb M P lam z.2)
        ∂(M.pi.prod M.pi) := by
    intro W
    have a' : Vdn M P lam W - Ybb = ∫ p, (Ysl M P lam W p - Yb M P lam p) ∂M.pi :=
      (integral_sub (tY.int_right W M.pi) iYb).symm
    have b' := integral_prod_mul (μ := M.pi) (ν := M.pi)
      (fun p => Ysl M P lam W p - Yb M P lam p) (fun p => Ysl M P lam W p - Yb M P lam p)
    rw [a', sq]; exact b'.symm
  have hpt : ∀ᵐ z ∂(M.pi.prod M.pi),
      ∫ W, (Ysl M P lam W z.1 - Yb M P lam z.1) * (Ysl M P lam W z.2 - Yb M P lam z.2)
        ∂stdGauss (J × Fin n) ≤ s z.1 * s z.2 := by
    have g1 : ∀ᵐ z ∂(M.pi.prod M.pi),
        ∫ W, (Ysl M P lam W z.1 - Yb M P lam z.1) ^ 2 ∂stdGauss (J × Fin n) ≤ s z.1 ^ 2 :=
      (Measure.quasiMeasurePreserving_fst (μ := M.pi) (ν := M.pi)).ae hVs
    have g2 : ∀ᵐ z ∂(M.pi.prod M.pi),
        ∫ W, (Ysl M P lam W z.2 - Yb M P lam z.2) ^ 2 ∂stdGauss (J × Fin n) ≤ s z.2 ^ 2 :=
      (Measure.quasiMeasurePreserving_snd (μ := M.pi) (ν := M.pi)).ae hVs
    filter_upwards [g1, g2] with z hA hB
    have hcs := cs_sq (stdGauss (J × Fin n))
      (fun W => Ysl M P lam W z.1 - Yb M P lam z.1)
      (fun W => Ysl M P lam W z.2 - Yb M P lam z.2)
      ((th.pow 2).int_left z.1) ((th.pow 2).int_left z.2) (tH.int_left z)
    have hX : 0 ≤ s z.1 * s z.2 := mul_nonneg (hs0 _) (hs0 _)
    have hprod := mul_le_mul hA hB (integral_nonneg fun W => sq_nonneg _) (sq_nonneg (s z.1))
    have hsq : (∫ W, (Ysl M P lam W z.1 - Yb M P lam z.1) *
        (Ysl M P lam W z.2 - Yb M P lam z.2) ∂stdGauss (J × Fin n)) ^ 2 ≤
        (s z.1 * s z.2) ^ 2 := by
      refine (hcs.trans hprod).trans (le_of_eq ?_); ring
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq hsq hX)
  have iR : Integrable (fun z : S × S => s z.1 * s z.2) (M.pi.prod M.pi) :=
    ((ts.comp_right measurable_fst).mul (ts.comp_right measurable_snd)).int_par (M.pi.prod M.pi)
  have hstep1 : ∫ W, (Vdn M P lam W - Ybb) ^ 2 ∂stdGauss (J × Fin n) ≤
      (∫ p, s p ∂M.pi) ^ 2 := by
    simp only [e1]
    rw [tH.swap (M.pi.prod M.pi)]
    have h1 := integral_mono_ae (tH.intW.int_par (M.pi.prod M.pi)) iR hpt
    rw [integral_prod_mul (μ := M.pi) (ν := M.pi) s s] at h1
    rw [sq]; exact h1
  -- the integral of `s`
  set C := ∫ p, Real.sqrt (L * tau p) * Real.sqrt (Yb M P lam p) ∂M.pi with hC
  have hsint : ∫ p, s p ∂M.pi = a * Ybb + b * C := by
    show ∫ p, (a * Yb M P lam p +
      b * (Real.sqrt (L * tau p) * Real.sqrt (Yb M P lam p))) ∂M.pi = _
    rw [integral_add (iYb.const_mul a) (ir.const_mul b), integral_const_mul, integral_const_mul]
  -- Step 2: Cauchy–Schwarz over the slices
  set Tt := ∫ p, tau p ∂M.pi with hTt
  have hTt0 : 0 ≤ Tt := integral_nonneg htau0
  have hYbb0 : 0 ≤ Ybb := integral_nonneg (Yb_nonneg M P lam)
  have hCS : C ^ 2 ≤ L * Tt * Ybb := by
    have hcs := cs_sq M.pi (fun p => Real.sqrt (L * tau p))
      (fun p => Real.sqrt (Yb M P lam p)) ((tr1.pow 2).int_par M.pi) ((tr2.pow 2).int_par M.pi) ir
    have e1 : ∫ p, Real.sqrt (L * tau p) ^ 2 ∂M.pi = L * Tt := by
      rw [hTt, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p =>
        Real.sq_sqrt (mul_nonneg hLn (htau0 p)))
    have e2 : ∫ p, Real.sqrt (Yb M P lam p) ^ 2 ∂M.pi = Ybb :=
      integral_congr_ae (Filter.Eventually.of_forall fun p =>
        Real.sq_sqrt (Yb_nonneg M P lam p))
    rw [e1, e2] at hcs
    exact hcs
  -- Step 3: the floor
  have hfl : 2 * (1 - Lam) * frobH H * L ^ 2 * Tt ^ 2 ≤ Ybb := by
    have i2 : Integrable (fun p => tau p ^ 2) M.pi := (ttau.pow 2).int_par M.pi
    have hJ := sq_integral_le M.pi tau itau i2
    have hfa : ∀ᵐ p ∂M.pi, 2 * (1 - Lam) * frobH H * L ^ 2 * tau p ^ 2 ≤ Yb M P lam p := by
      filter_upwards [hgood] with p hp
      refine le_trans (le_of_eq ?_) hp.1
      ring
    have h1 := integral_mono_ae (i2.const_mul (2 * (1 - Lam) * frobH H * L ^ 2)) iYb hfa
    rw [integral_const_mul] at h1
    have h2 : 2 * (1 - Lam) * frobH H * L ^ 2 * Tt ^ 2 ≤
        2 * (1 - Lam) * frobH H * L ^ 2 * ∫ p, tau p ^ 2 ∂M.pi :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    exact h2.trans h1
  -- Step 4
  have hfin := final_arith Lam η η' ω Yn kmax tmin Ybb C (frobH H) L Tt (Dq H A) (c0q η) a b
    hL0 hL1 hη hη' hω hYn hkm htm0 hc0 hF0 hLn hTt0 htm hYbb0 hCS hfl
    (by rw [hLdef]; exact hDq) ha2 hb2
  rw [hsint] at hstep1
  refine hstep1.trans (hfin.trans (le_of_eq ?_))
  unfold XQ
  rfl

end BstLean.Part89

#print axioms BstLean.Part89.quadVar
