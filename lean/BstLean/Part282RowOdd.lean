import BstLean.Part282World

/-!
# Part 282 (C2), one sphere row, odd `n`

Lean: `Part272Stated.sphAodd`, `sphEodd`, `oddA`, `oddE`, `KK`, `asinO`, `asinPos`, `DD`, `piO`.

`rowOdd n`: from `![s, w, α, κ]` the outputs `sphAodd n (sα) (wκ)` and `sphEodd n (sα) (wκ)`
(`rowOdd_eval`, no hypothesis). The stages: `m, k, d = −m/k, …` (stage `p3` of `Part282Row`);
`1 − d²`, `√(1 − d²)`, the indicator of `d < 0`, `|d|`; the indicator of `|d| > 1/2`,
`y = √((1 − |d|)/2)`, `|d|²`, `y²`; two Horner loops for `Q_{T_o}`; `K₀ = π_o/2 − arcsin_o d`;
the loop `K_{r+1} = (2r+1)/(2r+2)·K_r − d(1−d²)^r√(1−d²)/(2r+2)` (`P + 1` steps, five
operations each); `K_{P+2}`, `J₁`; the clipped moments and the branch selection.
`rowOdd_cost = 4T_o + 5P + 108`, `P = (n − 5)/2`, `T_o = Todd n`.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part157 BstLean.Part272

noncomputable section

variable {ι X Y : Type}

/-! ## Environment helpers -/

def up : RowIn ⊕ X → RowIn ⊕ (X ⊕ Y) := Sum.elim Sum.inl (fun x => Sum.inr (Sum.inl x))
def nw (y : Y) : RowIn ⊕ (X ⊕ Y) := Sum.inr (Sum.inr y)

@[simp] theorem elim_up (v : RowIn → ℝ) (F : X → ℝ) (G : Y → ℝ) (x : RowIn ⊕ X) :
    Sum.elim v (Sum.elim F G) (up x) = Sum.elim v F x := by
  cases x <;> rfl

@[simp] theorem elim_nw (v : RowIn → ℝ) (F : X → ℝ) (G : Y → ℝ) (y : Y) :
    Sum.elim v (Sum.elim F G) (nw (X := X) y) = G y := rfl

/-! ## The Horner loop with `T` terms -/

def hStepT (c : ℕ → ℚ) (T : ℕ) (z : ι) (j : ℕ) : RProg (ι ⊕ Unit) Unit :=
  (RExpr.add (RExpr.mul (.inp (Sum.inr ())) (.inp (Sum.inl z))) (.cst (c (T - 1 - j)))).prog

def hornerT (c : ℕ → ℚ) (T : ℕ) (z : ι) : RProg ι Unit :=
  RProg.iter (RProg.ofArgs fun _ => .cst 0) (hStepT c T z) T

theorem hornerT_aux (c : ℕ → ℚ) (T : ℕ) (z : ι) (v : ι → ℝ) (j : ℕ) (hj : j ≤ T) :
    (RProg.iter (RProg.ofArgs fun _ => .cst 0) (hStepT c T z) j).eval v () =
      ∑ r ∈ Finset.range j, (c (T - j + r) : ℝ) * v z ^ r := by
  induction j with
  | zero => simp [Arg.eval]
  | succ j ih =>
    rw [RProg.eval_iter_succ]
    simp only [hStepT, RExpr.eval_prog, RExpr.eval_add, RExpr.eval_mul, RExpr.eval_inp,
      RExpr.eval_cst, Sum.elim_inr, Sum.elim_inl]
    rw [ih (by omega), Finset.sum_mul]
    conv_rhs => rw [Finset.sum_range_succ']
    have hP : T - (j + 1) + 0 = T - 1 - j := by omega
    rw [hP, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : T - j + r = T - (j + 1) + (r + 1) := by
      simp at hr; omega
    rw [hr', pow_succ]
    ring

theorem hornerT_eval (c : ℕ → ℚ) (T : ℕ) (z : ι) (v : ι → ℝ) :
    (hornerT c T z).eval v () = ∑ r ∈ Finset.range T, (c r : ℝ) * v z ^ r := by
  rw [hornerT, hornerT_aux c T z v T le_rfl]
  simp

theorem hornerT_cost (c : ℕ → ℚ) (T : ℕ) (z : ι) : (hornerT c T z).cost = 2 * T := by
  rw [hornerT, RProg.cost_iter_const _ _ T 2 (fun j => by simp [hStepT])]
  simp; ring

/-! ## Rational constants -/

/-- `(2j)!/(4^j (j!)² (2j+1))`. -/
def qcQ (j : ℕ) : ℚ := ((2 * j).factorial : ℚ) / (4 ^ j * (j.factorial : ℚ) ^ 2 * (2 * (j : ℚ) + 1))

theorem QT_horner (T : ℕ) (v : ℝ) :
    QTsum T v = v * ∑ j ∈ Finset.range T, (qcQ j : ℝ) * (v * v) ^ j := by
  unfold QTsum qcQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  rw [pow_succ, pow_mul, ← pow_two]
  ring

def DDQ : ℕ → ℚ
  | 0 => 2
  | r + 1 => DDQ r * (2 * ((r : ℚ) + 1) + 2) / (2 * ((r : ℚ) + 1) + 1)

theorem DDQ_cast (r : ℕ) : ((DDQ r : ℚ) : ℝ) = DD r := by
  induction r with
  | zero => simp [DDQ, DD]
  | succ r ih => simp only [DDQ, DD]; push_cast; rw [ih]

def piOQ (n : ℕ) : ℚ := 16 * ATsumQ (Tpio n) (1 / 5) - 4 * ATsumQ (Tpio n) (1 / 239)

theorem piOQ_cast (n : ℕ) : ((piOQ n : ℚ) : ℝ) = piO n := by
  unfold piOQ piO; push_cast [ATsumQ_cast]; norm_num

/-- The loop coefficient `(2(r+1) − 1)/(2(r+1))` and divisor `2(r+1)`. -/
def kc1 (r : ℕ) : ℚ := (2 * ((r : ℚ) + 1) - 1) / (2 * ((r : ℚ) + 1))
def kc2 (r : ℕ) : ℚ := 2 * ((r : ℚ) + 1)

/-! ## The stages -/

abbrev X0 : Type := (Fin 2 ⊕ Fin 8) ⊕ Fin 1
abbrev X1 : Type := X0 ⊕ Fin 4
abbrev X2 : Type := X1 ⊕ Fin 4
abbrev X3 : Type := X2 ⊕ Fin 2
abbrev X4 : Type := X3 ⊕ Fin 1
abbrev X5 : Type := X4 ⊕ Fin 2
abbrev X6 : Type := X5 ⊕ Fin 2
abbrev X7 : Type := X6 ⊕ Fin 2

/-- Indices of stage 0 (`p3` of `Part282Row`). -/
def m0 : RowIn ⊕ X0 := Sum.inr (Sum.inl (Sum.inl 0))
def k0 : RowIn ⊕ X0 := Sum.inr (Sum.inl (Sum.inl 1))
def a0 (i : Fin 8) : RowIn ⊕ X0 := Sum.inr (Sum.inl (Sum.inr i))
def z0 : RowIn ⊕ X0 := Sum.inr (Sum.inr 0)

/-- Stage A: `1 − z`, `√(1 − z)`, `[d < 0]`, `|d|`. -/
def stA : Fin 4 → RExpr (RowIn ⊕ X0) :=
  ![RExpr.sub (.cst 1) (.inp z0),
    RExpr.sqrt (RExpr.sub (.cst 1) (.inp z0)),
    RExpr.div (RExpr.relu (RExpr.sub (.cst 0) (.inp (a0 0)))) (RExpr.relu (RExpr.sub (.cst 0) (.inp (a0 0)))),
    RExpr.add (RExpr.relu (.inp (a0 0))) (RExpr.relu (RExpr.sub (.cst 0) (.inp (a0 0))))]

def o1 : RProg RowIn X1 := RProg.ext p3 (RProg.parV stA)

/-- Stage B: `[|d| > 1/2]`, `y = √((1 − |d|)/2)`, `|d|²`, `y²`. -/
def avB : RExpr (RowIn ⊕ X1) := .inp (nw 3)
def yB : RExpr (RowIn ⊕ X1) := RExpr.sqrt (RExpr.div (RExpr.sub (.cst 1) avB) (.cst 2))
def stB : Fin 4 → RExpr (RowIn ⊕ X1) :=
  ![RExpr.div (RExpr.relu (RExpr.sub avB (.cst (1 / 2)))) (RExpr.relu (RExpr.sub avB (.cst (1 / 2)))),
    yB, RExpr.mul avB avB, RExpr.mul yB yB]

def o2 : RProg RowIn X2 := RProg.ext o1 (RProg.parV stB)

/-- Stage C: the Horner sums at `|d|²` and `y²`. -/
def stC (n : ℕ) : RProg (RowIn ⊕ X2) (Fin 2) :=
  RProg.parF fun j => hornerT qcQ (Todd n) (if j = 0 then nw 2 else nw 3)

def o3 (n : ℕ) : RProg RowIn X3 := RProg.ext o2 (stC n)

/-- Stage D: `K₀ = π_o/2 − (1 − 2[d<0])(Q(|d|) + [|d|>1/2](π_o/2 − 2yQ_y − Q(|d|)))`. -/
def k0E (n : ℕ) : RExpr (RowIn ⊕ X3) :=
  let av : RExpr (RowIn ⊕ X3) := .inp (up (up (nw 3)))
  let ineg : RExpr (RowIn ⊕ X3) := .inp (up (up (nw 2)))
  let ib : RExpr (RowIn ⊕ X3) := .inp (up (nw 0))
  let y : RExpr (RowIn ⊕ X3) := .inp (up (nw 1))
  let pa := RExpr.mul av (.inp (nw 0))
  let pb := RExpr.sub (.cst (piOQ n / 2)) (RExpr.mul (.cst 2) (RExpr.mul y (.inp (nw 1))))
  RExpr.sub (.cst (piOQ n / 2))
    (RExpr.mul (RExpr.sub (.cst 1) (RExpr.mul (.cst 2) ineg))
      (RExpr.add pa (RExpr.mul ib (RExpr.sub pb pa))))

def o4 (n : ℕ) : RProg RowIn X4 := RProg.ext (o3 n) (RProg.parV ![k0E n])

/-- The `K` loop: state `(K_r, (1−d²)^r √(1−d²))`. -/
def dK4 : RowIn ⊕ X4 := up (up (up (up (a0 0))))
def qK4 : RowIn ⊕ X4 := up (up (up (nw 0)))
def wK4 : RowIn ⊕ X4 := up (up (up (nw 1)))

def kStep (r : ℕ) : RProg ((RowIn ⊕ X4) ⊕ Fin 2) (Fin 2) :=
  RProg.parV ![RExpr.sub (RExpr.mul (.cst (kc1 r)) (.inp (Sum.inr 0)))
      (RExpr.div (RExpr.mul (.inp (Sum.inl dK4)) (.inp (Sum.inr 1))) (.cst (kc2 r))),
    RExpr.mul (.inp (Sum.inr 1)) (.inp (Sum.inl qK4))]

def kLoop (P : ℕ) : RProg (RowIn ⊕ X4) (Fin 2) :=
  RProg.iter (RProg.ofArgs ![.inp (nw 0), .inp wK4]) kStep (P + 1)

def o5 (n : ℕ) : RProg RowIn X5 := RProg.ext (o4 n) (kLoop ((n - 5) / 2))

/-- Stage F1: `K_{P+2}`, `J₁ = (1−d²)^{P+1}√(1−d²)/(2P+3)`. -/
def stF1 (P : ℕ) : Fin 2 → RExpr (RowIn ⊕ X5) :=
  ![RExpr.sub (RExpr.mul (.cst (kc1 (P + 1))) (.inp (nw 0)))
      (RExpr.div (RExpr.mul (.inp (up (up (up (up (up (a0 0))))))) (.inp (nw 1))) (.cst (kc2 (P + 1)))),
    RExpr.div (.inp (nw 1)) (.cst (2 * (P : ℚ) + 3))]

def o6 (n : ℕ) : RProg RowIn X6 := RProg.ext (o5 n) (RProg.parV (stF1 ((n - 5) / 2)))

/-- Stage F2: `relu(𝒩(mK₁ + kJ₁))` and `𝒩(m²K₁ + 2mkJ₁ + k²(K₁ − K₂))`, `𝒩 = D_P/π_o`. -/
def up6 (x : RowIn ⊕ X0) : RowIn ⊕ X6 := up (up (up (up (up (up x)))))
def stF2 (n P : ℕ) : Fin 2 → RExpr (RowIn ⊕ X6) :=
  let K1 : RExpr (RowIn ⊕ X6) := .inp (up (nw 0))
  let K2 : RExpr (RowIn ⊕ X6) := .inp (nw 0)
  let J1 : RExpr (RowIn ⊕ X6) := .inp (nw 1)
  ![RExpr.relu (RExpr.mul (.cst (DDQ P / piOQ n))
      (RExpr.add (RExpr.mul (.inp (up6 m0)) K1) (RExpr.mul (.inp (up6 k0)) J1))),
    RExpr.mul (.cst (DDQ P / piOQ n))
      (RExpr.add (RExpr.add (RExpr.mul (.inp (up6 (a0 1))) K1)
        (RExpr.mul (.cst 2) (RExpr.mul (.inp (up6 (a0 3))) J1)))
        (RExpr.mul (.inp (up6 (a0 2))) (RExpr.sub K1 K2)))]

def o7 (n : ℕ) : RProg RowIn X7 := RProg.ext (o6 n) (RProg.parV (stF2 n ((n - 5) / 2)))

/-- Stage F3: the branch selection. -/
def up7 (x : RowIn ⊕ X0) : RowIn ⊕ X7 := up (up6 x)
def stF3 (n : ℕ) : Fin 2 → RExpr (RowIn ⊕ X7) :=
  let m : RExpr (RowIn ⊕ X7) := .inp (up7 m0)
  let rm : RExpr (RowIn ⊕ X7) := .inp (up7 (a0 4))
  let i0 : RExpr (RowIn ⊕ X7) := .inp (up7 (a0 5))
  let ia : RExpr (RowIn ⊕ X7) := .inp (up7 (a0 6))
  let ib : RExpr (RowIn ⊕ X7) := .inp (up7 (a0 7))
  let ac : RExpr (RowIn ⊕ X7) := .inp (nw 0)
  let oe : RExpr (RowIn ⊕ X7) := .inp (nw 1)
  let q := RExpr.add (.inp (up7 (a0 1))) (RExpr.div (.inp (up7 (a0 2))) (.cst ((n : ℚ) - 1)))
  let ec := RExpr.add (RExpr.mul ac ac) (RExpr.relu (RExpr.sub oe (RExpr.mul ac ac)))
  ![RExpr.add rm (RExpr.mul i0 (RExpr.add (RExpr.sub m rm)
      (RExpr.mul ia (RExpr.sub (RExpr.mul ib ac) m)))),
    RExpr.add (RExpr.mul rm rm) (RExpr.mul i0 (RExpr.add (RExpr.sub q (RExpr.mul rm rm))
      (RExpr.mul ia (RExpr.sub (RExpr.mul ib ec) q))))]

/-- **One sphere row, odd `n`.** -/
def rowOdd (n : ℕ) : RProg RowIn (Fin 2) := (o7 n).bind (RProg.parV (stF3 n))

/-! ## The values -/

theorem max_eq_relu (a b : ℝ) : max a b = b + relu (a - b) := by
  unfold relu
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- The `K` loop. -/
theorem kLoop_aux (n : ℕ) (d : ℝ) (w : RowIn ⊕ X4 → ℝ) (hK : w (nw 0) = KK n d 0)
    (hd : w dK4 = d) (hq : w qK4 = 1 - d ^ 2) (hw : w wK4 = √(1 - d ^ 2)) (t : ℕ) :
    (RProg.iter (RProg.ofArgs ![.inp (nw 0), .inp wK4]) kStep t).eval w =
      ![KK n d t, (1 - d ^ 2) ^ t * √(1 - d ^ 2)] := by
  induction t with
  | zero =>
    funext x; fin_cases x <;> simp [Arg.eval, hK, hw]
  | succ t ih =>
    rw [RProg.eval_iter_succ, ih]
    funext x
    simp only [kStep, RProg.eval_parV]
    fin_cases x
    · simp only [Matrix.cons_val_zero, RExpr.eval_sub, RExpr.eval_mul, RExpr.eval_div,
        RExpr.eval_inp, RExpr.eval_cst, Sum.elim_inl, Sum.elim_inr, hd, Matrix.cons_val_one,
        Matrix.head_cons, Fin.zero_eta, Fin.isValue]
      simp only [KK, kc1, kc2]
      push_cast
      ring
    · simp [hq]
      ring

/-- `K₀ = π_o/2 − arcsin_o d` in the raw form of stage D. -/
theorem k0_value (n : ℕ) (d : ℝ) :
    ((piOQ n / 2 : ℚ) : ℝ) - (((1 : ℚ) : ℝ) - ((2 : ℚ) : ℝ) *
        (relu (((0 : ℚ) : ℝ) - d) / relu (((0 : ℚ) : ℝ) - d))) *
      ((relu d + relu (((0 : ℚ) : ℝ) - d)) * ∑ r ∈ Finset.range (Todd n), (qcQ r : ℝ) *
          ((relu d + relu (((0 : ℚ) : ℝ) - d)) * (relu d + relu (((0 : ℚ) : ℝ) - d))) ^ r +
        relu (relu d + relu (((0 : ℚ) : ℝ) - d) - ((1 / 2 : ℚ) : ℝ)) /
            relu (relu d + relu (((0 : ℚ) : ℝ) - d) - ((1 / 2 : ℚ) : ℝ)) *
          (((piOQ n / 2 : ℚ) : ℝ) - ((2 : ℚ) : ℝ) *
              (√((((1 : ℚ) : ℝ) - (relu d + relu (((0 : ℚ) : ℝ) - d))) / ((2 : ℚ) : ℝ)) *
                ∑ r ∈ Finset.range (Todd n), (qcQ r : ℝ) *
                  (√((((1 : ℚ) : ℝ) - (relu d + relu (((0 : ℚ) : ℝ) - d))) / ((2 : ℚ) : ℝ)) *
                    √((((1 : ℚ) : ℝ) - (relu d + relu (((0 : ℚ) : ℝ) - d))) / ((2 : ℚ) : ℝ))) ^ r) -
            (relu d + relu (((0 : ℚ) : ℝ) - d)) * ∑ r ∈ Finset.range (Todd n), (qcQ r : ℝ) *
              ((relu d + relu (((0 : ℚ) : ℝ) - d)) * (relu d + relu (((0 : ℚ) : ℝ) - d))) ^ r)) =
      KK n d 0 := by
  rw [← QT_horner, ← QT_horner, ind_pos, ind_pos]
  have hpi : (((piOQ n / 2 : ℚ)) : ℝ) = piO n / 2 := by push_cast [piOQ_cast]; ring
  rw [hpi]
  push_cast
  simp only [KK, asinO, asinPos]
  by_cases hd : 0 ≤ d
  · have h1 : relu d + relu (0 - d) = d := by
      simp only [relu]; rw [max_eq_right hd, max_eq_left (by linarith)]; ring
    have h2 : ¬ (0 < 0 - d) := by linarith
    rw [h1, if_pos hd, if_neg h2]
    by_cases h3 : d ≤ 1 / 2
    · rw [if_pos h3, if_neg (not_lt.mpr (by linarith))]; ring
    · rw [if_neg h3, if_pos (by linarith)]; ring
  · have h1 : relu d + relu (0 - d) = -d := by
      simp only [relu]; rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    have h2 : 0 < 0 - d := by linarith
    rw [h1, if_neg hd, if_pos h2]
    by_cases h3 : -d ≤ 1 / 2
    · rw [if_pos h3, if_neg (not_lt.mpr (by linarith))]; ring
    · rw [if_neg h3, if_pos (by linarith)]; ring

/-- **The odd row program computes `sphAodd`, `sphEodd`.** -/
theorem rowOdd_eval (n : ℕ) (s w α κ : ℝ) :
    (rowOdd n).eval (rowVal s w α κ) 0 = sphAodd n (s * α) (w * κ) ∧
      (rowOdd n).eval (rowVal s w α κ) 1 = sphEodd n (s * α) (w * κ) := by
  set P := (n - 5) / 2 with hP
  set m := s * α with hm
  set k := w * κ with hk
  set v := rowVal s w α κ with hv
  set d := -m / k with hd
  have L0 : (RProg.parV st1).eval v = ![m, k] := by
    funext j; fin_cases j <;> simp [st1, hv, rowVal, hm, hk]
  have L1 : p2.eval v = Sum.elim ![m, k] ![d, m * m, k * k, m * k, relu m, k / k,
      relu (k - m) / relu (k - m), relu (m + k) / relu (m + k)] := by
    funext x
    rcases x with j | j
    · simp only [p2, RProg.eval_ext_inl, L0, Sum.elim_inl]
    · simp only [p2, RProg.eval_ext_inr, RProg.eval_parV, L0]
      fin_cases j <;> simp [st2, mI, kI, hd]
  have L2 : p3.eval v = Sum.elim (p2.eval v) ![d * d] := by
    funext x
    rcases x with j | j
    · simp only [p3, RProg.eval_ext_inl, Sum.elim_inl]
    · simp only [p3, RProg.eval_ext_inr, RProg.eval_parV]
      fin_cases j
      simp [st3, L1]
  set AV := relu d + relu (((0 : ℚ) : ℝ) - d) with hAV
  set Y := √((((1 : ℚ) : ℝ) - AV) / ((2 : ℚ) : ℝ)) with hY
  have LA : o1.eval v = Sum.elim (p3.eval v) ![((1 : ℚ) : ℝ) - d * d, √(((1 : ℚ) : ℝ) - d * d),
      relu (((0 : ℚ) : ℝ) - d) / relu (((0 : ℚ) : ℝ) - d), AV] := by
    funext x
    rcases x with j | j
    · simp only [o1, RProg.eval_ext_inl, Sum.elim_inl]
    · simp only [o1, RProg.eval_ext_inr, RProg.eval_parV]
      fin_cases j <;> simp [stA, z0, a0, L2, L1, hAV]
  have LB : o2.eval v = Sum.elim (o1.eval v)
      ![relu (AV - ((1 / 2 : ℚ) : ℝ)) / relu (AV - ((1 / 2 : ℚ) : ℝ)), Y, AV * AV, Y * Y] := by
    funext x
    rcases x with j | j
    · simp only [o2, RProg.eval_ext_inl, Sum.elim_inl]
    · simp only [o2, RProg.eval_ext_inr, RProg.eval_parV]
      fin_cases j <;> simp [stB, avB, yB, nw, LA, hAV, hY]
  have LC : (o3 n).eval v = Sum.elim (o2.eval v)
      ![∑ r ∈ Finset.range (Todd n), (qcQ r : ℝ) * (AV * AV) ^ r,
        ∑ r ∈ Finset.range (Todd n), (qcQ r : ℝ) * (Y * Y) ^ r] := by
    funext x
    rcases x with j | j
    · simp only [o3, RProg.eval_ext_inl, Sum.elim_inl]
    · simp only [o3, RProg.eval_ext_inr, stC, RProg.eval_parF, hornerT_eval]
      fin_cases j <;> simp [nw, LB]
  have LD : (o4 n).eval v = Sum.elim ((o3 n).eval v) ![KK n d 0] := by
    funext x
    rcases x with j | j
    · simp only [o4, RProg.eval_ext_inl, Sum.elim_inl]
    · simp only [o4, RProg.eval_ext_inr, RProg.eval_parV]
      fin_cases j
      rw [← k0_value n d]
      simp only [k0E, Matrix.cons_val_fin_one, Matrix.cons_val_zero, RExpr.eval_sub,
        RExpr.eval_mul, RExpr.eval_add, RExpr.eval_inp, RExpr.eval_cst, LC, LB, LA, elim_up,
        elim_nw, Sum.elim_inr, Sum.elim_inl, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, hY, hAV, Fin.zero_eta, Fin.isValue] <;> rfl
  have hdd : ((1 : ℚ) : ℝ) - d * d = 1 - d ^ 2 := by push_cast; ring
  have LK : (o5 n).eval v = Sum.elim ((o4 n).eval v)
      ![KK n d (P + 1), (1 - d ^ 2) ^ (P + 1) * √(1 - d ^ 2)] := by
    funext x
    rcases x with j | j
    · simp only [o5, RProg.eval_ext_inl, Sum.elim_inl]
    · simp only [o5, RProg.eval_ext_inr, kLoop]
      rw [kLoop_aux n d _ (by simp [LD]) (by simp [dK4, a0, LD, LC, LB, LA, L2, L1])
        (by simp [qK4, LD, LC, LB, LA, pow_two]) (by simp [wK4, LD, LC, LB, LA, pow_two]) (P + 1)]
        <;> rfl
  have LF1 : (o6 n).eval v = Sum.elim ((o5 n).eval v)
      ![KK n d (P + 2), (1 - d ^ 2) ^ (P + 1) * √(1 - d ^ 2) / (2 * (P : ℝ) + 3)] := by
    funext x
    rcases x with j | j
    · simp only [o6, RProg.eval_ext_inl, Sum.elim_inl]
    · simp only [o6, RProg.eval_ext_inr, RProg.eval_parV]
      have hKs : ∀ r : ℕ, KK n d (r + 1) = (2 * ((r : ℝ) + 1) - 1) / (2 * ((r : ℝ) + 1)) *
          KK n d r - d * ((1 - d ^ 2) ^ r * √(1 - d ^ 2)) / (2 * ((r : ℝ) + 1)) := fun r => rfl
      fin_cases j
      · simp [stF1, a0, LK, LD, LC, LB, LA, L2, L1, kc1, kc2, hKs, hP] <;> ring
      · simp [stF1, LK, hP]
  have LF2 : (o7 n).eval v = Sum.elim ((o6 n).eval v) ![max 0 (oddA n m k), oddE n m k] := by
    funext x
    rcases x with j | j
    · simp only [o7, RProg.eval_ext_inl, Sum.elim_inl]
    · simp only [o7, RProg.eval_ext_inr, RProg.eval_parV]
      fin_cases j
      · simp [stF2, up6, m0, k0, a0, LF1, LK, LD, LC, LB, LA, L2, L1, oddA, relu, DDQ_cast,
          piOQ_cast, hd, hP]
      · (simp [stF2, up6, m0, k0, a0, LF1, LK, LD, LC, LB, LA, L2, L1, oddE, DDQ_cast,
          piOQ_cast, hd, hP]) <;> ring_nf <;> simp
  have hout : ∀ i : Fin 2, (rowOdd n).eval v i =
      (stF3 n i).eval (Sum.elim v ((o7 n).eval v)) := by
    intro i
    simp only [rowOdd, RProg.eval_bind, RProg.eval_parV]
  have rz : ∀ x : ℝ, x ≤ 0 → relu x = 0 := fun x hx => max_eq_left hx
  have rn : ∀ x : ℝ, 0 < x → relu x ≠ 0 := fun x hx => by
    unfold relu; rw [max_eq_right hx.le]; exact hx.ne'
  constructor
  · rw [hout 0]
    simp [stF3, up7, up6, m0, a0, LF2, LF1, LK, LD, LC, LB, LA, L2, L1, ind_ne]
    unfold sphAodd
    by_cases h0 : k = 0
    · simp [h0] <;> ring
    · by_cases h1 : k ≤ m
      · have r1 := rz (k - m) (by linarith)
        simp [h0, h1, r1] <;> ring
      · by_cases h2 : m ≤ -k
        · have r1 := rn (k - m) (by linarith)
          have r2 := rz (m + k) (by linarith)
          simp [h0, h1, h2, r1, r2] <;> ring
        · have r1 := rn (k - m) (by linarith)
          have r2 := rn (m + k) (by linarith)
          simp [h0, h1, h2, r1, r2] <;> ring
  · rw [hout 1]
    simp [stF3, up7, up6, m0, a0, LF2, LF1, LK, LD, LC, LB, LA, L2, L1, ind_ne]
    unfold sphEodd
    rw [max_eq_relu (oddE n m k)]
    by_cases h0 : k = 0
    · simp [h0, pow_two] <;> ring
    · by_cases h1 : k ≤ m
      · have r1 := rz (k - m) (by linarith)
        simp [h0, h1, r1, pow_two] <;> ring
      · by_cases h2 : m ≤ -k
        · have r1 := rn (k - m) (by linarith)
          have r2 := rz (m + k) (by linarith)
          simp [h0, h1, h2, r1, r2] <;> ring
        · have r1 := rn (k - m) (by linarith)
          have r2 := rn (m + k) (by linarith)
          simp only [h0, h1, h2, r1, r2, ne_eq, not_false_eq_true, if_true, if_false, pow_two]
          ring

theorem a1St_eq_rowOdd {n : ℕ} (ho : ¬ Even n) (c : Ret n) (s : ℝ) (i : Fin (mA n)) :
    a1St c s i = (rowOdd n).eval (rowVal s (√(1 - s ^ 2)) (alphaE c i) (kappaE c i)) 0 := by
  rw [(rowOdd_eval n _ _ _ _).1, a1St, if_neg ho]

theorem e1St_eq_rowOdd {n : ℕ} (ho : ¬ Even n) (c : Ret n) (s : ℝ) (i : Fin (mA n)) :
    e1St c s i = (rowOdd n).eval (rowVal s (√(1 - s ^ 2)) (alphaE c i) (kappaE c i)) 1 := by
  rw [(rowOdd_eval n _ _ _ _).2, e1St, if_neg ho]

theorem rowOdd_cost (n : ℕ) : (rowOdd n).cost = 4 * Todd n + 5 * ((n - 5) / 2) + 108 := by
  have hk : (kLoop ((n - 5) / 2)).cost = 5 * ((n - 5) / 2 + 1) := by
    rw [kLoop, RProg.cost_iter_const _ _ _ 5
      (fun r => by simp [kStep, RProg.cost_parV, Fin.sum_univ_succ])]
    simp; ring
  have hc : (stC n).cost = 4 * Todd n := by
    rw [stC, RProg.cost_parF_eq _ (2 * Todd n) (fun j => hornerT_cost _ _ _)]
    ring
  simp only [rowOdd, o7, o6, o5, o4, o3, o2, o1, p3, p2, RProg.cost_bind, RProg.cost_ext,
    RProg.cost_parV, hk, hc]
  simp [Fin.sum_univ_succ, stA, stB, avB, yB, k0E, stF1, stF2, stF3, st1, st2, st3] <;> omega

end

end BstLean.Part282

/-- info: 'BstLean.Part282.rowOdd_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.rowOdd_eval
/-- info: 'BstLean.Part282.rowOdd_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.rowOdd_cost
