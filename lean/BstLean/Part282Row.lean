import BstLean.Part282Kit
import BstLean.Part272Stated

/-!
# Part 282 (C2), one sphere row, even `n`

Paper: `theorem7-01-statement-program.tex`, Lemma `t7:p01:moments` (even `n`).
Lean: `Part272Even.sphA`, `sphE`, `JJ`, `NPinv`; `Part272Stated.a1St`, `e1St`.

`rowProg n`: from the inputs `s`, `w = √(1 − s²)`, `α`, `κ`, the two outputs
`sphA n (sα) (wκ)` and `sphE n (sα) (wκ)` (`rowProg_eval_A`, `rowProg_eval_E`). The program has
no branching: the three branch tests are the indicators `k/k`, `relu(k − m)/relu(k − m)`,
`relu(m + k)/relu(m + k)` (total division), and the value is a selection with them. The
coefficients `(−1)^r C(P, r)/(2r + j + 1)`, their sums, and `𝒩_P` are rational constants of the
model (free). The three sums `J_j(d)` use the Horner loop in `d²`:
`J_j(d) = Σ_r c_{r,j} − d^{j+1} Σ_r c_{r,j} d^{2r}` (`JJ_horner`).

`rowProg_cost`: `6P + 58` operations, `P = (n − 4)/2` (so `3n + 46` for even `n ≥ 4`).
This is MORE than the 29 fixed operations of `Part279.evenRowOps` (`3n + 29` in all), because
the branch selection without branching costs more than three comparisons. It is less than the
row allowance `3n + 100` of `Part189.sphereRowWork`.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part272

noncomputable section

variable {ι : Type}

/-! ## Several expressions side by side -/

/-- One expression per index of `Fin m`. -/
def RProg.parV {m : ℕ} (es : Fin m → RExpr ι) : RProg ι (Fin m) :=
  RProg.parF fun i => (es i).prog

@[simp] theorem RProg.eval_parV {m : ℕ} (es : Fin m → RExpr ι) (v : ι → ℝ) (i : Fin m) :
    (RProg.parV es).eval v i = (es i).eval v := by
  simp [RProg.parV]

theorem RProg.cost_parV {m : ℕ} (es : Fin m → RExpr ι) :
    (RProg.parV es).cost = ∑ i, (es i).size := by
  rw [RProg.parV, RProg.parF, RProg.cost_parL, Fin.sum_univ_def]
  simp

/-! ## The rational constants -/

/-- `c_{r,j} = (−1)^r C(P, r)/(2r + j + 1)`. -/
def coefQ (P j r : ℕ) : ℚ := (-1) ^ r * (P.choose r) / (2 * r + j + 1)

/-- `S_j = Σ_{r ≤ P} c_{r,j}`. -/
def sumQ (P j : ℕ) : ℚ := ∑ r ∈ Finset.range (P + 1), coefQ P j r

/-- `𝒩_P = (2∏_{r=1}^P 2r/(2r+1))⁻¹`. -/
def normQ (P : ℕ) : ℚ := (2 * ∏ r ∈ Finset.Icc 1 P, (2 * (r : ℚ)) / (2 * r + 1))⁻¹

theorem normQ_cast (P : ℕ) : ((normQ P : ℚ) : ℝ) = (NPinv P)⁻¹ := by
  simp [normQ, NPinv]

/-- **The Horner form of `J_j`.** -/
theorem JJ_horner (P j : ℕ) (d : ℝ) :
    JJ P j d = (sumQ P j : ℝ) -
      d ^ (j + 1) * ∑ r ∈ Finset.range (P + 1), (coefQ P j r : ℝ) * (d * d) ^ r := by
  unfold JJ sumQ
  rw [Finset.mul_sum]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [coefQ]
  push_cast
  have : d ^ (2 * r + j + 1) = d ^ (j + 1) * (d * d) ^ r := by
    rw [← pow_two, ← pow_mul, ← pow_add]; ring_nf
  rw [this]
  ring

/-! ## The program -/

/-- The inputs: `![s, w, α, κ]`. -/
abbrev RowIn : Type := Fin 4

/-- Stage 1: `m = sα`, `k = wκ`. -/
def st1 : Fin 2 → RExpr RowIn :=
  ![RExpr.mul (.inp 0) (.inp 2), RExpr.mul (.inp 1) (.inp 3)]

abbrev E1 : Type := RowIn ⊕ Fin 2
def mI : E1 := Sum.inr 0
def kI : E1 := Sum.inr 1

/-- Stage 2: `d = (0 − m)/k`, `m²`, `k²`, `mk`, `relu m`, `k/k`, the indicator of `k > m`,
the indicator of `m + k > 0`. -/
def st2 : Fin 8 → RExpr E1 :=
  ![RExpr.div (RExpr.sub (.cst 0) (.inp mI)) (.inp kI),
    RExpr.mul (.inp mI) (.inp mI),
    RExpr.mul (.inp kI) (.inp kI),
    RExpr.mul (.inp mI) (.inp kI),
    RExpr.relu (.inp mI),
    RExpr.div (.inp kI) (.inp kI),
    RExpr.div (RExpr.relu (RExpr.sub (.inp kI) (.inp mI))) (RExpr.relu (RExpr.sub (.inp kI) (.inp mI))),
    RExpr.div (RExpr.relu (RExpr.add (.inp mI) (.inp kI))) (RExpr.relu (RExpr.add (.inp mI) (.inp kI)))]

abbrev E2 : Type := RowIn ⊕ (Fin 2 ⊕ Fin 8)
def p2 : RProg RowIn (Fin 2 ⊕ Fin 8) := RProg.ext (RProg.parV st1) (RProg.parV st2)

/-- Stage 3: `z = d·d`. -/
def st3 : Fin 1 → RExpr E2 := ![RExpr.mul (.inp (Sum.inr (Sum.inr 0))) (.inp (Sum.inr (Sum.inr 0)))]

abbrev E3 : Type := RowIn ⊕ ((Fin 2 ⊕ Fin 8) ⊕ Fin 1)
def p3 : RProg RowIn ((Fin 2 ⊕ Fin 8) ⊕ Fin 1) := RProg.ext p2 (RProg.parV st3)

/-- Stage 4: the three Horner loops in `z`. -/
def st4 (P : ℕ) : RProg E3 (Fin 3) :=
  RProg.parF fun j => horner (coefQ P j) P (Sum.inr (Sum.inr 0))

abbrev E4 : Type := RowIn ⊕ (((Fin 2 ⊕ Fin 8) ⊕ Fin 1) ⊕ Fin 3)
def p4 (P : ℕ) : RProg RowIn (((Fin 2 ⊕ Fin 8) ⊕ Fin 1) ⊕ Fin 3) := RProg.ext p3 (st4 P)

def dI4 : E4 := Sum.inr (Sum.inl (Sum.inl (Sum.inr 0)))
def zI4 : E4 := Sum.inr (Sum.inl (Sum.inr 0))
def hI4 (j : Fin 3) : E4 := Sum.inr (Sum.inr j)

/-- Stage 5: `J₀ = S₀ − d H₀`, `J₁ = S₁ − z H₁`, `J₂ = S₂ − (z d) H₂`. -/
def st5 (P : ℕ) : Fin 3 → RExpr E4 :=
  ![RExpr.sub (.cst (sumQ P 0)) (RExpr.mul (.inp dI4) (.inp (hI4 0))),
    RExpr.sub (.cst (sumQ P 1)) (RExpr.mul (.inp zI4) (.inp (hI4 1))),
    RExpr.sub (.cst (sumQ P 2)) (RExpr.mul (RExpr.mul (.inp zI4) (.inp dI4)) (.inp (hI4 2)))]

abbrev E5 : Type := RowIn ⊕ ((((Fin 2 ⊕ Fin 8) ⊕ Fin 1) ⊕ Fin 3) ⊕ Fin 3)
def p5 (P : ℕ) : RProg RowIn ((((Fin 2 ⊕ Fin 8) ⊕ Fin 1) ⊕ Fin 3) ⊕ Fin 3) :=
  RProg.ext (p4 P) (RProg.parV (st5 P))

/-- References into the environment of stage 6. -/
def m6 : E5 := Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl 0))))
def k6 : E5 := Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl 1))))
def a6 (i : Fin 8) : E5 := Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr i))))
def j6 (j : Fin 3) : E5 := Sum.inr (Sum.inr j)

/-- `𝒩_P(mJ₀ + kJ₁)`. -/
def gAE (P : ℕ) : RExpr E5 :=
  RExpr.mul (.cst (normQ P))
    (RExpr.add (RExpr.mul (.inp m6) (.inp (j6 0))) (RExpr.mul (.inp k6) (.inp (j6 1))))

/-- `𝒩_P(m²J₀ + 2mkJ₁ + k²J₂)`. -/
def gEE (P : ℕ) : RExpr E5 :=
  RExpr.mul (.cst (normQ P))
    (RExpr.add (RExpr.add (RExpr.mul (.inp (a6 1)) (.inp (j6 0)))
      (RExpr.mul (.cst 2) (RExpr.mul (.inp (a6 3)) (.inp (j6 1)))))
      (RExpr.mul (.inp (a6 2)) (.inp (j6 2))))

/-- `m² + k²/(n − 1)`. -/
def qE (n : ℕ) : RExpr E5 := RExpr.add (.inp (a6 1)) (RExpr.div (.inp (a6 2)) (.cst ((n : ℚ) - 1)))

/-- `relu m + i₀((m − relu m) + i_a(i_b G_A − m))`. -/
def outA (P : ℕ) : RExpr E5 :=
  RExpr.add (.inp (a6 4)) (RExpr.mul (.inp (a6 5))
    (RExpr.add (RExpr.sub (.inp m6) (.inp (a6 4)))
      (RExpr.mul (.inp (a6 6)) (RExpr.sub (RExpr.mul (.inp (a6 7)) (gAE P)) (.inp m6)))))

/-- `(relu m)² + i₀((Q − (relu m)²) + i_a(i_b G_E − Q))`. -/
def outE (n P : ℕ) : RExpr E5 :=
  RExpr.add (RExpr.mul (.inp (a6 4)) (.inp (a6 4))) (RExpr.mul (.inp (a6 5))
    (RExpr.add (RExpr.sub (qE n) (RExpr.mul (.inp (a6 4)) (.inp (a6 4))))
      (RExpr.mul (.inp (a6 6)) (RExpr.sub (RExpr.mul (.inp (a6 7)) (gEE P)) (qE n)))))

/-- **One sphere row (even `n`).** Output `0`: `ā`; output `1`: `ē`. -/
def rowProg (n : ℕ) : RProg RowIn (Fin 2) :=
  (p5 ((n - 4) / 2)).bind (RProg.parV ![outA ((n - 4) / 2), outE n ((n - 4) / 2)])

def rowVal (s w α κ : ℝ) : RowIn → ℝ := ![s, w, α, κ]

/-! ## The value -/

theorem rowProg_eval (n : ℕ) (s w α κ : ℝ) :
    (rowProg n).eval (rowVal s w α κ) 0 = sphA n (s * α) (w * κ) ∧
      (rowProg n).eval (rowVal s w α κ) 1 = sphE n (s * α) (w * κ) := by
  set P := (n - 4) / 2 with hP
  set m := s * α with hm
  set k := w * κ with hk
  set v := rowVal s w α κ with hv
  set d := -m / k with hd
  set z := d * d with hz
  have L0 : (RProg.parV st1).eval v = ![m, k] := by
    funext j; fin_cases j <;> simp [st1, hv, rowVal, hm, hk]
  have L1 : p2.eval v = Sum.elim ![m, k] ![d, m * m, k * k, m * k, relu m, k / k,
      relu (k - m) / relu (k - m), relu (m + k) / relu (m + k)] := by
    funext x
    rcases x with j | j
    · simp only [p2, RProg.eval_ext_inl, L0, Sum.elim_inl]
    · simp only [p2, RProg.eval_ext_inr, RProg.eval_parV, L0]
      fin_cases j <;> simp [st2, mI, kI, hd]
  have L2 : p3.eval v = Sum.elim (p2.eval v) ![z] := by
    funext x
    rcases x with j | j
    · simp only [p3, RProg.eval_ext_inl, Sum.elim_inl]
    · simp only [p3, RProg.eval_ext_inr, RProg.eval_parV]
      fin_cases j
      simp [st3, L1, hz]
  have L3 : (p4 P).eval v = Sum.elim (p3.eval v)
      (fun j : Fin 3 => ∑ r ∈ Finset.range (P + 1), (coefQ P j r : ℝ) * z ^ r) := by
    funext x
    rcases x with j | j
    · simp only [p4, RProg.eval_ext_inl, Sum.elim_inl]
    · simp only [p4, RProg.eval_ext_inr, st4, RProg.eval_parF, horner_eval, Sum.elim_inr, L2]
      simp
  have L4 : (p5 P).eval v = Sum.elim ((p4 P).eval v)
      ![(sumQ P 0 : ℝ) - d * ∑ r ∈ Finset.range (P + 1), (coefQ P 0 r : ℝ) * z ^ r,
        (sumQ P 1 : ℝ) - z * ∑ r ∈ Finset.range (P + 1), (coefQ P 1 r : ℝ) * z ^ r,
        (sumQ P 2 : ℝ) - z * d * ∑ r ∈ Finset.range (P + 1), (coefQ P 2 r : ℝ) * z ^ r] := by
    funext x
    rcases x with j | j
    · simp only [p5, RProg.eval_ext_inl, Sum.elim_inl]
    · simp only [p5, RProg.eval_ext_inr, RProg.eval_parV]
      fin_cases j <;> simp [st5, dI4, zI4, hI4, L3, L2, L1]
  have hJ0 : JJ P 0 d = (sumQ P 0 : ℝ) - d * ∑ r ∈ Finset.range (P + 1), (coefQ P 0 r : ℝ) * z ^ r := by
    rw [JJ_horner, hz]; ring
  have hJ1 : JJ P 1 d = (sumQ P 1 : ℝ) - z * ∑ r ∈ Finset.range (P + 1), (coefQ P 1 r : ℝ) * z ^ r := by
    rw [JJ_horner, hz]; ring
  have hJ2 : JJ P 2 d = (sumQ P 2 : ℝ) - z * d * ∑ r ∈ Finset.range (P + 1), (coefQ P 2 r : ℝ) * z ^ r := by
    rw [JJ_horner, hz]; ring
  have hout : ∀ i : Fin 2, (rowProg n).eval v i =
      (![outA P, outE n P] i).eval (Sum.elim v ((p5 P).eval v)) := by
    intro i
    simp only [rowProg, RProg.eval_bind, RProg.eval_parV, hP]
  have hN : ((normQ P : ℚ) : ℝ) = (NPinv P)⁻¹ := normQ_cast P
  have rz : ∀ x : ℝ, x ≤ 0 → relu x = 0 := fun x hx => max_eq_left hx
  have rn : ∀ x : ℝ, 0 < x → relu x ≠ 0 := fun x hx => by
    unfold relu; rw [max_eq_right hx.le]; exact hx.ne'
  constructor
  · rw [hout 0]
    simp [L4, L3, L2, L1, outA, gAE, m6, k6, a6, j6, ind_ne, hN]
    unfold sphA
    rw [← hP, ← hd, hJ0, hJ1]
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
    simp [L4, L3, L2, L1, outE, gEE, qE, m6, k6, a6, j6, ind_ne, hN]
    unfold sphE
    rw [← hP, ← hd, hJ0, hJ1, hJ2]
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
          simp only [h0, h1, h2, r1, r2, ne_eq, not_false_eq_true, if_true, if_false]
          ring

/-- **The row program computes the stated moments (even `n`).** -/
theorem a1St_eq_rowProg {n : ℕ} (he : Even n) (c : BstLean.Part157.Ret n) (s : ℝ)
    (i : Fin (BstLean.Part130.mA n)) :
    a1St c s i = (rowProg n).eval (rowVal s (√(1 - s ^ 2)) (alphaE c i) (kappaE c i)) 0 := by
  rw [(rowProg_eval n _ _ _ _).1, a1St, if_pos he]

theorem e1St_eq_rowProg {n : ℕ} (he : Even n) (c : BstLean.Part157.Ret n) (s : ℝ)
    (i : Fin (BstLean.Part130.mA n)) :
    e1St c s i = (rowProg n).eval (rowVal s (√(1 - s ^ 2)) (alphaE c i) (kappaE c i)) 1 := by
  rw [(rowProg_eval n _ _ _ _).2, e1St, if_pos he]

/-! ## The cost -/

theorem rowProg_cost (n : ℕ) : (rowProg n).cost = 6 * ((n - 4) / 2) + 58 := by
  simp only [rowProg, p5, p4, p3, p2, st4, RProg.cost_bind, RProg.cost_ext, RProg.cost_parV]
  rw [RProg.cost_parF_eq _ (2 * ((n - 4) / 2)) (fun j => horner_cost _ _ _)]
  simp [Fin.sum_univ_succ, st1, st2, st3, st5, outA, outE, gAE, gEE, qE]
  omega

end

end BstLean.Part282

/-- info: 'BstLean.Part282.rowProg_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.rowProg_eval
